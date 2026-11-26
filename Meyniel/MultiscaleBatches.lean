module

public import Meyniel.MultiscaleSites

/-! # Charging newly assigned centers to their first launch interval -/

@[expose] public section

namespace Meyniel.Multiscale
open Finset Filter
noncomputable section
variable {V : Type*} [Fintype V]

def triggered (G : SimpleGraph V) (R : ℕ → V) (stop threshold : ℕ) (C : Finset V) : Finset V := by
  classical
  exact C.filter fun z => ∃ f ≤ stop, G.dist (R f) z ≤ threshold

private theorem stride_gap {x y r : ℕ} (hr : 0 < r) (hxy : x ≤ y) (heq : x/r=y/r) : y-x ≤ r := by
  have h1 := Nat.mod_add_div x r
  have h2 := Nat.mod_add_div y r
  rw [heq] at h1
  have h3 := Nat.mod_lt y hr
  omega

omit [Fintype V] in
private theorem sum_bucket (s : Finset V) (f : V → ℕ) {b : ℕ} (hf : ∀ z ∈ s, f z < b) :
    ∑ j ∈ range b, (s.filter (fun x => f x=j)).card = s.card := by
  rw [sum_card_fiberwise_eq_card_filter]
  congr 1
  exact filter_true_of_mem fun z hz => mem_range.mpr (hf z hz)

/-- The number of activated sites for a fixed radius, counted on a single real
robber history, including possible activation at the last allowed time. -/
theorem triggered_card (G : SimpleGraph V) (hc : G.Connected) (R : ℕ → V)
    (hR : SpeedOne G R) {δ : ℝ} {N : ℕ} (i : Fin (levels δ)) (r stop : ℕ)
    (hr : 0 < r) (pad : 2*(endTime (clockFactor δ) r+2*guardRadius δ N (i.val+1))+
      r+baseRadius δ N (i.val+1) ≤ outerRadius δ N (i.val+1)) :
    let q := physicalScale G δ N i
    let D := triggered G R stop (q.last r+2*q.base) (net G δ N i)
    (D.card:ℝ) ≤ ((stop/r+1 : ℕ):ℝ) * (N:ℝ)^(δ/100) := by
  classical
  let q := physicalScale G δ N i
  let C := net G δ N i
  let K := q.last r + 2*q.base
  let A := triggered G R stop K C
  let first (z : V) := if h : ∃ f ≤ stop, G.dist (R f) z ≤ K then h.choose else 0
  have ha {z : V} (hz : z ∈ A) : first z ≤ stop ∧ G.dist (R (first z)) z ≤ K := by
    have hh := (mem_filter.mp hz).2
    simpa [first,hh] using hh.choose_spec
  have hcnet {z : V} (hz : z ∈ A) : z ∈ C := (mem_filter.mp hz).1
  have near {x y : V} (hx : x ∈ A) (hy : y ∈ A) (eq : first x/r=first y/r) :
      G.dist x y ≤ 2*K+r := by
    wlog hh : first x ≤ first y generalizing x y
    · simpa [SimpleGraph.dist_comm] using this hy hx eq.symm (by omega)
    have e1 := (ha hx).2
    have e2 := (ha hy).2
    have hdist := displacement hc hR hh
    have hgap := stride_gap hr hh eq
    have ht := hc.dist_triangle (u:=x) (v:=R (first x)) (w:=y)
    have ht' := hc.dist_triangle (u:=R (first x)) (v:=R (first y)) (w:=y)
    rw [G.dist_comm (u:=R (first x)) (v:=x)] at e1
    omega
  have hbucket (j : ℕ) : ((A.filter (fun z => first z/r=j)).card:ℝ) ≤ (N:ℝ)^(δ/100) := by
    apply centers_in_batch hc (R:=outerRadius δ N (i.val+1)) (s:=q.base) (by positivity)
    · intro x hx y hy hh
      exact (net_spec G δ N i).2.1 _ (hcnet (mem_filter.mp hx).1) _ (hcnet (mem_filter.mp hy).1) hh
    · intro x hx y hy
      have h := near (mem_filter.mp hx).1 (mem_filter.mp hy).1 ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
      exact (Nat.add_le_add_right h _).trans pad
    · intro z hz
      exact (net_spec G δ N i).1 _ (hcnet (mem_filter.mp hz).1)
  have hcount := sum_bucket A (fun z => first z/r) (b:=stop/r+1)
    (fun z hz => Nat.lt_succ_of_le (Nat.div_le_div_right (ha hz).1))
  change (A.card:ℝ) ≤ _
  rw [← hcount,Nat.cast_sum]
  calc
    _ ≤ ∑ _ ∈ range (stop/r+1), (N:ℝ)^(δ/100) := sum_le_sum (fun j _ => hbucket j)
    _ = _ := by simp

theorem pad_le {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) :
    ∀ᶠ N : ℕ in atTop, ∀ i : Fin (levels δ), ∀ r ∈ radii δ N (i.val+1),
      2*(endTime (clockFactor δ) r+2*guardRadius δ N (i.val+1))+
      r+baseRadius δ N (i.val+1) ≤ outerRadius δ N (i.val+1) := by
  filter_upwards [scaleSeparation_eventually hδ ht (K:=1) (by norm_num) 0,
    eventually_ge_atTop (1:ℕ)] with N sep hN i r hr
  let s := guardRadius δ N (i.val+1)
  let A := dilation δ
  have hi : 1 ≤ i.val+1 := by omega
  have hk : i.val+1 ≤ levels δ := i.isLt
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have h1 := Real.one_le_rpow hn (gain_pos hδ ht).le
  have h2 := sep.support _ hi hk r hr
  simp only [pow_zero,mul_one,one_mul] at h2
  have hs : s ≤ r := by
    exact_mod_cast (show (s:ℝ) ≤ (r:ℝ) by
      apply le_trans _ h2; simpa using mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg s))
  have hgeom := (radii_bounds hδ ht hN hi hk hr).2
  have hA : A*r ≤ outerRadius δ N (i.val+1) := by
    apply Nat.cast_le (α:=ℝ) |>.mp
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hgeom (Nat.cast_nonneg A)).trans (Nat.le_ceil _)
  apply le_trans _ hA
  have : baseRadius δ N (i.val+1) ≤ r := (Nat.div_le_self s 4).trans hs
  change 2*(endTime (clockFactor δ) r+2*s)+r+baseRadius δ N (i.val+1) ≤ _
  have hcanon : baseRadius δ N (1+i.val) ≤ r := by simpa only [Nat.add_comm 1] using this
  dsimp [endTime,moveTime,leadTime,duration,A,dilation]
  ring_nf
  omega

end
end Meyniel.Multiscale
