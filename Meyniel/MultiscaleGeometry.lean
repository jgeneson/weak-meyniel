module

public import Meyniel.Game

/-! Ball packing, radial support multiplicities, and the costs of the guards
in the multiscale argument. All distances are in the graph in which the
current game is played. -/

@[expose] public section

namespace Meyniel.Multiscale
open Finset
noncomputable section
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A finite closed ball in the intrinsic graph distance. -/
def ball (G : SimpleGraph V) (z : V) (r : ℕ) : Finset V := by
  classical
  exact univ.filter (fun y => G.dist z y ≤ r)

@[simp] theorem mem_ball {z x : V} {r : ℕ} : x ∈ ball G z r ↔ G.dist z x ≤ r := by
  classical
  simp [ball]

theorem ball_nonempty (z : V) (r : ℕ) : (ball G z r).Nonempty := ⟨z, by simp⟩

theorem ball_subset {x y : V} {r R : ℕ} (hc : G.Connected) (h : G.dist x y + r ≤ R) :
    ball G y r ⊆ ball G x R := by
  intro z hz
  exact mem_ball.mpr ((hc.dist_triangle (v:=y)).trans
    ((Nat.add_le_add_left (mem_ball.mp hz) _).trans h))

/-- A maximal separated subfamily of good centers covers every good vertex. -/
theorem centers_exist (good : Finset V) (s : ℕ) :
    ∃ C ⊆ good, (∀ x ∈ C, ∀ y ∈ C, x ≠ y → s < G.dist x y) ∧
      ∀ v ∈ good, ∃ z ∈ C, G.dist v z ≤ s := by
  classical
  let sep := fun C : Finset V => ∀ x ∈ C, ∀ y ∈ C, x ≠ y → s < G.dist x y
  let pool := good.powerset.filter sep
  have hem : ∅ ∈ pool := by simp [pool,sep]
  obtain ⟨C,hC,hmax⟩ := pool.exists_max_image Finset.card ⟨_,hem⟩
  obtain ⟨hsub,hsep⟩ := mem_filter.mp hC
  refine ⟨C,mem_powerset.mp hsub,hsep,?_⟩
  intro v hgood
  by_contra! hn
  have hv : v ∉ C := by
    intro h
    simpa using hn v h
  have hi : insert v C ∈ pool := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (insert_subset hgood (mem_powerset.mp hsub)),?_⟩
    intro x hx y hy hxy
    by_cases ex : x = v
    · subst x
      exact hn y ((mem_insert.mp hy).resolve_left (Ne.symm hxy))
    · have hx' := (mem_insert.mp hx).resolve_left ex
      by_cases ey : y = v
      · subst y
        rw [SimpleGraph.dist_comm]
        exact hn x hx'
      · exact hsep x hx' y ((mem_insert.mp hy).resolve_left ey) hxy
  have hh := hmax _ hi
  rw [card_insert_of_notMem hv] at hh
  omega

theorem base_balls_disjoint (hc : G.Connected) {s : ℕ} {C : Finset V}
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → s < G.dist x y) :
    (C : Set V).PairwiseDisjoint (fun z => ball G z (s/4)) := by
  intro x hx y hy hxy
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  have h1 := mem_ball.mp hv
  have h2 := mem_ball.mp hv'
  have h3 := hc.dist_triangle (u:=x) (v:=v) (w:=y)
  rw [@SimpleGraph.dist_comm _ G v y] at h3
  have := hsep x hx y hy hxy
  omega

theorem base_mass_le (hc : G.Connected) {s : ℕ} {C : Finset V}
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → s < G.dist x y) :
    (∑ z ∈ C, (ball G z (s/4)).card) ≤ Fintype.card V := by
  classical
  rw [← card_biUnion (base_balls_disjoint hc hsep)]
  exact card_le_univ _

/-- The newly dispatched centers in one launch interval all fit in the
large good ball of the member having smallest base volume. -/
theorem centers_in_batch (hc : G.Connected) {s R : ℕ} {C : Finset V} {growth : ℝ}
    (hg : 0 ≤ growth)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → s < G.dist x y)
    (hclose : ∀ x ∈ C, ∀ y ∈ C, G.dist x y + s/4 ≤ R)
    (hgood : ∀ z ∈ C, ((ball G z R).card : ℝ) ≤ growth * (ball G z (s/4)).card) :
    (C.card : ℝ) ≤ growth := by
  classical
  by_cases hne : C.Nonempty
  · obtain ⟨z,hz,hmin⟩ := C.exists_min_image (fun v => (ball G v (s/4)).card) hne
    have hl := C.card_nsmul_le_sum (fun v => (ball G v (s/4)).card) _ hmin
    rw [nsmul_eq_mul, ← card_biUnion (base_balls_disjoint hc hsep)] at hl
    have hsub : C.biUnion (fun y => ball G y (s/4)) ⊆ ball G z R := by
      intro v hv
      obtain ⟨y,hy,hm⟩ := mem_biUnion.mp hv
      exact ball_subset hc (hclose z hz y hy) hm
    have hreal : (C.card : ℝ) * ((ball G z (s/4)).card : ℝ) ≤ (ball G z R).card := by
      exact_mod_cast hl.trans (card_le_card hsub)
    have hpos : (0:ℝ) < (ball G z (s/4)).card := by exact_mod_cast (ball_nonempty z (s/4)).card_pos
    exact (mul_le_mul_iff_left₀ hpos).mp (hreal.trans (hgood z hz))
  · simpa [not_nonempty_iff_eq_empty.mp hne] using hg

theorem sqrt_base_mass_le (hc : G.Connected) {s : ℕ} {C : Finset V}
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → s < G.dist x y) :
    ∑ z ∈ C, Real.sqrt (ball G z (s/4)).card ≤
      Real.sqrt C.card * Real.sqrt (Fintype.card V) := by
  have h := Real.sum_sqrt_mul_sqrt_le C (f:=fun _ => 1) (g:=fun v => ((ball G v (s/4)).card : ℝ))
    (fun _ => zero_le_one) (fun _ => Nat.cast_nonneg _)
  simp only [Real.sqrt_one, one_mul, sum_const, nsmul_eq_mul, mul_one] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  exact_mod_cast base_mass_le hc hsep

omit [Fintype V] in
/-- Double-count support incidences by time and by vertex. -/
theorem support_incidence {I : Type*} [DecidableEq V] (times : Finset I) (sites : Finset V)
    (S : I → Finset V) (hsub : ∀ i ∈ times, S i ⊆ sites) (B : ℕ)
    (hfreq : ∀ z ∈ sites, (times.filter (fun i => z ∈ S i)).card ≤ B)
    :
    ∑ i ∈ times, (S i).card ≤ sites.card * B := by
  classical
  calc
    _ = ∑ i ∈ times, ∑ _z ∈ S i, 1 := by simp
    _ = ∑ z ∈ sites, ∑ _i ∈ times.filter (fun i => z ∈ S i), 1 := by
      apply Finset.sum_comm'
      intro i z
      simp only [mem_filter]
      exact ⟨fun h => ⟨h,hsub i h.1 h.2⟩,fun h => h.1⟩
    _ ≤ _ := by simpa using sites.sum_le_card_nsmul (fun z => (times.filter (fun i => z ∈ S i)).card) B hfreq

/-- A fixed distance can occur in only a bounded number of equally spaced
columns of a band. Time is translated before taking a natural difference. -/
theorem spaced_band_card (I : Finset ℕ) {h width : ℕ} (hh : 0 < h)
    (hband : ∀ i ∈ I, ∀ j ∈ I, i ≤ j → (j-i)*h ≤ width) :
    I.card ≤ width/h + 1 := by
  classical
  by_cases hI : I.Nonempty
  · obtain ⟨a,ha,hm⟩ := I.exists_min_image id hI
    have bound (i : ℕ) (hi : i ∈ I) : i - a ≤ width/h :=
      (Nat.le_div_iff_mul_le hh).mpr (hband a ha i hi (hm i hi))
    have hcard := Finset.card_le_card_of_injOn (s:=I) (t:=range (width/h+1)) (fun i => i-a)
      (fun i hi => mem_range.mpr (Nat.lt_succ_of_le (bound i hi)))
      (fun i hi j hj he => by have := hm i hi; have := hm j hj; dsimp at *; omega)
    simpa using hcard
  · simp [not_nonempty_iff_eq_empty.mp hI]

omit [Fintype V] in
/-- A time-smoothed vertex in a band lies within the corresponding enlarged
radial interval. This applies to every support element, under any input law. -/
theorem smoothed_band (hc : G.Connected) (x y z : V) {l w r : ℕ}
    (hl : l < G.dist x y + w) (hu : G.dist x y ≤ l+2) (hr : G.dist y z ≤ r) :
    l < G.dist x z + w + r ∧ G.dist x z ≤ l+2+r := by
  have a := hc.dist_triangle (u:=x) (v:=y) (w:=z)
  have b := hc.dist_triangle (u:=x) (v:=z) (w:=y)
  rw [@SimpleGraph.dist_comm _ G z y] at b
  omega

end
end Meyniel.Multiscale
