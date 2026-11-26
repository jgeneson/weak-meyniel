module

public import Meyniel.MultiscaleSites
public import Meyniel.MultiscalePrices

/-! The radial incidence saving in a correct terminal trial. The anchor is
fixed by the already observed prefix. -/

@[expose] public section

namespace Meyniel.Multiscale
open Finset Interception
noncomputable section
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def radialSupport (G : SimpleGraph V) (A : Finset V) (x : V)
    (offset h width smoothing j : ℕ) : Finset V := by
  classical exact A.filter (fun y => offset+j*h < G.dist x y + width+smoothing ∧
    G.dist x y ≤ offset+j*h+2+smoothing)

omit [Fintype V] in
theorem radial_incidence (A : Finset V) (x : V) (M offset h width smoothing : ℕ)
    (hh : 0 < h) :
    (∑ j ∈ range M, (radialSupport G A x offset h width smoothing j).card) ≤
      A.card * ((width+2+2*smoothing)/h+1) := by
  classical
  apply support_incidence (range M) A _ (fun _ _ => filter_subset _ _) _
  intro y _
  apply spaced_band_card _ hh
  intro i hi j hj hij
  have hi' := (mem_filter.mp (mem_filter.mp hi).2).2.2
  have hj' := (mem_filter.mp (mem_filter.mp hj).2).2.1
  change G.dist x y ≤ offset+i*h+2+smoothing at hi'
  change offset+j*h < G.dist x y + width+smoothing at hj'
  rw [Nat.sub_mul]
  omega

omit [Fintype V] in
theorem log_support_saving {sites : Finset V} {S : ℕ → Finset V} {M N : ℕ} {g : ℝ}
    (hM : 0 < M) (hN : 0 < N) (pos : ∀ j < M, (S j).Nonempty)
    (total : ((∑ j ∈ range M, (S j).card : ℕ) : ℝ) * (N:ℝ)^g ≤ M*sites.card) :
    ∑ j ∈ range M, Real.log (S j).card ≤
      (M:ℝ)*(Real.log sites.card - g*Real.log N) := by
  let f j : ℝ := (S j).card
  let hne : (range M).Nonempty := ⟨0,mem_range.mpr hM⟩
  have hf (j) (hj : j ∈ range M) : 0 < f j := by dsimp [f]; exact_mod_cast (pos _ (mem_range.mp hj)).card_pos
  have hm := mean_pos hne hf
  have hjensen := sum_log_le_card_mul_log_mean hne hf
  rw [card_range] at hjensen
  apply hjensen.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hh := Real.rpow_pos_of_pos hn g
  have hmr : 0 < (M:ℝ) := by exact_mod_cast hM
  have hmean : mean (range M) f ≤ (sites.card:ℝ) / (N:ℝ)^g := by
    unfold mean
    rw [card_range]
    apply (div_le_div_iff₀ hmr hh).mpr
    push_cast at total
    simpa [f,mul_comm] using total
  have hsites : 0 < (sites.card:ℝ) := (div_pos_iff_of_pos_right hh).mp (hm.trans_le hmean)
  exact (Real.log_le_log hm hmean).trans_eq (by rw [Real.log_div hsites.ne' hh.ne',Real.log_rpow hn])

omit [Fintype V] in
theorem radial_log_saving (A : Finset V) (x : V) {M N : ℕ} (offset h width smoothing : ℕ)
    (g : ℝ) (hh : 0 < h) (hM : 0 < M) (hN : 0 < N)
    (pos : ∀ j < M, (radialSupport G A x offset h width smoothing j).Nonempty)
    (ratio : (((width+2+2*smoothing)/h+1 : ℕ) : ℝ)*(N:ℝ)^g ≤ M) :
    ∑ j ∈ range M, Real.log (radialSupport G A x offset h width smoothing j).card ≤
      (M:ℝ)*(Real.log A.card-g*Real.log N) := by
  apply log_support_saving hM hN pos
  have hInc := radial_incidence (G:=G) A x M offset h width smoothing hh
  have h' : ((∑ j ∈ range M, (radialSupport G A x offset h width smoothing j).card : ℕ) : ℝ) ≤
     (A.card : ℝ)*(((width+2+2*smoothing)/h+1 : ℕ) : ℝ) := by exact_mod_cast hInc
  have hn := Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) N) g
  calc _ ≤ _ := mul_le_mul_of_nonneg_right h' hn
       _ = (A.card:ℝ)*((((width+2+2*smoothing)/h+1 : ℕ) : ℝ)*(N:ℝ)^g) := by ring
       _ ≤ _ := by simpa [mul_comm] using mul_le_mul_of_nonneg_left ratio (Nat.cast_nonneg (α:=ℝ) A.card)

omit [Fintype V] in
theorem radial_at (hc : G.Connected) {R : ℕ → V} {x z : V} {F e a j h width smoothing : ℕ}
    (start : F ≤ a) (stop : a+j*h ≤ e) (anchor : R F = x)
    (band : InBand G R F e width) (near : G.dist (R (a+j*h+2)) z ≤ smoothing) :
    a-F+j*h < G.dist x z + width+smoothing ∧ G.dist x z ≤ a-F+j*h+2+smoothing := by
  have hB := band (a-F+j*h) (by omega)
  rw [show F+(a-F+j*h)+2=a+j*h+2 by omega,anchor] at hB
  exact smoothed_band hc x _ z hB.1 hB.2 near

theorem local_trial_volume (hc : G.Connected) (δ : ℝ) {r T R : ℕ} {z y : V}
    (hT : T = duration (clockFactor δ) r) (hR : R ≤ r) (hy : G.dist z y ≤ r) :
    Real.log (ball G z (r+T+R)).card ≤ logBall G y (dilation δ*r) := by
  apply Real.log_le_log (by exact_mod_cast (ball_nonempty (G:=G) z (r+T+R)).card_pos)
  apply Nat.cast_le.mpr
  apply card_le_card (ball_subset hc ?_)
  rw [SimpleGraph.dist_comm]
  rw [hT]
  unfold duration dilation
  rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul]
  omega
end
end Meyniel.Multiscale
