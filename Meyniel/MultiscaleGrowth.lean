module

public import Meyniel.MultiscaleGeometry
public import Meyniel.MultiscaleSeparation

/-! # The two ball-growth averages

The first bound sums over radii within a level. The second counts those levels
where the ball expands by more than the given factor at one fixed vertex.
-/

@[expose] public section

namespace Meyniel.Multiscale

open Filter Finset

noncomputable section
variable {V : Type*} [Fintype V]

def logBall (G : SimpleGraph V) (y : V) (r : ℕ) : ℝ := Real.log (ball G y r).card

theorem logBall_mono (G : SimpleGraph V) (y : V) : Monotone (logBall G y) := by
  intro r s hrs
  apply Real.log_le_log (by exact_mod_cast (ball_nonempty (G:=G) y r).card_pos)
  exact_mod_cast Finset.card_le_card (show ball G y r ⊆ ball G y s from
    fun _ hx => mem_ball.mpr ((mem_ball.mp hx).trans hrs))

theorem logBall_bound (G : SimpleGraph V) (y : V) (r : ℕ) {N : ℕ} (hN : Fintype.card V ≤ N) :
    0 ≤ logBall G y r ∧ logBall G y r ≤ Real.log N := by
  have hp : 0 < ((ball G y r).card : ℝ) := by exact_mod_cast (ball_nonempty (G:=G) y r).card_pos
  exact ⟨Real.log_nonneg (by exact_mod_cast (ball_nonempty (G:=G) y r).card_pos),
    Real.log_le_log hp (by exact_mod_cast (Finset.card_le_univ _).trans hN)⟩

def growth (G : SimpleGraph V) (y : V) (A r : ℕ) : ℝ :=
  logBall G y (A*r) - logBall G y r

private theorem consecutive_sum (f : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ range k, (f (i+1) - f i) = f k - f 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ,ih]; ring

theorem radius_growth_sum (G : SimpleGraph V) (y : V) {N : ℕ} (hN : Fintype.card V ≤ N)
    (δ : ℝ) (i : ℕ) :
    ∑ r ∈ radii δ N i, growth G y (dilation δ) r ≤ Real.log N := by
  let b := radiusBase δ
  let hi := maxRadiusExp δ i
  let k := ⌊hi * Real.logb b N⌋₊ + 1
  let f (j : ℕ) := logBall G y (b^j)
  have hb := radiusBase_ge δ
  have hm := logBall_mono G y
  have step (j : ℕ) : f j ≤ f (j+1) := by
    apply hm
    exact Nat.pow_le_pow_right (by dsimp [b]; omega) (by omega)
  unfold radii geometricRange
  rw [Finset.sum_image (Nat.pow_right_injective hb).injOn]
  calc
    _ ≤ ∑ j ∈ indices b N (minRadiusExp δ i) hi, (f (j+1)-f j) := by
      apply sum_le_sum; intro j _
      apply sub_le_sub_right (hm _) _
      change dilation δ * b^j ≤ b^(j+1)
      rw [pow_succ, mul_comm]
      apply Nat.mul_le_mul_left
      dsimp [b,radiusBase]; omega
    _ ≤ ∑ j ∈ range k, (f (j+1)-f j) :=
      sum_le_sum_of_subset_of_nonneg (fun j hj => mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hj).2))
        (fun j _ _ => sub_nonneg.mpr (step j))
    _ = _ := consecutive_sum f k
    _ ≤ _ := by
      have ma := (logBall_bound G y (b^k) hN).2
      have mi := (logBall_bound G y (b^0) hN).1
      dsimp [f]; simp only [pow_zero] at mi; linarith

def outerRadius (δ : ℝ) (N i : ℕ) : ℕ :=
  ⌈(dilation δ : ℝ) * (N:ℝ)^maxRadiusExp δ i⌉₊

def baseRadius (δ : ℝ) (N i : ℕ) : ℕ := guardRadius δ N i / 4

theorem adjacent_annuli {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 1 ≤ i → i+1 ≤ levels δ →
      outerRadius δ N i ≤ baseRadius δ N (i+1) := by
  let A : ℝ := dilation δ
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hτ := margin_pos hδ
  filter_upwards [polylog_le_power hτ (show 0 < 8*(A+1) by positivity) 0, eventually_ge_atTop 1]
    with N hpow hN i hi hk
  simp only [pow_zero,mul_one] at hpow
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hxn : (0:ℝ) < N := by linarith
  have posβ : 0 ≤ maxRadiusExp δ i := by
    obtain ⟨h1,h2,h3,_⟩ := radius_exponents hδ ht i hi (by omega)
    linarith
  let v := (N:ℝ)^maxRadiusExp δ i
  have hv : 1 ≤ v := Real.one_le_rpow hn posβ
  have hv0 : 0 ≤ v := by linarith
  have hlow : (8*(A+1))*v ≤ (guardRadius δ N (i+1) : ℝ) := by
    calc
      _ ≤ (N:ℝ)^margin δ * v := mul_le_mul_of_nonneg_right hpow hv0
      _ = (N:ℝ)^(margin δ+maxRadiusExp δ i) := (Real.rpow_add hxn ..).symm
      _ ≤ (N:ℝ)^guardRadiusExp δ (i+1 : ℕ) :=
        Real.rpow_le_rpow_of_exponent_le hn (by linarith [next_guard_exponent δ i])
      _ ≤ _ := Nat.le_ceil _
  have hup : (outerRadius δ N i : ℝ) ≤ A*v+1 := (Nat.ceil_lt_add_one (mul_nonneg hA hv0)).le
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mpr
  exact_mod_cast (show (outerRadius δ N i : ℝ)*4 ≤ (guardRadius δ N (i+1) : ℝ) by
    nlinarith [mul_nonneg hA hv0])

def badLevels (G : SimpleGraph V) (y : V) (δ : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 (levels δ)).filter (fun i =>
    δ/100 * Real.log N < logBall G y (outerRadius δ N i) - logBall G y (baseRadius δ N i))

private theorem sum_gaps (k : ℕ) (L U : ℕ → ℝ) (cap : ℝ)
    (hL : 0 ≤ L 0) (hU : ∀ j < k, U j ≤ cap)
    (hgap : ∀ j, j+1 < k → U j ≤ L (j+1)) (hc : 0 ≤ cap) :
    ∑ j ∈ range k, (U j-L j) ≤ cap := by
  cases k with
  | zero => simpa using hc
  | succ k =>
    have h : ∑ j ∈ range (k+1), (U j-L j) ≤ U k-L 0 := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [sum_range_succ]
        have h' := ih (fun j hj => hU j (by omega)) (fun j hj => hgap j (by omega))
        linarith [hgap k (by omega)]
    linarith [hU k (by omega)]

/-- Uniform in the vertex and the graph below the order cap. -/
theorem few_bad_levels_of_adjacent {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100)
    {N : ℕ} (hN : 2 ≤ N) (hsep : ∀ i : ℕ, 1 ≤ i → i+1 ≤ levels δ →
      outerRadius δ N i ≤ baseRadius δ N (i+1))
    (G : SimpleGraph V) (hsize : Fintype.card V ≤ N) (y : V) :
      ((badLevels G y δ N).card : ℝ) ≤ 100/δ := by
  classical
  have hln : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  let L (j : ℕ) := logBall G y (baseRadius δ N (j+1))
  let U (j : ℕ) := logBall G y (outerRadius δ N (j+1))
  let K := levels δ
  let f (j : ℕ) : ℝ := max 0 (U j-L j)
  have hsum : ∑ j ∈ range K, f j ≤ Real.log N := by
    have h := sum_gaps K L (fun j => max (L j) (U j)) (Real.log N)
      (logBall_bound G y _ hsize).1
      (fun j _ => max_le (logBall_bound G y _ hsize).2 (logBall_bound G y _ hsize).2) ?_ hln.le
    · simpa only [f,← max_sub_sub_right,sub_self] using h
    · intro j hj
      have h1 := hsep (j+1) (by omega) (by dsimp [K] at hj; omega)
      have hLmono : baseRadius δ N (j+1) ≤ baseRadius δ N (j+1+1) := by
        apply Nat.div_le_div_right
        apply Nat.ceil_mono
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
        unfold guardRadiusExp
        have hd : 0 ≤ logGap δ := div_nonneg (by linarith) (Nat.cast_nonneg _)
        push_cast; linarith
      exact max_le (logBall_mono G y hLmono) (logBall_mono G y h1)
  let B := badLevels G y δ N
  let B' := (range K).filter (fun j => j+1 ∈ B)
  have ecard : B'.card = B.card := by
    have eq : B = B'.image (·+1) := by
      ext i; constructor
      · intro hi
        have hmem : i ∈ Icc 1 K := (mem_filter.mp hi).1
        obtain ⟨hi1,hik⟩ := mem_Icc.mp hmem
        refine mem_image.mpr ⟨i-1,mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩,by omega⟩
        rwa [Nat.sub_add_cancel hi1]
      · intro hi
        obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
        exact (mem_filter.mp hj).2
    rw [eq,card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)]
  have hcnt : (B.card : ℝ)*(δ/100*Real.log N) ≤ Real.log N := by
    calc
      _ = ∑ _ ∈ B', δ/100*Real.log N := by simp [ecard]
      _ ≤ ∑ j ∈ B', f j := by
        apply sum_le_sum; intro j hj
        have hj' : j+1 ∈ badLevels G y δ N := (mem_filter.mp hj).2
        exact (mem_filter.mp hj').2.le.trans (le_max_right _ _)
      _ ≤ ∑ j ∈ range K, f j := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => le_max_left _ _)
      _ ≤ _ := hsum
  change (B.card:ℝ) ≤ 100/δ
  apply (le_div_iff₀ hδ).mpr
  nlinarith only [hcnt,hln, mul_pos hδ hln]

/-- The threshold is uniform in the order-capped graph, including its vertex type. -/
theorem few_bad_levels {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) :
    ∀ᶠ N : ℕ in atTop, ∀ (W : Type*) [Fintype W] (G : SimpleGraph W),
      Fintype.card W ≤ N → ∀ y : W, ((badLevels G y δ N).card:ℝ) ≤ 100/δ := by
  filter_upwards [adjacent_annuli hδ ht,eventually_ge_atTop 2] with N hsep hN
  exact fun _ _ => few_bad_levels_of_adjacent hδ ht hN hsep

end
end Meyniel.Multiscale
