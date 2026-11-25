import Meyniel.MultiscaleParameters

/-! # Geometric ranges of physical radii

The cardinality lower bound is uniform over levels. It pays for the sum of
logarithmic volume increments when a radius is chosen uniformly from a range.
-/

namespace Meyniel.Multiscale

open Filter Finset

noncomputable section

def dilation (δ : ℝ) : ℕ := 100*(clockFactor δ+1)

def radiusBase (δ : ℝ) : ℕ := 2*dilation δ+1

def indices (b N : ℕ) (lo hi : ℝ) : Finset ℕ :=
  Icc ⌈lo*Real.logb b N⌉₊ ⌊hi*Real.logb b N⌋₊

def geometricRange (b N : ℕ) (lo hi : ℝ) : Finset ℕ :=
  (indices b N lo hi).image (b^·)

def radii (δ : ℝ) (N i : ℕ) : Finset ℕ :=
  geometricRange (radiusBase δ) N (minRadiusExp δ i) (maxRadiusExp δ i)

def guardRadius (δ : ℝ) (N i : ℕ) : ℕ := ⌈(N:ℝ)^guardRadiusExp δ i⌉₊

theorem radiusBase_ge (δ : ℝ) : 2 ≤ radiusBase δ := by unfold radiusBase dilation; omega

theorem geometricRange_bounds {b N r : ℕ} {lo hi : ℝ} (hb : 2 ≤ b) (hN : 0 < N)
    (hhi : 0 ≤ hi) (hmem : r ∈ geometricRange b N lo hi) :
    (N:ℝ)^lo ≤ r ∧ (r:ℝ) ≤ (N:ℝ)^hi := by
  have hb' : (1:ℝ) < b := by exact_mod_cast hb
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  rcases mem_image.mp hmem with ⟨j,hj,rfl⟩
  have hj' := mem_Icc.mp hj
  have hlow : lo*Real.logb b N ≤ j := (Nat.le_ceil _).trans (Nat.cast_le.mpr hj'.1)
  have hlog : 0 ≤ Real.logb b N := Real.logb_nonneg hb' hN₁
  have hupp : (j:ℝ) ≤ hi*Real.logb b N :=
    (Nat.cast_le.mpr hj'.2).trans (Nat.floor_le (mul_nonneg hhi hlog))
  have hx (e : ℝ) : Real.logb b ((N:ℝ)^e) = e * Real.logb b N :=
    Real.logb_rpow_eq_mul_logb_of_pos hN'
  constructor
  · have h := (Real.logb_le_iff_le_rpow hb' (Real.rpow_pos_of_pos hN' lo)).mp ((hx _).trans_le hlow)
    simpa using h
  · have h := (Real.le_logb_iff_rpow_le hb' (Real.rpow_pos_of_pos hN' hi)).mp (hupp.trans_eq (hx _).symm)
    simpa using h

/-- Counts powers of a fixed base in any polynomial annulus. -/
theorem geometricRange_card {b N : ℕ} {lo hi : ℝ} (hb : 2 ≤ b) (hN : 0 < N)
    (hlo : 0 ≤ lo) :
    (hi-lo)*Real.logb b N - 1 ≤ ((geometricRange b N lo hi).card:ℝ) := by
  have hb' : (1:ℝ) < b := by exact_mod_cast hb
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.logb b N := Real.logb_nonneg hb' hN₁
  have low := Nat.ceil_lt_add_one (mul_nonneg hlo hlog)
  have upper := Nat.lt_floor_add_one (hi*Real.logb b N)
  rw [geometricRange, Finset.card_image_of_injective _ (Nat.pow_right_injective hb), indices, Nat.card_Icc]
  have s : ⌊hi*Real.logb b N⌋₊ + 1 ≤
      ⌊hi*Real.logb b N⌋₊ + 1 - ⌈lo*Real.logb b N⌉₊ + ⌈lo*Real.logb b N⌉₊ := by omega
  have s' := (Nat.cast_le (α:=ℝ)).mpr s
  push_cast only [Nat.cast_add,Nat.cast_one] at s'
  linarith

theorem margin_pos {δ : ℝ} (hδ : 0 < δ) : 0 < margin δ := by
  unfold margin
  exact div_pos hδ (mul_pos (by norm_num) (by exact_mod_cast levels_pos hδ))

theorem radius_exponents {δ : ℝ} (hδ : 0 < δ) (hmax : δ < 1/100) :
    ∀ i : ℕ, 1 ≤ i → i ≤ levels δ →
      0 < guardRadiusExp δ i ∧ guardRadiusExp δ i < minRadiusExp δ i ∧
      minRadiusExp δ i < maxRadiusExp δ i ∧ maxRadiusExp δ i < 1/3-δ := by
  intro i hi hk
  have hΔ : 0 < logGap δ := by
    unfold logGap
    apply div_pos (by linarith); exact_mod_cast levels_pos hδ
  have hτ := margin_pos hδ
  have hi' : (1:ℝ) ≤ i := by exact_mod_cast hi
  have hk' : (i:ℝ) ≤ levels δ := by exact_mod_cast hk
  have h0 : 0 < guardRadiusExp δ i := add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hi') hΔ.le) hτ
  have hgap := band_gain δ (i:ℝ)
  have hg := gain_pos hδ hmax
  refine ⟨h0, by linarith, ?_, ?_⟩
  · unfold maxRadiusExp minRadiusExp; linarith
  · have hp : (levels δ : ℝ) * logGap δ = 1/3-2*δ := by
      dsimp [logGap]; field_simp [show (levels δ : ℝ) ≠ 0 by exact_mod_cast (levels_pos hδ).ne']
    have h := mul_le_mul_of_nonneg_right hk' hΔ.le
    rw [hp] at h
    unfold maxRadiusExp; linarith

theorem next_guard_exponent (δ : ℝ) (i : ℕ) :
    guardRadiusExp δ (i+1 : ℕ) - maxRadiusExp δ i = 3 * margin δ / 2 := by
  unfold guardRadiusExp maxRadiusExp
  push_cast
  ring

theorem radii_bounds {δ : ℝ} {N i r : ℕ} (hδ : 0 < δ) (ht : δ < 1/100) (hn : 0 < N)
    (hi : 1 ≤ i) (hk : i ≤ levels δ) (hr : r ∈ radii δ N i) :
    (N:ℝ)^minRadiusExp δ i ≤ r ∧ (r:ℝ) ≤ (N:ℝ)^maxRadiusExp δ i := by
  obtain ⟨hh,ha,hb,_⟩ := radius_exponents hδ ht i hi hk
  exact geometricRange_bounds (radiusBase_ge _) hn ((hh.trans ha).trans hb).le hr

/-- Uniform lower bound by a positive multiple of log N, over all levels at once. -/
theorem many_radii {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 1 ≤ i → i ≤ levels δ →
      c*Real.log N ≤ ((radii δ N i).card : ℝ) := by
  let b := radiusBase δ
  have hb : 1 < (b:ℝ) := by exact_mod_cast radiusBase_ge δ
  have hτ := margin_pos hδ
  let c := margin δ / (4 * Real.log b)
  have hc : 0 < c := div_pos hτ (mul_pos (by norm_num) (Real.log_pos hb))
  refine ⟨c, hc, ?_⟩
  have hT := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hT.eventually_ge_atTop (1/c), eventually_ge_atTop 1] with N hN hn
  change 1/c ≤ Real.log N at hN
  have one : 1 ≤ c * Real.log N := by simpa [mul_comm] using (div_le_iff₀ hc).mp hN
  intro i hi hk
  obtain ⟨hh,ha,_,_⟩ := radius_exponents hδ ht i hi hk
  have lower := geometricRange_card (radiusBase_ge δ) hn (hh.trans ha).le (hi:=maxRadiusExp δ i)
  change c * Real.log N ≤ ((geometricRange b N (minRadiusExp δ i) (maxRadiusExp δ i)).card:ℝ)
  have hdiff : maxRadiusExp δ i - minRadiusExp δ i = margin δ / 2 := by
    unfold maxRadiusExp minRadiusExp; ring
  rw [hdiff,Real.logb] at lower
  have he : margin δ/2 * (Real.log N / Real.log b) = 2 * (c * Real.log N) := by dsimp [c]; ring
  change margin δ/2 * (Real.log N / Real.log b) - 1 ≤ _ at lower
  rw [he] at lower
  linarith

end
end Meyniel.Multiscale
