module

public import Mathlib

/-! # The exponent budget of the multiscale argument -/

@[expose] public section

noncomputable section

namespace Meyniel.Multiscale

/-- The number of levels used for an exponent slack `δ`. -/
def levels (δ : ℝ) : ℕ := ⌈100000 / δ^2⌉₊

def logGap (δ : ℝ) : ℝ := (1/3 - 2*δ) / levels δ

def margin (δ : ℝ) : ℝ := δ / (1000 * levels δ)

def gain (δ : ℝ) : ℝ := logGap δ - 3 * margin δ

def guardRadiusExp (δ i : ℝ) : ℝ := (i-1) * logGap δ + margin δ

def minRadiusExp (δ i : ℝ) : ℝ := i * logGap δ - margin δ

def maxRadiusExp (δ i : ℝ) : ℝ := i * logGap δ - margin δ/2

def clockFactor (δ : ℝ) : ℕ := ⌈100000 * ((levels δ : ℝ) + 1) / δ⌉₊

theorem levels_pos {δ : ℝ} (hδ : 0 < δ) : 0 < levels δ := by
  apply Nat.ceil_pos.mpr
  positivity

theorem gain_mul_levels {δ : ℝ} (hδ : 0 < δ) :
    gain δ * levels δ = 1/3 - 2*δ - 3*δ/1000 := by
  have hk : (levels δ : ℝ) ≠ 0 := by exact_mod_cast (levels_pos hδ).ne'
  dsimp [gain,logGap,margin]
  field_simp [hk]

theorem gain_pos {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) : 0 < gain δ := by
  have hk : 0 < (levels δ : ℝ) := by exact_mod_cast levels_pos hδ
  have h := gain_mul_levels hδ
  by_contra! hc
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hk.le]

theorem band_gain (δ i : ℝ) :
    minRadiusExp δ i - guardRadiusExp δ i = gain δ + margin δ := by
  unfold minRadiusExp guardRadiusExp gain
  ring

theorem guard_exponent {δ i : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) (hi : i ≤ levels δ) :
    1/2 + (1/3-δ)/2 + guardRadiusExp δ i - minRadiusExp δ i/2 -
        (i-1)*gain δ/2 + δ/100 + δ/20 ≤ 2/3-δ/4 := by
  have hk : 0 < (levels δ : ℝ) := by exact_mod_cast levels_pos hδ
  have hm : 0 ≤ margin δ := by unfold margin; positivity
  have bound : i * margin δ ≤ δ/1000 := by
    calc i * margin δ ≤ (levels δ : ℝ) * margin δ := mul_le_mul_of_nonneg_right hi hm
         _ = δ/1000 := by dsimp [margin]; field_simp [hk.ne']
  have hg : 0 ≤ logGap δ := div_nonneg (by linarith) hk.le
  unfold guardRadiusExp minRadiusExp gain
  nlinarith only [hg, bound, hδ]

theorem window_exponent {δ : ℝ} (hδ : 0 < δ) :
    (1/3-δ) + 1/2 - (levels δ : ℝ) * gain δ / 2 + δ/20 =
      2/3 + (103/2000) * δ := by
  linarith [show (levels δ : ℝ) * gain δ = 1/3-2*δ-3*δ/1000 by
    rw [mul_comm, gain_mul_levels hδ]]

/-- Total exponent loss caused by imperfect clocks and endpoints at bad scales.
The spare factor absorbs the bounded error divided by log of the order cap. -/
theorem loss_budget {δ : ℝ} (hδ : 0 < δ) (_ht : δ < 1/100) :
    (9*(levels δ:ℝ)+1)/clockFactor δ + 4*gain δ/(δ/100) < δ/100 := by
  let k : ℝ := levels δ
  have hk : 0 < k := by dsimp [k]; exact_mod_cast levels_pos hδ
  have hlevel : 100000 / δ^2 ≤ k := Nat.le_ceil _
  have hprod : 100000 ≤ k * δ^2 := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hlevel
  have hclock : 100000 * (k+1) / δ ≤ (clockFactor δ : ℝ) := Nat.le_ceil _
  have hcl : 0 < (clockFactor δ : ℝ) := lt_of_lt_of_le (div_pos (by positivity) hδ) hclock
  have hcost : (9*k+1)/clockFactor δ ≤ δ/10000 := by
    apply (div_le_iff₀ hcl).mpr
    nlinarith [(div_le_iff₀ hδ).mp hclock]
  have hg : gain δ * k = 1/3-2*δ-3*δ/1000 := gain_mul_levels hδ
  have he : 4*gain δ/(δ/100) ≤ δ/500 := by
    apply (div_le_iff₀ (by positivity)).mpr
    apply (mul_le_mul_iff_left₀ hk).mp
    nlinarith only [hprod,hg,hδ]
  change (9*k+1)/clockFactor δ + 4*gain δ/(δ/100) < δ/100
  linarith

end Meyniel.Multiscale
