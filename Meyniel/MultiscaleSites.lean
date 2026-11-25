import Meyniel.MultiscaleTiming

/-! # The physical scales and the separated sets of potential guard sites -/

namespace Meyniel.Multiscale
open Finset
noncomputable section
variable {V : Type*} [Fintype V]

def physicalScale (G : SimpleGraph V) (δ : ℝ) (N : ℕ) (i : Fin (levels δ)) : GuardScale V where
  radii := radii δ N (i.val+1)
  lead := leadTime (clockFactor δ)
  last := endTime (clockFactor δ)
  base := guardRadius δ N (i.val+1)
  run := windowTime N (guardRadius δ N (i.val+1))
  width := bandWidth N (guardRadius δ N (i.val+1))
  good y := ((ball G y (outerRadius δ N (i.val+1))).card:ℝ) ≤
    (N:ℝ)^(δ/100) * (ball G y (baseRadius δ N (i.val+1))).card

theorem physicalScale_good_iff (G : SimpleGraph V) (δ : ℝ) {N : ℕ} (hN : 0 < N)
    (i : Fin (levels δ)) (y : V) :
    (physicalScale G δ N i).good y ↔ i.val+1 ∉ badLevels G y δ N := by
  classical
  let j := i.val+1
  let b : ℝ := (ball G y (baseRadius δ N j)).card
  let B : ℝ := (ball G y (outerRadius δ N j)).card
  have hb : 0 < b := by dsimp [b]; exact_mod_cast (ball_nonempty (G:=G) y _).card_pos
  have hB : 0 < B := by dsimp [B]; exact_mod_cast (ball_nonempty (G:=G) y _).card_pos
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hi : j ∈ Icc 1 (levels δ) := mem_Icc.mpr ⟨by dsimp [j]; omega,i.isLt⟩
  change B ≤ (N:ℝ)^(δ/100)*b ↔ j ∉ badLevels G y δ N
  rw [badLevels,mem_filter,and_iff_right hi,not_lt,← Real.log_le_log_iff hB (mul_pos (Real.rpow_pos_of_pos hn _) hb),
    Real.log_mul (Real.rpow_pos_of_pos hn _).ne' hb.ne',Real.log_rpow hn]
  change Real.log B ≤ δ/100*Real.log N + Real.log b ↔ Real.log B - Real.log b ≤ δ/100*Real.log N
  constructor <;> intro h <;> linarith

/-- The same separated set of good vertices is used for all radii in a level. -/
def net (G : SimpleGraph V) (δ : ℝ) (N : ℕ) (i : Fin (levels δ)) : Finset V := by
  classical
  let q := physicalScale G δ N i
  exact (centers_exist (G:=G) (univ.filter q.good) q.base).choose

theorem net_spec (G : SimpleGraph V) (δ : ℝ) (N : ℕ) (i : Fin (levels δ)) :
    let q := physicalScale G δ N i
    let C := net G δ N i
    (∀ y ∈ C, q.good y) ∧
    (∀ x ∈ C, ∀ y ∈ C, x ≠ y → q.base < G.dist x y) ∧
    ∀ y, q.good y → ∃ z ∈ C, G.dist y z ≤ q.base := by
  classical
  let q := physicalScale G δ N i
  obtain ⟨hsub,hsep,hcov⟩ := (centers_exist (G:=G) (univ.filter q.good) q.base).choose_spec
  exact ⟨fun y hy => (mem_filter.mp (hsub hy)).2,hsep,
    fun y hy => hcov y (mem_filter.mpr ⟨mem_univ _,hy⟩)⟩

abbrev SiteIndex (G : SimpleGraph V) (δ : ℝ) (N : ℕ) :=
  (i : Fin (levels δ)) × (radii δ N (i.val+1)) × (net G δ N i)

/-- Deterministic walk covers absorb the additive rounding by taking one more
cop than the ceiling of their unrounded budget. -/
def siteCount (δ : ℝ) (N j m : ℕ) : ℕ :=
  ⌈((windowTime N (guardRadius δ N j)+3 : ℕ):ℝ) * Real.log N *
    Real.sqrt m * (N:ℝ)^(δ/200 - ((j:ℝ)-1)*gain δ/2+δ/20)⌉₊ + 1

def staggeredCopies (N s : ℕ) : ℕ := 6*windowTime N s/s+2

def globalCount (δ : ℝ) (N : ℕ) : ℕ :=
  ⌈((windowTime N (cutoff N δ)+3 : ℕ):ℝ) * Real.log N *
    (N:ℝ)^(1/2-(levels δ:ℝ)*gain δ/2+δ/20)⌉₊+1

end
end Meyniel.Multiscale
