import Meyniel.MultiscaleTrialPrice
import Meyniel.MultiscaleOffset

/-! The root offset bounds each time's weight uniformly, even after every
fixed translation by lower clocks. This pays only once for all bad levels. -/

namespace Meyniel.Multiscale
open Finset Filter Interception
noncomputable section
variable {V : Type*} [Fintype V]

def rootMean (δ : ℝ) (N i T : ℕ) (f : (r ξ b : ℕ) → ℝ) : ℝ :=
  mean (radii δ N i) (fun r =>
    let h := leadTime (clockFactor δ) r
    let B := moveTime (clockFactor δ) r
    let M := clockCount T 2 h
    mean (range h) (fun ξ => mean (range (Clock.top B h M + 1)) (fun b => f r ξ b)))

def rootEnd (δ : ℝ) (u r ξ b : ℕ) : ℕ :=
  let h := leadTime (clockFactor δ) r
  u + ξ + h + (Clock.column (moveTime (clockFactor δ) r) h b)*h

def rootCharge (G : SimpleGraph V) (δ : ℝ) (N T : ℕ) (y : ZMod (T+1) → V)
    (m r : ℕ) (t : ZMod (T+1)) : ℝ :=
  scaleCharge G y δ N (m+1) r t + trialPrice G δ N T y m r t

theorem charge_nonneg (G : SimpleGraph V) (δ : ℝ) (N i r : ℕ) {E : Type*} (y : E → V)
    (hA : 1 ≤ dilation δ) (hg : 0 ≤ gain δ * Real.log N / 2) (t : E) :
    0 ≤ scaleCharge G y δ N i r t := by
  have hh : r ≤ dilation δ*r := by simpa using Nat.mul_le_mul_right r hA
  unfold scaleCharge
  exact add_nonneg (sub_nonneg.mpr (logBall_mono G _ hh)) (by split_ifs <;> linarith)

theorem root_charge_mean (G : SimpleGraph V) (δ : ℝ) (N T u m : ℕ) (y : ZMod (T+1) → V)
    (Rmin cap : ℝ) (hG : Fintype.card V ≤ N) (hA : 1 ≤ dilation δ) (hr : 0 < Rmin)
    (count : ∀ i ≤ m+1, 1 ≤ i → Rmin ≤ ((radii δ N i).card : ℝ))
    (bad : ∀ t, ((badLevels G (y t) δ N).card : ℝ) ≤ cap)
    (hg : 0 ≤ gain δ * Real.log N / 2) (hT : 0 < T)
    (clock : ∀ r ∈ radii δ N (m+1), let h := leadTime (clockFactor δ) r
      let M := clockCount T 2 h
      0 < h ∧ h+(h-1)+h*M ≤ T ∧ T ≤ 2*(M*h)) :
    rootMean δ N (m+1) T (fun r ξ b => rootCharge G δ N T y m r (rootEnd δ u r ξ b : ℕ)) ≤
      (4/T) * (T+1:ℕ) * (((m+1 : ℕ):ℝ) * (Real.log N/Rmin) + cap * (gain δ*Real.log N/2)) := by
  have hpos i r t := charge_nonneg G δ N i r y hA hg t
  have nonneg r t : 0 ≤ rootCharge G δ N T y m r t := add_nonneg (hpos ..) (nestedPrice_nonneg _ _ _ _ hpos ..)
  have density r (hr' : r ∈ radii δ N (m+1)) := (clock r hr')
  let rs := radii δ N (m+1)
  have hne {i : ℕ} (lo : 1 ≤ i) (hi : i ≤ m+1) : (radii δ N i).Nonempty :=
    card_pos.mp (by exact_mod_cast hr.trans_le (count i hi lo))
  have hmean :
      rootMean δ N (m+1) T (fun r ξ b => rootCharge G δ N T y m r (rootEnd δ u r ξ b : ℕ)) ≤
        mean rs (fun r => (4/(T:ℝ)) * ∑ t, rootCharge G δ N T y m r t) := by
    apply mean_mono'
    intro r hr'
    obtain ⟨hh,hm,hs⟩ := density r hr'
    let h := leadTime (clockFactor δ) r
    let B := moveTime (clockFactor δ) r
    let M := clockCount T 2 h
    have hp := cyclic_offset_average (B:=B) (M:=M) (g:=h) hh
      (by change h ≤ h+2*r; omega) hT hm hs (rootCharge G δ N T y m r) (nonneg r) (u:ℕ)
    have he ξ b : ((rootEnd δ u r ξ b : ℕ) : ZMod (T+1)) =
        ((h+ξ+h*Clock.column B h b : ℕ) : ZMod (T+1))+(u:ℕ) := by
      dsimp only [rootEnd,h,B]; push_cast; ring
    simpa only [mean,card_range,←sum_div,he,h,B,M] using hp
  let lower := ∑ j ∈ range m, mean (radii δ N (j+1)) (fun r => ∑ t, scaleCharge G y δ N (j+1) r t)
  have prior (r : ℕ) : (∑ t, trialPrice G δ N T y m r t) = lower := by
    apply sum_nestedPrice
    · intro i hi hj; exact hne hi (by omega)
    · intro i hi hj parent child _
      exact ⟨0,mem_range.mpr (by omega)⟩
  have heq : mean rs (fun r => ∑ t, rootCharge G δ N T y m r t) =
      ∑ j ∈ range (m+1), mean (radii δ N (j+1)) (fun r => ∑ t, scaleCharge G y δ N (j+1) r t) := by
    simp only [rootCharge,sum_add_distrib,prior,sum_range_succ]
    change mean rs (fun r => (∑ t, scaleCharge G y δ N (m+1) r t) + lower) =
      lower + mean rs (fun r => ∑ t, scaleCharge G y δ N (m+1) r t)
    rw [mean_add',mean_const' (hne (by omega) (by omega):rs.Nonempty),add_comm]
  have ha := avg_charge_bound G y δ N (m+1) Rmin cap hr hG count bad hg
  rw [ZMod.card] at ha
  have pull : mean rs (fun r => (4/(T:ℝ)) * ∑ t, rootCharge G δ N T y m r t) =
      (4/(T:ℝ))*mean rs (fun r => ∑ t, rootCharge G δ N T y m r t) := by
    unfold mean
    rw [←mul_sum]; ring
  exact hmean.trans (by rw [pull,heq,mul_assoc]; exact mul_le_mul_of_nonneg_left ha (by positivity))

end
end Meyniel.Multiscale
