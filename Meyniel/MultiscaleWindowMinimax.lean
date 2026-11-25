import Meyniel.MultiscaleGraphClock

/-! Passing from a lower bound on the weighted log value under every true-word
law to one ordinary mixed strategy with the claimed cost on every word. -/
namespace Meyniel.Multiscale
open Finset GraphClock
noncomputable section

variable {W V : Type*} [Fintype W] [Nonempty W]

theorem weighted_window_minimax (G : SimpleGraph V) (R : W → ℕ → V) (u T : ℕ)
    (starts : V → Prop) [Nonempty {s : WindowPolicy G // starts s.start}] (K : W → ℝ)
    (h : ∀ p ∈ stdSimplex ℝ W, ∀ weight : W → ℝ, (∀ w, 0 < weight w) →
      expect p (fun w => Real.log (weight w)) - expect p K ≤
        Real.log (initialValue G p id weight R u T starts)) :
    WindowMixture G R u T starts K := by
  classical
  let allowed := {s : WindowPolicy G // starts s.start}
  let hit := fun (s : allowed) w => windowHit s.val (R w) u T
  apply mixture_of_weighted_response hit K
  intro p law
  let weight := fun w => Real.exp (K w+1)
  let s := optimal p weight univ hit
  let S := initialValue G p id weight R u T starts
  have hpos w : 0 < weight w := Real.exp_pos _
  have he : expect p (fun w => Real.log (weight w)) - expect p K = 1 := by
    simp [weight,expect,mul_add,sum_add_distrib,law.2]
  have hlog := h p law weight hpos
  rw [he] at hlog
  change 1 ≤ Real.log S at hlog
  have hs : 0 < S := by
    have hn : 0 ≤ S := value_nonneg p weight univ hit law.1 (fun w => (hpos w).le)
    rcases hn.eq_or_lt with e | e
    · rw [← e,Real.log_zero] at hlog; norm_num at hlog
    · exact e
  have hc : Real.exp 1 ≤ S := (Real.le_log_iff_exp_le hs).mp hlog
  have pay : S =
      (∑ w, p w * (if hit s w then Real.exp (K w) else 0)) * Real.exp 1 := by
    change captureGain p weight univ hit s = _
    unfold captureGain avgOn mass; rw [law.2,div_one,Finset.sum_mul]
    apply sum_congr rfl; intro w _
    dsimp only
    by_cases e : hit s w <;> simp [e,weight,Real.exp_add,mul_assoc]
  rw [pay,← one_mul (Real.exp 1)] at hc
  refine ⟨s,?_⟩
  apply le_of_mul_le_mul_right _ (Real.exp_pos (1:ℝ))
  simpa using hc

end
end Meyniel.Multiscale
