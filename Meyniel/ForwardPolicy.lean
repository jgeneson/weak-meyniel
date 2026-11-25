import Meyniel.Weights
import Meyniel.Sampler

/-! Direct comparison of the posted forward sampler with ordinary deterministic
policies. The forward mass and the conditional best capture count are adjoint
at each cell. Thus any branch losses of the sampler are harmless for the cop.
-/

namespace Meyniel.ForwardPolicy

open Finset ForwardWeights Sampler

variable {W V : Type*} [Fintype W] [Nonempty W] [Fintype V] [DecidableEq V]

theorem exists_anchored_policy_ge_live (G : SimpleGraph V) (X : ℕ → W → V) (T b : ℕ)
    (hb : b ≤ 2*T) (leg : ∀ i w, Step G (X i w) (X (i+1) w)) :
    ∃ (s : Policy G) (w : W), s.pos [] = X b w ∧ terminalLive (past X) X b * Fintype.card W ≤
      (Sampler.count univ (fun w => Hits s [] (remainder X T 0 w)) : ℝ) := by
  classical
  let route := remainder X T 0
  let scores := fun w => bestCount G univ route (X b w)
  obtain ⟨winner, _, hmax⟩ := exists_max_image univ scores univ_nonempty
  let s := (optimal G univ route (X b winner)).1
  let fraction := (scores winner : ℝ) / Fintype.card W
  have hl : terminalLive (past X) X b ≤ fraction := by
    apply terminalLive_le_bellman (past X) X b (fun _ _ => rfl) (value G X T b) fraction
    · intro w; simp [value]
    · intro w
      have hh : oldPrefix X 0 w = univ := by simp [oldPrefix, Interception.fiber,past]
      simp only [value, Nat.zero_le, if_true, hh, card_univ, tsub_zero]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmax w (mem_univ w)) (Nat.cast_nonneg _)
    · intro t ht w
      exact cell_bound G X T b t (b-t) hb ht rfl w leg
  refine ⟨s,winner,(optimal G univ route (X b winner)).property,?_⟩
  exact (le_div_iff₀ (show 0 < (Fintype.card W : ℝ) by exact_mod_cast Fintype.card_pos)).mp hl

theorem exists_policy_ge_live (G : SimpleGraph V) (X : ℕ → W → V) (T b : ℕ)
    (hb : b ≤ 2*T) (leg : ∀ i w, Step G (X i w) (X (i+1) w)) :
    ∃ s : Policy G, terminalLive (past X) X b * Fintype.card W ≤
      (Sampler.count univ (fun w => Hits s [] (remainder X T 0 w)) : ℝ) := by
  obtain ⟨s,_,_,hs⟩ := exists_anchored_policy_ge_live G X T b hb leg
  exact ⟨s,hs⟩

/-- The claimed deterministic one-cop capture fraction, derived specifically
by propagating the posted sampler's conditional mass and weight recurrence. -/
theorem tagged_one_cop_forward (G : SimpleGraph V) (X : ℕ→W→V) (T d n : ℕ) (home : V)
    (leg : ∀ i w, Step G (X i w) (X (i+1) w))
    (hhome : ∀ j, T+d ≤ j → ∀ w, X j w = home)
    (hcard : Fintype.card V ≤ n) (htime : (d:ℝ)*Real.log n ≤ (T:ℝ)*Real.log 2) :
    ∃ s : Policy G, 1 / Real.sqrt (2*(n:ℝ)) * Fintype.card W ≤
      (Sampler.count univ (fun w => Hits s [] (List.ofFn (fun i : Fin (T+1) => X i.val w))) : ℝ) := by
  have hn := (Fintype.card_pos_iff.mpr ⟨home⟩).trans_le hcard
  obtain ⟨b,hb,hs⟩ := exists_good_forward (past X) X T d n hn hcard htime (fun _ _ => rfl)
    (fun j hj w z => (hhome j hj w).trans (hhome j hj z).symm)
  obtain ⟨s,h⟩ := exists_policy_ge_live G X T b hb leg
  exact ⟨s, by simpa [remainder] using ((mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _)).trans h)⟩

end Meyniel.ForwardPolicy
