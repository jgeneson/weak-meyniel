module

public import Meyniel.RandomLaw
public import Meyniel.RandomCapture

/-! Averaging over actual fixed tapes yields one deterministic cop from the
posted backward sampler. The robber may subsequently see its full strategy. -/

@[expose] public section

namespace Meyniel.RandomConclusion

open Finset RandomPolicy
open RandomTable (avg)

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W] [Nonempty W] [Fintype V] [DecidableEq V]

private theorem avg_swap {A B : Type*} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    avg (fun a => avg (f a)) = avg (fun b => avg (fun a => f a b)) := by
  unfold RandomTable.avg
  simp only [← Finset.sum_div]; rw [Finset.sum_comm]; ring

private theorem exists_above_avg {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    ∃ a, avg f ≤ f a := by
  classical
  obtain ⟨a,_,ha⟩ := Finset.univ.exists_max_image f Finset.univ_nonempty
  refine ⟨a,?_⟩
  rw [← RandomTable.avg_const (A := A) (f a)]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum ha) (Nat.cast_nonneg _)

/-- This theorem returns not only an ordinary policy but a diagonal and a
specific finite random tape producing a covering fraction on the prescribed family. -/
theorem exists_covering_tape (G : SimpleGraph V) (X : ℕ→W→V) (T d n : ℕ) (home : V)
    (leg : ∀ i w, Step G (X i w) (X (i+1) w)) (hhome : ∀ j, T+d ≤ j → ∀ w, X j w = home)
    (hcard : Fintype.card V ≤ n) (htime : (d:ℝ)*Real.log n ≤ (T:ℝ)*Real.log 2) :
    ∃ b ≤ 2*T, ∃ tape : Tape W (b/2+1), 1 / Real.sqrt (2*(n:ℝ)) * Fintype.card W ≤
       (Sampler.count Finset.univ (fun w => Hits (policy G X leg b (b/2+1) tape) []
          (List.ofFn (fun i : Fin (T+1) => X i.val w))) : ℝ) := by
  classical
  have hn : 1 ≤ n := (Fintype.card_pos_iff.mpr ⟨home⟩).trans_le hcard
  obtain ⟨b,hb,hgood⟩ := ForwardWeights.exists_good_forward (Sampler.past X) X T d n hn hcard htime
    (fun _ _ => rfl) (fun j hj w z => (hhome j hj w).trans (hhome j hj z).symm)
  let live := fun (tape : Tape W (b/2+1)) (w : W) => if (outcome X b (b/2+1) tape w).2.isSome then (1:ℝ) else 0
  have hlive : avg (fun tape => avg (live tape)) = ForwardWeights.terminalLive (Sampler.past X) X b := by
    rw [avg_swap]
    change avg (fun w => avg (fun tape => if (outcome X b (b/2+1) tape w).2.isSome then (1:ℝ) else 0)) = _
    simp_rw [RandomLaw.terminal_probability]
    rfl
  obtain ⟨tape,htape⟩ := exists_above_avg (fun tape => avg (live tape))
  rw [hlive] at htape
  have hbound := (le_div_iff₀ (show 0 < (Fintype.card W : ℝ) by exact_mod_cast Fintype.card_pos)).mp (hgood.trans htape)
  refine ⟨b,hb,tape,hbound.trans ?_⟩
  change (∑ w, live tape w) ≤ ((Finset.univ.filter (fun w => Hits (policy G X leg b (b/2+1) tape) []
    (List.ofFn (fun i : Fin (T+1) => X i.val w)))).card : ℝ)
  rw [← Finset.sum_boole (R := ℝ)]
  apply Finset.sum_le_sum; intro w _
  dsimp only [live]
  by_cases h : (outcome X b (b/2+1) tape w).2.isSome
  · rw [if_pos h, if_pos (RandomCapture.terminal_seed_hits G X leg T b hb tape w h)]
  · simp [h]; positivity

/-- The arbitrary-family interception lemma with the literal fixed-tape strategy. -/
theorem tagged_one_cop_seed (G : SimpleGraph V) (X : ℕ→W→V) (T d n : ℕ) (home : V)
    (leg : ∀ i w, Step G (X i w) (X (i+1) w)) (hhome : ∀ j, T+d ≤ j → ∀ w, X j w = home)
    (hcard : Fintype.card V ≤ n) (htime : (d:ℝ)*Real.log n ≤ (T:ℝ)*Real.log 2) :
    ∃ s : Policy G, 1 / Real.sqrt (2*(n:ℝ)) * Fintype.card W ≤
      (Sampler.count Finset.univ (fun w => Hits s [] (List.ofFn (fun i : Fin (T+1) => X i.val w))) : ℝ) := by
  obtain ⟨b, _, seed, h⟩ := exists_covering_tape G X T d n home leg hhome hcard htime
  exact ⟨policy G X leg b (b/2+1) seed, h⟩

end
end Meyniel.RandomConclusion
