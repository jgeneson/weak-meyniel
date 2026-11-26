module

public import Meyniel.TwoThirds
public import Meyniel.Theorem
public import Meyniel.Corollary
public import Meyniel.CompareGame
public import Meyniel.ForwardPolicy

/-! # The weak Meyniel conjecture
The cop number is taken in the ordinary full-information, alternating game,
with the cops placing first and the robber allowed to choose each move after theirs.
-/

@[expose] public section

namespace Meyniel
universe u

/-- Every positive exponent saving strictly below one quarter is valid. -/
theorem weak_meyniel_for_epsilon (ε : ℝ) (he : 0 < ε) (he' : ε < 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ C * (Fintype.card V : ℝ) ^ (1 - ε) :=
  weak_forall_epsilon_of_bound (fun _ _ G hG => copNumber_three_quarters G hG) ε he he'

/-- The usual weak (soft) Meyniel conjecture, with universal constants. -/
theorem weak_meyniel_conjecture :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ C * (Fintype.card V : ℝ) ^ (1 - ε) :=
  soft_of_bound (fun _ _ G hG => copNumber_three_quarters G hG)

end Meyniel
