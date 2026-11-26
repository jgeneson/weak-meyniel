module

public import Meyniel.Game

/-! # The polynomial saving in the weak Meyniel conjecture

The constant may depend on the exponent but is uniform over all graphs.
The existential statement uses the quantifier order of the Formal
Conjectures project's `meyniel_conjecture.variants.soft`.
-/

@[expose] public section

namespace Meyniel

universe u

/-- The main quantitative estimate yields every fixed saving below one fourth. -/
theorem weak_forall_epsilon_of_bound
    (main : ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ 31 * (Fintype.card V : ℝ) ^ (3 / 4 : ℝ) *
        Real.log (2 * (Fintype.card V : ℝ)))
    (ε : ℝ) (_hε : 0 < ε) (hε' : ε < 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ C * (Fintype.card V : ℝ) ^ (1 - ε) := by
  let δ : ℝ := 1/4 - ε
  have hδ : 0 < δ := sub_pos.mpr hε'
  refine ⟨31 * (2 : ℝ) ^ δ / δ, by positivity, ?_⟩
  intro V _ G conn
  letI : Nonempty V := conn.nonempty
  let n : ℝ := Fintype.card V
  have hn : 0 < n := by
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have hsum : 1 - ε = 3 / 4 + δ := by dsimp [δ]; ring
  calc
    (copNumber G : ℝ) ≤ 31 * n ^ (3/4 : ℝ) * Real.log (2*n) := main V G conn
    _ ≤ 31 * n ^ (3/4 : ℝ) * ((2*n) ^ δ / δ) :=
      mul_le_mul_of_nonneg_left (Real.log_le_rpow_div (by positivity) hδ) (by positivity)
    _ = (31 * (2 : ℝ) ^ δ / δ) * n ^ (1 - ε) := by
      rw [hsum, Real.rpow_add hn, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hn.le]
      ring

/-- The soft conjecture, with globally chosen exponent and multiplicative constant. -/
theorem soft_of_bound
    (main : ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ 31 * (Fintype.card V : ℝ) ^ (3 / 4 : ℝ) *
        Real.log (2 * (Fintype.card V : ℝ))) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
      G.Connected → (copNumber G : ℝ) ≤ C * (Fintype.card V : ℝ) ^ (1 - ε) := by
  obtain ⟨C, hC, hg⟩ := weak_forall_epsilon_of_bound main (1 / 8) (by norm_num) (by norm_num)
  exact ⟨1 / 8, C, by norm_num, hC, hg⟩

end Meyniel
