/-
Copyright 2026 The Formal Conjectures Authors (game definitions and soft conjecture statement).
Licensed under the Apache License, Version 2.0. See LICENSES/Apache-2.0.txt.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.Lattice.Nat

/-!
# The weak Meyniel conjecture

For a finite connected undirected graph with `n` vertices, the ordinary visible cop number is
at most `n^(2/3 + e(n))` for a single positive function `e` tending to zero. This implies a
bound `C n^(1 - ε)` with positive constants independent of the graph. Meyniel's conjectured
`O(√n)` bound remains open.

The game definitions and the soft statement below follow the Formal Conjectures project,
`FormalConjectures/Wikipedia/MeynielConjecture.lean`.
-/

@[expose] public section

namespace MeynielConjecture

variable {V : Type*}

/-- A player may stay at its present vertex or move along one graph edge. -/
def Step (G : SimpleGraph V) (u v : V) : Prop :=
  u = v ∨ G.Adj u v

/-- From these positions, with cops to move, the cops can force capture within the given
number of rounds. After each simultaneous cop move the robber may choose any legal reply. -/
def CopsCatchWithin (G : SimpleGraph V) (k : ℕ) : ℕ → (Fin k → V) → V → Prop
  | 0, c, r => ∃ i, c i = r
  | m + 1, c, r =>
      (∃ i, c i = r) ∨
        ∃ c' : Fin k → V, (∀ i, Step G (c i) (c' i)) ∧
          ((∃ i, c' i = r) ∨ ∀ r', Step G r r' → CopsCatchWithin G k m c' r')

/-- The cops have initial positions from which they can force finite capture for every
choice of the robber's starting vertex. -/
def CopsWin (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → V, ∀ r : V, ∃ m, CopsCatchWithin G k m c r

/-- The least winning team size. On a finite graph one cop per vertex wins immediately. -/
noncomputable def copNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | CopsWin G k}

end MeynielConjecture

namespace PalomarMeyniel

open Filter
open scoped Topology

/-- One vanishing exponent error bounds the cop number of every connected graph of each order. -/
theorem twoThirds :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ (∀ n, 0 < e n) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
        (MeynielConjecture.copNumber G : ℝ) ≤
          (Fintype.card V : ℝ) ^ ((2 / 3 : ℝ) + e (Fintype.card V)) := by
  sorry

/-- The soft Meyniel conjecture. The exponent saving and the multiplicative constant are uniform. -/
theorem soft :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      (MeynielConjecture.copNumber G : ℝ) ≤
        C * (Fintype.card V : ℝ) ^ ((1 : ℝ) - ε) := by
  sorry

end PalomarMeyniel
