/-
Copyright 2026 The Formal Conjectures Authors (the game definitions and the soft conjecture statement).

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Meyniel.Corollary
public import Meyniel.Theorem

/-! # Comparing the game with the Formal Conjectures statement

The four definitions and soft theorem statement below reproduce the declarations from
`FormalConjectures/Wikipedia/MeynielConjecture.lean`, checked against upstream main
on November 25, 2026. This standalone comparison supplies the proofs locally.

Source: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MeynielConjecture.lean
Introducing commit: https://github.com/google-deepmind/formal-conjectures/commit/38a3477b3941f132f3e43d5eba58459cbf7e7175
-/

@[expose] public section

namespace MeynielConjecture

variable {V : Type*}

def Step (G : SimpleGraph V) (u v : V) : Prop :=
  u = v ∨ G.Adj u v

def CopsCatchWithin (G : SimpleGraph V) (k : ℕ) : ℕ → (Fin k → V) → V → Prop
  | 0, c, r => ∃ i, c i = r
  | m + 1, c, r =>
      (∃ i, c i = r) ∨
        ∃ c' : Fin k → V, (∀ i, Step G (c i) (c' i)) ∧
          ((∃ i, c' i = r) ∨ ∀ r', Step G r r' → CopsCatchWithin G k m c' r')

def CopsWin (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → V, ∀ r : V, ∃ m, CopsCatchWithin G k m c r

noncomputable def copNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | CopsWin G k}

/-- The two recursively defined game trees agree at every capture deadline. -/
theorem copsCatchWithin_iff (G : SimpleGraph V) (k t : ℕ) (c : Fin k → V) (r : V) :
    CopsCatchWithin G k t c r ↔ Meyniel.CatchesWithin G k t c r := by
  induction t generalizing c r with
  | zero => rfl
  | succ t ih => simp only [CopsCatchWithin, Meyniel.CatchesWithin, ih, Step, Meyniel.Step]

theorem copsWin_iff (G : SimpleGraph V) (k : ℕ) : CopsWin G k ↔ Meyniel.WinsWith G k := by
  simp only [CopsWin, Meyniel.WinsWith, copsCatchWithin_iff]

theorem copNumber_eq (G : SimpleGraph V) : copNumber G = Meyniel.copNumber G := by
  simp only [copNumber, Meyniel.copNumber, copsWin_iff]

/-- The upstream soft conjecture with its original quantifiers and its own cop number. -/
theorem meyniel_conjecture.variants.soft :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ C * (Fintype.card V : ℝ) ^ ((1 : ℝ) - ε) := by
  simpa only [copNumber_eq] using
    Meyniel.soft_of_bound (fun _ _ G conn => Meyniel.copNumber_three_quarters G conn)

end MeynielConjecture
