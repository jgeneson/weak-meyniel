module

public import Mathlib

/-! # The ordinary visible game of cops and robber
The robber and each cop can wait or traverse one edge. Histories supplied to a policy
are stored newest observation first. Test walks supplied to `Hits` are chronological.
-/

@[expose] public section

namespace Meyniel
universe u
variable {V : Type u}

def Step (G : SimpleGraph V) (u v : V) : Prop := u = v ∨ G.Adj u v

structure Policy (G : SimpleGraph V) where
  pos : List V → V
  legal : ∀ x h, Step G (pos h) (pos (x :: h))

def Policy.stay (G : SimpleGraph V) (v : V) : Policy G where
  pos := fun _ => v
  legal := fun _ _ => Or.inl rfl

/-- A capture by the end of a fixed walk. On a singleton only coincidence can count:
there is no additional cop move after the final robber move. -/
def Hits {G : SimpleGraph V} (s : Policy G) (h : List V) : List V → Prop
  | [] => False
  | [x] => s.pos h = x
  | x :: y :: xs => s.pos h = x ∨ s.pos (x :: h) = x ∨ Hits s (x :: h) (y :: xs)

/-- All consecutive robber positions are joined by a step. -/
def LegalWord (G : SimpleGraph V) (w : List V) : Prop := w.IsChain (Step G)

/-- A bounded perfect-information game tree. After the cops move they must be able
to handle every legal response by the robber. -/
def CatchesWithin (G : SimpleGraph V) (k : ℕ) : ℕ → (Fin k → V) → V → Prop
  | 0, c, r => ∃ i, c i = r
  | t+1, c, r => (∃ i, c i = r) ∨ ∃ c' : Fin k → V,
      (∀ i, Step G (c i) (c' i)) ∧
      ((∃ i, c' i = r) ∨ ∀ r', Step G r r' → CatchesWithin G k t c' r')

def WinsWith (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → V, ∀ r : V, ∃ t, CatchesWithin G k t c r

noncomputable def copNumber (G : SimpleGraph V) : ℕ := sInf {k | WinsWith G k}

/-- Cop number bounded by the size of any winning team. -/
theorem copNumber_le_of_win {G : SimpleGraph V} {k : ℕ} (hk : WinsWith G k) :
    copNumber G ≤ k := Nat.sInf_le hk

theorem winsWith_card [Fintype V] (G : SimpleGraph V) : WinsWith G (Fintype.card V) := by
  classical
  exact ⟨(Fintype.equivFin V).symm, fun r => ⟨0, Fintype.equivFin V r, by simp⟩⟩

end Meyniel
