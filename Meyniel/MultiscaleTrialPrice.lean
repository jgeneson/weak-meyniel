module

public import Meyniel.MultiscalePrices
public import Meyniel.MultiscaleQuotients

/-! The terminal price as an explicit function of the endpoint and parent
radius. The underlying finite group of times is used only to sum the prices. -/

@[expose] public section

namespace Meyniel.Multiscale
open Finset Interception
noncomputable section

def childCount (δ : ℝ) (parent child : ℕ) : ℕ :=
  clockCount (duration (clockFactor δ) parent) 1 (leadTime (clockFactor δ) child)

def childLabels (δ : ℝ) (_i parent child : ℕ) : Finset ℕ :=
  range (Clock.top (moveTime (clockFactor δ) child) (leadTime (clockFactor δ) child)
    (childCount δ parent child)+1)

def childLag (δ : ℝ) (parent child b : ℕ) : ℕ :=
  let C := clockFactor δ
  let h := leadTime C child
  duration C parent - (h + (Clock.column (moveTime C child) h b)*h)

def trialPrice {V : Type*} [Fintype V] (G : SimpleGraph V) (δ : ℝ) (N T : ℕ)
    (vertex : ZMod (T+1) → V) (smaller parent : ℕ) (e : ZMod (T+1)) : ℝ :=
  nestedPrice (radii δ N) (childLabels δ)
    (fun _ parent child b => ((childLag δ parent child b : ℕ) : ZMod (T+1)))
    (scaleCharge G vertex δ N) smaller parent e

def trialExtra {V : Type*} [Fintype V] (G : SimpleGraph V) (δ : ℝ) (N T : ℕ)
    (vertex : ZMod (T+1) → V) (i r : ℕ) (e : ZMod (T+1)) : ℝ := by
  classical exact trialPrice G δ N T vertex (i-1) r e -
    (i:ℝ)*gain δ*Real.log N/2 +
    (if i ∈ badLevels G (vertex e) δ N then gain δ*Real.log N/2 else 0) +
    9*(i:ℝ)/clockFactor δ*Real.log N + (i:ℝ)*Real.log 2

/-- For a parent clock ending at e, its terminal child time is the parent's
endpoint shifted backwards by a constant depending only on radii and label. -/
theorem child_translation {δ : ℝ} {T p r b e : ℕ}
    (hp : duration (clockFactor δ) p ≤ e)
    (ha : leadTime (clockFactor δ) r +
      Clock.column (moveTime (clockFactor δ) r) (leadTime (clockFactor δ) r) b *
      leadTime (clockFactor δ) r ≤ duration (clockFactor δ) p) :
    ((e - duration (clockFactor δ) p + leadTime (clockFactor δ) r +
      Clock.column (moveTime (clockFactor δ) r) (leadTime (clockFactor δ) r) b *
      leadTime (clockFactor δ) r : ℕ) : ZMod (T+1)) =
      (e : ZMod (T+1)) - (childLag δ p r b : ℕ) := by
  unfold childLag
  simp only
  rw [Nat.cast_sub (show leadTime (clockFactor δ) r + _ ≤ duration (clockFactor δ) p from ha)]
  push_cast [hp]
  ring

def cyclicWord {V : Type*} (R : ℕ → V) (u T : ℕ) (t : ZMod (T+1)) : V :=
  R (u+2+(t-(u:ℕ)).val)

theorem cyclicWord_at {V : Type*} (R : ℕ → V) {u T t : ℕ} (hu : u ≤ t) (ht : t ≤ u+T) :
    cyclicWord R u T t = R (t+2) := by
  unfold cyclicWord
  rw [← Nat.cast_sub hu,ZMod.val_natCast,Nat.mod_eq_of_lt (by omega)]
  congr 1 <;> omega

end
end Meyniel.Multiscale
