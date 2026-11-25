import Meyniel.Game
import Meyniel.MultiscaleMinimax

/-! Local windows in the game include a visible two-round prehistory.
A cop must choose its initial vertex before learning any of that prehistory. -/

namespace Meyniel.Multiscale
variable {V : Type*} {G : SimpleGraph V}

structure WindowPolicy (G : SimpleGraph V) where
  start : V
  play : V → V → Policy G
  start_eq : ∀ x y, (play x y).pos [] = start

def WindowPolicy.ofPolicy (s : Policy G) : WindowPolicy G := ⟨s.pos [],fun _ _ => s,fun _ _ => rfl⟩

def windowHit (s : WindowPolicy G) (R : ℕ → V) (u T : ℕ) : Prop :=
  Hits (s.play (R u) (R (u+1))) [] (List.ofFn (fun i : Fin (T+1) => R (u+2+i.val)))

/-- The mixed strategy has support on allowable starting sites, even for
different pairs of prehistory vertices. -/
def WindowMixture {W : Type*} (G : SimpleGraph V) (R : W → ℕ → V) (u T : ℕ)
    (starts : V → Prop) (cost : W → ℝ) : Prop :=
  ∃ m : Mixture {s : WindowPolicy G // starts s.start}, ∀ w,
    Real.exp (-cost w) ≤ m.success (fun s z => windowHit s.1 (R z) u T) w

end Meyniel.Multiscale
