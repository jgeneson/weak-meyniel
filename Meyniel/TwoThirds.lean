import Meyniel.MultiscaleRoot
import Meyniel.MultiscaleAssembly
import Meyniel.MultiscaleLimit
import Meyniel.CompareGame

/-! # The multiscale cop number bound for finite connected graphs -/

namespace Meyniel
open Filter
open scoped Topology
universe u

/-- For each positive slack, one constant suffices simultaneously for every graph. -/
theorem copNumber_two_thirds_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ C * (Fintype.card V : ℝ) ^ (2/3 + ε) :=
  Multiscale.two_thirds_of_windows (fun _ hδ ht =>
    Multiscale.constantWindows_of_positive hδ ht (Multiscale.positive_root_eventually hδ ht)) ε hε

/-- A single error tending to zero serves every graph of each order. -/
theorem copNumber_two_thirds_little_o :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ (∀ n, 0 < e n) ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
        (copNumber G : ℝ) ≤ (Fintype.card V : ℝ) ^ (2/3 + e (Fintype.card V)) :=
  Multiscale.vanishing_exponent_of_slack copNumber_two_thirds_epsilon

end Meyniel

namespace MeynielConjecture
open Filter
open scoped Topology

/-- The identical quantitative result for the upstream game's own cop number. -/
theorem copNumber_two_thirds_little_o :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ (∀ n, 0 < e n) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
        (copNumber G : ℝ) ≤ (Fintype.card V : ℝ) ^ (2/3 + e (Fintype.card V)) := by
  simpa only [copNumber_eq] using Meyniel.copNumber_two_thirds_little_o.{0}

end MeynielConjecture
