import Meyniel.TrialInputs
import Meyniel.TrialLocalGeometry

namespace Meyniel.Multiscale
open Finset Interception
noncomputable section
universe v w
variable {V : Type v} [Fintype V]

/-- The induction statement is uniform in the finite input family. This
allows every observed history/position fiber to be used as a child input. -/
def TrialAt (G : SimpleGraph V) (δ : ℝ) (N root T i : ℕ) : Prop :=
  ∀ {W : Type w} [Fintype W] [Nonempty W] {r F a : ℕ} {R : W → ℕ → V} {z x : V},
    r ∈ radii δ N i → TrialInput G δ N root T i r R F a z x →
    TrialOutcome G δ N root T i r R a z

def childPrice (G : SimpleGraph V) (δ : ℝ) (N T i p r : ℕ) (vertex : ZMod (T+1) → V)
    (e : ZMod (T+1)) : ℝ :=
  mean (childLabels δ i p r) (fun b =>
    let y := e-(childLag δ p r b : ℕ)
    scaleCharge G vertex δ N i r y + trialPrice G δ N T vertex (i-1) r y)

def radiusPrice {W : Type w} (G : SimpleGraph V) (δ : ℝ) (N root T i p r : ℕ)
    (R : W → ℕ → V) (a : ℕ) (band : Bool) (w : W) : ℝ :=
  let e := a+duration (clockFactor δ) p
  logBall G (R w (e+2)) (dilation δ*p)/2 -
    (if band then gain δ * Real.log N/2 else 0) +
    childPrice G δ N T i p r (cyclicWord (R w) root T) e -
    (i:ℝ)*gain δ*Real.log N/2 + (9*(i:ℝ)+7)/clockFactor δ*Real.log N +
    (i:ℝ)*Real.log 2

structure TrialFacts (δ : ℝ) (N : ℕ) : Prop where
  clock : 0 < clockFactor δ
  vertices : 0 < N
  gains : 0 ≤ gain δ
  ranges : ∀ i, 1 ≤ i → i ≤ levels δ → (radii δ N i).Nonempty
  timing : ∀ i, 1 ≤ i → i ≤ levels δ → ∀ r ∈ radii δ N i, TimingFacts δ N i r
  spare : ∀ i, 1 ≤ i → i+1 ≤ levels δ → ∀ p ∈ radii δ N (i+1), ∀ r ∈ radii δ N i,
     12*leadTime (clockFactor δ) r ≤ p

end
end Meyniel.Multiscale
