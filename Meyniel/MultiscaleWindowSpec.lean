import Meyniel.MultiscaleSites
import Meyniel.MultiscaleWindow

/-! # The two window estimates used in the multiscale deployment -/

namespace Meyniel.Multiscale
universe u

noncomputable def windowCost (δ : ℝ) (N m V : ℕ) : ℝ :=
  Real.log V/2 - (m:ℝ)*gain δ*Real.log N/2 + δ/20*Real.log N

structure ConstantWindows (δ : ℝ) (N : ℕ) : Prop where
  global : ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
    Fintype.card V ≤ N → G.diam ≤ cutoff N δ →
    ∀ (W : Type u) [Fintype W] [Nonempty W] (R : W → ℕ → V),
      (∀ w, SpeedOne G (R w)) →
      (∀ w i, Passes G (R w) (physicalScale G δ N i) 0 (windowTime N (cutoff N δ))) →
      WindowMixture G R 0 (windowTime N (cutoff N δ)) (fun _ => True)
        (fun _ => windowCost δ N (levels δ) N)
  local_window : ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
    Fintype.card V ≤ N → G.diam ≤ cutoff N δ →
    ∀ (i : Fin (levels δ)) (z : V), (physicalScale G δ N i).good z →
    ∀ (W : Type u) [Fintype W] [Nonempty W] (R : W → ℕ → V),
      (∀ w, SpeedOne G (R w)) →
      (∀ w, G.dist z (R w ((physicalScale G δ N i).run+2)) ≤ 2*(physicalScale G δ N i).base) →
      (∀ w l, l < i → Passes G (R w) (physicalScale G δ N l) 0 (physicalScale G δ N i).run) →
      WindowMixture G R 0 (physicalScale G δ N i).run
        (fun v => G.dist z v ≤ 2*(physicalScale G δ N i).run)
        (fun _ => windowCost δ N i.val (ball G z (outerRadius δ N (i.val+1))).card)

end Meyniel.Multiscale
