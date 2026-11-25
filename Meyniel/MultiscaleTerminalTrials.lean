import Meyniel.TrialAverage
import Meyniel.TrialRadius

/-! The full correct-terminal induction (equation (7) of the companion proof).
Every recursive call runs on a subfamily with the same observed prefix and
the same correct sampled endpoint. -/
namespace Meyniel.Multiscale
noncomputable section
universe v w
variable {V : Type v} [Fintype V] {G : SimpleGraph V}

theorem terminal_trials (hc : G.Connected) {δ : ℝ} {N root T i : ℕ} (facts : TrialFacts δ N)
    (hn : Fintype.card V ≤ N) (hi : 1 ≤ i) (hk : i ≤ levels δ) :
    TrialAt.{v,w} G δ N root T i := by
  induction i, hi using Nat.le_induction with
  | base =>
    intro W _ _ r F a R z x hr ctx
    exact trial_one hc ctx hn facts.vertices facts.clock (radius_pos_of_mem hr)
      (facts.timing 1 (by decide) hk r hr)
  | succ i hi ih =>
    intro W _ _ p F a R z x hp ctx
    have child : TrialAt.{v,w} G δ N root T i := ih (by omega)
    apply trial_merge R z x facts.vertices facts.clock hi (facts.ranges i hi (by omega)) ctx
    intro U _ _ f b band r hr
    exact terminal_per_radius hc (fun w => R (f w)) z x facts hn hi hk hp hr (ctx.pull f)
      b band child
end
end Meyniel.Multiscale
