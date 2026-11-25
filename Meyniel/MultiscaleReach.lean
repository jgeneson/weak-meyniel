import Meyniel.MultiscaleArrival
import Meyniel.MultiscaleGraphClock
import Meyniel.TrialMixtures

namespace Meyniel.Multiscale
variable {V W : Type*} {G : SimpleGraph V}

theorem hits_extends (s : Policy G) (past extra : List V) (w : List V)
    (hit : Hits s past w) : Hits s past (w++extra) := by
  induction w generalizing past with
  | nil => exact hit.elim
  | cons r rs ih =>
    cases rs with
    | nil => cases extra with
             | nil => exact hit
             | cons z zs => exact Or.inl hit
    | cons z zs =>
      rcases hit with now | move | later
      · exact Or.inl now
      · exact Or.inr (Or.inl move)
      · exact Or.inr (Or.inr (ih _ later))

theorem segment_initial_hit (s : Policy G) (R : ℕ → V) (t : ℕ) {a b : ℕ} (h : a≤b)
    (hit : Hits s [] (segment R t a)) : Hits s [] (segment R t b) := by
  rw [show b=a+(b-a) by omega,segment_add]
  exact hits_extends _ _ _ _ hit

/-- From the known candidate x at relative time f, travel during the
preparation period and play the chosen window mixture. The deadline may
extend past the end of the inner trial. -/
theorem reachWindow_mixture (hc : G.Connected) (x : V) (R : W → ℕ → V)
    (u T f a t : ℕ) (hprep : u+f+2 ≤ a) (hfinish : a+t ≤ u+T)
    (starts : V → Prop) (canReach : ∀ v, starts v → G.dist x v ≤ a-(u+f)) (cost : W → ℝ)
    (hwin : WindowMixture G R a t starts cost) :
    ∃ m : Mixture (Anchored G x), ∀ w, Real.exp (-cost w) ≤
      m.success (GraphClock.atHit R u T f x) w := by
  obtain ⟨m,hm⟩ := hwin
  let d := a-(u+f)
  let go (s : {s : WindowPolicy G // starts s.start}) := reachWindow hc x d s.1 (canReach _ s.2)
  refine ⟨m.map' go,fun w => (hm w).trans (m.map_success_le go _ _ w ?_)⟩
  intro s hit
  have ready : 2 ≤ d := by dsimp [d]; omega
  have join : (u+f)+d=a := by dsimp [d]; omega
  have arrived := reachWindow_hits hc x s.val (R w) (u+f) d t ready (canReach _ s.2)
    (by rwa [join])
  change Hits (go s).val [] (Flight.suffix (R w) u T f)
  rw [Flight.suffix,Flight.segment_ofFn]
  change Hits (go s).val [] (segment (R w) (u+f+2) (T+1-f))
  exact segment_initial_hit _ _ _ (by dsimp [d]; omega) arrived

end Meyniel.Multiscale
