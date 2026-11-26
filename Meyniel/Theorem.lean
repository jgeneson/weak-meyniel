module

public import Meyniel.Bounds
public import Meyniel.Extension
public import Meyniel.Guard
public import Meyniel.Optimize
public import Meyniel.RandomConclusion

/-! # The weak Meyniel bound for the ordinary cop game -/

@[expose] public section

namespace Meyniel

universe u
variable {V : Type u}

/-- Restrict the tagged-walk calculation to the given finite family of actual walks.
The artificial continuation is used only in predicting vertices; the capture policy
is evaluated on the original T-round words. -/
theorem walks_interception [Fintype V] {G : SimpleGraph V} (hc : G.Connected)
    (T D N : ℕ) (hcard : Fintype.card V ≤ N) (hdiam : G.diam ≤ D)
    (htime : (D:ℝ) * Real.log N ≤ T * Real.log 2) :
    WalkFraction G T (1 / Real.sqrt (2*N)) := by
  classical
  let home := Classical.choice hc.nonempty
  intro R hR hne
  letI : Nonempty R := hne.to_subtype
  let X (t : ℕ) (w : R) := Extension.extendWord hc home w.val t
  have leg (i : ℕ) (w : R) : Step G (X i w) (X (i+1) w) := by
    have hw : w.val ∈ walks G T := hR w.property
    exact Extension.extendWord_step hc home w.val (Finset.mem_filter.mp hw).2 i
  have last (j : ℕ) (hj : T+D ≤ j) (w : R) : X j w = home :=
    Extension.extendWord_home hc home w.val (by omega)
  obtain ⟨s, hs⟩ := RandomConclusion.tagged_one_cop_seed G X T D N home leg last hcard htime
  refine ⟨s, ?_⟩
  have he (w : R) : (fun i : Fin (T+1) => X i.val w) = w.val := by
    funext i
    exact Extension.extendWord_at hc home w.val i
  simp only [he, Fintype.card_coe] at hs
  have eqcount : Sampler.count Finset.univ (fun w : R => Hits s [] (List.ofFn w.val)) =
      (R.filter (fun w => Hits s [] (List.ofFn w))).card := by
    unfold Sampler.count
    change (R.attach.filter (fun w : R => Hits s [] (List.ofFn w.val))).card = _
    rw [Finset.filter_attach (fun w => Hits s [] (List.ofFn w))]
    simp
  rwa [eqcount] at hs

/-- Lemma 2, with precisely the ceiling of diameter times the base-two log. -/
theorem oneCop_lemma [Fintype V] {G : SimpleGraph V} (hc : G.Connected) :
    WalkFraction G (horizon (Fintype.card V) G.diam) (1 / Real.sqrt (2*Fintype.card V)) :=
  walks_interception hc _ _ _ le_rfl le_rfl (horizon_large ..)

/-- An explicit form of the manuscript's order estimate, uniform in the graph. -/
theorem copNumber_three_quarters [Fintype V] (G : SimpleGraph V) (hc : G.Connected) :
    (copNumber G : ℝ) ≤ 31 * (Fintype.card V : ℝ) ^ (3/4:ℝ) *
      Real.log (2 * (Fintype.card V : ℝ)) := by
  let n := Fintype.card V
  let D := diamThreshold n
  let T := horizon n D
  have hn : 1 ≤ n := by
    letI := hc.nonempty
    exact Fintype.card_pos
  have win : WinsWith G (budget n T + n/D) := by
    apply Guard.diameter_reduction hc (N := n) (K := budget n T) (D := D) le_rfl (diamThreshold_pos hn)
    intro W inst H hconn hs hd
    letI := hconn.nonempty
    exact winsWith_budget hn hs (walks_interception hconn T D n hs hd (horizon_large ..))
  exact (Nat.cast_le.mpr (copNumber_le_of_win win)).trans (budget_add_guards_le hn)

end Meyniel
