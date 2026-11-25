import Meyniel.Game
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

/-! A legal cop on a geodesic, with the precise move order of the game. -/
namespace Meyniel.Guard

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b : V}

/-- The projection index measured in the current connected territory. -/
noncomputable def shadow (p : G.Walk a b) (r : V) : ℕ := min p.length (G.dist a r)

lemma shadow_on_path (p : G.Walk a b) (geo : p.length = G.dist a b)
    (i : ℕ) (hi : i ≤ p.length) : shadow p (p.getVert i) = i := by
  have eqn := length_eq_dist_of_subwalk geo (p.isSubwalk_take i)
  rw [p.take_length, inf_eq_left.mpr hi] at eqn
  simp [shadow, ← eqn, hi]

lemma shadow_step (p : G.Walk a b) {r s : V} (h : r = s ∨ G.Adj r s) :
    shadow p r ≤ shadow p s + 1 ∧ shadow p s ≤ shadow p r + 1 := by
  rcases h with rfl | hadj
  · omega
  have hdist := hadj.diff_dist_adj (u := a)
  unfold shadow
  omega

/-- Move one integer step towards a requested index. An illegal input jump
is harmless: the cop still makes a legal move. -/
def approach (i goal : ℕ) : ℕ := max (i - 1) (min (i + 1) goal)

lemma approach_step (i goal : ℕ) : approach i goal ≤ i + 1 ∧ i ≤ approach i goal + 1 := by
  unfold approach
  omega

/-- At a cop turn the most recent robber observation heads the list. -/
noncomputable def index (p : G.Walk a b) : List V → ℕ
  | [] => 0
  | r :: h => approach (index p h) (shadow p r)

lemma index_le (p : G.Walk a b) (h : List V) : index p h ≤ p.length := by
  induction h with
  | nil => simp [index]
  | cons x h ih =>
    simp only [index, approach, shadow]
    omega

lemma vertices_step (p : G.Walk a b) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (h : i ≤ j + 1 ∧ j ≤ i + 1) : p.getVert i = p.getVert j ∨ G.Adj (p.getVert i) (p.getVert j) := by
  rcases (lt_trichotomy i j) with hlt | rfl | hgt
  · have e : j = i + 1 := by omega
    subst j
    exact Or.inr (p.adj_getVert_succ (by omega))
  · exact Or.inl rfl
  · have e : i = j + 1 := by omega
    subst i
    exact Or.inr (p.adj_getVert_succ (by omega)).symm

noncomputable def position (p : G.Walk a b) (h : List V) : V := p.getVert (index p h)

lemma legal (p : G.Walk a b) (r : V) (h : List V) :
    position p h = position p (r :: h) ∨ G.Adj (position p h) (position p (r :: h)) := by
  apply vertices_step p (index_le p _) (index_le p _)
  simpa [index, and_comm] using approach_step (index p h) (shadow p r)

@[simp] lemma position_nil (p : G.Walk a b) : position p [] = a := by simp [position, index]

/-- On any legal history the actual position has a closed form. In particular
acquisition takes at most the path length, irrespective of the robber moves. -/
lemma index_on_legal_history (p : G.Walk a b) (r : V) (h : List V)
    (hw : (r :: h).IsChain (fun x y ↦ x = y ∨ G.Adj x y)) :
    index p (r :: h) = min (h.length + 1) (shadow p r) := by
  induction h generalizing r with
  | nil => simp [index, approach]
  | cons s tail ih =>
    obtain ⟨hrs, htail⟩ := List.isChain_cons_cons.mp hw
    have hs := shadow_step p hrs
    rw [index, ih s htail, List.length_cons]
    unfold approach
    omega

/-- If the robber visits any vertex of the path after acquisition, the next
cop move lands on that vertex, before the robber gets another move. -/
lemma capture_on_path (p : G.Walk a b) (geo : p.length = G.dist a b) (r : V) (h : List V)
    (hw : (r :: h).IsChain (fun x y ↦ x = y ∨ G.Adj x y))
    (acquired : p.length ≤ h.length + 1) (hr : r ∈ p.support) : position p (r :: h) = r := by
  obtain ⟨i, hi, hlen⟩ := Walk.mem_support_iff_exists_getVert.mp hr
  subst r
  rw [position, index_on_legal_history p _ _ hw, shadow_on_path p geo _ hlen,
    min_eq_right (by omega)]

/-- A diametral geodesic has exactly `diam + 1` distinct vertices available
for deletion, even when the diameter is zero. -/
lemma exists_diametral_guard_path [DecidableEq V] (conn : G.Connected) :
    ∃ (a b : V) (p : G.Walk a b), p.length = G.dist a b ∧ p.length = G.diam ∧
      p.support.toFinset.card = G.diam + 1 := by
  letI : Nonempty V := conn.nonempty
  obtain ⟨a, b, hab⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp⟩ := conn.exists_walk_length_eq_dist a b
  have hpath := p.isPath_of_length_eq_dist hp
  refine ⟨a, b, p, hp, hp.trans hab, ?_⟩
  rw [List.toFinset_card_of_nodup hpath.support_nodup, p.length_support, hp, hab]

end Meyniel.Guard

namespace Meyniel.Guard
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {a b : V} {k : ℕ}

noncomputable def policy (p : G.Walk a b) : Policy G where
  pos := position p
  legal := legal p

private lemma add_time {t : ℕ} {c : Fin k → V} {r : V} (h : CatchesWithin G k t c r) :
    CatchesWithin G k (t+1) c r := by
  induction t generalizing c r with
  | zero => exact Or.inl h
  | succ t ih =>
    rcases h with cap | ⟨d, hd, cap | hnext⟩
    · exact Or.inl cap
    · exact Or.inr ⟨d, hd, Or.inl cap⟩
    · exact Or.inr ⟨d, hd, Or.inr (fun r' hr' => ih (hnext r' hr'))⟩

private lemma more_time {t t' : ℕ} {c : Fin k → V} {r : V} (h : CatchesWithin G k t c r)
    (ht : t ≤ t') : CatchesWithin G k t' c r := by
  induction t', ht using Nat.le_induction with
  | base => exact h
  | succ t' _ ih => exact add_time ih

/-- Finite branching turns separate finite capture times after each possible
robber reply into a uniform finite time before the cops' move. -/
private lemma advance [Fintype V] {c d : Fin k → V} {r : V} (hm : ∀ i, Step G (c i) (d i))
    (hw : ∀ s, Step G r s → ∃ t, CatchesWithin G k t d s) : ∃ t, CatchesWithin G k t c r := by
  classical
  have hp : ∀ s, ∃ t, Step G r s → CatchesWithin G k t d s := by
    intro s
    by_cases h : Step G r s
    · obtain ⟨t, ht⟩ := hw s h
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun hs => False.elim (h hs)⟩
  choose times htimes using hp
  exact ⟨Finset.univ.sup times + 1, Or.inr ⟨d, hm, Or.inr (fun s hs =>
    more_time (htimes s hs) (Finset.le_sup (f := times) (Finset.mem_univ s)))⟩⟩

/-- The path guard is slot zero. The other cops retain their local numbering. -/
private def team (g : V) (c : Fin k → V) : Fin (k+1) → V := Fin.cons g c

private lemma team_step {g g' : V} {c d : Fin k → V} (h : Step G g g')
    (hc : ∀ i, Step G (c i) (d i)) : ∀ i, Step G (team g c i) (team g' d i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [team] using h
  · simpa [team] using hc j

private noncomputable abbrev target (p : G.Walk a b) (r : V) := p.getVert (shadow p r)

private lemma target_step (p : G.Walk a b) {r s : V} (h : Step G r s) :
    Step G (target p r) (target p s) :=
  vertices_step p (min_le_left ..) (min_le_left ..) (shadow_step p h)

private lemma target_eq (p : G.Walk a b) (geo : p.length = G.dist a b) {r : V}
    (hr : r ∈ p.support) : target p r = r := by
  obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hr
  rw [target, shadow_on_path p geo i hi]

private lemma hit_guard (p : G.Walk a b) (geo : p.length = G.dist a b) {r g : V}
    (aligned : Step G g (target p r)) (hr : r ∈ p.support) (c : Fin k → V) :
    ∃ t, CatchesWithin G (k+1) t (team g c) r := by
  have hg : Step G g r := target_eq p geo hr ▸ aligned
  exact ⟨1, Or.inr ⟨team r c, team_step hg (fun _ => Or.inl rfl), Or.inl ⟨0, rfl⟩⟩⟩

/-- The residual component uses distances within its own induced graph. -/
abbrev Outside (p : G.Walk a b) := G.induce {x : V | x ∉ p.support}

private abbrev embed {p : G.Walk a b} {C : (Outside p).ConnectedComponent} (v : C) : V :=
  v.val.val

private lemma embed_step {p : G.Walk a b} {C : (Outside p).ConnectedComponent} {v w : C}
    (h : Step C.toSimpleGraph v w) : Step G (embed v) (embed w) := by
  rcases h with rfl | adj
  · exact Or.inl rfl
  · exact Or.inr adj

private lemma reply {p : G.Walk a b} {C : (Outside p).ConnectedComponent} (v : C)
    {r : V} (h : Step G (embed v) r) :
    r ∈ p.support ∨ ∃ w : C, embed w = r ∧ Step C.toSimpleGraph v w := by
  classical
  by_cases hr : r ∈ p.support
  · exact Or.inl hr
  right
  rcases h with he | adj
  · exact ⟨v, he, Or.inl rfl⟩
  · let s : {x : V | x ∉ p.support} := ⟨r, hr⟩
    have hadj : (Outside p).Adj v.val s := adj
    exact ⟨⟨s, C.mem_supp_of_adj_mem_supp v.property hadj⟩, rfl, Or.inr hadj⟩

/-- Once the remaining team occupies local cop positions, it can follow a
winning strategy inside the component. Any attempted exit gives the guard
a capture on its next turn. -/
private lemma play_inside [Fintype V] {p : G.Walk a b} (geo : p.length = G.dist a b)
    {C : (Outside p).ConnectedComponent} {t : ℕ} {c : Fin k → C} {r : C}
    (win : CatchesWithin C.toSimpleGraph k t c r) {g : V}
    (aligned : Step G g (target p (embed r))) :
    ∃ m, CatchesWithin G (k+1) m (team g (fun i => embed (c i))) (embed r) := by
  induction t generalizing c r g with
  | zero =>
    obtain ⟨i, hi⟩ := win
    exact ⟨0, i.succ, by simpa [team] using congrArg embed hi⟩
  | succ t ih =>
    rcases win with ⟨i, hi⟩ | ⟨d, hd, ⟨i, hi⟩ | cont⟩
    · exact ⟨0, i.succ, by simpa [team] using congrArg embed hi⟩
    · refine ⟨1, Or.inr ⟨team (target p (embed r)) (fun j => embed (d j)),
        team_step aligned (fun j => embed_step (hd j)), Or.inl ⟨i.succ, ?_⟩⟩⟩
      simpa [team] using congrArg embed hi
    · apply advance (team_step aligned (fun j => embed_step (hd j)))
      intro s hs
      have ready := target_step p hs
      obtain hpath | ⟨w, rfl, hw⟩ := reply r hs
      · exact hit_guard p geo ready hpath _
      · exact ih (cont w hw) ready

end Meyniel.Guard

namespace Meyniel.Guard

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b : V} {k : ℕ}

/-- Once the guard has synchronized, the other cops can travel along any
fixed routes in the full graph. The robber can enter the boundary during
deployment, in which event the guard immediately finishes the game. -/
private lemma deploy [Fintype V] {p : G.Walk a b} (geo : p.length = G.dist a b)
    {C : (Outside p).ConnectedComponent} (route : ℕ → Fin k → V)
    (moves : ∀ j i, Step G (route j i) (route (j+1) i)) (L : ℕ)
    (finish : ∀ (r : C) (g : V), Step G g (target p (embed r)) →
      ∃ t, CatchesWithin G (k+1) t (team g (route L)) (embed r)) :
    ∀ (remaining j : ℕ), j + remaining = L → ∀ (r : C) (g : V),
      Step G g (target p (embed r)) →
      ∃ t, CatchesWithin G (k+1) t (team g (route j)) (embed r) := by
  intro remaining
  induction remaining with
  | zero =>
    intro j hj
    have e : j = L := by omega
    subst j
    exact finish
  | succ m ih =>
    intro j hj r g hg
    apply advance (team_step hg (moves j))
    intro s hs
    have ready := target_step p hs
    obtain hpath | ⟨w, rfl, _⟩ := reply r hs
    · exact hit_guard p geo ready hpath _
    · exact ih (j+1) (by omega) w _ ready

private lemma walk_step (w : G.Walk a b) (j : ℕ) :
    Step G (w.getVert j) (w.getVert (j+1)) := by
  by_cases hj : j < w.length
  · exact Or.inr (w.adj_getVert_succ hj)
  · exact Or.inl ((w.getVert_of_length_le (by omega)).trans
      (w.getVert_of_length_le (by omega)).symm)

private lemma start_in_component [Fintype V] (conn : G.Connected) {p : G.Walk a b}
    (geo : p.length = G.dist a b) {C : (Outside p).ConnectedComponent}
    (win : WinsWith C.toSimpleGraph k) (r : C) (g : V) (ready : Step G g (target p (embed r))) :
    ∃ t, CatchesWithin G (k+1) t (team g (fun _ => a : Fin k → V)) (embed r) := by
  classical
  obtain ⟨c, hc⟩ := win
  let ws (i : Fin k) : G.Walk a (embed (c i)) := (conn a (embed (c i))).some
  let L := Finset.univ.sup (fun i => (ws i).length)
  let route (j : ℕ) (i : Fin k) := (ws i).getVert j
  have endroute : route L = (fun i => embed (c i)) := by
    funext i
    exact (ws i).getVert_of_length_le (Finset.le_sup (f := fun i => (ws i).length) (Finset.mem_univ i))
  have start : route 0 = (fun _ => a) := by funext i; simp [route]
  have finish : ∀ (s : C) (u : V), Step G u (target p (embed s)) →
      ∃ t, CatchesWithin G (k+1) t (team u (route L)) (embed s) := by
    intro s u hu
    rw [endroute]
    obtain ⟨t, ht⟩ := hc s
    exact play_inside geo ht hu
  rw [← start]
  exact deploy geo route (fun j i => walk_step (ws i) j) L finish L 0 (by omega) r g ready

private lemma acquire [Fintype V] (p : G.Walk a b) (tail : Fin k → V)
    (finish : ∀ r g, Step G g (target p r) → ∃ t, CatchesWithin G (k+1) t (team g tail) r) :
    ∀ (fuel i : ℕ), i ≤ p.length → p.length ≤ i + fuel → ∀ r, i ≤ shadow p r + 1 →
      ∃ t, CatchesWithin G (k+1) t (team (p.getVert i) tail) r := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hi hf r hnear
    apply finish
    apply vertices_step p hi (min_le_left ..)
    have : shadow p r ≤ p.length := min_le_left .. 
    exact ⟨hnear, show shadow p r ≤ i + 1 by omega⟩
  | succ m ih =>
    intro i hi hf r hnear
    by_cases ready : shadow p r ≤ i + 1
    · exact finish _ _ (vertices_step p hi (min_le_left ..) ⟨hnear, ready⟩)
    · have hbound : shadow p r ≤ p.length := min_le_left ..
      have hadj : G.Adj (p.getVert i) (p.getVert (i+1)) := p.adj_getVert_succ (by omega)
      apply advance (team_step (Or.inr hadj) (fun _ => Or.inl rfl))
      intro s hs
      have hstep := shadow_step p hs
      exact ih (i+1) (by omega) (by omega) s (by omega)

/-- One geodesic guard plus a team that wins in each possible residual
component wins in the full graph. The team starts together before the robber
is placed. The winning component and the routes to its starts are chosen
only after the guard acquires its projection. -/
theorem wins_with_guard [Fintype V] (conn : G.Connected) (p : G.Walk a b)
    (geo : p.length = G.dist a b)
    (win : ∀ C : (Outside p).ConnectedComponent, WinsWith C.toSimpleGraph k) :
    WinsWith G (k+1) := by
  classical
  let tail : Fin k → V := fun _ => a
  refine ⟨team a tail, fun r => ?_⟩
  have finish : ∀ s g, Step G g (target p s) →
      ∃ t, CatchesWithin G (k+1) t (team g tail) s := by
    intro s g hs
    by_cases hp : s ∈ p.support
    · exact hit_guard p geo hs hp tail
    · let v : {x : V | x ∉ p.support} := ⟨s, hp⟩
      let C := (Outside p).connectedComponentMk v
      let w : C := ⟨v, ConnectedComponent.connectedComponentMk_mem⟩
      exact start_in_component conn geo (win C) w g hs
  simpa only [Walk.getVert_zero] using acquire p tail finish p.length 0 (by omega)
    (by omega) r (by omega)

end Meyniel.Guard

namespace Meyniel.Guard

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} {a b : V}

private lemma keep_extra {k t : ℕ} {c : Fin k → V} {r : V}
    (h : CatchesWithin G k t c r) (extra : V) : CatchesWithin G (k+1) t (team extra c) r := by
  induction t generalizing c r with
  | zero =>
    obtain ⟨i, hi⟩ := h
    exact ⟨i.succ, by simpa [team] using hi⟩
  | succ t ih =>
    rcases h with ⟨i, hi⟩ | ⟨d, hd, ⟨i, hi⟩ | cont⟩
    · exact Or.inl ⟨i.succ, by simpa [team] using hi⟩
    · exact Or.inr ⟨team extra d, team_step (Or.inl rfl) hd, Or.inl ⟨i.succ, by simpa [team] using hi⟩⟩
    · exact Or.inr ⟨team extra d, team_step (Or.inl rfl) hd, Or.inr (fun s hs => ih (cont s hs))⟩

theorem winsWith_more [Nonempty V] {k m : ℕ} (hm : k ≤ m) (w : WinsWith G k) : WinsWith G m := by
  classical
  induction m, hm using Nat.le_induction with
  | base => exact w
  | succ j _ ih =>
    obtain ⟨c, hc⟩ := ih
    let extra : V := Classical.arbitrary V
    refine ⟨team extra c, fun r => ?_⟩
    obtain ⟨t, ht⟩ := hc r
    exact ⟨t, keep_extra ht extra⟩

/-- A surviving component excludes every vertex of the guarded path, even
when deletion has removed further components as well. -/
lemma component_card_add_path_le [Fintype V] [DecidableEq V] (p : G.Walk a b)
    (C : (Outside p).ConnectedComponent) [Fintype C] :
    Fintype.card C + p.support.toFinset.card ≤ Fintype.card V := by
  classical
  have hcard : Fintype.card C ≤ Fintype.card {x : V | x ∉ p.support} :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hsize : Fintype.card {x : V | x ∈ p.support} = p.support.toFinset.card :=
    Fintype.card_of_subtype _ (by simp)
  have hle : p.support.toFinset.card ≤ Fintype.card V := Finset.card_le_univ _
  have compl : Fintype.card {x : V | x ∉ p.support} = Fintype.card V - Fintype.card {x : V | x ∈ p.support} :=
    @Fintype.card_subtype_compl V _ (fun x => x ∈ p.support)
      (inferInstanceAs (Fintype ↑({x : V | x ∈ p.support} : Set V)))
      (inferInstanceAs (Fintype ↑({x : V | x ∉ p.support} : Set V)))
  rw [compl, hsize] at hcard
  omega

/-- With a uniform budget K for connected graphs of diameter at most D and
order at most N, an arbitrary connected graph in that order range needs at
most K plus ⌊|V|/D⌋ cops. Each new guard consumes at least D vertices.
The proof recursively restarts inside the intrinsic residual graph. -/
theorem diameter_reduction [Fintype V] (conn : G.Connected) {N K D : ℕ}
    (hsize : Fintype.card V ≤ N) (hD : 0 < D)
    (hsmall : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W), H.Connected →
      Fintype.card W ≤ N → H.diam ≤ D → WinsWith H K) :
    WinsWith G (K + Fintype.card V / D) := by
  classical
  have all : ∀ m : ℕ, ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      H.Connected → Fintype.card W = m → m ≤ N → WinsWith H (K + m / D) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro W _ H hc hm hmN
      letI : Nonempty W := hc.nonempty
      by_cases hd : H.diam ≤ D
      · exact winsWith_more (Nat.le_add_right K (m / D)) (hsmall W H hc (hm.le.trans hmN) hd)
      obtain ⟨u, v, p, geo, _, hp⟩ := exists_diametral_guard_path hc
      have cardP : p.support.toFinset.card ≤ Fintype.card W := Finset.card_le_univ _
      have one : 1 ≤ m / D := (Nat.le_div_iff_mul_le hD).mpr (by simpa using (show D ≤ m by omega))
      have w : WinsWith H ((K + (m / D - 1)) + 1) := by
        apply wins_with_guard hc p geo
        intro C
        letI : Fintype C := Fintype.ofFinite C
        letI : Nonempty C := C.connected_toSimpleGraph.nonempty
        have dec := component_card_add_path_le p C
        have less : Fintype.card C < m := by omega
        have sub := ih (Fintype.card C) less C C.toSimpleGraph C.connected_toSimpleGraph rfl (by omega)
        have addD : Fintype.card C + D ≤ m := by omega
        have ddiv : Fintype.card C / D + 1 ≤ m / D := by
          rw [← Nat.add_div_right _ hD]
          exact Nat.div_le_div_right addD
        exact winsWith_more (by omega) sub
      exact winsWith_more (by omega) w
  exact all (Fintype.card V) V G conn rfl hsize

end Meyniel.Guard
