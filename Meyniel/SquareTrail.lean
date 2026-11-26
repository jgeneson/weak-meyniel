module

public import Meyniel.Game
public import Mathlib.Combinatorics.SimpleGraph.Diam

/-! Two real rounds simulate one move of the graph-square game. Repeated wins
on the square assemble an arbitrary reserve at the two-round-old robber
position, while a prescribed group of other cops can wait at fixed starts. -/

@[expose] public section

namespace Meyniel.SquareTrail

universe u
variable {V : Type u} {G : SimpleGraph V}

theorem step_symm {a b : V} (h : Step G a b) : Step G b a :=
  h.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)

/-- Distinct points are adjacent in the square when two legal physical
steps (possibly including a wait) take one to the other. -/
def square (G : SimpleGraph V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ m, Step G a m ∧ Step G m b
  symm := ⟨fun _ _ ⟨ne, m, h, k⟩ => ⟨ne.symm, m, step_symm k, step_symm h⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem step_square_iff {a b : V} : Step (square G) a b ↔ ∃ m, Step G a m ∧ Step G m b := by
  constructor
  · rintro (rfl | ⟨_,h⟩)
    · exact ⟨a,Or.inl rfl,Or.inl rfl⟩
    · exact h
  · intro h
    by_cases eq : a = b
    · exact Or.inl eq
    · exact Or.inr ⟨eq,h⟩

theorem le_square : G ≤ square G :=
  fun _ _ h => ⟨h.ne, _, Or.inl rfl, Or.inr h⟩

theorem connected_square (hc : G.Connected) : (square G).Connected :=
  SimpleGraph.Connected.mono le_square hc

private theorem short_dist {a b : V} (h : Step (square G) a b) : (square G).dist a b ≤ 1 := by
  rcases h with rfl | h
  · simp
  · exact (SimpleGraph.dist_eq_one_iff_adj.mpr h).le

private theorem compressed_length (hc : G.Connected) {a b : V} (p : G.Walk a b) :
    (square G).dist a b ≤ (p.length+1)/2 := by
  have run : ∀ L (a b : V) (p : G.Walk a b), p.length = L → (square G).dist a b ≤ (L+1)/2 := by
    intro L
    induction L using Nat.strong_induction_on with
    | h L ih =>
      intro a b p hp
      cases p with
      | nil => simp
      | cons h tail =>
        cases tail with
        | nil =>
          simp at hp
          simpa [←hp] using short_dist (Or.inr (le_square h))
        | cons h' q =>
          have hh := short_dist (step_square_iff.mpr ⟨_,Or.inr h,Or.inr h'⟩)
          simp only [SimpleGraph.Walk.length_cons] at hp
          have ht := ih q.length (by omega) _ _ q rfl
          rename_i mid
          have hd := (connected_square hc).dist_triangle (u := a) (v := mid) (w := b)
          omega
  exact run p.length a b p rfl

/-- An integer upper bound on the diameter after a two-round simulation. -/
theorem diameter_square [Fintype V] (hc : G.Connected) :
    (square G).diam ≤ (G.diam+1)/2 := by
  letI := hc.nonempty
  obtain ⟨a,b,hab⟩ := (square G).exists_dist_eq_diam
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a b
  have h := compressed_length hc p
  have h' : G.dist a b ≤ G.diam := SimpleGraph.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc)
  omega

private abbrev CanWin (G : SimpleGraph V) {n : ℕ} (c : Fin n → V) (r : V) :=
  ∃ t, CatchesWithin G n t c r

private theorem more_time {n t : ℕ} {c : Fin n → V} {r : V} (h : CatchesWithin G n t c r) :
    CatchesWithin G n (t+1) c r := by
  induction t generalizing c r with
  | zero => exact Or.inl h
  | succ t ih =>
    rcases h with hit | ⟨d,hd,hit | next⟩
    · exact Or.inl hit
    · exact Or.inr ⟨d,hd,Or.inl hit⟩
    · exact Or.inr ⟨d,hd,Or.inr fun r' hr' => ih (next r' hr')⟩

private theorem advance [Fintype V] {n : ℕ} {c d : Fin n → V} {r : V}
    (hm : ∀ i, Step G (c i) (d i)) (h : ∀ s, Step G r s → CanWin G d s) : CanWin G c r := by
  classical
  have hp : ∀ s, ∃ t, Step G r s → CatchesWithin G n t d s := by
    intro s
    by_cases hs : Step G r s
    · obtain ⟨t, ht⟩ := h s hs
      exact ⟨t,fun _ => ht⟩
    · exact ⟨0,fun hn => (hs hn).elim⟩
  choose times hh using hp
  refine ⟨Finset.univ.sup times + 1, Or.inr ⟨d,hm,Or.inr fun s hs => ?_⟩⟩
  have le := Finset.le_sup (f := times) (Finset.mem_univ s)
  exact Nat.le_induction (hh s hs) (fun _ _ => more_time) _ le

/-- Place the designated searchers at the specified vertices, leaving all
other coordinates at the supplied default positions. -/
private noncomputable def place {s n : ℕ} (f : Fin s ↪ Fin n) (d : Fin s → V)
    (rest : Fin n → V) (i : Fin n) : V := by
  classical
  exact if h : ∃ j, f j = i then d h.choose else rest i

@[simp] private theorem place_at {s n : ℕ} (f : Fin s ↪ Fin n) (d : Fin s → V)
    (rest : Fin n → V) (j : Fin s) : place f d rest (f j) = d j := by
  classical
  simp [place]

private theorem place_off {s n : ℕ} (f : Fin s ↪ Fin n) (d : Fin s → V)
    (rest : Fin n → V) {i : Fin n} (hi : ∀ j, f j ≠ i) : place f d rest i = rest i := by
  classical
  simp [place, not_exists.mpr hi]

private theorem place_step {n s : ℕ} (f : Fin s ↪ Fin n) {c rest : Fin n → V} {d : Fin s → V}
    (h : ∀ j, Step G (c (f j)) (d j)) (hr : ∀ i, Step G (c i) (rest i)) :
    ∀ i, Step G (c i) (place f d rest i) := by
  classical
  intro i
  by_cases hi : ∃ j, f j = i
  · obtain ⟨j,rfl⟩ := hi
    simpa using h j
  · simpa [place,hi] using hr i


/-- Occupied slots reserve their current lagged position, while static cops
keep the same positions during all of the search phases. -/
private def Ready {n : ℕ} (tracked parked : Finset (Fin n)) (initial c : Fin n → V) (x : V) : Prop :=
  (∀ i ∈ tracked, c i = x) ∧ ∀ i ∈ parked, c i = initial i

private theorem move_searchers {n s : ℕ} {tracked parked : Finset (Fin n)}
    {init c : Fin n → V} {x y : V} (f : Fin s ↪ Fin n)
    (free : ∀ j, f j ∉ tracked ∧ f j ∉ parked) (dis : Disjoint tracked parked)
    (ok : Ready tracked parked init c x) (xy : Step G x y)
    (next : Fin s → V) (legal : ∀ j, Step G (c (f j)) (next j)) :
    ∃ d : Fin n → V, (∀ i, Step G (c i) (d i)) ∧ (∀ j, d (f j) = next j) ∧
      Ready tracked parked init d y := by
  classical
  let rest (i : Fin n) := if i ∈ tracked then y else c i
  refine ⟨place f next rest, place_step f legal (fun i => ?_), (fun j => place_at f next rest j), ?_, ?_⟩
  · by_cases hi : i ∈ tracked
    · simpa [rest,hi,ok.1 i hi] using xy
    · simp [rest,hi,Step]
  · intro i hi
    rw [place_off f next rest (fun j hj => (free j).1 (hj ▸ hi))]
    simp [rest,hi]
  · intro i hi
    rw [place_off f next rest (fun j hj => (free j).2 (hj ▸ hi))]
    have off : i ∉ tracked := fun hj => Finset.disjoint_left.mp dis hj hi
    simp [rest, off, ok.2 i hi]

private theorem walk_step {a b : V} (p : G.Walk a b) (j : ℕ) : Step G (p.getVert j) (p.getVert (j+1)) := by
  by_cases h : j < p.length
  · exact Or.inr (p.adj_getVert_succ h)
  · exact Or.inl ((p.getVert_of_length_le (by omega)).trans (p.getVert_of_length_le (by omega)).symm)

/-- Searchers may restart at their prescribed virtual starting positions. -/
private theorem redeploy [Fintype V] {n s : ℕ} {tracked parked : Finset (Fin n)} {init : Fin n → V}
    (f : Fin s ↪ Fin n) (free : ∀ j, f j ∉ tracked ∧ f j ∉ parked) (dis : Disjoint tracked parked)
    (target : Fin s → V) (conn : G.Connected)
    (finish : ∀ c x y r, Ready tracked parked init c x → Step G x y → Step G y r →
      (∀ j, c (f j) = target j) → CanWin G c r)
    (c : Fin n → V) (x y r : V) (ok : Ready tracked parked init c x) (xy : Step G x y) (yr : Step G y r) :
    CanWin G c r := by
  classical
  let routes (i : Fin s) : G.Walk (c (f i)) (target i) := (conn _ _).some
  let L := Finset.univ.sup (fun i => (routes i).length)
  have reach : ∀ fuel time, time + fuel = L → ∀ c' x' y' r', Ready tracked parked init c' x' →
      Step G x' y' → Step G y' r' → (∀ i, c' (f i) = (routes i).getVert time) → CanWin G c' r' := by
    intro fuel
    induction fuel with
    | zero =>
      intro time h c' x' y' r' ok' h1 h2 at'
      change time = L at h
      subst time
      apply finish c' x' y' r' ok' h1 h2
      intro i
      exact (at' i).trans ((routes i).getVert_of_length_le (Finset.le_sup (f := fun i => (routes i).length) (Finset.mem_univ i)))
    | succ fuel ih =>
      intro time h c' x' y' r' ok' h1 h2 at'
      obtain ⟨d,hm,atd,okd⟩ := move_searchers f free dis ok' h1
        (fun i => (routes i).getVert (time+1)) (fun i => (at' i).symm ▸ walk_step (routes i) time)
      exact advance hm (fun r'' hr'' => ih (time+1) (by omega) d y' r' r'' okd h2 hr'' atd)
  exact reach L 0 (by omega) c x y r ok xy yr (fun i => by simp [routes])

/-- A successful move by a virtual cop puts a physical cop at the current
robber vertex two rounds later. A virtual capture at a checkpoint is already
a physical capture. Members of the previously formed trail keep moving. -/
private theorem simulate [Fintype V] {n s : ℕ} {tracked parked : Finset (Fin n)} {init : Fin n → V}
    (f : Fin s ↪ Fin n) (free : ∀ j, f j ∉ tracked ∧ f j ∉ parked) (dis : Disjoint tracked parked)
    (finish : ∀ j c x y r, Ready (insert (f j) tracked) parked init c x →
      Step G x y → Step G y r → CanWin G c r) :
    ∀ t (c : Fin n → V) x y r, Ready tracked parked init c x → Step G x y → Step G y r →
      CatchesWithin (square G) s t (fun j => c (f j)) r → CanWin G c r := by
  intro t
  induction t with
  | zero =>
    intro c x y r _ _ _ h
    obtain ⟨j,hj⟩ := h
    exact ⟨0, f j, hj⟩
  | succ t ih =>
    intro c x y r ok xy yr h
    rcases h with ⟨j,hj⟩ | ⟨z,hz,win⟩
    · exact ⟨0,f j,hj⟩
    have bridge (j : Fin s) := step_square_iff.mp (hz j)
    choose mid hm₁ hm₂ using bridge
    obtain ⟨d,hd,mid_at,okd⟩ := move_searchers f free dis ok xy mid hm₁
    apply advance hd
    intro a ra
    obtain ⟨e,he,end_at,oke⟩ := move_searchers f free dis okd yr z (fun j => (mid_at j).symm ▸ hm₂ j)
    apply advance he
    intro b ab
    rcases win with ⟨j,hj⟩ | hn
    · apply finish j e r a b _ ra ab
      refine ⟨?_,oke.2⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact (end_at j).trans hj
      · exact oke.1 i hi
    · have hh := hn b (step_square_iff.mpr ⟨a,ra,ab⟩)
      have eq : (fun j => e (f j)) = z := funext end_at
      exact ih e r a b oke ra ab (eq ▸ hh)


/-- Assemble k search successes without moving any parked cops. Every round
already acquired cops follow one edge of the robber's recorded trail. -/
private theorem acquire [Fintype V] {n s k : ℕ} (conn : G.Connected) (virtual : WinsWith (square G) s)
    (parked : Finset (Fin n)) (init : Fin n → V) (capacity : k+s ≤ parkedᶜ.card)
    (finish : ∀ A : Finset (Fin n), Disjoint A parked → A.card = k →
      ∀ c x y r, Ready A parked init c x → Step G x y → Step G y r → CanWin G c r) :
    ∀ (fuel : ℕ) (A : Finset (Fin n)), Disjoint A parked → A.card + fuel = k →
      ∀ c x y r, Ready A parked init c x → Step G x y → Step G y r → CanWin G c r := by
  classical
  obtain ⟨starts,winning⟩ := virtual
  intro fuel
  induction fuel with
  | zero =>
    intro A hA hk
    exact finish A hA (by omega)
  | succ fuel ih =>
    intro A dis hk c x y r ok xy yr
    let pool := parkedᶜ \ A
    have inc : A ⊆ parkedᶜ := fun i hi => Finset.mem_compl.mpr (Finset.disjoint_left.mp dis hi)
    have num : s ≤ pool.card := by
      unfold pool
      rw [Finset.card_sdiff_of_subset inc]
      omega
    have emb : Nonempty (Fin s ↪ ↥pool) := Function.Embedding.nonempty_iff_card_le.mpr (by simpa using num)
    let chosen := Classical.choice emb
    let f : Fin s ↪ Fin n := chosen.trans (Function.Embedding.subtype (· ∈ pool))
    have free (j : Fin s) : f j ∉ A ∧ f j ∉ parked := by
      have hj := Finset.mem_sdiff.mp (chosen j).property
      exact ⟨hj.2,Finset.mem_compl.mp hj.1⟩
    apply redeploy f free dis starts conn _ c x y r ok xy yr
    intro c' x' y' r' ok' xy' yr' at'
    obtain ⟨t,win⟩ := winning r'
    apply simulate f free dis _ t c' x' y' r' ok' xy' yr'
    · simpa only [funext at'] using win
    · intro j d a b q
      apply ih (insert (f j) A)
      · exact Finset.disjoint_left.mpr (fun i hi hp => (Finset.mem_insert.mp hi).elim
          (fun eq => (free j).2 (eq ▸ hp)) (fun ha => Finset.disjoint_left.mp dis ha hp))
      · rw [Finset.card_insert_of_notMem (free j).1]; omega

private theorem embed_game {n s : ℕ} (f : Fin s ↪ Fin n) :
    ∀ t (c : Fin n → V) r, CatchesWithin G s t (fun j => c (f j)) r → CatchesWithin G n t c r := by
  classical
  intro t
  induction t with
  | zero =>
    intro c r h
    obtain ⟨j,hj⟩ := h
    exact ⟨f j, hj⟩
  | succ t ih =>
    intro c r h
    rcases h with ⟨j,hj⟩ | ⟨d,hm,cap⟩
    · exact Or.inl ⟨f j,hj⟩
    · let next := place f d c
      have hn (i) : next (f i) = d i := place_at .. 
      refine Or.inr ⟨next,place_step f hm (fun _ => Or.inl rfl),?_⟩
      rcases cap with ⟨j,hj⟩ | cont
      · exact Or.inl ⟨f j,(hn j).trans hj⟩
      · exact Or.inr (fun r' hr' => ih next r' (by simpa only [funext hn] using cont r' hr'))

/-- The hypothesis is the physical continuation used in the multiscale
proof: the first k cops are at the two-round-old vertex x and the other p
cops already occupy their fixed global starting positions. Adding one team
that wins on the square allows the game to begin with ordinary placements. -/
theorem winsWith_from_trail [Fintype V] {s k p : ℕ} (conn : G.Connected)
    (virtual : WinsWith (square G) s) (starts : Fin p → V)
    (finish : ∀ x y r : V, Step G x y → Step G y r →
      ∃ t, CatchesWithin G (k+p) t (Fin.append (fun _ => x) starts) r) :
    WinsWith G ((s+k)+p) := by
  classical
  let n := (s+k)+p
  let parked : Finset (Fin n) := Finset.univ.image (Fin.natAdd (s+k))
  let init : Fin n → V := Fin.append (fun _ => conn.nonempty.some) starts
  have card_parked : parked.card = p := by
    unfold parked
    rw [Finset.card_image_of_injective _ (Fin.natAdd_injective p (s+k))]
    simp
  have capacity : k+s ≤ parkedᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, card_parked]; dsimp [n]; omega
  refine ⟨init,fun r => ?_⟩
  apply acquire conn virtual parked init capacity _ k ∅ (by simp) (by simp) init r r r
  · exact ⟨by simp,fun _ _ => rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · intro A dis ac c x y r ok xy yr
    have have_map : Nonempty (Fin k ↪ ↥A) := Function.Embedding.nonempty_iff_card_le.mpr (by simp [ac])
    let e := Classical.choice have_map
    let pre (j : Fin k) : Fin n := e j
    let st : Fin p → Fin n := Fin.natAdd (s+k)
    have hpre (i) : pre i ∈ A := (e i).property
    have hst (j) : st j ∈ parked := Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    have neq (i j) : pre i ≠ st j := fun he => Finset.disjoint_left.mp dis (hpre i) (he ▸ hst j)
    let f : Fin (k+p) ↪ Fin n := ⟨Fin.append pre st, by
      intro a b
      refine Fin.addCases (fun i => ?_) (fun j => ?_) a <;>
        refine Fin.addCases (fun i' => ?_) (fun j' => ?_) b <;> simp only [Fin.append_left,Fin.append_right]
      · intro eq; exact congrArg _ (e.injective (Subtype.ext eq))
      · intro eq; exact (neq i j' eq).elim
      · intro h; exact (neq i' j h.symm).elim
      · intro eq; exact congrArg _ (Fin.natAdd_injective _ _ eq)⟩
    have hpos : (fun i => c (f i)) = Fin.append (fun _ => x) starts := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · change c (Fin.append pre st (Fin.castAdd p j)) = Fin.append (fun _ => x) starts (Fin.castAdd p j)
        simpa only [Fin.append_left] using ok.1 (pre j) (hpre j)
      · change c (Fin.append pre st (Fin.natAdd k j)) = Fin.append (fun _ => x) starts (Fin.natAdd k j)
        simpa only [Fin.append_right, init, st] using ok.2 (st j) (hst j)
    obtain ⟨t,ht⟩ := finish x y r xy yr
    exact ⟨t,embed_game f t c r (hpos ▸ ht)⟩

end Meyniel.SquareTrail
