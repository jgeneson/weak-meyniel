module

public import Meyniel.Game
public import Meyniel.Interception

/-! # Deterministic backward interception on a family of walks

A cop can choose a different continuation for every revealed vertex. Maximizing
its capture count on each child prefix implements the backward sampling bound
with deterministic policies; the only randomness needed is the averaging over
the tagged walks in the given finite family.
-/

@[expose] public section

namespace Meyniel.Sampler

open Finset

variable {V W : Type*} {G : SimpleGraph V}

def splicePos (x : V) (q : V → Policy G) (h : List V) : V :=
  match h.getLast? with
  | none => x
  | some r => (q r).pos h.dropLast

@[simp] theorem splicePos_append (x : V) (q : V → Policy G) (h : List V) (r : V) :
    splicePos x q (h ++ [r]) = (q r).pos h := by
  simp [splicePos]

/-- After observing r, switch to its preselected continuation; all other choices
remain functions solely of the robber observations. -/
def splice (x : V) (q : V → Policy G) (legal : ∀ r, Step G x ((q r).pos [])) : Policy G where
  pos := splicePos x q
  legal := by
    intro y h
    induction h using List.reverseRecOn with
    | nil => exact legal y
    | append_singleton h r _ =>
      change Step G (splicePos x q (h ++ [r])) (splicePos x q ((y :: h) ++ [r]))
      simp only [splicePos_append]
      exact (q r).legal y h

@[simp] theorem splice_nil (x : V) (q : V → Policy G) (L) : (splice x q L).pos [] = x := rfl

@[simp] theorem splice_append (x : V) (q : V → Policy G) (L) (h : List V) (r : V) :
    (splice x q L).pos (h ++ [r]) = (q r).pos h := splicePos_append ..

private theorem hits_splice (x : V) (q : V → Policy G) (L) (r : V) :
    ∀ (w h : List V), Hits (splice x q L) (h ++ [r]) w ↔ Hits (q r) h w
  | [], _ => Iff.rfl
  | [v], h => by simp [Hits]
  | v :: z :: zs, h => by
    change ((_ = v) ∨ (splice x q L).pos ((v :: h) ++ [r]) = v ∨
      Hits (splice x q L) ((v :: h) ++ [r]) (z :: zs)) ↔ _
    rw [hits_splice x q L r (z :: zs) (v :: h)]
    rw [splice_append x q L (v :: h) r, splice_append x q L h r]
    rfl

/-- What is captured after revealing r and committing to q, including immediate
collision and the absence of a final cop turn on a singleton walk. -/
def stageHits (x r : V) (q : Policy G) : List V → Prop
  | [] => x = r
  | z :: zs => x = r ∨ q.pos [] = r ∨ Hits q [] (z :: zs)

theorem stageHits_splice (x r : V) (q : V → Policy G) (L) (w : List V) :
    Hits (splice x q L) [] (r :: w) ↔ stageHits x r (q r) w := by
  cases w with
  | nil => rfl
  | cons z zs =>
    change (x = r ∨ _ = r ∨ Hits (splice x q L) ([] ++ [r]) (z :: zs)) ↔ _
    rw [hits_splice]
    rfl

noncomputable def count (A : Finset W) (P : W → Prop) : ℕ := by
  classical exact (A.filter P).card

theorem count_le (A : Finset W) (P : W → Prop) : count A P ≤ A.card := by
  classical exact card_filter_le ..

theorem exists_best {S : Type*} (witness : S) (f : S → ℕ) (cap : ℕ)
    (hle : ∀ q, f q ≤ cap) : ∃ q, ∀ z, f z ≤ f q := by
  have hb : BddAbove (Set.range f) := ⟨cap, by rintro _ ⟨s,rfl⟩; exact hle s⟩
  obtain ⟨q, hq⟩ := Nat.sSup_mem (s := Set.range f) ⟨f witness, witness, rfl⟩ hb
  exact ⟨q, fun z => hq ▸ le_csSup hb ⟨z,rfl⟩⟩

/-- An optimal single cop among all policies with the indicated initial vertex. -/
noncomputable def optimal (G : SimpleGraph V) (A : Finset W) (route : W → List V) (x : V) :
    {s : Policy G // s.pos [] = x} :=
  Classical.choose (exists_best (⟨Policy.stay G x, rfl⟩ : {s : Policy G // s.pos [] = x})
    (fun s => count A fun w => Hits s.1 [] (route w)) A.card (fun _ => count_le ..))

noncomputable def bestCount (G : SimpleGraph V) (A : Finset W) (route : W → List V) (x : V) : ℕ :=
  count A fun w => Hits (optimal G A route x).1 [] (route w)

theorem count_le_best (A : Finset W) (route : W → List V) (x : V) (q : Policy G) (hq : q.pos [] = x) :
    (count A fun w => Hits q [] (route w)) ≤ bestCount G A route x := by
  exact (Classical.choose_spec (exists_best (⟨Policy.stay G x, rfl⟩ : {s : Policy G // s.pos [] = x})
    (fun s => count A fun w => Hits s.1 [] (route w)) A.card (fun _ => count_le ..))) ⟨q,hq⟩

/-- The strategy selected for a child prefix can commit to any legal first move. -/
noncomputable def bestChild (G : SimpleGraph V) (A : Finset W) (tail : W → List V) (x r : V) :
    {q : Policy G // Step G x (q.pos [])} :=
  Classical.choose (exists_best (⟨Policy.stay G x, Or.inl rfl⟩ : {s : Policy G // Step G x (s.pos [])})
    (fun q => count A fun w => stageHits x r q.1 (tail w)) A.card (fun _ => count_le ..))

noncomputable def childCount (G : SimpleGraph V) (A : Finset W) (tail : W → List V) (x r : V) : ℕ :=
  count A fun w => stageHits x r (bestChild G A tail x r).1 (tail w)

theorem count_le_child (A : Finset W) (tail : W → List V) (x r : V) (q : Policy G)
    (hq : Step G x (q.pos [])) :
    (count A fun w => stageHits x r q (tail w)) ≤ childCount G A tail x r := by
  exact (Classical.choose_spec (exists_best (⟨Policy.stay G x, Or.inl rfl⟩ : {s : Policy G // Step G x (s.pos [])})
    (fun s => count A fun w => stageHits x r s.1 (tail w)) A.card (fun _ => count_le ..))) ⟨q,hq⟩

/-- Splitting the capture count among the possible revealed vertices is exact. -/
private theorem count_partition [Fintype V] [DecidableEq V] (A : Finset W) (obs : W → V) (P : W → Prop) :
    (∑ r, count (A.filter fun z => obs z = r) P) = count A P := by
  classical
  simpa only [count, Finset.card_filter] using Finset.sum_fiberwise A obs (fun z => if P z then 1 else (0:ℕ))

/-- Maximizing the first response independently at each possible revelation is
realizable by one policy starting at x, even for prefixes outside the family. -/
theorem sum_childCount_le_best [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset W)
    (obs : W → V) (tail : W → List V) (x : V) :
    (∑ r, childCount G (A.filter fun z => obs z = r) tail x r) ≤
      bestCount G A (fun z => obs z :: tail z) x := by
  classical
  let q := fun r => bestChild G (A.filter fun z => obs z = r) tail x r
  let s := splice x (fun r => (q r).1) (fun r => (q r).2)
  calc
    _ = ∑ r, count (A.filter fun z => obs z = r) (fun z => Hits s [] (obs z :: tail z)) := by
      apply Finset.sum_congr rfl; intro r _
      change ((A.filter _).filter _).card = ((A.filter _).filter _).card
      congr 1
      apply Finset.filter_congr
      intro w hw
      obtain ⟨_,hr⟩ := Finset.mem_filter.mp hw
      rw [hr]; exact (stageHits_splice x r (fun u => (q u).1) (fun u => (q u).2) (tail w)).symm
    _ = _ := count_partition A obs _
    _ ≤ _ := count_le_best A _ x s rfl

/-- Every compatible tag may propose its own legal backward move. The value
of each such proposal is bounded by the same best response for this child. -/
theorem best_next_le_child (G : SimpleGraph V) (A : Finset W) (tail : W → List V) (x r y : V)
    (hxy : Step G x y) : bestCount G A tail y ≤ childCount G A tail x r := by
  classical
  let s := optimal G A tail y
  apply le_trans _ (count_le_child A tail x r s.1 (s.2.symm ▸ hxy))
  apply Finset.card_le_card; intro w hmem
  obtain ⟨ha,hw⟩ := Finset.mem_filter.mp hmem
  refine Finset.mem_filter.mpr ⟨ha,?_⟩
  change Hits s.1 [] (tail w) at hw
  cases H : tail w with
  | nil => simp [H,Hits] at hw
  | cons z zs => exact Or.inr (Or.inr (H ▸ hw))

/-- At a terminal entry every walk with the compatible revealed vertex is
captured, either immediately or on the next cop turn if there is one. -/
theorem all_le_child (G : SimpleGraph V) (A : Finset W) (tail : W → List V) (x r : V)
    (hxy : Step G x r) (ht : ∀ w ∈ A, x = r ∨ tail w ≠ []) :
    A.card ≤ childCount G A tail x r := by
  classical
  apply le_trans _ (count_le_child A tail x r (Policy.stay G r) hxy)
  apply Finset.card_le_card
  intro w hw; apply Finset.mem_filter.mpr; refine ⟨hw, ?_⟩
  cases H : tail w with
  | nil => exact (ht w hw).resolve_right (not_not.mpr H)
  | cons z zs => exact Or.inr (Or.inl rfl)

/-- Each tag in one observed child is weighted by the inverse size of its
fiber. This permits the guesses for different tags to overlap arbitrarily. -/
theorem sum_div_fiber_le [Fintype V] [DecidableEq V] (M : Finset W) (obs : W → V)
    (a : W → ℝ) (c : V → ℕ) (h : ∀ w ∈ M, a w ≤ c (obs w)) :
    (∑ w ∈ M, a w / (M.filter fun z => obs z = obs w).card) ≤ ∑ r, (c r : ℝ) := by
  classical
  rw [← Finset.sum_fiberwise M obs]
  apply Finset.sum_le_sum
  intro r _
  let B := M.filter fun z => obs z = r
  change (∑ w ∈ B, _) ≤ _
  calc
    _ ≤ ∑ _w ∈ B, (c r : ℝ) / B.card := by
      apply Finset.sum_le_sum; intro w hw
      obtain ⟨hm,hr⟩ := Finset.mem_filter.mp hw
      rw [hr]; exact div_le_div_of_nonneg_right (hr ▸ h w hm) (Nat.cast_nonneg _)
    _ ≤ _ := by
      by_cases hb : B.Nonempty
      · have h0 : (B.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hb
        simp only [Finset.sum_const, nsmul_eq_mul]; field_simp; exact le_rfl
      · simp [Finset.not_nonempty_iff_eq_empty.mp hb]

open Interception

/-- The observed prefix before reveal t (newest observation first). -/
def past (X : ℕ → W → V) : ℕ → W → List V
  | 0, _ => []
  | t+1, w => X t w :: past X t w

/-- Chronological, with exactly the real robber observations still available. -/
def remainder (X : ℕ → W → V) (T t : ℕ) (w : W) : List V :=
  List.ofFn (fun i : Fin (T+1-t) => X (t+i.val) w)

private theorem remainder_cons (X : ℕ → W → V) (T t : ℕ) (ht : t ≤ T) (w : W) :
    remainder X T t w = X t w :: remainder X T (t+1) w := by
  unfold remainder
  have hh : T+1-t = (T+1-(t+1))+1 := by omega
  conv_lhs => rw [hh]
  rw [List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn; funext i; congr 1; simp [Fin.val_succ]; omega

variable [Fintype W] [DecidableEq V]

def oldPrefix (X : ℕ → W → V) (t : ℕ) (w : W) := fiber (past X t) (past X t w)

def key (X : ℕ → W → V) (t j : ℕ) (w : W) := (past X t w, X j w)

def tags (X : ℕ → W → V) (t j : ℕ) (w : W) := fiber (key X t j) (key X t j w)

noncomputable def conditional (X : ℕ → W → V) (t j : ℕ) (w : W) : ℝ :=
  ((tags X t j w).card : ℝ)/(oldPrefix X t w).card

private theorem mem_prefix {X : ℕ→W→V} {t : ℕ} {w z : W} :
    z ∈ oldPrefix X t w ↔ past X t z = past X t w := by simp [oldPrefix,fiber]

private theorem mem_tags {X : ℕ→W→V} {t j : ℕ} {w z : W} :
    z ∈ tags X t j w ↔ past X t z = past X t w ∧ X j z = X j w := by simp [tags,key,fiber]

private theorem prefix_pos (X : ℕ→W→V) (t : ℕ) (w : W) : 0 < ((oldPrefix X t w).card : ℝ) := by
  exact_mod_cast (show (oldPrefix X t w).Nonempty from ⟨w, mem_prefix.mpr rfl⟩).card_pos

private theorem tags_pos (X : ℕ→W→V) (t j : ℕ) (w : W) : 0 < ((tags X t j w).card : ℝ) := by
  exact_mod_cast (show (tags X t j w).Nonempty from ⟨w, mem_tags.mpr ⟨rfl,rfl⟩⟩).card_pos

theorem conditional_pos (X : ℕ→W→V) (t j : ℕ) (w : W) : 0 < conditional X t j w :=
  div_pos (tags_pos ..) (prefix_pos ..)

private theorem child_prefix {X : ℕ→W→V} {t j : ℕ} {w z : W} (hz : z ∈ tags X t j w) :
    (oldPrefix X t w).filter (fun y => X t y = X t z) = oldPrefix X (t+1) z := by
  ext u
  obtain ⟨hp,-⟩ := mem_tags.mp hz
  simp only [Finset.mem_filter, mem_prefix, past, List.cons.injEq]
  rw [hp]; tauto

private theorem child_tags {X : ℕ→W→V} {t j : ℕ} {w z : W} (hz : z ∈ tags X t j w) :
    (tags X t j w).filter (fun y => X t y = X t z) = tags X (t+1) j z := by
  ext u
  obtain ⟨hp,hx⟩ := mem_tags.mp hz
  simp only [Finset.mem_filter, mem_tags, past, List.cons.injEq]
  rw [hp,hx]; tauto

/-- At the fictitious row after the terminal entry the value is one. -/
noncomputable def value (G : SimpleGraph V) (X : ℕ→W→V) (T b t : ℕ) (w : W) : ℝ :=
  if t ≤ b/2 then (bestCount G (oldPrefix X t w) (remainder X T t) (X (b-t) w) : ℝ) /
    (oldPrefix X t w).card else 1

omit [DecidableEq V] in
private theorem step_symm {x y : V} (h : Step G x y) : Step G y x :=
  h.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)

/-- The best number of continuations after one observed vertex dominates every
compatible tag's next value, including both types of terminal entry. -/
private theorem child_dominates (G : SimpleGraph V) (X : ℕ→W→V) (T b t j : ℕ)
    (hb : b ≤ 2*T) (ht : t ≤ b/2) (hj : j=b-t) (w z : W) (hz : z ∈ tags X t j w)
    (leg : ∀ i w, Step G (X i w) (X (i+1) w)) :
    value G X T b (t+1) z * (oldPrefix X (t+1) z).card ≤
    childCount G ((oldPrefix X t w).filter fun y => X t y = X t z)
      (remainder X T (t+1)) (X j w) (X t z) := by
  rw [child_prefix hz, ← (mem_tags.mp hz).2]
  by_cases hnext : t+1 ≤ b/2
  · have hi : b-(t+1)+1 = j := by omega
    have hmove := step_symm (leg (b-(t+1)) z)
    rw [hi] at hmove
    simp only [value, if_pos hnext, div_mul_cancel₀ _ (prefix_pos X (t+1) z).ne']
    exact_mod_cast best_next_le_child G _ _ _ _ _ hmove
  · simp only [value, if_neg hnext, one_mul]
    have split : j=t ∨ j=t+1 := by omega
    apply Nat.cast_le.mpr
    apply all_le_child
    · rcases split with rfl | rfl
      · exact Or.inl rfl
      · exact step_symm (leg t z)
    · intro u _
      rcases split with rfl | rfl
      · exact Or.inl rfl
      · right; intro he
        have hlen := congrArg List.length he
        simp [remainder] at hlen; omega

variable [Fintype V]

/-- The finite Bellman inequality on each old-prefix, guessed-vertex fiber. -/
theorem cell_bound (G : SimpleGraph V) (X : ℕ→W→V) (T b t j : ℕ)
    (hb : b ≤ 2*T) (ht : t ≤ b/2) (hj : j=b-t) (w : W)
    (leg : ∀ i w, Step G (X i w) (X (i+1) w)) :
    blockMean (key X t j) (fun z => value G X T b (t+1) z * conditional X t j z /
      conditional X (t+1) j z) w ≤ value G X T b t w := by
  classical
  let A := oldPrefix X t w
  let M := tags X t j w
  let c := fun r => childCount G (A.filter fun y => X t y = r) (remainder X T (t+1)) (X j w) r
  let N := fun z => value G X T b (t+1) z * (oldPrefix X (t+1) z).card
  let f := fun z => N z / (M.filter fun y => X t y = X t z).card
  have hsum : (∑ z ∈ M, f z) ≤ ∑ r, (c r : ℝ) :=
    sum_div_fiber_le M (X t) N c (fun z hz => child_dominates G X T b t j hb ht hj w z hz leg)
  have hroute : (fun z => X t z :: remainder X T (t+1) z) = remainder X T t := by
    funext z; exact (remainder_cons X T t (by omega) z).symm
  have hcount := sum_childCount_le_best G A (X t) (remainder X T (t+1)) (X j w)
  rw [hroute] at hcount
  have htotal : (∑ r, (c r : ℝ)) ≤ (bestCount G A (remainder X T t) (X j w) : ℝ) := by
    exact_mod_cast hcount
  have hterm (z : W) (hz : z ∈ M) :
      value G X T b (t+1) z * conditional X t j z / conditional X (t+1) j z =
        f z * ((M.card : ℝ) / A.card) := by
    obtain ⟨hp,hx⟩ := mem_tags.mp hz
    have hM : tags X t j z = M := by simp [tags, key, M, hp, hx]
    have hA : oldPrefix X t z = A := by simp [oldPrefix,A,hp]
    dsimp only [f,N]; unfold conditional
    rw [hM,hA, child_tags hz]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  have hm : (M.card : ℝ) ≠ 0 := (tags_pos X t j w).ne'
  change (∑ z ∈ M, _) / (M.card : ℝ) ≤ _
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  rw [value, if_pos ht, ←hj]
  calc
    _ = (∑ z ∈ M, f z) / A.card := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (hsum.trans htotal) (Nat.cast_nonneg _)

/-- The optimal strategy when the starting vertex is also at the cop's disposal. -/
noncomputable def unrestricted (G : SimpleGraph V) (A : Finset W) (route : W → List V) (base : V) : Policy G :=
  Classical.choose (exists_best (Policy.stay G base)
    (fun s => count A fun w => Hits s [] (route w)) A.card (fun _ => count_le ..))

omit [Fintype W] [DecidableEq V] [Fintype V] in
private theorem le_unrestricted (G : SimpleGraph V) (A : Finset W) (route : W → List V) (base x : V) :
    bestCount G A route x ≤ count A (fun w => Hits (unrestricted G A route base) [] (route w)) :=
  (Classical.choose_spec (exists_best (Policy.stay G base)
    (fun s => count A fun w => Hits s [] (route w)) A.card (fun _ => count_le ..))) (optimal G A route x).1

omit [Fintype V] in
private theorem prefix_zero (X : ℕ→W→V) (w : W) : oldPrefix X 0 w = Finset.univ := by
  simp [oldPrefix, fiber, past]

omit [Fintype V] in
private theorem cond_zero (X : ℕ→W→V) (j : ℕ) : conditional X 0 j = frequency (X j) := by
  funext w
  have htag : tags X 0 j w = fiber (X j) (X j w) := by
    ext z; simp [tags, key, fiber, past]
  simp [conditional, prefix_zero, frequency, htag]

omit [Fintype V] in
private theorem cond_le_one (X : ℕ→W→V) (t j : ℕ) (w : W) : conditional X t j w ≤ 1 := by
  unfold conditional
  rw [div_le_one (prefix_pos X t w)]
  exact_mod_cast Finset.card_le_card (show tags X t j w ⊆ oldPrefix X t w from
    fun _ hz => mem_prefix.mpr (mem_tags.mp hz).1)

variable [Nonempty W]

/-- One actual deterministic strategy catches the stated fraction of every
nonempty tagged family. Only the first T+1 vertices are tested for capture;
the later vertices, and the common home, are used solely for choosing guesses. -/
theorem tagged_one_cop (G : SimpleGraph V) (X : ℕ→W→V) (T d n : ℕ) (home : V)
    (leg : ∀ i w, Step G (X i w) (X (i+1) w)) (hhome : ∀ j, T+d ≤ j → ∀ w, X j w = home)
    (hcard : Fintype.card V ≤ n) (htime : (d:ℝ)*Real.log n ≤ (T:ℝ)*Real.log 2) :
    ∃ s : Policy G, 1 / Real.sqrt (2*(n:ℝ)) * Fintype.card W ≤
      (count Finset.univ (fun w => Hits s [] (List.ofFn (fun i : Fin (T+1) => X i.val w))) : ℝ) := by
  classical
  let s := unrestricted G Finset.univ (remainder X T 0) home
  let success : ℝ := (count Finset.univ (fun w => Hits s [] (remainder X T 0 w)) : ℝ) / Fintype.card W
  let q := fun t j => logMean (conditional X t j)
  have hd (b : ℕ) (hb : b ≤ 2*T) : 0 < success ∧
      diagonalSum b (fun t j => q t j - q (t+1) j) ≤ Real.log success := by
    apply bellman_diagonal b (conditional X) (value G X T b) (fun t => key X t (b-t)) success
    · exact conditional_pos X
    · intro w; simp [value]
    · intro w; simp only [value, Nat.zero_le, if_true, prefix_zero, Finset.card_univ]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast le_unrestricted G Finset.univ (remainder X T 0) home (X (b-0) w)
    · intro t ht w; exact cell_bound G X T b t (b-t) hb ht rfl w leg
  have he : 1 ≤ n := (Fintype.card_pos_iff.mpr ⟨home⟩).trans_le hcard
  obtain ⟨_, _, hbound⟩ := exists_good_from_diagonal T d n he hcard htime X (conditional X)
    (fun _ => success) (fun t j w => ⟨conditional_pos X t j w, cond_le_one X t j w⟩) (cond_zero X)
    (fun j hj w z => (hhome j hj w).trans (hhome j hj z).symm) hd
  refine ⟨s,?_⟩
  have hh := (le_div_iff₀ (show 0 < (Fintype.card W : ℝ) by exact_mod_cast Fintype.card_pos)).mp hbound
  simpa [remainder] using hh

end Meyniel.Sampler
