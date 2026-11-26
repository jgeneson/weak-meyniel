module

public import Meyniel.RandomPolicy

/-! # Capture on the terminal diagonal

On an even diagonal the live cop already occupies the robber's current
vertex before its next move. On an odd diagonal the cop gets one last legal
move by the deadline. In particular there is no extra cop turn after time T.
-/

@[expose] public section

namespace Meyniel.RandomCapture

open Sampler

variable {V W : Type*} {G : SimpleGraph V}

private theorem remainder_at (X : ℕ → W → V) (T t : ℕ) (ht : t ≤ T) (w : W) :
    remainder X T t w = X t w :: remainder X T (t+1) w := by
  unfold remainder
  have hlen : T+1-t = (T+1-(t+1))+1 := by omega
  conv_lhs => rw [hlen]
  rw [List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 1
  simp [Fin.val_succ]
  omega

/-- A capture on the suffix, using its actual prior observations, counts
as a capture on the original word. -/
private theorem hits_from_time (s : Policy G) (X : ℕ → W → V) (T t : ℕ) (w : W)
    (ht : t ≤ T) (hit : Hits s (past X t w) (remainder X T t w)) :
    Hits s [] (remainder X T 0 w) := by
  induction t with
  | zero => exact hit
  | succ t ih =>
    apply ih (by omega)
    rw [remainder_at X T t (by omega) w, remainder_at X T (t+1) ht w]
    rw [remainder_at X T (t+1) ht w] at hit
    exact Or.inr (Or.inr hit)

private theorem hits_at_time (s : Policy G) (X : ℕ → W → V) (T t : ℕ) (w : W)
    (ht : t ≤ T) (meet : s.pos (past X t w) = X t w ∨
      (t < T ∧ s.pos (past X (t+1) w) = X t w)) :
    Hits s [] (List.ofFn (fun i : Fin (T+1) => X i.val w)) := by
  suffices full : Hits s [] (remainder X T 0 w) by simpa [remainder] using full
  apply hits_from_time s X T t w ht
  rw [remainder_at X T t ht w]
  by_cases ends : t = T
  · subst t
    have empty : remainder X T (T+1) w = [] := by simp [remainder]
    rw [empty]
    exact meet.elim id (fun h => (Nat.lt_irrefl T h.1).elim)
  · rw [remainder_at X T (t+1) (by omega) w]
    exact meet.elim Or.inl (fun h => Or.inr (Or.inl h.2))

end Meyniel.RandomCapture

namespace Meyniel.RandomCapture

open RandomPolicy Sampler

variable {V W : Type*} [Fintype W] [DecidableEq W] [DecidableEq V]

/-- A surviving final resampling step either certifies an existing
coincidence (even b), or puts the cop on the robber (odd b). -/
private theorem terminal_advance (X : ℕ → W → V) (b t : ℕ) (ht : t = b/2)
    (w : W) (row : Row W) (st : V × Option W)
    (alive : (advance X b t (past X (t+1) w) row st).2.isSome) :
    (b = 2*t ∧ st.1 = X t w) ∨
    (b = 2*t+1 ∧ (advance X b t (past X (t+1) w) row st).1 = X t w) := by
  have ha : t ≤ b/2 := ht.le
  rcases st with ⟨v, prev⟩
  cases prev with
  | none => simp [advance, ha] at alive
  | some old =>
    cases chosen : select row (pool X (t+1) (b-t) (past X (t+1) w) v) with
    | none => simp [advance, ha, chosen] at alive
    | some z =>
      have mem := select_mem chosen
      have both := (Finset.mem_filter.mp mem).2
      have hp : past X (t+1) z = past X (t+1) w := both.1
      have hx : X (b-t) z = v := both.2
      have hz : X t z = X t w := (List.cons.inj hp).1
      by_cases heven : b = 2*t
      · have jt : b-t = t := by omega
        rw [jt] at hx
        exact Or.inl ⟨heven, hx.symm.trans hz⟩
      · have hodd : b = 2*t+1 := by omega
        have hmove : t < b-t := by omega
        have jprev : b-t-1 = t := by omega
        exact Or.inr ⟨hodd, by simpa [advance,ha,chosen,hmove,jprev] using hz⟩

/-- A live terminal match on the diagonal is genuine capture by round T.
This holds on each true walk and for each fixed seed. -/
theorem terminal_seed_hits (G : SimpleGraph V) (X : ℕ → W → V)
    (legal : ∀ i w, Step G (X i w) (X (i+1) w))
    (T b : ℕ) (hb : b ≤ 2*T) (seed : Tape W (b/2+1)) (actual : W)
    (live : (outcome X b (b/2+1) seed actual).2.isSome) :
    Hits (policy G X legal b (b/2+1) seed) [] (List.ofFn (fun i : Fin (T+1) => X i.val actual)) := by
  let t := b/2
  let w₀ := initial (t+1) seed
  let rows := rowAt (t+1) seed
  let st := state X b w₀ rows (past X t actual)
  have hstate : state X b w₀ rows (past X (t+1) actual) =
      advance X b t (past X (t+1) actual) (rows t) st := by
    simp [state,st,past,length_past]
  change (state X b w₀ rows (past X (t+1) actual)).2.isSome at live
  rw [hstate] at live
  obtain ⟨he,hm⟩ | ⟨ho,hm⟩ := terminal_advance X b t rfl actual (rows t) st live
  · apply hits_at_time _ X T t actual (by dsimp [t]; omega)
    exact Or.inl hm
  · apply hits_at_time _ X T t actual (by dsimp [t]; omega)
    refine Or.inr ⟨by omega, ?_⟩
    change (state X b w₀ rows (past X (t+1) actual)).1 = _
    rw [hstate]
    exact hm

end Meyniel.RandomCapture
