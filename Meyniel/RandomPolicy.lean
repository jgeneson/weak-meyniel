module

public import Meyniel.Sampler
public import Meyniel.Weights
public import Meyniel.RandomTable

/-! # The backward sampler as finite random tapes of legal ordinary policies

At each row a fresh table selects a uniform tagged walk from each nonempty
compatible set. A fixed tape assigns all these choices before the robber starts.
The table is queried only after computing the compatible set from the real cop
vertex and the observed robber prefix.
-/

@[expose] public section

namespace Meyniel.RandomPolicy

open Finset

noncomputable section

variable {V W : Type*}

/-- A set of candidates that is safe to sample uniformly. -/
abbrev Key (W : Type*) := RandomTable.Key W

/-- One sample for every possible nonempty query at a fixed row. -/
abbrev Row (W : Type*) := RandomTable.Row W

def defaultRow (W : Type*) : Row W := fun B => ⟨B.prop.choose, B.prop.choose_spec⟩

/-- An initial guess and one independent response table for each subsequent reveal. -/
def Tape (W : Type*) : ℕ → Type _
  | 0 => W
  | t+1 => Tape W t × Row W

instance tapeFinite [Fintype W] : ∀ t, Fintype (Tape W t)
  | 0 => inferInstanceAs (Fintype W)
  | t+1 => by
    classical
    letI := tapeFinite t
    exact inferInstanceAs (Fintype (Tape W t × Row W))

instance tapeNonempty [Nonempty W] : ∀ t, Nonempty (Tape W t)
  | 0 => inferInstanceAs (Nonempty W)
  | t+1 => by
    letI := tapeNonempty t
    exact inferInstanceAs (Nonempty (Tape W t × Row W))

def initial : ∀ t, Tape W t → W
  | 0, s => s
  | t+1, (s,_) => initial t s

def rowAt : ∀ t, Tape W t → ℕ → Row W
  | 0, _, _ => defaultRow W
  | t+1, (s,row), k => if k=t then row else rowAt t s k

variable [Fintype W] [DecidableEq W] [DecidableEq V]

def pool (X : ℕ→W→V) (t j : ℕ) (h : List V) (cop : V) : Finset W :=
  Finset.univ.filter fun w => Sampler.past X t w = h ∧ X j w = cop

abbrev select (rows : Row W) (B : Finset W) : Option W := RandomTable.select rows B

omit [Fintype W] in
theorem select_mem {q : Row W} {B : Finset W} {w : W} (h : select q B = some w) : w ∈ B := by
  unfold select RandomTable.select at h; split at h
  next hb => exact (Option.some.inj h) ▸ (q ⟨B,hb⟩).property
  next => contradiction

/-- One transition of the exact guessing rule. Permanent failure retains the
physical vertex. The final odd entry also takes its last legal backward step. -/
def advance (X : ℕ→W→V) (b t : ℕ) (h : List V) (row : Row W) (st : V × Option W) : V × Option W :=
  if t ≤ b/2 then
    match st.2 with
    | none => st
    | some _ => match select row (pool X (t+1) (b-t) h st.1) with
      | none => (st.1,none)
      | some z => (if t < b-t then X (b-t-1) z else st.1,some z)
  else st

/-- Computing the physical state requires only the revealed prefix. -/
def state (X : ℕ→W→V) (b : ℕ) (w₀ : W) (rows : ℕ→Row W) : List V → V × Option W
  | [] => (X b w₀, some w₀)
  | r :: h => advance X b h.length (r::h) (rows h.length) (state X b w₀ rows h)

theorem advance_legal (G : SimpleGraph V) (X : ℕ→W→V)
    (legal : ∀i w, Step G (X i w) (X (i+1) w)) (b t) (h) (row) (st) :
    Step G st.1 (advance X b t h row st).1 := by
  unfold advance
  split
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      next z he =>
        split_ifs with hj
        · have hz := (Finset.mem_filter.mp (select_mem he)).2.2
          have hs := legal (b-t-1) z
          have hn : b-t-1+1=b-t := by omega
          rw [hn,hz] at hs
          exact hs.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)
        · exact Or.inl rfl
  · exact Or.inl rfl

/-- Fixing each coin is exactly one legal strategy with a public initial vertex. -/
def policy (G : SimpleGraph V) (X : ℕ→W→V) (legal : ∀i w, Step G (X i w) (X (i+1) w))
    (b k : ℕ) (tape : Tape W k) : Policy G where
  pos := fun h => (state X b (initial k tape) (rowAt k tape) h).1
  legal := fun r h => advance_legal G X legal b h.length (r::h) _ _

private theorem state_rows_congr (X : ℕ→W→V) (b) (w₀) (rows rows' : ℕ→Row W) (h : List V)
    (he : ∀ i < h.length, rows i = rows' i) : state X b w₀ rows h = state X b w₀ rows' h := by
  induction h with
  | nil => rfl
  | cons r h ih =>
    simp only [state,he h.length (by simp),ih (fun i hi => he i (by simp; omega))]

omit [Fintype W] [DecidableEq W] [DecidableEq V] in
@[simp] theorem length_past (X : ℕ→W→V) (t : ℕ) (w : W) : (Sampler.past X t w).length=t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [Sampler.past,ih]

/-- The next independent row cannot affect the cop's state before this reveal. -/
theorem state_before_new_row (X : ℕ→W→V) (b t : ℕ) (s : Tape W t) (row : Row W) (h : List V)
    (hh : h.length ≤ t) :
    state X b (initial (t+1) (s,row)) (rowAt (t+1) (s,row)) h = state X b (initial t s) (rowAt t s) h := by
  apply state_rows_congr
  intro i hi; simp [rowAt,show i ≠ t by omega]

/-- A live guess is always physically at its current target time. -/
theorem live_vertex (X : ℕ→W→V) (b) (w₀) (rows : ℕ→Row W) (h : List V) (z : W)
    (ht : h.length ≤ b/2) (hz : (state X b w₀ rows h).2 = some z) :
    (state X b w₀ rows h).1 = X (b-h.length) z := by
  cases h with
  | nil => simp [state] at hz ⊢; exact congrArg (X b) hz
  | cons r h =>
    have hk : h.length < b/2 := by simpa using ht
    simp only [state, advance, if_pos hk.le] at hz ⊢
    split at hz
    · next he => simp [he] at hz
    · next old he =>
        split at hz
        · contradiction
        next guess hguess =>
          simp only [Option.some.injEq] at hz
          simp only [if_pos (show h.length < b-h.length by omega),hz,List.length_cons]
          congr 1

/-- State after the first t reveals on the independently prescribed walk. -/
def outcome (X : ℕ→W→V) (b t : ℕ) (s : Tape W t) (actual : W) : V × Option W :=
  state X b (initial t s) (rowAt t s) (Sampler.past X t actual)

theorem outcome_succ (X : ℕ→W→V) (b t : ℕ) (s : Tape W t) (row : Row W) (actual : W) :
    outcome X b (t+1) (s,row) actual =
      advance X b t (Sampler.past X (t+1) actual) row (outcome X b t s actual) := by
  change advance X b _ _ _ (state X b _ _ (Sampler.past X t actual)) = _
  rw [length_past, state_before_new_row X b t s row _ (by simp)]
  simp [rowAt,outcome,Sampler.past]

end
end Meyniel.RandomPolicy
