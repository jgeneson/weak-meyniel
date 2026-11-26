module

public import Meyniel.RandomPolicy
public import Meyniel.RandomTable

/-! Exact law of the seeded backward policy under the uniform tape distribution. -/

@[expose] public section

namespace Meyniel.RandomLaw

open Finset RandomPolicy
open RandomTable (avg)

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W] [DecidableEq V] [Nonempty W]

private theorem avg_div {A : Type*} [Fintype A] (f : A→ℝ) (c : ℝ) :
    avg (fun a => f a / c) = avg f / c := by
  simp only [div_eq_mul_inv, RandomTable.avg_mul_const]

omit [Nonempty W] in
private theorem live_choice (X : ℕ→W→V) (b t : ℕ) (ht : t ≤ b/2) (h : List V) (row : Row W)
    (st : V × Option W) : (advance X b t h row st).2 =
      match st.2 with | none => none | some _ => select row (pool X (t+1) (b-t) h st.1) := by
  rcases st with ⟨x, _ | g⟩
  · simp [advance,ht]
  · simp only [advance,if_pos ht]; split <;> rename_i he <;> exact he.symm

omit [Nonempty W] in
private theorem one_row (X : ℕ→W→V) (b t : ℕ) (ht : t ≤ b/2) (a z : W)
    (st : V × Option W) (phys : ∀ g, st.2 = some g → st.1 = X (b-t) g) :
    avg (fun row : Row W => if (advance X b t (Sampler.past X (t+1) a) row st).2=some z
      then (1:ℝ) else 0) =
      if Sampler.past X (t+1) z = Sampler.past X (t+1) a then
        (∑ g ∈ (Finset.univ.filter fun g => X (b-t) g = X (b-t) z),
          if st.2=some g then (1:ℝ) else 0) /
          (ForwardWeights.joint (Sampler.past X (t+1)) (X (b-t)) z).card else 0 := by
  classical
  simp only [live_choice X b t ht]
  cases hg : st.2 with
  | none => simp [RandomTable.avg_const]
  | some g =>
    rw [phys g hg]
    let B := pool X (t+1) (b-t) (Sampler.past X (t+1) a) (X (b-t) g)
    change avg (fun row : RandomTable.Row W => if RandomTable.select row B = some z then (1:ℝ) else 0) = _
    rw [RandomTable.avg_select]
    have hmem : z ∈ B ↔ Sampler.past X (t+1) z = Sampler.past X (t+1) a ∧
      X (b-t) z = X (b-t) g := by simp [B,pool]
    by_cases hpre : Sampler.past X (t+1) z = Sampler.past X (t+1) a
    · simp only [if_pos hpre, Option.some.injEq]
      by_cases hx : X (b-t) g = X (b-t) z
      · have he : B = ForwardWeights.joint (Sampler.past X (t+1)) (X (b-t)) z := by
          ext u; simp [B,pool,ForwardWeights.joint,Interception.fiber,hpre,hx]
        simp [hpre,hx,he,ForwardWeights.joint,Interception.fiber]
      · simp [hmem,hpre,hx,Ne.symm hx]
    · simp [hmem,hpre]

omit [Nonempty W] in
private theorem avg_tape_succ (t : ℕ) (f : Tape W (t+1) → ℝ) :
    avg f = avg (fun s : Tape W t => avg (fun row : Row W => f (s,row))) := by
  classical
  let g : Tape W t × Row W → ℝ := f
  have h := RandomTable.avg_prod g
  apply Eq.trans _ h
  exact congrArg (fun F : Fintype (Tape W (t+1)) => @avg _ F f) (Subsingleton.elim _ _)

/-- The probability that a fixed tag is the currently live guess, conditioned on
observing the prescribed walk's real prefix, using an independent uniform tape. -/
def liveProbability (X : ℕ→W→V) (b t : ℕ) (a z : W) : ℝ :=
  avg (fun tape : Tape W t => if (outcome X b t tape a).2 = some z then 1 else 0)

/-- The paper's forward guess mass is the exact fraction of pure tapes whose
guess equals z at the indicated prefix. Off-prefix guesses have probability zero. -/
theorem liveProbability_eq (X : ℕ→W→V) (b t : ℕ) (ht : t ≤ b/2+1) (a z : W) :
    liveProbability X b t a z = if Sampler.past X t z = Sampler.past X t a then
      ForwardWeights.guessMass (Sampler.past X) X b t z else 0 := by
  classical
  induction t generalizing a z with
  | zero =>
    simp only [liveProbability, outcome, Sampler.past, initial, state, ite_true,
      ForwardWeights.guessMass]
    change avg (fun w : W => if some w = some z then (1 : ℝ) else 0) = _
    simp [RandomTable.avg]
  | succ t ih =>
    have hk : t ≤ b/2 := by omega
    let B := Finset.univ.filter fun g => X (b-t) g = X (b-t) z
    let J := ForwardWeights.joint (Sampler.past X (t+1)) (X (b-t)) z
    let pre := Sampler.past X (t+1) z = Sampler.past X (t+1) a
    let score := fun (s : Tape W t) (g : W) => if (outcome X b t s a).2=some g then (1:ℝ) else 0
    have he : liveProbability X b (t+1) a z =
        avg (fun s : Tape W t => if pre then (∑ g ∈ B, score s g) / J.card else 0) := by
      unfold liveProbability
      rw [avg_tape_succ]
      apply congrArg avg; funext s
      simp only [outcome_succ]
      apply one_row X b t hk a z
      intro g hg
      simpa [outcome] using live_vertex X b (initial t s) (rowAt t s) (Sampler.past X t a) g
        (by simp [hk]) hg
    rw [he]
    by_cases hp : pre
    · have hparent : Sampler.past X t z = Sampler.past X t a := (List.cons.inj hp).2
      have hp' : Sampler.past X (t+1) z = Sampler.past X (t+1) a := hp
      simp only [if_pos hp,if_pos hp',ForwardWeights.guessMass,ForwardWeights.splitMass]
      rw [avg_div, RandomTable.avg_sum_finset]
      apply congrArg (fun q : ℝ => q/J.card)
      change (∑ g ∈ B, liveProbability X b t a g) = _
      have hs : (∑ g ∈ B, liveProbability X b t a g) = ∑ g ∈ B,
          if Sampler.past X t g = Sampler.past X t a then ForwardWeights.guessMass (Sampler.past X) X b t g else 0 :=
        Finset.sum_congr rfl (fun g _ => ih (by omega) a g)
      rw [hs, ← Finset.sum_filter]
      congr 1
      ext u; simp [B,ForwardWeights.joint,Interception.fiber,hparent,and_comm]
    · have hp' : Sampler.past X (t+1) z ≠ Sampler.past X (t+1) a := hp
      simp [hp,hp']

/-- Under a fixed prescribed walk, total terminal-live mass in the manuscript
is exactly the probability that the presampled table still has a guess. -/
theorem terminal_probability (X : ℕ→W→V) (b : ℕ) (a : W) :
    avg (fun tape : Tape W (b/2+1) => if (outcome X b (b/2+1) tape a).2.isSome then (1:ℝ) else 0) =
      ∑ z ∈ ForwardWeights.block (Sampler.past X (b/2+1)) a,
        ForwardWeights.guessMass (Sampler.past X) X b (b/2+1) z := by
  classical
  let k := b/2+1
  have hsum (s : Tape W k) : (if (outcome X b k s a).2.isSome then (1:ℝ) else 0) =
      ∑ z : W, if (outcome X b k s a).2=some z then 1 else 0 := by
    cases h : (outcome X b k s a).2 <;> simp
  change avg (fun s : Tape W k => if (outcome X b k s a).2.isSome then (1:ℝ) else 0) = _
  simp_rw [hsum]
  rw [RandomTable.avg_sum]
  change (∑ z : W, liveProbability X b k a z) = _
  simp_rw [liveProbability_eq X b k (le_refl _) a]
  rw [← Finset.sum_filter]; rfl

end
end Meyniel.RandomLaw
