import Mathlib

/-! Finite minimax for the cost on each individual robber walk. -/

namespace Meyniel.Multiscale

open Finset

variable {W S : Type*} [Fintype W] [Fintype S]

private def payoff (A : W → S → ℝ) (p : W → ℝ) (q : S → ℝ) : ℝ :=
  ∑ w, p w * ∑ s, q s * A w s

private theorem payoff_left (A : W → S → ℝ) (p p' : W → ℝ) (q : S → ℝ) (a b : ℝ) :
    payoff A (a • p + b • p') q = a * payoff A p q + b * payoff A p' q := by
  simp only [payoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_sum,mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro w _
  ring

private theorem payoff_right (A : W → S → ℝ) (p : W → ℝ) (q q' : S → ℝ) (a b : ℝ) :
    payoff A p (a • q + b • q') = a * payoff A p q + b * payoff A p q' := by
  have h (w : W) : (∑ s, (a * q s + b * q' s) * A w s) =
      a * (∑ s, q s * A w s) + b * (∑ s, q' s * A w s) := by
    rw [mul_sum,mul_sum,← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  simp only [payoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h]
  rw [mul_sum,mul_sum,← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

variable [Nonempty W] [Nonempty S]

/-- A pure winning response in expectation to every input law yields one finite
mixture that attains the threshold on every input. -/
theorem finite_minimax (A : W → S → ℝ) (c : ℝ)
    (h : ∀ p ∈ stdSimplex ℝ W, ∃ s, c ≤ ∑ w, p w * A w s) :
    ∃ q ∈ stdSimplex ℝ S, ∀ w, c ≤ ∑ s, q s * A w s := by
  classical
  have cx (q : S → ℝ) : Continuous (fun p => payoff A p q) := by unfold payoff; fun_prop
  have cy (p : W → ℝ) : Continuous (payoff A p) := by unfold payoff; fun_prop
  have vx (q : S → ℝ) : ConvexOn ℝ (stdSimplex ℝ W) (fun p => payoff A p q) := by
    refine ⟨convex_stdSimplex .., ?_⟩
    intro p _ p' _ a b _ _ _
    exact (payoff_left A p p' q a b).le
  have vy (p : W → ℝ) : ConcaveOn ℝ (stdSimplex ℝ S) (payoff A p) := by
    refine ⟨convex_stdSimplex .., ?_⟩
    intro q _ q' _ a b _ _ _
    exact (payoff_right A p q q' a b).ge
  obtain ⟨p, hp, q, hq, saddle⟩ := Sion.exists_isSaddlePointOn
    (f := payoff A) (X := stdSimplex ℝ W) (Y := stdSimplex ℝ S)
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary W)⟩ (convex_stdSimplex ..) (isCompact_stdSimplex ..)
    (fun q _ => (cx q).continuousOn.lowerSemicontinuousOn) (fun q _ => (vx q).quasiconvexOn)
    (convex_stdSimplex ..) ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary S)⟩ (isCompact_stdSimplex ..)
    (fun p _ => (cy p).continuousOn.upperSemicontinuousOn) (fun p _ => (vy p).quasiconcaveOn)
  obtain ⟨s, hs⟩ := h p hp
  refine ⟨q,hq,fun w => hs.trans ?_⟩
  simpa [payoff,Pi.single_apply] using
    saddle _ (single_mem_stdSimplex ℝ w) _ (single_mem_stdSimplex ℝ s)

/-- A finite list of deterministic strategies and probabilities that sum to one.
The underlying all-history strategy type need not itself be finite. -/
structure Mixture (S : Type*) where
  size : ℕ
  strategy : Fin size → S
  prob : Fin size → ℝ
  law : prob ∈ stdSimplex ℝ (Fin size)

noncomputable def Mixture.success {S W : Type*} (m : Mixture S) (hit : S → W → Prop) (w : W) : ℝ := by
  classical exact ∑ i, m.prob i * (if hit (m.strategy i) w then 1 else 0)

/-- The paper's weighted minimax step. Its rows may be ordinary legal policies
on arbitrarily long histories. Their capture patterns on W form a finite type. -/
theorem mixture_of_weighted_response {W S : Type*} [Fintype W] [Nonempty W] [Nonempty S]
    (hit : S → W → Prop) (K : W → ℝ)
    (response : ∀ μ ∈ stdSimplex ℝ W, ∃ s : S,
      1 ≤ ∑ w, μ w * (by classical exact if hit s w then Real.exp (K w) else 0)) :
    ∃ m : Mixture S, ∀ w, Real.exp (-K w) ≤ m.success hit w := by
  classical
  let patterns := {u : Finset W // ∃ s : S, u = univ.filter (hit s)}
  letI : Fintype patterns := Fintype.ofFinite patterns
  letI : Nonempty patterns := ⟨⟨_,Classical.arbitrary S,rfl⟩⟩
  let f : patterns → S := fun a => Classical.choose a.property
  have hh (a : patterns) (w : W) : w ∈ a.val ↔ hit (f a) w := by
    have he := Classical.choose_spec a.property
    rw [he]
    simp [f]
  let mat := fun (w : W) (a : patterns) => if w ∈ a.val then Real.exp (K w) else 0
  have h (μ : W → ℝ) (hμ : μ ∈ stdSimplex ℝ W) : ∃ a : patterns, 1 ≤ ∑ w, μ w * mat w a := by
    obtain ⟨s,hs⟩ := response μ hμ
    exact ⟨⟨_,s,rfl⟩,by simpa [mat] using hs⟩
  obtain ⟨q,hq,hcover⟩ := finite_minimax mat 1 h
  let e := (Fintype.equivFin patterns).symm
  let m : Mixture S := ⟨_,fun i => f (e i),fun i => q (e i),
    ⟨fun i => hq.1 (e i), (Equiv.sum_comp e q).trans hq.2⟩⟩
  refine ⟨m,fun w => ?_⟩
  have he : (∑ a, q a * mat w a) = m.success hit w * Real.exp (K w) := by
    unfold Mixture.success
    dsimp only [m]
    rw [Equiv.sum_comp e (fun a => q a * (if hit (f a) w then 1 else 0)),Finset.sum_mul]
    apply sum_congr rfl
    intro a _
    simp only [mat,hh]
    split_ifs <;> ring
  rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos _), ← he]
  exact hcover w

end Meyniel.Multiscale
