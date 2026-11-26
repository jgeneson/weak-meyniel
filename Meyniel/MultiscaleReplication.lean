module

public import Meyniel.MultiscaleMinimax

/-! Turning uniform counting bounds on replicated inputs into a mixed
strategy with the same guarantee against each individual input. -/

@[expose] public section

namespace Meyniel.Multiscale
open Finset
open scoped Classical
variable {W S : Type*} [Fintype W] [Nonempty W] [Nonempty S]

/-- Only finitely many capture patterns occur on a finite input space.
Rounding down the probabilities times a large common denominator therefore
gives the exact real-valued minimax bound. -/
theorem weighted_of_replicated (hit : S → W → Prop) (p : ℝ) (hp : 0 ≤ p)
    (single : ∀ m : W → ℕ, ∃ s, p * (∑ w, (m w : ℝ)) ≤ ∑ w, if hit s w then (m w : ℝ) else 0)
    (μ : W → ℝ) (hμ : μ ∈ stdSimplex ℝ W) :
    ∃ s, p ≤ ∑ w, if hit s w then μ w else 0 := by
  classical
  let pattern (s : S) := univ.filter (hit s)
  let pool := (univ : Finset (Finset W)).filter (fun F => ∃ s, pattern s=F)
  have mem (s : S) : pattern s ∈ pool := mem_filter.mpr ⟨mem_univ _,s,rfl⟩
  let score (F : Finset W) := ∑ w ∈ F, μ w
  obtain ⟨best,hb,maximal⟩ := pool.exists_max_image score ⟨_,mem (Classical.arbitrary S)⟩
  obtain ⟨s₀,he⟩ := (mem_filter.mp hb).2
  have identity (s : S) : (∑ w, if hit s w then μ w else 0)=score (pattern s) := by
    simp [score,pattern,sum_filter]
  refine ⟨s₀,?_⟩
  rw [identity,he]
  by_contra! hlow
  have hgap : 0 < p-score best := sub_pos.mpr hlow
  obtain ⟨n,hn⟩ := exists_nat_gt (p * Fintype.card W / (p-score best))
  have hn' := (div_lt_iff₀ hgap).mp hn
  let m (w : W) := ⌊(n:ℝ)*μ w⌋₊
  obtain ⟨s,hs⟩ := single m
  have lower : (n:ℝ) ≤ (∑ w, (m w : ℝ)) + Fintype.card W := by
    have h (w : W) : (n:ℝ)*μ w ≤ (m w : ℝ)+1 := (Nat.lt_floor_add_one _).le
    have h' := sum_le_sum (s:=univ) (fun w _ => h w)
    simpa [←mul_sum,hμ.2,sum_add_distrib] using h'
  have upper : (∑ w, if hit s w then (m w : ℝ) else 0) ≤ (n:ℝ)*score best := by
    calc
      _ ≤ ∑ w, (n:ℝ)*(if hit s w then μ w else 0) := by
        apply sum_le_sum
        intro w _
        split_ifs
        · exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (hμ.1 w))
        · simp
      _ = (n:ℝ)*score (pattern s) := by rw [← mul_sum,identity]
      _ ≤ _ := mul_le_mul_of_nonneg_left (maximal _ (mem s)) (Nat.cast_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left lower hp, hs.trans upper]

theorem mixture_of_replicated (hit : S → W → Prop) (K : ℝ)
    (single : ∀ m : W → ℕ, ∃ s, Real.exp (-K) * (∑ w, (m w : ℝ)) ≤
      ∑ w, if hit s w then (m w : ℝ) else 0) :
    ∃ m : Mixture S, ∀ w, Real.exp (-K) ≤ m.success hit w := by
  classical
  apply mixture_of_weighted_response hit (fun _ => K)
  intro μ hμ
  obtain ⟨s,hs⟩ := weighted_of_replicated hit _ (Real.exp_pos _).le single μ hμ
  refine ⟨s,?_⟩
  rw [Real.exp_neg,inv_eq_one_div,div_le_iff₀ (Real.exp_pos _)] at hs
  calc
    _ ≤ _ := hs
    _ = _ := by
      rw [sum_mul]
      apply sum_congr rfl
      intro w _
      split_ifs <;> ring

end Meyniel.Multiscale
