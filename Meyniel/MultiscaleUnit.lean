module

public import Meyniel.ForwardPolicy
public import Meyniel.Extension
public import Meyniel.MultiscaleWindow
public import Meyniel.MultiscaleBands

/-! The unit-time base of the multiscale induction, with the different
support sizes at different columns kept in the bound. -/

@[expose] public section

namespace Meyniel.Multiscale
open Finset Interception
noncomputable section
variable {W V : Type*} [Fintype W] [Nonempty W] [Fintype V] [DecidableEq V]

theorem unit_tagged {G : SimpleGraph V} (X : ℕ → W → V) (T : ℕ)
    (leg : ∀ t w, Step G (X t w) (X (t+1) w))
    (cost : ℝ) (C : ℕ → ℝ)
    (support : ∀ j ≤ 2*T, Real.log ((univ.image (X j)).card) ≤ C j)
    (budget : (∑ j ∈ range (2*T+1), C j) ≤ (2*(T:ℝ)+1)*cost) :
    ∃ s : Policy G, (∃ b ≤ 2*T, ∃ w, s.pos [] = X b w) ∧
      Real.exp (-cost) * Fintype.card W ≤
        (Sampler.count univ (fun w => Hits s [] (Sampler.remainder X T 0 w)) : ℝ) := by
  let history := Sampler.past X
  let p t j := ForwardWeights.conditional (history t) (X j)
  let q t j := logMean (p t j)
  let live b := ForwardWeights.terminalLive history X b
  have diag b : 0 < live b ∧ diagonalSum b (fun t j => q t j - q (t+1) j) ≤ Real.log (live b) :=
    ForwardWeights.forward_diagonal history X b (fun _ _ => rfl)
  have start j (hj : j ≤ 2*T) : -(C j) ≤ q 0 j := by
    dsimp [q,p]
    rw [ForwardWeights.conditional_initial _ (fun _ _ => rfl)]
    exact (neg_le_neg (support j hj)).trans (logMean_frequency_ge _)
  have last t j : q t j ≤ 0 := logMean_nonpos _ (ForwardWeights.conditional_bound _ _)
  have hcols : -(∑ j ∈ range (2*T+1), C j) ≤
      ∑ b ∈ range (2*T+1), diagonalSum b (fun t j => q t j-q (t+1) j) := by
    rw [sum_diagonals_eq_sum_columns]
    simp only [sum_range_sub']
    rw [← sum_neg_distrib]
    apply sum_le_sum
    intro j hj
    linarith [start j (by simpa using hj),last (min j (2*T-j)+1) j]
  have good : ∃ b ≤ 2*T, Real.exp (-cost) ≤ live b := by
    by_contra! hf
    have hsum := hcols.trans (sum_le_sum (s:=range (2*T+1)) (fun b _ => (diag b).2))
    have hlt := sum_lt_sum_of_nonempty (s:=range (2*T+1))
      (show (range (2*T+1)).Nonempty from ⟨0,by simp⟩)
      (fun b hb => (Real.log_lt_iff_lt_exp (diag b).1).mpr (hf b (by simpa using hb)))
    rw [sum_const,nsmul_eq_mul,card_range] at hlt
    push_cast at hlt
    nlinarith
  obtain ⟨b,hb,hgain⟩ := good
  obtain ⟨s,w,hs,hm⟩ := ForwardPolicy.exists_anchored_policy_ge_live G X T b hb leg
  exact ⟨s,⟨b,hb,w,hs⟩,(mul_le_mul_of_nonneg_right hgain (Nat.cast_nonneg _)).trans hm⟩

/-- The last r columns before reaching the common home cost at most log N
each. The bound also covers r>T, when there are fewer than r such columns. -/
theorem unit_column_budget (T r : ℕ) (H : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) :
    (∑ j ∈ range (2*T+1), if j<T then H j else if j<T+r then L else 0)
       ≤ (∑ j ∈ range T, H j) + r*L := by
  rw [show 2*T+1=T+(T+1) by omega,sum_range_add]
  have hpre : (∑ j ∈ range T, if j<T then H j else if j<T+r then L else 0) =
      ∑ j ∈ range T, H j := sum_congr rfl (fun j hj => if_pos (mem_range.mp hj))
  rw [hpre]
  apply add_le_add_right
  have hrepl : (∑ j ∈ range (T+1), if T+j<T then H (T+j) else if T+j<T+r then L else 0) =
      ∑ j ∈ range (T+1), if j<r then L else 0 := by simp
  rw [hrepl, ← sum_filter]
  have hcard : ((range (T+1)).filter (fun j => j<r)).card ≤ r :=
    (card_le_card (show (range (T+1)).filter (fun j => j<r) ⊆ range r from
      fun _ hj => mem_range.mpr (mem_filter.mp hj).2)).trans_eq (card_range r)
  simpa using mul_le_mul_of_nonneg_right (show (((range (T+1)).filter (fun j => j<r)).card : ℝ) ≤ r by exact_mod_cast hcard) hL

end
end Meyniel.Multiscale
