module

public import Meyniel.TwoThirds

/-! # Proofs of the uniform two-thirds bound and its soft Meyniel corollary -/

public section

namespace PalomarMeyniel

open Filter
open scoped Topology

/-- The multiscale theorem transferred to the Formal Conjectures game. -/
theorem twoThirds :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ (∀ n, 0 < e n) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
        (MeynielConjecture.copNumber G : ℝ) ≤
          (Fintype.card V : ℝ) ^ ((2 / 3 : ℝ) + e (Fintype.card V)) :=
  MeynielConjecture.copNumber_two_thirds_little_o

/-- Take the saving `1/4`. The coefficient covers the finitely many graph orders before the
exponent error stays below `1/12`. -/
theorem soft :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      (MeynielConjecture.copNumber G : ℝ) ≤
        C * (Fintype.card V : ℝ) ^ ((1 : ℝ) - ε) := by
  obtain ⟨e, he, _, hbound⟩ := twoThirds
  obtain ⟨N, hN⟩ := eventually_atTop.mp (he.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 12))
  let b (k : ℕ) : ℝ := (k : ℝ) ^ ((2 / 3 : ℝ) + e k)
  have hb (k : ℕ) : 0 ≤ b k := Real.rpow_nonneg (Nat.cast_nonneg k) _
  let C : ℝ := 1 + ∑ k ∈ Finset.range N, b k
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hb k)
  refine ⟨1 / 4, C, by norm_num, lt_of_lt_of_le zero_lt_one hC, ?_⟩
  intro V _ G hG
  letI : Nonempty V := hG.nonempty
  have hn : 1 ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card V))
  have hpow : 1 ≤ (Fintype.card V : ℝ) ^ ((1 : ℝ) - 1 / 4) :=
    Real.one_le_rpow hn (by norm_num)
  refine (hbound V G hG).trans ?_
  by_cases hlarge : N ≤ Fintype.card V
  · have hsmallerr := hN _ hlarge
    exact (Real.rpow_le_rpow_of_exponent_le hn (by linarith)).trans
      (le_mul_of_one_le_left (le_trans zero_le_one hpow) hC)
  · have hmem : Fintype.card V ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_of_not_ge hlarge)
    have hsum : b (Fintype.card V) ≤ ∑ k ∈ Finset.range N, b k :=
      Finset.single_le_sum (fun k _ => hb k) hmem
    have hle : b (Fintype.card V) ≤ C := hsum.trans (le_add_of_nonneg_left zero_le_one)
    exact hle.trans (le_mul_of_one_le_right (le_trans zero_le_one hC) hpow)

end PalomarMeyniel
