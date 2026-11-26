module

public import Meyniel.Cover

/-! # Choosing the time horizon and the number of cops -/

@[expose] public section

namespace Meyniel
open scoped Classical

noncomputable def horizon (N D : ℕ) : ℕ := ⌈(D : ℝ) * Real.log N / Real.log 2⌉₊
noncomputable def diamThreshold (N : ℕ) : ℕ := ⌈(N : ℝ) ^ (1/4 : ℝ) / Real.log (2*N)⌉₊
noncomputable def budget (N T : ℕ) : ℕ :=
  ⌊Real.sqrt (2*N) * ((T+1 : ℕ) : ℝ) * Real.log N⌋₊ + 1

theorem horizon_large (N D : ℕ) :
    D * Real.log N ≤ (horizon N D : ℝ) * Real.log 2 :=
  (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp (Nat.le_ceil _)

theorem power_decay {x p : ℝ} (hx : 0 < x) (hp : p ≤ 1) {m : ℕ}
    (hm : Real.log x < (m : ℝ) * p) : x * (1-p)^m < 1 := by
  have he : 1-p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  calc
    x * (1-p)^m ≤ x * (Real.exp (-p))^m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) he _) hx.le
    _ = x / Real.exp ((m:ℝ)*p) := by
      rw [← Real.exp_nat_mul, mul_neg, Real.exp_neg, div_eq_mul_inv]
    _ < 1 := (div_lt_one (Real.exp_pos _)).mpr ((Real.log_lt_iff_lt_exp hx).mp hm)

/-- The one-cop estimate on arbitrary residual walk families. All seed choices have
already been fixed when the policy in the conclusion is selected. -/
def WalkFraction {V : Type*} [Fintype V] (G : SimpleGraph V) (T : ℕ) (p : ℝ) : Prop :=
  ∀ R ⊆ walks G T, R.Nonempty → ∃ s : Policy G,
    p * R.card ≤ (R.filter (fun w => Hits s [] (List.ofFn w))).card

theorem winsWith_budget {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    {N T : ℕ} (hN : 1 ≤ N) (hsize : Fintype.card V ≤ N)
    (hf : WalkFraction G T (1 / Real.sqrt (2*N))) : WinsWith G (budget N T) := by
  classical
  let p : ℝ := 1 / Real.sqrt (2*N)
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hs : 1 ≤ Real.sqrt (2*N) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hs0 : 0 < Real.sqrt (2*N) := by linarith
  have hp : p ≤ 1 := (div_le_one hs0).mpr hs
  have hb : Real.sqrt (2*N) * ((T+1 : ℕ) : ℝ) * Real.log N < (budget N T : ℝ) := by
    unfold budget
    push_cast
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one
      (Real.sqrt (2*N) * ((T : ℝ)+1) * Real.log N)
  have hdec : (N : ℝ)^(T+1) * (1-p)^(budget N T) < 1 := by
    apply power_decay (pow_pos (by linarith) _) hp
    rw [Real.log_pow]
    dsimp [p]
    rw [mul_one_div, lt_div_iff₀ hs0]
    nlinarith [hb]
  have hcard : ((walks G T).card : ℝ) ≤ (N:ℝ)^(T+1) := by
    exact_mod_cast (walks_card_le G T).trans (Nat.pow_le_pow_left hsize _)
  have hsmall := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcard
    (pow_nonneg (sub_nonneg.mpr hp) (budget N T))) hdec
  obtain ⟨L, hlen, hc⟩ := greedy_cover (fun (s : Policy G) w => Hits s [] (List.ofFn w))
    p hp (walks G T) hf (budget N T) hsmall
  let team (i : Fin (budget N T)) : Policy G :=
    if hi : i.val < L.length then L.get ⟨i.val,hi⟩ else Policy.stay G (Classical.arbitrary V)
  apply winsWith_of_word_cover team
  intro w hw
  obtain ⟨s, hmem, hit⟩ := hc w hw
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hmem
  refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hlen⟩, ?_⟩
  simpa [team, i.isLt] using hit

end Meyniel
