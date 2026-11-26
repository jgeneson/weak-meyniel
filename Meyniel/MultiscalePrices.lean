module

public import Meyniel.MultiscaleGrowth
public import Meyniel.Interception

/-! Summing the charges from all lower clocks. Time can be taken modulo the
length of a window for this calculation: on the actual clock each terminal
lies in the window, and a fixed child label translates its parent's endpoint.
Translation preserves the sum over a whole window of endpoint times. -/

@[expose] public section

namespace Meyniel.Multiscale
open Finset Interception
noncomputable section

theorem mean_add' {A : Type*} (s : Finset A) (f g : A → ℝ) :
    mean s (fun a => f a + g a) = mean s f + mean s g := by simp [mean,sum_add_distrib,add_div]

theorem mean_const' {A : Type*} {s : Finset A} (hs : s.Nonempty) (c : ℝ) :
    mean s (fun _ => c) = c := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  simp [mean,hc]

theorem mean_mono' {A : Type*} (s : Finset A) {f g : A → ℝ} (h : ∀ a ∈ s, f a ≤ g a) :
    mean s f ≤ mean s g := div_le_div_of_nonneg_right (sum_le_sum h) (Nat.cast_nonneg _)

theorem sum_mean {A B : Type*} (s : Finset A) (t : Finset B) (f : A → B → ℝ) :
    (∑ a ∈ s, mean t (f a)) = mean t (fun b => ∑ a ∈ s, f a b) := by
  simp only [mean,←sum_div]; rw [sum_comm]

/-- m is the number of levels strictly below the parent. For fixed parent,
radius and label, lag is a translation independent of the parent's endpoint. -/
def nestedPrice {E : Type*} [AddGroup E] (radii : ℕ → Finset ℕ)
    (labels : ℕ → ℕ → ℕ → Finset ℕ) (lag : ℕ → ℕ → ℕ → ℕ → E)
    (cost : ℕ → ℕ → E → ℝ) : ℕ → ℕ → E → ℝ
  | 0,_,_ => 0
  | m+1,parent,t => mean (radii (m+1)) (fun r =>
      mean (labels (m+1) parent r) (fun b =>
        let y := t - lag (m+1) parent r b
        cost (m+1) r y + nestedPrice radii labels lag cost m r y))

theorem nestedPrice_nonneg {E : Type*} [AddGroup E] (rs : ℕ → Finset ℕ)
    (ls : ℕ → ℕ → ℕ → Finset ℕ) (lag : ℕ → ℕ → ℕ → ℕ → E) (c : ℕ → ℕ → E → ℝ)
    (hc : ∀ i r y, 0 ≤ c i r y) (m parent : ℕ) (t : E) : 0 ≤ nestedPrice rs ls lag c m parent t := by
  induction m generalizing parent t with
  | zero => rfl
  | succ m ih =>
    exact div_nonneg (sum_nonneg (fun r _ => div_nonneg (sum_nonneg (fun b _ =>
      add_nonneg (hc ..) (ih ..))) (Nat.cast_nonneg _))) (Nat.cast_nonneg _)

theorem sum_nestedPrice {E : Type*} [AddGroup E] [Fintype E]
    (rs : ℕ → Finset ℕ) (ls : ℕ → ℕ → ℕ → Finset ℕ) (lag : ℕ → ℕ → ℕ → ℕ → E)
    (c : ℕ → ℕ → E → ℝ) (m : ℕ) (hr : ∀ i, 1 ≤ i → i ≤ m → (rs i).Nonempty)
    (hl : ∀ i, 1 ≤ i → i ≤ m → ∀ parent r, r ∈ rs i → (ls i parent r).Nonempty) (parent : ℕ) :
    (∑ t : E, nestedPrice rs ls lag c m parent t) =
      ∑ j ∈ range m, mean (rs (j+1)) (fun r => ∑ t : E, c (j+1) r t) := by
  induction m generalizing parent with
  | zero => simp [nestedPrice]
  | succ m ih =>
    simp only [nestedPrice,sum_mean,sum_range_succ]
    let prev := ∑ j ∈ range m, mean (rs (j+1)) (fun r => ∑ t : E, c (j+1) r t)
    have he r (hmem : r ∈ rs (m+1)) :
        mean (ls (m+1) parent r) (fun b => ∑ t : E, (c (m+1) r (t-lag (m+1) parent r b) +
          nestedPrice rs ls lag c m r (t-lag (m+1) parent r b))) =
        (∑ t : E, c (m+1) r t) + prev := by
      have hfun b : (∑ t : E, (c (m+1) r (t-lag (m+1) parent r b) +
          nestedPrice rs ls lag c m r (t-lag (m+1) parent r b))) = (∑ t : E, c (m+1) r t)+prev := by
        calc
          _ = ∑ t : E, (c (m+1) r t + nestedPrice rs ls lag c m r t) :=
            (Equiv.subRight _).sum_comp _
          _ = _ := by rw [sum_add_distrib, ih (fun i hi hj => hr i hi (by omega))
            (fun i hi hj => hl i hi (by omega)) r]
      simp_rw [hfun]
      exact mean_const' (hl _ (by omega) (by omega) _ r hmem) _
    have hreplace : mean (rs (m+1)) (fun r => mean (ls (m+1) parent r) (fun b =>
        ∑ t : E, (c (m+1) r (t-lag (m+1) parent r b) + nestedPrice rs ls lag c m r (t-lag (m+1) parent r b)))) =
        mean (rs (m+1)) (fun r => (∑ t : E, c (m+1) r t)+prev) := by
      unfold mean
      congr 1
      exact sum_congr rfl he
    rw [hreplace,mean_add',mean_const' (hr _ (by omega) (by omega))]
    exact add_comm ..

/-- One fixed radius's loss for a terminal whose absolute time is t. The
baseline saving is charged separately and each bad level refunds one saving. -/
def scaleCharge {V E : Type*} [Fintype V] (G : SimpleGraph V) (vertex : E → V)
    (δ : ℝ) (N i r : ℕ) (t : E) : ℝ := by
  classical exact growth G (vertex t) (dilation δ) r +
    (if i ∈ badLevels G (vertex t) δ N then gain δ * Real.log N / 2 else 0)


theorem avg_charge_bound {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]
    (G : SimpleGraph V) (vertex : E → V) (δ : ℝ) (N m : ℕ) (Rmin cap : ℝ)
    (hr : 0 < Rmin) (hG : Fintype.card V ≤ N)
    (count : ∀ i ≤ m, 1 ≤ i → Rmin ≤ ((radii δ N i).card : ℝ))
    (hbad : ∀ t, ((badLevels G (vertex t) δ N).card : ℝ) ≤ cap)
    (hg : 0 ≤ gain δ * Real.log N / 2) :
    (∑ j ∈ range m, mean (radii δ N (j+1)) (fun r => ∑ t : E, scaleCharge G vertex δ N (j+1) r t)) ≤
      (Fintype.card E : ℝ) * ((m:ℝ) * (Real.log N / Rmin) + cap * (gain δ * Real.log N / 2)) := by
  classical
  let g := gain δ * Real.log N / 2
  have hn0 : 0 ≤ Real.log N := (logBall_bound G (vertex (Classical.arbitrary E)) 0 hG).1.trans
    (logBall_bound G (vertex (Classical.arbitrary E)) 0 hG).2
  have per (t : E) : (∑ j ∈ range m, mean (radii δ N (j+1)) (fun r => scaleCharge G vertex δ N (j+1) r t)) ≤
        (m:ℝ) * (Real.log N / Rmin) + cap * g := by
    let bad := badLevels G (vertex t) δ N
    have step (j : ℕ) (hj : j ∈ range m) :
        mean (radii δ N (j+1)) (fun r => scaleCharge G vertex δ N (j+1) r t) ≤
          Real.log N / Rmin + (if j+1 ∈ bad then g else 0) := by
      have hh := count (j+1) (mem_range.mp hj) (by omega)
      have ne : (radii δ N (j+1)).Nonempty := card_pos.mp (by exact_mod_cast hr.trans_le hh)
      unfold scaleCharge
      rw [mean_add',mean_const' ne]
      apply add_le_add_left
      calc
        _ ≤ Real.log N / (radii δ N (j+1)).card := div_le_div_of_nonneg_right
          (radius_growth_sum G (vertex t) hG δ (j+1)) (Nat.cast_nonneg _)
        _ ≤ _ := div_le_div_of_nonneg_left hn0 hr hh
    have bd : ((range m).filter (fun j => j+1 ∈ bad)).card ≤ bad.card :=
      card_le_card_of_injOn (fun i => i+1) (fun _ hi => (mem_filter.mp hi).2)
        (fun i _ j _ h => Nat.add_right_cancel h)
    have sums := sum_le_sum step
    rw [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,← sum_filter,sum_const,nsmul_eq_mul] at sums
    exact sums.trans (add_le_add_right (mul_le_mul_of_nonneg_right
      ((show (((range m).filter (fun j => j+1 ∈ bad)).card : ℝ) ≤ bad.card by exact_mod_cast bd).trans (hbad t)) hg) _)
  simp_rw [← sum_mean]
  rw [sum_comm]
  simpa only [nsmul_eq_mul,card_univ,g] using univ.sum_le_card_nsmul _ _ (fun t _ => per t)

end
end Meyniel.Multiscale
