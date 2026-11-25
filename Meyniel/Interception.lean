import Mathlib

/-! Finite counting and the diagonal estimate in the one-cop interception argument.
The type of walks below is the original nonempty family, with its uniform law.
-/ 

open Finset
open scoped BigOperators

namespace Meyniel.Interception

noncomputable section

variable {W K V : Type*}

def mean (s : Finset W) (f : W → ℝ) : ℝ :=
  (∑ w ∈ s, f w) / s.card

theorem mean_pos {s : Finset W} {f : W → ℝ} (hs : s.Nonempty)
    (hf : ∀ w ∈ s, 0 < f w) : 0 < mean s f := by
  exact div_pos (sum_pos hf hs) (by exact_mod_cast hs.card_pos)

theorem sum_log_le_card_mul_log_mean {s : Finset W} {f : W → ℝ} (hs : s.Nonempty)
    (hf : ∀ w ∈ s, 0 < f w) :
    ∑ w ∈ s, Real.log (f w) ≤ s.card * Real.log (mean s f) := by
  have hm := mean_pos hs hf
  have h := sum_le_sum (s := s) (fun w hw =>
    Real.log_le_sub_one_of_pos (div_pos (hf w hw) hm))
  have heq : ∑ w ∈ s, Real.log (f w / mean s f) =
      ∑ w ∈ s, Real.log (f w) - s.card * Real.log (mean s f) := by
    rw [← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib]
    exact sum_congr rfl fun w hw => Real.log_div (hf w hw).ne' hm.ne'
  have hr : ∑ w ∈ s, (f w / mean s f - 1) = 0 := by
    rw [sum_sub_distrib, ← sum_div, sum_const, nsmul_eq_mul, mul_one, sub_eq_zero,
      div_eq_iff hm.ne']
    unfold mean
    have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
    field_simp
  linarith [heq, hr]

def fiber [Fintype W] [DecidableEq K] (key : W → K) (k : K) : Finset W :=
  univ.filter fun w => key w = k

def blockMean [Fintype W] [DecidableEq K] (key : W → K) (f : W → ℝ) (w : W) : ℝ :=
  mean (fiber key (key w)) f

theorem mem_own_fiber [Fintype W] [DecidableEq K] (key : W → K) (w : W) :
    w ∈ fiber key (key w) := by simp [fiber]

theorem blockMean_pos [Fintype W] [DecidableEq K] (key : W → K) (f : W → ℝ)
    (hf : ∀ w, 0 < f w) (w : W) : 0 < blockMean key f w :=
  mean_pos ⟨w, mem_own_fiber key w⟩ (fun v _ => hf v)

theorem sum_by_fiber [Fintype W] [DecidableEq K] (key : W → K) (f : W → ℝ) :
    ∑ k ∈ univ.image key, ∑ w ∈ fiber key k, f w = ∑ w, f w := by
  classical
  exact sum_fiberwise_of_maps_to (fun w hw => mem_image_of_mem key hw) f

theorem block_log_le [Fintype W] [DecidableEq K] (key : W → K) (f : W → ℝ)
    (hf : ∀ w, 0 < f w) :
    ∑ w, Real.log (f w) ≤ ∑ w, Real.log (blockMean key f w) := by
  classical
  rw [← sum_by_fiber key (fun w => Real.log (f w)),
    ← sum_by_fiber key (fun w => Real.log (blockMean key f w))]
  apply sum_le_sum
  intro k hk
  obtain ⟨w, _, rfl⟩ := mem_image.mp hk
  let s := fiber key (key w)
  have hs : s.Nonempty := ⟨w, mem_own_fiber key w⟩
  calc
    _ ≤ s.card * Real.log (mean s f) :=
      sum_log_le_card_mul_log_mean hs (fun v _ => hf v)
    _ = ∑ v ∈ s, Real.log (mean s f) := by simp
    _ = _ := sum_congr rfl fun v hv => by
      have h : key v = key w := (mem_filter.mp hv).2
      simp [blockMean, h, s]

def logMean [Fintype W] (f : W → ℝ) : ℝ := mean univ (fun w => Real.log (f w))

theorem logMean_le_log_mean [Fintype W] [Nonempty W] {f : W → ℝ} (hf : ∀ w, 0 < f w) :
    logMean f ≤ Real.log (mean univ f) := by
  have h := sum_log_le_card_mul_log_mean (s := univ) univ_nonempty (fun w _ => hf w)
  unfold logMean mean
  apply (div_le_iff₀ (by exact_mod_cast (univ_nonempty : (univ : Finset W).Nonempty).card_pos)).2
  simpa [mean, mul_comm] using h

theorem logMean_update [Fintype W] [Nonempty W] [DecidableEq K]
    (key : W → K) (old new pre post : W → ℝ)
    (ho : ∀ w, 0 < old w) (hp : ∀ w, 0 < pre w) (hq : ∀ w, 0 < post w)
    (hu : ∀ w, new w = blockMean key old w * pre w / post w) :
    logMean old + (logMean pre - logMean post) ≤ logMean new := by
  have he : ∀ w, Real.log (new w) =
      Real.log (blockMean key old w) + Real.log (pre w) - Real.log (post w) := by
    intro w
    rw [hu w, Real.log_div (mul_pos (blockMean_pos key old ho _) (hp _)).ne' (hq _).ne',
      Real.log_mul (blockMean_pos key old ho _).ne' (hp _).ne']
  simp only [logMean, mean, he, sum_sub_distrib, sum_add_distrib]
  simp only [sub_div, add_div]
  have hh := div_le_div_of_nonneg_right (block_log_le key old ho) (show 0 ≤ ((univ : Finset W).card : ℝ) by positivity)
  linarith


theorem logMean_mono [Fintype W] {f g : W → ℝ} (hf : ∀ w, 0 < f w) (h : ∀ w, f w ≤ g w) :
    logMean f ≤ logMean g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun w _ => Real.log_le_log (hf w) (h w)))
    (show 0 ≤ ((univ : Finset W).card : ℝ) by positivity)

theorem logMean_bellman [Fintype W] [Nonempty W] [DecidableEq K]
    (key : W → K) (old new pre post : W → ℝ)
    (hn : ∀ w, 0 < new w) (hp : ∀ w, 0 < pre w) (hq : ∀ w, 0 < post w)
    (hu : ∀ w, blockMean key (fun z => new z * pre z / post z) w ≤ old w) :
    logMean new + (logMean pre - logMean post) ≤ logMean old := by
  let f := fun z => new z * pre z / post z
  have hf : ∀ z, 0 < f z := fun z => div_pos (mul_pos (hn z) (hp z)) (hq z)
  calc
    logMean new + (logMean pre - logMean post) = logMean f := by
      have he (w : W) : Real.log (f w) = Real.log (new w) + Real.log (pre w) - Real.log (post w) := by
        dsimp only [f]
        rw [Real.log_div (mul_pos (hn w) (hp w)).ne' (hq w).ne',
          Real.log_mul (hn w).ne' (hp w).ne']
      simp only [logMean, mean, he, sum_sub_distrib, sum_add_distrib, sub_div, add_div]
      ring
    _ ≤ logMean (blockMean key f) := div_le_div_of_nonneg_right (block_log_le key f hf)
      (show 0 ≤ ((univ : Finset W).card : ℝ) by positivity)
    _ ≤ _ := logMean_mono (blockMean_pos key f hf) hu

/-- Marginal mass of the tagged walk's own vertex at one specified time. -/
def frequency [Fintype W] [DecidableEq V] (position : W → V) (w : W) : ℝ :=
  ((fiber position (position w)).card : ℝ) / Fintype.card W

theorem frequency_pos [Fintype W] [Nonempty W] [DecidableEq V] (position : W → V) (w : W) :
    0 < frequency position w := by
  have hc := (show (fiber position (position w)).Nonempty from ⟨w, mem_own_fiber position w⟩).card_pos
  exact div_pos (by exact_mod_cast hc) (by exact_mod_cast Fintype.card_pos (α := W))

theorem mean_inv_frequency [Fintype W] [Nonempty W] [DecidableEq V] (position : W → V) :
    mean univ (fun w => (frequency position w)⁻¹) = (univ.image position).card := by
  classical
  have h (v : V) (hv : v ∈ univ.image position) :
      ∑ w ∈ fiber position v, (frequency position w)⁻¹ = Fintype.card W := by
    obtain ⟨w, _, rfl⟩ := mem_image.mp hv
    let s := fiber position (position w)
    have hs : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast (show s.Nonempty from ⟨w, mem_own_fiber position w⟩).card_pos.ne'
    calc
      _ = ∑ _v ∈ s, ((s.card : ℝ) / Fintype.card W)⁻¹ := by
        apply sum_congr rfl
        intro v hv
        have hh : position v = position w := (mem_filter.mp hv).2
        simp [frequency, hh, s]
      _ = _ := by simp only [sum_const, nsmul_eq_mul, inv_div]; field_simp
  unfold mean
  rw [← sum_by_fiber position (fun w => (frequency position w)⁻¹), sum_congr rfl h]
  have hw : (Fintype.card W : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  simp [hw]

theorem logMean_frequency_ge [Fintype W] [Nonempty W] [DecidableEq V] (position : W → V) :
    -Real.log ((univ.image position).card) ≤ logMean (frequency position) := by
  have h := logMean_le_log_mean (fun w => inv_pos.mpr (frequency_pos position w))
  rw [mean_inv_frequency] at h
  simpa [logMean, mean, Real.log_inv, Finset.sum_neg_distrib, neg_div, neg_le] using h

/-- Total along a diagonal, from time zero to the meeting row. -/
def diagonalSum (b : ℕ) (a : ℕ → ℕ → ℝ) :=
  ∑ t ∈ range (b / 2 + 1), a t (b - t)

theorem backward_telescope (b : ℕ) (a : ℕ → ℕ → ℝ) (v : ℕ → ℝ)
    (h : ∀ t ≤ b / 2, v (t+1) + a t (b-t) ≤ v t) :
    diagonalSum b a ≤ v 0 - v (b / 2 + 1) := by
  unfold diagonalSum
  rw [← sum_range_sub' v]
  apply sum_le_sum
  intro t ht
  have := h t (by simpa using ht)
  linarith

theorem forward_telescope (b : ℕ) (a : ℕ → ℕ → ℝ) (v : ℕ → ℝ)
    (h : ∀ t ≤ b / 2, v t + a t (b-t) ≤ v (t+1)) :
    diagonalSum b a ≤ v (b / 2 + 1) - v 0 := by
  unfold diagonalSum
  rw [← sum_range_sub v]
  apply sum_le_sum
  intro t ht
  have := h t (by simpa using ht)
  linarith

private def cells (T : ℕ) : Finset (ℕ × ℕ) :=
  ((range (2*T+1)) ×ˢ (range (2*T+1))).filter fun q => q.1 ≤ q.2 ∧ q.1+q.2 ≤ 2*T

private theorem mem_cells {T t j : ℕ} :
    (t,j) ∈ cells T ↔ t ≤ j ∧ t+j ≤ 2*T := by
  simp only [cells, mem_filter, mem_product, mem_range]
  omega

theorem sum_diagonals_eq_sum_columns (T : ℕ) (a : ℕ → ℕ → ℝ) :
    ∑ b ∈ range (2*T+1), diagonalSum b a =
      ∑ j ∈ range (2*T+1), ∑ t ∈ range (min j (2*T-j)+1), a t j := by
  classical
  let f := fun q : ℕ × ℕ => a q.1 q.2
  have hdiag (b : ℕ) (hb : b ∈ range (2*T+1)) : diagonalSum b a =
      ∑ q ∈ (cells T).filter (fun q => q.1+q.2=b), f q := by
    apply sum_bij (fun t _ => (t,b-t))
    · intro t ht
      simp only [mem_range] at ht hb
      simp only [mem_filter, mem_cells]
      omega
    · intro i _ j _ hij
      exact congrArg Prod.fst hij
    · rintro ⟨t,j⟩ h
      simp only [mem_filter, mem_cells] at h
      exact ⟨t, by simp only [mem_range]; omega, by exact Prod.ext rfl (by change b - t = j; omega)⟩
    · intros; rfl
  have hcol (j : ℕ) (hj : j ∈ range (2*T+1)) :
      ∑ t ∈ range (min j (2*T-j)+1), a t j =
      ∑ q ∈ (cells T).filter (fun q => q.2=j), f q := by
    apply sum_bij (fun t _ => (t,j))
    · intro t ht
      have hm : t ≤ min j (2*T-j) := by simpa using ht
      have h₁ := (le_min_iff.mp hm).1
      have h₂ := (le_min_iff.mp hm).2
      have hj' : j ≤ 2*T := by simpa using hj
      apply mem_filter.mpr
      exact ⟨mem_cells.mpr ⟨h₁, by omega⟩, rfl⟩
    · intro i _ k _ hik
      exact congrArg Prod.fst hik
    · rintro ⟨t,j'⟩ h
      simp only [mem_filter, mem_cells] at h
      exact ⟨t, by simp only [mem_range]; omega, by exact Prod.ext rfl h.2.symm⟩
    · intros; rfl
  rw [sum_congr rfl hdiag, sum_congr rfl hcol]
  have hd (q : ℕ × ℕ) (hq : q ∈ cells T) : q.1+q.2 ∈ range (2*T+1) := by
    obtain ⟨t,j⟩ := q
    simp only [mem_cells] at hq
    simp only [mem_range]
    omega
  have hc (q : ℕ × ℕ) (hq : q ∈ cells T) : q.2 ∈ range (2*T+1) := by
    obtain ⟨t,j⟩ := q
    simp only [mem_cells] at hq
    simp only [mem_range]
    omega
  rw [sum_fiberwise_of_maps_to hd f, sum_fiberwise_of_maps_to hc f]


/-- The global log bound resulting from summing the costs of revealing each
column. Once the original column is constant its log marginal contributes zero. -/
theorem summed_diagonal_lower (T cut : ℕ) (L : ℝ) (q : ℕ → ℕ → ℝ)
    (hL : 0 ≤ L) (hfirst : ∀ j ≤ 2*T, -L ≤ q 0 j)
    (hhome : ∀ j ≤ 2*T, cut ≤ j → 0 ≤ q 0 j)
    (hlast : ∀ j ≤ 2*T, q (min j (2*T-j)+1) j ≤ 0) :
    -(cut : ℝ) * L ≤ ∑ b ∈ range (2*T+1),
      diagonalSum b (fun t j => q t j - q (t+1) j) := by
  rw [sum_diagonals_eq_sum_columns]
  simp only [sum_range_sub']
  let J := (range (2*T+1)).filter (fun j => j < cut)
  have hc : J.card ≤ cut := by
    rw [← card_range cut]
    exact card_le_card (fun j hj => mem_range.mpr (mem_filter.mp hj).2)
  have hsum : (∑ j ∈ range (2*T+1), if j < cut then -L else 0) = J.card * (-L) := by
    rw [← sum_filter]
    simp [J]
  calc
    _ ≤ J.card * (-L) := by
      have hcr : (J.card : ℝ) ≤ cut := by exact_mod_cast hc
      nlinarith [mul_le_mul_of_nonneg_right hcr hL]
    _ = _ := hsum.symm
    _ ≤ _ := by
      apply sum_le_sum
      intro j hj
      have hj' : j ≤ 2*T := by simpa using hj
      by_cases h : j < cut
      · simp only [h, if_true]
        linarith [hfirst j hj', hlast j hj']
      · simpa [h] using (sub_nonneg.mpr ((hlast j hj').trans (hhome j hj' (by omega))))

/-- Some diagonal has the required success fraction as soon as its log fraction
dominates the sum of the one-step changes in log weight along that diagonal. -/
theorem exists_good_diagonal (T d n : ℕ) (q : ℕ → ℕ → ℝ) (s : ℕ → ℝ)
    (hn : 1 ≤ n) (ht : (d : ℝ) * Real.log n ≤ (T : ℝ) * Real.log 2)
    (hs : ∀ b ≤ 2*T, 0 < s b)
    (hfirst : ∀ j ≤ 2*T, -Real.log n ≤ q 0 j)
    (hhome : ∀ j ≤ 2*T, T+d ≤ j → 0 ≤ q 0 j)
    (hlast : ∀ j ≤ 2*T, q (min j (2*T-j)+1) j ≤ 0)
    (hdiag : ∀ b ≤ 2*T,
      diagonalSum b (fun t j => q t j - q (t+1) j) ≤ Real.log (s b)) :
    ∃ b ≤ 2*T, 1 / Real.sqrt (2*n) ≤ s b := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n:ℝ) := by linarith
  have hln := Real.log_nonneg hn'
  have hl2 := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
  have hq := summed_diagonal_lower T (T+d) (Real.log n) q hln hfirst hhome hlast
  have hsum := hq.trans (sum_le_sum (s := range (2*T+1))
    (fun b hb => hdiag b (by simpa using hb)))
  by_contra! hc
  have hlt := sum_lt_sum_of_nonempty (s := range (2*T+1))
    (show (range (2*T+1)).Nonempty from ⟨0, mem_range.mpr (by omega)⟩)
    (fun b hb => Real.strictMonoOn_log (hs b (by simpa using hb))
      (show 0 < 1 / Real.sqrt (2*(n:ℝ)) by positivity) (hc b (by simpa using hb)))
  rw [sum_const, nsmul_eq_mul, card_range] at hlt
  rw [one_div, Real.log_inv, Real.log_sqrt (by positivity),
    Real.log_mul (by norm_num) hnpos.ne'] at hlt
  push_cast at hsum hlt
  nlinarith

/-- Converting the paper's natural-valued inequality to the logarithmic
initialization used by the diagonal estimate. -/
theorem horizon_log_of_pow {d T n : ℕ} (hn : 0 < n) (h : n^d ≤ 2^T) :
    (d : ℝ) * Real.log n ≤ (T : ℝ) * Real.log 2 := by
  have h' : (n : ℝ)^d ≤ (2 : ℝ)^T := by exact_mod_cast h
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos (by exact_mod_cast hn) d) h'


@[simp] theorem logMean_one [Fintype W] : logMean (fun _ : W => 1) = 0 := by
  simp [logMean, mean]

theorem logMean_nonpos [Fintype W] (f : W → ℝ) (h : ∀ w, 0 < f w ∧ f w ≤ 1) :
    logMean f ≤ 0 := by
  exact (logMean_mono (fun w => (h w).1) (fun w => (h w).2)).trans_eq logMean_one

theorem logMean_frequency_ge_of_card_le [Fintype W] [Nonempty W] [Fintype V] [DecidableEq V]
    (position : W → V) (n : ℕ) (hn : Fintype.card V ≤ n) :
    -Real.log n ≤ logMean (frequency position) := by
  have hcard : (univ.image position).card ≤ n := (card_le_univ _).trans hn
  have hnz : 0 < (univ.image position).card :=
    (univ_nonempty.image position).card_pos
  have hl := Real.log_le_log (show 0 < (((univ.image position).card : ℕ) : ℝ) by exact_mod_cast hnz)
    (show (((univ.image position).card : ℕ) : ℝ) ≤ n by exact_mod_cast hcard)
  exact (neg_le_neg hl).trans (logMean_frequency_ge position)

theorem frequency_of_constant [Fintype W] [Nonempty W] [DecidableEq V] {position : W → V}
    (h : ∀ v w, position v = position w) (w : W) : frequency position w = 1 := by
  have hs : fiber position (position w) = univ := by
    ext v
    simp [fiber, h v w]
  simp [frequency, hs, Fintype.card_ne_zero]

/-- Supply a cell-by-cell Bellman bound and a terminal condition, and obtain a
good diagonal. The columns and their marginal frequencies are ordinary maps
on the original finite family of walks. -/
theorem exists_good_of_bellman [Fintype W] [Nonempty W] [Fintype V] [DecidableEq V]
    [DecidableEq K] (T d n : ℕ) (hn : 1 ≤ n) (hsize : Fintype.card V ≤ n)
    (hT : (d : ℝ) * Real.log n ≤ (T : ℝ) * Real.log 2)
    (position : ℕ → W → V) (p v : ℕ → ℕ → W → ℝ) (key : ℕ → ℕ → W → K)
    (s : ℕ → ℝ)
    (hpos : ∀ t j w, 0 < p t j w ∧ p t j w ≤ 1)
    (hzero : ∀ j, p 0 j = frequency (position j))
    (hhome : ∀ j, T+d ≤ j → ∀ x y, position j x = position j y)
    (hvend : ∀ b ≤ 2*T, v b (b/2+1) = fun _ => 1)
    (hv : ∀ b ≤ 2*T, ∀ t ≤ b/2+1, ∀ w, 0 < v b t w)
    (hstep : ∀ b ≤ 2*T, ∀ t ≤ b/2, ∀ w,
      blockMean (key t (b-t))
        (fun z => v b (t+1) z * p t (b-t) z / p (t+1) (b-t) z) w ≤ v b t w)
    (hstart : ∀ b ≤ 2*T, mean univ (v b 0) ≤ s b) :
    ∃ b ≤ 2*T, 1 / Real.sqrt (2*n) ≤ s b := by
  apply exists_good_diagonal T d n (fun t j => logMean (p t j)) s hn hT
  · intro b hb
    exact (mean_pos univ_nonempty (fun w _ => hv b hb 0 (by omega) w)).trans_le (hstart b hb)
  · intro j _
    rw [hzero]
    exact logMean_frequency_ge_of_card_le _ _ hsize
  · intro j _ hj
    rw [hzero]
    have hh := funext (frequency_of_constant (hhome j hj))
    rw [hh, logMean_one]
  · intro j _
    exact logMean_nonpos _ (hpos _ _)
  · intro b hb
    have ht := backward_telescope b (fun t j => logMean (p t j) - logMean (p (t+1) j))
      (fun t => logMean (v b t))
      (fun t hd => logMean_bellman (key t (b-t)) _ _ _ _ (hv b hb (t+1) (by omega))
        (fun w => (hpos _ _ w).1) (fun w => (hpos _ _ w).1) (hstep b hb t hd))
    rw [hvend b hb, logMean_one, sub_zero] at ht
    have hp := hv b hb 0 (by omega)
    exact ht.trans ((logMean_le_log_mean hp).trans
      (Real.log_le_log (mean_pos univ_nonempty (fun w _ => hp w)) (hstart b hb)))


@[simp] theorem logMean_const [Fintype W] [Nonempty W] (r : ℝ) :
    logMean (fun _ : W => r) = Real.log r := by
  simp [logMean, mean, Fintype.card_ne_zero]

/-- For one diagonal it is enough to bound the first backward value by the
success rate. Positivity of every intermediate value follows from the recursion. -/
theorem bellman_diagonal [Fintype W] [Nonempty W] [DecidableEq K]
    (b : ℕ) (p : ℕ → ℕ → W → ℝ) (v : ℕ → W → ℝ) (key : ℕ → W → K) (s : ℝ)
    (hp : ∀ t j w, 0 < p t j w)
    (hend : ∀ w, v (b/2+1) w = 1) (hstart : ∀ w, v 0 w ≤ s)
    (hstep : ∀ t ≤ b/2, ∀ w, blockMean (key t)
      (fun z => v (t+1) z * p t (b-t) z / p (t+1) (b-t) z) w ≤ v t w) :
    0 < s ∧ diagonalSum b (fun t j => logMean (p t j) - logMean (p (t+1) j)) ≤
      Real.log s := by
  have hv (t : ℕ) (ht : t ≤ b/2+1) : ∀ w, 0 < v t w := by
    induction ht using Nat.decreasingInduction with
    | self => intro w; rw [hend w]; norm_num
    | of_succ i hi ih =>
      intro w
      exact (blockMean_pos (key i) _
        (fun z => div_pos (mul_pos (ih z) (hp i (b-i) z)) (hp (i+1) (b-i) z)) w).trans_le
        (hstep i (by omega) w)
  have hv0 := hv 0 (by omega)
  constructor
  · let w : W := Classical.choice (inferInstance : Nonempty W)
    exact (hv0 w).trans_le (hstart w)
  · have ht := backward_telescope b (fun t j => logMean (p t j) - logMean (p (t+1) j))
      (fun t => logMean (v t))
      (fun t hd => logMean_bellman (key t) _ _ _ _ (hv (t+1) (by omega))
        (hp t (b-t)) (hp (t+1) (b-t)) (hstep t hd))
    rw [funext hend, logMean_one, sub_zero] at ht
    exact ht.trans ((logMean_mono hv0 hstart).trans_eq (logMean_const s))

/-- Direct bridge from a fixed-diagonal strategy and the actual column marginal
frequencies to a strategy attaining the claimed fraction. -/
theorem exists_good_from_diagonal [Fintype W] [Nonempty W] [Fintype V] [DecidableEq V]
    (T d n : ℕ) (hn : 1 ≤ n) (hsize : Fintype.card V ≤ n)
    (hT : (d : ℝ) * Real.log n ≤ (T : ℝ) * Real.log 2)
    (position : ℕ → W → V) (p : ℕ → ℕ → W → ℝ) (s : ℕ → ℝ)
    (hpos : ∀ t j w, 0 < p t j w ∧ p t j w ≤ 1)
    (hzero : ∀ j, p 0 j = frequency (position j))
    (hhome : ∀ j, T+d ≤ j → ∀ x y, position j x = position j y)
    (hdiag : ∀ b ≤ 2*T, 0 < s b ∧
      diagonalSum b (fun t j => logMean (p t j) - logMean (p (t+1) j)) ≤ Real.log (s b)) :
    ∃ b ≤ 2*T, 1 / Real.sqrt (2*n) ≤ s b := by
  apply exists_good_diagonal T d n (fun t j => logMean (p t j)) s hn hT
    (fun b hb => (hdiag b hb).1)
  · intro j _
    rw [hzero]
    exact logMean_frequency_ge_of_card_le _ _ hsize
  · intro j _ hj
    rw [hzero, funext (frequency_of_constant (hhome j hj)), logMean_one]
  · intro j _
    exact logMean_nonpos _ (hpos _ _)
  · exact fun b hb => (hdiag b hb).2

end
end Meyniel.Interception
