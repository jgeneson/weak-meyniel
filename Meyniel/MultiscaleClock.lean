module

public import Meyniel.Interception

/-! The integer clock for comparisons spaced B rounds apart, with targets
spaced h rounds apart. A label b traces the diagonal t+j=b until tB≤jh
last holds. This file uses row 0 for the first observation. -/

@[expose] public section

namespace Meyniel.Multiscale.Clock
open Finset

def row (B h b : ℕ) := b*h / (B+h)
def height (B h j : ℕ) := j*h/B
def top (B h M : ℕ) := M + height B h M
def column (B h b : ℕ) := b - row B h b

theorem le_row_iff {B h t b : ℕ} (hB : 0 < B) (hh : 0 < h) :
    t ≤ row B h b ↔ t ≤ b ∧ t*B ≤ (b-t)*h := by
  rw [row,Nat.le_div_iff_mul_le (by omega),Nat.mul_add]
  constructor
  · intro e
    have ht : t ≤ b := Nat.le_of_mul_le_mul_right (by omega : t*h ≤ b*h) hh
    refine ⟨ht,?_⟩
    rw [Nat.sub_mul]
    omega
  · rintro ⟨e,f⟩
    have := Nat.mul_le_mul_right h e
    rw [Nat.sub_mul] at f
    omega

theorem last_le {B h : ℕ} (hB : 0 < B) (hh : 0 < h) (b : ℕ) : row B h b ≤ b :=
  ((le_row_iff hB hh).mp le_rfl).1

theorem height_mono {B h : ℕ} : Monotone (height B h) :=
  fun _ _ hj => Nat.div_le_div_right (Nat.mul_le_mul_right _ hj)

theorem height_succ {B h : ℕ} (hB : 0 < B) (hb : h ≤ B) (j : ℕ) :
    height B h (j+1) ≤ height B h j + 1 := by
  unfold height
  rw [Nat.succ_mul]
  calc
    _ ≤ (j*h + B) / B := Nat.div_le_div_right (Nat.add_le_add_left hb _)
    _ = _ := Nat.add_div_right _ hB

theorem column_le {B h M b : ℕ} (hB : 0 < B) (hh : 0 < h) (hb : b ≤ top B h M) :
    column B h b ≤ M := by
  unfold top height at hb
  by_cases e : b ≤ M
  · unfold column; omega
  · have hz : b-M ≤ M*h/B := by omega
    have ht : b-M ≤ row B h b := (le_row_iff hB hh).mpr ⟨by omega,by
      have eqn : b-(b-M)=M := by omega
      rw [eqn]; exact (Nat.le_div_iff_mul_le hB).mp hz⟩
    unfold column; omega

def cells (B h M : ℕ) : Finset (ℕ × ℕ) :=
  ((range (top B h M+1)) ×ˢ (range (top B h M+1))).filter
    fun p => p.1 * B ≤ p.2 * h ∧ p.1+p.2 ≤ top B h M

theorem mem_cells {B h M t j : ℕ} : (t,j) ∈ cells B h M ↔
    t * B ≤ j * h ∧ t+j ≤ top B h M := by
  simp only [cells,mem_filter,mem_product,mem_range]
  omega

theorem sum_columns {B h : ℕ} (hB : 0 < B) (hh : 0 < h) (M : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ b ∈ range (top B h M+1), ∑ t ∈ range (row B h b+1), f t (b-t) =
    ∑ j ∈ range (top B h M+1), ∑ t ∈ range (min (height B h j) (top B h M-j)+1), f t j := by
  classical
  let g := fun p : ℕ × ℕ => f p.1 p.2
  have diag (b : ℕ) (hb : b ∈ range (top B h M+1)) :
      ∑ t ∈ range (row B h b+1), f t (b-t) =
      ∑ p ∈ (cells B h M).filter (fun p => p.1+p.2=b), g p := by
    apply sum_bij (fun t _ => (t,b-t))
    · intro t ht
      have e := (le_row_iff hB hh).mp (show t ≤ row B h b by simpa using ht)
      simp only [mem_range] at hb
      simp only [mem_filter,mem_cells]
      omega
    · intro i _ j _ e; exact congrArg Prod.fst e
    · rintro ⟨t,j⟩ hp
      simp only [mem_filter,mem_cells] at hp
      have hj : b-t=j := by omega
      refine ⟨t,?_,Prod.ext rfl hj⟩
      simp only [mem_range]
      exact Nat.lt_succ_of_le ((le_row_iff hB hh).mpr ⟨by omega,hj ▸ hp.1.1⟩)
    · intros; rfl
  have col (j : ℕ) (hj : j ∈ range (top B h M+1)) :
      ∑ t ∈ range (min (height B h j) (top B h M-j)+1), f t j =
      ∑ p ∈ (cells B h M).filter (fun p => p.2=j), g p := by
    apply sum_bij (fun t _ => (t,j))
    · intro t ht
      have hmin := le_min_iff.mp (show t ≤ min (height B h j) (top B h M-j) by simpa using ht)
      apply mem_filter.mpr
      refine ⟨mem_cells.mpr ⟨(Nat.le_div_iff_mul_le hB).mp hmin.1,?_⟩,rfl⟩
      simp only [mem_range] at hj
      omega
    · intro i _ j _ e; exact congrArg Prod.fst e
    · rintro ⟨t,k⟩ hp
      simp only [mem_filter,mem_cells] at hp
      obtain ⟨⟨hb,ht⟩,rfl⟩ := hp
      refine ⟨t,?_,rfl⟩
      simp only [mem_range,Nat.lt_succ_iff,le_min_iff]
      exact ⟨(Nat.le_div_iff_mul_le hB).mpr hb,by omega⟩
    · intros; rfl
  rw [sum_congr rfl diag,sum_congr rfl col]
  have hd (p : ℕ×ℕ) (hp : p ∈ cells B h M) : p.1+p.2 ∈ range (top B h M+1) := by
    obtain ⟨t,j⟩ := p
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_cells.mp hp).2)
  have hc (p : ℕ×ℕ) (hp : p ∈ cells B h M) : p.2 ∈ range (top B h M+1) := by
    obtain ⟨t,j⟩ := p
    exact mem_range.mpr (by have e := (mem_cells.mp hp).2; omega)
  rw [sum_fiberwise_of_maps_to hd g,sum_fiberwise_of_maps_to hc g]

/-- Terminal labels in column j correspond to the rows from the preceding
column's height (inclusive) through the current height. -/
theorem terminal_iff {B h : ℕ} (hB : 0 < B) (hh : 0 < h) (j t : ℕ) :
    row B h (t+j) = t ↔
      height B h (j-1) ≤ t ∧ t ≤ height B h j := by
  have ht : t ≤ row B h (t+j) ↔ t ≤ height B h j := by
    rw [le_row_iff hB hh, height, Nat.le_div_iff_mul_le hB]
    simp
  cases j with
  | zero =>
    simp [height] at ht ⊢
    exact ⟨fun e => ht.mp e.ge, fun e => by subst t; simp [row]⟩
  | succ j =>
    have hn : t+1 ≤ row B h (t+(j+1)) ↔ t+1 ≤ height B h j := by
      rw [le_row_iff hB hh,height,Nat.le_div_iff_mul_le hB]
      have e : t+(j+1)-(t+1)=j := by omega
      simp [e]
    simp only [Nat.add_sub_cancel_right]
    omega

theorem last_on_original {B h M : ℕ} (j : ℕ) (hj : j ≤ M) :
    min (height B h j) (top B h M-j) = height B h j := by
  have hj' := height_mono (B:=B) (h:=h) hj
  unfold top
  omega

theorem sum_terminals {B h : ℕ} (hB : 0 < B) (hh : 0 < h) (M : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ b ∈ range (top B h M+1), f (row B h b) (column B h b) =
    ∑ j ∈ range (M+1), ∑ t ∈ Icc (height B h (j-1)) (height B h j), f t j := by
  classical
  have a (j : ℕ) (hj : j ∈ range (M+1)) :
      ∑ t ∈ Icc (height B h (j-1)) (height B h j), f t j =
      ∑ b ∈ (range (top B h M+1)).filter (fun b => column B h b=j), f (row B h b) (column B h b) := by
    apply sum_bij (fun t _ => t+j)
    · intro t ht
      have wh := mem_Icc.mp ht
      have hj' := height_mono (B:=B) (h:=h) (show j ≤ M by simpa using hj)
      have r := (terminal_iff hB hh j t).mpr wh
      apply mem_filter.mpr
      constructor
      · apply mem_range.mpr
        unfold top
        have := mem_range.mp hj
        omega
      · unfold column
        rw [r]
        omega
    · intros; omega
    · intro b hb
      have rb := last_le hB hh b
      obtain ⟨_,hc⟩ := mem_filter.mp hb
      have e : row B h b+j=b := by unfold column at hc; omega
      exact ⟨row B h b,mem_Icc.mpr ((terminal_iff hB hh ..).mp (by rw [e])),e⟩
    · intro t ht
      have r := (terminal_iff hB hh j t).mpr (mem_Icc.mp ht)
      simp [r,column]
  rw [sum_congr rfl a]
  symm
  exact sum_fiberwise_of_maps_to (fun b hb => mem_range.mpr (Nat.lt_succ_of_le (column_le hB hh
    (show b ≤ top B h M by simpa using hb)))) _

/-- After one terminal entropy has cancelled, a possible second one is
paid for by half the common local support bound from each of the two labels. -/
theorem split_terminal {a b : ℕ} (hab : a ≤ b) (hba : b ≤ a+1)
    (v : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) (h : ∀ t ∈ Icc a b, v t ≤ L) :
    (∑ t ∈ Icc a b, (v t - L/2)) ≤ v b := by
  have e : b=a ∨ b=a+1 := by omega
  rcases e with he | he <;> subst b
  · simpa using (show v a-L/2 ≤ v a by linarith)
  · have s : Icc a (a+1) = {a,a+1} := by ext t; simp; omega
    have ha := h a (mem_Icc.mpr ⟨le_rfl,by omega⟩)
    simp [s]
    linarith

/-- Sum of all one-step entropy costs and all terminal conditional entropies.
The earlier of two terminals in a column is paid for by the local support cost. -/
theorem total_observation_cost {B h : ℕ} (hB : 0 < B) (hh : 0 < h) (hsmall : h ≤ B)
    (M : ℕ) (E : ℕ → ℕ → ℝ) (L : ℕ → ℝ)
    (hn : ∀ t j, 0 ≤ E t j) (hL : ∀ j ≤ M, 0 ≤ L j)
    (hlocal : ∀ j ≤ M, ∀ t ∈ Icc (height B h (j-1)) (height B h j), E (t+1) j ≤ L j) :
    (∑ b ∈ range (top B h M+1), ∑ t ∈ range (row B h b+1),
      (E t (b-t) - E (t+1) (b-t))) +
    (∑ b ∈ range (top B h M+1), (E (row B h b+1) (column B h b) - L (column B h b)/2)) ≤
    ∑ j ∈ range (top B h M+1), E 0 j := by
  rw [sum_columns hB hh M (fun t j => E t j-E (t+1) j),
    sum_terminals hB hh M (fun t j => E (t+1) j - L j/2)]
  simp only [Finset.sum_range_sub']
  rw [Finset.sum_sub_distrib]
  suffices he :
      (∑ j ∈ range (M+1), ∑ t ∈ Icc (height B h (j-1)) (height B h j), (E (t+1) j-L j/2)) ≤
      ∑ j ∈ range (top B h M+1), E (min (height B h j) (top B h M-j)+1) j by linarith
  calc
    _ ≤ ∑ j ∈ range (M+1), E (min (height B h j) (top B h M-j)+1) j := by
      apply sum_le_sum; intro j hj
      have hM : j ≤ M := by simpa using hj
      rw [last_on_original _ hM]
      apply split_terminal (height_mono (Nat.sub_le j 1)) _ (fun t => E (t+1) j) _ (hL j hM)
        (hlocal j hM)
      cases j with
      | zero => simp
      | succ j => simpa using height_succ hB hsmall j
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (range_subset_range.mpr (by unfold top; omega)) (fun j _ _ => hn _ j)

/-- A column still contributes at most log N until it reaches home. This
includes the last original target M amongst the D possible boundary charges. -/
theorem marginal_cost_bound {B h : ℕ} (M D : ℕ) (E : ℕ → ℝ) (L : ℝ)
    (_hL : 0 ≤ L) (hn : ∀ j, 0 ≤ E j) (hbound : ∀ j, E j ≤ L)
    (home : ∀ j, M+D ≤ j → E j=0) :
    ∑ j ∈ range (top B h M+1), E j ≤ (∑ j ∈ range M, E j) + D*L := by
  classical
  let u := top B h M+1
  have e : (∑ j ∈ range u, E j) = ∑ j ∈ (range u).filter (· < M+D), E j := by
    rw [sum_filter]
    exact sum_congr rfl fun j _ => by split_ifs with h; rfl; exact home j (by omega)
  rw [e]
  calc
    _ ≤ ∑ j ∈ range (M+D), E j := sum_le_sum_of_subset_of_nonneg
      (fun j hj => mem_range.mpr (mem_filter.mp hj).2) (fun j _ _ => hn j)
    _ ≤ _ := by
      rw [sum_range_add]
      apply add_le_add_right
      calc
        _ ≤ ∑ _j ∈ range D, L := sum_le_sum (fun j _ => hbound _)
        _ = _ := by simp

/-- The complete numerical inequality (1) for a multiscale clock, from its
one-observation log/Bellman inequality and its terminal information estimate.
E t j is H(Zj | prefix before reveal t). The sum of H(Zj) for j<M and the
D boundary columns are charged exactly as in the text. -/
theorem clock_pass {B h : ℕ} (hB : 0 < B) (hh : 0 < h) (hsmall : h ≤ B)
    (M D : ℕ) (E : ℕ → ℕ → ℝ) (large small d : ℕ → ℝ) (V : ℕ → ℕ → ℝ)
    (logS logWeight logN : ℝ)
    (hn : ∀ t j, 0 ≤ E t j) (hN : 0 ≤ logN) (hbound : ∀ j, E 0 j ≤ logN)
    (home : ∀ j, M+D ≤ j → E 0 j=0) (hL : ∀ j ≤ M, 0 ≤ large j)
    (hlocal : ∀ j ≤ M, ∀ t ∈ Icc (height B h (j-1)) (height B h j), E (t+1) j ≤ large j)
    (start : ∀ b ≤ top B h M, V b 0 ≤ logS)
    (step : ∀ b ≤ top B h M, ∀ t ≤ row B h b,
      V b (t+1) - V b t ≤ E t (b-t) - E (t+1) (b-t))
    (terminal : ∀ b ≤ top B h M, logWeight - large (column B h b)/2 - d b -
      E (row B h b+1) (column B h b) + small (column B h b) ≤ V b (row B h b+1)) :
    logWeight -
      ((∑ j ∈ range M, E 0 j)+D*logN) / (top B h M+1 : ℕ) -
      (∑ b ∈ range (top B h M+1), (large (column B h b) - small (column B h b) + d b)) /
        (top B h M+1 : ℕ) ≤ logS := by
  let J := top B h M+1
  have hJ : (0:ℝ) < J := by dsimp [J]; positivity
  have per (b : ℕ) (hb : b ∈ range J) : logWeight - logS ≤
      (∑ t ∈ range (row B h b+1), (E t (b-t) - E (t+1) (b-t))) +
      (E (row B h b+1) (column B h b) - large (column B h b)/2) +
      (large (column B h b)-small (column B h b)+d b) := by
    have hb' : b ≤ top B h M := by simpa [J] using hb
    have htel : V b (row B h b+1)-V b 0 ≤
        ∑ t ∈ range (row B h b+1), (E t (b-t)-E (t+1) (b-t)) := by
      rw [← sum_range_sub]
      exact sum_le_sum (fun t ht => step b hb' t (by simpa using ht))
    linarith [start b hb',terminal b hb']
  have hsum := sum_le_sum per
  simp only [sum_const,card_range,nsmul_eq_mul,sum_add_distrib] at hsum
  have hobs := total_observation_cost hB hh hsmall M E large hn hL hlocal
  have hm := marginal_cost_bound (B:=B) (h:=h) M D (E 0) logN hN (hn 0) hbound home
  change logWeight - _ / (J:ℝ) - _ / (J:ℝ) ≤ logS
  rw [sub_sub,← add_div,sub_le_iff_le_add',← sub_le_iff_le_add,le_div_iff₀ hJ]
  dsimp only [J] at hsum ⊢
  rw [sum_add_distrib]
  linarith


end Meyniel.Multiscale.Clock
