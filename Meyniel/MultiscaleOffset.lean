import Meyniel.MultiscaleClock
import Meyniel.MultiscaleQuotients

/-! # Endpoint density under a random top clock and offset -/
namespace Meyniel.Multiscale
open Finset

private theorem labels_per_column {B h : ℕ} (hB : 0 < B) (hh : h ≤ B) (j : ℕ) :
    (Icc (Clock.height B h (j-1)) (Clock.height B h j)).card ≤ 2 := by
  rw [Nat.card_Icc]
  cases j with
  | zero => simp
  | succ j =>
    simp only [Nat.add_one_sub_one]
    have step := Clock.height_succ (B:=B) (h:=h) hB hh j
    omega

/-- Before normalization each time can receive at most two offset-label pairs. -/
theorem offset_sum {B h M g T : ℕ} (hh : 0 < h) (hb : h ≤ B)
    (hmax : g + (h-1) + h*M ≤ T) (f : ℕ → ℝ) (hf : ∀ t, 0 ≤ f t) :
    ∑ x ∈ range h, ∑ b ∈ range (Clock.top B h M+1), f (g+x+h*Clock.column B h b)
      ≤ 2*∑ t ∈ range (T+1), f t := by
  let L := (range h) ×ˢ (range (M+1))
  let time (v : ℕ × ℕ) := g+v.1+h*v.2
  have hinj : Set.InjOn time (L : Set (ℕ × ℕ)) := by
    rintro ⟨x,j⟩ hx ⟨y,k⟩ hy he
    have hx' := mem_range.mp (mem_product.mp hx).1
    have hy' := mem_range.mp (mem_product.mp hy).1
    change g+x+h*j=g+y+h*k at he
    have head : x+h*j=y+h*k := by omega
    have hq := congrArg (·/h) head
    rw [Nat.add_mul_div_left _ _ hh,Nat.add_mul_div_left _ _ hh,Nat.div_eq_of_lt hx',
      Nat.div_eq_of_lt hy',Nat.zero_add,Nat.zero_add] at hq
    subst k
    have : x=y := by omega
    subst y
    rfl
  have hsub : L.image time ⊆ range (T+1) := by
    intro t ht
    obtain ⟨⟨x,j⟩,hp,rfl⟩ := mem_image.mp ht
    have hx := mem_range.mp (mem_product.mp hp).1
    have hj := mem_range.mp (mem_product.mp hp).2
    have h := Nat.mul_le_mul_left h (show j ≤ M by omega)
    apply mem_range.mpr; dsimp [time]; omega
  have hsum : ∑ x ∈ range h, ∑ j ∈ range (M+1), f (g+x+h*j) ≤ ∑ t ∈ range (T+1), f t := by
    rw [← Finset.sum_product (range h) (range (M+1)) (fun p => f (time p))]
    change ∑ v ∈ L, f (time v) ≤ _
    rw [← Finset.sum_image hinj]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hf i)
  calc
    _ ≤ ∑ x ∈ range h, 2 * ∑ j ∈ range (M+1), f (g+x+h*j) := by
      apply sum_le_sum; intro x _
      rw [Clock.sum_terminals (hh.trans_le hb) hh M (fun _ j => f (g+x+h*j)),mul_sum]
      apply sum_le_sum; intro j _
      rw [sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (hf _)
      exact_mod_cast labels_per_column (hh.trans_le hb) hb j
    _ = 2*(∑ x ∈ range h, ∑ j ∈ range (M+1), f (g+x+h*j)) := (mul_sum ..).symm
    _ ≤ _ := by linarith

/-- The mean cost at the selected endpoint is at most 4/T times the sum over
all actual rounds. Translation of costs on the cyclic window preserves this sum. -/
theorem offset_average {B h M g T : ℕ} (hh : 0 < h) (hb : h ≤ B) (hT : 0 < T)
    (hmax : g+(h-1)+h*M ≤ T) (hspan : T ≤ 2*(M*h)) (f : ℕ → ℝ) (hf : ∀ t, 0 ≤ f t) :
    (∑ x ∈ range h, ∑ b ∈ range (Clock.top B h M+1), f (g+x+h*Clock.column B h b)) /
      ((Clock.top B h M+1 : ℕ):ℝ) / h ≤ (4/T) * ∑ t ∈ range (T+1), f t := by
  let J := Clock.top B h M+1
  have hJ : (0:ℝ) < J := by dsimp [J]; positivity
  have hh' : (0:ℝ) < h := by exact_mod_cast hh
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hM : M ≤ J := by dsimp [J,Clock.top]; omega
  have hspan' : (T:ℝ) ≤ 2*(J:ℝ)*h := by
    exact_mod_cast (show T ≤ 2*J*h by nlinarith only [hspan, Nat.mul_le_mul_right h hM])
  have hsum := offset_sum hh hb hmax f hf
  set S := ∑ t ∈ range (T+1), f t
  have hS : 0 ≤ S := sum_nonneg (fun _ _ => hf _)
  change _ / (J:ℝ) / (h:ℝ) ≤ 4/T * S
  apply (div_le_iff₀ hh').mpr
  apply (div_le_iff₀ hJ).mpr
  apply hsum.trans
  field_simp [hT'.ne']
  nlinarith only [mul_le_mul_of_nonneg_right hspan' hS]

theorem cyclic_sum (T : ℕ) (f : ZMod (T+1) → ℝ) :
    ∑ t ∈ range (T+1), f (t:ZMod (T+1)) = ∑ t, f t := by
  apply Finset.sum_bij (fun (t : ℕ) _ => (t:ZMod (T+1)))
  · simp
  · intro a ha b hb eq
    have h := congrArg ZMod.val eq
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt (mem_range.mp ha),Nat.mod_eq_of_lt (mem_range.mp hb)] at h
    exact h
  · intro a _
    exact ⟨a.val,mem_range.mpr (ZMod.val_lt a),ZMod.natCast_zmod_val a⟩
  · simp

theorem cyclic_offset_average {B h M g T : ℕ} (hh : 0 < h) (hb : h ≤ B) (hT : 0 < T)
    (hmax : g+(h-1)+h*M ≤ T) (hspan : T ≤ 2*(M*h))
    (f : ZMod (T+1) → ℝ) (hf : ∀ t, 0 ≤ f t) (shift : ZMod (T+1)) :
    (∑ x ∈ range h, ∑ b ∈ range (Clock.top B h M+1),
      f (((g+x+h*Clock.column B h b : ℕ) : ZMod (T+1)) + shift)) /
      ((Clock.top B h M+1 : ℕ):ℝ) / h ≤ (4/T) * ∑ t, f t := by
  have he := offset_average hh hb hT hmax hspan (fun t => f ((t:ZMod (T+1))+shift)) (fun _ => hf _)
  rw [cyclic_sum T (fun t => f (t+shift))] at he
  have hs : ∑ t, f (t+shift) = ∑ t, f t := Finset.sum_equiv (Equiv.addRight shift) (by simp) (fun _ _ => rfl)
  rw [hs] at he
  exact he

end Meyniel.Multiscale
