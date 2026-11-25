import Mathlib

/-! A finite uniform source of compatible guesses. One row of the source
chooses a member of every nonempty subset of tags. Splitting off a specified
coordinate proves that it is uniform on that subset. -/

namespace Meyniel.RandomTable

open Finset
noncomputable section

variable {A B I W : Type*}

def avg [Fintype A] (f : A → ℝ) : ℝ := (∑ a, f a) / Fintype.card A

@[simp] theorem avg_const [Fintype A] [Nonempty A] (c : ℝ) :
    avg (fun _ : A => c) = c := by
  simp only [avg, sum_const, card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c (by exact_mod_cast Fintype.card_ne_zero)

theorem avg_prod [Fintype A] [Fintype B] (f : A × B → ℝ) :
    avg f = avg (fun a : A => avg (fun b : B => f (a,b))) := by
  simp only [avg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← sum_div]
  ring

theorem avg_sum_finset [Fintype A] (s : Finset I) (f : I → A → ℝ) :
    avg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, avg (f i) := by
  simp only [avg, ← sum_div]
  rw [sum_comm]

theorem avg_sum [Fintype A] [Fintype I] (f : I → A → ℝ) :
    avg (fun a => ∑ i, f i a) = ∑ i, avg (f i) := avg_sum_finset univ f

theorem avg_mul_const [Fintype A] (f : A → ℝ) (c : ℝ) :
    avg (fun a => f a * c) = avg f * c := by
  simp only [avg, ← sum_mul]
  ring

theorem avg_equiv [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    avg (fun a => f (e a)) = avg f := by
  simp only [avg, e.sum_comp, Fintype.card_congr e]

@[simp] theorem avg_indicator_unique [Fintype A] [DecidableEq A] (a : A) :
    avg (fun z : A => if z = a then (1 : ℝ) else 0) = 1 / Fintype.card A := by
  simp [avg]

/-- Every coordinate of a uniform finite dependent product has its own
uniform marginal, provided the other coordinates are inhabited. -/
theorem avg_coordinate [Fintype I] [DecidableEq I] (P : I → Type*) [∀ i, Fintype (P i)]
    (hne : ∀ i, Nonempty (P i)) (i : I) (f : P i → ℝ) :
    avg (fun row : ∀ j, P j => f (row i)) = avg f := by
  classical
  let e := Equiv.piSplitAt i P
  letI : Nonempty ((j : {j : I // j ≠ i}) → P j) :=
    ⟨fun j => Classical.choice (hne j)⟩
  have h := avg_equiv e (fun z => f z.1)
  calc
    _ = avg (fun z : P i × ((j : {j : I // j ≠ i}) → P j) => f z.1) := h
    _ = _ := by rw [avg_prod]; simp

abbrev Key (W : Type*) := {B : Finset W // B.Nonempty}
abbrev Row (W : Type*) := (B : Key W) → {w : W // w ∈ B.val}

instance rowNonempty : Nonempty (Row W) :=
  ⟨fun B => Classical.choice B.property.to_subtype⟩

def select [DecidableEq W] (row : Row W) (B : Finset W) : Option W :=
  if hb : B.Nonempty then some ((row ⟨B,hb⟩).val) else none

theorem avg_select [Fintype W] [DecidableEq W] (B : Finset W) (w : W) :
    avg (fun row : Row W => if select row B = some w then (1:ℝ) else 0) =
      if w ∈ B then (1 : ℝ) / (B.card : ℝ) else 0 := by
  classical
  by_cases hb : B.Nonempty
  · let i : Key W := ⟨B,hb⟩
    let P := fun j : Key W => {z : W // z ∈ j.val}
    let f : P i → ℝ := fun z => if z.val = w then 1 else 0
    have hu : avg (fun row : Row W => if select row B = some w then (1:ℝ) else 0) = avg f := by
      simpa [select,hb,f,i,P] using avg_coordinate P (fun j => j.property.to_subtype) i f
    rw [hu]
    by_cases hw : w ∈ B
    · let v : P i := ⟨w,hw⟩
      have he : f = fun z => if z = v then 1 else 0 := by
        funext z
        change (if z.val = v.val then (1 : ℝ) else 0) = if z = v then 1 else 0
        by_cases hz : z = v
        · have hval : z.val = v.val := congrArg Subtype.val hz
          simp only [if_pos hz, if_pos hval]
        · have hval : z.val ≠ v.val := fun h => hz (Subtype.ext h)
          simp only [if_neg hz, if_neg hval]
      have hc : Fintype.card (P i) = B.card := Fintype.card_coe B
      rw [he, avg_indicator_unique, hc, if_pos hw]
    · have he : f = fun _ => 0 := by
        funext z
        have hne : z.val ≠ w := fun h => hw (h ▸ z.property)
        simp [f, hne]
      rw [he, if_neg hw]
      simp [avg]
  · rw [not_nonempty_iff_eq_empty.mp hb]
    simp [select,avg]

end
end Meyniel.RandomTable
