import Meyniel.Interception

/-! Weighted finite expectation, conditional entropy, and the one-observation
inequality of the multiscale comparison clock. Atoms may include the smoothing
choices. The type of atoms is the positive support of the input law. -/

namespace Meyniel.Multiscale
open Finset Interception

noncomputable section

variable {Ω A B Z : Type*} [Fintype Ω]

def mass (μ : Ω → ℝ) (a : Finset Ω) : ℝ := ∑ w ∈ a, μ w

def avgOn (μ : Ω → ℝ) (a : Finset Ω) (v : Ω → ℝ) : ℝ :=
  (∑ w ∈ a, μ w * v w) / mass μ a

def expect (μ v : Ω → ℝ) : ℝ := ∑ w, μ w * v w

def atom [DecidableEq A] (a : Ω → A) (w : Ω) : Finset Ω := fiber a (a w)

def condProb [DecidableEq A] [DecidableEq Z] (μ : Ω → ℝ) (a : Ω → A) (z : Ω → Z) (w : Ω) : ℝ :=
  mass μ (atom (fun u => (a u,z u)) w) / mass μ (atom a w)

def condEntropy [DecidableEq A] [DecidableEq Z] (μ : Ω → ℝ) (a : Ω → A) (z : Ω → Z) : ℝ :=
  -expect μ (fun w => Real.log (condProb μ a z w))

omit [Fintype Ω] in
theorem mass_pos {μ : Ω → ℝ} (hμ : ∀ w, 0 < μ w) {s : Finset Ω} (hs : s.Nonempty) :
    0 < mass μ s := sum_pos (fun i _ => hμ i) hs

theorem atom_mass_pos [DecidableEq A] (μ : Ω → ℝ) (hμ : ∀ w, 0 < μ w) (a : Ω → A) (w : Ω) :
    0 < mass μ (atom a w) := mass_pos hμ ⟨w,mem_own_fiber a w⟩

theorem condProb_pos [DecidableEq A] [DecidableEq Z] (μ : Ω → ℝ) (hμ : ∀ w, 0 < μ w)
    (a : Ω → A) (z : Ω → Z) (w : Ω) : 0 < condProb μ a z w :=
  div_pos (atom_mass_pos μ hμ _ _) (atom_mass_pos μ hμ _ _)

omit [Fintype Ω] in
theorem weighted_log_sum {μ v : Ω → ℝ} (hμ : ∀ w, 0 < μ w) (hv : ∀ w, 0 < v w)
    (s : Finset Ω) (hs : s.Nonempty) :
    (∑ w ∈ s, μ w * Real.log (v w)) ≤ mass μ s * Real.log (avgOn μ s v) := by
  have hm := mass_pos hμ hs
  have ha : 0 < avgOn μ s v :=
    div_pos (sum_pos (fun w _ => mul_pos (hμ w) (hv w)) hs) hm
  have h (w : Ω) : μ w * (Real.log (v w) - Real.log (avgOn μ s v)) ≤
      μ w * (v w / avgOn μ s v - 1) := by
    rw [← Real.log_div (hv w).ne' ha.ne']
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos (hv w) ha)) (hμ w).le
  have ht := sum_le_sum (s:=s) (fun w _ => h w)
  simp only [mul_sub,mul_one,sum_sub_distrib, ← sum_mul] at ht
  have he : (∑ w ∈ s, μ w * (v w / avgOn μ s v)) = mass μ s := by
    simp_rw [← mul_div_assoc]
    rw [← sum_div, div_eq_iff ha.ne']
    dsimp only [avgOn]
    field_simp
  rw [he] at ht
  dsimp only [mass] at *
  linarith

theorem average_log_on_atoms [DecidableEq A] (μ : Ω → ℝ) (a : Ω → A) (f : Ω → ℝ)
    (hμ : ∀ w, 0 < μ w) (hf : ∀ w, 0 < f w) :
    expect μ (fun w => Real.log (f w)) ≤ expect μ (fun w => Real.log (avgOn μ (atom a w) f)) := by
  classical
  unfold expect
  rw [← sum_by_fiber a (fun w => μ w * Real.log (f w)),
    ← sum_by_fiber a (fun w => μ w * Real.log (avgOn μ (atom a w) f))]
  apply sum_le_sum
  intro x hx
  obtain ⟨v,_,rfl⟩ := mem_image.mp hx
  let s := fiber a (a v)
  have hs : s.Nonempty := ⟨v, mem_own_fiber a v⟩
  calc
    _ ≤ mass μ s * Real.log (avgOn μ s f) := weighted_log_sum hμ hf s hs
    _ = ∑ w ∈ s, μ w * Real.log (avgOn μ s f) := Finset.sum_mul ..
    _ = _ := Finset.sum_congr rfl fun w hw => by
      have he := (mem_filter.mp hw).2
      simp [atom,he,s]

/-- Information paid to reveal the next prefix when the cop has a current
target z. The right side is precisely H(z|old prefix)-H(z|new prefix). -/
theorem one_observation [DecidableEq A] [DecidableEq B] [DecidableEq Z]
    (μ : Ω → ℝ) (old : Ω → A) (new : Ω → B) (z : Ω → Z) (before after : Ω → ℝ)
    (hμ : ∀ w, 0 < μ w) (ha : ∀ w, 0 < after w)
    (move : ∀ w, avgOn μ (atom (fun u => (old u,z u)) w)
      (fun u => after u * condProb μ old z u / condProb μ new z u) ≤ before w) :
    expect μ (fun w => Real.log (after w)) - expect μ (fun w => Real.log (before w)) ≤
      condEntropy μ old z - condEntropy μ new z := by
  let ratio := fun u => after u * condProb μ old z u / condProb μ new z u
  have ho := condProb_pos μ hμ old z
  have hn := condProb_pos μ hμ new z
  have hr (w : Ω) : 0 < ratio w := div_pos (mul_pos (ha w) (ho w)) (hn w)
  have h := average_log_on_atoms μ (fun u => (old u,z u)) ratio hμ hr
  have h' : expect μ (fun w => Real.log (avgOn μ (atom (fun u => (old u,z u)) w) ratio)) ≤
      expect μ (fun w => Real.log (before w)) := by
    apply sum_le_sum
    intro w _
    apply mul_le_mul_of_nonneg_left _ (hμ w).le
    apply Real.log_le_log _ (move w)
    exact div_pos (sum_pos (fun u _ => mul_pos (hμ u) (hr u)) ⟨w,mem_own_fiber _ w⟩)
      (atom_mass_pos μ hμ _ _)
  have hh := h.trans h'
  have he w : Real.log (ratio w) =
      Real.log (after w) + Real.log (condProb μ old z w) - Real.log (condProb μ new z w) := by
    dsimp only [ratio]
    rw [Real.log_div (mul_pos (ha w) (ho w)).ne' (hn w).ne',
      Real.log_mul (ha w).ne' (ho w).ne']
  simp only [expect, he, mul_add,mul_sub,sum_add_distrib,sum_sub_distrib] at hh
  unfold condEntropy expect
  linarith

/-- Averaging over the next observation under the true prefix law dominates
the conditional transport used in the logarithmic inequality. Children that
cannot have the selected target contribute a nonnegative amount on the right. -/
theorem conditional_transport [DecidableEq A] [DecidableEq B] [DecidableEq Z]
    (μ : Ω → ℝ) (old : Ω → A) (new : Ω → B) (z : Ω → Z) (v : B → Z → ℝ)
    (hμ : ∀ w, 0 < μ w) (hv : ∀ b x, 0 ≤ v b x)
    (refines : ∀ u w, new u = new w → old u = old w) (w : Ω) :
    avgOn μ (atom (fun u => (old u,z u)) w)
      (fun u => v (new u) (z u) * condProb μ old z u / condProb μ new z u) ≤
    avgOn μ (atom old w) (fun u => v (new u) (z w)) := by
  classical
  let A₀ := atom old w
  let J := atom (fun u => (old u,z u)) w
  have hA : 0 < mass μ A₀ := atom_mass_pos μ hμ _ _ 
  have hJ : 0 < mass μ J := atom_mass_pos μ hμ _ _
  unfold avgOn
  change (∑ u ∈ J, _) / mass μ J ≤ (∑ u ∈ A₀, _) / mass μ A₀
  have hjmap : ∀ u ∈ J, new u ∈ univ.image new := fun u _ => mem_image_of_mem new (mem_univ u)
  have hamap : ∀ u ∈ A₀, new u ∈ univ.image new := fun u _ => mem_image_of_mem new (mem_univ u)
  rw [← Finset.sum_fiberwise_of_maps_to hjmap, ← Finset.sum_fiberwise_of_maps_to hamap,
    Finset.sum_div,Finset.sum_div]
  apply sum_le_sum
  intro y _
  let P := A₀.filter (fun u => new u = y)
  let Q := J.filter (fun u => new u = y)
  change (∑ u ∈ Q, _) / mass μ J ≤ (∑ u ∈ P, _) / mass μ A₀
  by_cases hQ : Q.Nonempty
  · obtain ⟨b,hb⟩ := hQ
    have hprop (u : Ω) (hu : u ∈ Q) : (old u = old w ∧ z u = z w) ∧ new u = y := by
      simpa [Q,J,atom,fiber] using hu
    have pb := hprop b hb
    have hOld (u : Ω) (hu : u ∈ Q) : condProb μ old z u = mass μ J / mass μ A₀ := by
      obtain ⟨⟨p,q⟩,_⟩ := hprop u hu
      simp [condProb,atom,J,A₀,p,q]
    have hNew (u : Ω) (hu : u ∈ Q) : condProb μ new z u = mass μ Q / mass μ P := by
      obtain ⟨⟨_,qx⟩,qy⟩ := hprop u hu
      have h1 : atom new u = P := by
        ext t
        simp only [atom,fiber,P,A₀,mem_filter,mem_univ,true_and,qy]
        exact ⟨fun h => ⟨(refines t b (h.trans pb.2.symm)).trans pb.1.1,h⟩, And.right⟩
      have h2 : atom (fun t => (new t,z t)) u = Q := by
        ext t
        simp only [atom,fiber,Q,J,mem_filter,mem_univ,true_and,Prod.mk.injEq,qy,qx]
        exact ⟨fun h => ⟨⟨(refines t b (h.1.trans pb.2.symm)).trans pb.1.1,h.2⟩,h.1⟩,
          fun h => ⟨h.2,h.1.2⟩⟩
      rw [condProb,h1,h2]
    have hmQ := mass_pos hμ ⟨b,hb⟩
    have hmP : 0 < mass μ P := by
      apply mass_pos hμ
      refine ⟨b,?_⟩
      simp [P,A₀,atom,fiber,pb.1.1,pb.2]
    have hl : (∑ u ∈ Q, μ u * (v (new u) (z u) * condProb μ old z u / condProb μ new z u)) =
        mass μ Q * (v y (z w) * (mass μ J / mass μ A₀) / (mass μ Q / mass μ P)) := by
      rw [mass,Finset.sum_mul]
      exact sum_congr rfl fun u hu => by rw [hOld u hu,hNew u hu,(hprop u hu).1.2,(hprop u hu).2]; rfl
    have hr : (∑ u ∈ P, μ u * v (new u) (z w)) = mass μ P * v y (z w) := by
      rw [mass,Finset.sum_mul]
      exact sum_congr rfl fun u hu => by rw [(mem_filter.mp hu).2]
    rw [hl,hr]
    apply le_of_eq; field_simp
  · rw [not_nonempty_iff_eq_empty.mp hQ,Finset.sum_empty,zero_div]
    exact div_nonneg (sum_nonneg fun u _ => mul_nonneg (hμ u).le (hv ..)) hA.le

theorem reveal_entropy [DecidableEq A] [DecidableEq B] [DecidableEq Z]
    (μ : Ω → ℝ) (old : Ω → A) (new : Ω → B) (z : Ω → Z) (v : B → Z → ℝ)
    (before : Ω → ℝ) (hμ : ∀ w, 0 < μ w) (hv : ∀ b x, 0 ≤ v b x)
    (hpos : ∀ w, 0 < v (new w) (z w)) (refines : ∀ u w, new u = new w → old u = old w)
    (move : ∀ w, avgOn μ (atom old w) (fun u => v (new u) (z w)) ≤ before w) :
    expect μ (fun w => Real.log (v (new w) (z w))) - expect μ (fun w => Real.log (before w)) ≤
      condEntropy μ old z - condEntropy μ new z :=
  one_observation μ old new z before _ hμ hpos
    (fun w => (conditional_transport μ old new z v hμ hv refines w).trans (move w))

theorem condProb_le_one [DecidableEq A] [DecidableEq Z] (μ : Ω → ℝ) (hμ : ∀ w, 0 < μ w)
    (a : Ω → A) (z : Ω → Z) (w : Ω) : condProb μ a z w ≤ 1 := by
  apply (div_le_one (atom_mass_pos μ hμ a w)).mpr
  apply sum_le_sum_of_subset_of_nonneg _ (fun u _ _ => (hμ u).le)
  intro u hu
  apply mem_filter.mpr
  exact ⟨mem_univ _, congrArg Prod.fst (mem_filter.mp hu).2⟩

theorem condEntropy_nonneg [DecidableEq A] [DecidableEq Z] (μ : Ω → ℝ) (hμ : ∀ w, 0 < μ w)
    (a : Ω → A) (z : Ω → Z) : 0 ≤ condEntropy μ a z := by
  apply neg_nonneg.mpr
  exact sum_nonpos (fun w _ => mul_nonpos_of_nonneg_of_nonpos (hμ w).le
    (Real.log_nonpos (condProb_pos μ hμ a z w).le (condProb_le_one μ hμ a z w)))

/-- The conditional support size bound, allowing a different bound after
each observed history. -/
theorem condEntropy_le_log_support [DecidableEq A] [DecidableEq Z] (μ : Ω → ℝ)
    (hμ : ∀ w, 0 < μ w) (a : Ω → A) (z : Ω → Z) (L : Ω → ℝ)
    (hsize : ∀ w, (((atom a w).image z).card : ℝ) ≤ L w) :
    condEntropy μ a z ≤ expect μ (fun w => Real.log (L w)) := by
  classical
  have hrec (w : Ω) : 0 < (condProb μ a z w)⁻¹ := inv_pos.mpr (condProb_pos μ hμ a z w)
  have hrecavg (w : Ω) :
      avgOn μ (atom a w) (fun u => (condProb μ a z u)⁻¹) = ((atom a w).image z).card := by
    let S := atom a w
    have hm := atom_mass_pos μ hμ a w
    have hgroup (x : Z) (hx : x ∈ S.image z) :
        (∑ u ∈ S.filter (fun u => z u = x), μ u * (condProb μ a z u)⁻¹) = mass μ S := by
      let B := S.filter (fun u => z u = x)
      obtain ⟨t,ht,he⟩ := mem_image.mp hx
      have hB : 0 < mass μ B := mass_pos hμ ⟨t,mem_filter.mpr ⟨ht,he⟩⟩
      have equal (u : Ω) (hu : u ∈ B) : condProb μ a z u = mass μ B / mass μ S := by
        have ha := (mem_filter.mp (mem_filter.mp hu).1).2
        have hz := (mem_filter.mp hu).2
        have hh : atom (fun v => (a v,z v)) u = B := by ext v; simp [atom,B,S,fiber,ha,hz]
        have h': atom a u = S := by simp [S,atom,ha]
        rw [condProb,hh,h']
      change (∑ u ∈ B, _) = _
      calc
        _ = ∑ u ∈ B, μ u * (mass μ B / mass μ S)⁻¹ :=
          sum_congr rfl (fun u hu => by rw [equal u hu])
        _ = _ := by rw [← sum_mul]; change mass μ B * _ = _; field_simp
    rw [avgOn,← Finset.sum_fiberwise_of_maps_to (fun u (hu : u ∈ S) => mem_image_of_mem z hu)]
    rw [sum_congr rfl hgroup]
    simp only [sum_const,nsmul_eq_mul]
    exact (mul_div_cancel_right₀ _ hm.ne')
  have h := average_log_on_atoms μ a (fun u => (condProb μ a z u)⁻¹) hμ hrec
  simp_rw [hrecavg,Real.log_inv] at h
  have hh : expect μ (fun w => -Real.log (condProb μ a z w)) = condEntropy μ a z := by
    simp [condEntropy,expect,Finset.sum_neg_distrib]
  rw [hh] at h
  apply h.trans
  apply sum_le_sum
  intro w _
  refine mul_le_mul_of_nonneg_left (Real.log_le_log ?_ (hsize w)) (hμ w).le
  exact_mod_cast (Finset.Nonempty.image (f:=z) ⟨w,mem_own_fiber a w⟩).card_pos

@[simp] theorem expect_const (μ : Ω → ℝ) (law : ∑ w, μ w = 1) (c : ℝ) :
    expect μ (fun _ => c) = c := by rw [expect,← sum_mul,law,one_mul]

theorem condEntropy_zero_of_constant [DecidableEq A] [DecidableEq Z]
    (μ : Ω → ℝ) (hμ : ∀ w, 0 < μ w) (a : Ω → A) (z : Ω → Z)
    (constant : ∀ u w, z u=z w) : condEntropy μ a z = 0 := by
  have h (w : Ω) : atom (fun u => (a u,z u)) w = atom a w := by
    ext u; simp [atom,fiber,constant u w]
  simp [condEntropy,expect,condProb,h,ne_of_gt (atom_mass_pos μ hμ a _)]

end
end Meyniel.Multiscale
