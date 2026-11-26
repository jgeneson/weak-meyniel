module

public import Meyniel.MultiscaleEntropy
public import Meyniel.MultiscaleWindow

/-! Conditional values for a weighted finite family. All maximizations are
over actual deterministic strategies, even when their history domain is infinite. -/

@[expose] public section

namespace Meyniel.Multiscale
open Finset Interception
noncomputable section

variable {Ω S A B : Type*} [Fintype Ω]

def captureGain (μ weight : Ω → ℝ) (D : Finset Ω) (hit : S → Ω → Prop) (s : S) : ℝ := by
  classical exact avgOn μ D (fun w => if hit s w then weight w else 0)

/-- A best deterministic response exists by finiteness of capture patterns. -/
theorem exists_optimal [Nonempty S] (μ weight : Ω → ℝ) (D : Finset Ω) (hit : S → Ω → Prop) :
    ∃ s : S, ∀ s', captureGain μ weight D hit s' ≤ captureGain μ weight D hit s := by
  classical
  let pat := fun s : S => univ.filter (hit s)
  let score := fun a : Finset Ω => avgOn μ D (fun w => if w ∈ a then weight w else 0)
  have he (s : S) : score (pat s) = captureGain μ weight D hit s := by simp [score,pat,captureGain]
  let P := Finset.univ.filter (fun a : Finset Ω => ∃ s, pat s = a)
  have hP : P.Nonempty := ⟨pat (Classical.arbitrary S), by simp [P]⟩
  obtain ⟨a,ha,hmax⟩ := exists_max_image P score hP
  obtain ⟨s,rfl⟩ := (mem_filter.mp ha).2
  exact ⟨s,fun s' => (he s').symm ▸ (he s).symm ▸ hmax (pat s') (by simp [P])⟩

def optimal [Nonempty S] (μ weight : Ω → ℝ) (D : Finset Ω) (hit : S → Ω → Prop) : S :=
  (exists_optimal μ weight D hit).choose

def value [Nonempty S] (μ weight : Ω → ℝ) (D : Finset Ω) (hit : S → Ω → Prop) : ℝ :=
  captureGain μ weight D hit (optimal μ weight D hit)

theorem gain_le_value [Nonempty S] (μ weight : Ω → ℝ) (D : Finset Ω) (hit : S → Ω → Prop) (s : S) :
    captureGain μ weight D hit s ≤ value μ weight D hit :=
  (exists_optimal μ weight D hit).choose_spec s

theorem value_nonneg [Nonempty S] (μ weight : Ω → ℝ) (D : Finset Ω) (hit : S → Ω → Prop)
    (hμ : ∀ w, 0 ≤ μ w) (hw : ∀ w, 0 ≤ weight w) : 0 ≤ value μ weight D hit := by
  classical
  unfold value captureGain avgOn mass
  exact div_nonneg (sum_nonneg (fun w _ => mul_nonneg (hμ w) (by dsimp only; split_ifs <;> simp [hw]))) (sum_nonneg fun w _ => hμ w)

/-- The conditional expectation of best continuations, after partitioning the
current prefix by the next reveal, can be captured by one policy whenever those
continuations may be chosen contingent on the revealed prefix. -/
theorem value_splice [DecidableEq A] [DecidableEq B] {P Q : Type*} [Nonempty P] [Nonempty Q]
    (μ weight : Ω → ℝ) (old : Ω → A) (new : Ω → B) (cur : Ω)
    (hμ : ∀ w, 0 < μ w) (hw : ∀ w, 0 ≤ weight w)
    (refines : ∀ u v, new u = new v → old u = old v)
    (before : P → Ω → Prop) (after : Q → Ω → Prop)
    (splice : ∀ f : B → Q, ∃ s : P, ∀ w, old w=old cur → after (f (new w)) w → before s w) :
    avgOn μ (atom old cur) (fun w => value μ weight (atom new w) after) ≤
    value μ weight (atom old cur) before := by
  classical
  let A₀ := atom old cur
  let pick (b : B) := optimal μ weight (fiber new b) after
  obtain ⟨p,hp⟩ := splice pick
  apply le_trans _ (gain_le_value μ weight A₀ before p)
  have hm := atom_mass_pos μ hμ old cur
  unfold captureGain avgOn
  apply div_le_div_of_nonneg_right _ hm.le
  have hmap : ∀ w ∈ A₀, new w ∈ A₀.image new := fun w h => mem_image_of_mem new h
  rw [← sum_fiberwise_of_maps_to hmap,← sum_fiberwise_of_maps_to hmap (f := fun w => μ w * (if before p w then weight w else 0))]
  apply sum_le_sum; intro b hb
  obtain ⟨w,hwA,rfl⟩ := mem_image.mp hb
  let C := fiber new (new w)
  have he : A₀.filter (fun u => new u = new w) = C := by
    ext u
    simp only [A₀,C,atom,fiber,mem_filter,mem_univ,true_and]
    exact ⟨And.right,fun h => ⟨(refines u w h).trans (mem_filter.mp hwA).2,h⟩⟩
  rw [he]
  have equal (u : Ω) (hu : u ∈ C) : atom new u = C := by
    simp [C,atom,(mem_filter.mp hu).2]
  have hC : 0 < mass μ C := mass_pos hμ ⟨w, mem_own_fiber new w⟩
  calc
    _ = ∑ u ∈ C, μ u * value μ weight C after := sum_congr rfl (fun u hu => by dsimp only; rw [equal u hu])
    _ = ∑ u ∈ C, μ u * (if after (pick (new w)) u then weight u else 0) := by
      rw [← sum_mul]
      change mass μ C * (_/mass μ C) = _
      field_simp; rfl
    _ ≤ _ := by
      apply sum_le_sum; intro u hu
      apply mul_le_mul_of_nonneg_left _ (hμ u).le
      have hn := (mem_filter.mp hu).2
      have hold : old u = old cur := (refines u w hn).trans (mem_filter.mp hwA).2
      by_cases e : after (pick (new w)) u
      · rw [if_pos e,if_pos (hp u hold (hn ▸ e))]
      · rw [if_neg e]; split_ifs <;> simp [hw]

/-- A randomized continuation has conditional payoff at most that of the
best deterministic continuation at its present vertex. -/
theorem mixture_gain_le_value [Nonempty S] (μ weight : Ω → ℝ) (D : Finset Ω)
    (hit : S → Ω → Prop) (m : Mixture S) :
    avgOn μ D (fun u => weight u * m.success hit u) ≤ value μ weight D hit := by
  classical
  have he : avgOn μ D (fun u => weight u * m.success hit u) =
      ∑ i, m.prob i * captureGain μ weight D hit (m.strategy i) := by
    unfold avgOn Mixture.success captureGain
    simp only [avgOn,mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro i _
    rw [← mul_div_assoc,Finset.mul_sum]
    congr 1
    apply sum_congr rfl
    intro u _
    split_ifs <;> ring
  rw [he]
  calc
    _ ≤ ∑ i, m.prob i * value μ weight D hit :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (gain_le_value ..) (m.law.1 i)
    _ = _ := by rw [← sum_mul,m.law.2,one_mul]

theorem value_pos_of_possible [Nonempty S] (μ weight : Ω → ℝ) (D : Finset Ω)
    (hit : S → Ω → Prop) (hμ : ∀ w, 0 < μ w) (hw : ∀ w, 0 < weight w)
    {w : Ω} (hwD : w ∈ D) {s : S} (hs : hit s w) : 0 < value μ weight D hit := by
  classical
  apply lt_of_lt_of_le _ (gain_le_value μ weight D hit s)
  apply div_pos _ (mass_pos hμ ⟨w,hwD⟩)
  apply sum_pos'
  · intro u _
    apply mul_nonneg (hμ u).le; dsimp only; split_ifs <;> simp [(hw u).le]
  · exact ⟨w,hwD,by dsimp only; rw [if_pos hs]; exact mul_pos (hμ _) (hw _)⟩

theorem Mixture.exists_hit_of_success_pos {W S : Type*} (m : Mixture S) (hit : S → W → Prop)
    (w : W) (h : 0 < m.success hit w) : ∃ i, hit (m.strategy i) w := by
  classical
  by_contra! hh
  simp [Mixture.success,hh] at h

/-- Relabelling or adjoining independent finite noise has no effect on the
window's optimal value when the cop scores only on the true word. -/
theorem value_pushforward {Q : Type*} [Fintype Q] [Nonempty S]
    (μ : Ω → ℝ) (ν : Q → ℝ) (map : Ω → Q) (weight : Q → ℝ) (hit : S → Q → Prop)
    (preserve : ∀ f : Q → ℝ, expect μ (fun i => f (map i)) = expect ν f) :
    value μ (fun i => weight (map i)) univ (fun s i => hit s (map i)) =
    value ν weight univ hit := by
  classical
  have hm : mass μ univ = mass ν univ := by simpa [mass,expect] using preserve (fun _=>1)
  have he (s : S) : captureGain μ (fun i => weight (map i)) univ (fun s i => hit s (map i)) s =
      captureGain ν weight univ hit s := by
    unfold captureGain avgOn
    rw [hm]
    exact congrArg (fun x => x/mass ν univ) (preserve (fun j => if hit s j then weight j else 0))
  apply le_antisymm
  · unfold value; rw [he]; exact gain_le_value ..
  · change _ ≤ captureGain μ _ _ _ _
    rw [he]
    let best := optimal ν weight univ hit
    have e := gain_le_value μ (fun i => weight (map i)) univ (fun s i => hit s (map i)) best
    rw [he] at e
    exact e.trans_eq (he _)

theorem expect_support {Q : Type*} [Fintype Q] (p : Q → ℝ) (hp : ∀ j, 0 ≤ p j) (f : Q → ℝ) :
    expect (fun q : {j // 0 < p j} => p q.val) (fun q => f q.val) = expect p f := by
  classical
  unfold expect
  rw [← Finset.sum_subtype (s:=univ.filter fun j : Q => 0 < p j) (p:=fun j : Q => 0 < p j)
    (by simp) (f:=fun j => p j*f j),Finset.sum_filter]
  apply sum_congr rfl; intro j _
  split_ifs with hs
  · rfl
  · simp [(hp j).antisymm' (le_of_not_gt hs)]

end
end Meyniel.Multiscale
