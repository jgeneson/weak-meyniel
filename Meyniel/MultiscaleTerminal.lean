import Meyniel.MultiscaleValues

/-! Weighted terminal comparison, including the conditional entropy of a
smoothed vertex given the entire true word. -/
namespace Meyniel.Multiscale
open Finset
noncomputable section

variable {Ω W A Z : Type*} [Fintype Ω] [DecidableEq W] [DecidableEq A] [DecidableEq Z]

theorem Mixture.success_nonneg {W S : Type*} (m : Mixture S) (hit : S → W → Prop)
    (w : W) : 0 ≤ m.success hit w := by
  classical
  apply sum_nonneg; intro i _
  apply mul_nonneg (m.law.1 i); split_ifs <;> norm_num

/-- A terminal mixture at each observed history/vertex, positive on correct
latent targets, pays H(Z|history)-H(Z|word) to pass to the whole-word law. -/
theorem terminal_entropy {P : Z → Type*} [∀ x, Nonempty (P x)]
    (μ : Ω → ℝ) (hμ : ∀ i, 0 < μ i) (word : Ω → W) (history : W → A)
    (z : Ω → Z) (weight cost : W → ℝ) (hw : ∀ w, 0 < weight w)
    (hit : (x : Z) → P x → W → Prop)
    (trial : (h : A) → (x : Z) → Mixture (P x))
    (hh : ∀ i, Real.exp (-cost (word i)) ≤
      (trial (history (word i)) (z i)).success (hit (z i)) (word i)) :
    let old := fun i => history (word i)
    let before := fun i => value μ (fun j => weight (word j)) (atom old i)
      (fun s j => hit (z i) s (word j))
    (∀ i, 0 < before i) ∧
    expect μ (fun i => Real.log (weight (word i)) - cost (word i)) -
      condEntropy μ old z + condEntropy μ word z ≤ expect μ (fun i => Real.log (before i)) := by
  classical
  let old := fun i => history (word i)
  let before := fun i => value μ (fun j => weight (word j)) (atom old i)
    (fun s j => hit (z i) s (word j))
  let v := fun w x => weight w * (trial (history w) x).success (hit x) w
  have hsuccess i : 0 < (trial (old i) (z i)).success (hit (z i)) (word i) :=
    (Real.exp_pos _).trans_le (hh i)
  have refines (u i : Ω) (eqn : word u=word i) : old u=old i := congrArg history eqn
  have move (i : Ω) : avgOn μ (atom old i) (fun j => v (word j) (z i)) ≤ before i := by
    have he : avgOn μ (atom old i) (fun j => v (word j) (z i)) =
        avgOn μ (atom old i) (fun j => weight (word j) *
          (trial (old i) (z i)).success (fun s j => hit (z i) s (word j)) j) := by
      unfold avgOn; congr 1; apply sum_congr rfl; intro j hj
      have hj' : old j=old i := (mem_filter.mp hj).2
      change μ j * (weight (word j) * (trial (old j) (z i)).success _ _) = _
      rw [hj']
      rfl
    rw [he]
    exact mixture_gain_le_value .. 
  have hinfo := reveal_entropy μ old word z v before hμ
    (fun w x => mul_nonneg (hw w).le (Mixture.success_nonneg ..))
    (fun i => mul_pos (hw _) (hsuccess i)) refines move
  have hle : expect μ (fun i => Real.log (weight (word i))- cost (word i)) ≤
      expect μ (fun i => Real.log (v (word i) (z i))) := by
    apply sum_le_sum; intro i _
    apply mul_le_mul_of_nonneg_left _ (hμ i).le
    dsimp only [v]
    rw [Real.log_mul (hw _).ne' (hsuccess i).ne']
    linarith [Real.log_le_log (Real.exp_pos _) (hh i), Real.log_exp (-cost (word i))]
  refine ⟨?_,by linarith⟩
  intro i
  obtain ⟨k,hk⟩ := Mixture.exists_hit_of_success_pos (trial (old i) (z i)) (hit (z i)) (word i) (hsuccess i)
  exact value_pos_of_possible μ _ _ _ hμ (fun j => hw _) (Interception.mem_own_fiber old i) hk

end
end Meyniel.Multiscale
