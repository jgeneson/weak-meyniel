module

public import Meyniel.MultiscaleWindow
public import Meyniel.MultiscaleTerminal
public import Meyniel.MultiscalePrices

/-! Mixing a correct-terminal strategy over the chosen radius and over the
ordinary and band-restricted families. These choices take place before the
terminal endpoint is known. -/

@[expose] public section

namespace Meyniel.Multiscale
open Finset Interception
noncomputable section

def Mixture.map' {S T : Type*} (m : Mixture S) (f : S → T) : Mixture T :=
  ⟨m.size, f ∘ m.strategy, m.prob, m.law⟩

theorem Mixture.map_success_le {W S T : Type*} (m : Mixture S) (f : S → T)
    (h : S → W → Prop) (h' : T → W → Prop) (w : W) (write : ∀ s, h s w → h' (f s) w) :
    m.success h w ≤ (m.map' f).success h' w := by
  classical
  unfold Mixture.success
  apply sum_le_sum
  intro i _
  dsimp [Mixture.map']
  by_cases hyp : h (m.strategy i) w
  · simp [hyp,write _ hyp]
  · by_cases newHit : h' (f (m.strategy i)) w <;> simp [hyp,newHit,m.law.1 i]

def Mixture.combine {J S : Type*} [Fintype J] (ν : J → ℝ) (law : ν ∈ stdSimplex ℝ J)
    (m : J → Mixture S) : Mixture S := by
  classical
  let A := (j : J) × Fin (m j).size
  let prob := fun a : A => ν a.1 * (m a.1).prob a.2
  let e := (Fintype.equivFin A).symm
  refine ⟨Fintype.card A,fun i => (m (e i).1).strategy (e i).2,prob ∘ e,?_⟩
  constructor
  · intro i; exact mul_nonneg (law.1 _) ((m _).law.1 _)
  · rw [show (∑ i, (prob ∘ e) i) = ∑ a, prob a from Equiv.sum_comp e prob]
    simp only [A,prob,Fintype.sum_sigma, ←mul_sum]
    simpa only [fun j => (m j).law.2,mul_one] using law.2

theorem Mixture.combine_success {J S W : Type*} [Fintype J] (ν : J → ℝ) (law : ν ∈ stdSimplex ℝ J)
    (m : J → Mixture S) (hit : S → W → Prop) (w : W) :
    (Mixture.combine ν law m).success hit w = ∑ j, ν j * (m j).success hit w := by
  classical
  let A := (j : J) × Fin (m j).size
  let f (a : A) : ℝ := (ν a.1*(m a.1).prob a.2)*(if hit ((m a.1).strategy a.2) w then 1 else 0)
  let e := (Fintype.equivFin A).symm
  change (∑ i, f (e i)) = _
  rw [Equiv.sum_comp e f]
  simp [A,f,Fintype.sum_sigma,Mixture.success, mul_sum]

def uniformProb (J : Type*) [Fintype J] (_ : J) : ℝ := (Fintype.card J : ℝ)⁻¹

theorem uniformLaw (J : Type*) [Fintype J] [Nonempty J] : uniformProb J ∈ stdSimplex ℝ J := by
  classical
  have hn : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact ⟨fun _ => by unfold uniformProb; positivity, by simp [uniformProb,hn]⟩

theorem combine_log_cost {J S W : Type*} [Fintype J] [Nonempty J]
    (m : J → Mixture S) (hit : S → W → Prop) (cost : J → W → ℝ)
    (h : ∀ j w, Real.exp (-cost j w) ≤ (m j).success hit w) (w : W) :
    Real.exp (-mean univ (fun j => cost j w)) ≤
      (Mixture.combine (uniformProb J) (uniformLaw J) m).success hit w := by
  classical
  let ν := uniformProb J
  have law := uniformLaw J
  have eq : -mean univ (fun j => cost j w) = ∑ j, ν j * (-cost j w) := by
    simp [mean,ν,uniformProb,div_eq_inv_mul,mul_sum]
  rw [eq,Mixture.combine_success]
  calc
    _ ≤ ∑ j, ν j * Real.exp (-cost j w) := by
      have hh := logMean_le_log_mean (fun j => Real.exp_pos (-cost j w))
      have hp := mean_pos (s:=univ) univ_nonempty (fun j _ => Real.exp_pos (-cost j w))
      have he := Real.exp_le_exp.mpr hh
      rw [Real.exp_log hp] at he
      simpa [logMean,mean,ν,uniformProb,div_eq_inv_mul,mul_sum] using he
    _ ≤ _ := sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j w) (law.1 _))

/-- The fair coin works when an endpoint's good/bad status is learned only
after the strategy is chosen. The restricted family may be empty. -/
theorem combine_good {S W : Type*} (hit : S → W → Prop) (cost : W → ℝ)
    (good : W → Prop) [DecidablePred good] (saving : ℝ) (ordinary : Mixture S)
    (ho : ∀ w, Real.exp (-cost w) ≤ ordinary.success hit w)
    (restricted : Nonempty {w // good w} → ∃ m : Mixture S, ∀ w, good w →
      Real.exp (-(cost w-saving)) ≤ m.success hit w) :
    ∃ m : Mixture S, ∀ w, Real.exp (-(cost w - (if good w then saving else 0) + Real.log 2)) ≤
      m.success hit w := by
  classical
  by_cases has : Nonempty {w // good w}
  · obtain ⟨m,hm⟩ := restricted has
    let choices : Bool → Mixture S := fun i => if i then m else ordinary
    refine ⟨Mixture.combine (uniformProb Bool) (uniformLaw Bool) choices,?_⟩
    intro w
    rw [Mixture.combine_success]
    simp only [Fintype.sum_bool,uniformProb,Fintype.card_bool,Nat.cast_ofNat,choices,Bool.false_eq_true,↓reduceIte]
    have h0 := ordinary.success_nonneg hit w
    have h1 := m.success_nonneg hit w
    by_cases hw : good w
    · simp only [if_pos hw,neg_add_rev,Real.exp_add,Real.exp_neg (Real.log 2),Real.exp_log (by norm_num : (0:ℝ)<2)]
      linarith [hm w hw]
    · simp only [if_neg hw,sub_zero,neg_add_rev,Real.exp_add,Real.exp_neg (Real.log 2),Real.exp_log (by norm_num : (0:ℝ)<2)]
      linarith [ho w]
  · refine ⟨ordinary,fun w => ?_⟩
    have ng : ¬ good w := fun h => has ⟨⟨w,h⟩⟩
    simp only [if_neg ng,sub_zero]
    exact (Real.exp_le_exp.mpr (by linarith [Real.log_nonneg (by norm_num : (1:ℝ)≤2)])).trans (ho w)

end
end Meyniel.Multiscale
