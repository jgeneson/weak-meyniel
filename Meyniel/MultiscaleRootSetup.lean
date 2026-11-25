import Meyniel.TrialStepDefs
import Meyniel.MultiscaleRootLoss

namespace Meyniel.Multiscale
open Filter Finset Interception
noncomputable section

theorem trial_facts_eventually {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) :
    ∀ᶠ N : ℕ in atTop, TrialFacts δ N := by
  obtain ⟨c,hc,many⟩ := many_radii hδ ht
  let K : ℝ := 12*(2*(clockFactor δ:ℝ)+3)
  have hK : 0 < K := by dsimp [K]; positivity
  filter_upwards [many,timingFacts_eventually hδ ht,scaleSeparation_eventually hδ ht hK 0,
    scaleSeparation_eventually hδ ht (K:=1) (by norm_num) 0,eventually_ge_atTop 2] with N hm tf sep sep' hN
  simp only [pow_zero,mul_one] at sep sep'
  have hn : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hH := Real.one_le_rpow hn.le (gain_pos hδ ht).le
  refine ⟨Nat.ceil_pos.mpr (by positivity),by omega,(gain_pos hδ ht).le,?_,tf,?_⟩
  · intro i hi hk; exact card_pos.mp (by exact_mod_cast (mul_pos hc (Real.log_pos hn)).trans_le (hm i hi hk))
  · intro i hi hk p hp r hr
    have hh := sep.adjacent i hi hk r hr
    have hs := sep'.support (i+1) (by omega) hk p hp
    rw [one_mul] at hs
    have cmp := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg (α:=ℝ) (guardRadius δ N (i+1)))
    simp only [mul_one] at cmp
    have le := cmp.trans hs
    apply Nat.cast_le (α:=ℝ) |>.mp
    calc
      _ = K*r := by dsimp [K,leadTime,duration]; push_cast; ring
      _ ≤ _ := hh.trans le

theorem root_setup_cost {N C M J D A vol : ℕ}
    (hN : 0<N) (hC : 0<C) (hM : 0<M) (hMJ : M≤J) (hA : 0<A) (hAV : A≤vol) (hAN : A≤N)
    (coeff : (M:ℝ)/(J:ℝ) ≤ 1/2+1/(C:ℝ)) (home : (D:ℝ)*Real.log N/M≤2) :
    ((M:ℝ)*Real.log A+D*Real.log N)/(J:ℝ) ≤ Real.log vol/2+Real.log N/C+2 := by
  have ha : (0:ℝ)<A := by exact_mod_cast hA
  have hapos : 0≤Real.log (A:ℝ) := Real.log_nonneg (by exact_mod_cast hA)
  have hv := Real.log_le_log ha (by exact_mod_cast hAV : (A:ℝ)≤vol)
  have hn := Real.log_le_log ha (by exact_mod_cast hAN : (A:ℝ)≤N)
  have hM' : (0:ℝ)<M := by exact_mod_cast hM
  have hJ : (0:ℝ)<J := by exact_mod_cast Nat.lt_of_lt_of_le hM hMJ
  have hdiv : (D:ℝ)*Real.log N/J ≤ 2 :=
    (div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hN)))
      hM' (by exact_mod_cast hMJ)).trans home
  have hlog := mul_le_mul_of_nonneg_right coeff hapos
  have h2 := div_le_div_of_nonneg_right hn (Nat.cast_nonneg C)
  rw [add_div,show (M:ℝ)*Real.log A/J = (M/J)*Real.log A by ring]
  rw [add_mul] at hlog
  rw [show 1/(C:ℝ)*Real.log A=Real.log A/C by ring] at hlog
  linarith

end
end Meyniel.Multiscale
