module

public import Meyniel.MultiscaleRootPrice

@[expose] public section

namespace Meyniel.Multiscale
open Filter Finset Interception
noncomputable section

/-- An order threshold, uniform over all windows, absorbs the fixed price of
the home columns, the radii count, and the terminal coins. -/
theorem root_loss {δ c : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ i T : ℕ, i ≤ levels δ → 0<T →
      2+((9*(i:ℝ)+1)/clockFactor δ)*Real.log N+(i:ℝ)*Real.log 2 +
        (4/(T:ℝ))*((T+1:ℕ):ℝ)*((i:ℝ)*(Real.log N/(c*Real.log N))+
          (100/δ)*(gain δ*Real.log N/2)) ≤ δ/20*Real.log N := by
  let L : ℝ := 2+(levels δ:ℝ)*Real.log 2+8*(levels δ:ℝ)/c
  have htend := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop (L/(δ/50)),eventually_ge_atTop 2] with N hlog hn i T hi hT
  change L/(δ/50) ≤ Real.log N at hlog
  have hL := (div_le_iff₀ (by positivity : 0<δ/50)).mp hlog
  have hn' : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hl := Real.log_pos hn'
  have tpos : (0:ℝ)<T := by exact_mod_cast hT
  have t1 : (1:ℝ)≤T := by exact_mod_cast hT
  have hi' : (i:ℝ)≤levels δ := by exact_mod_cast hi
  have hc' : (0:ℝ)<clockFactor δ := lt_of_lt_of_le (by positivity) (Nat.le_ceil (100000*((levels δ:ℝ)+1)/δ))
  have mult : 4/(T:ℝ)*((T+1:ℕ):ℝ) ≤ 8 := by
    push_cast; rw [div_mul_eq_mul_div,(div_le_iff₀ tpos)]; linarith
  have simpL : Real.log N/(c*Real.log N)=1/c := by field_simp
  rw [simpL]
  have g := (gain_pos hδ ht).le
  have rel : (0:ℝ) ≤ (i:ℝ)*(1/c)+(100/δ)*(gain δ*Real.log N/2) := by positivity
  have hcap : 8 * ((100/δ)*(gain δ*Real.log N/2)) = 4*gain δ/(δ/100)*Real.log N := by field_simp; ring
  have hmul := mul_le_mul_of_nonneg_right mult rel
  rw [mul_add (8:ℝ),hcap] at hmul
  have hprice := mul_le_mul_of_nonneg_right (loss_budget hδ ht).le hl.le
  have hcoef : (9*(i:ℝ)+1)/clockFactor δ ≤ (9*(levels δ:ℝ)+1)/clockFactor δ := by gcongr
  have hcoins := mul_le_mul_of_nonneg_right hi' (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  have hrad := mul_le_mul_of_nonneg_right hi' (inv_nonneg.mpr hc.le)
  dsimp [L] at hL
  rw [add_mul] at hprice
  rw [one_div] at hmul
  rw [div_eq_mul_inv] at hL
  rw [one_div]
  nlinarith only [hL,hmul,hprice,hcoins,hrad,mul_pos hδ hl,mul_le_mul_of_nonneg_right hcoef hl.le]

end
end Meyniel.Multiscale
