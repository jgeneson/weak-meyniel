import Meyniel.Bounds

/-! # Balancing the two teams -/

namespace Meyniel

/-- A global logarithmic factor can be absorbed in any fixed positive power. -/
theorem log_two_mul_le {x e : ℝ} (hx : 1 ≤ x) (he : 0 < e) :
    Real.log (2*x) ≤ (1+1/e) * x ^ e := by
  have hxp : 0 < x := by linarith
  rw [Real.log_mul (by norm_num) hxp.ne']
  have ht : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have h1 := Real.one_le_rpow hx he.le
  have he' := Real.log_le_rpow_div hxp.le he
  rw [add_mul, one_mul, one_div_mul_eq_div]
  linarith

theorem diamThreshold_pos {N : ℕ} (hN : 1 ≤ N) : 0 < diamThreshold N := by
  have hn : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  apply Nat.ceil_pos.mpr
  exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.log_pos (by linarith))

/-- An explicit universal constant; the conservative rounding covers small graphs too. -/
theorem budget_add_guards_le {N : ℕ} (hN : 1 ≤ N) :
    ((budget N (horizon N (diamThreshold N)) + N / diamThreshold N : ℕ) : ℝ) ≤
      31 * (N:ℝ) ^ (3/4:ℝ) * Real.log (2*N) := by
  let x : ℝ := N
  let L := Real.log (2*x)
  let a := x ^ (1/4:ℝ)
  let b := x ^ (3/4:ℝ)
  let D := diamThreshold N
  let T := horizon N D
  have hx : 1 ≤ x := by change (1:ℝ) ≤ (N:ℝ); exact_mod_cast hN
  have hxp : 0 < x := by linarith
  have ha : 1 ≤ a := Real.one_le_rpow hx (by norm_num)
  have hb : 1 ≤ b := Real.one_le_rpow hx (by norm_num)
  have hL : (1/2:ℝ) ≤ L := by
    have h : Real.log 2 ≤ Real.log (2*x) := Real.log_le_log (by norm_num) (by linarith)
    dsimp [L]
    linarith [Real.log_two_gt_d9]
  have hLp : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog : Real.log x ≤ L := Real.log_le_log hxp (by linarith)
  have hla : L ≤ 5*a := by
    have h := log_two_mul_le (e := (1/4:ℝ)) hx (by norm_num)
    norm_num at h
    exact h
  have hDp : 0 < (D:ℝ) := by exact_mod_cast diamThreshold_pos hN
  have hlo : a ≤ D * L := (div_le_iff₀ hLp).mp (Nat.le_ceil _)
  have hhi : (D:ℝ)*L ≤ 6*a := by
    have he : (D:ℝ) < a/L+1 := Nat.ceil_lt_add_one (div_nonneg (by linarith) hLp.le)
    have hm := mul_lt_mul_of_pos_right he hLp
    rw [add_mul, div_mul_cancel₀ _ hLp.ne', one_mul] at hm
    linarith
  have h2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2pos : 0 < Real.log 2 := by linarith
  have htime : (T:ℝ)+1 ≤ 14*a := by
    have ht : (T:ℝ) < (D:ℝ)*Real.log x/Real.log 2 + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hDp.le hlog0) h2pos.le)
    have he : (D:ℝ)*Real.log x/Real.log 2 ≤ 12*a := by
      apply (div_le_iff₀ h2pos).mpr
      have h12 : 6*a ≤ (12*a)*Real.log 2 := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ a) (sub_nonneg.mpr h2)]
      exact ((mul_le_mul_of_nonneg_left hlog hDp.le).trans hhi).trans h12
    linarith
  have hsqrt : Real.sqrt (2*x) ≤ 2* Real.sqrt x := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg x)
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hprod : Real.sqrt x * a = b := by
    dsimp [a,b]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxp]
    norm_num
  have hab : b*a = x := by
    dsimp [a,b]
    rw [← Real.rpow_add hxp]
    norm_num
  have hbase : (1/2:ℝ) ≤ b*L := by nlinarith [mul_nonneg (sub_nonneg.mpr hb) hLp.le]
  have hteam : (budget N T : ℝ) ≤ 30*b*L := by
    have hfl : (budget N T : ℝ) ≤ Real.sqrt (2*x) * ((T:ℝ)+1) * Real.log x + 1 := by
      dsimp [budget]
      push_cast
      gcongr
      apply Nat.floor_le
      positivity
    have hupper := mul_le_mul hsqrt htime (by positivity : (0:ℝ) ≤ T+1)
      (by positivity : 0 ≤ 2 * Real.sqrt x)
    have hmore := mul_le_mul hupper hlog hlog0 (by positivity : 0 ≤ (2 * Real.sqrt x) * (14*a))
    have he : (2 * Real.sqrt x) * (14*a) = 28*b := by rw [← hprod]; ring
    rw [he] at hmore
    linarith
  have hguards : ((N / D : ℕ) : ℝ) ≤ b*L := by
    refine Nat.cast_div_le.trans ((div_le_iff₀ hDp).mpr ?_)
    have h := mul_le_mul_of_nonneg_left hlo (by linarith : 0 ≤ b)
    rw [hab] at h
    change x ≤ _
    linarith only [h, show b*((D:ℝ)*L) = b*L*D by ring]
  push_cast
  change (budget N T : ℝ) + ((N / D : ℕ) : ℝ) ≤ 31*b*L
  linarith

end Meyniel
