import Meyniel.MultiscaleRadii
import Meyniel.MultiscaleBounds

/-! # Uniform separation of the multiscale clocks and guard radii -/

noncomputable section
namespace Meyniel.Multiscale

open Filter

/-- An arbitrary fixed power of the logarithm fits in the positive margin. -/
theorem polylog_le_power {θ K : ℝ} (hθ : 0 < θ) (hK : 0 < K) (p : ℕ) :
    ∀ᶠ N : ℕ in atTop, K * Real.log (2*(N:ℝ))^p ≤ (N:ℝ)^θ := by
  let c : ℝ := 1/(K*2^p)
  have hc : 0 < c := by dsimp [c]; positivity
  have h := (isLittleO_log_rpow_rpow_atTop (p:ℝ) hθ).bound hc
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h, eventually_ge_atTop (2:ℕ)] with N hh hN
  have hx : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have h2 : Real.log (2*(N:ℝ)) ≤ 2*Real.log N := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    linarith [Real.log_le_log (by norm_num : (0:ℝ)<2) hx]
  change ‖Real.log N ^ (p:ℝ)‖ ≤ c * ‖(N:ℝ)^θ‖ at hh
  simp only [Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg hl p),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hh
  calc
    _ ≤ K*(2*Real.log N)^p := by gcongr; exact Real.log_nonneg (by linarith)
    _ = (K*2^p) * Real.log N ^ p := by rw [mul_pow]; ring
    _ ≤ (K*2^p) * (c * (N:ℝ)^θ) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by dsimp [c]; field_simp

private theorem packing_product {n a x y : ℝ} (hn : 1 ≤ n) (h : a+x ≤ y) :
    n^a * n^x ≤ n^y := by
  rw [← Real.rpow_add (by linarith : 0 < n)]
  exact Real.rpow_le_rpow_of_exponent_le hn h

/-- These four estimates hold at once for all levels, all selected radii and any
fixed logarithmic overhead. They include the gain needed in a restricted support. -/
structure ScaleSeparation (δ : ℝ) (N : ℕ) (F : ℝ) : Prop where
  bottom : ∀ i, 1 ≤ i → i ≤ levels δ → F ≤ (guardRadius δ N i : ℝ)
  support : ∀ i, 1 ≤ i → i ≤ levels δ → ∀ r ∈ radii δ N i,
    F*(guardRadius δ N i : ℝ)*(N:ℝ)^gain δ ≤ r
  adjacent : ∀ i, 1 ≤ i → i+1 ≤ levels δ → ∀ r ∈ radii δ N i,
    F*r ≤ (guardRadius δ N (i+1) : ℝ)
  top : ∀ i, 1 ≤ i → i ≤ levels δ → ∀ r ∈ radii δ N i,
    F*r ≤ (cutoff N δ : ℝ)

theorem scaleSeparation_eventually {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100)
    {K : ℝ} (hK : 0 < K) (p : ℕ) :
    ∀ᶠ N : ℕ in atTop, ScaleSeparation δ N (K*Real.log (2*(N:ℝ))^p) := by
  have hτ := margin_pos hδ
  have hΔ : 0 ≤ logGap δ := div_nonneg (by linarith) (Nat.cast_nonneg _)
  filter_upwards [polylog_le_power hτ (show 0 < 2*K by positivity) p, eventually_ge_atTop (1:ℕ)]
    with N hmargin hN
  let n : ℝ := N
  let F := K*Real.log (2*n)^p
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast hN
  have hnp : 0 < n := by linarith
  have hFp : 0 ≤ F := by dsimp [F]; apply mul_nonneg hK.le; apply pow_nonneg; exact Real.log_nonneg (by linarith)
  have hF2 : F * 2 ≤ n ^ margin δ := by dsimp [F,n]; linarith
  have hF : F ≤ n^margin δ := by linarith
  have stepGuard (i : ℕ) (hi : 1 ≤ i) : margin δ ≤ guardRadiusExp δ i := by
    have hi' : 1 ≤ (i:ℝ) := by exact_mod_cast hi
    unfold guardRadiusExp
    linarith [mul_nonneg (sub_nonneg.mpr hi') hΔ]
  have hs (i : ℕ) : n^guardRadiusExp δ i ≤ (guardRadius δ N i : ℝ) := Nat.le_ceil _
  have upper (i : ℕ) (hi : 1 ≤ i) : (guardRadius δ N i : ℝ) ≤ 2*n^guardRadiusExp δ i := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hnp.le (guardRadiusExp δ i))
    have h1 := Real.one_le_rpow hn (hτ.le.trans (stepGuard i hi))
    change (⌈n ^ guardRadiusExp δ i⌉₊ : ℝ) ≤ _
    linarith
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi _
    exact (hF.trans (Real.rpow_le_rpow_of_exponent_le hn (stepGuard i hi))).trans (hs i)
  · intro i hi hk r hr
    have hR := (radii_bounds hδ ht hN hi hk hr).1
    change F*(guardRadius δ N i:ℝ)*n^gain δ ≤ _
    calc
      _ ≤ (F*2)*(n^guardRadiusExp δ i)*n^gain δ := by
        rw [mul_assoc F 2]; gcongr; exact upper i hi
      _ ≤ (n^margin δ)*(n^guardRadiusExp δ i)*n^gain δ := by gcongr
      _ = n ^ minRadiusExp δ i := by
        rw [← Real.rpow_add hnp, ← Real.rpow_add hnp]
        congr 1; linarith [band_gain δ (i:ℝ)]
      _ ≤ _ := hR
  · intro i hi hk r hr
    have hR := (radii_bounds hδ ht hN hi (by omega) hr).2
    exact (mul_le_mul hF hR (Nat.cast_nonneg _) (Real.rpow_nonneg hnp.le _)).trans
      ((packing_product hn (by linarith [next_guard_exponent δ i])).trans (hs (i+1)))
  · intro i hi hk r hr
    have hR := (radii_bounds hδ ht hN hi hk hr).2
    have hh := (mul_le_mul_of_nonneg_right (show (i:ℝ) ≤ levels δ by exact_mod_cast hk) hΔ)
    have hkδ : (0:ℝ) < levels δ := by exact_mod_cast levels_pos hδ
    have he : (levels δ : ℝ)*logGap δ = 1/3-2*δ := by unfold logGap; field_simp [hkδ.ne']
    rw [he] at hh
    have hτδ : margin δ ≤ δ := by
      unfold margin; apply (div_le_iff₀ (by positivity)).mpr
      have hk1 : (1:ℝ) ≤ levels δ := by exact_mod_cast levels_pos hδ
      nlinarith only [mul_nonneg hδ.le (sub_nonneg.mpr hk1), hδ]
    have hx : margin δ + maxRadiusExp δ i ≤ 1/3-δ := by unfold maxRadiusExp; linarith
    exact (mul_le_mul hF hR (Nat.cast_nonneg _) (Real.rpow_nonneg hnp.le _)).trans
      ((packing_product hn hx).trans (Nat.le_ceil _))

end Meyniel.Multiscale
