import Meyniel.Guard
import Meyniel.Optimize

/-! # Counting cops in the multiscale argument

The diameter recurrence is uniform in the graph and additive at each halving.
The final theorem of this module records precisely what that recurrence implies.
-/

namespace Meyniel.Multiscale

universe u

/-- A single team-size bound for all graphs subject to the two caps. -/
def BoundedWins (N d k : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] (H : SimpleGraph W), H.Connected →
    Fintype.card W ≤ N → H.diam ≤ d → WinsWith H k

/-- Cost of one diameter-halving stage in the game. -/
def DiameterStep (N Q A : ℕ) : Prop :=
  ∀ d, 2 ≤ d → d ≤ Q → ∀ k, BoundedWins.{u} N ((d+1)/2) k → BoundedWins.{u} N d (k+A)

noncomputable def cutoff (N : ℕ) (δ : ℝ) : ℕ := ⌈(N : ℝ) ^ (1/3 - δ)⌉₊

theorem diameter_one (N : ℕ) : BoundedWins.{u} N 1 1 := by
  intro W _ G conn _ hd
  letI : Nonempty W := conn.nonempty
  let x : W := Classical.choice conn.nonempty
  refine ⟨fun _ => x, fun r => ⟨1, Or.inr ⟨fun _ => r, fun _ => ?_, Or.inl ⟨0,rfl⟩⟩⟩⟩
  have hr := (SimpleGraph.dist_le_diam (G.connected_iff_ediam_ne_top.mp conn) (u:=x) (v:=r)).trans hd
  by_cases he : G.dist x r = 0
  · exact Or.inl (conn.dist_eq_zero_iff.mp he)
  · have hdist : G.dist x r = 1 := by omega
    exact Or.inr (SimpleGraph.dist_eq_one_iff_adj.mp hdist)

/-- The ceiling-logarithm counts all recursively needed diameter reductions. -/
theorem iterate_diameter_step {N Q A : ℕ} (step : DiameterStep.{u} N Q A) :
    ∀ d ≤ Q, BoundedWins.{u} N d (1 + Nat.clog 2 d * A) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    by_cases hsmall : d ≤ 1
    · rw [Nat.clog_of_right_le_one hsmall, zero_mul, add_zero]
      exact fun W _ G conn hn hdiam => diameter_one N W G conn hn (hdiam.trans hsmall)
    have htwo : 2 ≤ d := by omega
    let m := (d+1)/2
    have hlt : m < d := by dsimp [m]; omega
    have smaller :=  ih m hlt (hlt.le.trans hd)
    have hclog : Nat.clog 2 d = Nat.clog 2 m + 1 := by
      rw [Nat.clog_of_two_le (by decide : 1 < 2) htwo]
      rfl
    rw [hclog, Nat.add_mul, Nat.one_mul, ← Nat.add_assoc]
    exact step d htwo hd _ smaller

theorem wins_of_diameter_step {V : Type u} [Fintype V] (G : SimpleGraph V) (conn : G.Connected)
    {N Q A : ℕ} (hsize : Fintype.card V ≤ N) (hQ : 0 < Q) (step : DiameterStep.{u} N Q A) :
    WinsWith G (1 + Nat.clog 2 Q * A + Fintype.card V / Q) :=
  Guard.diameter_reduction conn hsize hQ (iterate_diameter_step step Q le_rfl)

private theorem cutoff_pos {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) : 0 < cutoff n δ := by
  apply Nat.ceil_pos.mpr
  apply Real.rpow_pos_of_pos
  exact_mod_cast (show 0 < n by omega)

private theorem cutoff_le {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ) : cutoff n δ ≤ n := by
  apply Nat.ceil_le.mpr
  have hx : (1:ℝ) ≤ n := by exact_mod_cast hn
  simpa using Real.rpow_le_rpow_of_exponent_le hx (show 1/3-δ ≤ (1:ℝ) by linarith)

private theorem quotient_le {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) :
    ((n / cutoff n δ : ℕ) : ℝ) ≤ (n : ℝ) ^ (2/3+δ) := by
  have hx : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hc : 0 < (cutoff n δ : ℝ) := by exact_mod_cast cutoff_pos hn δ
  have lower : (n : ℝ) ^ (1/3-δ) ≤ (cutoff n δ : ℝ) := Nat.le_ceil _
  apply Nat.cast_div_le.trans ((div_le_iff₀ hc).mpr ?_)
  calc
    (n : ℝ) = (n : ℝ)^(2/3+δ) * (n : ℝ)^(1/3-δ) := by
      rw [← Real.rpow_add hx]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left lower (Real.rpow_nonneg hx.le _)

private theorem clog_le {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (hθ : 0 < θ) :
    (Nat.clog 2 n : ℝ) ≤ (1+1/(θ * Real.log 2)) * (n:ℝ)^θ := by
  have hx : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh : 0 ≤ Real.logb 2 n := div_nonneg (Real.log_nonneg hx) hl.le
  rw [← Real.natCeil_logb_natCast]
  have hceil := Nat.ceil_lt_add_one hh
  have hs := Real.log_le_rpow_div (zero_le_one.trans hx) hθ
  have hpow := Real.one_le_rpow hx hθ.le
  calc
    _ ≤ Real.logb 2 n + 1 := hceil.le
    _ ≤ ((n:ℝ)^θ / θ) / Real.log 2 + (n:ℝ)^θ :=
      add_le_add (div_le_div_of_nonneg_right hs hl.le) hpow
    _ = _ := by ring

/-- From the cost of the multiscale deployment to the claimed upper bound.
The constants and the threshold may depend on the fixed exponent slack. -/
theorem two_thirds_of_step
    (input : ∀ δ : ℝ, 0 < δ → δ < 1/100 → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∃ A : ℕ, (A : ℝ) ≤ C * (N:ℝ)^(2/3+δ/4) ∧
        DiameterStep.{u} N (cutoff N δ) A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ C * (Fintype.card V : ℝ) ^ (2/3+ε) := by
  let δ := min (ε/2) (1/200)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hsmall : δ < 1/100 := lt_of_le_of_lt (min_le_right ..) (by norm_num)
  have hδe : δ ≤ ε/2 := min_le_left .. 
  obtain ⟨C,hC,N₀,h⟩ := input δ hδ hsmall
  let B := 1+1/(δ * Real.log 2)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨2 + B*C + N₀, by positivity, ?_⟩
  intro V _ G conn
  let n := Fintype.card V
  letI : Nonempty V := conn.nonempty
  have hn : 1 ≤ n := Fintype.card_pos
  have hx : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hx' : (0:ℝ) < n := by linarith
  let f := (n:ℝ)^(2/3+ε)
  have hf : 1 ≤ f := Real.one_le_rpow hx (by linarith)
  change (copNumber G : ℝ) ≤ (2 + B*C + N₀) * f
  by_cases ht : N₀ ≤ n
  · obtain ⟨A,hA,step⟩ := h n ht
    have win := wins_of_diameter_step G conn (N:=n) le_rfl (cutoff_pos hn δ) step
    have hQ : cutoff n δ ≤ n := cutoff_le hn hδ.le
    have hcl := (Nat.cast_le.mpr (Nat.clog_mono_right 2 hQ) :
      (Nat.clog 2 (cutoff n δ) : ℝ) ≤ Nat.clog 2 n).trans (clog_le hn hδ)
    have hprod : (Nat.clog 2 (cutoff n δ) : ℝ) * A ≤ B*C*f := by
      calc
        _ ≤ (B*(n:ℝ)^δ) * (C*(n:ℝ)^(2/3+δ/4)) :=
          mul_le_mul hcl hA (Nat.cast_nonneg _) (by positivity)
        _ = B*C * (n:ℝ)^(δ + (2/3+δ/4)) := by rw [Real.rpow_add hx' δ (2/3+δ/4)]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (by positivity)
    have hdiv : ((n/cutoff n δ : ℕ) : ℝ) ≤ f :=
      (quotient_le hn δ).trans (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
    have bound := (Nat.cast_le (α:=ℝ)).mpr (copNumber_le_of_win win)
    change (copNumber G : ℝ) ≤ ((1 + Nat.clog 2 (cutoff n δ)*A + n/cutoff n δ : ℕ) : ℝ) at bound
    push_cast at bound
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) N₀) (show 0 ≤ f by linarith)]
  · have hcn : copNumber G ≤ n := copNumber_le_of_win (winsWith_card G)
    have hs : (n : ℝ) ≤ N₀ := by exact_mod_cast (show n ≤ N₀ by omega)
    have ha : (copNumber G : ℝ) ≤ N₀ := (Nat.cast_le.mpr hcn).trans hs
    have hmore : (N₀:ℝ) ≤ N₀*f := by nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) N₀) (sub_nonneg.mpr hf)]
    nlinarith [mul_nonneg (mul_pos hB hC).le (show 0 ≤ f by linarith)]

end Meyniel.Multiscale
