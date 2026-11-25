import Meyniel.MultiscaleRootRegion
import Meyniel.MultiscaleTrials
import Meyniel.MultiscaleWindowSpec

/-! The positive-level window estimate has global and local incarnations.
The zero-level local window is the ordinary one-step clock. -/
namespace Meyniel.Multiscale
open Filter Finset Interception
noncomputable section
universe u

def PositiveRootAt (δ : ℝ) (N : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected → Fintype.card V ≤ N →
    ∀ (W : Type u) [Fintype W] [Nonempty W] (R : W → ℕ → V) (m X vol : ℕ) (starts : V → Prop),
    m+1 ≤ levels δ → 0 < X → (∀ w, SpeedOne G (R w)) →
    (∀ w (l : Fin (levels δ)), l.val < m+1 → Passes G (R w) (physicalScale G δ N l) 0 (windowTime N X)) →
    (∀ r ∈ radii δ N (m+1), 4*leadTime (clockFactor δ) r ≤ X ∧
      Nonempty (RootRegion G R 0 (windowTime N X) X r vol starts)) →
    WindowMixture G R 0 (windowTime N X) starts (fun _ => windowCost δ N (m+1) vol)

theorem root_zero {δ : ℝ} {N X outer : ℕ} (hN : 2 ≤ N) (hX : 0 < X)
    (slack : 1 ≤ δ/20*Real.log N) (hout : 2*X+windowTime N X ≤ outer)
    {V W : Type*} [Fintype V] [Fintype W] [Nonempty W] {G : SimpleGraph V}
    (hc : G.Connected) (hn : Fintype.card V ≤ N) (R : W → ℕ → V) (z : V)
    (speed : ∀ w, SpeedOne G (R w))
    (ends : ∀ w, G.dist z (R w (windowTime N X+2)) ≤ 2*X) :
    WindowMixture G R 0 (windowTime N X) (fun x => G.dist z x ≤ 2*windowTime N X)
      (fun _ => windowCost δ N 0 (ball G z outer).card) := by
  let T := windowTime N X
  let S := ball G z outer
  have ends' w : G.dist z (R w (0+2+T)) ≤ 2*X := by simpa [T,Nat.add_comm] using ends w
  have supports (j) (hj : j<T) w : R w (0+2+j) ∈ S := by
    apply mem_ball.mpr
    have h := displacement hc (speed w) (show 0+2+j ≤ T+2 by omega)
    rw [@SimpleGraph.dist_comm _ G (R w (0+2+j)) (R w (T+2))] at h
    have d := hc.dist_triangle (u:=z) (v:=R w (T+2)) (w:=R w (0+2+j))
    have := ends w
    change 2*X+T ≤ outer at hout
    change G.dist z (R w (T+2)) ≤ 2*X at this
    omega
  apply window_weaken (unit_window hc R 0 T (2*X) N z hn speed ends' (fun _ => S) supports)
  · intro x hx
    have a := mem_ball.mp hx
    have b := (run_width hX hN).2.1
    change G.dist z x ≤ 2*T
    change 2*X ≤ T at b
    omega
  · intro w
    have v1 : (1:ℝ) ≤ S.card := by exact_mod_cast (ball_nonempty (G:=G) z outer).card_pos
    have v0 := Real.log_nonneg v1
    have n1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1≤N by omega)
    have l0 := Real.log_nonneg n1
    have hlog : Real.log (N:ℝ) ≤ Real.log (2*N) := Real.log_le_log (by linarith) (by linarith)
    have hT : 8*(X:ℝ)*Real.log (2*N) ≤ T := Nat.le_ceil _
    have tx : (X:ℝ)*Real.log (N:ℝ) ≤ T := by
      have lm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg X)
      nlinarith [mul_nonneg (Nat.cast_nonneg X) l0]
    have den : (0:ℝ) < 2*(T:ℝ)+1 := by positivity
    change ((∑ _j ∈ range T, Real.log (S.card:ℝ)) + (↑(2*X):ℝ)*Real.log N)/(2*(T:ℝ)+1) ≤ windowCost δ N 0 S.card
    simp only [sum_const, card_range,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,windowCost,Nat.cast_zero,zero_mul,zero_div,sub_zero]
    apply (div_le_iff₀ den).mpr
    have sh := mul_le_mul_of_nonneg_right slack den.le
    nlinarith

theorem constantWindows_of_positive {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100)
    (positive : ∀ᶠ N : ℕ in atTop, PositiveRootAt.{u} δ N) :
    ∀ᶠ N : ℕ in atTop, ConstantWindows.{u} δ N := by
  have growth := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨c,hc,many⟩ := many_radii hδ ht
  filter_upwards [positive,root_radius_spare hδ ht,timingFacts_eventually hδ ht,local_start_radius hδ ht,
    many,growth.eventually_ge_atTop (20/δ),eventually_ge_atTop 2] with N pos spare timing start ranges large hN
  change 20/δ ≤ Real.log N at large
  have slack : 1 ≤ δ/20*Real.log N := by have := (div_le_iff₀ hδ).mp large; linarith
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hK := levels_pos hδ
  constructor
  · intro V _ G conn size diam W _ _ R speed passes
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
    rw [hm]
    apply pos V G conn size W R m (cutoff N δ) N (fun _ => True) (by omega)
      (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hn _)) speed
    · intro w l _; exact passes w l
    · intro r hr
      exact ⟨(spare (m+1) (by omega) (by omega) r hr).1,global_region conn R _ _ _ _ _ size diam⟩
  · intro V _ G conn size _ i z _ W _ _ R speed ends passes
    let X := guardRadius δ N (i.val+1)
    let T := windowTime N X
    have hX : 0<X := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hn _)
    change ∀ w, G.dist z (R w (T+2)) ≤ 2*X at ends
    change WindowMixture G R 0 T (fun v => G.dist z v ≤ 2*T) (fun _ => windowCost δ N i.val (ball G z (outerRadius δ N (i.val+1))).card)
    cases hi : i.val with
    | zero =>
      simpa only [hi] using root_zero hN hX slack (start (i.val+1) (by omega) i.isLt) conn size R z speed ends
    | succ m =>
      apply pos V G conn size W R m X _ _ (by omega) hX speed
      · intro w l hl; exact passes w l (by omega)
      · intro r hr
        have hs := (spare (m+1) (by omega) (by omega) r hr).2 (by omega)
        have hsX : 4*leadTime (clockFactor δ) r ≤ X := by simpa [X,hi] using hs
        have hrad : r ≤ X := by unfold leadTime at hsX; omega
        have highT : 2*X+r ≤ T := by
          have n2 : (1:ℝ) ≤ Real.log (2*N) := by
            have htwo : (2:ℝ) ≤ N := by exact_mod_cast hN
            have h4 : Real.log 4 ≤ Real.log (2*(N:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
            rw [show (4:ℝ)=2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)] at h4
            linarith [Real.log_two_gt_d9]
          have ceilT : 8*(X:ℝ)*Real.log (2*N) ≤ T := Nat.le_ceil _
          have three : 3*X ≤ T := by exact_mod_cast (show 3*(X:ℝ)≤T by nlinarith [mul_le_mul_of_nonneg_left n2 (Nat.cast_nonneg X)])
          omega
        have hc' : (0:ℝ) < (radii δ N (i.val+1)).card :=
          (mul_pos hc (Real.log_pos (by exact_mod_cast (show 1<N by omega)))).trans_le (ranges _ (by omega) i.isLt)
        obtain ⟨p,hp⟩ := card_pos.mp (show 0<(radii δ N (i.val+1)).card by exact_mod_cast hc')
        have hv := (timing (i.val+1) (by omega) i.isLt p hp).local_volume r (by simpa [hi] using hr) (by omega)
        have reg := (local_region conn R speed 0 T X r z (by simpa using ends) highT).some
        have hv' : 2*X+T+r ≤ outerRadius δ N (m+1+1) := by simpa only [← hi] using hv
        refine ⟨hsX,⟨{reg with sites_card := reg.sites_card.trans (card_le_card ?_) }⟩⟩
        intro y hy
        exact mem_ball.mpr ((mem_ball.mp hy).trans hv')

end
end Meyniel.Multiscale
