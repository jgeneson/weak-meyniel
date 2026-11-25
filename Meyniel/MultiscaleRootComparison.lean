import Meyniel.MultiscaleRootTrials
import Meyniel.MultiscaleRootSetup
import Meyniel.MultiscaleRootRegion

namespace Meyniel.Multiscale
open Finset Interception Targets Clock
noncomputable section
universe v w
variable {V : Type v} {W : Type w} [Fintype V] [Fintype W] [Nonempty W] {G : SimpleGraph V}

def rootBase (δ : ℝ) (N i vol : ℕ) : ℝ :=
  Real.log vol/2 - (i:ℝ)*gain δ*Real.log N/2 +
  2 + (9*(i:ℝ)+1)/clockFactor δ*Real.log N + (i:ℝ)*Real.log 2

def rootRowCost (G : SimpleGraph V) (δ : ℝ) (N T m r ξ : ℕ) (R : W → ℕ → V) (w : W) : ℝ :=
  mean (range (top (moveTime (clockFactor δ) r) (leadTime (clockFactor δ) r)
    (clockCount T 2 (leadTime (clockFactor δ) r))+1)) (fun b =>
    rootCharge G δ N T (cyclicWord (R w) 0 T) m r ((rootEnd δ 0 r ξ b:ℕ):ZMod (T+1)))

theorem root_fixed (hc : G.Connected) {δ : ℝ} {N m X vol r ξ : ℕ}
    (R : W → ℕ → V) (speed : ∀ w, SpeedOne G (R w)) (hN : 2 ≤ N) (hn : Fintype.card V ≤ N)
    (facts : TrialFacts δ N) (hX : 0<X) (hk : m+1 ≤ levels δ) (hr : r ∈ radii δ N (m+1))
    (spare : 4*leadTime (clockFactor δ) r ≤ X) (offset : ξ < leadTime (clockFactor δ) r)
    (starts : V → Prop) (reg : RootRegion G R 0 (windowTime N X) X r vol starts)
    (passes : ∀ w (l : Fin (levels δ)), l.val < m+1 →
      Passes G (R w) (physicalScale G δ N l) 0 (windowTime N X))
    (ih : TrialAt.{v,w} G δ N 0 (windowTime N X) (m+1)) :
    WindowMixture G R 0 (windowTime N X) starts
      (fun w => rootRowCost G δ N (windowTime N X) m r ξ R w + rootBase δ N (m+1) vol) := by
  classical
  let C := clockFactor δ
  let T := windowTime N X
  let h := leadTime C r
  let B := moveTime C r
  let M := clockCount T 2 h
  let D := ceilRatio (6*X) B
  let J := top B h M+1
  let e b := endpoint ξ h h (column B h b)
  let y j := center R 0 ξ h h j
  let word w := cyclicWord (R w) 0 T
  let cost b w := trialExtra G δ N T (word w) (m+1) r (e b)
  change 4*h ≤ X at spare
  change ξ<h at offset
  have rp : 0<r := radius_pos_of_mem hr
  have rh : r≤h := by dsimp [h,leadTime]; omega
  have hh : 0<h := by omega
  have hb : h≤B := by dsimp [B,moveTime]; omega
  have hB := hh.trans_le hb
  have ww := (run_width hX hN).2.1
  change 2*X ≤ T at ww
  have mc := count_cover (t:=T) (q:=2) hh (by omega)
  change M*h+2*h ≤ T ∧ T < M*h+3*h at mc
  have deadline : endpoint ξ h h M ≤ T := by unfold endpoint; omega
  have last : T-endpoint ξ h h M ≤ 2*h := by unfold endpoint; omega
  have he j (hj:j≤M) : endpoint ξ h h j≤T := by
    have := Nat.mul_le_mul_right h hj
    unfold endpoint at *; omega
  have hsites : reg.sites.Nonempty := by
    let w : W := Classical.arbitrary _
    refine ⟨_, reg.support w 0 (by omega) r le_rfl (by apply mem_ball.mpr; rw [SimpleGraph.dist_self]; omega)⟩
  letI : Nonempty {s : WindowPolicy G // starts s.start} := by
    obtain ⟨x,hx⟩ := hsites
    exact ⟨⟨WindowPolicy.ofPolicy (Policy.stay G x),reg.start_of_mem _ hx⟩⟩
  obtain ⟨trial,correct⟩ := clock_terminal_trials hc R speed facts.vertices (by omega) hk hr rp
    (root:=0) (u:=0) (T:=T) (L:=T) (v:=ξ) (M:=M) (by omega) (by omega)
    (fun j hj w => by simpa [T] using passes w j (by omega)) ih deadline
  have region j (hj:j≤M) w : ball G (y j w) r ⊆ reg.sites :=
    reg.support w _ (he j hj) r le_rfl
  have H := ball_clock_mixture hc R speed 0 T ξ h h r M B D N (dilation δ*r) hB hh le_rfl hn
    (by simpa only [endTime,two_mul] using endTime_bound δ r) deadline reg.home
    (reg.last_home_bound hc speed hB (by omega) (by omega) deadline last) starts
    (fun j hj w x hx => reg.start_of_mem _ (region _ hj w hx))
    (fun w => reg.retreat_start w _ deadline r le_rfl)
    (fun _ => reg.sites) (fun j hj => region _ hj.le) cost trial (by simpa only [Nat.zero_add] using correct)
  obtain ⟨_,hm,home⟩ := root_clock_setup hN hX hh hb spare
  have coeff := clock_mean_coefficient (M:=M) facts.clock rp
  have bound := root_setup_cost facts.vertices facts.clock hm (show M≤J by dsimp [J,top]; omega)
    hsites.card_pos reg.sites_card ((card_le_univ _).trans hn) coeff home
  apply window_weaken H (fun _ h => h)
  intro w
  let base := -((m+1:ℕ):ℝ)*gain δ*Real.log N/2 + 9*((m+1:ℕ):ℝ)/C*Real.log N+((m+1:ℕ):ℝ)*Real.log 2
  let price b := rootCharge G δ N T (word w) m r (rootEnd δ 0 r ξ b:ℕ)
  have point b (hb:b∈range J) :
      logBall G (y (column B h b) w) (dilation δ*r) - logBall G (y (column B h b) w) r+cost b w =
      price b + base := by
    have hj := column_le hB hh (show b≤top B h M by simpa [J] using hb)
    have he' := he _ hj
    have cy := cyclicWord_at (R w) (u:=0) (T:=T) (t:=e b) (by omega) (by simpa [e] using he')
    have align : rootEnd δ 0 r ξ b=e b := by simp [rootEnd,e,endpoint,h,B,C]
    have cy' : word w (e b) = y (column B h b) w := by simpa only [y,center,Nat.zero_add] using cy
    unfold price rootCharge scaleCharge growth cost trialExtra
    simp only [align,Nat.add_sub_cancel]
    rw [cy']
    dsimp only [base,C]
    ring
  have am : mean (range J) (fun b => logBall G (y (column B h b) w) (dilation δ*r) -
      logBall G (y (column B h b) w) r+cost b w) = mean (range J) price+base := by
    trans mean (range J) (fun b => price b+base)
    · unfold mean; rw [sum_congr rfl point]
    · rw [mean_add',mean_const' (show (range J).Nonempty from ⟨0,mem_range.mpr (by dsimp [J]; omega)⟩)]
  change ((∑ _j ∈ range M, Real.log reg.sites.card)+D*Real.log N)/(J:ℝ) +
    (∑ b ∈ range J, _)/(J:ℝ) ≤ _
  have ar : (∑ b ∈ range J, (logBall G (y (column B h b) w) (dilation δ*r) -
      logBall G (y (column B h b) w) r+cost b w))/(J:ℝ) = mean (range J) price+base := by simpa [mean] using am
  rw [ar]
  simp only [sum_const,card_range,nsmul_eq_mul]
  change _ ≤ mean (range J) price+rootBase δ N (m+1) vol
  dsimp only [base,rootBase,C] at *
  linarith only [bound,show (9*((m+1:ℕ):ℝ)+1)/(clockFactor δ)*Real.log N =
      9*((m+1:ℕ):ℝ)/(clockFactor δ)*Real.log N+Real.log N/(clockFactor δ) by ring]

end
end Meyniel.Multiscale
