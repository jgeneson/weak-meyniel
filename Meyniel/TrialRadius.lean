import Meyniel.TrialRadiusPrice
import Meyniel.MultiscaleRootTrials

namespace Meyniel.Multiscale
open Finset Interception Targets GraphClock Clock
noncomputable section
universe v w
variable {V : Type v} {W : Type w} [Fintype V] [Fintype W] [Nonempty W] {G : SimpleGraph V}

theorem terminal_per_radius (hc : G.Connected) {δ : ℝ} {N root T i p r F a : ℕ}
    (R : W → ℕ → V) (z x : V) (facts : TrialFacts δ N) (hn : Fintype.card V ≤ N)
    (hi : 1 ≤ i) (hk : i+1 ≤ levels δ) (parent : p ∈ radii δ N (i+1))
    (child : r ∈ radii δ N i) (ctx : TrialInput G δ N root T (i+1) p R F a z x)
    (restricted : Bool)
    (band : restricted=true → ∀ w, InBand G (R w) F (a+duration (clockFactor δ) p)
      (bandWidth N (guardRadius δ N (i+1))))
    (ih : TrialAt.{v,w} G δ N root T i) :
    WindowMixture G R a (duration (clockFactor δ) p)
      (fun y => y∈ball G z (duration (clockFactor δ) p+3*p))
      (radiusPrice G δ N root T i p r R a restricted) := by
  classical
  let C := clockFactor δ
  let t := duration C p
  let h := leadTime C r
  let B := moveTime C r
  let M := childCount δ p r
  let J := top B h M+1
  let D := ceilRatio (4*p) B
  let wid := bandWidth N (guardRadius δ N (i+1))
  let A := ball G z (p+t+r)
  let S := fun j => if restricted then radialSupport G A x (a+h-F) h wid r j else A
  let save : ℝ := if restricted then gain δ*Real.log N else 0
  have rpos := radius_pos_of_mem child
  have xC := facts.clock
  have hpos : 0<h := by dsimp [h,leadTime]; omega
  have hB : 0<B := by dsimp [B,moveTime,h,leadTime]; omega
  have spare := facts.spare i hi hk p parent r child
  have rleh : r ≤ h := by dsimp [h,leadTime]; omega
  change 12*h ≤ p at spare
  have ht : t=C*p := rfl
  have geo := local_geometry hc R ctx.speed z facts.clock rpos spare ctx.near
  have setup := local_clock_setup (C:=C) (r:=p) (b:=B) xC hpos (show h ≤ B by dsimp [B,moveTime,h]; omega) spare
  change t ≤ M*h*2 ∧ 0<M ∧ (D:ℝ)/M ≤ 6/(C:ℝ) at setup
  have mpos := setup.2.1
  have hN := facts.vertices
  have ln := Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN)
  have deadline : endpoint 0 h h M ≤ t := geo.horizon
  have tm := facts.timing (i+1) (by omega) hk p parent
  have subset j (hj : j<M) w : ball G (center R a 0 h h j w) r ⊆ S j := by
    intro y hy
    have inside := geo.orig j hj.le w hy
    dsimp only [S]
    split_ifs with yes
    · apply mem_filter.mpr
      refine ⟨inside,?_⟩
      have stopj : a+h+j*h ≤ a+t := by
        have := Nat.mul_le_mul_right h hj.le; simp only [endpoint,Nat.zero_add] at deadline; change h+M*h ≤ t at deadline; omega
      have d := mem_ball.mp hy
      have eq : center R a 0 h h j w=R w (a+h+j*h+2) := by unfold center endpoint; congr 1; omega
      rw [eq] at d
      exact radial_at hc ((ctx.launched).trans (Nat.le_add_right _ _)) stopj (ctx.anchor w) (band yes w) d
    · exact inside
  have pos j (hj : j<M) : (S j).Nonempty :=
    (ball_nonempty (G:=G) (center R a 0 h h j (Classical.arbitrary W)) r).mono (subset j hj _)
  have support : (∑ j ∈ range M, Real.log (S j).card) ≤ (M:ℝ)*(Real.log A.card-save) := by
    cases wh : restricted with
    | false => simp [S,wh,save]
    | true =>
      have budget := tm.child_support r (by simpa using child) (by omega)
      have ratio := local_gain_ratio hpos setup.1 (g:=gain δ) (width:=wid) (r:=r) (N:=N) budget
      simpa only [S,wh,↓reduceIte,save] using radial_log_saving (G:=G) A x (M:=M) (N:=N)
        (a+h-F) h wid r (gain δ) hpos mpos hN (by simpa only [S,wh,↓reduceIte] using pos) ratio
  letI : Nonempty {s : WindowPolicy G // s.start∈A} :=
    ⟨⟨WindowPolicy.ofPolicy (Policy.stay G z),by change z ∈ ball G z _; simp⟩⟩
  obtain ⟨tr,ok⟩ := clock_terminal_trials (v:=0) (M:=M) hc R ctx.speed hN hi (by omega) child rpos
    ctx.starts ctx.stops (fun j hj => ctx.passes j (by omega)) ih deadline
  let extra := terminalExtras G δ N root T i r R a 0
  have clock := ball_clock_mixture hc R ctx.speed a t 0 h h r M B D N (dilation δ*r)
    hB hpos (by rfl) hn (by simpa [endTime,two_mul,Nat.add_assoc] using endTime_bound δ r)
    deadline z geo.home (fun y => y∈A) geo.orig geo.tail S subset extra tr (by
      intro b hb w y hy
      simpa [extra,terminalExtras,endpoint,Nat.add_assoc] using ok b hb w y hy)
  apply window_weaken clock
  · intro y hy
    apply mem_ball.mpr
    have hnear := mem_ball.mp hy
    change _ ≤ p+t+r at hnear
    change _ ≤ t+3*p
    omega
  · intro w
    have hJ : 0<J := by dsimp [J]; omega
    have jm : M ≤ J := by dsimp [J,top]; omega
    have nonneg : 0 ≤ ∑ j ∈ range M, Real.log (S j).card :=
      sum_nonneg (fun j hj => Real.log_nonneg (by exact_mod_cast (pos j (mem_range.mp hj)).card_pos))
    have hs : 0 ≤ save := by dsimp [save]; split <;> simp [mul_nonneg facts.gains ln]
    have vmax : Real.log A.card ≤ Real.log N := (logBall_bound G z (p+t+r) hn).2
    have overhead := local_overhead (C:=C) hN (by exact_mod_cast xC) (by exact_mod_cast mpos)
      (J:=(J:ℝ)) (by exact_mod_cast hJ) (clock_mean_coefficient xC rpos)
      (by exact_mod_cast jm) setup.2.2 (Nat.cast_nonneg _) nonneg support hs vmax
    have price := avg_child_price (G:=G) δ N root T i p r a R w ctx.starts ctx.stops deadline rpos
    have vol := local_trial_volume hc δ (T:=t) (R:=r) rfl (by omega : r ≤ p) (ctx.near w)
    change (∑ j ∈ range M, Real.log (S j).card + D*Real.log N)/(J:ℝ)+_ ≤ _
    rw [price]
    unfold radiusPrice
    change Real.log A.card ≤ _ at vol
    dsimp only [save] at overhead
    cases wb : restricted <;> simp [wb] at overhead ⊢ <;>
      dsimp only [C,t] at * <;>
      linear_combination (norm := ring_nf) overhead+vol/2 <;> norm_num

end
end Meyniel.Multiscale
