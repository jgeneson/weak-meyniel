import Meyniel.TrialStepDefs
import Meyniel.MultiscaleBallClock
namespace Meyniel.Multiscale
open Finset Interception Targets GraphClock Clock
noncomputable section
variable {V W : Type*} [Fintype V] {G : SimpleGraph V}

def terminalExtras (G : SimpleGraph V) (δ : ℝ) (N root T i r : ℕ) (R : W → ℕ → V)
    (a v : ℕ) (b : ℕ) (w : W) : ℝ :=
  let h := leadTime (clockFactor δ) r
  let B := moveTime (clockFactor δ) r
  trialExtra G δ N T (cyclicWord (R w) root T) i r ((a+v+h+column B h b*h:ℕ) : ZMod (T+1))

theorem avg_child_price (δ : ℝ) (N root T i p r a : ℕ) (R : W → ℕ → V) (w : W)
    (start : root ≤ a) (stop : a+duration (clockFactor δ) p ≤ root+T)
    (horiz : endpoint 0 (leadTime (clockFactor δ) r) (leadTime (clockFactor δ) r)
      (childCount δ p r) ≤ duration (clockFactor δ) p) (hr : 0<r) :
    let h := leadTime (clockFactor δ) r
    let B := moveTime (clockFactor δ) r
    let J := top B h (childCount δ p r)+1
    (∑ b ∈ range J, (logBall G (center R a 0 h h (column B h b) w) (dilation δ*r) -
       logBall G (center R a 0 h h (column B h b) w) r+terminalExtras G δ N root T i r R a 0 b w))/(J:ℝ) =
      childPrice G δ N T i p r (cyclicWord (R w) root T) (a+duration (clockFactor δ) p) -
      (i:ℝ)*gain δ*Real.log N/2 + 9*(i:ℝ)/clockFactor δ*Real.log N+(i:ℝ)*Real.log 2 := by
  classical
  let C := clockFactor δ
  let h := leadTime C r
  let B := moveTime C r
  let t := duration C p
  let M := childCount δ p r
  let J := top B h M+1
  let y := cyclicWord (R w) root T
  let A b := scaleCharge G y δ N i r ((a+t:ℕ)-(childLag δ p r b:ℕ): ZMod (T+1)) +
    trialPrice G δ N T y (i-1) r ((a+t:ℕ)-(childLag δ p r b:ℕ): ZMod (T+1))
  let K := -(i:ℝ)*gain δ*Real.log N/2 + 9*(i:ℝ)/C*Real.log N+(i:ℝ)*Real.log 2
  have hh : 0<h := by dsimp [h,leadTime]; omega
  have hb : 0<B := by dsimp [B,moveTime,h,leadTime]; omega
  have localEq b (hb' : b ∈ range J) :
      logBall G (center R a 0 h h (column B h b) w) (dilation δ*r) -
       logBall G (center R a 0 h h (column B h b) w) r+terminalExtras G δ N root T i r R a 0 b w =
      A b+K := by
    let j := column B h b
    let e := a+h+j*h
    have hj := column_le hb hh (M:=M) (b:=b) (by simpa [J] using mem_range.mp hb')
    have hjh : j*h ≤ M*h := Nat.mul_le_mul_right h hj
    simp only [endpoint,Nat.zero_add] at horiz
    change h+M*h ≤ t at horiz
    have hd : h+j*h ≤ t := by omega
    have trans := child_translation (δ:=δ) (T:=T) (p:=p) (r:=r) (b:=b) (e:=a+t) (by change t ≤ a+t; omega) hd
    rw [show a+t-duration (clockFactor δ) p=a by change a+t-t=a; omega] at trans
    have cf := cyclicWord_at (R w) (u:=root) (T:=T) (t:=e) (by dsimp [e]; omega) (by change a+t ≤ root+T at stop; dsimp [e]; omega)
    have cc : center R a 0 h h j w = R w (e+2) := by unfold center endpoint e; congr 1; omega
    change logBall G (center R a 0 h h j w) _ - logBall G (center R a 0 h h j w) _ +
      trialExtra G δ N T y i r (e:ℕ) = A b+K
    change (e:ZMod (T+1))=((a+t:ℕ):ZMod (T+1))-(childLag δ p r b:ℕ) at trans
    dsimp only [A,K]
    rw [cc,← trans]
    unfold trialExtra scaleCharge growth
    change y (e:ZMod (T+1))=R w (e+2) at cf
    rw [cf]
    ring
  change (∑ b ∈ range J, _)/(J:ℝ)=_
  rw [sum_congr rfl localEq,sum_add_distrib,add_div]
  have hJ : (J:ℝ)≠0 := by dsimp [J]; positivity
  simp only [sum_const,card_range,nsmul_eq_mul]
  rw [mul_div_cancel_left₀ K hJ]
  change (∑ b ∈ range J, A b)/(J:ℝ)+K = _
  have id : (∑ b ∈ range J, A b)/(J:ℝ) = childPrice G δ N T i p r y (a+t) := by
    simp only [childPrice,mean,childLabels,card_range,A,J,B,h,M,C,Nat.cast_add]
  rw [id]
  dsimp [K]
  ring

theorem local_overhead {sum vol save D M J C : ℝ} {N : ℕ}
    (hN : 0<N) (hC : 0<C) (hM : 0<M) (hJ : 0<J)
    (hmj : M/J ≤ 1/2+1/C) (hjm : M ≤ J)
    (hd : D/M ≤ 6/C) (hD : 0 ≤ D) (hsum : 0 ≤ sum)
    (support : sum ≤ M*(vol-save)) (saving : 0 ≤ save) (vmax : vol ≤ Real.log N) :
    (sum+D*Real.log N)/J ≤ vol/2-save/2+7/C*Real.log N := by
  have ln := Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN)
  have nonneg := nonneg_of_mul_nonneg_right (hsum.trans support) hM
  have supp : sum/J ≤ (1/2+1/C)*(vol-save) := by
    calc _ ≤ (M/J)*(vol-save) := by calc _ ≤ (M*(vol-save))/J := div_le_div_of_nonneg_right support hJ.le
                                  _ = _ := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hmj nonneg
  have hd' : D/J ≤ 6/C := (div_le_div_of_nonneg_left hD hM hjm).trans hd
  have hcost := mul_le_mul_of_nonneg_right hd' ln
  have hs := mul_le_mul_of_nonneg_left (show vol-save ≤ Real.log N by linarith) (one_div_nonneg.mpr hC.le)
  rw [add_div]
  linear_combination (norm := ring_nf) supp+hcost+hs; norm_num

end
end Meyniel.Multiscale
