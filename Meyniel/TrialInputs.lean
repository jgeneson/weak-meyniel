module

public import Meyniel.MultiscaleTrials
public import Meyniel.MultiscaleGraphClock

@[expose] public section

namespace Meyniel.Multiscale
open Finset Interception
open scoped Classical
noncomputable section
variable {V W : Type*} [Fintype V] {G : SimpleGraph V}

/-- An ordinary correct-terminal family seen at launch. The absolute clock
agrees with the cyclic accounting word throughout this window. -/
structure TrialInput (G : SimpleGraph V) (δ : ℝ) (N root T i r : ℕ)
    (R : W → ℕ → V) (F a : ℕ) (z x : V) : Prop where
  starts : root ≤ a
  stops : a+duration (clockFactor δ) r ≤ root+T
  launched : F ≤ a
  speed : ∀ w, SpeedOne G (R w)
  anchor : ∀ w, R w F=x
  near : ∀ w, G.dist z (R w (a+duration (clockFactor δ) r+2)) ≤ r
  passes : ∀ (j : Fin (levels δ)), j.val+1 < i → ∀ w,
    Passes G (R w) (physicalScale G δ N j) a (a+duration (clockFactor δ) r)
  band : ∀ w, i ∉ badLevels G (R w (a+duration (clockFactor δ) r+2)) δ N →
    InBand G (R w) F (a+duration (clockFactor δ) r) (bandWidth N (guardRadius δ N i))

def TrialOutcome (G : SimpleGraph V) (δ : ℝ) (N root T i r : ℕ)
    (R : W → ℕ → V) (a : ℕ) (z : V) : Prop :=
  let t := duration (clockFactor δ) r
  WindowMixture G R a t (fun y => y ∈ ball G z (t+3*r)) (fun w =>
    logBall G (R w (a+t+2)) (dilation δ*r)/2+
      trialExtra G δ N T (cyclicWord (R w) root T) i r (a+t))

theorem trial_one [Fintype W] [Nonempty W] (hc : G.Connected) {δ : ℝ} {N root T r F a : ℕ}
    {R : W → ℕ → V} {z x : V} (ctx : TrialInput G δ N root T 1 r R F a z x)
    (hn : Fintype.card V ≤ N) (hN : 0 < N) (hC : 0 < clockFactor δ) (hr : 0 < r)
    (time : TimingFacts δ N 1 r) : TrialOutcome G δ N root T 1 r R a z := by
  classical
  let t := duration (clockFactor δ) r
  let good w := 1 ∉ badLevels G (R w (a+t+2)) δ N
  obtain hm := bottom_window hc R a F r N (clockFactor δ) (bandWidth N (guardRadius δ N 1))
    z x (gain δ) hn hN hC hr ctx.launched ctx.speed ctx.anchor
    (fun w => by simpa [duration,Nat.add_right_comm a 2] using ctx.near w)
    good ctx.band (by simpa [duration] using time.bottom_support)
  apply window_weaken hm
  · intro y hy; apply mem_ball.mpr; have hh := mem_ball.mp hy
    change _ ≤ t+3*r
    change _ ≤ r+t at hh
    omega
  · intro w
    have vol := local_trial_volume hc δ (r:=r) (T:=t) (R:=0) rfl (Nat.zero_le _) (ctx.near w)
    rw [Nat.add_zero] at vol
    have cw := cyclicWord_at (R w) (u:=root) (T:=T) (t:=a+t) (by have := ctx.starts; omega) ctx.stops
    have eq : (a:ZMod (T+1))+(t:ZMod (T+1))=((a+t:ℕ):ZMod (T+1)) := by push_cast; rfl
    have ln := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN)
    have hcR : 0 < (clockFactor δ:ℝ) := by exact_mod_cast hC
    unfold trialExtra trialPrice
    rw [eq,cw]
    simp only [one_mul,Nat.cast_one,Nat.sub_self,nestedPrice,zero_sub]
    by_cases hg : good w
    · have hb : 1 ∉ badLevels G (R w (a+t+2)) δ N := hg
      simp only [if_pos hg,if_neg hb,add_zero]
      have h := div_nonneg ln hcR.le
      dsimp [t,duration] at vol ⊢
      ring_nf at vol h ⊢; nlinarith only [vol,h]
    · have hb : 1 ∈ badLevels G (R w (a+t+2)) δ N := by simpa [good] using hg
      simp only [if_neg hg,if_pos hb,sub_zero]
      have h := div_nonneg ln hcR.le
      dsimp [t,duration] at vol ⊢
      ring_nf at vol h ⊢; nlinarith only [vol,h]

/-- Launch and endpoint times for a child label; both are offsets from the
outer window's start. -/
theorem label_times {h B b : ℕ} (hh : 0<h) (hB : 0<B) :
    let f := Clock.row B h b*B
    let e := h+Clock.column B h b*h
    f+h ≤ e ∧ e < f+2*h+B := by
  let k := Clock.row B h b
  let j := Clock.column B h b
  have H := (Clock.le_row_iff (b:=b) (t:=k) hB hh).mp le_rfl
  have le := H.1
  have hk : k*B ≤ j*h := H.2
  have hn : ¬ (k+1 ≤ b ∧ (k+1)*B ≤ (b-(k+1))*h) := by
    rw [← Clock.le_row_iff hB hh]; omega
  by_cases eq : k=b
  · have : j=0 := by dsimp [j,Clock.column]; change b-k=0; omega
    change k*B+h ≤ h+j*h ∧ h+j*h < k*B+2*h+B
    rw [this,Nat.zero_mul] at hk ⊢; omega
  · have hsub : b-(k+1)+1=j := by dsimp [j,Clock.column]; change _=b-k; omega
    have hm : (b-(k+1))*h+h=j*h := by rw [← Nat.succ_mul, Nat.succ_eq_add_one, hsub]
    rw [Nat.succ_mul] at hn
    change k*B+h ≤ h+j*h ∧ h+j*h < k*B+2*h+B
    omega
end
end Meyniel.Multiscale
