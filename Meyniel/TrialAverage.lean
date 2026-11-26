module

public import Meyniel.TrialStepDefs
public import Meyniel.MultiscaleRootRegion

@[expose] public section

namespace Meyniel.Multiscale
open Finset Interception
open scoped Classical
noncomputable section
universe v w
variable {V : Type v} {W : Type w} [Fintype V] {G : SimpleGraph V}

theorem TrialInput.pull {U : Type*} {δ : ℝ} {N root T i p F a : ℕ} {R : W → ℕ → V} {z x : V}
    (h : TrialInput G δ N root T i p R F a z x) (f : U → W) :
    TrialInput G δ N root T i p (fun w => R (f w)) F a z x :=
  ⟨h.starts,h.stops,h.launched,fun w => h.speed (f w),fun w => h.anchor (f w),
   fun w => h.near (f w),fun j hj w => h.passes j hj (f w),fun w => h.band (f w)⟩

def parentBase (G : SimpleGraph V) (δ : ℝ) (N root T i p : ℕ) (R : W → ℕ → V)
    (a : ℕ) (w : W) : ℝ :=
  let e := a+duration (clockFactor δ) p
  logBall G (R w (e+2)) (dilation δ*p)/2+
    trialPrice G δ N T (cyclicWord (R w) root T) i p e -
    (i:ℝ)*gain δ*Real.log N/2 + (9*(i:ℝ)+7)/clockFactor δ*Real.log N + (i:ℝ)*Real.log 2

theorem average_radius_price (δ : ℝ) {N root T i p a : ℕ} (R : W → ℕ → V) (w : W)
    (band : Bool) (hi : 0 < i) (hne : (radii δ N i).Nonempty) :
    mean (radii δ N i) (fun r => radiusPrice G δ N root T i p r R a band w) =
      parentBase G δ N root T i p R a w - (if band then gain δ*Real.log N/2 else 0) := by
  let e := a+duration (clockFactor δ) p
  let y := cyclicWord (R w) root T
  let constant := logBall G (R w (e+2)) (dilation δ*p)/2 - (if band then gain δ*Real.log N/2 else 0) -
    (i:ℝ)*gain δ*Real.log N/2 + (9*(i:ℝ)+7)/clockFactor δ*Real.log N+(i:ℝ)*Real.log 2
  have per (r : ℕ) : radiusPrice G δ N root T i p r R a band w = childPrice G δ N T i p r y e+constant := by
    dsimp only [radiusPrice,constant,e,y]; ring
  simp_rw [per]
  rw [mean_add',mean_const' hne]
  have childEq : mean (radii δ N i) (fun r => childPrice G δ N T i p r y e)=
      trialPrice G δ N T y i p e := by
    cases i with
    | zero => omega
    | succ i => rfl
  rw [childEq]
  dsimp only [parentBase,constant,e,y]; ring

theorem trial_merge [Fintype W] [Nonempty W] {δ : ℝ} {N root T i p F a : ℕ}
    (R : W → ℕ → V) (z x : V) (hN : 0 < N) (hC : 0 < clockFactor δ) (hi : 0 < i)
    (ranges : (radii δ N i).Nonempty) (ctx : TrialInput G δ N root T (i+1) p R F a z x)
    (step : ∀ {U : Type w} [Fintype U] [Nonempty U] (f : U → W) (b : Bool),
      (b=true → ∀ w, InBand G (R (f w)) F (a+duration (clockFactor δ) p) (bandWidth N (guardRadius δ N (i+1)))) →
      ∀ r ∈ radii δ N i, WindowMixture G (fun w => R (f w)) a (duration (clockFactor δ) p)
        (fun y => y∈ball G z (duration (clockFactor δ) p+3*p))
        (radiusPrice G δ N root T i p r (fun w => R (f w)) a b)) :
    TrialOutcome G δ N root T (i+1) p R a z := by
  classical
  let t := duration (clockFactor δ) p
  let e := a+t
  let good w := i+1 ∉ badLevels G (R w (e+2)) δ N
  let start y := y∈ball G z (t+3*p)
  let hit (s : {s : WindowPolicy G // start s.start}) w := windowHit s.val (R w) a t
  let base := parentBase G δ N root T i p R a
  let sv := gain δ*Real.log N/2
  have mix {U : Type w} [Fintype U] [Nonempty U] (f : U → W) (b : Bool)
       (hb : b=true → ∀ w, InBand G (R (f w)) F e (bandWidth N (guardRadius δ N (i+1)))) :
      WindowMixture G (fun w => R (f w)) a t start (fun w => base (f w) - (if b then sv else 0)) := by
    have h := window_average _ ranges (fun w => R (f w)) a t start
      (fun r => radiusPrice G δ N root T i p r (fun w => R (f w)) a b) (step f b hb)
    exact window_weaken h (fun _ => id) (fun w => (average_radius_price δ _ w b hi ranges).le)
  obtain ⟨m,hm⟩ := mix id false (by simp)
  have full w : Real.exp (-base w) ≤ m.success hit w := by simpa [hit] using hm w
  obtain ⟨m',hm'⟩ := combine_good hit base good sv m full (by
    intro hq
    letI := hq
    obtain ⟨s,hs⟩ := mix (Subtype.val (p:=good)) true (fun _ w => ctx.band _ w.2)
    exact ⟨s,fun w h => by simpa [hit,Mixture.success] using hs ⟨w,h⟩⟩)
  apply window_weaken (show WindowMixture G R a t start (fun w => base w-(if good w then sv else 0)+Real.log 2) from ⟨m',hm'⟩)
    (fun _ => id)
  intro w
  have cyc := cyclicWord_at (R w) (u:=root) (T:=T) (t:=e) (by dsimp [e]; have := ctx.starts; omega) ctx.stops
  have posC : 0<(clockFactor δ:ℝ) := by exact_mod_cast hC
  have ln := Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN)
  have NN := mul_nonneg (inv_nonneg.mpr posC.le) ln
  rw [← Nat.cast_add]
  change _ ≤ logBall G (R w (e+2)) _/2+trialExtra G δ N T (cyclicWord (R w) root T) (i+1) p (e:ℕ)
  dsimp only [base,parentBase,trialExtra]
  rw [show i+1-1=i by omega,cyc]
  push_cast
  by_cases yes : good w
  · have hno : i+1 ∉ badLevels G (R w (e+2)) δ N := yes
    simp only [if_pos yes,if_neg hno,add_zero]
    dsimp [sv,e,t]
    simp only [Nat.cast_add]
    linear_combination (norm := ring_nf) 2*NN; norm_num
  · have hyes : i+1 ∈ badLevels G (R w (e+2)) δ N := by simpa [good] using yes
    simp only [if_neg yes,if_pos hyes,sub_zero]
    dsimp [sv,e,t]
    simp only [Nat.cast_add]
    linear_combination (norm := ring_nf) 2*NN; norm_num
end
end Meyniel.Multiscale
