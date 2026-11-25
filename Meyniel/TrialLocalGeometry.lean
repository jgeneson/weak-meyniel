import Meyniel.TrialSupport
import Meyniel.MultiscaleTargets
import Meyniel.MultiscaleQuotients
namespace Meyniel.Multiscale
open Finset Interception Targets Clock
noncomputable section
variable {V W : Type*} [Fintype V] {G : SimpleGraph V}

theorem radius_pos_of_mem {δ : ℝ} {N i r : ℕ} (mem : r ∈ radii δ N i) : 0<r := by
  obtain ⟨j,_,rfl⟩ := mem_image.mp mem
  exact pow_pos (by have := radiusBase_ge δ; omega) _

/-- The local radius clock starts at u, looks at u+h+jh and runs up to
u+Cp. These estimates include its extension-to-home cost. -/
structure LocalGeometry (G : SimpleGraph V) (R : W → ℕ → V) (z : V) (u C p r : ℕ) : Prop where
  horizon : endpoint 0 (leadTime C r) (leadTime C r) (clockCount (C*p) 1 (leadTime C r)) ≤ C*p
  home : ∀ w, G.dist z (center R u 0 (leadTime C r) (leadTime C r) (clockCount (C*p) 1 (leadTime C r)) w)+r ≤
    ceilRatio (4*p) (moveTime C r)*moveTime C r
  orig : ∀ j ≤ clockCount (C*p) 1 (leadTime C r), ∀ w, ball G (center R u 0 (leadTime C r) (leadTime C r) j w) r ⊆
    ball G z (p+C*p+r)
  tail : ∀ w y, G.dist z y ≤ G.dist z (center R u 0 (leadTime C r) (leadTime C r) (clockCount (C*p) 1 (leadTime C r)) w)+r →
    y ∈ ball G z (p+C*p+r)

theorem local_geometry (hc : G.Connected) (R : W → ℕ → V) (speed : ∀ w, SpeedOne G (R w))
    {u C p r : ℕ} (z : V) (hC : 0 < C) (hr : 0 < r) (spare : 12*leadTime C r ≤ p)
    (near : ∀ w, G.dist z (R w (u+C*p+2)) ≤ p) : LocalGeometry G R z u C p r := by
  let h := leadTime C r
  let B := moveTime C r
  let M := clockCount (C*p) 1 h
  have hpos : 0 < h := by dsimp [h,leadTime]; omega
  have rleh : r ≤ h := by dsimp [h,leadTime]; omega
  have hB : 0 < B := by dsimp [B,moveTime]; omega
  have hp : p ≤ C*p := Nat.le_mul_of_pos_left _ hC
  change 12*h ≤ p at spare
  have cover := count_cover (t:=C*p) (q:=1) hpos (by omega)
  simp only [Nat.one_mul] at cover
  change M*h+h ≤ C*p ∧ C*p < M*h+2*h at cover
  have endLe j (hj : j ≤ M) : h+j*h ≤ C*p := by have := Nat.mul_le_mul_right h hj; omega
  have bound j (hj : j≤M) w : G.dist z (center R u 0 h h j w) ≤ p+(C*p-(h+j*h)) := by
    have hh := endLe j hj
    have hd := displacement hc (speed w) (u:=u+(h+j*h)+2) (v:=u+C*p+2) (by omega)
    have tri := hc.dist_triangle (u:=z) (v:=R w (u+C*p+2)) (w:=R w (u+(h+j*h)+2))
    rw [@SimpleGraph.dist_comm _ G (R w (u+C*p+2)) (R w (u+(h+j*h)+2))] at tri
    have hn := near w
    simpa only [center,endpoint,Nat.zero_add] using (show G.dist z (R w (u+(h+j*h)+2)) ≤ p+(C*p-(h+j*h)) by omega)
  refine ⟨by simpa [endpoint] using endLe M le_rfl,?_,?_,?_⟩
  · intro w
    have cc := (ceilRatio_spec (a:=4*p) hB).1
    change G.dist z (center R u 0 h h M w)+r ≤ ceilRatio (4*p) B*B
    have h' := bound M le_rfl w; omega
  · intro j hj w
    apply ball_subset hc
    change G.dist z (center R u 0 h h j w)+r ≤ p+C*p+r
    have hd := bound j hj w; omega
  · intro w y hy
    apply mem_ball.mpr
    change G.dist z y ≤ G.dist z (center R u 0 h h M w)+r at hy
    have h' := bound M le_rfl w
    omega

theorem local_gain_ratio {t M h width r N : ℕ} {g : ℝ} (hh : 0<h)
    (full : t ≤ M*h*2) (budget : ((2*(h+width+2+2*r) : ℕ):ℝ)*(N:ℝ)^g ≤ t) :
    (((width+2+2*r)/h+1 : ℕ):ℝ)*(N:ℝ)^g ≤ M := by
  have hc := Nat.div_mul_le_self (width+2+2*r) h
  have hfreq : ((width+2+2*r)/h+1)*h ≤ h+width+2+2*r := by rw [Nat.succ_mul]; omega
  have hfr : ((((width+2+2*r)/h+1:ℕ):ℝ))*(h:ℝ) ≤ (h:ℝ)+width+2+2*r := by exact_mod_cast hfreq
  have nt : (t:ℝ) ≤ (M:ℝ)*h*2 := by exact_mod_cast full
  have hn := Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) N) g
  have p := mul_le_mul_of_nonneg_right hfr hn
  push_cast at budget
  apply (mul_le_mul_iff_left₀ (show 0<(h:ℝ) by exact_mod_cast hh)).mp
  nlinarith only [budget,nt,p]
end
end Meyniel.Multiscale
