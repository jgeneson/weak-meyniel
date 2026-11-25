import Meyniel.MultiscaleTiming
import Meyniel.MultiscaleClock

/-! # Rounding the numbers of observations and extension steps -/

namespace Meyniel.Multiscale

open Filter
noncomputable section

def ceilRatio (a b : ℕ) : ℕ := (a+b-1)/b

theorem ceilRatio_spec {a b : ℕ} (hb : 0 < b) :
    a ≤ ceilRatio a b*b ∧ ceilRatio a b*b ≤ a+b := by
  unfold ceilRatio
  have h := Nat.mod_add_div (a+b-1) b
  have hm := Nat.mod_lt (a+b-1) hb
  rw [Nat.mul_comm b] at h
  omega

/-- A clock running intermittently in a window of length t, with a preparatory
period of q time strides. -/
def clockCount (t q h : ℕ) := (t-q*h)/h

theorem count_cover {t q h : ℕ} (hh : 0 < h) (hslack : q*h ≤ t) :
    clockCount t q h*h + q*h ≤ t ∧ t < clockCount t q h*h + (q+1)*h := by
  have eq := Nat.mod_add_div (t-q*h) h
  have hm := Nat.mod_lt (t-q*h) hh
  unfold clockCount
  rw [Nat.mul_comm h] at eq; rw [Nat.add_mul,Nat.one_mul]
  omega

theorem clock_mean_coefficient {C r M : ℕ} (hC : 0 < C) (hr : 0 < r) :
    (M:ℝ) / ((Clock.top (moveTime C r) (leadTime C r) M + 1 : ℕ):ℝ) ≤ 1/2 + 1/(C:ℝ) := by
  let h := leadTime C r
  let B := moveTime C r
  let J := Clock.top B h M+1
  have hb : 0 < B := by dsimp [B,moveTime]; omega
  have hJ : (0:ℝ) < J := by dsimp [J]; positivity
  have hb' : (0:ℝ) < B := by exact_mod_cast hb
  have hC' : (0:ℝ) < C := by exact_mod_cast hC
  have hh' : (0:ℝ) ≤ h := Nat.cast_nonneg _
  have eq := Nat.mod_add_div (M*h) B
  have hm := Nat.mod_lt (M*h) hb
  have hobs : M*(B+h) ≤ J*B := by
    dsimp [J,Clock.top,Clock.height]
    rw [Nat.mul_add,Nat.succ_mul,Nat.add_mul]
    rw [Nat.mul_comm B] at eq
    omega
  have hobs' : (M:ℝ)*((B:ℝ)+h) ≤ J*B := by exact_mod_cast hobs
  have lower : (M:ℝ) / J ≤ B / ((B:ℝ)+h) := by
    apply (div_le_div_iff₀ hJ (by positivity)).mpr
    linarith
  apply lower.trans
  apply (div_le_iff₀ (by positivity)).mpr
  apply (mul_le_mul_iff_left₀ hC').mp
  rw [show (1/2 + 1/(C:ℝ))*((B:ℝ)+h)*C = ((C:ℝ)/2+1)*(B+h) by field_simp]
  dsimp [B,h,moveTime,leadTime,duration]
  push_cast
  nlinarith [Nat.cast_nonneg (α:=ℝ) r, mul_nonneg (Nat.cast_nonneg (α:=ℝ) r) hC'.le]

/-- The extension penalty in a nonbottom terminal: D/M ≤ 6/C. -/
theorem local_clock_setup {C r b h : ℕ} (hC : 0 < C) (hh : 0 < h)
    (hb : h ≤ b) (hspare : 12*h ≤ r) :
    let M := clockCount (C*r) 1 h
    M*h*2 ≥ C*r ∧ 0 < M ∧
      (ceilRatio (4*r) b:ℝ) / M ≤ 6 / (C:ℝ) := by
  let M := clockCount (C*r) 1 h
  let D := ceilRatio (4*r) b
  have hCr : r ≤ C*r := Nat.le_mul_of_pos_left _ hC
  have hc := count_cover (t:=C*r) (q:=1) hh (by omega)
  simp only [Nat.one_mul] at hc
  change M*h+h ≤ C*r ∧ C*r < M*h+2*h at hc
  have hMh : C*r ≤ M*h*2 := by omega
  have hM : 0 < M := by
    by_contra! hzero
    have ee : M = 0 := by omega
    rw [ee,Nat.zero_mul,Nat.zero_mul] at hMh
    omega
  refine ⟨hMh,hM,?_⟩
  have hb' : 0 < b := hh.trans_le hb
  have hD : D*h ≤ 4*r+h := by
    by_cases he : D=0
    · simp [he]
    have lo := (ceilRatio_spec (a:=4*r) hb').2
    change D*b ≤ 4*r+b at lo
    have hh' := Nat.mul_le_mul_left (D-1) hb
    have heq (t : ℕ) : D*t = (D-1)*t+t := by
      rw [← Nat.succ_mul]; congr 1; omega
    rw [heq b] at lo
    rw [heq h]
    omega
  have target : D*C ≤ 6*M := by
    apply Nat.le_of_mul_le_mul_right (c:=h) _ hh
    have hu := Nat.mul_le_mul_left C hD
    have hs := Nat.mul_le_mul_left C (show h ≤ r by omega)
    have h := Nat.mul_le_mul_left 6 hc.2.le
    nlinarith only [hu,hs,h,hspare,hCr]
  apply (div_le_div_iff₀ (by exact_mod_cast hM) (by exact_mod_cast hC)).mpr
  exact_mod_cast target

/-- D/J in a root window times log N is bounded by an absolute constant.
This covers D=ceil(X/B) and D=ceil(6X/B). -/
theorem root_clock_setup {N X b h : ℕ} (hN : 2 ≤ N) (hX : 0 < X)
    (hh : 0 < h) (hb : h ≤ b) (hspare : 4*h ≤ X) :
    let T := windowTime N X
    let M := clockCount T 2 h
    M*h*2 ≥ T ∧ 0 < M ∧
      (ceilRatio (6*X) b:ℝ)*Real.log N / M ≤ 2 := by
  let T := windowTime N X
  let M := clockCount T 2 h
  let D := ceilRatio (6*X) b
  let L := Real.log (2*(N:ℝ))
  have ht := (run_width hX hN).2.1
  change 2*X ≤ T at ht
  have hc := count_cover (t:=T) (q:=2) hh (by omega)
  change M*h+2*h ≤ T ∧ T < M*h+3*h at hc
  have hMh : T ≤ M*h*2 := by omega
  have hM : 0 < M := by
    by_contra! hzero
    have ee : M = 0 := by omega
    rw [ee,Nat.zero_mul,Nat.zero_mul] at hMh
    omega
  refine ⟨hMh,hM,?_⟩
  have hD : D*h ≤ 7*X := by
    by_cases he : D=0
    · simp [he]
    have lo := (ceilRatio_spec (a:=6*X) (hh.trans_le hb)).2
    change D*b ≤ 6*X+b at lo
    have hh' := Nat.mul_le_mul_left (D-1) hb
    have heq (t : ℕ) : D*t = (D-1)*t+t := by
      rw [← Nat.succ_mul]; congr 1; omega
    rw [heq b] at lo
    rw [heq h]
    omega
  have hh' : (0:ℝ) < h := by exact_mod_cast hh
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hD' : (D:ℝ)*h ≤ 7*X := by exact_mod_cast hD
  have hT' : (T:ℝ) ≤ M*h*2 := by exact_mod_cast hMh
  have hT : 8*(X:ℝ)*L ≤ T := Nat.le_ceil _
  have ln0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hl : Real.log N ≤ L := Real.log_le_log hn (by linarith)
  apply (div_le_iff₀ hM').mpr
  apply (mul_le_mul_iff_left₀ hh').mp
  nlinarith only [hT,hT',mul_le_mul_of_nonneg_right hl (show 0 ≤ (7:ℝ)*X by positivity),
    mul_le_mul_of_nonneg_right hD' ln0,
    mul_nonneg (Nat.cast_nonneg (α:=ℝ) X) (ln0.trans hl)]

end
end Meyniel.Multiscale
