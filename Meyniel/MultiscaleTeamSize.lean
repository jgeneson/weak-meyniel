module

public import Meyniel.MultiscaleBatches

/-! # The number of guards along a realized trail -/

@[expose] public section

noncomputable section
namespace Meyniel.Multiscale

open Finset Filter
variable {V : Type*} [Fintype V]

def batchExp (δ j : ℝ) := δ/100 + (1/3-δ) - minRadiusExp δ j
def siteExp (δ j : ℝ) := δ/200 - (j-1)*gain δ/2+δ/20
def physicalBudget (δ : ℝ) (N : ℕ) : ℕ :=
  ⌈50000 * ((levels δ:ℝ)+1) * Real.log (2*(N:ℝ))^5 * (N:ℝ)^(2/3-δ/4)⌉₊

private theorem log_ge_one {N : ℕ} (hN : 2 ≤ N) : 1 ≤ Real.log (2*(N:ℝ)) := by
  have hn : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hx := Real.log_le_log (by norm_num : (0:ℝ)<2*2) (by linarith : (2:ℝ)*2 ≤ 2*N)
  rw [Real.log_mul (by norm_num) (by norm_num)] at hx
  linarith [Real.log_two_gt_d9]

private theorem round_power {N : ℕ} (hN : 2 ≤ N) {e : ℝ} (he : 0 ≤ e) :
    1 ≤ ⌈(N:ℝ)^e⌉₊ ∧ ((⌈(N:ℝ)^e⌉₊ : ℕ):ℝ) ≤ 2*(N:ℝ)^e := by
  have hx : (2:ℝ) ≤ N := by exact_mod_cast hN
  have h := Real.one_le_rpow (by linarith : (1:ℝ) ≤ N) he
  exact ⟨Nat.ceil_pos.mpr (by linarith), by linarith [Nat.ceil_lt_add_one (show 0 ≤ (N:ℝ)^e by linarith)]⟩

/-- The exact per-site integer cover budget, with all staggered copies. -/
theorem site_size {δ : ℝ} {N j m : ℕ} (hN : 2 ≤ N) (hs : 1 ≤ guardRadius δ N j) :
    let s := guardRadius δ N j
    let L := Real.log (2*(N:ℝ))
    (staggeredCopies N s * siteCount δ N j m:ℕ) ≤
      (56*L)*(12*s*L^2 * (N:ℝ)^siteExp δ j * Real.sqrt m + 2 : ℝ) := by
  let s := guardRadius δ N j
  let L := Real.log (2*(N:ℝ))
  let T := windowTime N s
  let n : ℝ := N
  have hn : (2:ℝ) ≤ n := by dsimp [n]; exact_mod_cast hN
  have hL := log_ge_one hN
  change 1 ≤ L at hL
  have hs' : 1 ≤ (s:ℝ) := by exact_mod_cast hs
  have sL := one_le_mul_of_one_le_of_one_le hs' hL
  have hL' : Real.log n ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hT := (run_width hs hN).2.2.1
  change (T:ℝ) ≤ 9*s*L at hT
  have ht : (T:ℝ)+3 ≤ 12*s*L := by linarith
  have copies : (staggeredCopies N s : ℝ) ≤ 56*L := by
    have hdiv : (((6*T/s : ℕ) : ℝ)) ≤ 6*(T:ℝ)/s := by simpa using (show (((6*T/s:ℕ):ℝ)) ≤ ((6*T:ℕ):ℝ)/s from Nat.cast_div_le)
    have hh : 6*(T:ℝ)/s ≤ 54*L := (div_le_iff₀ (by linarith)).mpr (by linarith)
    dsimp [staggeredCopies]; push_cast
    change ((6*T/s : ℕ):ℝ)+2 ≤ 56*L
    linarith
  let U := (N:ℝ)^siteExp δ j
  have hU : 0 ≤ U := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have raw : ((T:ℝ)+3)*Real.log n*Real.sqrt m*U ≤ (12*s*L^2)*U*Real.sqrt m := by
    have h := mul_le_mul ht hL' hlog (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg m)) hU]
  have count : (siteCount δ N j m : ℝ) ≤ (12*s*L^2)*U*Real.sqrt m+2 := by
    let a := ((T+3 : ℕ):ℝ)*Real.log n*Real.sqrt m*U
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have ha : (⌈a⌉₊:ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
    change ((⌈a⌉₊ + 1 : ℕ):ℝ) ≤ _
    push_cast
    have raw' : a ≤ (12*s*L^2)*U*Real.sqrt m := by dsimp [a]; push_cast; exact raw
    linarith
  push_cast
  exact mul_le_mul copies count (Nat.cast_nonneg _) (by positivity)

private theorem number_batches {N j r : ℕ} {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100)
    (hN : 2 ≤ N) (hj : 1 ≤ j) (hk : j ≤ levels δ) (hr : r ∈ radii δ N j) :
    (((2*windowTime N (cutoff N δ))/r+1 : ℕ):ℝ) * (N:ℝ)^(δ/100) ≤
      40*Real.log (2*(N:ℝ))*(N:ℝ)^batchExp δ j := by
  let L := Real.log (2*(N:ℝ))
  let q : ℝ := 1/3-δ
  let a := minRadiusExp δ j
  let n : ℝ := N
  have hx : (2:ℝ) ≤ n := by dsimp [n]; exact_mod_cast hN
  have hxp : 0<n := by linarith
  have hL : 1 ≤ L := log_ge_one hN
  obtain ⟨_,_,h1,h2⟩ := radius_exponents hδ ht j hj hk
  have haq : a ≤ q := h1.le.trans h2.le
  have hE := Real.one_le_rpow (by linarith : 1 ≤ n) (sub_nonneg.mpr haq)
  have hgeo := (radii_bounds hδ ht (by omega) hj hk hr).1
  have hrpos : (0:ℝ)<r := (Real.rpow_pos_of_pos hxp _).trans_le hgeo
  obtain ⟨hQ,upper⟩ := round_power (e:=q) hN (by dsimp [q]; linarith)
  have hT := (run_width hQ hN).2.2.1
  change (windowTime N (cutoff N δ):ℝ) ≤ 9*(cutoff N δ:ℝ)*L at hT
  change (cutoff N δ:ℝ) ≤ 2*n^q at upper
  have bound : 2*(windowTime N (cutoff N δ):ℝ)/(r:ℝ) ≤ 36*L*n^(q-a) := by
    apply (div_le_iff₀ hrpos).mpr
    have div : n^q = n^(q-a)*n^a := by rw [← Real.rpow_add hxp]; congr 1; ring
    change n^a ≤ (r:ℝ) at hgeo
    nlinarith only [hT,mul_le_mul_of_nonneg_right upper (show 0≤L by linarith),
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeo (Real.rpow_nonneg hxp.le (q-a)))
        (show 0≤36*L by linarith),congrArg (fun z:ℝ => z*L) div]
  have bdiv : (((2*windowTime N (cutoff N δ))/r : ℕ):ℝ) ≤ 2*(windowTime N (cutoff N δ):ℝ)/r :=
    by simpa using (show (((2*windowTime N (cutoff N δ))/r:ℕ):ℝ) ≤ ((2*windowTime N (cutoff N δ):ℕ):ℝ)/r from Nat.cast_div_le)
  have count : ((((2*windowTime N (cutoff N δ))/r)+1:ℕ):ℝ) ≤ 40*L*n^(q-a) := by
    push_cast
    linarith [one_le_mul_of_one_le_of_one_le hL hE]
  apply (mul_le_mul_of_nonneg_right count (Real.rpow_nonneg (Nat.cast_nonneg N) (δ/100))).trans_eq
  change 40*L*n^(q-a)*n^(δ/100)=40*L*n^(δ/100+q-a)
  rw [mul_assoc,← Real.rpow_add hxp]
  congr 2; ring

set_option maxHeartbeats 650000 in
theorem radius_charge (δ : ℝ) (hδ : 0 < δ) (ht : δ < 1/100) {N : ℕ} (hN : 2 ≤ N)
    (G : SimpleGraph V) (hc : G.Connected) (hsize : Fintype.card V ≤ N)
    (R : ℕ → V) (hR : SpeedOne G R) (i : Fin (levels δ)) (r : ℕ)
    (hr : r ∈ radii δ N (i.val+1)) (hrpos : 0 < r)
    (pad : let j := i.val+1; 2*(endTime (clockFactor δ) r+2*guardRadius δ N j)+r+
      baseRadius δ N j ≤ outerRadius δ N j) :
    let j := i.val+1
    let s := guardRadius δ N j
    let L := Real.log (2*(N:ℝ))
    let D := triggered G R (2*windowTime N (cutoff N δ)) (endTime (clockFactor δ) r+2*s) (net G δ N i)
    ((∑ z ∈ D, staggeredCopies N s * siteCount δ N j (ball G z (s/4)).card : ℕ):ℝ) ≤
      16000*L^4*(N:ℝ)^(2/3-δ/4) := by
  classical
  let j := i.val+1
  let n : ℝ := N
  let s := guardRadius δ N j
  let L := Real.log (2*n)
  let D := triggered G R (2*windowTime N (cutoff N δ)) (endTime (clockFactor δ) r+2*s) (net G δ N i)
  let m (z : V) := (ball G z (s/4)).card
  let v := siteExp δ j
  let a := batchExp δ j
  let u := guardRadiusExp δ j
  let b : ℝ := 2/3-δ/4
  have hn : (2:ℝ) ≤ n := by dsimp [n]; exact_mod_cast hN
  have hnp : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hL : 1 ≤ L := log_ge_one hN
  have hL0 : 0 ≤ L := by linarith
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hjk : j ≤ levels δ := i.isLt
  obtain ⟨hu,ha,_,_⟩ := radius_exponents hδ ht j hj hjk
  obtain ⟨hs,hsc⟩ := round_power (e:=u) hN hu.le
  change (s:ℝ) ≤ 2*n^u at hsc
  have card : (D.card:ℝ) ≤ 40*L*n^a := by
    apply (triggered_card G hc R hR i r _ hrpos pad).trans
    exact number_batches hδ ht hN hj hjk hr
  have sumMass : ∑ z ∈ D, Real.sqrt (m z) ≤ 8*L*n^(a/2)*Real.sqrt n := by
    have hsep := (net_spec G δ N i).2.1
    have h := sqrt_base_mass_le hc (C:=D) (s:=s) (fun x hx y hy hxy =>
      hsep x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hxy)
    have sqrtCount : Real.sqrt (D.card:ℝ) ≤ 8*L*n^(a/2) := by
      apply (Real.sqrt_le_iff).mpr ⟨by positivity,?_⟩
      have sq : (n^(a/2))^2 = n^a := by rw [pow_two,← Real.rpow_add hnp]; congr 1; ring
      have hfac : 40*L ≤ (8*L)^2 := by nlinarith [(sq_nonneg (L-1))]
      rw [mul_pow,sq]; exact card.trans (mul_le_mul_of_nonneg_right hfac (Real.rpow_nonneg hnp.le a))
    exact h.trans (mul_le_mul sqrtCount (Real.sqrt_le_sqrt (by change (Fintype.card V:ℝ) ≤ (N:ℝ); exact_mod_cast hsize))
      (Real.sqrt_nonneg _) (by positivity))
  have sumper := sum_le_sum (s:=D) (fun z _ => site_size (m:=m z) hN hs)
  have sumEq : ∑ z ∈ D, (56*L)*(12*(s:ℝ)*L^2*n^v*Real.sqrt (m z)+2) =
      (56*L)*(12*s*L^2*n^v * (∑ z ∈ D, Real.sqrt (m z)) + 2*D.card) := by
    rw [← mul_sum,sum_add_distrib,← mul_sum]; simp [mul_comm]
  change ∑ z ∈ D, _ ≤ ∑ z ∈ D, (56*L)*(12*(s:ℝ)*L^2*n^v*Real.sqrt (m z)+2) at sumper
  rw [sumEq] at sumper
  have hExp : u+v+a/2+1/2 ≤ b := by
    have hh := guard_exponent hδ ht (show (j:ℝ) ≤ levels δ by exact_mod_cast hjk)
    dsimp [u,v,a,b,siteExp,batchExp]; linarith
  have hExp' : a ≤ b := by
    dsimp [a,b,batchExp]; linarith
  have hmain : 12*(s:ℝ)*L^2*n^v * (∑ z ∈ D, Real.sqrt (m z)) ≤ 192*L^3*n^b := by
    calc
      _ ≤ 12*(2*n^u)*L^2*n^v * (8*L*n^(a/2)*Real.sqrt n) := by
        apply mul_le_mul _ sumMass (sum_nonneg (fun _ _ => Real.sqrt_nonneg _)) (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hnp.le _)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hsc (by norm_num)
      _ = 192*L^3*(n^u*n^v*n^(a/2)*n^(1/2:ℝ)) := by rw [Real.sqrt_eq_rpow]; ring
      _ = 192*L^3*n^(u+v+a/2+1/2) := by rw [← Real.rpow_add hnp,← Real.rpow_add hnp,← Real.rpow_add hnp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hExp) (by positivity)
  have hcard' : (D.card:ℝ) ≤ 40*L*n^b := card.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hExp') (by positivity))
  change ((∑ z ∈ D, staggeredCopies N s * siteCount δ N j (m z) : ℕ):ℝ) ≤ 16000*L^4*n^b
  rw [Nat.cast_sum]
  apply sumper.trans
  have hpow : L ≤ L^3 := by nlinarith [sq_nonneg (L-1),mul_nonneg hL0 (sq_nonneg (L-1))]
  have posb : 0 ≤ n^b := Real.rpow_nonneg hnp.le _
  nlinarith only [mul_le_mul_of_nonneg_right (add_le_add hmain (mul_le_mul_of_nonneg_left hcard' (by norm_num : (0:ℝ)≤2))) (show 0 ≤ 56*L by positivity),
    mul_nonneg (mul_nonneg hL0 posb) (sub_nonneg.mpr hpow), mul_nonneg (pow_nonneg hL0 4) posb]

end Meyniel.Multiscale
