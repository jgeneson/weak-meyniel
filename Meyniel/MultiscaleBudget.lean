import Meyniel.MultiscaleTeamSize

/-! # The fixed pool sufficient for all realized guard assignments -/

namespace Meyniel.Multiscale
open Filter Finset
noncomputable section

private theorem log_bound {N : ℕ} (hN : 2 ≤ N) : 1 ≤ Real.log (2*(N:ℝ)) := by
  have hn : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hh := Real.log_le_log (by norm_num : (0:ℝ)<2*2) (by linarith : (2:ℝ)*2 ≤ 2*N)
  rw [Real.log_mul (by norm_num) (by norm_num)] at hh; linarith [Real.log_two_gt_d9]

theorem radii_card_upper {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) {N i : ℕ}
    (hN : 2 ≤ N) (hi : 1 ≤ i) (hk : i ≤ levels δ) :
    ((radii δ N i).card:ℝ) ≤ 3 * Real.log (2*N) := by
  let b := radiusBase δ
  let α := minRadiusExp δ i; let β := maxRadiusExp δ i
  let n : ℝ := N
  have hn : (2:ℝ) ≤ n := by dsimp [n]; exact_mod_cast hN
  have hβ := radius_exponents hδ ht i hi hk
  have hβ0 : 0 ≤ β := (hβ.1.trans (hβ.2.1.trans hβ.2.2.1)).le
  have hβ1 : β ≤ 1 := by change maxRadiusExp δ i ≤ 1; linarith [hβ.2.2.2]
  have hbase : (2:ℝ) ≤ b := by exact_mod_cast radiusBase_ge δ
  have hlb : 1/2 ≤ Real.log b := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<2) hbase
    linarith [Real.log_two_gt_d9]
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have logBound : Real.logb b n ≤ 2*Real.log n := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log b)).mpr
    nlinarith [mul_nonneg hlogn (sub_nonneg.mpr hlb)]
  have hl : Real.log n ≤ Real.log (2*n) := Real.log_le_log (by linarith) (by linarith)
  have h1 := log_bound hN
  have logbPos : 0 ≤ Real.logb b n := Real.logb_nonneg (by linarith) (by linarith)
  let m := ⌊β * Real.logb b n⌋₊
  have hm : (m:ℝ) ≤ Real.logb b n := (Nat.floor_le (mul_nonneg hβ0 logbPos)).trans
    (by simpa using mul_le_mul_of_nonneg_right hβ1 logbPos)
  have hcard : (radii δ N i).card ≤ m+1 := by
    unfold radii geometricRange
    apply Finset.card_image_le.trans
    rw [indices,Nat.card_Icc]; exact Nat.sub_le _ _
  have hh := (Nat.cast_le (α:=ℝ)).mpr hcard
  push_cast at hh
  change _ ≤ 3*Real.log (2*n)
  change 1 ≤ Real.log (2*n) at h1
  linarith

/-- The realized cost, in the dependent-sum indexing used by dispatch. -/
def activeJobs {V : Type*} [Fintype V] (G : SimpleGraph V) (δ : ℝ) (N : ℕ)
    (R : ℕ → V) (s : SiteIndex G δ N) : ℕ := by
  classical
  let z := s.2.2.val
  let r := s.2.1.val
  let i := s.1
  let q := physicalScale G δ N i
  exact if ∃ t ≤ 2*windowTime N (cutoff N δ), G.dist (R t) z ≤ q.last r + 2*q.base then
    staggeredCopies N q.base * siteCount δ N (i.val+1) (ball G z (q.base/4)).card else 0

theorem activeJobs_bound {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) :
    ∀ᶠ N : ℕ in atTop, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V), G.Connected →
      Fintype.card V ≤ N → ∀ R, SpeedOne G R →
      ∑ a : SiteIndex G δ N, activeJobs G δ N R a ≤ physicalBudget δ N := by
  classical
  filter_upwards [pad_le hδ ht,eventually_ge_atTop 2] with N hpad hn V _ G hc hsize R hR
  let L := Real.log (2*(N:ℝ))
  let b : ℝ := 2/3-δ/4
  let Q := cutoff N δ
  let W := windowTime N Q
  have hL : 1 ≤ L := log_bound hn
  have charge (i : Fin (levels δ)) (r : radii δ N (i.val+1)) :
      ((∑ z : net G δ N i, activeJobs G δ N R ⟨i,(r,z)⟩:ℕ):ℝ) ≤ 16000*L^4*(N:ℝ)^b := by
    let j := i.val+1; let s := guardRadius δ N j
    have hrad := radii_bounds (i:=i.val+1) (r:=r.val) hδ ht (show 0<N by omega) (by omega) i.isLt r.property
    have hnp : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have rpos : 0 < r.val := by exact_mod_cast ((Real.rpow_pos_of_pos hnp _).trans_le hrad.1)
    have he := radius_charge δ hδ ht hn G hc hsize R hR i r.val r.property rpos (hpad i r.val r.property)
    let funZ (z : V) := if ∃ t ≤ 2*W, G.dist (R t) z ≤ endTime (clockFactor δ) r.val+2*s then
        staggeredCopies N s * siteCount δ N j (ball G z (s/4)).card else 0
    change ((∑ z : net G δ N i, funZ z.val:ℕ):ℝ) ≤ _
    rw [sum_coe_sort]
    dsimp only at he
    unfold triggered at he
    rw [sum_filter] at he
    exact he
  have costLevel (i : Fin (levels δ)) :
      ((∑ p : (radii δ N (i.val+1)) × (net G δ N i), activeJobs G δ N R ⟨i,p⟩ : ℕ):ℝ) ≤
        48000*L^5*(N:ℝ)^b := by
    rw [Fintype.sum_prod_type,Nat.cast_sum]
    calc
      _ ≤ ∑ _ : radii δ N (i.val+1), 16000*L^4*(N:ℝ)^b := sum_le_sum (fun r _ => charge i r)
      _ = ((radii δ N (i.val+1)).card:ℝ)*(16000*L^4*(N:ℝ)^b) := by simp
      _ ≤ (3*L)*(16000*L^4*(N:ℝ)^b) := by
        apply mul_le_mul_of_nonneg_right (radii_card_upper hδ ht hn (by omega) i.isLt)
        positivity
      _ = _ := by ring
  apply Nat.cast_le (α:=ℝ) |>.mp
  rw [Fintype.sum_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ _ : Fin (levels δ), 48000*L^5*(N:ℝ)^b := sum_le_sum (fun i _ => costLevel i)
    _ = (levels δ:ℝ)*(48000*L^5*(N:ℝ)^b) := by simp
    _ ≤ 50000*((levels δ:ℝ)+1)*L^5*(N:ℝ)^b := by
      have hp : 0 ≤ L^5*(N:ℝ)^b := by positivity
      nlinarith only [hp, mul_nonneg (Nat.cast_nonneg (α:=ℝ) (levels δ)) hp]
    _ ≤ _ := Nat.le_ceil _

theorem final_additive_cost {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) :
    ∀ᶠ N : ℕ in atTop, ((physicalBudget δ N + globalCount δ N:ℕ):ℝ) ≤
      5*(N:ℝ)^(2/3+δ/4) := by
  let K := 50000*((levels δ:ℝ)+1)
  have hK : 0<K := by dsimp [K]; positivity
  filter_upwards [polylog_le_power (show 0<δ/2 by linarith) hK 5,
    polylog_le_power (show 0 < δ/8 by linarith) (K:=21) (by norm_num) 2,
    eventually_ge_atTop 2] with N hp hg hN
  let n : ℝ := N
  let L := Real.log (2*n)
  let q : ℝ := 1/3-δ
  let p : ℝ := 1/2-(levels δ:ℝ)*gain δ/2+δ/20
  let v : ℝ := 2/3+δ/4
  have hn : (2:ℝ) ≤ n := by dsimp [n]; exact_mod_cast hN
  have hnp : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hL : 1 ≤ L := log_bound hN
  have h1 : 1 ≤ n^v := Real.one_le_rpow hn1 (by dsimp [v]; linarith)
  change K*L^5 ≤ n^(δ/2) at hp
  change 21*L^2 ≤ n^(δ/8) at hg
  have shield : (physicalBudget δ N:ℝ) ≤ n^v+1 := by
    have raw : K*L^5*n^(2/3-δ/4) ≤ n^v := by
      calc
        _ ≤ n^(δ/2)*n^(2/3-δ/4) := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hnp.le _)
        _ = _ := by rw [← Real.rpow_add hnp]; congr 1; dsimp [v]; ring
    change (⌈K*L^5*n^(2/3-δ/4)⌉₊:ℝ) ≤ _
    have he := Nat.ceil_lt_add_one (a:=K*L^5*n^(2/3-δ/4)) (by positivity)
    linarith
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hQ := Real.one_le_rpow hn1 hq
  have qpos : 1 ≤ cutoff N δ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnp _)
  have hT := (run_width qpos hN).2.2.1
  have qceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hnp.le q)
  change (cutoff N δ:ℝ) < n^q+1 at qceil
  change (windowTime N (cutoff N δ):ℝ) ≤ 9*(cutoff N δ:ℝ)*L at hT
  have term : (windowTime N (cutoff N δ):ℝ)+3 ≤ 21*n^q*L := by
    nlinarith only [hT, mul_le_mul_of_nonneg_right qceil.le (show 0 ≤ L by linarith),
      mul_le_mul_of_nonneg_right hQ (show 0 ≤ L by linarith),hL]
  have hln : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlnL : Real.log n ≤ L := Real.log_le_log hnp (by linarith)
  have logexp : δ/8 + (q+p) ≤ v := by
    have e := window_exponent hδ
    dsimp [q,p,v]; linarith
  have global : (globalCount δ N:ℝ) ≤ n^v+2 := by
    let A := ((windowTime N (cutoff N δ)+3 : ℕ):ℝ) * Real.log n * n^p
    have raw : A ≤ n^v := by
      calc
        _ ≤ (21*n^q*L)*L*n^p := by
          dsimp [A]; push_cast
          exact mul_le_mul_of_nonneg_right (mul_le_mul term hlnL hln (by positivity)) (Real.rpow_nonneg hnp.le p)
        _ = (21*L^2)*n^(q+p) := by rw [Real.rpow_add hnp q p]; ring
        _ ≤ n^(δ/8)*n^(q+p) := mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hnp.le _)
        _ ≤ n^v := by rw [← Real.rpow_add hnp]; exact Real.rpow_le_rpow_of_exponent_le hn1 logexp
    change ((⌈A⌉₊+1:ℕ):ℝ) ≤ _
    push_cast
    have he := Nat.ceil_lt_add_one (a:=A) (by dsimp [A]; positivity)
    linarith
  push_cast
  change _ ≤ 5*n^v
  linarith

end
end Meyniel.Multiscale
