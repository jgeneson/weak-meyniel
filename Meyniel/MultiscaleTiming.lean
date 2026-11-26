module

public import Meyniel.MultiscaleGrowth
public import Meyniel.MultiscaleBands

/-! # Deployment and support estimates for the hierarchy of clocks -/

@[expose] public section

namespace Meyniel.Multiscale
open Filter
noncomputable section

def windowTime (N X : ℕ) : ℕ := ⌈8*(X:ℝ)*Real.log (2*N)⌉₊
def bandWidth (N s : ℕ) : ℕ := ⌈1000*(s:ℝ)*Real.log (2*N)⌉₊

def duration (C r : ℕ) : ℕ := C*r
def leadTime (C r : ℕ) : ℕ := 2*duration C r+3*r
def moveTime (C r : ℕ) : ℕ := leadTime C r+2*r
def endTime (C r : ℕ) : ℕ := 2*leadTime C r+moveTime C r

theorem endTime_bound (δ : ℝ) (r : ℕ) :
    2 * endTime (clockFactor δ) r + r ≤ dilation δ * r := by
  unfold endTime moveTime leadTime duration dilation
  ring_nf
  omega

theorem run_width {N s : ℕ} (hs : 1 ≤ s) (hN : 2 ≤ N) :
    3 * windowTime N s + s < bandWidth N s ∧
      2*s ≤ windowTime N s ∧
      (windowTime N s : ℝ) ≤ 9*s*Real.log (2*N) ∧
      (bandWidth N s : ℝ) ≤ 1001*s*Real.log (2*N) := by
  have hn : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hfour : Real.log 4 ≤ Real.log (2*(N:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
  have hl4 : (1:ℝ) ≤ Real.log 4 := by
    rw [show (4:ℝ)=2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9]
  let L := Real.log (2*(N:ℝ))
  have hL : 1 ≤ L := hl4.trans hfour
  have hs' : 1 ≤ (s:ℝ) := by exact_mod_cast hs
  have hprod : 1 ≤ (s:ℝ)*L := one_le_mul_of_one_le_of_one_le hs' hL
  have hL0 : 0 ≤ L := by linarith
  have hS : (s:ℝ) ≤ s*L := by simpa using mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg s)
  have hT : (windowTime N s : ℝ) < 8*(s:ℝ)*L+1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hw : (bandWidth N s : ℝ) < 1000*(s:ℝ)*L+1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hw' : 1000*(s:ℝ)*L ≤ (bandWidth N s : ℝ) := Nat.le_ceil _
  have hT' : 8*(s:ℝ)*L ≤ (windowTime N s : ℝ) := Nat.le_ceil _
  refine ⟨?_,?_,?_,?_⟩
  · exact_mod_cast (show (3:ℝ)*(windowTime N s : ℝ)+s < bandWidth N s by linarith)
  · exact_mod_cast (show (2:ℝ)*s ≤ windowTime N s by linarith)
  · change _ ≤ 9*(s:ℝ)*L; linarith
  · change _ ≤ 1001*(s:ℝ)*L; linarith

structure TimingFacts (δ : ℝ) (N i r : ℕ) : Prop where
  run_lt_lead : windowTime N (guardRadius δ N i) < leadTime (clockFactor δ) r
  first_deadline : 3*windowTime N (guardRadius δ N i)+guardRadius δ N i <
    bandWidth N (guardRadius δ N i)
  bottom_support : ((bandWidth N (guardRadius δ N i) + 3 : ℕ) : ℝ) * (N:ℝ)^gain δ ≤
    duration (clockFactor δ) r
  top_spare : 4 * leadTime (clockFactor δ) r ≤ windowTime N (cutoff N δ)
  child_lead : ∀ r' ∈ radii δ N (i-1), 1 < i →
    4 * leadTime (clockFactor δ) r' ≤ duration (clockFactor δ) r
  child_support : ∀ r' ∈ radii δ N (i-1), 1 < i →
    ((2*(leadTime (clockFactor δ) r' + bandWidth N (guardRadius δ N i) + 2 + 2*r') : ℕ) : ℝ) *
      (N:ℝ)^gain δ ≤ duration (clockFactor δ) r
  local_volume : ∀ r' ∈ radii δ N (i-1), 1 < i →
    2*guardRadius δ N i + windowTime N (guardRadius δ N i) + r' ≤ outerRadius δ N i

theorem timingFacts_eventually {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) :
    ∀ᶠ N : ℕ in atTop, ∀ i, 1 ≤ i → i ≤ levels δ → ∀ r ∈ radii δ N i, TimingFacts δ N i r := by
  let C := clockFactor δ
  let K : ℝ := 100000*((C:ℝ)+1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hC0 : (100000:ℝ) * ((levels δ:ℝ)+1) / δ ≤ C := Nat.le_ceil _
  have hC : (1:ℝ) ≤ C := by
    apply le_trans _ hC0; apply (le_div_iff₀ hδ).mpr
    linarith [Nat.cast_nonneg (α:=ℝ) (levels δ)]
  have hC' : 1 ≤ C := by exact_mod_cast hC
  filter_upwards [scaleSeparation_eventually hδ ht hK 1, eventually_ge_atTop (2:ℕ)] with N sep hN i hi hk r hr
  let s := guardRadius δ N i
  let w := bandWidth N s
  let T := windowTime N s
  let L := Real.log (2*(N:ℝ))
  let H := (N:ℝ)^gain δ
  have hn : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : 1 ≤ N := by omega
  have hL : 1 ≤ L := by
    have hx : Real.log (2*2) ≤ L := Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_mul (by norm_num) (by norm_num)] at hx; linarith [Real.log_two_gt_d9]
  have H1 : 1 ≤ H := Real.one_le_rpow (by linarith) (gain_pos hδ ht).le
  simp only [pow_one] at sep
  have hs : 1 ≤ s := by
    apply Nat.ceil_pos.mpr
    exact Real.rpow_pos_of_pos (by linarith) _
  obtain ⟨hdead,_,hT,hw⟩ := run_width hs hN
  change (T:ℝ) ≤ 9*(s:ℝ)*L at hT
  change (w:ℝ) ≤ 1001*(s:ℝ)*L at hw
  have hs1 : 1 ≤ (s:ℝ) := by exact_mod_cast hs
  have hsL := one_le_mul_of_one_le_of_one_le hs1 hL
  have hsL' : (s:ℝ) ≤ s*L := by simpa using mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)
  have sup := sep.support i hi hk r hr
  change K*L*s*H ≤ r at sup
  have Hpos : 0 ≤ H := by linarith
  have supp : (10000*(s:ℝ)*L)*H ≤ r := by
    apply le_trans _ sup
    apply mul_le_mul_of_nonneg_right _ Hpos
    dsimp [K]
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) C) (show 0 ≤ (s:ℝ)*L by linarith),hsL]
  have sup0 : 10000*(s:ℝ)*L ≤ r := by
    apply le_trans _ supp
    simpa using (mul_le_mul_of_nonneg_left H1 (by positivity : 0 ≤ 10000*(s:ℝ)*L))
  have tr : (r:ℝ) ≤ duration C r := by dsimp [duration]; exact_mod_cast Nat.le_mul_of_pos_left r hC'
  have child {r' : ℕ} (hr' : r' ∈ radii δ N (i-1)) (hii : 1 < i) :
      (4*(leadTime C r' : ℝ)+2*r') ≤ s := by
    have hidx : i-1+1 = i := by omega
    have hchild := sep.adjacent (i-1) (by omega) (by omega) r' hr'
    rw [hidx] at hchild
    change K*L*r' ≤ s at hchild
    have h1 : K*(r':ℝ) ≤ K*L*r' := by gcongr; simpa using (mul_le_mul_of_nonneg_left hL hK.le)
    dsimp [leadTime,duration]; push_cast
    refine (le_trans ?_ h1).trans hchild
    dsimp [K]; nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) C) (Nat.cast_nonneg (α:=ℝ) r'), Nat.cast_nonneg (α:=ℝ) r']
  refine ⟨?_,hdead,?_,?_,?_,?_,?_⟩
  · change T < leadTime C r
    have : (T:ℝ) < r := by linarith
    have : T < r := by exact_mod_cast this
    unfold leadTime; omega
  · change ((w+3 : ℕ):ℝ)*H ≤ duration C r
    push_cast
    exact (mul_le_mul_of_nonneg_right (by linarith) Hpos).trans (supp.trans tr)
  · have htop := sep.top i hi hk r hr
    change K*L*r ≤ (cutoff N δ : ℝ) at htop
    have hQ : (cutoff N δ : ℝ) ≤ windowTime N (cutoff N δ) := by
      have hqt : 0 ≤ (cutoff N δ : ℝ) := Nat.cast_nonneg _
      calc _ ≤ 8*(cutoff N δ:ℝ)*L := by nlinarith [mul_nonneg hqt (sub_nonneg.mpr hL)]
           _ ≤ _ := Nat.le_ceil _
    apply Nat.cast_le (α:=ℝ) |>.mp
    push_cast
    refine (le_trans ?_ htop).trans hQ
    dsimp [K,leadTime,duration]; push_cast
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) r) (sub_nonneg.mpr hL),
      mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℝ) r) (Nat.cast_nonneg (α:=ℝ) C)) (sub_nonneg.mpr hL),
      Nat.cast_nonneg (α:=ℝ) r, mul_nonneg (Nat.cast_nonneg (α:=ℝ) r) (Nat.cast_nonneg (α:=ℝ) C)]
  · intro r' hr' hii
    have hh := child hr' hii
    exact_mod_cast (show 4*(leadTime C r' :ℝ) ≤ duration C r by linarith [Nat.cast_nonneg (α:=ℝ) r'])
  · intro r' hr' hii
    have hh := child hr' hii
    change ((2*(leadTime C r'+w+2+2*r') : ℕ):ℝ)*H ≤ duration C r
    push_cast
    apply le_trans _ (supp.trans tr)
    apply mul_le_mul_of_nonneg_right _ Hpos
    linarith [Nat.cast_nonneg (α:=ℝ) (leadTime C r')]
  · intro r' hr' hii
    have hh := child hr' hii
    have hR := (radii_bounds hδ ht hn1 hi hk hr).2
    have hA : (1:ℝ) ≤ dilation δ := by dsimp [dilation]; norm_cast; omega
    have hβ : 0 ≤ (N:ℝ)^maxRadiusExp δ i := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hO : (r:ℝ) ≤ outerRadius δ N i := by
      calc _ ≤ (N:ℝ)^maxRadiusExp δ i := hR
           _ ≤ (dilation δ :ℝ)*(N:ℝ)^maxRadiusExp δ i := by simpa using mul_le_mul_of_nonneg_right hA hβ
           _ ≤ _ := Nat.le_ceil _
    change 2*s+T+r' ≤ _
    exact_mod_cast (show 2*(s:ℝ)+T+r' ≤ (outerRadius δ N i :ℝ) by
      linarith [Nat.cast_nonneg (α:=ℝ) (leadTime C r'),Nat.cast_nonneg (α:=ℝ) r'])

/-- All root clocks have stride at most a quarter of the relevant window scale. -/
theorem root_radius_spare {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) :
    ∀ᶠ N : ℕ in atTop, ∀ i, 1 ≤ i → i ≤ levels δ → ∀ r ∈ radii δ N i,
      4*leadTime (clockFactor δ) r ≤ cutoff N δ ∧
      (i < levels δ → 4*leadTime (clockFactor δ) r ≤ guardRadius δ N (i+1)) := by
  let c : ℝ := 4*(2*(clockFactor δ:ℝ)+3)
  have hC : 0 < c := by dsimp [c]; positivity
  filter_upwards [scaleSeparation_eventually hδ ht hC 0] with N sep i hi hk r hr
  simp only [pow_zero,mul_one] at sep
  have eq : (4:ℝ)*leadTime (clockFactor δ) r = c*r := by
    dsimp [c,leadTime,duration]; push_cast; ring
  refine ⟨?_,?_⟩
  · exact_mod_cast (show (4:ℝ)*leadTime (clockFactor δ) r ≤ cutoff N δ by rw [eq]; exact sep.top _ hi hk r hr)
  · intro hi'; exact_mod_cast (show (4:ℝ)*leadTime (clockFactor δ) r ≤ guardRadius δ N (i+1) by
      rw [eq]; exact sep.adjacent _ hi hi' r hr)

/-- The bottom window also has room for the endpoint ball and its full run. -/
theorem local_start_radius {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) :
    ∀ᶠ N : ℕ in atTop, ∀ i, 1 ≤ i → i ≤ levels δ →
      2*guardRadius δ N i + windowTime N (guardRadius δ N i) ≤ outerRadius δ N i := by
  obtain ⟨c,hc,many⟩ := many_radii hδ ht
  filter_upwards [many,scaleSeparation_eventually hδ ht (K:=20) (by norm_num) 1,
    eventually_ge_atTop 2] with N hm sep hN i hi hk
  have hn : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : 1 ≤ N := by omega
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hcard := hm i hi hk
  have rpos : (0:ℝ) < (radii δ N i).card := (mul_pos hc hl).trans_le hcard
  obtain ⟨r,hr⟩ := Finset.card_pos.mp (show 0 < (radii δ N i).card by exact_mod_cast rpos)
  let s := guardRadius δ N i
  have hs : 1 ≤ s := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)
  have hT := (run_width hs hN).2.2.1
  have sup := sep.support _ hi hk r hr
  rw [pow_one] at sup
  have hH := Real.one_le_rpow (by linarith : (1:ℝ) ≤ N) (gain_pos hδ ht).le
  have hL : 1 ≤ Real.log (2*(N:ℝ)) := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2*2) (by linarith : (2:ℝ)*2 ≤ 2*N)
    rw [Real.log_mul (by norm_num) (by norm_num)] at hh; linarith [Real.log_two_gt_d9]
  have hsr : (20:ℝ)*Real.log (2*N)*s ≤ r := by
    apply le_trans _ sup
    simpa using mul_le_mul_of_nonneg_left hH (show 0 ≤ (20:ℝ)*Real.log (2*N)*s by positivity)
  have hsmall : 2*s+windowTime N s ≤ r := by
    exact_mod_cast (show (2:ℝ)*s+windowTime N s ≤ r by
      nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) s) (sub_nonneg.mpr hL)])
  apply hsmall.trans
  have ub := (radii_bounds hδ ht hn1 hi hk hr).2
  have hA : (1:ℝ) ≤ dilation δ := by dsimp [dilation]; norm_cast; omega
  apply Nat.cast_le (α:=ℝ) |>.mp
  calc
    _ ≤ (N:ℝ)^maxRadiusExp δ i := ub
    _ ≤ (dilation δ:ℝ)*(N:ℝ)^maxRadiusExp δ i := by
      simpa using mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (Nat.cast_nonneg N) (maxRadiusExp δ i))
    _ ≤ _ := Nat.le_ceil _

end
end Meyniel.Multiscale
