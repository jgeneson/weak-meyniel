import Meyniel.TrialSupport
import Meyniel.TrialMixtures
import Meyniel.MultiscaleUnitWindow
import Meyniel.MultiscaleTrialPrice

/-! Correct-terminal trials on a physical interval. -/
namespace Meyniel.Multiscale
open Finset Interception
open scoped Classical
noncomputable section
variable {V W : Type*} [Fintype V] [Fintype W] [Nonempty W] {G : SimpleGraph V}

omit [Fintype V] [Fintype W] [Nonempty W] in
theorem window_weaken {R : W → ℕ → V} {a t : ℕ} {P Q : V → Prop} {c d : W → ℝ}
    (m : WindowMixture G R a t P c) (sites : ∀ y, P y → Q y) (price : ∀ w, c w ≤ d w) :
    WindowMixture G R a t Q d := by
  classical
  obtain ⟨m,hm⟩ := m
  let f : {s : WindowPolicy G // P s.start} → {s : WindowPolicy G // Q s.start} :=
    fun s => ⟨s.1,sites _ s.2⟩
  exact ⟨m.map' f,fun w => ((Real.exp_le_exp.mpr (neg_le_neg (price w))).trans (hm w)).trans
    (m.map_success_le f _ _ w (fun _ h => h))⟩

private theorem bottom_cost {t r C : ℕ} {cond sum L : ℝ}
    (hC : 0 < C) (hr : 0 < r) (ht : t=C*r) (hsum : 0 ≤ sum)
    (bound : sum ≤ t*cond) (hL : 0 ≤ L) :
    (sum+r*L)/(2*(t:ℝ)+1) ≤ cond/2+L/C := by
  have ht0 : 0 < t := ht ▸ Nat.mul_pos hC hr
  have ht' : (0:ℝ) < t := by exact_mod_cast ht0
  have hc' : (0:ℝ) < C := by exact_mod_cast hC
  have hcond := nonneg_of_mul_nonneg_right (hsum.trans bound) ht'
  have htC : (t:ℝ)=(C:ℝ)*r := by exact_mod_cast ht
  have cost0 := div_nonneg hL hc'.le
  have rid : (L/C)*(t:ℝ) = r*L := by rw [htC]; field_simp
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [bound,cost0,hcond,rid,mul_nonneg cost0 ht'.le]

/-- A bottom correct terminal: a fair coin purchases the radial incidence
saving precisely on walks with a good endpoint. -/
theorem bottom_window (hc : G.Connected) (R : W → ℕ → V) (a F r N C width : ℕ)
    (z x : V) (g : ℝ) (hn : Fintype.card V ≤ N) (hN : 0 < N) (hC : 0 < C) (hr : 0 < r)
    (hFa : F ≤ a) (speed : ∀ w, SpeedOne G (R w)) (anchor : ∀ w, R w F = x)
    (ends : ∀ w, G.dist z (R w (a+2+C*r)) ≤ r) (good : W → Prop)
    (band : ∀ w, good w → InBand G (R w) F (a+C*r) width)
    (saving : ((width+3 : ℕ) : ℝ)*(N:ℝ)^g ≤ C*r) :
    WindowMixture G R a (C*r) (fun y => y ∈ ball G z (r+C*r)) (fun w =>
      Real.log (ball G z (r+C*r)).card / 2 + Real.log N/C -
      (if good w then g*Real.log N/2 else 0) + Real.log 2) := by
  classical
  let t := C*r
  let A := ball G z (r+t)
  let hit (s : {s : WindowPolicy G // s.start ∈ A}) w := windowHit s.1 (R w) a t
  let base := Real.log A.card/2+Real.log N/C
  have ht : 0 < t := Nat.mul_pos hC hr
  have hlN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have inside j (hj : j<t) (w : W) : R w (a+2+j) ∈ A := by
    apply mem_ball.mpr
    have tri := hc.dist_triangle (u:=z) (v:=R w (a+2+t)) (w:=R w (a+2+j))
    rw [@SimpleGraph.dist_comm _ G (R w (a+2+t)) (R w (a+2+j))] at tri
    have d := displacement hc (speed w) (u:=a+2+j) (v:=a+2+t) (by omega)
    have hnear := ends w
    change G.dist z (R w (a+2+t)) ≤ r at hnear
    omega
  obtain ⟨m,hm⟩ := unit_window hc R a t r N z hn speed ends (fun _ => A) inside
  have La : 0 ≤ Real.log A.card := Real.log_nonneg (by exact_mod_cast (ball_nonempty (G:=G) z _).card_pos)
  have ordinary w : Real.exp (-base) ≤ m.success hit w := by
    apply (Real.exp_le_exp.mpr (neg_le_neg ?_)).trans (hm w)
    simp only [sum_const,card_range,nsmul_eq_mul]
    exact bottom_cost hC hr rfl (mul_nonneg (Nat.cast_nonneg _) La) le_rfl hlN
  apply combine_good hit (fun _ => base) good (g*Real.log N/2) m ordinary
  intro hgood
  letI := hgood
  let R' := fun w : {w // good w} => R w.1
  let S := radialSupport G A x (a-F) 1 width 0
  have member (j : ℕ) (hj : j<t) (w : {w // good w}) : R' w (a+2+j) ∈ S j := by
    apply mem_filter.mpr
    refine ⟨inside j hj w.1,?_⟩
    have h := radial_at hc (R:=R w.1) (j:=j) (h:=1) (smoothing:=0) hFa
      (e:=a+t) (by omega) (anchor _) (band _ w.2) (z:=R w.1 (a+j+2)) (by simp)
    simpa [R',Nat.add_right_comm a 2 j] using h
  obtain ⟨mb,hb⟩ := unit_window hc R' a t r N z hn (fun w => speed w.1) (fun w => ends w.1) S member
  refine ⟨mb,fun w hw => ?_⟩
  apply (Real.exp_le_exp.mpr (neg_le_neg ?_)).trans (hb ⟨w,hw⟩)
  have pos j (hj : j<t) : (S j).Nonempty := ⟨_,member j hj (Classical.arbitrary _)⟩
  have tot := radial_log_saving (G:=G) A x (M:=t) (N:=N) (a-F) 1 width 0 g (by decide) ht hN pos
    (by simpa [t,Nat.add_assoc] using saving)
  have nonneg : 0 ≤ ∑ j ∈ range t, Real.log (S j).card := sum_nonneg (fun j hj =>
    Real.log_nonneg (by exact_mod_cast (pos j (mem_range.mp hj)).card_pos))
  have res := bottom_cost hC hr (t:=t) rfl nonneg tot hlN
  dsimp only [base]
  linarith
end
end Meyniel.Multiscale
