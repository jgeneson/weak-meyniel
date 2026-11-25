import Meyniel.MultiscaleTeams
import Meyniel.MultiscaleBudget
import Meyniel.MultiscaleDeployment

/-! # From multiscale window estimates to the cop number

This module constructs the sites, teams, staggering, nested deadlines and reserve,
then iterates the square-graph recurrence and applies geodesic guarding.
-/

namespace Meyniel.Multiscale
open Finset Filter
universe u
noncomputable section

/-- A common deadline spacing accommodates every base radius. -/
theorem deadline_space {δ : ℝ} (hδ : 0<δ) (ht : δ<1/100) :
    ∀ᶠ N : ℕ in atTop, ∀ i : Fin (levels δ),
      guardRadius δ N (i.val+1) ≤ windowTime N (cutoff N δ) / levels δ := by
  obtain ⟨c,hc,many⟩ := many_radii hδ ht
  let k := levels δ
  have hk : 0<k := levels_pos hδ
  filter_upwards [scaleSeparation_eventually hδ ht (K:=(k:ℝ)+1) (by positivity) 0,
    many,eventually_ge_atTop 2] with N sep hmany hN i
  simp only [pow_zero,mul_one] at sep
  have hn : (1:ℝ) < N := by exact_mod_cast hN
  have mass := (mul_pos hc (Real.log_pos hn)).trans_le (hmany (i.val+1) (by omega) i.isLt)
  have mass' : 0 < (radii δ N (i.val+1)).card := by exact_mod_cast mass
  obtain ⟨r,hr⟩ := Finset.card_pos.mp mass'
  have support := sep.support (i.val+1) (by omega) i.isLt r hr
  have top := sep.top (i.val+1) (by omega) i.isLt r hr
  have gain := Real.one_le_rpow hn.le (gain_pos hδ ht).le
  let s := guardRadius δ N (i.val+1)
  have skirt : (k:ℝ)*s ≤ r := by
    change _*s*(N:ℝ)^_ ≤ _ at support
    nlinarith only [support,mul_le_mul_of_nonneg_left gain
      (show 0 ≤ ((k:ℝ)+1)*s by positivity),Nat.cast_nonneg (α:=ℝ) s]
  have rad : (r:ℝ) ≤ cutoff N δ := by nlinarith only [top,mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (Nat.cast_nonneg (α:=ℝ) r)]
  have prod : k*s ≤ cutoff N δ := by exact_mod_cast skirt.trans rad
  have qpos : 1 ≤ cutoff N δ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)
  have w := (run_width qpos hN).2.1
  apply (Nat.le_div_iff_mul_le hk).mpr
  simpa [Nat.mul_comm] using (prod.trans (by omega : cutoff N δ ≤ windowTime N (cutoff N δ)))

private theorem deadline_arithmetic {k W : ℕ} (base : Fin k → ℕ) (hb : ∀ l, base l ≤ W/k) :
    let lim (l : Fin k) := W + (k-1-l.val)*(W/k)
    (∀ l, W ≤ lim l ∧ lim l ≤ 2*W ∧ lim l + base l ≤ 3*W) ∧
    (∀ l m, m<l → lim l + base l ≤ lim m) := by
  let spacing := W/k
  have total : k*spacing ≤ W := by simpa [spacing,Nat.mul_comm] using (Nat.div_mul_le_self W k)
  constructor
  · intro l
    have small := Nat.mul_le_mul_right spacing (show k-1-l.val ≤ k by omega)
    have rel := hb l
    have spos : spacing ≤ W := Nat.div_le_self .. 
    dsimp; change _ ∧ W+_*spacing ≤ _ ∧ W+_*spacing+_ ≤ _
    change _ ≤ spacing at rel
    omega
  · intro l m h
    have lt' : m.val < l.val := h
    have small := Nat.mul_le_mul_right spacing (show k-1-l.val+1 ≤ k-1-m.val by omega)
    rw [Nat.add_mul,Nat.one_mul] at small
    have rel := hb l
    change _ ≤ spacing at rel
    dsimp; change W+_*spacing+_ ≤ W+_*spacing
    omega

/-- The physical game on a fixed graph, including the initial square search. -/
private theorem deploy_graph {δ : ℝ} {N k : ℕ} (hN : 2 ≤ N)
    (win : ConstantWindows.{u} δ N) (V : Type u) [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected) (hsize : Fintype.card V ≤ N) (hd : G.diam ≤ cutoff N δ)
    (sq : WinsWith (SquareTrail.square G) k)
    (space : ∀ i : Fin (levels δ), guardRadius δ N (i.val+1) ≤ windowTime N (cutoff N δ)/levels δ)
    (budget : ∀ R, SpeedOne G R → ∑ a : SiteIndex G δ N, activeJobs G δ N R a ≤ physicalBudget δ N) :
    WinsWith G (k + (physicalBudget δ N + globalCount δ N)) := by
  classical
  let q := physicalScale G δ N
  let W := windowTime N (cutoff N δ)
  let kL := levels δ
  let I := SiteIndex G δ N
  let lim (l : Fin kL) := W+(kL-1-l.val)*(W/kL)
  let base (l : Fin kL) := (q l).base
  have hs (l : Fin kL) : 0 < (q l).base := by
    apply Nat.ceil_pos.mpr
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0<N by omega)) _
  have widths (l : Fin kL) := run_width (hs l) hN
  obtain ⟨global,global_covers⟩ := global_team (show 0<N by omega) hc hsize hd win
  have loc (a : I) := local_team (show 0<N by omega) hc hsize hd win a.1 a.2.2.val
    ((net_spec G δ N a.1).1 _ a.2.2.property)
  let site (a : I) : Deployment.Site q G := {
    level := a.1
    radius := a.2.1.val
    center := a.2.2.val
    count := siteCount δ N (a.1.val+1) (ball G a.2.2.val ((q a.1).base/4)).card
    copies := staggeredCopies N (q a.1).base
    policy := (loc a).choose
    period := by
      let s := (q a.1).base
      let T := (q a.1).run
      have h := copies_do_not_overlap T s (hs a.1)
      have spos : 0<s := hs a.1
      change 2*T < (6*T/s+2)*s
      rw [Nat.add_mul] at h ⊢; omega
    start_near := (loc a).choose_spec.1 }
  have deadlines := deadline_arithmetic base space
  have cover : Deployment.WindowCovers q site global lim W (2*W) (3*W) (physicalBudget δ N) := {
    global_end := by omega
    limits := deadlines.1
    slack := by
      intro l
      have width := widths l
      change 3*(q l).run+ (q l).base < (q l).width ∧ 2*(q l).base ≤ (q l).run ∧ _ at width
      exact ⟨hs l,by have := hs l; omega,width.1.le⟩
    nested := deadlines.2
    centers := by
      intro l r hr y hy
      obtain ⟨z,hz,hclose⟩ := (net_spec G δ N l).2.2 y hy
      exact ⟨⟨l,(⟨r,hr⟩,⟨z,hz⟩)⟩,rfl,rfl,hclose⟩
    local_cover := fun i => (loc i).choose_spec.2
    global_cover := global_covers
    cost := by
      intro R hR
      apply le_trans _ (budget R hR)
      apply Finset.sum_le_sum
      intro a _
      split_ifs with h
      · obtain ⟨t,_,ha⟩ := h
        have ha' := of_decide_eq_true ha
        have trig : ∃ t ≤ 2*W, G.dist (R t) (site a).center ≤
          (q (site a).level).last (site a).radius+2*(q (site a).level).base := ⟨t,ha'⟩
        unfold activeJobs
        exact le_of_eq (if_pos trig).symm
      · exact Nat.zero_le _ }
  simpa only [Nat.add_assoc] using Deployment.winsWith_windows hc cover sq

theorem step_of_windows {δ : ℝ} (hδ : 0<δ) (ht : δ<1/100) :
    ∀ᶠ N : ℕ in atTop, ConstantWindows.{u} δ N →
      DiameterStep.{u} N (cutoff N δ) (physicalBudget δ N + globalCount δ N) := by
  filter_upwards [deadline_space hδ ht,activeJobs_bound.{u} hδ ht,eventually_ge_atTop 2]
    with N space cost hN windows d _ hd k half V _ G hc card diam
  have sd := SquareTrail.diameter_square hc
  have target : (SquareTrail.square G).diam ≤ (d+1)/2 :=
    sd.trans (Nat.div_le_div_right (Nat.add_le_add_right diam 1))
  exact deploy_graph hN windows V G hc card (diam.trans hd)
    (half V _ (SquareTrail.connected_square hc) card target) space (cost V G hc card)

/-- One (N^{2/3+\varepsilon}) bound for all finite connected graphs, for
each fixed positive exponent slack, from the two uniform window estimates. -/
theorem two_thirds_of_windows
    (windows : ∀ δ : ℝ, 0<δ → δ<1/100 → ∀ᶠ N : ℕ in atTop, ConstantWindows.{u} δ N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ C*(Fintype.card V : ℝ)^(2/3+ε) := by
  apply two_thirds_of_step _ ε hε
  intro δ hδ ht
  have ready := (windows δ hδ ht).and ((step_of_windows hδ ht).and (final_additive_cost hδ ht))
  obtain ⟨n₀,hn⟩ := eventually_atTop.1 ready
  exact ⟨5,by norm_num,n₀,fun N hN => ⟨_,(hn N hN).2.2,(hn N hN).2.1 (hn N hN).1⟩⟩

end
end Meyniel.Multiscale
