module

public import Meyniel.MultiscaleBallClock
public import Meyniel.MultiscaleQuotients
public import Meyniel.TrialMixtures

/-! Allowable starts and terminal root-column geometry in the global window
and in a window whose last robber vertex lies in a specified ball. -/

@[expose] public section

namespace Meyniel.Multiscale
open Finset Interception Clock Targets GraphClock
noncomputable section

variable {W V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The two root window types share these data. The support region includes
the closed target balls; the reachability condition covers all extension sites. -/
structure RootRegion (G : SimpleGraph V) (R : W → ℕ → V) (u T X rmax volume : ℕ) (starts : V → Prop) where
  home : V
  sites : Finset V
  sites_card : sites.card ≤ volume
  support : ∀ w t, t ≤ T → ∀ r ≤ rmax, ball G (R w (u+t+2)) r ⊆ sites
  start_of_mem : ∀ x ∈ sites, starts x
  retreat_start : ∀ w t, t ≤ T → ∀ r ≤ rmax, ∀ x, G.dist home x ≤ G.dist home (R w (u+t+2))+r → starts x
  final_near : ∀ w, G.dist home (R w (u+T+2)) ≤ 2*X

theorem global_region (hc : G.Connected) (R : W → ℕ → V) (u T X rmax N : ℕ)
    (hn : Fintype.card V ≤ N) (hd : G.diam ≤ X) : Nonempty (RootRegion G R u T X rmax N (fun _ => True)) := by
  classical
  letI : Nonempty V := hc.nonempty
  let z := Classical.choice hc.nonempty
  refine ⟨⟨z,univ,by simpa using hn,fun _ _ _ _ _ => subset_univ _,fun _ _ => trivial,
    fun _ _ _ _ _ _ _ => trivial,fun w => ?_⟩⟩
  have e := SimpleGraph.dist_le_diam (u:=z) (v:=R w (u+T+2)) (G.connected_iff_ediam_ne_top.mp hc)
  omega

theorem local_region (hc : G.Connected) (R : W → ℕ → V) (speed : ∀ w, SpeedOne G (R w))
    (u T X rmax : ℕ) (z : V) (hend : ∀ w, G.dist z (R w (u+T+2)) ≤ 2*X)
    (hT : 2*X+rmax ≤ T) :
    Nonempty (RootRegion G R u T X rmax (ball G z (2*X+T+rmax)).card (fun x => G.dist z x ≤ 2*T)) := by
  have h (w : W) (t : ℕ) (ht : t ≤ T) : G.dist z (R w (u+t+2)) ≤ 2*X+(T-t) := by
    have d := displacement hc (speed w) (show u+t+2 ≤ u+T+2 by omega)
    rw [@SimpleGraph.dist_comm _ G (R w (u+t+2)) (R w (u+T+2))] at d
    have tr := hc.dist_triangle (u:=z) (v:=R w (u+T+2)) (w:=R w (u+t+2))
    have := hend w
    omega
  refine ⟨⟨z,ball G z (2*X+T+rmax),le_rfl,?_,?_,?_,hend⟩⟩
  · intro w t ht r hr
    exact ball_subset hc (by have := h w t ht; omega)
  · intro x hx; have := mem_ball.mp hx; omega
  · intro w t ht r hr x hx; have := h w t ht; omega

/-- Reachability of the common home by the local root clock's last target.
The same estimate is used under the global diameter hypothesis. -/
theorem RootRegion.last_home_bound {R : W → ℕ → V} {u T X rmax volume : ℕ} {starts : V → Prop}
    (reg : RootRegion G R u T X rmax volume starts) (hc : G.Connected)
    (speed : ∀ w, SpeedOne G (R w)) {v g h M r B : ℕ} (hB : 0 < B)
    (hr : r ≤ X) (hh : h ≤ X) (he : endpoint v g h M ≤ T)
    (hlast : T-endpoint v g h M ≤ 2*h) (w : W) :
    G.dist reg.home (center R u v g h M w)+r ≤ ceilRatio (6*X) B*B := by
  let e := endpoint v g h M
  have t := displacement hc (speed w) (show u+e+2 ≤ u+T+2 by dsimp [e]; omega)
  rw [@SimpleGraph.dist_comm _ G (R w (u+e+2)) (R w (u+T+2))] at t
  have d := hc.dist_triangle (u:=reg.home) (v:=R w (u+T+2)) (w:=R w (u+e+2))
  have f := reg.final_near w
  have cc := (ceilRatio_spec (a:=6*X) hB).1
  change G.dist reg.home (R w (u+e+2))+r ≤ _
  dsimp [e] at t d ⊢
  omega

/-- Uniform mixing over any nonempty finite set of window constructions, with
the average cost valid separately on each true word. -/
theorem window_average {I W V : Type*} {G : SimpleGraph V} (indices : Finset I) (hne : indices.Nonempty)
    (R : W → ℕ → V) (u T : ℕ) (starts : V → Prop) (cost : I → W → ℝ)
    (hm : ∀ i ∈ indices, WindowMixture G R u T starts (cost i)) :
    WindowMixture G R u T starts (fun w => mean indices (fun i => cost i w)) := by
  classical
  letI := hne.to_subtype
  let m (i : indices) := (hm i.val i.property).choose
  refine ⟨Mixture.combine (uniformProb indices) (uniformLaw indices) m,fun w => ?_⟩
  have h := combine_log_cost m (fun (s : {p : WindowPolicy G // starts p.start}) x => windowHit s.val (R x) u T)
    (fun (i : indices) x => cost i.val x) (fun i x => (hm i.val i.property).choose_spec x) w
  simpa only [mean,card_univ,Fintype.card_coe,Finset.sum_coe_sort indices (fun i => cost i w)] using h

end
end Meyniel.Multiscale
