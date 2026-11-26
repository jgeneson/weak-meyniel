module

public import Meyniel.MultiscaleRootCases
public import Meyniel.MultiscaleRootComparison
public import Meyniel.MultiscaleTerminalTrials

@[expose] public section

namespace Meyniel.Multiscale
open Filter Finset Interception
noncomputable section
universe u

/-- Averaging over the comparison radius and its time offset pays for each
bad level on the realized robber word. The same thresholds apply to every
graph, family of walks, and starting region. -/
theorem positive_root_eventually {δ : ℝ} (hδ : 0 < δ) (ht : δ < 1/100) :
    ∀ᶠ N : ℕ in atTop, PositiveRootAt.{u} δ N := by
  obtain ⟨c,hc,many⟩ := many_radii hδ ht
  filter_upwards [many,trial_facts_eventually hδ ht,root_loss hδ ht hc,
    few_bad_levels.{u} hδ ht,eventually_ge_atTop 2] with N hcount facts hprice hbad hN
  intro V _ G conn hn W _ _ R m X vol starts hk hX speed passes regions
  classical
  let i := m+1
  let T := windowTime N X
  let rs := radii δ N i
  let C := clockFactor δ
  let base := rootBase δ N i vol
  let cost r ξ w := rootRowCost G δ N T m r ξ R w
  have ihi : i≤levels δ := hk
  have ipos : 1 ≤ i := by dsimp [i]; omega
  have htpos : 0<T := by
    have h := (run_width hX hN).2.1
    change 2*X≤T at h; omega
  have hrs : rs.Nonempty := facts.ranges i ipos ihi
  have rpos r (hr : r∈rs) : 0 < leadTime C r := by
    have p := radius_pos_of_mem hr
    dsimp [leadTime]; omega
  have one (r : ℕ) (hr : r∈rs) :
      WindowMixture G R 0 T starts (fun w => mean (range (leadTime C r)) (fun ξ => cost r ξ w)+base) := by
    have hh : (range (leadTime C r)).Nonempty := ⟨0, mem_range.mpr (rpos r hr)⟩
    have mixed := window_average (range (leadTime C r)) hh R 0 T starts (fun ξ w => cost r ξ w+base)
      (fun ξ hξ => root_fixed conn R speed hN hn facts hX hk hr (regions r hr).1 (mem_range.mp hξ)
        starts (regions r hr).2.some passes (terminal_trials conn facts hn ipos hk))
    apply window_weaken mixed (fun _ h => h)
    intro w
    rw [mean_add',mean_const' hh]
  have mixed := window_average rs hrs R 0 T starts
    (fun r w => mean (range (leadTime C r)) (fun ξ => cost r ξ w)+base) one
  apply window_weaken mixed (fun _ h => h)
  intro w
  rw [mean_add',mean_const' hrs]
  let y := cyclicWord (R w) 0 T
  have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have att := root_charge_mean G δ N T 0 m y (c*Real.log N) (100/δ) hn
    (by dsimp [dilation]; omega) (mul_pos hc hl)
    (fun j hj lo => hcount j lo (hj.trans hk)) (fun t => hbad V G hn (y t))
    (div_nonneg (mul_nonneg facts.gains hl.le) (by norm_num)) htpos (fun r hr => by
      let h := leadTime C r
      let M := clockCount T 2 h
      have hpos : 0<h := rpos r hr
      have hsp : 4*h≤X := (regions r hr).1
      have tt := (run_width hX hN).2.1
      change 2*X≤T at tt
      have hh := count_cover (t:=T) (q:=2) hpos (by omega)
      have mc := (root_clock_setup hN hX hpos (show h ≤ moveTime C r by dsimp [moveTime]; omega) hsp).1
      change M*h+2*h≤T ∧ _ at hh
      change T≤M*h*2 at mc
      change 0<h ∧ h+(h-1)+h*M≤T ∧ T≤2*(M*h)
      rw [Nat.mul_comm h M]; omega)
  change rootMean δ N i T (fun r ξ b => rootCharge G δ N T y m r (rootEnd δ 0 r ξ b:ℕ))+base ≤ _
  have h := hprice i T ihi htpos
  change _ ≤ (4/(T:ℝ))*((T+1:ℕ):ℝ)*((i:ℝ)*(Real.log N/(c*Real.log N))+(100/δ)*(gain δ*Real.log N/2)) at att
  change _ ≤ windowCost δ N i vol
  unfold base rootBase windowCost
  linarith only [att,h]

end
end Meyniel.Multiscale
