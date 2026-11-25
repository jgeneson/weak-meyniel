import Meyniel.MultiscaleFiber
import Meyniel.TrialStepDefs
import Meyniel.MultiscaleTargets

namespace Meyniel.Multiscale
open Finset GraphClock Targets Clock
noncomputable section
universe v w
variable {V : Type v} {W : Type w} [Fintype V] [Fintype W] [Nonempty W] {G : SimpleGraph V}

theorem view_anchor {R S : ℕ → V} (u f : ℕ) (hb : Flight.view R u f=Flight.view S u f) :
    R (u + f)=S (u + f) := by
  simp only [Flight.view,Flight.segment_ofFn] at hb
  exact congrFun (List.ofFn_injective hb) ⟨f,by omega⟩

/-- Every terminal is run only after its entire observed prefix is known.
The induction is applied on the fiber of this prefix and the sampled ball.
This one construction handles both inner clocks and the outer clock. -/
theorem clock_terminal_trials (hc : G.Connected) {δ : ℝ} {N root T i r u L v M : ℕ}
    (R : W → ℕ → V) (speed : ∀ w, SpeedOne G (R w)) (hN : 0 < N)
    (hi : 1 ≤ i) (hk : i ≤ levels δ) (hr : r ∈ radii δ N i) (rpos : 0 < r)
    (before : root ≤ u) (after : u + L ≤ root + T)
    (passed : ∀ (j : Fin (levels δ)), j.val + 1 ≤ i → ∀ w, Passes G (R w) (physicalScale G δ N j) u (u + L))
    (ih : TrialAt.{v,w} G δ N root T i)
    (deadline : Targets.endpoint v (leadTime (clockFactor δ) r) (leadTime (clockFactor δ) r) M ≤ L) :
    let h := leadTime (clockFactor δ) r
    let B := moveTime (clockFactor δ) r
    let e b := u + endpoint v h h (column B h b)
    ∃ trial : ℕ → List V → (x : V) → Mixture (Anchored G x),
      ∀ b  ≤  top B h M, ∀ w x, x  ∈  ball G (center R u v h h (column B h b) w) r →
      Real.exp (-(logBall G (center R u v h h (column B h b) w) (dilation δ*r)/2 + 
        trialExtra G δ N T (cyclicWord (R w) root T) i r (e b)))  ≤ 
      (trial b (reveal R u v B (row B h b + 1) w) x).success
        (atHit R u L (time v B (row B h b)) x) w := by
  classical
  let C := clockFactor δ
  let t := duration C r
  let h := leadTime C r
  let B := moveTime C r
  let e b := u + endpoint v h h (column B h b)
  let f b := time v B (row B h b)
  let y b w := center R u v h h (column B h b) w
  let pre b := reveal R u v B (row B h b + 1)
  let cost b w := logBall G (y b w) (dilation δ*r)/2 + trialExtra G δ N T (cyclicWord (R w) root T) i r (e b)
  apply fiber_trials (fun b => b ≤ top B h M) pre (fun b w x => x ∈ ball G (y b w) r)
    (fun b x => atHit R u L (f b) x) (fun b w => Real.exp (-cost b w))
  intro b hb hist x E en
  letI : Nonempty E := en
  let s : E := Classical.arbitrary _
  let S (w:E) := R w.1
  let F := u + f b
  let a := e b-t
  have hval : h=2*t + 3*r := rfl
  have hh : 0 < h := by omega
  have hB : 0 < B := by dsimp [B,moveTime]; change 0 < h + 2*r; omega
  obtain ⟨h₁,h₂⟩ := label_times (b:=b) hh hB
  have time1 : F + h ≤ e b := by dsimp [F,f,e,time,endpoint]; omega
  have time2 : e b  <  F + endTime C r := by change e b < F + (2*h + B); dsimp [F,f,e,time,endpoint]; omega
  have upl : e b  ≤  u + L := by
    have he := Nat.mul_le_mul_right h (column_le hB hh hb)
    change v + h + M*h ≤ L at deadline
    dsimp [e,endpoint]; omega
  have rdy : F + 2 ≤ a := by dsimp [a]; omega
  have far : t + 3*r ≤ a-F := by dsimp [a]; omega
  have eq : a + t=e b := by dsimp [a]; omega
  have uF : u ≤ F := by dsimp [F]; omega
  have atE (w:E) : y b w.1 = S w (e b + 2) := rfl
  let j : Fin (levels δ) := ⟨i-1,by omega⟩
  have idx : j.val + 1=i := by dsimp [j]; omega
  have ctx : TrialInput G δ N root T i r S F a x (S s F) := by
    refine ⟨by omega,by change a + t  ≤  root + T; omega,by omega,fun w => speed w.val,?_,?_,?_,?_⟩
    · intro w
      apply view_anchor u (f b)
      exact w.2.1.trans s.2.1.symm
    · intro w
      have hy := mem_ball.mp w.2.2
      rw [atE w,SimpleGraph.dist_comm] at hy
      change G.dist x (S w (a + t + 2))  ≤  r
      rwa [eq]
    · intro l hl w
      exact passes_subwindow (passed l (by omega) w.val) (by omega) (by change a + t ≤ u + L; omega)
    · intro w hg
      change i ∉ badLevels G (S w (a + t + 2)) δ N at hg
      rw [eq] at hg
      change InBand G (S w) F (a + t) (bandWidth N (guardRadius δ N i))
      rw [eq]
      have hhpass := passed j (by omega) w.val
      have hrad : r  ∈  (physicalScale G δ N j).radii := by simpa [physicalScale,idx] using hr
      have good := (physicalScale_good_iff G δ hN j (S w (e b + 2))).mpr (by simpa [idx] using hg)
      have band := hhpass r hrad F (e b) uF (by omega) upl
        (by change h ≤ e b-F; omega) (by change e b-F < endTime C r; omega) good
      simpa [physicalScale,idx,S] using band
  have win := ih hr ctx
  let price (w:E) := logBall G (S w (a + t + 2)) (dilation δ*r)/2 + 
    trialExtra G δ N T (cyclicWord (S w) root T) i r (a + t)
  obtain ⟨mix,hm⟩ := reachWindow_mixture hc x S u L (f b) a t rdy (by omega)
    (fun y => y ∈ ball G x (t + 3*r)) (fun y hy => (mem_ball.mp hy).trans far) price win
  refine ⟨mix,fun w => ?_⟩
  have heq : price w=cost b w.1 := by dsimp only [price,cost]; rw [← Nat.cast_add,eq,atE]
  exact (heq ▸ hm w)

end
end Meyniel.Multiscale
