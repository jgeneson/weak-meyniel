import Meyniel.MultiscaleWindow
import Meyniel.MultiscaleSplice

/-! Reaching a window's start during a correct-terminal trial. -/

namespace Meyniel.Multiscale
variable {V : Type*} {G : SimpleGraph V}

def segment (R : ℕ → V) (v len : ℕ) : List V := List.ofFn (fun i : Fin len => R (v+i.val))

@[simp] theorem length_segment (R : ℕ → V) (v n : ℕ) : (segment R v n).length=n := by simp [segment]

theorem segment_succ (R : ℕ → V) (v n : ℕ) : segment R v (n+1) = R v :: segment R (v+1) n := by
  simp only [segment,List.ofFn_succ,Fin.val_zero,Nat.add_zero,Fin.val_succ]
  congr 2
  funext i
  congr 1
  omega

theorem segment_add (R : ℕ → V) (v m n : ℕ) :
    segment R v (m+n) = segment R v m ++ segment R (v+m) n := by
  induction m generalizing v with
  | zero => simp [segment]
  | succ m ih =>
    rw [Nat.succ_add,segment_succ,segment_succ,ih]
    simp only [List.cons_append]
    congr 3 <;> omega

theorem segment_getD (R : ℕ → V) (v m i : ℕ) (d : V) (h : i < m) :
    (segment R v m).getD i d = R (v+i) := by simp [segment,List.getD_eq_getElem?_getD,h]

noncomputable def reachWindow (hc : G.Connected) (x : V) (d : ℕ) (s : WindowPolicy G)
    (near : G.dist x s.start ≤ d) : Anchored G x := by
  classical
  let route := (route_to hc x s.start d near).choose
  have hs := (route_to hc x s.start d near).choose_spec
  let branch (h : List V) : Anchored G (route d) :=
    ⟨s.play (h.getD (d-2) x) (h.getD (d-1) x), (s.start_eq ..).trans hs.2.1.symm⟩
  let q := travelThen d route hs.2.2 branch
  exact ⟨q.1,q.2.trans hs.1⟩

private theorem travel_preserves_hit (d : ℕ) (pre : List V) (len : pre.length=d)
    (route : ℕ → V) (legal : ∀ t, Step G (route t) (route (t+1)))
    (branch : List V → Anchored G (route d)) (now : V) (tail : List V)
    (hit : Hits (branch (pre++[now])).1 [] (now::tail)) :
    Hits (travelThen d route legal branch).1 [] (pre++now::tail) := by
  subst d
  exact travelThen_hits pre route legal branch now tail hit

theorem reachWindow_hits (hc : G.Connected) (x : V) (s : WindowPolicy G) (R : ℕ → V)
    (F d T : ℕ) (hd : 2 ≤ d) (near : G.dist x s.start ≤ d) (hs : windowHit s R (F+d) T) :
    Hits (reachWindow hc x d s near).val [] (segment R (F+2) (d+T+1)) := by
  classical
  let route := (route_to hc x s.start d near).choose
  have hroute := (route_to hc x s.start d near).choose_spec
  let branch (h : List V) : Anchored G (route d) :=
    ⟨s.play (h.getD (d-2) x) (h.getD (d-1) x), (s.start_eq ..).trans hroute.2.1.symm⟩
  let pre := segment R (F+2) d
  let now := R (F+2+d)
  let tail := segment R (F+2+d+1) T
  have plen : pre.length=d := length_segment ..
  have original : segment R (F+2) (d+T+1) = pre ++ now::tail := by
    rw [Nat.add_assoc,segment_add,segment_succ]
  have history : pre++[now]=segment R (F+2) (d+1) := by
    rw [segment_add]; simp [pre,now,segment]
  have one : (pre++[now]).getD (d-2) x=R (F+d) := by
    rw [history,segment_getD _ _ _ _ _ (by omega)]; congr 1 <;> omega
  have two : (pre++[now]).getD (d-1) x=R (F+d+1) := by
    rw [history,segment_getD _ _ _ _ _ (by omega)]; congr 1 <;> omega
  have suffix : now::tail = segment R (F+d+2) (T+1) := by
    rw [segment_succ]; dsimp [now,tail]; congr 2 <;> omega
  have hit : Hits (branch (pre++[now])).val [] (now::tail) := by
    change Hits (s.play _ _) [] _
    rw [one,two,suffix]
    exact hs
  rw [original]
  change Hits (travelThen d route hroute.2.2 branch).val [] _
  exact travel_preserves_hit d pre plen route hroute.2.2 branch now tail hit

end Meyniel.Multiscale
