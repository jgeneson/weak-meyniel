module

public import Meyniel.MultiscaleBands
public import Meyniel.MultiscaleGraphClock
public import Meyniel.MultiscaleSmoothing

/-! Smoothed target columns at fixed time spacing, and their common-home extension. -/

@[expose] public section

namespace Meyniel.Multiscale.Targets
open Finset Interception GraphClock Flight Clock Smoothing
noncomputable section

variable {W V : Type*} {G : SimpleGraph V}

def endpoint (v g h j : ℕ) := v+g+j*h
def center (R : W → ℕ → V) (u v g h j : ℕ) (w : W) := R w (u+endpoint v g h j+2)

def toEnd (hc : G.Connected) (home y : V) (i : ℕ) : V :=
  (Extension.route hc home y).getVert i

private theorem toEnd_speed (hc : G.Connected) (home y : V) : SpeedOne G (toEnd hc home y) := by
  intro t
  let p := Extension.route hc home y
  change Step G (p.getVert t) (p.getVert (t+1))
  by_cases e : t < p.length
  · exact Or.inr (p.adj_getVert_succ e)
  · exact Or.inl ((p.getVert_of_length_le (by omega)).trans (p.getVert_of_length_le (by omega)).symm)

def retreat (hc : G.Connected) (home y : V) (i : ℕ) := toEnd hc home y (G.dist home y-i)

@[simp] theorem retreat_zero (hc : G.Connected) (home y : V) : retreat hc home y 0=y := by
  simp [retreat,toEnd,← Extension.route_length hc home y]

theorem retreat_home (hc : G.Connected) (home y : V) (i : ℕ) (hi : G.dist home y ≤ i) :
    retreat hc home y i = home := by simp [retreat,toEnd,Nat.sub_eq_zero_of_le hi]

theorem retreat_radius (hc : G.Connected) (home y : V) (i : ℕ) :
    G.dist home (retreat hc home y i) ≤ G.dist home y := by
  have e := displacement hc (toEnd_speed hc home y) (Nat.zero_le (G.dist home y-i))
  simp only [toEnd,SimpleGraph.Walk.getVert_zero,Nat.sub_zero] at e
  exact e.trans (Nat.sub_le _ _)

theorem retreat_dist (hc : G.Connected) (home y : V) {l m : ℕ} (hlm : l ≤ m) :
    G.dist (retreat hc home y m) (retreat hc home y l) ≤ m-l := by
  have e := displacement hc (toEnd_speed hc home y)
      (show G.dist home y-m ≤ G.dist home y-l by omega)
  exact e.trans (by omega)

variable [Fintype V] [DecidableEq V]

def target (hc : G.Connected) (R : W → ℕ → V) (u v g h r M B : ℕ) (home : V)
    (j : ℕ) (i : Tag W V) : V :=
  if j ≤ M then sample G (center R u v g h j) r i
  else retreat hc home (sample G (center R u v g h M) r i) ((j-M)*B)

omit [DecidableEq V] in
theorem target_after (hc : G.Connected) (R : W → ℕ → V) (u v g h r M B : ℕ) (home : V)
    {j : ℕ} (hj : M ≤ j) (i : Tag W V) :
    target hc R u v g h r M B home j i =
    retreat hc home (sample G (center R u v g h M) r i) ((j-M)*B) := by
  rcases hj.eq_or_lt with rfl | hj
  · simp [target]
  · simp [target,not_le.mpr hj]

omit [DecidableEq V] in
theorem target_leg (hc : G.Connected) (R : W → ℕ → V) (hR : ∀ w, SpeedOne G (R w))
    (u v g h r M B : ℕ) (width : h+2*r ≤ B) (home : V) (j : ℕ) (i : Tag W V) :
    G.dist (target hc R u v g h r M B home (j+1) i) (target hc R u v g h r M B home j i) ≤ B := by
  by_cases e : j < M
  · simp only [target,if_pos (show j+1 ≤ M by omega),if_pos e.le]
    let y := center R u v g h j i.1
    let y' := center R u v g h (j+1) i.1
    let z := sample G (center R u v g h j) r i
    let z' := sample G (center R u v g h (j+1)) r i
    have ds : G.dist y z ≤ r := mem_ball.mp (sample_mem G (center R u v g h j) r i)
    have ds' : G.dist y' z' ≤ r := mem_ball.mp (sample_mem G (center R u v g h (j+1)) r i)
    have dt : G.dist y y' ≤ h := by
      let t := u+endpoint v g h j+2
      have e' : u+endpoint v g h (j+1)+2=t+h := by simp [t,endpoint,Nat.succ_mul]; omega
      unfold y y' center
      rw [e']
      simpa [t] using displacement hc (hR i.1) (show t ≤ t+h by omega)
    have tri := hc.dist_triangle (u:=z') (v:=y') (w:=z)
    have tri' := hc.dist_triangle (u:=y') (v:=y) (w:=z)
    rw [@SimpleGraph.dist_comm _ G z' y'] at tri
    rw [@SimpleGraph.dist_comm _ G y' y] at tri'
    change G.dist z' z ≤ B
    omega
  · rw [target_after hc _ _ _ _ _ _ _ _ _ (show M ≤ j+1 by omega),
        target_after hc _ _ _ _ _ _ _ _ _ (show M ≤ j by omega)]
    have e' : (j+1-M)*B=(j-M)*B+B := by rw [show j+1-M=(j-M)+1 by omega,Nat.succ_mul]
    rw [e']
    exact (retreat_dist hc home _ (Nat.le_add_right _ _)).trans (by omega)

omit [DecidableEq V] in
theorem target_home (hc : G.Connected) (R : W → ℕ → V)
    (u v g h r M B D : ℕ) (home : V)
    (last : ∀ w, G.dist home (center R u v g h M w)+r ≤ D*B)
    {j : ℕ} (hj : M+D ≤ j) (i : Tag W V) : target hc R u v g h r M B home j i=home := by
  rw [target_after hc _ _ _ _ _ _ _ _ _ (show M ≤ j by omega)]
  apply retreat_home
  have ds := mem_ball.mp (sample_mem G (center R u v g h M) r i)
  have d := hc.dist_triangle (u:=home) (v:=center R u v g h M i.1) (w:=sample G (center R u v g h M) r i)
  have bound := Nat.mul_le_mul_right B (show D ≤ j-M by omega)
  have := last i.1
  omega

theorem endpoint_gaps {B h j t : ℕ} (hB : 0 < B) (hh : 0 < h)
    (term : t ∈ Icc (height B h (j-1)) (height B h j)) (v g : ℕ) :
    time v B t + g ≤ endpoint v g h j ∧ endpoint v g h j < time v B t + (g+h+B) := by
  have d := (Nat.le_div_iff_mul_le hB).mp (mem_Icc.mp term).2
  have hh' : (j-1)*h/B < t+1 := Nat.lt_succ_of_le (mem_Icc.mp term).1
  have u := (Nat.div_lt_iff_lt_mul hB).mp hh'
  rw [Nat.succ_mul] at u
  unfold time endpoint
  cases j with
  | zero => simp at *; omega
  | succ j => simp only [Nat.add_sub_cancel_right,Nat.succ_mul] at *; omega

theorem target_support [Fintype W] (hc : G.Connected) (R : W → ℕ → V)
    (hR : ∀ w, SpeedOne G (R w)) (u v g h r M B A : ℕ) (hB : 0 < B) (hh : 0 < h)
    (rad : 2*(g+h+B)+r ≤ A) (home : V) {j t : ℕ} (hj : j ≤ M)
    (term : t ∈ Icc (height B h (j-1)) (height B h j)) (i : Tag W V) :
    (atom (fun l : Tag W V => reveal R u v B (t+1) l.1) i).image
      (target hc R u v g h r M B home j) ⊆ ball G (center R u v g h j i.1) A := by
  classical
  rintro _ hy
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hy
  have rev := (mem_filter.mp ha).2
  let F := time v B t
  let e := endpoint v g h j
  have fix : R a.1 (u+F+2) = R i.1 (u+F+2) := by
    have eqn : segment (R a.1) u ((F+2)+1) = segment (R i.1) u ((F+2)+1) := rev
    have hpos := congrArg (fun (l : List V) => l[F+2]?) eqn
    simp only [segment_ofFn,List.getElem?_ofFn,dif_pos (Nat.lt_succ_self _),Option.some.injEq] at hpos
    simpa only [Nat.add_assoc] using hpos
  have g₀ := endpoint_gaps hB hh term v g
  have leFe : u+F+2 ≤ u+e+2 := by dsimp [F,e]; omega
  have da := displacement hc (hR a.1) leFe
  have di := displacement hc (hR i.1) leFe
  rw [fix] at da
  let zz := sample G (center R u v g h j) r a
  have dz : G.dist (center R u v g h j a.1) zz ≤ r := mem_ball.mp (sample_mem G (center R u v g h j) r a)
  have p := hc.dist_triangle (u:=center R u v g h j i.1) (v:=R i.1 (u+F+2)) (w:=zz)
  have q := hc.dist_triangle (u:=R i.1 (u+F+2)) (v:=center R u v g h j a.1) (w:=zz)
  rw [@SimpleGraph.dist_comm _ G (center R u v g h j i.1) (R i.1 (u+F+2))] at p
  rw [target,if_pos hj,mem_ball]
  change G.dist (R i.1 (u+e+2)) zz ≤ A
  change G.dist (R i.1 (u+e+2)) zz ≤ G.dist (R i.1 (u+F+2)) (R i.1 (u+e+2)) + G.dist (R i.1 (u+F+2)) zz at p
  change G.dist (R i.1 (u+F+2)) zz ≤ G.dist (R i.1 (u+F+2)) (R a.1 (u+e+2)) + G.dist (R a.1 (u+e+2)) zz at q
  change G.dist (R a.1 (u+e+2)) zz ≤ r at dz
  change F+g ≤ e ∧ e<F+(g+h+B) at g₀
  omega

end
end Meyniel.Multiscale.Targets
