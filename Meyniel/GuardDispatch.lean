module

public import Meyniel.GuardPool
public import Meyniel.WindowRun

/-! Physical first dispatch from the two-round-old robber vertex. A copy
travels to the center, reaches its preselected initial site in the deployment
interval, then repeatedly executes its local covering strategy. -/

@[expose] public section

namespace Meyniel.Multiscale.GuardDispatch
open Meyniel.Multiscale

variable {V : Type*} {G : SimpleGraph V}
noncomputable section

/-- After a launch at time f, a script starts at the current trail vertex.
The argument j counts real rounds since this launch. -/
structure Script (G : SimpleGraph V) where
  pos : (ℕ → V) → ℕ → ℕ → V
  zero : ∀ R f, pos R f 0 = R f
  step : ∀ R, SpeedOne G R → ∀ f j, Step G (pos R f j) (pos R f (j+1))
  causal : ∀ R S, SpeedOne G R → SpeedOne G S → ∀ f j,
    SameThrough R S (f+j+1) → pos R f j = pos S f j

/-- The first launch that has already been observed when the current
position is evaluated. The position at the launch itself is still the trail. -/
def first (test : (ℕ → V) → ℕ → Bool) (R : ℕ → V) : ℕ → Option ℕ
  | 0 => none
  | t+1 => (first test R t).orElse (fun _ => if test R t then some t else none)

private theorem first_lt {test : (ℕ → V) → ℕ → Bool} {R : ℕ → V} {t f : ℕ}
    (h : first test R t = some f) : f < t := by
  induction t with
  | zero => simp [first] at h
  | succ t ih =>
    cases e : first test R t with
    | none =>
      simp only [first,e,Option.orElse_none] at h
      split at h <;> simp_all
    | some a =>
      simp only [first,e,Option.orElse_some,Option.some.injEq] at h
      obtain rfl := h
      exact (ih e).trans (Nat.lt_succ_self _)

theorem first_iff {test : (ℕ → V) → ℕ → Bool} {R : ℕ → V} {f t : ℕ} :
    first test R t = some f ↔ f < t ∧ test R f = true ∧ ∀ j < f, test R j = false := by
  induction t with
  | zero => simp [first]
  | succ t ih =>
    by_cases prior : ∃ j < t, test R j = true
    · have hsome : (first test R t).isSome := by
        clear ih
        induction t with
        | zero => simp at prior
        | succ t it =>
          by_cases p : ∃ j < t, test R j = true
          · have hj := it p
            cases h : first test R t <;> simp_all [first]
          · obtain ⟨j,hj,ok⟩ := prior
            have eq : j=t := by by_contra hn; exact p ⟨j,by omega,ok⟩
            subst j
            cases h : first test R t <;> simp [first,h,ok]
      obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp hsome
      simp [first,ha] 
      constructor
      · rintro rfl
        obtain ⟨hf,hh,none⟩ := ih.mp ha
        exact ⟨by omega,hh,none⟩
      · rintro ⟨hf,hh,none⟩
        obtain ⟨j,hj,hit⟩ := prior
        have hf' : f < t := by by_contra hn; simpa [hit] using none j (by omega)
        exact Option.some.inj (ha.symm.trans (ih.mpr ⟨hf',hh,none⟩))
    · have empty : first test R t = none := by
        clear ih
        induction t with
        | zero => rfl
        | succ t it =>
          have hnot : test R t = false := by cases h : test R t <;> simp_all
          simp [first,it (fun h => prior (by obtain ⟨j,hj,yes⟩ := h; exact ⟨j,by omega,yes⟩)),hnot]
      simp only [first,empty,Option.orElse_none]
      by_cases now : test R t = true
      · simp only [now,if_true,Option.some.injEq]
        constructor
        · rintro rfl
          refine ⟨by omega,now,?_⟩
          intro j hj; cases e : test R j <;> simp_all
        · rintro ⟨hf,hh,_⟩
          by_contra e; exact prior ⟨f,by omega,hh⟩
      · simp only [Bool.not_eq_true] at now
        simp only [now,Bool.false_eq_true,if_false,reduceCtorEq,false_iff]
        rintro ⟨hf,hh,_⟩
        have hf' : f < t := by
          by_contra hn
          have eq : f=t := by omega
          rw [eq,now] at hh
          contradiction
        exact prior ⟨f,hf',hh⟩

private theorem first_eq {test : (ℕ → V) → ℕ → Bool} {R S : ℕ → V} {t : ℕ}
    (h : ∀ j < t, test R j = test S j) : first test R t = first test S t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [first,ih (fun j hj => h j (by omega)),h t (by omega)]

def dispatched (sc : Script G) (test : (ℕ → V) → ℕ → Bool)
    (obs : ∀ R S, SpeedOne G R → SpeedOne G S → ∀ t, SameThrough R S (t+2) → test R t = test S t) :
    PhysicalPolicy G where
  pos R t := match first test R t with
    | none => R t
    | some f => sc.pos R f (t-f)
  causal R S hr hs t eq := by
    have h := first_eq (fun j (hj : j < t) => obs R S hr hs j (eq.restrict (by omega)))
    rw [h]
    cases hd : first test S t with
    | none => exact eq t (by omega)
    | some f => exact sc.causal R S hr hs f (t-f) (eq.restrict (by have := first_lt hd; omega))
  step R hr t := by
    cases hf : first test R t with
    | none =>
      by_cases now : test R t = true
      · simpa [first,hf,now,sc.zero] using sc.step R hr t 0
      · simpa [first,hf,now] using hr t
    | some f =>
      have hf' := first_lt hf
      simpa [first,hf,show t+1-f=t-f+1 by omega] using sc.step R hr f (t-f)

/-- Prepend travel and waiting to an arbitrary post-arrival trajectory. -/
def leg {a b : V} (hc : G.Connected) (wait : ℕ) (k : ℕ → V) (j : ℕ) : V :=
  if j < wait then (Extension.route hc a b).getVert j else k (j-wait)

private theorem route_step {a b : V} (hc : G.Connected) (j : ℕ) :
    Step G ((Extension.route hc a b).getVert j) ((Extension.route hc a b).getVert (j+1)) := by
  let p := Extension.route hc a b
  by_cases h : j < p.length
  · exact Or.inr (p.adj_getVert_succ h)
  · exact Or.inl ((p.getVert_of_length_le (by omega)).trans (p.getVert_of_length_le (by omega)).symm)

private theorem leg_zero {a b : V} (hc : G.Connected) (w : ℕ) (hw : G.dist a b ≤ w)
    (k : ℕ → V) (k0 : k 0 = b) : leg (a:=a) (b:=b) hc w k 0 = a := by
  by_cases h : 0 < w
  · simp [leg,h]
  · have hab := hc.dist_eq_zero_iff.mp (show G.dist a b = 0 by omega)
    simp [leg,h,k0,hab]

private theorem leg_step {a b : V} (hc : G.Connected) (w : ℕ) (hw : G.dist a b ≤ w)
    (k : ℕ → V) (k0 : k 0 = b) (hk : ∀ i, Step G (k i) (k (i+1))) (j : ℕ) :
    Step G (leg (a:=a) (b:=b) hc w k j) (leg (a:=a) (b:=b) hc w k (j+1)) := by
  by_cases old : j < w
  · by_cases newer : j+1 < w
    · simpa [leg,old,newer] using route_step (a:=a) (b:=b) hc j
    · have he : j+1 = w := by omega
      have endp : (Extension.route hc a b).getVert (j+1) = b :=
        (Extension.route hc a b).getVert_of_length_le (by rw [Extension.route_length]; omega)
      simpa [leg,old,newer,show j+1-w=0 by omega,k0,endp] using route_step (a:=a) (b:=b) hc j
  · simpa [leg,old,show ¬j+1<w by omega,show j+1-w=j-w+1 by omega] using hk (j-w)

def working {z : V} (hc : G.Connected) (s : WindowPolicy G) (T P offset : ℕ)
    (hP : 2*T < P) (travel : G.dist z s.start ≤ 2*T) : Script G where
  pos R f j :=
    let a := G.dist (R f) z
    let w := 2*T+offset
    leg (a:=R f) (b:=z) hc a (leg (a:=z) (b:=s.start) hc w (WindowRun.periodic s R (f+a+w) T P)) j
  zero R f := by
    apply leg_zero hc _ le_rfl
    apply leg_zero hc _ (by omega)
    exact WindowRun.periodic_start ..
  step R hR f j := by
    apply leg_step hc _ le_rfl
    · apply leg_zero hc _ (by omega); exact WindowRun.periodic_start ..
    · intro d
      apply leg_step hc _ (by omega)
      · exact WindowRun.periodic_start ..
      · intro i; exact WindowRun.periodic_step _ _ _ _ _ _ hP
  causal R S hr hs f j eq := by
    have hf := eq f (by omega)
    simp only [hf]
    unfold leg
    split
    · rfl
    · split
      · rfl
      · apply WindowRun.periodic_congr
        apply eq.restrict
        omega

theorem working_run {z : V} (hc : G.Connected) (s : WindowPolicy G) (T P offset : ℕ)
    (hP : 2*T < P) (travel : G.dist z s.start ≤ 2*T) (R : ℕ → V)
    (f q j : ℕ) (hj : j ≤ T) :
    let a := G.dist (R f) z
    let u := f+a+(2*T+offset)
    (working hc s T P offset hP travel).pos R f (a+(2*T+offset)+q*P+j) =
      WindowRun.position s R (u+q*P) j := by
  dsimp only
  simp only [working,leg]
  split_ifs with early earlier
  · omega
  · omega
  · convert WindowRun.periodic_run s R (f+G.dist (R f) z+(2*T+offset)) T P q j hP hj using 1
    congr 1
    omega

end
end Meyniel.Multiscale.GuardDispatch
