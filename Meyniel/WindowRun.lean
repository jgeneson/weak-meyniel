import Meyniel.PhysicalPolicy
import Meyniel.MultiscaleWindow
import Meyniel.Extension

/-! A local team can run the same deterministic strategy at staggered
deadlines. Each copy starts at its fixed site. It may retrace its own
moves between runs, which brings it back by the next scheduled start. -/
namespace Meyniel.Multiscale.WindowRun
open Meyniel.Multiscale
variable {V : Type*} {G : SimpleGraph V}

private def hist (R : ℕ → V) (u : ℕ) : ℕ → List V
  | 0 => []
  | t+1 => R (u+2+t) :: hist R u t

def position (s : WindowPolicy G) (R : ℕ → V) (u j : ℕ) : V :=
  (s.play (R u) (R (u+1))).pos (hist R u j)

@[simp] theorem position_zero (s : WindowPolicy G) (R : ℕ → V) (u : ℕ) : position s R u 0 = s.start :=
  s.start_eq ..

theorem position_step (s : WindowPolicy G) (R : ℕ → V) (u j : ℕ) :
    Step G (position s R u j) (position s R u (j+1)) := (s.play ..).legal ..

private theorem hist_congr {R S : ℕ → V} (u j : ℕ) (he : SameThrough R S (u+j+1)) :
    hist R u j = hist S u j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [hist,ih (he.restrict (by omega)),he (u+2+j) (by omega)]

theorem position_congr (s : WindowPolicy G) {R S : ℕ → V} (u j : ℕ)
    (he : SameThrough R S (u+j+1)) : position s R u j = position s S u j := by
  simp [position,hist_congr u j he,he u (by omega),he (u+1) (by omega)]

theorem hit_in_run (s : WindowPolicy G) (R : ℕ → V) (u T : ℕ) (hh : windowHit s R u T) :
    ∃ j ≤ T, position s R u j = R (u+j+2) ∨ j < T ∧ position s R u (j+1) = R (u+j+2) := by
  let p := s.play (R u) (R (u+1))
  let word (a l : ℕ) := List.ofFn (fun i : Fin l => R (u+2+a+i.val))
  have word_succ (a l : ℕ) : word a (l+1) = R (u+2+a) :: word (a+1) l := by
    unfold word
    rw [List.ofFn_succ]
    simp only [Fin.val_zero,Nat.add_zero]
    congr 1
    apply congrArg List.ofFn
    funext i
    congr 1
    simp [Fin.val_succ]; omega
  have run : ∀ d a, a+d = T → Hits p (hist R u a) (word a (d+1)) →
      ∃ j ≤ T, position s R u j = R (u+j+2) ∨ j < T ∧ position s R u (j+1) = R (u+j+2) := by
    intro d
    induction d with
    | zero =>
      intro a ha h
      rw [word_succ] at h
      have : word (a+1) 0 = [] := by simp [word]
      rw [this] at h
      exact ⟨a,by omega,Or.inl (by simpa [Hits,position,p,Nat.add_right_comm] using h)⟩
    | succ d ih =>
      intro a ha h
      rw [word_succ,word_succ] at h
      rcases h with h | h | h
      · exact ⟨a,by omega,Or.inl (by simpa [position,p,Nat.add_right_comm] using h)⟩
      · exact ⟨a,by omega,Or.inr ⟨by omega, by simpa [position,hist,p,Nat.add_right_comm] using h⟩⟩
      · apply ih (a+1) (by omega)
        rw [word_succ]
        exact h
  apply run T 0 (by omega)
  simpa [windowHit,word,p,hist] using hh

private def atRound (T i : ℕ) : ℕ := min i (2*T-i)

private theorem same_or_step {a b : ℕ} (h : a ≤ b+1 ∧ b ≤ a+1) :
    a = b ∨ b = a+1 ∨ a = b+1 := by omega

private theorem rewind_step (s : WindowPolicy G) (R : ℕ → V) (u T i : ℕ) :
    Step G (position s R u (atRound T i)) (position s R u (atRound T (i+1))) := by
  rcases same_or_step (a:=atRound T i) (b:=atRound T (i+1)) (by unfold atRound; omega) with e | e | e
  · rw [e]; exact Or.inl rfl
  · rw [e]; exact position_step ..
  · rw [e]; exact (position_step s R u _).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

def periodic (s : WindowPolicy G) (R : ℕ → V) (u T P j : ℕ) : V :=
  position s R (u+(j/P)*P) (atRound T (j%P))

theorem periodic_start (s : WindowPolicy G) (R : ℕ → V) (u T P : ℕ) :
    periodic s R u T P 0 = s.start := by simp [periodic,atRound]

theorem periodic_step (s : WindowPolicy G) (R : ℕ → V) (u T P j : ℕ) (hP : 2*T < P) :
    Step G (periodic s R u T P j) (periodic s R u T P (j+1)) := by
  have pp : 0 < P := by omega
  have small := Nat.mod_lt j pp
  by_cases last : j%P+1 = P
  · have mod0 : (j+1)%P = 0 := by rw [←Nat.mod_add_mod,last,Nat.mod_self]
    have h0 : atRound T (j%P) = 0 := by unfold atRound; omega
    simp only [periodic,h0,mod0,show atRound T 0 = 0 by simp [atRound], position_zero]
    exact Or.inl rfl
  · have hj : j%P+1 < P := by omega
    have mod' : (j+1)%P = j%P+1 := by
      rw [←Nat.mod_add_mod, Nat.mod_eq_of_lt hj]
    have div' : (j+1)/P = j/P := by
      have h1 := Nat.mod_add_div j P
      have h2 := Nat.mod_add_div (j+1) P
      rw [mod'] at h2
      have hh : P*((j+1)/P) = P*(j/P) := by omega
      exact Nat.eq_of_mul_eq_mul_left pp hh
    simpa only [periodic,mod',div'] using rewind_step s R (u+(j/P)*P) T (j%P)

theorem periodic_congr (s : WindowPolicy G) {R S : ℕ → V} (u T P j : ℕ)
    (he : SameThrough R S (u+j+1)) : periodic s R u T P j = periodic s S u T P j := by
  apply position_congr
  apply he.restrict
  have hle : atRound T (j%P) ≤ j%P := min_le_left .. 
  have hh := Nat.mod_add_div j P
  rw [Nat.mul_comm P (j/P)] at hh
  omega

theorem periodic_run (s : WindowPolicy G) (R : ℕ → V) (u T P b j : ℕ) (hP : 2*T < P) (hj : j ≤ T) :
    periodic s R u T P (b*P+j) = position s R (u+b*P) j := by
  have pp : 0 < P := by omega
  have jp : j < P := by omega
  have div' : (b*P+j)/P = b := by rw [Nat.mul_comm b P, Nat.mul_add_div pp, Nat.div_eq_of_lt jp, Nat.add_zero]
  have mod' : (b*P+j)%P = j := by rw [Nat.mul_comm b P, Nat.mul_add_mod, Nat.mod_eq_of_lt jp]
  simp [periodic,div',mod',atRound,show j ≤ 2*T-j by omega]

end Meyniel.Multiscale.WindowRun
