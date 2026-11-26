module

public import Meyniel.MultiscaleTerminal
public import Meyniel.MultiscaleFlight
public import Meyniel.MultiscaleClock

/-! The weighted comparison clock in the ordinary graph game. -/

@[expose] public section

namespace Meyniel.Multiscale.GraphClock
open Finset Interception Flight Clock
noncomputable section

variable {Ω W V : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq W] [DecidableEq V]
variable {G : SimpleGraph V}

instance anchoredNonempty (G : SimpleGraph V) (x : V) : Nonempty (Anchored G x) :=
  ⟨⟨Policy.stay G x,rfl⟩⟩

def time (v B t : ℕ) := v+t*B

def reveal (R : W → ℕ → V) (u v B : ℕ) : ℕ → W → List V
  | 0, _ => []
  | t+1, w => view (R w) u (time v B t)

def atHit (R : W → ℕ → V) (u T t : ℕ) (x : V) (p : Anchored G x) (w : W) :=
  Hits p.1 [] (suffix (R w) u T t)

def initialValue (G : SimpleGraph V) (μ : Ω → ℝ) (word : Ω → W) (weight : W → ℝ)
    (R : W → ℕ → V) (u T : ℕ) (starts : V → Prop) [Nonempty {s : WindowPolicy G // starts s.start}] : ℝ :=
  value μ (fun i => weight (word i)) univ
    (fun (s : {s : WindowPolicy G // starts s.start}) i => windowHit s.val (R (word i)) u T)

def node (G : SimpleGraph V) (μ : Ω → ℝ) (word : Ω → W) (weight : W → ℝ)
    (R : W → ℕ → V) (u T v B t : ℕ) (h : List V) (x : V) : ℝ :=
  value μ (fun i => weight (word i)) (fiber (fun i => reveal R u v B (t+1) (word i)) h)
    (fun s i => atHit (G:=G) R u T (time v B t) x s (word i))

def score (G : SimpleGraph V) (μ : Ω → ℝ) (word : Ω → W) (weight : W → ℝ)
    (R : W → ℕ → V) (u T v B : ℕ) (z : ℕ → Ω → V) (starts : V → Prop)
    [Nonempty {s : WindowPolicy G // starts s.start}] (b : ℕ) : ℕ → Ω → ℝ
  | 0, _ => initialValue G μ word weight R u T starts
  | t+1, i => node G μ word weight R u T v B t (reveal R u v B (t+1) (word i)) (z (b-t) i)

omit [Nonempty Ω] [DecidableEq W] in
theorem bellman_move (G : SimpleGraph V) (hc : G.Connected)
    (μ : Ω → ℝ) (hμ : ∀ i, 0 < μ i) (word : Ω → W) (weight : W → ℝ) (hw : ∀ w, 0 < weight w)
    (R : W → ℕ → V) (u T v B : ℕ) (z : ℕ → Ω → V)
    (leg : ∀ j i, G.dist (z (j+1) i) (z j i) ≤ B) (starts : V → Prop)
    [Nonempty {s : WindowPolicy G // starts s.start}] (b t : ℕ)
    (allow : ∀ i, starts (z b i)) (ht : t ≤ b) (deadline : time v B t ≤ T) (i : Ω) :
    avgOn μ (atom (fun j => reveal R u v B t (word j)) i)
      (fun j => node G μ word weight R u T v B t (reveal R u v B (t+1) (word j)) (z (b-t) i)) ≤
      score G μ word weight R u T v B z starts b t i := by
  classical
  cases t with
  | zero =>
    let g := fun j => reveal R u v B 1 (word j)
    let k := fun j : Ω => ([] : List V)
    have ka : atom k i=univ := by ext; simp [k,atom,fiber]
    have splice (f : List V → Anchored G (z b i)) :
        ∃ s : {s : WindowPolicy G // starts s.start}, ∀ j, k j=k i →
          atHit R u T (time v B 0) (z b i) (f (g j)) (word j) →
          windowHit s.val (R (word j)) u T := by
      obtain ⟨s,hs⟩ := first_flight G R u T (time v B 0) deadline starts (z b i) (allow i) f
      exact ⟨s,fun j _ => hs (word j)⟩
    have h := value_splice μ (fun j => weight (word j)) k g i hμ (fun j => (hw _).le)
      (fun _ _ _ => rfl)
      (fun (s : {s : WindowPolicy G // starts s.start}) j => windowHit s.val (R (word j)) u T)
      (fun (s : Anchored G (z b i)) j => atHit R u T (time v B 0) (z b i) s (word j)) splice
    rw [ka] at h
    change avgOn μ (atom k i) _ ≤ _
    rw [ka]
    simpa only [score,Nat.sub_zero,node,initialValue,atom,g] using h
  | succ t =>
    let a := time v B t
    let e := time v B (t+1)
    have hae : e=a+B := by simp [e,a,time,Nat.succ_mul,Nat.add_assoc]
    have hab : a ≤ e := by omega
    let k := fun j => reveal R u v B (t+1) (word j)
    let g := fun j => reveal R u v B (t+2) (word j)
    let x := z (b-t) i
    let y := z (b-(t+1)) i
    have reach : G.dist x y ≤ e-a := by
      have eqn : b-(t+1)+1=b-t := by omega
      have h := leg (b-(t+1)) i
      simpa only [eqn,x,y,hae,Nat.add_sub_cancel_left] using h
    have splice (f : List V → Anchored G y) :
        ∃ s : Anchored G x, ∀ j, k j=k i →
          atHit R u T e y (f (g j)) (word j) → atHit R u T a x s (word j) := by
      obtain ⟨s,hs⟩ := local_flight G hc R u T a e hab deadline (word i) x y reach f
      exact ⟨s,fun j => hs (word j)⟩
    exact value_splice μ (fun j => weight (word j)) k g i hμ (fun j => (hw _).le)
      (fun _ _ => view_refines hab)
      (fun (s : Anchored G x) j => atHit R u T a x s (word j))
      (fun (s : Anchored G y) j => atHit R u T e y s (word j)) splice

omit [Nonempty Ω] in
/-- A single legal weighted label, including its first placement and terminal
continuation. The deadline refers to the original window's actual deadline. -/
theorem weighted_label (G : SimpleGraph V) (hc : G.Connected)
    (μ : Ω → ℝ) (hμ : ∀ i, 0 < μ i) (law : ∑ i, μ i=1) (word : Ω → W)
    (weight : W → ℝ) (hw : ∀ w, 0 < weight w) (R : W → ℕ → V)
    (u T v B h b : ℕ) (hB : 0 < B) (hh : 0 < h) (z : ℕ → Ω → V)
    (leg : ∀ j i, G.dist (z (j+1) i) (z j i) ≤ B) (starts : V → Prop)
    [Nonempty {s : WindowPolicy G // starts s.start}] (allow : ∀ i, starts (z b i))
    (deadline : time v B (row B h b) ≤ T) (cost : W → ℝ)
    (trial : List V → (x : V) → Mixture (Anchored G x))
    (correct : ∀ i, Real.exp (-cost (word i)) ≤
      (trial (reveal R u v B (row B h b+1) (word i)) (z (column B h b) i)).success
        (atHit R u T (time v B (row B h b)) (z (column B h b) i)) (word i)) :
    let C := fun t i => reveal R u v B t (word i)
    let E := fun t j => condEntropy μ (C t) (z j)
    let A := fun t => expect μ (fun i => Real.log (score G μ word weight R u T v B z starts b t i))
    (A 0 ≤ Real.log (initialValue G μ word weight R u T starts)) ∧
    (∀ t ≤ row B h b, A (t+1)-A t ≤ E t (b-t)-E (t+1) (b-t)) ∧
    (expect μ (fun i => Real.log (weight (word i))-cost (word i)) -
      E (row B h b+1) (column B h b) + condEntropy μ word (z (column B h b)) ≤ A (row B h b+1)) := by
  classical
  let C := fun t i => reveal R u v B t (word i)
  let f := row B h b
  let S := score G μ word weight R u T v B z starts b
  let nv := node G μ word weight R u T v B
  have term := terminal_entropy μ hμ word (reveal R u v B (f+1)) (z (column B h b)) weight cost hw
    (atHit (G:=G) R u T (time v B f)) trial correct
  have past (t : ℕ) (ht : t ≤ f) : time v B t ≤ T := by
    have e := Nat.mul_le_mul_right B ht
    change v+t*B ≤ T
    change v+f*B ≤ T at deadline
    omega
  have move (t : ℕ) (ht : t ≤ f) (i : Ω) :
      avgOn μ (atom (C t) i) (fun j => nv t (C (t+1) j) (z (b-t) i)) ≤ S t i :=
    bellman_move G hc μ hμ word weight hw R u T v B z leg starts b t allow
      (ht.trans (last_le hB hh b)) (past t ht) i
  have nonneg (t : ℕ) (c : List V) (x : V) : 0 ≤ nv t c x :=
    value_nonneg μ _ _ _ (fun j => (hμ j).le) (fun j => (hw (word j)).le)
  have pos : ∀ rem t, rem+t=f+1 → ∀ i, 0 < S t i := by
    intro rem; induction rem with
    | zero =>
      intro t e; have et : t=f+1 := by omega
      subst t; exact term.1
    | succ rem ih =>
      intro t e i
      have hnext := ih (t+1) (by omega) i
      apply lt_of_lt_of_le _ (move t (by omega) i)
      apply div_pos _ (atom_mass_pos μ hμ (C t) i)
      apply sum_pos'
      · exact fun j _ => mul_nonneg (hμ j).le (nonneg ..)
      · exact ⟨i,mem_own_fiber _ _,mul_pos (hμ i) hnext⟩
  refine ⟨?_,?_,term.2⟩
  · simp only [score,expect_const μ law]; rfl
  · intro t ht
    change expect μ (fun i => Real.log (nv t (C (t+1) i) (z (b-t) i))) -
      expect μ (fun i => Real.log (S t i)) ≤ _
    apply reveal_entropy μ (C t) (C (t+1)) (z (b-t)) (nv t) (S t) hμ (nonneg t)
      (pos _ (t+1) (show (f-t)+(t+1)=f+1 by omega)) _ (move t ht)
    intro j i he
    cases t with
    | zero => rfl
    | succ t =>
      apply view_refines _ he
      simp only [time,Nat.succ_mul]
      omega

/-- The clock lemma, with arbitrary independent true-word law and latent
smoothed vertices. The output is the logarithm of the value of an actual
legal strategy placed prior to both prehistory observations. -/
theorem graph_clock_pass (G : SimpleGraph V) (hc : G.Connected)
    (μ : Ω → ℝ) (hμ : ∀ i, 0 < μ i) (law : ∑ i, μ i=1) (word : Ω → W)
    (weight : W → ℝ) (hw : ∀ w, 0 < weight w) (R : W → ℕ → V)
    (u T v B h M D N : ℕ) (hB : 0 < B) (hh : 0 < h) (hsmall : h ≤ B)
    [Fintype V] (hN : Fintype.card V ≤ N) (z : ℕ → Ω → V)
    (leg : ∀ j i, G.dist (z (j+1) i) (z j i) ≤ B) (starts : V → Prop)
    [Nonempty {s : WindowPolicy G // starts s.start}]
    (allow : ∀ b ≤ top B h M, ∀ i, starts (z b i))
    (deadline : ∀ b ≤ top B h M, time v B (row B h b) ≤ T)
    (home : ∀ j, M+D ≤ j → ∀ a b, z j a=z j b)
    (large : ℕ → W → ℝ) (d : ℕ → W → ℝ) (large_nonneg : ∀ j ≤ M, ∀ w, 0 ≤ large j w)
    (support : ∀ j ≤ M, ∀ t ∈ Icc (height B h (j-1)) (height B h j), ∀ i,
      (((atom (fun l => reveal R u v B (t+1) (word l)) i).image (z j)).card : ℝ) ≤
        Real.exp (large j (word i)))
    (trial : ℕ → List V → (x : V) → Mixture (Anchored G x))
    (correct : ∀ b ≤ top B h M, ∀ i, Real.exp (-(large (column B h b) (word i)/2+d b (word i))) ≤
      (trial b (reveal R u v B (row B h b+1) (word i)) (z (column B h b) i)).success
        (atHit R u T (time v B (row B h b)) (z (column B h b) i)) (word i)) :
    let J := top B h M+1
    let empty := fun _ : Ω => ([] : List V)
    let s := initialValue G μ word weight R u T starts
    expect μ (fun i => Real.log (weight (word i))) -
      ((∑ j ∈ range M, condEntropy μ empty (z j))+D*Real.log N)/(J:ℝ) -
      (∑ b ∈ range J, (expect μ (fun i => large (column B h b) (word i)) -
        condEntropy μ word (z (column B h b)) + expect μ (fun i => d b (word i)))) / (J:ℝ)
      ≤ Real.log s := by
  classical
  let C := fun t i => reveal R u v B t (word i)
  let E := fun t j => condEntropy μ (C t) (z j)
  let A := fun b t => expect μ (fun i => Real.log (score G μ word weight R u T v B z starts b t i))
  let L := fun j => expect μ (fun i => large j (word i))
  let d' := fun b => expect μ (fun i => d b (word i))
  let small := fun j => condEntropy μ word (z j)
  have labelled (b : ℕ) (hb : b ≤ top B h M) :=
    weighted_label G hc μ hμ law word weight hw R u T v B h b hB hh z leg starts (allow b hb)
      (deadline b hb) (fun w => large (column B h b) w/2+d b w) (trial b) (correct b hb)
  have npos : 1 ≤ N := (Fintype.card_pos_iff.mpr ⟨z 0 (Classical.arbitrary Ω)⟩).trans_le hN
  refine clock_pass hB hh hsmall M D E L small d' A _ _ _
    (fun t j => condEntropy_nonneg μ hμ (C t) (z j))
    (Real.log_nonneg (by exact_mod_cast npos)) ?_ ?_ ?_ ?_
    (fun b hb => (labelled b hb).1) (fun b hb => (labelled b hb).2.1) ?_
  · intro j
    calc
      _ ≤ expect μ (fun _ => Real.log N) := condEntropy_le_log_support μ hμ (C 0) (z j) (fun _ => N)
        (fun i => by exact_mod_cast (Finset.card_le_univ _).trans hN)
      _ = _ := expect_const μ law _
  · intro j hj; exact condEntropy_zero_of_constant μ hμ (C 0) (z j) (home j hj)
  · intro j hj; exact sum_nonneg (fun i _ => mul_nonneg (hμ i).le (large_nonneg j hj (word i)))
  · intro j hj t ht
    have he := condEntropy_le_log_support μ hμ (C (t+1)) (z j)
      (fun i => Real.exp (large j (word i))) (support j hj t ht)
    simpa only [Real.log_exp] using he
  · intro b hb
    have ht := (labelled b hb).2.2
    have he : expect μ (fun i => Real.log (weight (word i)) -
        (large (column B h b) (word i)/2+d b (word i))) =
        expect μ (fun i => Real.log (weight (word i)))-L (column B h b)/2-d' b := by
      simp only [expect,L,d',mul_sub,mul_add,← mul_div_assoc,sum_sub_distrib,sum_add_distrib,
        ← sum_div]; ring
    rw [he] at ht
    exact ht

end
end Meyniel.Multiscale.GraphClock

