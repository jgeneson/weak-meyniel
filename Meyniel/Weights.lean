module

public import Meyniel.Interception

/-! The posted proof's forward probability calculation. For a specified observed
prefix, a vector stores the conditional probability of each live guessed walk.
A reveal first adds all live mass arriving at the same vertex and then divides
that mass equally among the compatible walks. Missing matches contribute zero.
-/

@[expose] public section

namespace Meyniel.ForwardWeights

open Finset Interception

noncomputable section

variable {W K V : Type*} [Fintype W] [DecidableEq K] [DecidableEq V]

def block (k : W → K) (w : W) : Finset W := fiber k (k w)

def joint (k : W → K) (x : W → V) (w : W) : Finset W :=
  fiber (fun z => (k z, x z)) (k w, x w)

def conditional (k : W → K) (x : W → V) (w : W) : ℝ :=
  ((joint k x w).card : ℝ) / (block k w).card

theorem block_pos (k : W → K) (w : W) : 0 < ((block k w).card : ℝ) := by
  exact_mod_cast (show (block k w).Nonempty from ⟨w, mem_own_fiber k w⟩).card_pos

theorem joint_pos (k : W → K) (x : W → V) (w : W) : 0 < ((joint k x w).card : ℝ) :=
  block_pos (fun z => (k z,x z)) w

theorem conditional_bound (k : W → K) (x : W → V) (w : W) :
    0 < conditional k x w ∧ conditional k x w ≤ 1 := by
  have h : joint k x w ⊆ block k w := by
    intro v hv
    apply mem_filter.mpr
    exact ⟨mem_univ _, congrArg Prod.fst (mem_filter.mp hv).2⟩
  exact ⟨div_pos (joint_pos k x w) (block_pos k w), (div_le_one (block_pos k w)).mpr
    (by exact_mod_cast card_le_card h)⟩

/-- Splitting the old conditional mass at the current vertex equally among the
compatible new guesses. Only the positive-sized block of a tagged walk is used. -/
def splitMass (oldKey newKey : W → K) (x : W → V) (mass : W → ℝ) (w : W) : ℝ :=
  (∑ z ∈ joint oldKey x w, mass z) / (joint newKey x w).card

def weight (k : W → K) (mass : W → ℝ) (w : W) : ℝ := (block k w).card * mass w

theorem split_weight (oldKey newKey : W → K) (x : W → V) (mass : W → ℝ) (w : W) :
    weight newKey (splitMass oldKey newKey x mass) w =
      blockMean (fun z => (oldKey z, x z)) (weight oldKey mass) w *
        conditional oldKey x w / conditional newKey x w := by
  have sum_weight :
      ∑ z ∈ joint oldKey x w, weight oldKey mass z =
      (block oldKey w).card * ∑ z ∈ joint oldKey x w, mass z := by
    rw [mul_sum]
    apply sum_congr rfl
    intro z hz
    have he : oldKey z = oldKey w := congrArg Prod.fst (mem_filter.mp hz).2
    simp [weight, block, he]
  change (block newKey w).card * ((∑ z ∈ joint oldKey x w, mass z) / _) =
    ((∑ z ∈ joint oldKey x w, weight oldKey mass z) / (joint oldKey x w).card) *
    (((joint oldKey x w).card : ℝ) / (block oldKey w).card) /
    (((joint newKey x w).card : ℝ) / (block newKey w).card)
  rw [sum_weight]
  field_simp [ne_of_gt (block_pos oldKey w), ne_of_gt (block_pos newKey w),
    ne_of_gt (joint_pos oldKey x w), ne_of_gt (joint_pos newKey x w)]

/-- Averaging weights over all tagged walks is exactly the expectation of the
total live probability conditional on the independently sampled true prefix. -/
theorem mean_total_live (k : W → K) (mass : W → ℝ) :
    mean univ (fun w => ∑ z ∈ block k w, mass z) = mean univ (weight k mass) := by
  unfold mean
  congr 1
  rw [← sum_by_fiber k (fun w => ∑ z ∈ block k w, mass z), ← sum_by_fiber k (weight k mass)]
  apply sum_congr rfl
  intro h _
  calc
    _ = ∑ _w ∈ fiber k h, ∑ z ∈ fiber k h, mass z := by
      apply sum_congr rfl
      intro w hw
      simp [block, (mem_filter.mp hw).2]
    _ = ((fiber k h).card : ℝ) * ∑ z ∈ fiber k h, mass z := by simp
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro w hw
      simp [weight, block, (mem_filter.mp hw).2]

theorem conditional_initial (k : W → K) (hk : ∀ v w, k v = k w) (x : W → V) :
    conditional k x = frequency x := by
  funext w
  have hb : block k w = univ := by ext v; simp [block,fiber,hk v w]
  have hj : joint k x w = fiber x (x w) := by ext v; simp [joint,fiber,hk v w]
  simp [conditional, frequency, hb, hj]

variable [Nonempty W]

/-- Live guess mass for one fixed diagonal. The initial guess is uniformly
sampled from the original family before the first reveal. -/
def guessMass (history : ℕ → W → K) (X : ℕ → W → V) (b : ℕ) : ℕ → W → ℝ
  | 0 => fun _ => 1 / Fintype.card W
  | t+1 => splitMass (history t) (history (t+1)) (X (b-t)) (guessMass history X b t)

theorem guessMass_pos (history : ℕ → W → K) (X : ℕ → W → V) (b t : ℕ) :
    ∀ w, 0 < guessMass history X b t w := by
  induction t with
  | zero => intro w; exact one_div_pos.mpr (by exact_mod_cast Fintype.card_pos (α := W))
  | succ t ih =>
    intro w
    exact div_pos (sum_pos (fun z _ => ih z)
      ⟨w, mem_own_fiber (fun z => (history t z,X (b-t) z)) w⟩) (joint_pos ..)

def terminalLive (history : ℕ → W → K) (X : ℕ → W → V) (b : ℕ) : ℝ :=
  mean univ (fun w => ∑ z ∈ block (history (b/2+1)) w, guessMass history X b (b/2+1) z)

theorem forward_diagonal (history : ℕ → W → K) (X : ℕ → W → V) (b : ℕ)
    (hinit : ∀ x y, history 0 x = history 0 y) :
    0 < terminalLive history X b ∧ diagonalSum b (fun t j =>
      logMean (conditional (history t) (X j)) - logMean (conditional (history (t+1)) (X j))) ≤
      Real.log (terminalLive history X b) := by
  let mass := guessMass history X b
  let wt := fun t => weight (history t) (mass t)
  have hwt t w : 0 < wt t w := mul_pos (block_pos _ w) (guessMass_pos history X b t w)
  have hzero : wt 0 = fun _ => 1 := by
    funext w
    have h : block (history 0) w = univ := by
      ext z; simp [block,fiber,hinit z w]
    simp [wt,weight,mass,guessMass,h,Fintype.card_ne_zero]
  have he := forward_telescope b (fun t j =>
      logMean (conditional (history t) (X j)) - logMean (conditional (history (t+1)) (X j)))
    (fun t => logMean (wt t)) (fun t _ =>
      logMean_update (fun z => (history t z,X (b-t) z)) (wt t) (wt (t+1)) _ _
        (hwt t) (fun w => (conditional_bound _ _ w).1) (fun w => (conditional_bound _ _ w).1)
        (split_weight _ _ _ _))
  rw [hzero, logMean_one, sub_zero] at he
  unfold terminalLive
  rw [mean_total_live]
  exact ⟨mean_pos univ_nonempty (fun w _ => hwt _ w), he.trans (logMean_le_log_mean (hwt _))⟩

/-- The posted forward-sampler estimate on terminal live mass for concrete
history and position tables, obtained directly from the uniform split law. -/
theorem exists_good_forward [Fintype V] (history : ℕ → W → K) (X : ℕ → W → V)
    (T d n : ℕ) (hn : 1 ≤ n) (hsize : Fintype.card V ≤ n)
    (hT : (d : ℝ)*Real.log n ≤ (T : ℝ)*Real.log 2)
    (hinit : ∀ x y, history 0 x = history 0 y)
    (hhome : ∀ j, T+d ≤ j → ∀ x y, X j x = X j y) :
    ∃ b ≤ 2*T, 1 / Real.sqrt (2*n) ≤ terminalLive history X b := by
  exact exists_good_from_diagonal T d n hn hsize hT X
    (fun t j => conditional (history t) (X j)) (terminalLive history X)
    (fun _ _ => conditional_bound _ _) (fun _ => conditional_initial _ hinit _)
    hhome (fun b _ => forward_diagonal history X b hinit)


omit [Nonempty W] in
/-- Uniform averaging on fibers is self-adjoint for the counting measure. -/
theorem sum_blockMean_mul (k : W → K) (f g : W → ℝ) :
    (∑ w, blockMean k f w * g w) = ∑ w, f w * blockMean k g w := by
  rw [← sum_by_fiber k (fun w => blockMean k f w * g w),
      ← sum_by_fiber k (fun w => f w * blockMean k g w)]
  apply sum_congr rfl
  intro i _
  let A := fiber k i
  calc
    _ = ∑ w ∈ A, mean A f * g w := by
      apply sum_congr rfl
      intro w hw
      simp [blockMean, (mem_filter.mp hw).2, A]
    _ = (∑ w ∈ A, f w) * mean A g := by rw [← mul_sum]; unfold mean; ring
    _ = ∑ w ∈ A, f w * mean A g := by rw [sum_mul]
    _ = _ := by
      apply sum_congr rfl
      intro w hw
      simp [blockMean, (mem_filter.mp hw).2, A]

omit [Nonempty W] in
/-- The live forward mass paired with a backward value cannot increase when
the latter dominates the conditional arithmetic mean of all next positions. -/
theorem pairing_step (k : W → K) (old new pre post vOld vNew : W → ℝ)
    (hpos : ∀ w, 0 ≤ old w)
    (hnew : ∀ w, new w = blockMean k old w * pre w / post w)
    (hv : ∀ w, blockMean k (fun z => vNew z * pre z / post z) w ≤ vOld w) :
    mean univ (fun w => new w * vNew w) ≤ mean univ (fun w => old w * vOld w) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    ∑ w, new w * vNew w = ∑ w, blockMean k old w * (vNew w * pre w / post w) := by
      apply sum_congr rfl
      intro w _
      rw [hnew]
      ring
    _ = _ := sum_blockMean_mul k old (fun z => vNew z * pre z / post z)
    _ ≤ _ := sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hv w) (hpos w))

/-- The same explicit forward mass can be compared directly with *any*
Bellman supersolution, using the arithmetic adjoint at each cell. -/
theorem terminalLive_le_bellman (history : ℕ → W → K) (X : ℕ → W → V) (b : ℕ)
    (hinit : ∀ x y, history 0 x = history 0 y)
    (v : ℕ → W → ℝ) (s : ℝ) (hend : ∀ w, v (b/2+1) w = 1) (hstart : ∀ w, v 0 w ≤ s)
    (hstep : ∀ t ≤ b/2, ∀ w,
      blockMean (fun z => (history t z,X (b-t) z))
        (fun z => v (t+1) z * conditional (history t) (X (b-t)) z /
           conditional (history (t+1)) (X (b-t)) z) w ≤ v t w) :
    terminalLive history X b ≤ s := by
  let wt := fun t => weight (history t) (guessMass history X b t)
  let pair := fun t => mean univ (fun w => wt t w * v t w)
  have hs (t : ℕ) (ht : t ≤ b/2) : pair (t+1) ≤ pair t := by
    exact pairing_step (fun z => (history t z,X (b-t) z)) _ _ _ _ _ _
      (fun z => (mul_pos (block_pos _ z) (guessMass_pos history X b t z)).le)
      (split_weight _ _ _ _) (hstep t ht)
  have hm (t : ℕ) (ht : t ≤ b/2+1) : pair t ≤ pair 0 := by
    induction t with
    | zero => rfl
    | succ i ih => exact (hs i (by omega)).trans (ih (by omega))
  have he : pair (b/2+1) = terminalLive history X b := by
    simp only [pair, hend, mul_one, terminalLive, mean_total_live, wt]
  have hw (w : W) : wt 0 w = 1 := by
    have h : block (history 0) w = univ := by ext z; simp [block,fiber,hinit z w]
    simp [wt,weight,guessMass,h,Fintype.card_ne_zero]
  have h0 : pair 0 ≤ s := by
    simp only [pair,hw,one_mul,mean]
    apply (div_le_iff₀ (by exact_mod_cast (univ_nonempty : (univ : Finset W).Nonempty).card_pos)).2
    simpa [Finset.sum_const, mul_comm] using sum_le_sum (s := (univ : Finset W)) (fun w _ => hstart w)
  rw [← he]
  exact (hm _ le_rfl).trans h0


omit [Nonempty W] in
/-- For a prescribed next robber observation the total live guess mass can
only decrease. The only loss is old mass at vertices with no compatible tag. -/
theorem splitMass_total_le [Fintype V] (oldKey newKey : W → K) (x : W → V)
    (mass : W → ℝ) (w : W) (hn : ∀ z, 0 ≤ mass z)
    (refines : ∀ a b, newKey a = newKey b → oldKey a = oldKey b) :
    ∑ z ∈ block newKey w, splitMass oldKey newKey x mass z ≤ ∑ z ∈ block oldKey w, mass z := by
  classical
  rw [← sum_fiberwise (block newKey w) x, ← sum_fiberwise (block oldKey w) x]
  apply sum_le_sum
  intro y _
  let A := (block oldKey w).filter fun z => x z = y
  let B := (block newKey w).filter fun z => x z = y
  change (∑ z ∈ B, splitMass oldKey newKey x mass z) ≤ ∑ z ∈ A, mass z
  by_cases hB : B.Nonempty
  · have hb : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
    have he (z : W) (hz : z ∈ B) : splitMass oldKey newKey x mass z = (∑ v ∈ A, mass v)/B.card := by
      obtain ⟨hnw, hxy⟩ := mem_filter.mp hz
      have hnew : newKey z = newKey w := (mem_filter.mp hnw).2
      have hold := refines _ _ hnew
      have ha : joint oldKey x z = A := by
        ext v; simp only [joint,block,fiber,A,mem_filter,mem_univ,true_and,Prod.mk.injEq,hold,hxy]
      have hc : joint newKey x z = B := by
        ext v; simp only [joint,block,fiber,B,mem_filter,mem_univ,true_and,Prod.mk.injEq,hnew,hxy]
      simp [splitMass, ha,hc]
    rw [sum_congr rfl he, sum_const,nsmul_eq_mul]
    exact le_of_eq (by field_simp)
  · rw [not_nonempty_iff_eq_empty.mp hB, sum_empty]
    exact sum_nonneg (fun z _ => hn z)

theorem total_live_le_one [Fintype V] (history : ℕ → W → K) (X : ℕ → W → V)
    (refines : ∀ t a b, history (t+1) a = history (t+1) b → history t a = history t b)
    (b t : ℕ) (w : W) :
    ∑ z ∈ block (history t) w, guessMass history X b t z ≤ 1 := by
  induction t with
  | zero =>
    have h : (block (history 0) w).card ≤ Fintype.card W := card_le_univ _
    simp only [guessMass, sum_const, nsmul_eq_mul]
    rw [mul_one_div, div_le_one (by exact_mod_cast Fintype.card_pos (α := W))]
    exact_mod_cast h
  | succ t ih =>
    exact (splitMass_total_le _ _ _ _ w (fun z => (guessMass_pos history X b t z).le) (refines t)).trans ih

end
end Meyniel.ForwardWeights
