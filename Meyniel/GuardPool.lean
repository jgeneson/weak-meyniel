module

public import Meyniel.PhysicalPolicy

/-! Reserve cops are shared between potential guard assignments whose locations
depend on the observed play. The number required is the largest number actually
dispatched on one walk. The online allocation below fixes a cop's assignment
permanently, even when other walks would have triggered different jobs. -/

@[expose] public section

namespace Meyniel.Multiscale.GuardPool
open Meyniel.Multiscale

variable {J V : Type*} {G : SimpleGraph V} [DecidableEq J]

noncomputable def queue (a : (ℕ → V) → ℕ → Finset J) (R : ℕ → V) : ℕ → List J
  | 0 => []
  | t+1 =>
    let old := queue a R t
    old ++ (a R t \ old.toFinset).toList

theorem queue_nodup (a : (ℕ → V) → ℕ → Finset J) (R : ℕ → V) (t : ℕ) :
    (queue a R t).Nodup := by
  induction t with
  | zero => simp [queue]
  | succ t ih =>
    rw [queue,List.nodup_append]
    refine ⟨ih,Finset.nodup_toList _,?_⟩
    intro i hi j hj e
    subst j
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hj)).2 (List.mem_toFinset.mpr hi)

theorem mem_queue {a : (ℕ → V) → ℕ → Finset J} {R : ℕ → V} {j : J} {t : ℕ} :
    j ∈ queue a R t ↔ ∃ f < t, j ∈ a R f := by
  induction t with
  | zero => simp [queue]
  | succ t ih =>
    simp only [queue,List.mem_append,Finset.mem_toList,Finset.mem_sdiff,List.mem_toFinset]
    simp only [ih]
    have split : ((∃ f < t, j ∈ a R f) ∨ j ∈ a R t ∧ ¬ (∃ f < t, j ∈ a R f)) ↔ ((∃ f < t, j ∈ a R f) ∨ j ∈ a R t) := by
      by_cases P : ∃ f < t, j ∈ a R f <;> simp [P]
    rw [split]
    constructor
    · rintro (⟨f,hf,h⟩ | h)
      · exact ⟨f,by omega,h⟩
      · exact ⟨t,by omega,h⟩
    · rintro ⟨f,hf,h⟩
      by_cases eq : f = t
      · exact Or.inr (eq ▸ h)
      · exact Or.inl ⟨f,by omega,h⟩

private theorem queue_prefix (a : (ℕ → V) → ℕ → Finset J) (R : ℕ → V) {t T : ℕ} (h : t ≤ T) :
    queue a R t <+: queue a R T := by
  induction T, h using Nat.le_induction with
  | base => exact ⟨[],by simp⟩
  | succ T _ ih => exact ih.trans (List.prefix_append ..)

private theorem queue_causal {a : (ℕ → V) → ℕ → Finset J}
    (obs : ∀ R S, SpeedOne G R → SpeedOne G S → ∀ t, SameThrough R S (t+2) → a R t = a S t)
    {R S : ℕ → V} (hr : SpeedOne G R) (hs : SpeedOne G S) (t : ℕ) (eq : SameThrough R S (t+1)) :
    queue a R t = queue a S t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 := ih (eq.restrict (by omega))
    have h2 := obs R S hr hs t eq
    simp only [queue,h1,h2]

omit [DecidableEq J] in
private theorem inactive_at_slot {l l' : List J} (p : l <+: l') (nd : l'.Nodup)
    {i : ℕ} (ho : l.length ≤ i) (hn : i < l'.length) : l'[i] ∉ l := by
  intro h
  obtain ⟨j,hj,eq⟩ := List.getElem_of_mem h
  have hh : l'[j]'(hj.trans_le p.length_le) = l'[i] := (p.getElem hj).symm.trans eq
  have := (List.getElem_inj nd).mp hh
  omega

noncomputable def slotPos (jobs : J → PhysicalPolicy G) (a : (ℕ → V) → ℕ → Finset J)
    (i : ℕ) (R : ℕ → V) (t : ℕ) : V :=
  if h : i < (queue a R t).length then (jobs (queue a R t)[i]).pos R t else R t

/-- One fixed physical slot reads the visible queue and either follows
the trail or continues its permanently assigned legal guard strategy. -/
noncomputable def slot (jobs : J → PhysicalPolicy G) (a : (ℕ → V) → ℕ → Finset J)
    (obs : ∀ R S, SpeedOne G R → SpeedOne G S → ∀ t, SameThrough R S (t+2) → a R t = a S t)
    (idle : ∀ R, SpeedOne G R → ∀ j t, j ∉ queue a R t → (jobs j).pos R t = R t)
    (i : ℕ) : PhysicalPolicy G where
  pos := slotPos jobs a i
  causal R S hr hs t eq := by
    have hg := queue_causal obs hr hs t eq
    unfold slotPos
    rw [hg]
    split
    · exact (jobs _).causal R S hr hs t eq
    · exact eq t (by omega)
  step R hR t := by
    have pref := queue_prefix a R (Nat.le_succ t)
    by_cases hi : i < (queue a R t).length
    · have hi' := hi.trans_le pref.length_le
      simp only [slotPos,dif_pos hi,dif_pos hi']
      exact (congrArg (fun j => Step G ((jobs (queue a R t)[i]).pos R t) ((jobs j).pos R (t+1))) (pref.getElem hi)).mp ((jobs _).step R hR t)
    · by_cases hi' : i < (queue a R (t+1)).length
      · have hm := inactive_at_slot pref (queue_nodup a R (t+1)) (Nat.le_of_not_gt hi) hi'
        have hh := idle R hR _ t hm
        simp only [slotPos,dif_neg hi,dif_pos hi',←hh]
        exact (jobs _).step R hR t
      · simpa only [slotPos,dif_neg hi,dif_neg hi'] using hR t

@[simp] theorem slot_start (jobs : J → PhysicalPolicy G) (a : (ℕ → V) → ℕ → Finset J)
    (obs idle) (i : ℕ) (R : ℕ → V) : (slot jobs a obs idle i).pos R 0 = R 0 := by
  simp [slot,slotPos,queue]

/-- Once a job is assigned, its physical slot has followed its entire
trajectory, including the common trail before activation. -/
theorem preserving_slot {jobs : J → PhysicalPolicy G} {a : (ℕ → V) → ℕ → Finset J}
    (obs idle) {K : ℕ} {R : ℕ → V} (hr : SpeedOne G R) {j : J} {T : ℕ}
    (enough : (queue a R T).length ≤ K) (assigned : j ∈ queue a R T) :
    ∃ i : Fin K, ∀ t ≤ T, (slot jobs a obs idle i.val).pos R t = (jobs j).pos R t := by
  obtain ⟨i,hi,hj⟩ := List.getElem_of_mem assigned
  refine ⟨⟨i,hi.trans_le enough⟩,?_⟩
  intro t ht
  have pref := queue_prefix a R ht
  change slotPos jobs a i R t = _
  unfold slotPos
  split
  next before => exact congrArg (fun j => (jobs j).pos R t) ((pref.getElem before).trans hj)
  next after =>
    have inactive := inactive_at_slot pref (queue_nodup ..) (Nat.le_of_not_gt after) hi
    rw [hj] at inactive
    exact (idle R hr j t inactive).symm

end Meyniel.Multiscale.GuardPool
