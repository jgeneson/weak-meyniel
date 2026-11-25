import Meyniel.MultiscaleBands

/-! A legal physical policy evaluated on complete plays, with an explicit
test that its current position depends only on observations already made.
This representation supports time-shifted and staggered local strategies. -/
namespace Meyniel.Multiscale
variable {V : Type*} {G : SimpleGraph V}

def SameThrough (R S : ℕ → V) (t : ℕ) : Prop := ∀ i ≤ t, R i = S i

lemma SameThrough.restrict {R S : ℕ → V} {s t : ℕ} (h : SameThrough R S t) (hs : s ≤ t) :
    SameThrough R S s := fun i hi => h i (hi.trans hs)

/-- At the start of round t the last robber vertex a cop used was R(t+1).
The most recently observed R(t+2) can influence the position at t+1.
R(0) and R(1) are the two vertices preceding the game window. -/
structure PhysicalPolicy (G : SimpleGraph V) where
  pos : (ℕ → V) → ℕ → V
  step : ∀ R, SpeedOne G R → ∀ t, Step G (pos R t) (pos R (t+1))
  causal : ∀ R S, SpeedOne G R → SpeedOne G S → ∀ t,
    SameThrough R S (t+1) → pos R t = pos S t

def PhysicalHit (g : PhysicalPolicy G) (R : ℕ → V) (u v : ℕ) : Prop :=
  ∃ t, u ≤ t ∧ t ≤ v ∧ (g.pos R t = R (t+2) ∨ t < v ∧ g.pos R (t+1) = R (t+2))

theorem PhysicalHit.mono {g : PhysicalPolicy G} {R : ℕ → V} {u v a b : ℕ}
    (h : PhysicalHit g R u v) (ha : a ≤ u) (hb : v ≤ b) : PhysicalHit g R a b := by
  obtain ⟨t,h1,h2,hit | ⟨h3,hit⟩⟩ := h
  · exact ⟨t,ha.trans h1,h2.trans hb,Or.inl hit⟩
  · exact ⟨t,ha.trans h1,h2.trans hb,Or.inr ⟨h3.trans_le hb,hit⟩⟩

def trail (G : SimpleGraph V) : PhysicalPolicy G where
  pos R t := R t
  step R h t := h t
  causal R S _ _ t h := h t (by omega)

private def update (R : ℕ → V) (t : ℕ) (z : V) (i : ℕ) : V := if i ≤ t then R i else z

private theorem update_speed {R : ℕ → V} {t : ℕ} {z : V} (hR : SpeedOne G R)
    (hn : Step G (R t) z) : SpeedOne G (update R t z) := by
  intro i
  by_cases hi : i < t
  · simpa [update,hi.le, show i+1 ≤ t by omega] using hR i
  · by_cases e : i = t
    · subst i; simpa [update] using hn
    · simp [update,show ¬i≤t by omega,show ¬i+1≤t by omega,Step]

/-- Any collection of causal legal trajectories covering all walks in the
window is a winning ordinary team, with the same fixed start and deadline. -/
theorem physical_cover_gives_game {n T : ℕ} (g : Fin n → PhysicalPolicy G)
    {x y r : V} {starts : Fin n → V} (xy : Step G x y) (yr : Step G y r)
    (init : ∀ R, SpeedOne G R → R 0 = x → R 1 = y → R 2 = r → ∀ i, (g i).pos R 0 = starts i)
    (cover : ∀ R, SpeedOne G R → R 0 = x → R 1 = y → R 2 = r → ∃ i, PhysicalHit (g i) R 0 T) :
    CatchesWithin G n T starts r := by
  have run : ∀ fuel t, t+fuel = T → ∀ R : ℕ → V, SpeedOne G R →
      (∀ S, SpeedOne G S → SameThrough R S (t+2) → ∃ i, PhysicalHit (g i) S t T) →
      CatchesWithin G n fuel (fun i => (g i).pos R t) (R (t+2)) := by
    intro fuel
    induction fuel with
    | zero =>
      intro t ht R hR cap
      obtain ⟨i,j,h1,h2,hit | ⟨h3,_⟩⟩ := cap R hR (fun _ _ => rfl)
      · have eq : j=t := by omega
        exact ⟨i,eq ▸ hit⟩
      · omega
    | succ fuel ih =>
      intro t ht R hR cap
      by_cases already : ∃ i, (g i).pos R t = R (t+2)
      · exact Or.inl already
      refine Or.inr ⟨fun i => (g i).pos R (t+1), fun i => (g i).step R hR t, ?_⟩
      by_cases moved : ∃ i, (g i).pos R (t+1) = R (t+2)
      · exact Or.inl moved
      refine Or.inr fun s hs => ?_
      let S := update R (t+2) s
      have hS : SpeedOne G S := update_speed hR hs
      have eqR : SameThrough R S (t+2) := fun j hj => by simp [S,update,hj]
      have eqC : (fun i => (g i).pos R (t+1)) = (fun i => (g i).pos S (t+1)) :=
        funext fun i => (g i).causal R S hR hS (t+1) eqR
      have eqS : S (t+1+2) = s := by simp [S,update]
      rw [eqC, ←eqS]
      apply ih (t+1) (by omega) S hS
      intro U hU eqU
      have joint : SameThrough R U (t+2) := fun j hj => (eqR j hj).trans (eqU j (by omega))
      obtain ⟨i,j,h1,h2,hit⟩ := cap U hU joint
      by_cases e : j = t
      · subst j
        rcases hit with hit | ⟨_,hit⟩
        · exact (already ⟨i,((g i).causal R U hR hU t (joint.restrict (by omega))).trans
            (hit.trans (joint _ le_rfl).symm)⟩).elim
        · exact (moved ⟨i,((g i).causal R U hR hU (t+1) joint).trans
            (hit.trans (joint _ le_rfl).symm)⟩).elim
      · exact ⟨i,j,by omega,h2,hit⟩
  let R : ℕ → V := fun i => if i=0 then x else if i=1 then y else r
  have hR : SpeedOne G R := by
    intro i
    rcases i with _ | _ | i
    · simpa [R] using xy
    · simpa [R] using yr
    · simp [R,Step]
  have start := funext (init R hR (by simp [R]) (by simp [R]) (by simp [R]))
  rw [←start]
  simpa only [show R (0+2) = r by simp [R]] using
    run T 0 (by omega) R hR (fun S hS eq => cover S hS
      ((eq 0 (by omega)).symm.trans (by simp [R]))
      ((eq 1 (by omega)).symm.trans (by simp [R]))
      ((eq 2 (by omega)).symm.trans (by simp [R])))

end Meyniel.Multiscale
