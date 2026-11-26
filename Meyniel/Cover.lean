module

public import Meyniel.Game

/-! # Deterministic covering and adaptive robbers -/

@[expose] public section

namespace Meyniel

universe u v

/-- Choosing the strategies successively on the *remaining* walks pays a logarithmic
factor, and requires no control over overlaps outside that remaining set. -/
theorem greedy_residual {W : Type u} {S : Type v} (C : S → W → Prop) [∀ s, DecidablePred (C s)] (p : ℝ)
    (hp : p ≤ 1) (U : Finset W)
    (select : ∀ R ⊆ U, R.Nonempty → ∃ s, p * R.card ≤ (R.filter (C s)).card)
    (m : ℕ) :
    ∃ team : List S, team.length ≤ m ∧
      (↑(U.filter (fun w => ∀ s ∈ team, ¬ C s w)).card : ℝ) ≤ U.card * (1-p)^m := by
  classical
  induction m with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ m ih =>
    obtain ⟨team, hl, hb⟩ := ih
    let R := U.filter (fun w => ∀ s ∈ team, ¬ C s w)
    by_cases hR : R.Nonempty
    · obtain ⟨s, hs⟩ := select R (Finset.filter_subset ..) hR
      refine ⟨s :: team, by simp; omega, ?_⟩
      have hsame : U.filter (fun w => ∀ z ∈ s :: team, ¬ C z w) =
          R.filter (fun w => ¬ C s w) := by
        ext w
        simp [R, and_left_comm, and_comm]
      rw [hsame]
      have hc := Finset.card_filter_add_card_filter_not (s := R) (C s)
      have hadd : (((R.filter (C s)).card : ℝ) +
          ((R.filter (fun w => ¬ C s w)).card : ℝ)) = R.card := by exact_mod_cast hc
      have hstep : ((R.filter (fun w => ¬ C s w)).card : ℝ) ≤ R.card * (1-p) := by nlinarith
      change (R.card : ℝ) ≤ _ at hb
      calc
        _ ≤ (R.card : ℝ) * (1-p) := hstep
        _ ≤ (U.card * (1-p)^m) * (1-p) := mul_le_mul_of_nonneg_right hb (by linarith)
        _ = _ := by ring
    · have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
      refine ⟨team, by omega, ?_⟩
      change (R.card : ℝ) ≤ _
      rw [he]
      simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)

/-- An actual cover once the residual bound drops below one. -/
theorem greedy_cover {W : Type u} {S : Type v} (C : S → W → Prop)
    [∀ s, DecidablePred (C s)] (p : ℝ) (hp : p ≤ 1) (U : Finset W)
    (select : ∀ R ⊆ U, R.Nonempty → ∃ s, p * R.card ≤ (R.filter (C s)).card)
    (m : ℕ) (small : (U.card : ℝ) * (1-p)^m < 1) :
    ∃ team : List S, team.length ≤ m ∧ ∀ w ∈ U, ∃ s ∈ team, C s w := by
  classical
  obtain ⟨team, hl, hb⟩ := greedy_residual C p hp U select m
  refine ⟨team, hl, ?_⟩
  have hlt := hb.trans_lt small
  have hempty : (U.filter (fun w => ∀ s ∈ team, ¬ C s w)).card < 1 := by
    exact_mod_cast hlt
  intro w hw
  by_contra! hmiss
  have hm : w ∈ U.filter (fun w => ∀ s ∈ team, ¬ C s w) := Finset.mem_filter.mpr ⟨hw, hmiss⟩
  have := Finset.card_pos.mpr ⟨_, hm⟩
  omega

variable {V : Type u} {G : SimpleGraph V}

/-- Following the covering team produces a winning game tree, even when the robber
sees all moves before choosing its next vertex. -/
theorem catchesWithin_of_cover {k : ℕ} (team : Fin k → Policy G) (t : ℕ)
    (h : List V) (r : V)
    (cover : ∀ tail : List V, tail.length = t → LegalWord G (r :: tail) →
      ∃ i, Hits (team i) h (r :: tail)) :
    CatchesWithin G k t (fun i => (team i).pos h) r := by
  induction t generalizing h r with
  | zero =>
    exact cover [] rfl (by simp [LegalWord])
  | succ t ih =>
    by_cases hstart : ∃ i, (team i).pos h = r
    · exact Or.inl hstart
    refine Or.inr ⟨fun i => (team i).pos (r::h), fun i => (team i).legal r h, ?_⟩
    by_cases hmove : ∃ i, (team i).pos (r :: h) = r
    · exact Or.inl hmove
    refine Or.inr (fun y hy => ih (r :: h) y ?_)
    intro tail ht hw
    obtain ⟨i, hit⟩ := cover (y :: tail) (by simp [ht]) (List.isChain_cons_cons.mpr ⟨hy, hw⟩)
    rcases hit with hc | hc | hc
    · exact (hstart ⟨i, hc⟩).elim
    · exact (hmove ⟨i, hc⟩).elim
    · exact ⟨i, hc⟩

/-- The subtype of legal chronological words is a subset of all `n^(T+1)` words. -/
noncomputable def walks [Fintype V] (G : SimpleGraph V) (T : ℕ) : Finset (Fin (T+1) → V) := by
  classical
  exact Finset.univ.filter (fun w => LegalWord G (List.ofFn w))

theorem walks_card_le [Fintype V] (G : SimpleGraph V) (T : ℕ) :
    (walks G T).card ≤ Fintype.card V ^ (T+1) := by
  classical
  simpa [walks] using Finset.card_le_card (Finset.filter_subset
    (fun w : Fin (T+1) → V => LegalWord G (List.ofFn w)) Finset.univ)

theorem winsWith_of_word_cover [Fintype V] {k T : ℕ} (team : Fin k → Policy G)
    (cover : ∀ w ∈ walks G T, ∃ i, Hits (team i) [] (List.ofFn w)) :
    WinsWith G k := by
  refine ⟨fun i => (team i).pos [], fun r => ⟨T, catchesWithin_of_cover team T [] r ?_⟩⟩
  intro tail ht hw
  let l := r :: tail
  have hlen : l.length = T+1 := by simp [l, ht]
  let w : Fin (T+1) → V := fun i => l.get (Fin.cast hlen.symm i)
  have hword : List.ofFn w = l := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      rw [List.getElem_ofFn]
      rfl
  have hm : w ∈ walks G T := by
    classical
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hword.symm ▸ hw⟩
  have hc := cover w hm
  rw [hword] at hc
  exact hc

end Meyniel
