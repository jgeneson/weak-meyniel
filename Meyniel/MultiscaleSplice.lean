import Meyniel.Sampler
import Meyniel.Extension

/-! Moving to a prescribed site and choosing a continuation on the observed
prefix. The last observation, at the instant of arrival, can be used before
the next cop move. -/

namespace Meyniel.Multiscale
variable {V : Type*} {G : SimpleGraph V}

abbrev Anchored (G : SimpleGraph V) (x : V) := {s : Policy G // s.pos [] = x}

def after (s : Policy G) (h : List V) : Policy G where
  pos p := s.pos (p ++ h)
  legal r p := s.legal r (p ++ h)

theorem hits_after (s : Policy G) (h : List V) : ∀ (w p : List V),
    Hits (after s h) p w ↔ Hits s (p++h) w
  | [], _ => Iff.rfl
  | [_], _ => Iff.rfl
  | x :: y :: w, p => by
    change (_ ∨ _ ∨ Hits (after s h) (x::p) (y::w)) ↔ _
    rw [hits_after s h (y::w) (x::p)]
    rfl

def onReveal (x : V) (branch : V → Anchored G x) : Anchored G x := by
  let q r := after (branch r).1 [r]
  have legal r : Step G x ((q r).pos []) := by
    rw [← (branch r).2]
    exact (branch r).1.legal r []
  exact ⟨Sampler.splice x q legal,rfl⟩

theorem hits_onReveal (x : V) (branch : V → Anchored G x) (r : V) (tail : List V) :
    Hits (onReveal x branch).val [] (r::tail) ↔ Hits (branch r).val [] (r::tail) := by
  unfold onReveal
  rw [Sampler.stageHits_splice]
  cases tail with
  | nil => exact (congrArg (fun v => v=r) (branch r).property.symm).to_iff
  | cons y ys =>
    change (x=r ∨ _ ∨ Hits (after _ [r]) [] (y::ys)) ↔ _
    rw [hits_after]
    change (x=r ∨ _ ∨ _) ↔ ((branch r).val.pos []=r ∨ _ ∨ _)
    rw [(branch r).2]
    rfl

/-- Follow the first B steps of route. The continuation is indexed by the
chronological list of B+1 observations ending at arrival. On every history its
initial vertex must be route B. -/
def travelThen : (B : ℕ) → (route : ℕ → V) → (∀ t, Step G (route t) (route (t+1))) →
    (List V → Anchored G (route B)) → Anchored G (route 0)
  | 0,route,_,branch => onReveal (route 0) (fun r => branch [r])
  | B+1,route,legal,branch => by
    let q r := travelThen B (fun t => route (t+1)) (fun t => legal (t+1)) (fun h => branch (r::h))
    have L r : Step G (route 0) ((q r).1.pos []) := (q r).2.symm ▸ legal 0
    exact ⟨Sampler.splice (route 0) (fun r => (q r).1) L,rfl⟩

theorem travelThen_hits (pre : List V) (route : ℕ → V) (legal : ∀ t, Step G (route t) (route (t+1)))
    (branch : List V → Anchored G (route pre.length)) (r : V) (tail : List V)
    (hit : Hits (branch (pre++[r])).val [] (r::tail)) :
    Hits (travelThen pre.length route legal branch).val [] (pre++r::tail) := by
  induction pre generalizing route with
  | nil => exact (hits_onReveal _ _ r tail).2 hit
  | cons x xs ih =>
    simp only [List.length_cons,travelThen,List.cons_append]
    rw [Sampler.stageHits_splice]
    have h := ih (fun t => route (t+1)) (fun t => legal (t+1)) (fun h => branch (x::h)) hit
    cases he : xs ++ r::tail with
    | nil => simp at he
    | cons y ys => rw [he] at h; exact Or.inr (Or.inr h)

/-- A legal fixed route from x to z, padded by stays, of every length at least
their distance. -/
theorem route_to (hc : G.Connected) (x z : V) (B : ℕ) (hd : G.dist x z ≤ B) :
    ∃ route : ℕ → V, route 0=x ∧ route B=z ∧ ∀ t, Step G (route t) (route (t+1)) := by
  let p := Extension.route hc x z
  refine ⟨p.getVert,by simp,p.getVert_of_length_le (by simpa [p,Extension.route_length] using hd),?_⟩
  intro t
  by_cases h : t < p.length
  · exact Or.inr (p.adj_getVert_succ h)
  · exact Or.inl ((p.getVert_of_length_le (by omega)).trans (p.getVert_of_length_le (by omega)).symm)

end Meyniel.Multiscale
