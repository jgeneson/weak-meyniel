import Meyniel.MultiscaleReach

namespace Meyniel.Multiscale
open Classical
noncomputable section
variable {V W : Type*} {G : SimpleGraph V}

/-- A mixture may use the revealed history and its own site. Correctness is
required on the whole fiber consistent with both, including every possible
continuation on that fiber. At an impossible input the cop stays in place. -/
theorem fiber_trials (valid : ℕ → Prop) (past : ℕ → W → List V) (ok : ℕ → W → V → Prop)
    (hit : ℕ → (x : V) → Anchored G x → W → Prop) (p : ℕ → W → ℝ)
    (build : ∀ b, valid b → ∀ (h : List V) (x : V),
      let E := {w : W // past b w=h ∧ ok b w x}
      Nonempty E → ∃ m : Mixture (Anchored G x), ∀ w : E, p b w.1 ≤
        m.success (fun s k => hit b x s k.val) w) :
    ∃ trial : ℕ → List V → (x : V) → Mixture (Anchored G x),
      ∀ b, valid b → ∀ w x, ok b w x →
        p b w ≤ (trial b (past b w) x).success (hit b x) w := by
  classical
  let E b h x := {w : W // past b w=h ∧ ok b w x}
  let law b h x := if k : valid b ∧ Nonempty (E b h x) then
      (build b k.1 h x k.2).choose else (⟨1, fun _ => ⟨Policy.stay G x,rfl⟩, _, uniformLaw (Fin 1)⟩ : Mixture (Anchored G x))
  refine ⟨law,?_⟩
  intro b hb w x hx
  let w' : E b (past b w) x := ⟨w,rfl,hx⟩
  have h : valid b ∧ Nonempty (E b (past b w) x) := ⟨hb,⟨w'⟩⟩
  have eq : law b (past b w) x = (build b hb (past b w) x h.2).choose := dif_pos h
  rw [eq]
  exact (build b hb (past b w) x h.2).choose_spec w'

end
end Meyniel.Multiscale
