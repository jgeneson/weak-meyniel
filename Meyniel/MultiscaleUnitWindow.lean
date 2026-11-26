module

public import Meyniel.MultiscaleUnit
public import Meyniel.MultiscaleReplication

@[expose] public section

namespace Meyniel.Multiscale
open Finset
open scoped Classical
noncomputable section
variable {V W : Type*} [Fintype V] [Fintype W] [Nonempty W] {G : SimpleGraph V}

/-- The local unit-clock estimate (equation (3)), with its initial
placement restricted to the required ball and its capture deadline T. -/
theorem unit_window (hc : G.Connected) (R : W → ℕ → V) (u T r N : ℕ) (z : V)
    (hn : Fintype.card V ≤ N) (speed : ∀ w, SpeedOne G (R w))
    (ends : ∀ w, G.dist z (R w (u+2+T)) ≤ r) (S : ℕ → Finset V)
    (hsupport : ∀ j < T, ∀ w, R w (u+2+j) ∈ S j) :
    WindowMixture G R u T (fun y => y ∈ ball G z (r+T))
      (fun _ => ((∑ j ∈ range T, Real.log (S j).card) + r*Real.log N) / (2*(T:ℝ)+1)) := by
  classical
  let K := ((∑ j ∈ range T, Real.log (S j).card) + r*Real.log N) / (2*(T:ℝ)+1)
  let starts := {s : WindowPolicy G // s.start ∈ ball G z (r+T)}
  let trivial : starts := ⟨WindowPolicy.ofPolicy (Policy.stay G z),by simp [WindowPolicy.ofPolicy,Policy.stay]⟩
  letI : Nonempty starts := ⟨trivial⟩
  let hit := fun (s : starts) w => windowHit s.1 (R w) u T
  change ∃ m : Mixture starts, ∀ w, Real.exp (-K) ≤ m.success hit w
  apply mixture_of_replicated hit K
  intro mult
  let U := (w : W) × Fin (mult w)
  by_cases hU : Nonempty U
  · letI := hU
    let word w := fun i : Fin (T+1) => R w (u+2+i.val)
    let X (j : ℕ) (tag : U) := Extension.extendWord hc z (word tag.1) j
    have atTime j (hj : j ≤ T) (tag : U) : X j tag = R tag.1 (u+2+j) :=
      Extension.extendWord_at hc z (word tag.1) ⟨j,by omega⟩
    have legal (i : ℕ) (tag : U) : Step G (X i tag) (X (i+1) tag) := by
      apply Extension.extendWord_step
      apply List.isChain_iff_getElem.mpr
      intro j hj
      simp only [List.getElem_ofFn]
      exact speed tag.1 (u+2+j)
    have hend (tag : U) : (Extension.route hc ((word tag.1) (Fin.last T)) z).length ≤ r := by
      rw [Extension.route_length,SimpleGraph.dist_comm]
      exact ends tag.1
    have home (j : ℕ) (hj : T+r ≤ j) (tag : U) : X j tag = z := by
      rw [show X j tag = _ from Extension.extendWord_after hc z (word tag.1) (show T ≤ j by omega)]
      exact SimpleGraph.Walk.getVert_of_length_le _ (by have := hend tag; omega)
    have inside (j : ℕ) (tag : U) : X j tag ∈ ball G z (r+T) := by
      apply mem_ball.mpr
      by_cases hj : j ≤ T
      · rw [atTime j hj tag]
        have tri := hc.dist_triangle (u:=z) (v:=R tag.1 (u+2+T)) (w:=R tag.1 (u+2+j))
        rw [@SimpleGraph.dist_comm _ G (R tag.1 (u+2+T)) (R tag.1 (u+2+j))] at tri
        have h := displacement hc (speed tag.1) (u:=u+2+j) (v:=u+2+T) (by omega)
        have := ends tag.1
        omega
      · rw [show X j tag = _ from Extension.extendWord_after hc z (word tag.1) (show T ≤ j by omega),SimpleGraph.dist_comm]
        have h := SimpleGraph.dist_le ((Extension.route hc (word tag.1 (Fin.last T)) z).drop (j-T))
        rw [SimpleGraph.Walk.drop_length] at h
        exact h.trans ((Nat.sub_le ..).trans ((hend tag).trans (Nat.le_add_right _ _)))
    let C j := if j<T then Real.log (S j).card else if j<T+r then Real.log N else 0
    have hN : 1 ≤ N := (Fintype.card_pos_iff.mpr ⟨z⟩).trans_le hn
    have bound j (_hj : j ≤ 2*T) : Real.log ((univ.image (X j)).card) ≤ C j := by
      have pos : 0 < (((univ.image (X j)).card) : ℝ) := by exact_mod_cast (univ_nonempty.image _).card_pos
      dsimp only [C]
      split_ifs with ht hr
      · apply Real.log_le_log pos
        exact_mod_cast card_le_card (show univ.image (X j) ⊆ S j from by
          intro y hy
          obtain ⟨tag,_,rfl⟩ := mem_image.mp hy
          rw [atTime j ht.le tag]
          exact hsupport j ht _)
      · exact Real.log_le_log pos (by exact_mod_cast (card_le_univ _).trans hn)
      · have hx : X j = fun _ => z := funext (home j (by omega))
        have hset : univ.image (X j) = {z} := by
          ext v
          simp [hx,eq_comm]
        simp [hset]
    have budget : (∑ j ∈ range (2*T+1), C j) ≤ (2*(T:ℝ)+1)*K := by
      dsimp only [K]
      have hd : 2*(T:ℝ)+1 ≠ 0 := by positivity
      rw [mul_comm (2*(T:ℝ)+1), div_mul_cancel₀ _ hd]
      exact unit_column_budget T r _ _ (Real.log_nonneg (by exact_mod_cast hN))
    obtain ⟨s,⟨b,_,tag,hinitial⟩,hcnt⟩ := unit_tagged X T legal K C bound budget
    let s' : starts := ⟨WindowPolicy.ofPolicy s,by change s.pos [] ∈ _; rw [hinitial]; exact inside b tag⟩
    refine ⟨s',?_⟩
    have hpath (g : U) : Sampler.remainder X T 0 g = List.ofFn (word g.1) := by
      simp only [Sampler.remainder,Nat.sub_zero,Nat.zero_add]
      congr 1
      funext i
      exact atTime i.val (by omega) g
    have hh (g : U) : Hits s [] (Sampler.remainder X T 0 g) ↔ hit s' g.1 := by
      rw [hpath]; rfl
    rw [Sampler.count] at hcnt
    simp_rw [hh] at hcnt
    rw [← Finset.sum_boole (R:=ℝ)] at hcnt
    simp only [U,Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum,Fintype.sum_sigma] at hcnt
    refine hcnt.trans_eq (sum_congr rfl (fun w _ => ?_))
    by_cases yes : hit s' w <;> simp [yes]
  · have zero (w : W) : mult w=0 := by
      by_contra! h
      exact hU ⟨⟨w,⟨0,Nat.pos_of_ne_zero h⟩⟩⟩
    refine ⟨trivial,?_⟩
    simp [zero]

end
end Meyniel.Multiscale
