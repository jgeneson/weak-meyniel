module

public import Meyniel.MultiscaleWindowSpec
public import Meyniel.MultiscaleCover
public import Meyniel.MultiscaleTeamSize

/-! # Choosing the two deterministic window covers -/

@[expose] public section

namespace Meyniel.Multiscale
open Finset
universe u
noncomputable section
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

private theorem cover_cost {N T k : ℕ} (hN : 0 < N) {B : ℝ} (hB : 0 < B)
    (hk : k = ⌈((T+3:ℕ):ℝ)*Real.log N*B⌉₊+1) :
    (N:ℝ)^(T+3)*(1-min 1 (1/B))^k < 1 := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hk0 : 0 < k := by omega
  by_cases h : B ≤ 1
  · have hb := (le_div_iff₀ hB).mpr (by simpa using h : 1*B ≤ 1)
    rw [min_eq_left hb,sub_self,zero_pow hk0.ne',mul_zero]
    norm_num
  · have hb : 1/B ≤ 1 := (div_le_one hB).mpr (le_of_lt (lt_of_not_ge h))
    rw [min_eq_right hb]
    apply power_decay (pow_pos hn _) hb
    rw [Real.log_pow,mul_one_div,lt_div_iff₀ hB,hk]
    push_cast
    have h':=((Nat.le_ceil (((T+3:ℕ):ℝ)*Real.log N*B)))
    push_cast at h'
    linarith

theorem exp_windowCost {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (δ : ℝ) (i : ℕ) :
    Real.exp (windowCost δ N i M) = Real.sqrt M * (N:ℝ)^(-(i:ℝ)*gain δ/2+δ/20) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hm,Real.rpow_def_of_pos hn,← Real.exp_add]
  congr 1; unfold windowCost; ring

private theorem success_from_cost {B cost : ℝ} (_hB : 0 < B) (hle : Real.exp cost ≤ B) :
    min 1 (1/B) ≤ Real.exp (-cost) := by
  apply (min_le_right ..).trans
  rw [Real.exp_neg,← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos _) hle

/-- A fixed global team. -/
theorem global_team {δ : ℝ} {N : ℕ} (hN : 0<N) (hc : G.Connected)
    (hsize : Fintype.card V ≤ N) (hd : G.diam ≤ cutoff N δ) (win : ConstantWindows.{u} δ N) :
    ∃ team : Fin (globalCount δ N) → WindowPolicy G, ∀ R, SpeedOne G R →
      (∀ l, Passes G R (physicalScale G δ N l) 0 (windowTime N (cutoff N δ))) →
        ∃ j, windowHit (team j) R 0 (windowTime N (cutoff N δ)) := by
  classical
  let T := windowTime N (cutoff N δ)
  let B := (N:ℝ)^(1/2-(levels δ:ℝ)*gain δ/2+δ/20)
  let P (R : ℕ → V) := SpeedOne G R ∧ ∀ l, Passes G R (physicalScale G δ N l) 0 T
  let a := Classical.choice hc.nonempty
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hB : 0<B := Real.rpow_pos_of_pos hn _
  have he : Real.exp (windowCost δ N (levels δ) N) = B := by
    rw [exp_windowCost hN hN,Real.sqrt_eq_rpow,← Real.rpow_add hn]
    dsimp [B]; congr 1; ring
  have hsmall := cover_cost (N:=N) (T:=T) (k:=globalCount δ N) hN hB rfl
  obtain ⟨team,hcov⟩ := uniform_cover G T N (globalCount δ N) hsize (fun _ => True)
    ⟨WindowPolicy.ofPolicy (Policy.stay G a), trivial⟩ P (min 1 (1/B)) (min_le_left ..) hsmall (by
      intro W _ _ R hP
      obtain ⟨m,hm⟩ := win.global V G hc hsize hd W R (fun w => (hP w).1) (fun w => (hP w).2)
      exact ⟨m,fun w => (success_from_cost hB he.le).trans (hm w)⟩)
  refine ⟨fun j => (team j).1,?_⟩
  intro R hR passes
  have hh : shiftPath R 0 = R := by funext j; simp [shiftPath]
  exact hcov R 0 (hh.symm ▸ (show P R from ⟨hR,passes⟩))

/-- Fixed local teams for all phases of the same assigned center. -/
theorem local_team {δ : ℝ} {N : ℕ} (hN : 0<N) (hc : G.Connected)
    (hsize : Fintype.card V ≤ N) (hd : G.diam ≤ cutoff N δ) (win : ConstantWindows.{u} δ N)
    (i : Fin (levels δ)) (z : V) (hz : (physicalScale G δ N i).good z) :
    let q := physicalScale G δ N i
    let count := siteCount δ N (i.val+1) (ball G z (q.base/4)).card
    ∃ team : Fin count → WindowPolicy G,
      (∀ j, G.dist z (team j).start ≤ 2*q.run) ∧
      ∀ R u, SpeedOne G R → G.dist (R (u+q.run+2)) z ≤ 2*q.base →
        (∀ l < i, Passes G R (physicalScale G δ N l) u (u+q.run)) →
        ∃ j, windowHit (team j) R u q.run := by
  classical
  let q := physicalScale G δ N i
  let T := q.run
  let m := (ball G z (q.base/4)).card
  let M := (ball G z (outerRadius δ N (i.val+1))).card
  let count := siteCount δ N (i.val+1) m
  let B := Real.sqrt m*(N:ℝ)^siteExp δ (i.val+1 : ℕ)
  let P (R : ℕ→V) := SpeedOne G R ∧ G.dist z (R (T+2)) ≤ 2*q.base ∧
    ∀ l < i, Passes G R (physicalScale G δ N l) 0 T
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hm : 0 < m := (ball_nonempty (G:=G) z _).card_pos
  have hM : 0 < M := (ball_nonempty (G:=G) z _).card_pos
  have hB : 0<B := mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hm)) (Real.rpow_pos_of_pos hn _)
  have he : Real.exp (windowCost δ N i.val M) ≤ B := by
    rw [exp_windowCost hN hM]
    calc
      _ ≤ Real.sqrt ((N:ℝ)^(δ/100)*m)*(N:ℝ)^(-(i.val:ℝ)*gain δ/2+δ/20) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hz) (Real.rpow_nonneg hn.le _)
      _ = B := by
        rw [Real.sqrt_mul (Real.rpow_nonneg hn.le _),Real.sqrt_eq_rpow,
          ← Real.rpow_mul hn.le,mul_comm _ (Real.sqrt m),mul_assoc,← Real.rpow_add hn]
        dsimp [B,siteExp]; push_cast; congr 2; ring
  have hs : (N:ℝ)^(T+3)*(1-min 1 (1/B))^count < 1 := by
    apply cover_cost hN hB
    simp only [count,siteCount,B,siteExp,T,q,physicalScale,mul_assoc]
  obtain ⟨team,hcov⟩ := uniform_cover G T N count hsize (fun x => G.dist z x ≤ 2*T)
    ⟨WindowPolicy.ofPolicy (Policy.stay G z), by change G.dist z z ≤ _; simp⟩ P (min 1 (1/B)) (min_le_left ..) hs (by
      intro W _ _ R hP
      obtain ⟨m,hm⟩ := win.local_window V G hc hsize hd i z hz W R (fun w => (hP w).1)
        (fun w => (hP w).2.1) (fun w => (hP w).2.2)
      exact ⟨m,fun w => (success_from_cost hB he).trans (hm w)⟩)
  refine ⟨fun j => (team j).1,fun j => (team j).2,?_⟩
  intro R u hR e hpass
  apply hcov R u
  refine ⟨shift_speed hR u,?_,fun l hl => shift_passes (hpass l hl)⟩
  simpa only [shiftPath,← Nat.add_assoc,G.dist_comm (u:=z)] using e

end
end Meyniel.Multiscale
