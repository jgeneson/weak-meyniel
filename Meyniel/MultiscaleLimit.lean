module

public import Meyniel.MultiscaleBounds

/-! # A uniform vanishing exponent

The constants in a bound for each fixed positive slack may depend on the
slack. Diagonalization produces a single function of the graph order tending
to zero, with a pointwise upper bound valid for every finite connected graph.
-/

@[expose] public section

namespace Meyniel.Multiscale
open Filter
open scoped Topology
universe u

theorem vanishing_exponent_of_slack
    (fixed : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0<C ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
        (copNumber G : ℝ) ≤ C*(Fintype.card V : ℝ)^(2/3+ε)) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ (∀ n, 0 < e n) ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
        (copNumber G : ℝ) ≤ (Fintype.card V : ℝ)^(2/3+e (Fintype.card V)) := by
  classical
  let error (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have epos j : 0<error j := by dsimp [error]; positivity
  let bound (j N : ℕ) := ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.Connected →
    Fintype.card V = N → (copNumber G : ℝ) ≤ (N:ℝ)^(2/3+error j)
  have tail (j : ℕ) : ∃ K : ℕ, ∀ N≥K, bound j N := by
    let h := error j/2
    have hp : 0<h := half_pos (epos j)
    obtain ⟨C,_,hf⟩ := fixed h hp
    have grow := (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
    obtain ⟨K,hK⟩ := eventually_atTop.1 (grow.eventually_ge_atTop C)
    refine ⟨K,?_⟩
    intro N hN V _ G hc card
    have hn : 0 < (N:ℝ) := by
      haveI : Nonempty V := hc.nonempty
      exact_mod_cast card ▸ (Fintype.card_pos : 0 < Fintype.card V)
    have hcost := hf V G hc
    rw [card] at hcost
    calc
      _ ≤ C*(N:ℝ)^(2/3+h) := hcost
      _ ≤ (N:ℝ)^h*(N:ℝ)^(2/3+h) := mul_le_mul_of_nonneg_right (hK N hN) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [←Real.rpow_add hn]; congr 1; dsimp [h]; ring
  let K (j : ℕ) := if j=0 then 0 else (tail j).choose
  have start (N : ℕ) : K 0 ≤ N := by simp [K]
  let index (N : ℕ) := Nat.findGreatest (fun j => K j ≤ N) N
  have growth : Tendsto index atTop atTop := by
    apply tendsto_atTop.2
    intro j
    filter_upwards [eventually_ge_atTop j,eventually_ge_atTop (K j)] with N hj hk
    exact Nat.le_findGreatest hj hk
  refine ⟨fun N => error (index N),tendsto_one_div_add_atTop_nhds_zero_nat.comp growth,
    fun N => epos _,?_⟩
  intro V _ G hc
  let n := Fintype.card V
  haveI : Nonempty V := hc.nonempty
  have hn : (1:ℝ) ≤ n := by exact_mod_cast (Fintype.card_pos : 1 ≤ Fintype.card V)
  let j := index n
  have hk : K j ≤ n := Nat.findGreatest_spec (P:=fun j => K j ≤ n) (Nat.zero_le n) (start n)
  by_cases hz : j=0
  · change (copNumber G:ℝ) ≤ (n:ℝ)^(2/3+error j)
    rw [hz]
    have H : (copNumber G:ℝ) ≤ n := by exact_mod_cast copNumber_le_of_win (winsWith_card G)
    apply H.trans
    calc
      (n:ℝ) = (n:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (by norm_num [error])
  · have th := (tail j).choose_spec n (by simpa [K,hz] using hk)
    exact th V G hc rfl

end Meyniel.Multiscale
