import Meyniel.MultiscaleEntropy
import Meyniel.RandomTable
import Meyniel.MultiscaleGeometry

/-! Joint laws for the smoothed future positions. A uniform finite response
table selects one vertex in each ball. The argument only needs the marginals
given the word, so the same auxiliary table can serve at all target times. -/
namespace Meyniel.Multiscale.Smoothing
open Finset Interception RandomTable
noncomputable section

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]

abbrev Tag (W V : Type*) := W × Row V
def measure (p : W → ℝ) (i : Tag W V) : ℝ := p i.1 / Fintype.card (Row V)

omit [Fintype W] [DecidableEq W] in
theorem measure_pos (p : W → ℝ) (hp : ∀ w, 0 < p w) (i : Tag W V) : 0 < measure p i :=
  div_pos (hp _) (by exact_mod_cast Fintype.card_pos)

omit [DecidableEq W] in
theorem expect_measure (p : W → ℝ) (f : W → ℝ) :
    expect (measure (V:=V) p) (fun i => f i.1) = expect p f := by
  unfold expect measure
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl; intro w _
  simp only [sum_const,card_univ,nsmul_eq_mul]
  field_simp [show (Fintype.card (Row V) : ℝ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero]

omit [DecidableEq W] in
theorem measure_mass (p : W → ℝ) : ∑ i : Tag W V, measure p i = ∑ w, p w := by
  have h := expect_measure (V:=V) p (fun _ => 1)
  simpa [expect] using h

def sample (G : SimpleGraph V) (center : W → V) (r : ℕ) (i : Tag W V) : V :=
  (i.2 ⟨ball G (center i.1) r, ball_nonempty _ _⟩).val

omit [Fintype W] [DecidableEq W] [DecidableEq V] in
@[simp] theorem sample_mem (G : SimpleGraph V) (center : W → V) (r : ℕ) (i : Tag W V) :
    sample G center r i ∈ ball G (center i.1) r := (i.2 _).property

omit [Fintype W] [DecidableEq W] in
theorem average_single (G : SimpleGraph V) (center : W → V) (r : ℕ) (w : W) (x : V)
    (hx : x ∈ ball G (center w) r) :
    avg (fun a : Row V => if sample G center r (w,a) = x then (1:ℝ) else 0) =
      1 / (ball G (center w) r).card := by
  have hh := avg_select (ball G (center w) r) x
  simp [select,sample,ball_nonempty,hx] at hh ⊢
  convert hh using 3; congr

private theorem fiber_word_sum (p : W → ℝ) (w : W) (f : Tag W V → ℝ) :
    (∑ i ∈ fiber (Prod.fst : Tag W V → W) w, measure p i * f i) =
      p w * avg (fun a => f (w,a)) := by
  unfold fiber measure RandomTable.avg
  rw [sum_filter,Fintype.sum_prod_type]
  dsimp only
  calc
    _ = ∑ w' : W, if w'=w then ∑ r : Row V, p w'/Fintype.card (Row V)*f (w',r) else 0 := by
      apply sum_congr rfl; intro w' _; split_ifs with e <;> simp [e]
    _ = _ := by
      simp only [sum_ite_eq',mem_univ,if_true]
      rw [← mul_sum]
      ring

theorem condProb_sample (p : W → ℝ) (hp : ∀ w, 0 < p w) (G : SimpleGraph V) (center : W → V)
    (r : ℕ) (i : Tag W V) :
    condProb (measure p) Prod.fst (sample G center r) i = 1 / (ball G (center i.1) r).card := by
  classical
  let z := sample G center r
  let X := z i
  let S := atom Prod.fst i
  have he : atom (fun u : Tag W V => (u.1,z u)) i = S.filter (fun u => z u=X) := by
    ext u; simp [S,X,atom,fiber]
  have hs : mass (measure p) S = p i.1 := by
    simpa [S,mass,atom,avg_const] using fiber_word_sum (V:=V) p i.1 (fun _ => 1)
  have hj : mass (measure p) (S.filter (fun u => z u=X)) =
      p i.1 * (1/(ball G (center i.1) r).card) := by
    rw [mass,sum_filter]
    have hh := fiber_word_sum p i.1 (fun a => if z a=X then (1:ℝ) else 0)
    change (∑ a ∈ fiber Prod.fst i.1, _) = _
    simp only [mul_ite,mul_one,mul_zero] at hh
    rw [hh]
    rw [average_single G center r i.1 X (sample_mem G center r i)]
  change mass (measure p) (atom (fun u => (u.1,z u)) i) / mass (measure p) S = _
  rw [he,hs,hj]
  field_simp [(hp i.1).ne']

theorem condEntropy_sample (p : W → ℝ) (hp : ∀ w, 0 < p w) (G : SimpleGraph V)
    (center : W → V) (r : ℕ) :
    condEntropy (measure p) Prod.fst (sample G center r) =
      expect p (fun w => Real.log (ball G (center w) r).card) := by
  unfold condEntropy
  simp_rw [condProb_sample p hp G center r, one_div,Real.log_inv]
  rw [expect_measure (V:=V) p (fun w => -Real.log (ball G (center w) r).card)]
  simp [expect,Finset.sum_neg_distrib]

end
end Meyniel.Multiscale.Smoothing
