import Meyniel.MultiscaleTargets
import Meyniel.MultiscaleGrowth
import Meyniel.MultiscaleWindowMinimax

/-! A single comparison with uniform future-ball centers and a terminal trial
at each possible final row. Marginal support bounds can be chosen separately
for each target column. -/
namespace Meyniel.Multiscale
open Finset Interception Clock GraphClock Smoothing Targets
noncomputable section

variable {W V : Type*} [Fintype W] [Nonempty W] [DecidableEq W]
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The logarithmic value inequality for a true-word law of full support.
The allowed starts contain the sampled balls and the common-home extensions. -/
theorem positive_ball_clock (hc : G.Connected) (R : W → ℕ → V) (speed : ∀ w, SpeedOne G (R w))
    (p : W → ℝ) (hp : ∀ w, 0 < p w) (law : ∑ w, p w = 1)
    (weight : W → ℝ) (hw : ∀ w, 0 < weight w)
    (u T v g h r M B D N big : ℕ) (hB : 0 < B) (hh : 0 < h) (width : h+2*r ≤ B)
    (hN : Fintype.card V ≤ N) (hrad : 2*(g+h+B)+r ≤ big)
    (deadline : endpoint v g h M ≤ T) (home : V)
    (distHome : ∀ w, G.dist home (center R u v g h M w)+r ≤ D*B)
    (starts : V → Prop) [Nonempty {s : WindowPolicy G // starts s.start}]
    (orig : ∀ j ≤ M, ∀ w, ∀ x ∈ ball G (center R u v g h j w) r, starts x)
    (tail : ∀ w x, G.dist home x ≤ G.dist home (center R u v g h M w)+r → starts x)
    (support : ℕ → Finset V) (available : ∀ j < M, ∀ w, ball G (center R u v g h j w) r ⊆ support j)
    (d : ℕ → W → ℝ) (trial : ℕ → List V → (x : V) → Mixture (Anchored G x))
    (correct : ∀ b ≤ top B h M, ∀ w x, x ∈ ball G (center R u v g h (column B h b) w) r →
      Real.exp (-(logBall G (center R u v g h (column B h b) w) big/2+d b w)) ≤
      (trial b (reveal R u v B (row B h b+1) w) x).success
        (atHit R u T (time v B (row B h b)) x) w) :
    let J := top B h M+1
    expect p (fun w => Real.log (weight w)) -
      ((∑ j ∈ range M, Real.log (support j).card)+D*Real.log N)/(J:ℝ) -
      (∑ b ∈ range J, expect p (fun w => logBall G (center R u v g h (column B h b) w) big -
        logBall G (center R u v g h (column B h b) w) r+d b w))/(J:ℝ) ≤
      Real.log (initialValue G p id weight R u T starts) := by
  classical
  let μ := measure (V:=V) p
  let z := target hc R u v g h r M B home
  let y := center R u v g h
  let J := top B h M+1
  have lawμ : ∑ i, μ i=1 := (measure_mass p).trans law
  have hμpos : ∀ i, 0 < μ i := measure_pos p hp
  have hy {j : ℕ} (hj : j ≤ M) : z j = sample G (y j) r := by funext i; simp [z,target,hj,y]
  have gain (w : W) (j : ℕ) : 0 < ((ball G (y j w) big).card : ℝ) := by
    exact_mod_cast (ball_nonempty (G:=G) (y j w) big).card_pos
  have hbtime (b : ℕ) (hb : b ≤ top B h M) : time v B (row B h b) ≤ T := by
    let j := column B h b
    have hj := column_le hB hh hb
    have hje : row B h b+j=b := by
      have rb := last_le hB hh b
      unfold j column; omega
    have hrow := ((le_row_iff hB hh).mp (show row B h b ≤ row B h b from le_rfl)).2
    have hm := Nat.mul_le_mul_right h hj
    unfold time; unfold endpoint at deadline
    change _ ≤ column B h b*h at hrow
    omega
  have allow (b : ℕ) (_ : b ≤ top B h M) (i : Tag W V) : starts (z b i) := by
    by_cases e : b ≤ M
    · rw [hy e]; exact orig b e i.1 _ (sample_mem ..)
    · rw [show z b i = retreat hc home (sample G (y M) r i) ((b-M)*B) from
        target_after hc _ _ _ _ _ _ _ _ _ (by omega) i]
      apply tail i.1
      apply (retreat_radius ..).trans
      exact (hc.dist_triangle (v:=y M i.1)).trans (Nat.add_le_add_left (mem_ball.mp (sample_mem ..)) _)
  have hhome (j : ℕ) (hj : M+D ≤ j) (a b : Tag W V) : z j a=z j b :=
    (target_home hc R u v g h r M B D home distHome hj a).trans
      (target_home hc R u v g h r M B D home distHome hj b).symm
  have he := graph_clock_pass G hc μ hμpos lawμ Prod.fst weight hw R u T v B h M D N hB hh
    (by omega) hN z (target_leg hc R speed u v g h r M B width home) starts allow hbtime hhome
    (fun j w => logBall G (y j w) big) d
    (fun j _ w => Real.log_nonneg (by exact_mod_cast (ball_nonempty (G:=G) (y j w) big).card_pos))
    (fun j hj t ht i => by
      rw [logBall,Real.exp_log (gain i.1 j)]
      exact_mod_cast Finset.card_le_card (target_support hc R speed u v g h r M B big hB hh hrad home hj ht i))
    trial (fun b hb i => by
      rw [hy (column_le hB hh hb)]
      exact correct b hb i.1 _ (sample_mem ..))
  have hvalue : initialValue G μ Prod.fst weight R u T starts=initialValue G p id weight R u T starts :=
    value_pushforward μ p Prod.fst weight (fun (s : {p : WindowPolicy G // starts p.start}) w =>
      windowHit s.val (R w) u T) (expect_measure p)
  let empty := fun _ : Tag W V => ([]:List V)
  have marg (j : ℕ) (hj : j < M) :
      condEntropy μ empty (z j) ≤ Real.log (support j).card := by
    have inc (i : Tag W V) : (atom empty i).image (z j) ⊆ support j := by
      intro x hx
      obtain ⟨l,_,rfl⟩ := mem_image.mp hx
      rw [hy hj.le]
      exact available j hj l.1 (sample_mem ..)
    exact (condEntropy_le_log_support μ hμpos empty (z j) (fun _=> (support j).card)
      (fun i => by exact_mod_cast card_le_card (inc i))).trans_eq (expect_const μ lawμ _)
  have hsum : (∑ j ∈ range M, condEntropy μ empty (z j)) ≤ ∑ j ∈ range M, Real.log (support j).card :=
    sum_le_sum (fun j hj => marg j (mem_range.mp hj))
  have hcharge (b : ℕ) (hb : b ∈ range J) :
      expect μ (fun i => logBall G (y (column B h b) i.1) big) -
      condEntropy μ Prod.fst (z (column B h b))+expect μ (fun i => d b i.1) =
      expect p (fun w => logBall G (y (column B h b) w) big - logBall G (y (column B h b) w) r+d b w) := by
    have hj := column_le hB hh (show b ≤ top B h M by simpa [J] using hb)
    rw [hy hj,condEntropy_sample p hp]
    rw [expect_measure p (fun w => logBall G (y (column B h b) w) big),expect_measure p (d b)]
    simp [expect,logBall,mul_add,mul_sub,sum_add_distrib,sum_sub_distrib]
  change _ ≤ Real.log (initialValue G μ Prod.fst weight R u T starts) at he
  rw [hvalue, expect_measure p (fun w => Real.log (weight w)),sum_congr rfl hcharge] at he
  apply le_trans _ he
  apply sub_le_sub_right
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_right (add_le_add_left hsum _) (Nat.cast_nonneg _)

omit [Nonempty W] in
/-- The comparison bound for any finite input law, including zero mass on some words. -/
theorem ball_clock (hc : G.Connected) (R : W → ℕ → V) (speed : ∀ w, SpeedOne G (R w))
    (p : W → ℝ) (hp : ∀ w, 0 ≤ p w) (law : ∑ w, p w = 1)
    (weight : W → ℝ) (hw : ∀ w, 0 < weight w)
    (u T v g h r M B D N big : ℕ) (hB : 0 < B) (hh : 0 < h) (width : h+2*r ≤ B)
    (hN : Fintype.card V ≤ N) (hrad : 2*(g+h+B)+r ≤ big)
    (deadline : endpoint v g h M ≤ T) (home : V)
    (distHome : ∀ w, G.dist home (center R u v g h M w)+r ≤ D*B)
    (starts : V → Prop) [Nonempty {s : WindowPolicy G // starts s.start}]
    (orig : ∀ j ≤ M, ∀ w, ∀ x ∈ ball G (center R u v g h j w) r, starts x)
    (tail : ∀ w x, G.dist home x ≤ G.dist home (center R u v g h M w)+r → starts x)
    (support : ℕ → Finset V) (available : ∀ j < M, ∀ w, ball G (center R u v g h j w) r ⊆ support j)
    (d : ℕ → W → ℝ) (trial : ℕ → List V → (x : V) → Mixture (Anchored G x))
    (correct : ∀ b ≤ top B h M, ∀ w x, x ∈ ball G (center R u v g h (column B h b) w) r →
      Real.exp (-(logBall G (center R u v g h (column B h b) w) big/2+d b w)) ≤
      (trial b (reveal R u v B (row B h b+1) w) x).success
        (atHit R u T (time v B (row B h b)) x) w) :
    let J := top B h M+1
    expect p (fun w => Real.log (weight w)) -
      ((∑ j ∈ range M, Real.log (support j).card)+D*Real.log N)/(J:ℝ) -
      (∑ b ∈ range J, expect p (fun w => logBall G (center R u v g h (column B h b) w) big -
        logBall G (center R u v g h (column B h b) w) r+d b w))/(J:ℝ) ≤
      Real.log (initialValue G p id weight R u T starts) := by
  classical
  let U := {w : W // 0 < p w}
  have hne : Nonempty U := by
    by_contra! e
    have hz (w : W) : p w=0 := by
      by_contra h
      exact e.false (⟨w,lt_of_le_of_ne (hp w) (Ne.symm h)⟩ : U)
    simp [hz] at law
  letI := hne
  let p' := fun a : U => p a.val
  let R' := fun a : U => R a.val
  let weight' := fun a : U => weight a.val
  let d' := fun b (a : U) => d b a.val
  have pres : ∀ f : W → ℝ, expect p' (fun a => f a.val) = expect p f := expect_support p hp
  have hlaw : ∑ a, p' a=1 := by simpa [expect,law] using pres (fun _=>1)
  have he := positive_ball_clock hc R' (fun a => speed a.val) p' (fun a => a.property) hlaw
    weight' (fun a => hw a.val) u T v g h r M B D N big hB hh width hN hrad deadline home
    (fun a => distHome a.val) starts (fun j hj a => orig j hj a.val)
    (fun a => tail a.val) support (fun j hj a => available j hj a.val) d' trial
    (fun b hb a x hx => correct b hb a.val x hx)
  have hv : initialValue G p' id weight' R' u T starts = initialValue G p id weight R u T starts :=
    value_pushforward p' p Subtype.val weight (fun (s : {p : WindowPolicy G // starts p.start}) w =>
      windowHit s.val (R w) u T) pres
  have charge (b : ℕ) : expect p' (fun a => logBall G (center R' u v g h (column B h b) a) big -
      logBall G (center R' u v g h (column B h b) a) r + d' b a) =
      expect p (fun w => logBall G (center R u v g h (column B h b) w) big -
      logBall G (center R u v g h (column B h b) w) r + d b w) :=
    pres (fun w => logBall G (center R u v g h (column B h b) w) big -
      logBall G (center R u v g h (column B h b) w) r + d b w)
  change _ ≤ Real.log (initialValue G p' id weight' R' u T starts) at he
  rwa [hv,pres (fun w => Real.log (weight w)),sum_congr rfl (fun b _ => charge b)] at he


/-- A fixed clock's pathwise charge, after taking a single mixed strategy
valid simultaneously on every word. -/
theorem ball_clock_mixture (hc : G.Connected) (R : W → ℕ → V) (speed : ∀ w, SpeedOne G (R w))
    (u T v g h r M B D N big : ℕ) (hB : 0 < B) (hh : 0 < h) (width : h+2*r ≤ B)
    (hN : Fintype.card V ≤ N) (hrad : 2*(g+h+B)+r ≤ big)
    (deadline : endpoint v g h M ≤ T) (home : V)
    (distHome : ∀ w, G.dist home (center R u v g h M w)+r ≤ D*B)
    (starts : V → Prop) [Nonempty {s : WindowPolicy G // starts s.start}]
    (orig : ∀ j ≤ M, ∀ w, ∀ x ∈ ball G (center R u v g h j w) r, starts x)
    (tail : ∀ w x, G.dist home x ≤ G.dist home (center R u v g h M w)+r → starts x)
    (support : ℕ → Finset V) (available : ∀ j < M, ∀ w, ball G (center R u v g h j w) r ⊆ support j)
    (d : ℕ → W → ℝ) (trial : ℕ → List V → (x : V) → Mixture (Anchored G x))
    (correct : ∀ b ≤ top B h M, ∀ w x, x ∈ ball G (center R u v g h (column B h b) w) r →
      Real.exp (-(logBall G (center R u v g h (column B h b) w) big/2+d b w)) ≤
      (trial b (reveal R u v B (row B h b+1) w) x).success
        (atHit R u T (time v B (row B h b)) x) w) :
    let J := top B h M+1
    WindowMixture G R u T starts (fun w =>
      ((∑ j ∈ range M, Real.log (support j).card)+D*Real.log N)/(J:ℝ) +
      (∑ b ∈ range J, (logBall G (center R u v g h (column B h b) w) big -
        logBall G (center R u v g h (column B h b) w) r+d b w))/(J:ℝ)) := by
  classical
  let J := top B h M+1
  let total : ℝ := ((∑ j ∈ range M, Real.log (support j).card)+D*Real.log N)/(J:ℝ)
  let cost := fun b w => logBall G (center R u v g h (column B h b) w) big -
        logBall G (center R u v g h (column B h b) w) r+d b w
  apply weighted_window_minimax
  intro p law weight hw
  have H := ball_clock hc R speed p law.1 law.2 weight hw u T v g h r M B D N big hB hh
    width hN hrad deadline home distHome starts orig tail support available d trial correct
  have he : expect p (fun w => total+(∑ b ∈ range J, cost b w)/(J:ℝ)) =
      total+(∑ b ∈ range J, expect p (cost b))/(J:ℝ) := by
    simp only [expect,mul_add,← mul_div_assoc,mul_sum,sum_add_distrib,← sum_div,← sum_mul,law.2,one_mul]
    rw [sum_comm]
  change expect p (fun w => Real.log (weight w)) - expect p (fun w =>
    total+(∑ b ∈ range J, cost b w)/(J:ℝ)) ≤ _
  rw [he,← sub_sub]
  exact H

end
end Meyniel.Multiscale
