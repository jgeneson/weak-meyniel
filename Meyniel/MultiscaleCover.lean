import Meyniel.MultiscaleBands
import Meyniel.MultiscaleWindow
import Meyniel.Bounds

/-! A single deterministic window cover valid at every future launch time.
Its starting vertices are chosen before either prehistory observation. -/

namespace Meyniel.Multiscale
open Finset
noncomputable section
universe u
variable {V : Type u} {G : SimpleGraph V}

def shiftPath (R : ℕ → V) (u : ℕ) (t : ℕ) := R (u+t)

theorem shift_speed {R : ℕ → V} (h : SpeedOne G R) (u : ℕ) : SpeedOne G (shiftPath R u) :=
  fun j => h (u+j)

theorem shift_passes {R : ℕ → V} {q : GuardScale V} {u T : ℕ} (h : Passes G R q u (u+T)) :
    Passes G (shiftPath R u) q 0 T := by
  intro r hr F e _ hFe he hg hh hgood
  have hb := h r hr (u+F) (u+e) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by simpa [shiftPath,Nat.add_assoc] using hgood)
  intro l hl
  have h' := hb l (by omega)
  simpa only [shiftPath,Nat.add_assoc] using h'

theorem shift_hit (s : WindowPolicy G) (R : ℕ → V) (u T : ℕ) :
    windowHit s (shiftPath R u) 0 T ↔ windowHit s R u T := by simp [windowHit,shiftPath,Nat.add_assoc]

def encode (R : ℕ → V) (T : ℕ) : Fin (T+3) → V := fun i => R i.val

theorem hit_encoded (s : WindowPolicy G) {R R' : ℕ → V} {T : ℕ} (he : encode R T=encode R' T) :
    windowHit s R 0 T ↔ windowHit s R' 0 T := by
  have equal (i : ℕ) (hi : i<T+3) : R i=R' i := congrFun he ⟨i,hi⟩
  unfold windowHit
  simp only [Nat.zero_add]
  rw [equal 0 (by omega),equal 1 (by omega)]
  have h : (fun i : Fin (T+1) => R (2+i.val)) = fun i : Fin (T+1) => R' (2+i.val) := by
    funext i; apply equal; omega
  rw [h]

theorem mixture_good_count {S W : Type*} [Fintype W] (m : Mixture S) (hit : S → W → Prop)
    (p : ℝ) (hp : ∀ w, p ≤ m.success hit w) :
    ∃ s, p * Fintype.card W ≤ (by classical exact ((univ.filter (hit s)).card : ℝ)) := by
  classical
  let score i : ℝ := (univ.filter (hit (m.strategy i))).card
  have hn : Nonempty (Fin m.size) := by
    by_contra! h
    have eq := m.law.2
    letI : IsEmpty (Fin m.size) := h
    simp at eq
  letI := hn
  obtain ⟨i,_,hmax⟩ := univ.exists_max_image score univ_nonempty
  refine ⟨m.strategy i,?_⟩
  have hc (j : Fin m.size) : (∑ w, if hit (m.strategy j) w then (1:ℝ) else 0)=score j := by
    simp [score,sum_boole]
  calc
    _ = ∑ _w : W, p := by simp [mul_comm]
    _ ≤ ∑ w, m.success hit w := sum_le_sum (fun w _ => hp w)
    _ = ∑ j, m.prob j * score j := by
      unfold Mixture.success
      rw [sum_comm]
      simp_rw [←mul_sum,hc]
    _ ≤ ∑ j, m.prob j * score i := sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hmax j (mem_univ _)) (m.law.1 _))
    _ = _ := by rw [← sum_mul,m.law.2,one_mul]

/-- A finite input set is obtained by coding the T+3 observations. For each
remaining set we may take an arbitrary realization of each code. Complete
infinite paths are used only for the window's hypotheses. -/
theorem uniform_cover [Fintype V] (G : SimpleGraph V) (T N k : ℕ) (hn : Fintype.card V ≤ N)
    (starts : V → Prop) (fallback : {s : WindowPolicy G // starts s.start})
    (P : (ℕ → V) → Prop) (p : ℝ) (hp : p ≤ 1)
    (small : (N:ℝ)^(T+3)*(1-p)^k < 1)
    (one : ∀ (W : Type u) [Fintype W] [Nonempty W] (R : W → ℕ → V), (∀ w, P (R w)) →
      ∃ m : Mixture {s : WindowPolicy G // starts s.start}, ∀ w,
        p ≤ m.success (fun s w => windowHit s.1 (R w) 0 T) w) :
    ∃ team : Fin k → {s : WindowPolicy G // starts s.start},
      ∀ R u, P (shiftPath R u) → ∃ i, windowHit (team i).1 R u T := by
  classical
  let C := Fin (T+3) → V
  let U : Finset C := univ.filter (fun x => ∃ R, P R ∧ encode R T=x)
  let pick (x : C) (h : x∈U) := Classical.choose (mem_filter.mp h).2
  have spec (x : C) (h:x∈U) : P (pick x h) ∧ encode (pick x h) T=x := Classical.choose_spec (mem_filter.mp h).2
  let S := {s : WindowPolicy G // starts s.start}
  let hit (s:S) (x:C) := ∃ h : x∈U, windowHit s.1 (pick x h) 0 T
  have sel (A : Finset C) (ss : A ⊆ U) (ne : A.Nonempty) :
      ∃ s, p*A.card ≤ ((A.filter (hit s)).card:ℝ) := by
    letI : Nonempty A := ne.to_subtype
    let R (w:A) := pick w.val (ss w.property)
    obtain ⟨m,hm⟩ := one A R (fun w => (spec w.val (ss w.property)).1)
    obtain ⟨s,hs⟩ := mixture_good_count m _ p hm
    refine ⟨s,?_⟩
    have hh (w:A) : windowHit s.1 (R w) 0 T ↔ hit s w.val :=
      ⟨fun h => ⟨ss w.property,h⟩,fun ⟨_,h⟩ => h⟩
    simp only [hh,Fintype.card_coe] at hs
    change _ ≤ ((A.attach.filter (fun w => hit s w.val)).card:ℝ) at hs
    rw [Finset.filter_attach (hit s)] at hs
    simpa using hs
  have cU : (U.card:ℝ) ≤ (N:ℝ)^(T+3) := by
    exact_mod_cast (card_le_univ U).trans (by simpa [C] using Nat.pow_le_pow_left hn (T+3))
  have thresh := (mul_le_mul_of_nonneg_right cU (pow_nonneg (sub_nonneg.mpr hp) k)).trans_lt small
  obtain ⟨L,ls,all⟩ := greedy_cover hit p hp U sel k thresh
  let team (i : Fin k) : S := if h : i.val<L.length then L.get ⟨i.val,h⟩ else fallback
  refine ⟨team,?_⟩
  intro R u hR
  let x := encode (shiftPath R u) T
  have mem : x ∈ U := mem_filter.mpr ⟨mem_univ _,_,hR,rfl⟩
  obtain ⟨s,hL,hm,hs⟩ := all x mem
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hL
  refine ⟨⟨i.val,by omega⟩,?_⟩
  simpa only [team,dif_pos i.isLt] using (shift_hit _ R u T).mp ((hit_encoded _ (spec x hm).2).mp hs)

end
end Meyniel.Multiscale
