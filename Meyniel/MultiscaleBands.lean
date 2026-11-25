import Meyniel.MultiscaleGeometry

/-! Tests of radial progress and their enforcement by local guard windows.
The input path contains two positions preceding time zero. The anchor at
launch time F is exactly the robber's vertex from two rounds before F. -/

namespace Meyniel.Multiscale
open Finset
variable {V : Type*} {G : SimpleGraph V}

def SpeedOne (G : SimpleGraph V) (R : ℕ → V) : Prop := ∀ t, Step G (R t) (R (t+1))

theorem displacement (hc : G.Connected) {R : ℕ → V} (hR : SpeedOne G R) {u v : ℕ}
    (huv : u ≤ v) : G.dist (R u) (R v) ≤ v-u := by
  induction v, huv using Nat.le_induction with
  | base => simp
  | succ v huv ih =>
    have h : G.dist (R v) (R (v+1)) ≤ 1 := by
      rcases hR v with e | e
      · rw [e]; simp
      · exact (SimpleGraph.dist_eq_one_iff_adj.mpr e).le
    have tri := hc.dist_triangle (u:=R u) (v:=R v) (w:=R (v+1))
    omega

/-- The strict inequality is written additively so that the lower band may
be negative. Natural subtraction here would give the wrong test at zero. -/
def InBand (G : SimpleGraph V) (R : ℕ → V) (F e w : ℕ) : Prop :=
  ∀ l ≤ e-F, l < G.dist (R F) (R (F+l+2)) + w ∧ G.dist (R F) (R (F+l+2)) ≤ l+2

theorem band_of_endpoint (hc : G.Connected) {R : ℕ → V} (hR : SpeedOne G R) {F e w : ℕ}
    (hFe : F ≤ e) (far : e-F < G.dist (R F) (R (e+2)) + w) : InBand G R F e w := by
  intro l hl
  have hle : F+l+2 ≤ e+2 := by omega
  have htail := displacement hc hR hle
  have hfront := displacement hc hR (u:=F) (v:=F+l+2) (by omega)
  have htri := hc.dist_triangle (u:=R F) (v:=R (F+l+2)) (w:=R (e+2))
  omega

/-- All copies at a center can run for T rounds, deploy for 2T, and return
for 3T. The first deadline is 3T after arrival and subsequent deadlines are
spaced by s. This gives the first deadline following a proposed visit. -/
theorem next_deadline (arrival T s e : ℕ) (hs : 0 < s) (he : arrival+3*T ≤ e) :
    ∃ j : ℕ, e ≤ arrival + 3*T + j*s ∧ arrival+3*T+j*s ≤ e+s ∧
      (arrival+3*T+j*s)-T ≥ arrival+2*T := by
  let n := e-(arrival+3*T)
  let j := (n+s-1)/s
  have h1 := Nat.mod_lt (n+s-1) hs
  have h2 := Nat.mod_add_div (n+s-1) s
  refine ⟨j,?_,?_,?_⟩ <;> dsimp [j,n] at * <;> rw [Nat.mul_comm _ s] <;> omega

theorem copies_do_not_overlap (T s : ℕ) (hs : 0 < s) :
    6*T ≤ (6*T/s+1)*s := by
  have h := Nat.mod_add_div (6*T) s
  have hm := Nat.mod_lt (6*T) hs
  rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm _ s]
  omega

structure GuardScale (V : Type*) where
  radii : Finset ℕ
  lead : ℕ → ℕ
  last : ℕ → ℕ
  base : ℕ
  run : ℕ
  width : ℕ
  good : V → Prop

def Passes (G : SimpleGraph V) (R : ℕ → V) (q : GuardScale V) (start stop : ℕ) : Prop :=
  ∀ r ∈ q.radii, ∀ F e, start ≤ F → F ≤ e → e ≤ stop →
    q.lead r ≤ e-F → e-F < q.last r → q.good (R (e+2)) → InBand G R F e q.width

theorem passes_subwindow {R : ℕ → V} {q : GuardScale V} {a b c d : ℕ}
    (h : Passes G R q a d) (h1 : a ≤ b) (h2 : c ≤ d) : Passes G R q b c :=
  fun r hr F e hF hFe he hg hH hgood => h r hr F e (h1.trans hF) hFe (he.trans h2) hg hH hgood

/-- Departing at the first threshold crossing is at least as fast as
departing from the present point on the trail. -/
theorem first_dispatch_le (hc : G.Connected) {R : ℕ → V} (hR : SpeedOne G R)
    {F f : ℕ} (h : f ≤ F) (z : V) :
    f + G.dist (R f) z ≤ F + G.dist (R F) z := by
  have htri := hc.dist_triangle (u:=R f) (v:=R F) (w:=z)
  have hu := displacement hc hR h
  omega

/-- On an evading walk, a guard running a full cycle excludes a violation
of the endpoint bound. Here cover is the pointwise guarantee of the
deployed deterministic team at each scheduled deadline. -/
theorem guarded_test (hc : G.Connected) {R : ℕ → V} (hR : SpeedOne G R)
    (q : GuardScale V) (F e : ℕ) (hFe : F ≤ e)
    (hslack : 3*q.run + q.base ≤ q.width)
    (hguard : ∀ z, G.dist (R (e+2)) z ≤ q.base →
      F + G.dist (R F) z + 3*q.run ≤ e →
      ∃ e', e ≤ e' ∧ e' ≤ e+q.base ∧ 2*q.base < G.dist (R (e'+2)) z)
    (covered : ∃ z, G.dist (R (e+2)) z ≤ q.base) : InBand G R F e q.width := by
  apply band_of_endpoint hc hR hFe
  by_contra! hslow
  obtain ⟨z,hz⟩ := covered
  have ta := hc.dist_triangle (u:=R F) (v:=R (e+2)) (w:=z)
  obtain ⟨e',he',hemax,hmiss⟩ := hguard z hz (by omega)
  have d := displacement hc hR (u:=e+2) (v:=e'+2) (by omega)
  have tt := hc.dist_triangle (u:=R (e'+2)) (v:=R (e+2)) (w:=z)
  rw [@SimpleGraph.dist_comm _ G (R (e'+2)) (R (e+2))] at tt
  omega

/-- A guarded window on the next level can use all previously enforced
tests. The decreasing end limits allow s extra rounds for the next deadline. -/
theorem enforce_levels {k : ℕ} (G : SimpleGraph V) (R : ℕ → V) (q : Fin k → GuardScale V)
    (limit : Fin k → ℕ)
    (guard : ∀ i, (∀ j < i, Passes G R (q j) 0 (limit j)) → Passes G R (q i) 0 (limit i))
    (W : ℕ) (hlim : ∀ i, W ≤ limit i) :
    ∀ i, Passes G R (q i) 0 W := by
  have all (i : Fin k) : Passes G R (q i) 0 (limit i) := by
    induction i using WellFoundedLT.induction with
    | ind i ih => exact guard i ih
  exact fun i => passes_subwindow (all i) le_rfl (hlim i)

end Meyniel.Multiscale
