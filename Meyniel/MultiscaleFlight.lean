import Meyniel.MultiscaleSplice
import Meyniel.MultiscaleWindow

/-! Window histories and realizability of a move between comparison rows. -/
namespace Meyniel.Multiscale.Flight
open Meyniel.Multiscale

variable {W V : Type*} {G : SimpleGraph V}

def segment (r : ℕ → V) (u : ℕ) : ℕ → List V
  | 0 => []
  | n+1 => r u :: segment r (u+1) n

@[simp] theorem segment_length (r : ℕ → V) (u n : ℕ) : (segment r u n).length=n := by
  induction n generalizing u <;> simp [segment, *]

theorem segment_ofFn (r : ℕ → V) (u n : ℕ) :
    segment r u n = List.ofFn (fun i : Fin n => r (u+i.val)) := by
  induction n generalizing u with
  | zero => simp [segment]
  | succ n ih =>
    rw [segment,List.ofFn_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1; apply congrArg List.ofFn; funext i; congr 1; omega

theorem segment_add (r : ℕ → V) (u a b : ℕ) :
    segment r u (a+b) = segment r u a ++ segment r (u+a) b := by
  induction a generalizing u with
  | zero => simp [segment]
  | succ a ih =>
    rw [Nat.succ_add,segment,segment,List.cons_append,ih]
    simp [Nat.add_comm,Nat.add_left_comm]

theorem segment_prefix {r s : ℕ → V} {u a b : ℕ} (h : a ≤ b)
    (eqn : segment r u b=segment s u b) : segment r u a=segment s u a := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le h
  simpa [segment_add,List.take_append,segment_length] using congrArg (List.take a) eqn

def view (r : ℕ → V) (u t : ℕ) := segment r u (t+3)

def suffix (r : ℕ → V) (u T t : ℕ) := segment r (u+t+2) (T+1-t)

theorem view_refines {r s : ℕ → V} {u a b : ℕ} (h : a ≤ b)
    (eqn : view r u b=view s u b) : view r u a=view s u a :=
  segment_prefix (by omega) eqn

theorem suffix_split (r : ℕ → V) {u T a b : ℕ} (hab : a ≤ b) (hb : b ≤ T) :
    suffix r u T a = segment r (u+a+2) (b-a) ++ suffix r u T b := by
  unfold suffix
  have e : T+1-a=(b-a)+(T+1-b) := by omega
  rw [e,segment_add]
  congr 2; omega

theorem suffix_head (r : ℕ → V) {u T t : ℕ} (ht : t ≤ T) :
    suffix r u T t = r (u+t+2) :: segment r (u+t+3) (T-t) := by
  unfold suffix
  have e : T+1-t=(T-t)+1 := by omega
  rw [e,segment]

private theorem delayed_hits {k : ℕ} (pre : List V) (hl : pre.length=k) (route : ℕ→V)
    (leg : ∀ t, Step G (route t) (route (t+1))) (branch : List V → Anchored G (route k))
    (r : V) (tail : List V) (hit : Hits (branch (pre++[r])).val [] (r::tail)) :
    Hits (travelThen k route leg branch).val [] (pre++r::tail) := by
  subst k; exact travelThen_hits pre route leg branch r tail hit

theorem local_flight (G : SimpleGraph V) (hc : G.Connected) (R : W → ℕ → V)
    (u T a b : ℕ) (hab : a ≤ b) (hb : b ≤ T) (cur : W) (x z : V) (reach : G.dist x z ≤ b-a)
    (f : List V → Anchored G z) :
    ∃ p : Anchored G x, ∀ w, view (R w) u a = view (R cur) u a →
      Hits (f (view (R w) u b)).1 [] (suffix (R w) u T b) → Hits p.1 [] (suffix (R w) u T a) := by
  obtain ⟨route,ha,hz,step⟩ := route_to hc x z (b-a) reach
  subst x z
  let base := segment (R cur) u (a+2)
  let branch := fun (new : List V) => f (base++new)
  refine ⟨travelThen (b-a) route step branch,?_⟩
  intro w eqn hit
  let pre := segment (R w) (u+a+2) (b-a)
  let r := R w (u+b+2)
  let tail := segment (R w) (u+b+3) (T-b)
  have hl : pre.length=b-a := segment_length ..
  have e : base++(pre++[r])=view (R w) u b := by
    have e₀ : segment (R w) u (a+2) = base := segment_prefix (by omega : a+2 ≤ a+3) eqn
    rw [← e₀]
    unfold view pre r
    have he : b+3=(a+2)+((b-a)+1) := by omega
    rw [he,segment_add (R w) u (a+2) ((b-a)+1),segment_add (R w) (u+(a+2)) (b-a) 1]
    have hz : u+(a+2)+(b-a)=u+b+2 := by omega
    rw [hz]; simp [segment,Nat.add_assoc]
  have end_eq : suffix (R w) u T b = r::tail := suffix_head _ hb
  rw [end_eq] at hit
  have full_eq : suffix (R w) u T a=pre++r::tail := (suffix_split _ hab hb).trans (by rw [end_eq])
  rw [full_eq]
  apply delayed_hits pre hl route step branch r tail
  simpa only [branch,e] using hit

/-- A fixed start can wait before the first comparison. The two preceding
observations are available to the continuation when the first row is chosen. -/
theorem first_flight (G : SimpleGraph V) (R : W → ℕ → V) (u T t : ℕ) (ht : t ≤ T)
    (starts : V → Prop) (x : V) (hx : starts x) (f : List V → Anchored G x) :
    ∃ p : {s : WindowPolicy G // starts s.start}, ∀ w,
      Hits (f (view (R w) u t)).1 [] (suffix (R w) u T t) → windowHit p.1 (R w) u T := by
  let p : WindowPolicy G := ⟨x,fun a b =>
    (travelThen t (fun _ => x) (fun _ => Or.inl rfl) (fun new => f (a::b::new))).1,
    fun a b => (travelThen t (fun _ => x) (fun _ => Or.inl rfl) (fun new => f (a::b::new))).2⟩
  refine ⟨⟨p,hx⟩,fun w hit => ?_⟩
  let pre := segment (R w) (u+2) t
  have hl : pre.length=t := segment_length ..
  have eqn : R w u :: R w (u+1) :: (pre ++ [R w (u+t+2)]) = view (R w) u t := by
    unfold view pre
    have e : t+3=2+(t+1) := by omega
    rw [e,segment_add]
    change _ = _ :: _ :: segment (R w) (u+2) (t+1)
    rw [segment_add]
    simp [segment,Nat.add_right_comm]
  rw [suffix_head _ ht] at hit
  unfold windowHit
  rw [← segment_ofFn]
  have e : segment (R w) (u+2) (T+1) = pre++R w (u+t+2):: segment (R w) (u+t+3) (T-t) := by
    change suffix (R w) u T 0 = _
    rw [suffix_split _ (Nat.zero_le t) ht,suffix_head _ ht]
    rfl
  rw [e]
  change Hits (travelThen t (fun _ => x) (fun _ => Or.inl rfl)
    (fun new => f (R w u::R w (u+1)::new))).1 [] _
  apply delayed_hits pre hl
  rwa [eqn]

end Meyniel.Multiscale.Flight
