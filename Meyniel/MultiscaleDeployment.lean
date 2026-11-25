import Meyniel.GuardDispatch
import Meyniel.SquareTrail

/-! From local and global deterministic window covers to a physical game.
The cost of mobile guards is bounded along each realized walk. -/
namespace Meyniel.Multiscale.Deployment
open Meyniel.Multiscale
variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] {G : SimpleGraph V} {k : ℕ}
noncomputable section

structure Site (q : Fin k → GuardScale V) (G : SimpleGraph V) where
  level : Fin k
  radius : ℕ
  center : V
  count : ℕ
  copies : ℕ
  policy : Fin count → WindowPolicy G
  period : 2*(q level).run < copies*(q level).base
  start_near : ∀ j, G.dist center (policy j).start ≤ 2*(q level).run

abbrev Jobs {q : Fin k → GuardScale V} (site : I → Site q G) :=
  (i : I) × Fin (site i).copies × Fin (site i).count

def active {q : Fin k → GuardScale V} (site : I → Site q G) (stop : ℕ) (i : I)
    (R : ℕ → V) (f : ℕ) : Bool :=
  decide (f ≤ stop ∧ G.dist (R f) (site i).center ≤ (q (site i).level).last (site i).radius + 2*(q (site i).level).base)

omit [Fintype V] [Fintype I] [DecidableEq I] in
private theorem active_causal {q : Fin k → GuardScale V} (site : I → Site q G)
    (stop : ℕ) (i : I) (R S : ℕ → V) (_ : SpeedOne G R) (_ : SpeedOne G S) (t : ℕ)
    (he : SameThrough R S (t+2)) : active site stop i R t = active site stop i S t := by
  simp only [active,he t (by omega)]

def assignments {q : Fin k → GuardScale V} (site : I → Site q G) (stop : ℕ) (R : ℕ → V) (f : ℕ) :
    Finset (Jobs site) := Finset.univ.filter (fun j => active site stop j.1 R f = true)

omit [Fintype V] [DecidableEq I] in
private theorem assignment_obs {q : Fin k → GuardScale V} (site : I → Site q G) (stop : ℕ) :
    ∀ R S, SpeedOne G R → SpeedOne G S → ∀ t, SameThrough R S (t+2) →
      assignments site stop R t = assignments site stop S t := by
  intro R S hr hs t he
  ext j
  simp [assignments,active_causal site stop j.1 R S hr hs t he]

def guards {q : Fin k → GuardScale V} (hc : G.Connected) (site : I → Site q G) (stop : ℕ)
    (j : Jobs site) : PhysicalPolicy G :=
  let z := site j.1
  let g := q z.level
  let s := z.policy j.2.2
  GuardDispatch.dispatched (GuardDispatch.working hc s g.run (z.copies*g.base) (j.2.1.val*g.base)
    z.period (z.start_near j.2.2)) (active site stop j.1) (active_causal site stop j.1)

omit [Fintype V] in
private theorem idle {q : Fin k → GuardScale V} (hc : G.Connected) (site : I → Site q G) (stop : ℕ) :
    ∀ R, SpeedOne G R → ∀ j t, j ∉ GuardPool.queue (assignments site stop) R t →
      (guards hc site stop j).pos R t = R t := by
  intro R _ j t hn
  cases h : GuardDispatch.first (active site stop j.1) R t with
  | none => simp [guards,GuardDispatch.dispatched,h]
  | some f =>
    obtain ⟨hf,ha,_⟩ := GuardDispatch.first_iff.mp h
    exact (hn (GuardPool.mem_queue.mpr ⟨f,hf,by simp [assignments,ha]⟩)).elim

def reserve {q : Fin k → GuardScale V} (hc : G.Connected) (site : I → Site q G) (stop : ℕ)
    (slot : ℕ) : PhysicalPolicy G :=
  GuardPool.slot (guards hc site stop) (assignments site stop)
    (assignment_obs site stop) (idle hc site stop) slot

omit [Fintype V] in
/-- Counting online reservations is exactly the sum of all staggered local
team sizes at centers that have triggered at least once. -/
theorem cost_eq {q : Fin k → GuardScale V} (site : I → Site q G) (stop : ℕ) (R : ℕ → V) (H : ℕ) :
    (GuardPool.queue (assignments site stop) R H).length =
      ∑ i : I, if ∃ f < H, active site stop i R f = true then (site i).copies*(site i).count else 0 := by
  classical
  let Q := GuardPool.queue (assignments site stop) R H
  have card : Q.toFinset.card = Q.length := List.toFinset_card_of_nodup (GuardPool.queue_nodup ..)
  rw [←card,show Q.toFinset.card = ∑ _j ∈ Q.toFinset, (1:ℕ) by simp]
  have card' : ∑ j ∈ Q.toFinset, 1 = ∑ j : Jobs site, if ∃ f < H, active site stop j.1 R f = true then 1 else 0 := by
    rw [←Finset.sum_filter]
    congr 1
    ext j
    simp [Q,GuardPool.mem_queue,assignments]
  rw [card',Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ev : ∃ f < H, active site stop i R f = true <;> simp [ev]

private def fixedGlobal (s : WindowPolicy G) : PhysicalPolicy G where
  pos R t := WindowRun.position s R 0 t
  step R _ t := WindowRun.position_step ..
  causal R S _ _ t he := WindowRun.position_congr _ _ _ (by simpa using he)

omit [Fintype V] in
private theorem catch_global (s : WindowPolicy G) (R : ℕ → V) {W H : ℕ} (h : W ≤ H)
    (hit : windowHit s R 0 W) : PhysicalHit (fixedGlobal s) R 0 H := by
  obtain ⟨j,hj,ht | ⟨ht,eq⟩⟩ := WindowRun.hit_in_run s R 0 W hit
  · exact ⟨j,by omega,by omega,Or.inl (by simpa [fixedGlobal] using ht)⟩
  · exact ⟨j,by omega,by omega,Or.inr ⟨by omega,by simpa [fixedGlobal] using eq⟩⟩

omit [Fintype V] [Fintype I] [DecidableEq I] in
/-- At deadline number a the copy with residue a modulo the number of
copies is conducting its a/copies-th local run. -/
private theorem catch_local {q : Fin k → GuardScale V} (hc : G.Connected) (site : I → Site q G)
    (stop : ℕ) (i : I) (R : ℕ → V) (f a : ℕ) (p : Fin (site i).count)
    (good : active site stop i R f = true) (prev : ∀ j < f, active site stop i R j = false)
    (hT : 0 < (q (site i).level).run)
    (hit : windowHit ((site i).policy p) R
      (f+G.dist (R f) (site i).center+2*(q (site i).level).run+a*(q (site i).level).base)
      (q (site i).level).run) :
    ∃ j : Jobs site, j.1=i ∧ PhysicalHit (guards hc site stop j) R 0
      (f+G.dist (R f) (site i).center+3*(q (site i).level).run+a*(q (site i).level).base) := by
  let z := site i
  let g := q z.level
  let T := g.run
  let s := g.base
  let c := z.copies
  let P := c*s
  let dist := G.dist (R f) z.center
  let u := f+dist+2*T+a*s
  have period : 2*T < P := z.period
  have posC : 0 < c := by by_contra! hn; have := Nat.eq_zero_of_le_zero hn; simp [P,this] at period
  let l : Fin c := ⟨a%c,Nat.mod_lt _ posC⟩
  let b := a/c
  let j : Jobs site := ⟨i,l,p⟩
  have sum : l.val*s+b*P = a*s := by
    have h := congrArg (fun n : ℕ => n*s) (Nat.mod_add_div a c)
    change (a%c+c*(a/c))*s = a*s at h
    rw [Nat.add_mul] at h
    simpa only [l,b,P,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h
  have hs (v : ℕ) (hv : v ≤ T) : (guards hc site stop j).pos R (u+v) = WindowRun.position (z.policy p) R u v := by
    have later : f < u+v := by dsimp [u]; change 0<T at hT; omega
    have first := GuardDispatch.first_iff.mpr (show f < u+v ∧ _ ∧ _ from ⟨later,good,prev⟩)
    change (match GuardDispatch.first (active site stop i) R (u+v) with
      | none => R (u+v)
      | some f' => (GuardDispatch.working hc (z.policy p) T P (l.val*s) period (z.start_near p)).pos R f' (u+v-f')) = _
    rw [first]
    change (GuardDispatch.working hc (z.policy p) T P (l.val*s) period (z.start_near p)).pos R f (u+v-f) = _
    have eq : u+v-f=dist+(2*T+l.val*s)+b*P+v := by dsimp [u]; omega
    rw [eq]
    have hw := GuardDispatch.working_run hc (z.policy p) T P (l.val*s) period (z.start_near p) R f b v hv
    have hu : f + dist + (2*T+l.val*s) + b*P = u := by dsimp [u]; omega
    exact hw.trans (congrArg (fun t => WindowRun.position (z.policy p) R t v) hu)
  have endeq : f+G.dist (R f) (site i).center+3*(q (site i).level).run+a*(q (site i).level).base = u+T := by
    dsimp [u,dist,T,s,g,z]; omega
  refine ⟨j,rfl,?_⟩
  rw [endeq]
  obtain ⟨v,hv,now | ⟨before,done⟩⟩ := WindowRun.hit_in_run (z.policy p) R u T hit
  · exact ⟨u+v,by omega,by omega,Or.inl ((hs v hv).trans now)⟩
  · have later := hs (v+1) (by omega)
    rw [←Nat.add_assoc] at later
    exact ⟨u+v,by omega,by omega,Or.inr ⟨by omega,later.trans done⟩⟩


/-- Explicit obligations for using local and global window covers together.
All deadline and packing inequalities are ordinary numerical properties of
the chosen scales. The continuation below discharges the online strategy. -/
structure WindowCovers (q : Fin k → GuardScale V) (site : I → Site q G) {p : ℕ}
    (global : Fin p → WindowPolicy G) (limit : Fin k → ℕ) (W stop H K : ℕ) : Prop where
  global_end : W ≤ H
  limits : ∀ l, W ≤ limit l ∧ limit l ≤ stop ∧ limit l + (q l).base ≤ H
  slack : ∀ l, 0 < (q l).base ∧ 0 < (q l).run ∧ 3*(q l).run + (q l).base ≤ (q l).width
  nested : ∀ l m, m < l → limit l + (q l).base ≤ limit m
  centers : ∀ l r, r ∈ (q l).radii → ∀ y, (q l).good y →
    ∃ i, (site i).level=l ∧ (site i).radius=r ∧ G.dist y (site i).center ≤ (q l).base
  local_cover : ∀ i R u, SpeedOne G R →
    G.dist (R (u+(q (site i).level).run+2)) (site i).center ≤ 2*(q (site i).level).base →
    (∀ l < (site i).level, Passes G R (q l) u (u+(q (site i).level).run)) →
    ∃ j, windowHit ((site i).policy j) R u (q (site i).level).run
  global_cover : ∀ R, SpeedOne G R → (∀ l, Passes G R (q l) 0 W) → ∃ j, windowHit (global j) R 0 W
  cost : ∀ R, SpeedOne G R →
    (∑ i : I, if ∃ f < H, active site stop i R f = true then (site i).copies*(site i).count else 0) ≤ K

omit [Fintype V] in
private theorem passes_if_evaded {q : Fin k → GuardScale V} (hc : G.Connected)
    {site : I → Site q G} {p : ℕ} {global : Fin p → WindowPolicy G} {limit : Fin k → ℕ}
    {W stop H K : ℕ} (cover : WindowCovers q site global limit W stop H K)
    (R : ℕ → V) (hR : SpeedOne G R) (evaded : ∀ i < K, ¬ PhysicalHit (reserve hc site stop i) R 0 H) :
    ∀ l, Passes G R (q l) 0 W := by
  classical
  apply enforce_levels G R q limit _ W (fun l => (cover.limits l).1)
  intro l ih r hr F e _ Fe he lo ltLast good
  apply band_of_endpoint hc hR Fe
  by_contra! slow
  obtain ⟨i,il,ir,close⟩ := cover.centers l r hr (R (e+2)) good
  let z := (site i).center
  let s := (q l).base
  let T := (q l).run
  have hsl := cover.slack l
  have ht := hc.dist_triangle (u:=R F) (v:=R (e+2)) (w:=z)
  have cf : active site stop i R F = true := by
    simp only [active,il,ir,decide_eq_true_eq]
    exact ⟨Fe.trans (he.trans (cover.limits l).2.1),by change G.dist (R F) z ≤ _; dsimp [z] at *; omega⟩
  let existsFirst : ∃ f, active site stop i R f = true := ⟨F,cf⟩
  let f := Nat.find existsFirst
  have f_yes : active site stop i R f = true := Nat.find_spec existsFirst
  have f_le : f ≤ F := Nat.find_min' existsFirst cf
  have earlier (a : ℕ) (ha : a < f) : active site stop i R a = false := by
    have no := Nat.find_min existsFirst ha
    cases eq : active site stop i R a <;> simp_all
  let arrival := f + G.dist (R f) z
  have arr := first_dispatch_le hc hR f_le z
  have intime : arrival + 3*T ≤ e := by dsimp [arrival,T,z] at *; omega
  obtain ⟨a,hafter,hbefore,_⟩ := next_deadline arrival T s e hsl.1 intime
  let u := arrival+2*T+a*s
  have endpoint : arrival + 3*T + a*s = u+T := by dsimp [u]; omega
  rw [endpoint] at hbefore hafter
  have near : G.dist (R (u+T+2)) z ≤ 2*s := by
    have motion := displacement hc hR (u:=e+2) (v:=u+T+2) (by omega)
    have tri := hc.dist_triangle (u:=R (u+T+2)) (v:=R (e+2)) (w:=z)
    rw [@SimpleGraph.dist_comm _ G (R (u+T+2)) (R (e+2))] at tri
    change G.dist (R (e+2)) z ≤ s at close
    omega
  have lower : ∀ m < (site i).level, Passes G R (q m) u (u+(q (site i).level).run) := by
    intro m hm
    rw [il] at hm ⊢
    apply passes_subwindow (ih m hm) (Nat.zero_le _)
    have bound := cover.nested l m hm
    change u+T ≤ limit m
    change limit l + s ≤ limit m at bound
    omega
  obtain ⟨p',hp⟩ := cover.local_cover i R u hR (by simpa only [il] using near) lower
  have localHit : windowHit ((site i).policy p') R
      (f+G.dist (R f) (site i).center+2*(q (site i).level).run+a*(q (site i).level).base)
      (q (site i).level).run := by simpa only [u,arrival,T,s,z,il] using hp
  obtain ⟨j,hsite,hj⟩ := catch_local hc site stop i R f a p' f_yes earlier
    (by rw [il]; exact hsl.2.1) localHit
  have finish : f+G.dist (R f) (site i).center+3*(q (site i).level).run+a*(q (site i).level).base ≤ H := by
    rw [il]; change arrival+3*T+a*s ≤ H; rw [endpoint]
    have := (cover.limits l).2.2
    change limit l + s ≤ H at this
    omega
  have f_before : f < H := by
    rw [il] at finish
    have pos := hsl.2.1
    omega
  have inQ : j ∈ GuardPool.queue (assignments site stop) R H := GuardPool.mem_queue.mpr
    ⟨f,f_before,by simp [assignments,hsite,f_yes]⟩
  have budget : (GuardPool.queue (assignments site stop) R H).length ≤ K := (cost_eq ..).le.trans (cover.cost R hR)
  obtain ⟨idx,owns⟩ := GuardPool.preserving_slot (assignment_obs site stop) (idle hc site stop) hR budget inQ
  apply evaded idx.val idx.isLt
  obtain ⟨t,h0,hH,hit | ⟨before,hit⟩⟩ := hj.mono le_rfl finish
  · exact ⟨t,h0,hH,Or.inl ((owns t hH).trans hit)⟩
  · exact ⟨t,h0,hH,Or.inr ⟨before,(owns (t+1) (by omega)).trans hit⟩⟩

omit [Fintype V] in
/-- The local packed guards and waiting global team win physically from lag
two. The tile placements and staggered deadlines are all generated online. -/
theorem trail_continuation {q : Fin k → GuardScale V} (hc : G.Connected) {site : I → Site q G}
    {p : ℕ} {global : Fin p → WindowPolicy G} {limit : Fin k → ℕ} {W stop H K : ℕ}
    (cover : WindowCovers q site global limit W stop H K)
    (x y r : V) (xy : Step G x y) (yr : Step G y r) :
    CatchesWithin G (K+p) H (Fin.append (fun _ => x) (fun i => (global i).start)) r := by
  let team := Fin.append (fun i : Fin K => reserve hc site stop i.val) (fun i : Fin p => fixedGlobal (global i))
  apply physical_cover_gives_game team xy yr
  · intro R _ hx _ _ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [team,reserve] using hx
    · simp [team,fixedGlobal]
  · intro R hs _ _ _
    by_cases success : ∃ i < K, PhysicalHit (reserve hc site stop i) R 0 H
    · obtain ⟨i,hi,hit⟩ := success
      refine ⟨(⟨i,hi⟩ : Fin K).castAdd p,?_⟩
      simpa only [team,Fin.append_left] using hit
    · push Not at success
      obtain ⟨j,hit⟩ := cover.global_cover R hs (passes_if_evaded hc cover R hs success)
      exact ⟨Fin.natAdd K j, by simpa [team] using catch_global (global j) R cover.global_end hit⟩

/-- A winning square search plus the window-cover budget gives a win with
all initial placements chosen before the robber appears. -/
theorem winsWith_windows {q : Fin k → GuardScale V} (hc : G.Connected) {site : I → Site q G}
    {p s : ℕ} {global : Fin p → WindowPolicy G} {limit : Fin k → ℕ} {W stop H K : ℕ}
    (cover : WindowCovers q site global limit W stop H K) (squared : WinsWith (SquareTrail.square G) s) :
    WinsWith G ((s+K)+p) :=
  SquareTrail.winsWith_from_trail hc squared (fun i => (global i).start)
    (fun x y r xy yr => ⟨H,trail_continuation hc cover x y r xy yr⟩)

end
end Meyniel.Multiscale.Deployment
