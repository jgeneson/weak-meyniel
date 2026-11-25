import Meyniel.Game

namespace Meyniel.Extension
variable {V : Type*} {G : SimpleGraph V} {T : ℕ}

/-- A fixed shortest route from each possible endpoint to the common home. -/
noncomputable def route (hc : G.Connected) (x home : V) : G.Walk x home :=
  (hc.exists_walk_length_eq_dist x home).choose

theorem route_length (hc : G.Connected) (x home : V) :
    (route hc x home).length = G.dist x home :=
  (hc.exists_walk_length_eq_dist x home).choose_spec

noncomputable def extendWord (hc : G.Connected) (home : V) (w : Fin (T+1) → V)
    (t : ℕ) : V :=
  if h : t < T then w ⟨t, by omega⟩
  else (route hc (w (Fin.last T)) home).getVert (t-T)

theorem extendWord_at (hc : G.Connected) (home : V) (w : Fin (T+1) → V) (i : Fin (T+1)) :
    extendWord hc home w i.val = w i := by
  obtain ⟨t, ht⟩ := i
  by_cases h : t < T
  · simp [extendWord, h]
  · have he : t = T := by omega
    subst t
    simp [extendWord, Fin.last]

theorem extendWord_after (hc : G.Connected) (home : V) (w : Fin (T+1) → V)
    {t : ℕ} (ht : T ≤ t) :
    extendWord hc home w t = (route hc (w (Fin.last T)) home).getVert (t-T) := by
  simp [extendWord, Nat.not_lt.mpr ht]

theorem extendWord_home [Finite V] (hc : G.Connected) (home : V) (w : Fin (T+1) → V)
    {t : ℕ} (ht : T + G.diam ≤ t) : extendWord hc home w t = home := by
  letI : Nonempty V := ⟨home⟩
  rw [extendWord_after hc home w (by omega)]
  apply SimpleGraph.Walk.getVert_of_length_le
  rw [route_length]
  have hd : G.dist (w (Fin.last T)) home ≤ G.diam :=
    SimpleGraph.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc)
  omega

theorem extendWord_step (hc : G.Connected) (home : V) (w : Fin (T+1) → V)
    (hw : LegalWord G (List.ofFn w)) (t : ℕ) :
    Step G (extendWord hc home w t) (extendWord hc home w (t+1)) := by
  by_cases ht : t < T
  · have he (i : ℕ) (hi : i < T+1) : extendWord hc home w i = w ⟨i, hi⟩ :=
      extendWord_at hc home w ⟨i, hi⟩
    rw [he t (by omega), he (t+1) (by omega)]
    exact List.isChain_ofFn.mp hw t (by omega)
  · have h : T ≤ t := by omega
    rw [extendWord_after hc home w h, extendWord_after hc home w (by omega)]
    let path := route hc (w (Fin.last T)) home
    change Step G (path.getVert (t - T)) (path.getVert (t + 1 - T))
    rw [show t+1-T = (t-T)+1 by omega]
    by_cases hl : t - T < path.length
    · exact Or.inr (path.adj_getVert_succ hl)
    · left
      rw [path.getVert_of_length_le (by omega : path.length ≤ t - T),
        path.getVert_of_length_le (by omega : path.length ≤ t - T + 1)]

end Meyniel.Extension
