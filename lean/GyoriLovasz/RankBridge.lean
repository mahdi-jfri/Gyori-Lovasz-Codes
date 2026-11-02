import GyoriLovasz.Criticality

namespace GyoriLovasz
open Side

noncomputable def putSep (C : Cut α) (q : α) : Cut α :=
  by classical exact fun x => if x = q then sep else C x

theorem size_putSep_absent {vertices : List α} {C : Cut α} {q : α}
    (h : q ∉ vertices) : size vertices (putSep C q) = size vertices C := by
  classical
  induction vertices with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ q := by intro he; subst x; exact h (by simp)
    have hxs : q ∉ xs := fun he => h (by simp [he])
    simp only [size, putSep, if_neg hx]
    rw [ih hxs]

theorem size_putSep {vertices : List α} {C : Cut α} {q : α}
    (hn : vertices.Nodup) (hq : q ∈ vertices) (hl : C q = left) :
    size vertices (putSep C q) = size vertices C + 1 := by
  classical
  induction vertices with
  | nil => simp at hq
  | cons x xs ih =>
    have hn' := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hq with he | he
    · subst x
      have ha := size_putSep_absent (C := C) hn'.1
      simp only [size, putSep, if_pos rfl, hl, Side.weight]
      change 1 + size xs (putSep C q) = 0 + size xs C + 1
      omega
    · by_cases hx : x = q
      · subst x
        exact False.elim (hn'.1 he)
      · have hi := ih hn'.2 he
        simp only [size, putSep, if_neg hx]
        change (C x).weight + size xs (putSep C q) = (C x).weight + size xs C + 1
        omega

theorem valid_lift_deleted {E : α → α → Prop} {T : α → Prop}
    {v p q : α} {C : Cut α}
    (hc : Valid (DeleteEdge E p q) T v C) (hq : C q = left) :
    Valid E T v (putSep C q) := by
  classical
  have hvq : v ≠ q := by
    intro he
    have hs := hc.source
    rw [he, hq] at hs
    cases hs
  refine ⟨by simp [putSep, hvq, hc.source], ?_, ?_⟩
  · intro t ht
    by_cases h : t = q
    · simp [putSep, h]
    · simpa [putSep, h] using hc.terminals t ht
  · intro x y he hx hy
    have hxq : x ≠ q := by
      intro h
      simp [putSep, h] at hx
    have hyq : y ≠ q := by
      intro h
      simp [putSep, h] at hy
    have hxc : C x = right := by simpa [putSep, hxq] using hx
    have hyc : C y = left := by simpa [putSep, hyq] using hy
    exact hc.no_cross x y ⟨he, fun h => hyq h.2⟩ hxc hyc

theorem rank_delete_le {vertices : List α} {E : α → α → Prop}
    {T : α → Prop} {v p q : α} {r s : Nat}
    (hr : HasRank vertices E T v r)
    (hs : HasRank vertices (DeleteEdge E p q) T v s) : s ≤ r := by
  obtain ⟨C, hc⟩ := hr.witness
  have h := hs.lower C (valid_delete hc.1)
  rw [hc.2] at h
  exact h

theorem rank_delete_lower {vertices : List α} {E : α → α → Prop}
    {T : α → Prop} {v p q : α} {r s : Nat}
    (hn : vertices.Nodup) (hq : q ∈ vertices)
    (hr : HasRank vertices E T v r)
    (hs : HasRank vertices (DeleteEdge E p q) T v s) : r ≤ s + 1 := by
  classical
  obtain ⟨C, hc⟩ := hs.witness
  by_cases hv : Valid E T v C
  · have h := hr.lower C hv
    have heq := hc.2
    omega
  · have cross := invalid_restore_crosses hc.1 hv
    have lifted := valid_lift_deleted hc.1 cross.2
    have lower := hr.lower (putSep C q) lifted
    have sz := size_putSep hn hq cross.2
    have heq := hc.2
    omega

/-- A cut-only replacement for the rerouting fact used in Lemma 4.9.
Any rank-decreasing deletion out of `p` makes every OTHER terminal neighbor
of `p` essential in the original graph. -/
theorem rank_drop_neighbor_essential {vertices : List α} {E : α → α → Prop}
    {T : α → Prop} {v p q t : α} {r s : Nat}
    (hn : vertices.Nodup) (hq : q ∈ vertices)
    (hr : HasRank vertices E T v r)
    (hs : HasRank vertices (DeleteEdge E p q) T v s)
    (drop : s < r) (ht : T t) (hp : E p t) (hqt : q ≠ t) :
    CutEssential vertices E T v r t := by
  classical
  obtain ⟨C, hc⟩ := hs.witness
  have invalid : ¬Valid E T v C := by
    intro h
    have l := hr.lower C h
    have eq := hc.2
    omega
  have cross := invalid_restore_crosses hc.1 invalid
  have edge : DeleteEdge E p q p t :=
    ⟨hp, fun h => hqt h.2.symm⟩
  have nl := hc.1.no_cross p t edge cross.1
  have nr := hc.1.terminals t ht
  have ct : C t = sep := by
    cases h : C t with
    | left => exact False.elim (nl h)
    | sep => rfl
    | right => exact False.elim (nr h)
  have lifted := valid_lift_deleted hc.1 cross.2
  have sz := size_putSep hn hq cross.2
  have lower := hr.lower (putSep C q) lifted
  have eq := hc.2
  refine ⟨putSep C q, ⟨lifted, by omega⟩, ?_⟩
  simp [putSep, Ne.symm hqt, ct]

theorem criticality_assignable {vertices : List α} {E : α → α → Prop}
    {T : α → Prop} {v p q t u : α} {r s : Nat}
    (hn : vertices.Nodup) (hq : q ∈ vertices)
    (hr : HasRank vertices E T v r)
    (hs : HasRank vertices (DeleteEdge E p q) T v s)
    (hu : T u) (hp : E p u) (hqu : q ≠ u)
    (he : CutEssential vertices E T v r t)
    (hlost : ¬CutEssential vertices (DeleteEdge E p q) T v s t) :
    CutEssential vertices E T v r u :=
  rank_drop_neighbor_essential hn hq hr hs
    (critical_forces_rank_drop hs he hlost) hu hp hqu

/-- Complete cut-based version of Lemma 4.14.
Ranks are explicit minimum-cut witnesses, not unproved path-connectivity claims.
No common-rank hypothesis is assumed: it is derived below.
-/
theorem transfer_criticality {vertices : List α} {E : α → α → Prop}
    {T : α → Prop} {v p q p' q' t u : α} {r ri rj rh : Nat}
    (hn : vertices.Nodup) (hq : q ∈ vertices) (hq' : q' ∈ vertices)
    (hr : HasRank vertices E T v r)
    (hi : HasRank vertices (DeleteEdge E p q) T v ri)
    (hj : HasRank vertices (DeleteEdge E p' q') T v rj)
    (hh : HasRank vertices (DeleteEdge (DeleteEdge E p' q') p q) T v rh)
    (ht : T t) (hu : T u) (hp : E p u) (hqu : q ≠ u)
    (hpp' : p ≠ p')
    (et : CutEssential vertices E T v r t)
    (it : ¬CutEssential vertices (DeleteEdge E p q) T v ri t)
    (ju : ¬CutEssential vertices (DeleteEdge E p' q') T v rj u) :
    ¬CutEssential vertices (DeleteEdge E p' q') T v rj t := by
  classical
  have eu := criticality_assignable hn hq hr hi hu hp hqu et it
  have iu := secondary_not_critical hr hi hu hp hqu eu
  have di := critical_forces_rank_drop hi et it
  have dj := critical_forces_rank_drop hj eu ju
  have bi := rank_delete_lower hn hq hr hi
  have bj := rank_delete_lower hn hq' hr hj
  have eqij : ri = rj := by omega
  have eqr : r = ri + 1 := by omega
  have hle := rank_delete_le hj hh
  have eqh : rh = rj := by
    by_cases hlt : rh < rj
    · have surviving : DeleteEdge E p' q' p u :=
        ⟨hp, fun h => hpp' h.1⟩
      exact False.elim (ju (rank_drop_neighbor_essential hn hq hj hh hlt hu surviving hqu))
    · omega
  intro jt
  have original : HasRank vertices E T v (ri + 1) := eqr ▸ hr
  have common : HasRank vertices (DeleteEdge (DeleteEdge E p q) p' q') T v ri := by
    have eq : rh = ri := by omega
    have same : DeleteEdge (DeleteEdge E p' q') p q =
        DeleteEdge (DeleteEdge E p q) p' q' := by
      funext x y
      apply propext
      constructor
      · intro h; exact ⟨⟨h.1.1, h.2⟩, h.1.2⟩
      · intro h; exact ⟨⟨h.1.1, h.2⟩, h.1.2⟩
    rw [← same, ← eq]
    exact hh
  have jt' : CutEssential vertices (DeleteEdge E p' q') T v ri t := eqij.symm ▸ jt
  have ju' : ¬CutEssential vertices (DeleteEdge E p' q') T v ri u := eqij.symm ▸ ju
  exact rank_pattern_impossible original common ht hu iu it jt' ju'

end GyoriLovasz
