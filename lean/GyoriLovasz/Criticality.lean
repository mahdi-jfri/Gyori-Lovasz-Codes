import GyoriLovasz.Cuts

/-!
Cut-based essentiality. Its equivalence to the paper's path-based definition
requires finite directed Menger; that bridge is not asserted in this project.
`rank_pattern_impossible` proves the uncrossing contradiction in Lemma 4.14.
The common-rank hypothesis for the graph with BOTH arcs removed is explicit
in this intermediate file. `RankBridge.lean` discharges it using cuts.
-/
namespace GyoriLovasz
open Side

def RankCut (vertices : List α) (E : α → α → Prop) (T : α → Prop)
    (v : α) (r : Nat) (C : Cut α) : Prop :=
  Valid E T v C ∧ size vertices C = r

structure HasRank (vertices : List α) (E : α → α → Prop)
    (T : α → Prop) (v : α) (r : Nat) : Prop where
  witness : ∃ C, RankCut vertices E T v r C
  lower : ∀ C, Valid E T v C → r ≤ size vertices C

def CutEssential (vertices : List α) (E : α → α → Prop) (T : α → Prop)
    (v : α) (r : Nat) (t : α) : Prop :=
  ∃ C, RankCut vertices E T v r C ∧ C t = sep

theorem rankcut_minimum {vertices : List α} {E : α → α → Prop}
    {T : α → Prop} {v : α} {r : Nat} {C : Cut α}
    (hr : HasRank vertices E T v r) (hc : RankCut vertices E T v r C) :
    Minimum vertices E T v C :=
  ⟨hc.1, fun D hD => hc.2 ▸ hr.lower D hD⟩

theorem rankcut_union_inter {vertices : List α} {E : α → α → Prop}
    {T : α → Prop} {v : α} {r : Nat} {C D : Cut α}
    (hr : HasRank vertices E T v r)
    (hc : RankCut vertices E T v r C) (hd : RankCut vertices E T v r D) :
    RankCut vertices E T v r (union C D) ∧
    RankCut vertices E T v r (inter C D) := by
  have hu := valid_union hc.1 hd.1
  have hi := valid_inter hc.1 hd.1
  have hru := hr.lower _ hu
  have hri := hr.lower _ hi
  have hm := size_modular vertices C D
  have ec := hc.2
  have ed := hd.2
  exact ⟨⟨hu, by omega⟩, ⟨hi, by omega⟩⟩

theorem nonessential_left {vertices : List α} {E : α → α → Prop}
    {T : α → Prop} {v t : α} {r : Nat} {C : Cut α}
    (ht : T t) (hc : RankCut vertices E T v r C)
    (hn : ¬CutEssential vertices E T v r t) : C t = left := by
  have hright := hc.1.terminals t ht
  have hsep : C t ≠ sep := fun hs => hn ⟨C, hc, hs⟩
  cases h : C t with
  | left => rfl
  | sep => exact False.elim (hsep h)
  | right => exact False.elim (hright h)

theorem critical_forces_rank_drop {vertices : List α} {E : α → α → Prop}
    {T : α → Prop} {v t p q : α} {r s : Nat}
    (hs : HasRank vertices (DeleteEdge E p q) T v s)
    (he : CutEssential vertices E T v r t)
    (hn : ¬CutEssential vertices (DeleteEdge E p q) T v s t) : s < r := by
  obtain ⟨C, hc, hct⟩ := he
  have hd := valid_delete (p := p) (q := q) hc.1
  have hle := hs.lower C hd
  have hne : s ≠ r := by
    intro h
    apply hn
    exact ⟨C, ⟨hd, hc.2.trans h.symm⟩, hct⟩
  have heq := hc.2
  omega

/-- Cut version of Lemma 4.13, with existence of the two minimum ranks explicit. -/
theorem secondary_not_critical {vertices : List α} {E : α → α → Prop}
    {T : α → Prop} {v p q t : α} {r s : Nat}
    (hr : HasRank vertices E T v r)
    (hs : HasRank vertices (DeleteEdge E p q) T v s)
    (ht : T t) (hp : E p t) (hqt : q ≠ t)
    (he : CutEssential vertices E T v r t) :
    CutEssential vertices (DeleteEdge E p q) T v s t := by
  classical
  by_cases h : CutEssential vertices (DeleteEdge E p q) T v s t
  · exact h
  · have drop := critical_forces_rank_drop hs he h
    obtain ⟨C, hc⟩ := hs.witness
    have invalid : ¬Valid E T v C := by
      intro hv
      have lower := hr.lower C hv
      have eq := hc.2
      omega
    have crosses := invalid_restore_crosses hc.1 invalid
    have edge : DeleteEdge E p q p t := by
      refine ⟨hp, ?_⟩
      intro hpair
      exact hqt hpair.2.symm
    have nl := hc.1.no_cross p t edge crosses.1
    have nr := hc.1.terminals t ht
    have ns := nonessential_left ht hc h
    exact False.elim (nl ns)

/-- The cut-uncrossing core of Lemma 4.14. This is a conditional theorem,
not by itself the complete criticality-transfer lemma: the common rank of
the double-deletion graph is established subsequently in `RankBridge.lean`. -/
theorem rank_pattern_impossible
    {vertices : List α} {E : α → α → Prop} {T : α → Prop}
    {v p q p' q' t u : α} {r : Nat}
    (original : HasRank vertices E T v (r + 1))
    (common : HasRank vertices (DeleteEdge (DeleteEdge E p q) p' q') T v r)
    (ht : T t) (hu : T u)
    (u_essential : CutEssential vertices (DeleteEdge E p q) T v r u)
    (t_not : ¬CutEssential vertices (DeleteEdge E p q) T v r t)
    (t_essential : CutEssential vertices (DeleteEdge E p' q') T v r t)
    (u_not : ¬CutEssential vertices (DeleteEdge E p' q') T v r u) : False := by
  classical
  obtain ⟨C, hc, hcu⟩ := u_essential
  obtain ⟨D, hd, hdt⟩ := t_essential
  have hct : C t = left := nonessential_left ht hc t_not
  have hdu : D u = left := nonessential_left hu hd u_not
  have hch : RankCut vertices (DeleteEdge (DeleteEdge E p q) p' q') T v r C :=
    ⟨valid_delete hc.1, hc.2⟩
  have hdh : RankCut vertices (DeleteEdge (DeleteEdge E p q) p' q') T v r D := by
    refine ⟨⟨hd.1.source, hd.1.terminals, ?_⟩, hd.2⟩
    intro x y he
    exact hd.1.no_cross x y ⟨he.1.1, he.2⟩
  obtain ⟨hUnion, hInter⟩ := rankcut_union_inter common hch hdh
  have hit : inter C D t = sep := by simp [inter, hct, hdt, Side.inter]
  have hiu : inter C D u = sep := by simp [inter, hcu, hdu, Side.inter]
  have inter_invalid_i : ¬Valid (DeleteEdge E p q) T v (inter C D) := by
    intro hv
    exact t_not ⟨inter C D, ⟨hv, hInter.2⟩, hit⟩
  have inter_invalid_j : ¬Valid (DeleteEdge E p' q') T v (inter C D) := by
    intro hv
    exact u_not ⟨inter C D, ⟨hv, hInter.2⟩, hiu⟩
  have cross_j := invalid_restore_crosses hInter.1 inter_invalid_i
  have swapped : Valid (DeleteEdge (DeleteEdge E p' q') p q) T v (inter C D) := by
    refine ⟨hInter.1.source, hInter.1.terminals, ?_⟩
    intro x y he
    exact hInter.1.no_cross x y ⟨⟨he.1.1, he.2⟩, he.1.2⟩
  have cross_i := invalid_restore_crosses swapped inter_invalid_j
  have q_in_D : D q = left := ((inter_left _ _).mp cross_i.2).2
  have q'_in_C : C q' = left := ((inter_left _ _).mp cross_j.2).1
  have C_invalid : ¬Valid E T v C := by
    intro h
    have l := original.lower C h
    have eq := hc.2
    omega
  have D_invalid : ¬Valid E T v D := by
    intro h
    have l := original.lower D h
    have eq := hd.2
    omega
  have cp := invalid_restore_crosses hc.1 C_invalid
  have dp := invalid_restore_crosses hd.1 D_invalid
  -- Both missing edges must actually belong to the original graph.
  have epq : E p q := by
    by_cases h : E p q
    · exact h
    · apply False.elim
      apply C_invalid
      refine ⟨hc.1.source, hc.1.terminals, ?_⟩
      intro x y he hx hy
      apply hc.1.no_cross x y ⟨he, ?_⟩ hx hy
      intro hpq
      obtain ⟨rfl, rfl⟩ := hpq
      exact h he
  have ep'q' : E p' q' := by
    by_cases h : E p' q'
    · exact h
    · apply False.elim
      apply D_invalid
      refine ⟨hd.1.source, hd.1.terminals, ?_⟩
      intro x y he hx hy
      apply hd.1.no_cross x y ⟨he, ?_⟩ hx hy
      intro hpq
      obtain ⟨rfl, rfl⟩ := hpq
      exact h he
  have distinct : ¬(p = p' ∧ q = q') := by
    intro h
    obtain ⟨rfl, rfl⟩ := h
    exact t_not ⟨D, hd, hdt⟩
  have pd_not_right : D p ≠ right := by
    intro h
    exact hd.1.no_cross p q ⟨epq, distinct⟩ h q_in_D
  have pc_not_right : C p' ≠ right := by
    intro h
    have rev : ¬(p' = p ∧ q' = q) := fun h => distinct ⟨h.1.symm, h.2.symm⟩
    exact hc.1.no_cross p' q' ⟨ep'q', rev⟩ h q'_in_C
  have safe_i : ¬(union C D p = right ∧ union C D q = left) := by
    intro h
    exact pd_not_right ((union_right _ _).mp h.1).2
  have safe_j : ¬(union C D p' = right ∧ union C D q' = left) := by
    intro h
    exact pc_not_right ((union_right _ _).mp h.1).1
  have restored_i := valid_restore hUnion.1 safe_j
  have restored := valid_restore restored_i safe_i
  have lower := original.lower (union C D) restored
  have eq := hUnion.2
  omega

end GyoriLovasz
