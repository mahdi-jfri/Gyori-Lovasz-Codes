import GyoriLovasz.Contraction

namespace GyoriLovasz
open Side

def DeleteVertex (E : α → α → Prop) (t : α) : α → α → Prop :=
  fun x y => E x y ∧ x ≠ t ∧ y ≠ t

def WithoutTerminal (T : α → Prop) (t : α) : α → Prop := fun x => T x ∧ x ≠ t

theorem valid_remove_terminal {E : α → α → Prop} {T : α → Prop}
    {v t : α} {C : Cut α} (hc : Valid E T v C) :
    Valid (DeleteVertex E t) (WithoutTerminal T t) v C :=
  ⟨hc.source, fun u hu => hc.terminals u hu.1,
    fun x y he => hc.no_cross x y he.1⟩

theorem valid_add_terminal {E : α → α → Prop} {T : α → Prop}
    {v t : α} {D : Cut α} (hvt : v ≠ t)
    (hd : Valid (DeleteVertex E t) (WithoutTerminal T t) v D) :
    Valid E T v (putSide D t sep) := by
  classical
  refine ⟨by simp [putSide, hvt, hd.source], ?_, ?_⟩
  · intro u hu
    by_cases hut : u = t
    · simp [putSide, hut]
    · simpa [putSide, hut] using hd.terminals u ⟨hu, hut⟩
  · intro x y he hx hy
    have hxt : x ≠ t := by intro h; subst x; simp [putSide] at hx
    have hyt : y ≠ t := by intro h; subst y; simp [putSide] at hy
    have hxr : D x = right := by simpa [putSide, hxt] using hx
    have hyl : D y = left := by simpa [putSide, hyt] using hy
    exact hd.no_cross x y ⟨he, hxt, hyt⟩ hxr hyl

theorem size_add_terminal [DecidableEq α] {vertices : List α} {D : Cut α} {t : α}
    (hn : vertices.Nodup) (ht : t ∈ vertices) :
    size vertices (putSide D t sep) = 1 + size (vertices.erase t) D := by
  classical
  have he := size_erase (C := putSide D t sep) ht
  have ha := size_putSide_absent (C := D) (p := t) (s := sep) (List.Nodup.not_mem_erase hn)
  have hw : (putSide D t sep t).weight = 1 := by simp [putSide, Side.weight]
  rw [hw, ha] at he
  exact he

theorem inter_terminal_sep {E : α → α → Prop} {T : α → Prop}
    {v t : α} {C D : Cut α} (hc : Valid E T v C) (ht : T t) (hd : D t = sep) :
    inter C D t = sep := by
  have nr := hc.terminals t ht
  cases h : C t with
  | left => simp [inter, h, hd, Side.inter]
  | sep => simp [inter, h, hd, Side.inter]
  | right => exact False.elim (nr h)

/-- Cut-based version of essentiality preservation under removal of another
terminal. The removed vertex is erased from the active vertex list. -/
theorem terminal_removal_preserves_essential [DecidableEq α]
    {vertices : List α} {E : α → α → Prop} {T : α → Prop}
    {v t u : α} {r s : Nat}
    (hn : vertices.Nodup) (ht_mem : t ∈ vertices)
    (hvt : v ≠ t) (ht : T t) (hu : T u) (_hut : u ≠ t)
    (hr : HasRank vertices E T v r)
    (hs : HasRank (vertices.erase t) (DeleteVertex E t) (WithoutTerminal T t) v s)
    (essential_u : CutEssential vertices E T v r u) :
    CutEssential (vertices.erase t) (DeleteVertex E t) (WithoutTerminal T t) v s u := by
  classical
  obtain ⟨D, hd⟩ := hs.witness
  have liftvalid := valid_add_terminal hvt hd.1
  have liftsize := size_add_terminal (D := D) hn ht_mem
  have lower := hr.lower _ liftvalid
  have hds := hd.2
  have bound : r ≤ s + 1 := by omega
  obtain ⟨C, hc, hcu⟩ := essential_u
  by_cases essential_t : CutEssential vertices E T v r t
  · obtain ⟨B, hb, hbt⟩ := essential_t
    obtain ⟨_, hi⟩ := rankcut_union_inter hr hc hb
    have hit : inter C B t = sep := inter_terminal_sep hc.1 ht hbt
    have hiu : inter C B u = sep := by
      have nr := hb.1.terminals u hu
      cases hv : B u with
      | left => simp [inter, hcu, hv, Side.inter]
      | sep => simp [inter, hcu, hv, Side.inter]
      | right => exact False.elim (nr hv)
    have removed := valid_remove_terminal (t := t) hi.1
    have sz := size_erase (C := inter C B) ht_mem
    simp only [hit, Side.weight] at sz
    have hmin := hs.lower _ removed
    have his := hi.2
    exact ⟨inter C B, ⟨removed, by omega⟩, hiu⟩
  · have no_drop : r ≤ s := by
      by_cases h : r ≤ s
      · exact h
      · have heq : size vertices (putSide D t sep) = r := by omega
        apply False.elim
        apply essential_t
        exact ⟨putSide D t sep, ⟨liftvalid, heq⟩, by simp [putSide]⟩
    have hct : C t ≠ sep := fun he => essential_t ⟨C, hc, he⟩
    have hw : (C t).weight = 0 := by
      cases h : C t with
      | left => rfl
      | sep => exact False.elim (hct h)
      | right => rfl
    have sz := size_erase (C := C) ht_mem
    rw [hw] at sz
    have removed := valid_remove_terminal (t := t) hc.1
    have hmin := hs.lower _ removed
    have hcs := hc.2
    exact ⟨C, ⟨removed, by omega⟩, hcu⟩

end GyoriLovasz
