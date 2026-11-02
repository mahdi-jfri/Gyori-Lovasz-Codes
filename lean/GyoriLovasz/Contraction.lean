import GyoriLovasz.Counting

namespace GyoriLovasz
open Side

noncomputable def putSide (C : Cut α) (p : α) (s : Side) : Cut α := by
  classical
  exact fun x => if x = p then s else C x

theorem size_putSide_absent {vertices : List α} {C : Cut α} {p : α} {s : Side}
    (h : p ∉ vertices) : size vertices (putSide C p s) = size vertices C := by
  classical
  induction vertices with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ p := by intro he; subst x; exact h (by simp)
    have ht : p ∉ xs := fun hm => h (by simp [hm])
    simp only [size, putSide, if_neg hx]
    rw [ih ht]

theorem size_erase [DecidableEq α] {vertices : List α} {C : Cut α} {p : α}
    (hp : p ∈ vertices) : size vertices C = (C p).weight + size (vertices.erase p) C := by
  induction vertices with
  | nil => simp at hp
  | cons x xs ih =>
    by_cases he : x = p
    · subst x; simp [size]
    · have hmem : p ∈ xs := by simpa [he, Ne.symm he] using hp
      have hi := ih hmem
      simp [List.erase_cons, he, Ne.symm he, size]
      omega

def Contract (E : α → α → Prop) (p t : α) : α → α → Prop :=
  fun x y => x ≠ p ∧ y ≠ p ∧ (E x y ∨ (E x p ∧ y = t))

noncomputable def liftContractCut (D : Cut α) (p t : α) : Cut α := by
  classical
  exact putSide D p (if D t = sep then right else left)

theorem liftContractCut_valid {E : α → α → Prop} {T : α → Prop}
    {p t v : α} {D : Cut α} (hv : v ≠ p) (hp : ¬T p) (ht : T t)
    (only : ∀ y, E p y → y = t) (hd : Valid (Contract E p t) T v D) :
    Valid E T v (liftContractCut D p t) := by
  classical
  have htp : t ≠ p := fun h => hp (h ▸ ht)
  have hdt := hd.terminals t ht
  refine ⟨by simp [liftContractCut, putSide, hv, hd.source], ?_, ?_⟩
  · intro u hu
    have hup : u ≠ p := fun h => hp (h ▸ hu)
    simpa [liftContractCut, putSide, hup] using hd.terminals u hu
  · intro x y he hx hy
    by_cases hxp : x = p
    · subst x
      have hyt := only y he
      subst y
      by_cases hts : D t = sep
      · simp [liftContractCut, putSide, htp, hts] at hy
      · simp [liftContractCut, putSide, hts] at hx
    · have hxr : D x = right := by simpa [liftContractCut, putSide, hxp] using hx
      by_cases hyp : y = p
      · subst y
        have htl : D t = left := by
          cases hdval : D t with
          | left => rfl
          | sep => simp [liftContractCut, putSide, hdval] at hy
          | right => exact False.elim (hdt hdval)
        exact hd.no_cross x t ⟨hxp, htp, Or.inr ⟨he, rfl⟩⟩ hxr htl
      · have hyl : D y = left := by simpa [liftContractCut, putSide, hyp] using hy
        exact hd.no_cross x y ⟨hxp, hyp, Or.inl he⟩ hxr hyl

theorem liftContractCut_size [DecidableEq α] {vertices : List α} {D : Cut α} {p t : α}
    (hn : vertices.Nodup) (hp : p ∈ vertices) :
    size vertices (liftContractCut D p t) = size (vertices.erase p) D := by
  classical
  have erase_absent : p ∉ vertices.erase p := by
    exact List.Nodup.not_mem_erase hn
  have he := size_erase (C := liftContractCut D p t) hp
  have ha := size_putSide_absent (C := D)
    (s := if D t = sep then right else left) erase_absent
  have hw : (liftContractCut D p t p).weight = 0 := by
    by_cases h : D t = sep <;> simp [liftContractCut, putSide, h, Side.weight]
  change size (vertices.erase p) (liftContractCut D p t) = size (vertices.erase p) D at ha
  rw [hw, ha] at he
  simpa using he

noncomputable def descendContractCut (C : Cut α) (p t : α) : Cut α := by
  classical
  exact if C p = sep then putSep C t else C

theorem descendContractCut_valid {E : α → α → Prop} {T : α → Prop}
    {p t v : α} {C : Cut α} (ht : T t) (edge : E p t) (hc : Valid E T v C) :
    Valid (Contract E p t) T v (descendContractCut C p t) := by
  classical
  have vt : v ≠ t := by intro h; subst v; exact hc.terminals t ht hc.source
  by_cases hps : C p = sep
  · have aux : Valid (Contract E p t) T v (putSep C t) := by
      refine ⟨by simp [putSep, vt, hc.source], ?_, ?_⟩
      · intro u hu
        by_cases he : u = t
        · simp [putSep, he]
        · simpa [putSep, he] using hc.terminals u hu
      · intro x y he hx hy
        have hxt : x ≠ t := by intro h; subst x; simp [putSep] at hx
        have hyt : y ≠ t := by intro h; subst y; simp [putSep] at hy
        have hxr : C x = right := by simpa [putSep, hxt] using hx
        have hyl : C y = left := by simpa [putSep, hyt] using hy
        rcases he.2.2 with oldedge | redirect
        · exact hc.no_cross x y oldedge hxr hyl
        · exact hyt redirect.2
    simpa [descendContractCut, hps] using aux
  · have aux : Valid (Contract E p t) T v C := by
      refine ⟨hc.source, hc.terminals, ?_⟩
      intro x y he hx hy
      rcases he.2.2 with oldedge | redirect
      · exact hc.no_cross x y oldedge hx hy
      · obtain ⟨hxp, hyt⟩ := redirect
        rw [hyt] at hy
        have hpl := hc.no_cross x p hxp hx
        have hpr : C p = right := by
          cases hpval : C p with
          | left => exact False.elim (hpl hpval)
          | sep => exact False.elim (hps hpval)
          | right => rfl
        exact hc.no_cross p t edge hpr hy
    simpa [descendContractCut, hps] using aux

theorem descendContractCut_size [DecidableEq α] {vertices : List α} {C : Cut α} {p t : α}
    (hn : vertices.Nodup) (hp : p ∈ vertices) (ht : t ∈ vertices)
    (hpt : p ≠ t) (htr : C t ≠ right) :
    size (vertices.erase p) (descendContractCut C p t) ≤ size vertices C := by
  classical
  have he := size_erase (C := C) hp
  by_cases hps : C p = sep
  · have hte : t ∈ vertices.erase p := (List.mem_erase_of_ne hpt.symm).mpr ht
    have hne : (vertices.erase p).Nodup := hn.sublist List.erase_sublist
    cases htv : C t with
    | right => exact False.elim (htr htv)
    | left =>
      have hs := size_putSep hne hte htv
      simp only [hps, Side.weight] at he
      simp only [descendContractCut, if_pos hps]
      omega
    | sep =>
      have hs : putSep C t = C := by
        funext x
        by_cases hxt : x = t
        · simp [putSep, hxt, htv]
        · simp [putSep, hxt]
      simp only [descendContractCut, if_pos hps, hs]
      omega
  · simp only [descendContractCut, if_neg hps]
    omega

/-- Contraction of a vertex with its only outgoing edge to a terminal preserves
minimum rank and every other terminal's cut-essentiality. The active vertex
list loses `p`, so this result supports an induction on vertex count. -/
theorem contraction_preserves_essential [DecidableEq α]
    {vertices : List α} {E : α → α → Prop} {T : α → Prop}
    {v p t u : α} {r s : Nat}
    (hn : vertices.Nodup) (hp_mem : p ∈ vertices) (ht_mem : t ∈ vertices)
    (hv : v ≠ p) (hp : ¬T p) (ht : T t) (_hu : T u)
    (edge : E p t) (only : ∀ y, E p y → y = t)
    (hr : HasRank vertices E T v r)
    (hs : HasRank (vertices.erase p) (Contract E p t) T v s)
    (essential : CutEssential vertices E T v r u) :
    s = r ∧ CutEssential (vertices.erase p) (Contract E p t) T v s u := by
  classical
  have hpt : p ≠ t := fun h => hp (h.symm ▸ ht)
  obtain ⟨D, hd⟩ := hs.witness
  have liftvalid := liftContractCut_valid hv hp ht only hd.1
  have liftsize := liftContractCut_size (D := D) (t := t) hn hp_mem
  have rle := hr.lower _ liftvalid
  have hds := hd.2
  have rs : r ≤ s := by omega
  obtain ⟨C, hc, hcu⟩ := essential
  have descendvalid := descendContractCut_valid ht edge hc.1
  have descendsize := descendContractCut_size hn hp_mem ht_mem hpt (hc.1.terminals t ht)
  have sle := hs.lower _ descendvalid
  have hcs := hc.2
  have sr : s = r := by omega
  refine ⟨sr, descendContractCut C p t, ⟨descendvalid, by omega⟩, ?_⟩
  by_cases hps : C p = sep
  · by_cases hut : u = t
    · simp [descendContractCut, hps, putSep, hut]
    · simp [descendContractCut, hps, putSep, hut, hcu]
  · simp [descendContractCut, hps, hcu]

end GyoriLovasz
