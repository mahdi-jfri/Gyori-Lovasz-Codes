import GyoriLovasz.Counting

namespace GyoriLovasz
open Side
variable {α β : Type}

theorem size_map (xs : List β) (e : β → α) (C : Cut α) :
    size (xs.map e) C = size xs (fun x => C (e x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [size, ih]

theorem size_perm {xs ys : List α} (perm : xs.Perm ys) (C : Cut α) :
    size xs C = size ys C := by
  rw [size_eq_countTrue, size_eq_countTrue]
  exact countTrue_perm perm _

theorem hasRank_unique {vertices : List α} {E : α → α → Prop}
    {T : α → Prop} {v : α} {r s : Nat}
    (hr : HasRank vertices E T v r) (hs : HasRank vertices E T v s) : r = s := by
  obtain ⟨C, hc⟩ := hr.witness
  obtain ⟨D, hd⟩ := hs.witness
  have h1 := hr.lower D hd.1
  have h2 := hs.lower C hc.1
  have h3 := hc.2
  have h4 := hd.2
  omega

/-- Data for reindexing an active graph. Vertices outside `vertices` have no
incident edges and are not terminals. This is the interface needed after an
erasure, when the smaller graph is represented on a new finite type. -/
structure GraphReindex (vertices : List α) (xs : List β)
    (E : α → α → Prop) (T : α → Prop) (e : β → α) (r : α → β) : Prop where
  complete : ∀ x, x ∈ xs
  inverse : ∀ x, r (e x) = x
  retract : ∀ x, x ∈ vertices → e (r x) = x
  enumeration : (xs.map e).Perm vertices
  edges : ∀ x y, E x y → x ∈ vertices ∧ y ∈ vertices
  terminals : ∀ x, T x → x ∈ vertices

theorem GraphReindex.image_mem {vertices : List α} {xs : List β}
    {E : α → α → Prop} {T : α → Prop} {e : β → α} {r : α → β}
    (h : GraphReindex vertices xs E T e r) (x : β) : e x ∈ vertices :=
  (h.enumeration.mem_iff).mp (List.mem_map.mpr ⟨x, h.complete x, rfl⟩)

noncomputable def extendCut (vertices : List α) (r : α → β) (D : Cut β) : Cut α := by
  classical
  exact fun x => if x ∈ vertices then D (r x) else left

theorem GraphReindex.extend_valid {vertices : List α} {xs : List β}
    {E : α → α → Prop} {T : α → Prop} {e : β → α} {r : α → β}
    (h : GraphReindex vertices xs E T e r) {v : β} {D : Cut β}
    (hd : Valid (fun x y => E (e x) (e y)) (fun x => T (e x)) v D) :
    Valid E T (e v) (extendCut vertices r D) := by
  classical
  refine ⟨by simp [extendCut, h.image_mem v, h.inverse, hd.source], ?_, ?_⟩
  · intro t ht
    have hmem := h.terminals t ht
    have tr : T (e (r t)) := (h.retract t hmem).symm ▸ ht
    simpa [extendCut, hmem] using hd.terminals (r t) tr
  · intro x y edge hx hy
    obtain ⟨xm, ym⟩ := h.edges x y edge
    have he : E (e (r x)) (e (r y)) := by rw [h.retract x xm, h.retract y ym]; exact edge
    exact hd.no_cross (r x) (r y) he
      (by simpa [extendCut, xm] using hx) (by simpa [extendCut, ym] using hy)

theorem GraphReindex.extend_size {vertices : List α} {xs : List β}
    {E : α → α → Prop} {T : α → Prop} {e : β → α} {r : α → β}
    (h : GraphReindex vertices xs E T e r) (D : Cut β) :
    size vertices (extendCut vertices r D) = size xs D := by
  classical
  rw [← size_perm h.enumeration, size_map]
  have he : (fun x => extendCut vertices r D (e x)) = D := by
    funext x
    simp [extendCut, h.image_mem x, h.inverse]
  rw [he]

theorem GraphReindex.rank {vertices : List α} {xs : List β}
    {E : α → α → Prop} {T : α → Prop} {e : β → α} {r : α → β}
    (h : GraphReindex vertices xs E T e r) {v : β} {rank : Nat}
    (hr : HasRank vertices E T (e v) rank) :
    HasRank xs (fun x y => E (e x) (e y)) (fun x => T (e x)) v rank := by
  obtain ⟨C, hc⟩ := hr.witness
  refine ⟨⟨fun x => C (e x), ⟨hc.1.source,
    fun x hx => hc.1.terminals (e x) hx,
    fun x y he => hc.1.no_cross (e x) (e y) he⟩, ?_⟩, ?_⟩
  · rw [← size_map, size_perm h.enumeration]
    exact hc.2
  · intro D hd
    have lower := hr.lower _ (h.extend_valid hd)
    rw [h.extend_size] at lower
    exact lower

theorem GraphReindex.essential {vertices : List α} {xs : List β}
    {E : α → α → Prop} {T : α → Prop} {e : β → α} {r : α → β}
    (h : GraphReindex vertices xs E T e r) {v t : β} {rank : Nat}
    (essential : CutEssential vertices E T (e v) rank (e t)) :
    CutEssential xs (fun x y => E (e x) (e y)) (fun x => T (e x)) v rank t := by
  obtain ⟨C, hc, ht⟩ := essential
  refine ⟨fun x => C (e x), ⟨⟨hc.1.source,
    fun x hx => hc.1.terminals (e x) hx,
    fun x y he => hc.1.no_cross (e x) (e y) he⟩, ?_⟩, ht⟩
  rw [← size_map, size_perm h.enumeration]
  exact hc.2

end GyoriLovasz


