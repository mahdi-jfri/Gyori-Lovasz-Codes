import GyoriLovasz.Counting

namespace GyoriLovasz

/-- A finite functional graph has a nonempty invariant subset on which the
function is a permutation. One or more cycles suffice for reassignment. -/
theorem exists_invariant_permutation (vertices : List α) (f : α → α)
    (hu : vertices.Nodup) (hne : vertices ≠ [])
    (closed : ∀ x, x ∈ vertices → f x ∈ vertices) :
    ∃ xs : List α, xs ≠ [] ∧ xs.Nodup ∧
      (∀ x, x ∈ xs → x ∈ vertices) ∧ (xs.map f).Perm xs := by
  classical
  let Good := fun xs : List α => xs ≠ [] ∧ xs.Nodup ∧
    (∀ x, x ∈ xs → x ∈ vertices) ∧ (∀ x, x ∈ xs → f x ∈ xs)
  have ex : ∃ m, ∃ xs, Good xs ∧ xs.length = m :=
    ⟨vertices.length, vertices, ⟨hne, hu, fun _ hx => hx, closed⟩, rfl⟩
  obtain ⟨m, ⟨xs, hxs, hm⟩, minimal⟩ := exists_minimal_nat _ ex
  let ys := xs.filter (fun y => decide (∃ x, x ∈ xs ∧ f x = y))
  have memys (y : α) : y ∈ ys ↔ y ∈ xs ∧ ∃ x, x ∈ xs ∧ f x = y := by
    simp [ys]
  have hys : Good ys := by
    refine ⟨?_, List.Pairwise.filter _ hxs.2.1, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil xs hxs.1
      have hf := (memys (f x)).mpr ⟨hxs.2.2.2 x hx, x, hx, rfl⟩
      exact List.ne_nil_of_mem hf
    · intro x hx
      exact hxs.2.2.1 x ((memys x).mp hx).1
    · intro y hy
      have hyx := ((memys y).mp hy).1
      exact (memys (f y)).mpr ⟨hxs.2.2.2 y hyx, y, hyx, rfl⟩
  have lower := minimal ys.length ⟨ys, hys, rfl⟩
  have same : ys = xs := List.Sublist.eq_of_length_le (List.filter_sublist) (by omega)
  have hsurj : ∀ y, y ∈ xs → y ∈ xs.map f := by
    intro y hy
    have hy' : y ∈ ys := same.symm ▸ hy
    obtain ⟨x, hx, he⟩ := ((memys y).mp hy').2
    exact List.mem_map.mpr ⟨x, hx, he⟩
  have perm : xs.Perm (xs.map f) :=
    nodup_subset_perm_of_length hxs.2.1 hsurj (by simp)
  exact ⟨xs, hxs.1, hxs.2.1, hxs.2.2.1, perm.symm⟩

theorem exists_terminal_cycles (f : Fin k → Fin k) (hk : 0 < k) :
    ∃ xs : List (Fin k), xs ≠ [] ∧ xs.Nodup ∧ (xs.map f).Perm xs := by
  obtain ⟨xs, hne, hnd, _, hp⟩ := exists_invariant_permutation (List.finRange k) f
    (finRange_nodup k) (by intro h; have hl := congrArg List.length h; simp at hl; omega)
    (fun x _ => mem_finRange (f x))
  exact ⟨xs, hne, hnd, hp⟩

noncomputable def reassign (selected : List α) (vertex : α → β)
    (old : β → α) (v : β) : α := by
  classical
  exact if h : ∃ t, t ∈ selected ∧ vertex t = v then Classical.choose h else old v

theorem reassign_selected {selected : List α} {vertex : α → β} {old : β → α}
    (hinj : ∀ a, a ∈ selected → ∀ b, b ∈ selected → vertex a = vertex b → a = b)
    {t : α} (ht : t ∈ selected) : reassign selected vertex old (vertex t) = t := by
  classical
  have h : ∃ u, u ∈ selected ∧ vertex u = vertex t := ⟨t, ht, rfl⟩
  simp only [reassign, dif_pos h]
  have hc := Classical.choose_spec h
  exact hinj _ hc.1 t ht hc.2

theorem reassign_unchanged {selected : List α} {vertex : α → β} {old : β → α}
    {v : β} (hv : v ∉ selected.map vertex) : reassign selected vertex old v = old v := by
  classical
  have h : ¬∃ t, t ∈ selected ∧ vertex t = v := by
    rintro ⟨t, ht, he⟩
    exact hv (List.mem_map.mpr ⟨t, ht, he⟩)
  simp [reassign, h]

/-- Reassigning distinct selected vertices preserves every capacity when
their old terminal labels are a permutation of their new labels. -/
theorem reassignment_preserves_counts (vertices : List β) (selected : List α)
    (vertex : α → β) (old : β → α)
    (hu : vertices.Nodup) (hs : selected.Nodup)
    (hm : ∀ t, t ∈ selected → vertex t ∈ vertices)
    (perm : (selected.map (fun t => old (vertex t))).Perm selected)
    (target : α) :
    countTrue vertices (fun v => reassign selected vertex old v = target) =
      countTrue vertices (fun v => old v = target) := by
  classical
  have hnmap : (selected.map (fun t => old (vertex t))).Nodup := perm.symm.nodup hs
  have hinj : ∀ a, a ∈ selected → ∀ b, b ∈ selected → vertex a = vertex b → a = b := by
    intro a ha b hb he
    exact map_nodup_injOn hnmap ha hb (congrArg old he)
  have hmnd : (selected.map vertex).Nodup := by
    apply List.pairwise_map.mpr
    have hp := List.pairwise_map.mp hnmap
    exact List.Pairwise.imp (fun hne he => hne (congrArg old he)) hp
  let touched := vertices.filter (fun v => decide (v ∈ selected.map vertex))
  let rest := vertices.filter (fun v => !decide (v ∈ selected.map vertex))
  have htperm : touched.Perm (selected.map vertex) := by
    apply nodup_perm_of_same_mem (List.Pairwise.filter _ hu) hmnd
    intro v
    simp only [touched, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro h
      obtain ⟨t, ht, he⟩ := List.mem_map.mp h
      exact ⟨he ▸ hm t ht, h⟩
  have split : (touched ++ rest).Perm vertices := List.filter_append_perm _ _
  have hrest : countTrue rest (fun v => reassign selected vertex old v = target) =
      countTrue rest (fun v => old v = target) := by
    apply countTrue_congr
    intro v hv
    have hn : v ∉ selected.map vertex := by simpa [rest] using (List.mem_filter.mp hv).2
    rw [reassign_unchanged hn]
  have htouched : countTrue touched (fun v => reassign selected vertex old v = target) =
      countTrue touched (fun v => old v = target) := by
    rw [countTrue_perm htperm, countTrue_perm htperm, countTrue_map, countTrue_map]
    have hnew : countTrue selected (fun t => reassign selected vertex old (vertex t) = target) =
        countTrue selected (fun t => t = target) := by
      apply countTrue_congr
      intro t ht
      rw [reassign_selected hinj ht]
    rw [hnew]
    exact (countTrue_perm perm (fun t => t = target)).symm.trans (countTrue_map _ _ _)
  rw [← countTrue_perm split, ← countTrue_perm split, countTrue_append, countTrue_append,
    hrest, htouched]

end GyoriLovasz
