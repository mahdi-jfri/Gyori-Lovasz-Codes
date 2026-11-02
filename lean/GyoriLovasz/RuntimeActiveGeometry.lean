import GyoriLovasz.RuntimeReindex
import GyoriLovasz.RuntimeRoundBlock
import GyoriLovasz.WeightedAssembly

namespace GyoriLovasz.ComputedReindex

theorem active_mem (selected : Vector Bool n) (v : Fin n) :
    v ∈ (active selected).1.2.toList ↔ selected[v.val] = true := by
  simp only [active_list, retain_value, List.mem_filter, List.mem_finRange, true_and]

theorem active_injective (selected : Vector Bool n) :
    Function.Injective (fun j : Fin (active selected).1.1 => (active selected).1.2[j.val]) := by
  have hn := retain_nodup selected
  rw [← active_list, ← enumeration, ← List.ofFn_eq_map, List.nodup_ofFn] at hn
  exact hn

theorem active_size_le (selected : Vector Bool n) : (active selected).1.1 ≤ n := by
  change (retain selected).1.length ≤ n
  rw [retain_value]
  exact (List.length_filter_le _ _).trans_eq List.length_finRange

theorem active_positive (selected : Vector Bool n) (h : ∃ v : Fin n, selected[v.val] = true) :
    0 < (active selected).1.1 := by
  obtain ⟨v, hv⟩ := h
  have mem := (active_mem selected v).mpr hv
  have len := List.length_pos_of_mem mem
  simpa using len

theorem active_size_lt (selected : Vector Bool n) (h : ∃ v : Fin n, selected[v.val] = false) :
    (active selected).1.1 < n := by
  obtain ⟨v, hv⟩ := h
  have hn := retain_nodup selected
  have card : (active selected).1.1 = (Finset.univ.filter (fun v : Fin n => selected[v.val] = true)).card := by
    change (retain selected).1.length = _
    rw [← List.toFinset_card_of_nodup hn]
    congr 1
    ext x
    simp [retain_value]
  rw [card]
  have proper : Finset.univ.filter (fun v : Fin n => selected[v.val] = true) ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro eq
    have mem : v ∈ Finset.univ.filter (fun v : Fin n => selected[v.val] = true) := eq.symm ▸ Finset.mem_univ v
    simp [hv] at mem
  simpa using Finset.card_lt_card proper

theorem active_complement_list (removed : Vector Bool n) :
    (active (complementMask removed).1).1.2.toList =
      GyoriLovasz.retain (List.finRange n) (SaturationPrune.selectedSet removed) := by
  rw [active_list, retain_value]
  unfold GyoriLovasz.retain
  apply List.filter_congr
  intro v _
  apply Bool.eq_iff_iff.mpr
  simp only [complementMask_correct, decide_eq_true_eq, SaturationPrune.mem_selectedSet]

theorem active_graph (selected : Vector Bool n) (positive : 0 < (active selected).1.1)
    (E : Fin n → Fin n → Prop) (T : Fin n → Prop)
    (edges : ∀ x y, E x y → selected[x.val] = true ∧ selected[y.val] = true)
    (terminals : ∀ x, T x → selected[x.val] = true) :
    GraphReindex (active selected).1.2.toList (List.finRange (active selected).1.1) E T
      (fun j => (active selected).1.2[j.val])
      (fun v => (inverse (active selected).1.2 ⟨0, positive⟩).1[v.val]) := by
  apply graphReindex (active selected).1.2 ⟨0, positive⟩ (active_injective selected) E T
  · intro x y he
    exact ⟨(active_mem selected x).mpr (edges x y he).1, (active_mem selected y).mpr (edges x y he).2⟩
  · intro x hx
    exact (active_mem selected x).mpr (terminals x hx)

end GyoriLovasz.ComputedReindex
