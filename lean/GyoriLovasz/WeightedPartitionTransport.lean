import GyoriLovasz.WeightedTransport
import GyoriLovasz.WeightedReconstruction

namespace GyoriLovasz
open scoped BigOperators

theorem weighted_partition_reindex {vertices : List (Fin n)} {E : Fin n → Fin n → Prop}
    {T : Fin n → Prop} {roots : Fin k → Fin n} {weight : Fin n → Nat} {limit : Fin k → Nat}
    {e : Fin m → Fin n} {r : Fin n → Fin m} {d : Fin l → Fin k}
    (h : GraphReindex vertices (List.finRange m) E T e r)
    (dinj : Function.Injective d) (rootmem : ∀ j, roots (d j) ∈ vertices)
    {label : Fin m → Fin l}
    (part : WeightedPartitionOn Finset.univ Finset.univ (fun x y => E (e x) (e y))
      (fun j => r (roots (d j))) (fun x => weight (e x)) (fun j => limit (d j)) label) :
    WeightedPartitionOn vertices.toFinset (Finset.univ.image d) E roots weight limit
      (fun x => d (label (r x))) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _
    exact Finset.mem_image.mpr ⟨label (r x), Finset.mem_univ _, rfl⟩
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨List.mem_toFinset.mpr (rootmem j), congrArg d (part.2.1 j (Finset.mem_univ _)).2⟩
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    have cnt := h.sum_filter (fun _ => True)
      (fun x => if d (label (r x)) = d j then weight x else 0)
    simp only [Finset.filter_True] at cnt
    have same : (∑ x : Fin m, if d (label (r (e x))) = d j then weight (e x) else 0) =
        partLoad Finset.univ (fun x => weight (e x)) label j := by
      apply Finset.sum_congr rfl
      intro x _
      rw [h.inverse x]
      simp only [dinj.eq_iff]
    change (∑ x ∈ vertices.toFinset, if d (label (r x)) = d j then weight x else 0) ≤ _
    rw [← cnt, same]
    exact part.2.2.1 j (Finset.mem_univ _)
  · intro i hi x hx hl
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    have path := (part.2.2.2 j (Finset.mem_univ _) (r x) (Finset.mem_univ _) (dinj hl)).map e
      (fun _ _ he => he) (B := fun y => y ∈ vertices.toFinset ∧ d (label (r y)) = d j)
      (fun y hy => ⟨List.mem_toFinset.mpr (h.image_mem y), by rw [h.inverse y, hy.2]⟩)
    rw [h.retract x (List.mem_toFinset.mp hx), h.retract (roots (d j)) (rootmem j)] at path
    exact path

end GyoriLovasz
