import GyoriLovasz.WeightedRoundedParts
import GyoriLovasz.WeightedReconstruction

namespace GyoriLovasz
open scoped BigOperators

theorem weighted_rounded_partition {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {weight : Fin n → Nat} {capacity : Fin k → Nat} {bound : Nat}
    (hinj : Function.Injective roots) (rootzero : ∀ i, weight (roots i) = 0)
    (S : Finset (Fin k)) (N : Finset (Fin n)) (f : Fin n → Fin k)
    (injective : Set.InjOn f N) (targets : ∀ p ∈ N, f p ∈ S)
    (edges : ∀ p ∈ N, E p (roots (f p))) (nonterminal : ∀ p ∈ N, ¬RootSet roots p)
    (positive : ∀ i ∈ S, 0 < capacity i) (upper : ∀ p ∈ N, weight p ≤ bound) :
    ∃ label, WeightedPartitionOn (S.image roots ∪ N) S E roots weight
      (fun i => capacity i + bound - 1) label := by
  classical
  let label := fun x => if ht : RootSet roots x then Classical.choose ht else f x
  have rootlabel (i : Fin k) : label (roots i) = i := by
    have ht : RootSet roots (roots i) := ⟨i, rfl⟩
    simp only [label, dif_pos ht]
    exact hinj (Classical.choose_spec ht)
  have neighborlabel (x : Fin n) (hx : x ∈ N) : label x = f x := by
    simp [label, nonterminal x hx]
  have basic := rounded_parts_valid S N f injective edges nonterminal positive upper
  refine ⟨label, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with root | neighbor
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp root
      rw [rootlabel]
      exact hj
    · rw [neighborlabel x neighbor]
      exact targets x neighbor
  · intro i hi
    exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩), rootlabel i⟩
  · intro i hi
    have sumN : partLoad (S.image roots ∪ N) weight label i =
        ∑ x ∈ N, if label x = i then weight x else 0 := by
      unfold partLoad
      apply Finset.sum_union_eq_right
      intro x hx _
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      simp [rootzero]
    rw [sumN]
    have same : (∑ x ∈ N, if label x = i then weight x else 0) =
        ∑ x ∈ N.filter (fun x => f x = i), weight x := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      rw [neighborlabel x hx]
    rw [same]
    exact (basic i hi).1
  · intro i hi x hx hl
    have shape : x = roots i ∨ (x ∈ N ∧ f x = i) := by
      rcases Finset.mem_union.mp hx with root | neighbor
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp root
        have ji := (rootlabel j).symm.trans hl
        exact Or.inl (congrArg roots ji)
      · exact Or.inr ⟨neighbor, (neighborlabel x neighbor).symm.trans hl⟩
    exact ((basic i hi).2.1 x shape).mono_allowed (fun y hy => by
      rcases hy with he | neighbor
      · subst y
        exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩), rootlabel i⟩
      · exact ⟨Finset.mem_union_right _ neighbor.1, (neighborlabel y neighbor.1).trans neighbor.2⟩)

end GyoriLovasz
