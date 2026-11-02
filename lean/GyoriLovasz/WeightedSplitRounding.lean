import GyoriLovasz.WeightedHall
import GyoriLovasz.WeightedRemove
import GyoriLovasz.Weighted
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace GyoriLovasz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The original matrix, restricted after rounding, preserves every surviving
row supply, respects capacities, and is supported on essential surviving roots.
The graph is still represented on the old vertex type with a smaller active list. -/
theorem rounding_split_restriction {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {weight : Fin n → Nat} {capacity : Fin k → Nat}
    {split : Fin n → Fin k → Nat} (feasible : SplitFeasible E roots weight capacity split)
    (S : Finset (Fin k))
    (nonessential : ∀ i ∈ S, ∀ v, ∀ hv : ¬RootSet roots v,
      v ∉ S.biUnion (predecessorSet E roots) → ¬Essential E (RootSet roots) v hv (roots i)) :
    let N := S.biUnion (predecessorSet E roots)
    let V := Finset.univ.filter (fun v => ¬RootSet roots v ∧ v ∉ N)
    (∀ v ∈ V, ∑ i ∈ Finset.univ.filter (fun i => i ∉ S), split v i = weight v) ∧
    (∀ i, ∑ v ∈ V, split v i ≤ capacity i) ∧
    (∀ v ∈ V, ∀ i, i ∉ S → 0 < split v i →
      ∃ r, HasRank (retain (List.finRange n) (S.image roots ∪ N))
          (RemoveVertices E (S.image roots ∪ N)) (RemoveTerminals (RootSet roots) (S.image roots)) v r ∧
        CutEssential (retain (List.finRange n) (S.image roots ∪ N))
          (RemoveVertices E (S.image roots ∪ N)) (RemoveTerminals (RootSet roots) (S.image roots)) v r (roots i)) := by
  classical
  dsimp only
  let N := S.biUnion (predecessorSet E roots)
  have zero (v : Fin n) (hv : ¬RootSet roots v) (outside : v ∉ N) (i : Fin k) (hi : i ∈ S) :
      split v i = 0 := by
    by_contra h
    exact nonessential i hi v hv outside (feasible.1 v hv i (Nat.pos_of_ne_zero h))
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    have prop := (Finset.mem_filter.mp hv).2
    calc
      _ = ∑ i, split v i := Finset.sum_subset (Finset.filter_subset _ _)
        (fun i _ hi => zero v prop.1 prop.2 i (by simpa using hi))
      _ = weight v := feasible.2.1 v prop.1
  · intro i
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (by intro v hv; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2.1⟩)
      (fun _ _ _ => Nat.zero_le _)) (feasible.2.2 i)
  · intro v hv i hi positive
    have prop := (Finset.mem_filter.mp hv).2
    have essential := feasible.1 v prop.1 i positive
    have terminals : ∀ x ∈ S.image roots, RootSet roots x := by
      intro x hx
      obtain ⟨j, _, he⟩ := Finset.mem_image.mp hx
      exact ⟨j, he⟩
    have neighbors_nonterminal : ∀ x ∈ N, ¬RootSet roots x := by
      intro x hx
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp hj).2.1
    have covers : ∀ x y, ¬RootSet roots x → y ∈ S.image roots → E x y → x ∈ N := by
      intro x y hnt hy edge
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_biUnion.mpr ⟨j, hj, by simp [predecessorSet, hnt, edge]⟩
    have neighbors : ∀ x ∈ N, ∃ y ∈ S.image roots, E x y := by
      intro x hx
      obtain ⟨j, hj, edge⟩ := Finset.mem_biUnion.mp hx
      exact ⟨roots j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, (Finset.mem_filter.mp edge).2.2⟩
    have outsideRoot : roots i ∉ S.image roots := by
      intro hx
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hx
      exact nonessential j hj v prop.1 prop.2 (he.symm ▸ essential)
    exact rounding_essential (S.image roots) N terminals neighbors_nonterminal covers neighbors
      prop.1 ⟨i, rfl⟩ prop.2 outsideRoot (cutRank_spec E (RootSet roots) v prop.1)
      (fun x hx => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        exact nonessential j hj v prop.1 prop.2) essential

end GyoriLovasz
