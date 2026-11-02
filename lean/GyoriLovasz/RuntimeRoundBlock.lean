import GyoriLovasz.RuntimeRoundAssignment

namespace GyoriLovasz

def blockCell (neighbors : Vector (Vector Bool n) k) (roots : Vector (Fin n) k)
    (selected : Vector Bool k) (v : Fin n) : Bool × Nat :=
  let indices := Costed.enumerateIndices k
  let found := Costed.find (fun i => (selected[i.val] && (decide (roots[i.val] = v) || neighbors[i.val][v.val]), 6)) indices.1
  (found.1.isSome, indices.2 + found.2 + 1)

theorem blockCell_correct (neighbors : Vector (Vector Bool n) k) (roots : Vector (Fin n) k)
    (selected : Vector Bool k) (v : Fin n) :
    (blockCell neighbors roots selected v).1 = true ↔
      ∃ i : Fin k, selected[i.val] = true ∧ (roots[i.val] = v ∨ neighbors[i.val][v.val] = true) := by
  simp only [blockCell, Costed.find_value, List.find?_isSome, Costed.enumerateIndices_value,
    List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]

theorem blockCell_cost (neighbors : Vector (Vector Bool n) k) (roots : Vector (Fin n) k)
    (selected : Vector Bool k) (v : Fin n) :
    (blockCell neighbors roots selected v).2 ≤ 2 * k * k + 11 * k + 3 := by
  have hi := Costed.enumerateIndices_cost k
  have hf := Costed.find_cost
    (fun i : Fin k => (selected[i.val] && (decide (roots[i.val] = v) || neighbors[i.val][v.val]), 6))
    (Costed.enumerateIndices k).1 6 (by intros; rfl)
  simp only [Costed.enumerateIndices_value, List.length_finRange] at hf
  dsimp only [blockCell]
  simp only [Costed.enumerateIndices_value]
  omega

def roundBlock (neighbors : Vector (Vector Bool n) k) (roots : Vector (Fin n) k) (selected : Vector Bool k) :
    Costed.Computation (Vector Bool n) := Costed.tabulate n (blockCell neighbors roots selected)

theorem roundBlock_set (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k) (selected : Vector Bool k) :
    SaturationPrune.selectedSet (roundBlock (rootNeighbors E roots).1 roots selected).1 =
      (SaturationPrune.selectedSet selected).image (fun i => roots[i.val]) ∪
      (SaturationPrune.selectedSet selected).biUnion
        (predecessorSet (fun x y => E[x.val][y.val] = true) (fun i => roots[i.val])) := by
  classical
  ext v
  rw [SaturationPrune.mem_selectedSet, roundBlock, Costed.tabulate_value, blockCell_correct]
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, SaturationPrune.mem_selectedSet]
  constructor
  · rintro ⟨i, hi, edge | neighbor⟩
    · exact Or.inl ⟨i, hi, edge⟩
    · apply Or.inr
      refine ⟨i, hi, ?_⟩
      rw [← rootNeighbors_family E roots]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, neighbor⟩
  · rintro (⟨i, hi, edge⟩ | ⟨i, hi, neighbor⟩)
    · exact ⟨i, hi, Or.inl edge⟩
    · refine ⟨i, hi, Or.inr ?_⟩
      rw [← rootNeighbors_family E roots] at neighbor
      exact (Finset.mem_filter.mp neighbor).2

theorem roundBlock_cost (neighbors : Vector (Vector Bool n) k) (roots : Vector (Fin n) k) (selected : Vector Bool k) :
    (roundBlock neighbors roots selected).2 ≤ 2 * n * n + n * (2 * k * k + 11 * k + 9) + 3 := by
  simpa only [roundBlock, Nat.add_assoc] using Costed.tabulate_cost n _ (2 * k * k + 11 * k + 3)
    (blockCell_cost neighbors roots selected)

def complementMask (mask : Vector Bool n) : Costed.Computation (Vector Bool n) :=
  Costed.tabulate n (fun v => (!mask[v.val], 2))

theorem complementMask_correct (mask : Vector Bool n) (v : Fin n) :
    (complementMask mask).1[v.val] = true ↔ ¬mask[v.val] = true := by
  simp only [complementMask, Costed.tabulate_value, Bool.not_eq_true', Bool.eq_false_iff]

theorem complementMask_cost (mask : Vector Bool n) :
    (complementMask mask).2 ≤ 2 * n * n + 8 * n + 3 := by
  simpa only [Nat.mul_comm n 8] using Costed.tabulate_cost n (fun v => (!mask[v.val], 2)) 2 (by intros; rfl)

end GyoriLovasz
