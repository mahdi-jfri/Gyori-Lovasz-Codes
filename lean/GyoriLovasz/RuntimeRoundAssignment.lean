import GyoriLovasz.RuntimeMatchingInverse

namespace GyoriLovasz
open TransportNetwork

def roundAssignment (neighbors : Vector (Vector Bool n) k) (selected : Vector Bool k) (i : Fin k) :
    Costed.Computation (Vector (Fin k) n) :=
  let cleared := SaturationPrune.clear selected i
  let matched := matchingWitness neighbors cleared.1
  let inverted := inverseMatching matched.1
  let labels := Costed.tabulate n (fun v => (inverted.1[v.val].getD i, 2))
  (labels.1, cleared.2 + matched.2 + inverted.2 + labels.2 + 3)

theorem roundAssignment_correct (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (selected : Vector Bool k) (i : Fin k)
    (hi : selected[i.val] = true)
    (deficient : ((SaturationPrune.selectedSet selected).biUnion
      (predecessorSet (fun x y => E[x.val][y.val] = true) (fun i => roots[i.val]))).card <
      (SaturationPrune.selectedSet selected).card)
    (sat : Saturates (fun a v => (rootNeighbors E roots).1[a.val][v.val])
      (fun a => (SaturationPrune.clear selected i).1[a.val])) :
    let S := SaturationPrune.selectedSet selected
    let N := S.biUnion (predecessorSet (fun x y => E[x.val][y.val] = true) (fun i => roots[i.val]))
    let f := fun v : Fin n => (roundAssignment (rootNeighbors E roots).1 selected i).1[v.val]
    Set.InjOn f N ∧ ∀ v ∈ N, f v ∈ S ∧ E[v.val][roots[(f v).val].val] = true := by
  classical
  let M := (matchingWitness (rootNeighbors E roots).1 (SaturationPrune.clear selected i).1).1
  let S := SaturationPrune.selectedSet selected
  let N := S.biUnion (predecessorSet (fun x y => E[x.val][y.val] = true) (fun i => roots[i.val]))
  have correct := matchingWitness_correct (rootNeighbors E roots).1 (SaturationPrune.clear selected i).1 sat
  have matched : ∀ a ∈ S.erase i, ∃ v, M[a.val] = some v ∧ v ∈ N := by
    intro a ha
    have active : (SaturationPrune.clear selected i).1[a.val] = true := by
      rw [← SaturationPrune.mem_selectedSet, SaturationPrune.clear_set]
      exact ha
    obtain ⟨v, hv, edge⟩ := correct.1 a active
    refine ⟨v, hv, Finset.mem_biUnion.mpr ⟨a, Finset.mem_of_mem_erase ha, ?_⟩⟩
    rw [← rootNeighbors_family E roots]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, edge⟩
  have h := inverse_matching_rounds M S N i ((SaturationPrune.mem_selectedSet selected i).mpr hi)
    deficient matched correct.2
  simp only [roundAssignment, Costed.tabulate_value]
  refine ⟨h.1, ?_⟩
  intro v hv
  have hv' := h.2 v hv
  refine ⟨hv'.1, ?_⟩
  obtain ⟨a, ha, he⟩ := matching_covers_deficiency M S N i
    ((SaturationPrune.mem_selectedSet selected i).mpr hi) deficient matched correct.2 v hv
  have active : (SaturationPrune.clear selected i).1[a.val] = true := by
    rw [← SaturationPrune.mem_selectedSet, SaturationPrune.clear_set]
    exact ha
  obtain ⟨w, hw, edge⟩ := correct.1 a active
  have wv : w = v := Option.some.inj (hw.symm.trans he)
  have ae := correct.2 a (((inverseMatching M).1[v.val]).getD i) v he hv'.2
  rw [wv] at edge
  have original := ((rootNeighbors_correct E roots a v).mp edge).2
  simpa only [ae] using original

def roundAssignmentBudget (n k : Nat) := (2 * k * k + 9 * k + 3) + matchingWitnessBudget k n +
  (2 * n * n + n * (2 * k * k + 8 * k + 9) + 3) + (2 * n * n + 8 * n + 3) + 3

theorem roundAssignment_cost (neighbors : Vector (Vector Bool n) k) (selected : Vector Bool k) (i : Fin k) :
    (roundAssignment neighbors selected i).2 ≤ roundAssignmentBudget n k := by
  have hc := SaturationPrune.clear_cost selected i
  have hm := matchingWitness_cost neighbors (SaturationPrune.clear selected i).1
  have hv := inverseMatching_cost (matchingWitness neighbors (SaturationPrune.clear selected i).1).1
  have hl := Costed.tabulate_cost n
    (fun v => ((inverseMatching (matchingWitness neighbors (SaturationPrune.clear selected i).1).1).1[v.val].getD i, 2))
    2 (by intros; rfl)
  dsimp only [roundAssignment, roundAssignmentBudget]
  norm_num only at hl
  simp only [Nat.mul_comm n 8] at hl
  omega

end GyoriLovasz
