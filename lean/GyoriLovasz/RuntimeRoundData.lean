import GyoriLovasz.RuntimeRoundSelection
import GyoriLovasz.RuntimeRoundBlock

namespace GyoriLovasz
open TransportNetwork

theorem prunedSet_deficiency (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (failure : ¬Saturates (fun i v => (rootNeighbors E roots).1[i.val][v.val]) (fun _ => true)) :
    let S := SaturationPrune.selectedSet (prunedSet (rootNeighbors E roots).1).1
    S.Nonempty ∧
      (S.biUnion (predecessorSet (fun x y => E[x.val][y.val] = true) (fun i => roots[i.val]))).card < S.card ∧
      ∀ U, U ⊂ S → U.card ≤
        (U.biUnion (predecessorSet (fun x y => E[x.val][y.val] = true) (fun i => roots[i.val]))).card := by
  have hn : ¬Saturates (fun i v => (rootNeighbors E roots).1[i.val][v.val]) (fun i => (allSelected k).1[i.val]) := by
    simpa only [allSelected_value] using failure
  exact pruned_roots_deficient E roots (allSelected k).1 hn

def roundData (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (failure : ¬Saturates (fun i v => (rootNeighbors E roots).1[i.val][v.val]) (fun _ => true)) :
    Costed.Computation (Vector Bool k × Vector (Fin k) n) :=
  let neighbors := rootNeighbors E roots
  let selected := prunedSet neighbors.1
  let chosen := selectedIndex selected.1 (prunedSet_spec neighbors.1 failure).1
  let assignment := roundAssignment neighbors.1 selected.1 chosen.1
  ((selected.1, assignment.1), neighbors.2 + selected.2 + chosen.2 + assignment.2 + 3)

theorem roundData_correct (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (inj : Function.Injective (fun i : Fin k => roots[i.val]))
    (failure : ¬Saturates (fun i v => (rootNeighbors E roots).1[i.val][v.val]) (fun _ => true)) :
    let data := (roundData E roots failure).1
    let S := SaturationPrune.selectedSet data.1
    let N := S.biUnion (predecessorSet (fun x y => E[x.val][y.val] = true) (fun i => roots[i.val]))
    let f := fun v : Fin n => data.2[v.val]
    S.Nonempty ∧ Set.InjOn f N ∧
      (∀ v ∈ N, f v ∈ S ∧ E[v.val][roots[(f v).val].val] = true) ∧
      (∀ i ∈ S, ∀ v, ∀ hv : ¬RootSet (fun i => roots[i.val]) v,
        v ∉ N → ¬Essential (fun x y => E[x.val][y.val] = true) (RootSet (fun i => roots[i.val])) v hv roots[i.val]) := by
  let neighbors := (rootNeighbors E roots).1
  let selected := (prunedSet neighbors).1
  let i := (selectedIndex selected (prunedSet_spec neighbors failure).1).1
  have hi : selected[i.val] = true := selectedIndex_correct selected (prunedSet_spec neighbors failure).1
  have deficient := prunedSet_deficiency E roots failure
  have assigned := roundAssignment_correct E roots selected i hi deficient.2.1
    (prunedSet_clear_saturates neighbors failure i hi)
  exact ⟨deficient.1, assigned.1, assigned.2,
    local_hall_nonessential inj _ deficient.2.1 deficient.2.2⟩

def roundDataBudget (n k : Nat) := rootNeighborBudget n k + prunedSetBudget k n +
  (2 * k * k + 6 * k + 4) + roundAssignmentBudget n k + 3

theorem roundData_cost (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (failure : ¬Saturates (fun i v => (rootNeighbors E roots).1[i.val][v.val]) (fun _ => true)) :
    (roundData E roots failure).2 ≤ roundDataBudget n k := by
  have hn := rootNeighbors_cost E roots
  have hs := prunedSet_cost (rootNeighbors E roots).1
  have hi := selectedIndex_cost (prunedSet (rootNeighbors E roots).1).1 (prunedSet_spec _ failure).1
  have ha := roundAssignment_cost (rootNeighbors E roots).1 (prunedSet (rootNeighbors E roots).1).1
    (selectedIndex (prunedSet (rootNeighbors E roots).1).1 (prunedSet_spec _ failure).1).1
  dsimp only [roundData, roundDataBudget]
  omega

end GyoriLovasz
