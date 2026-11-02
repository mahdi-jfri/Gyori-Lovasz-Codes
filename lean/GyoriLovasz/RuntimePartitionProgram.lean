import GyoriLovasz.RuntimeUniformBudget

namespace GyoriLovasz.WordInstance

def CheckedResult (s : Input n k) (bound N B : Nat) :=
  {answer : Costed.Computation (Vector (Fin k) n) //
    WeightedPartitionOn Finset.univ Finset.univ (relation s) (root s) (weights s)
      (fun i => capacities s i + bound - 1) (fun v => answer.1[v.val]) ∧
    answer.2 ≤ (n + 1) * universalBudget N B}

set_option maxHeartbeats 2000000 in
/-- The executable normalized partition program. Proof fields certify the
computed labels and counter and are erased during execution. Every recursive
call has fewer vertices; no partition or matching oracle is an argument. -/
def solveNormalized (N B bound : Nat) {n k : Nat} (s : Input n k)
    (h : Valid s bound) (wb : Bounded s B) (size : n ≤ N) : CheckedResult s bound N B := by
  have rootsSize : k ≤ N := (valid_root_count s bound h).trans size
  let found := nonrootFind s.roots
  have foundCost : found.2 ≤ nonrootCeiling N := nonroot_uniform s.roots N size rootsSize
  cases foundEq : found.1 with
  | none =>
    have allroot := nonrootFind_none s.roots foundEq
    let labels := baseLabels s.roots allroot
    have labelsCost : labels.2 ≤ baseCeiling N := base_uniform s.roots allroot N size rootsSize
    have localBound : found.2 + labels.2 + 20 ≤ universalBudget N B := by
      unfold universalBudget
      omega
    exact ⟨(labels.1, found.2 + labels.2 + 20),
      baseLabels_correct s _ h.injective h.rootzero allroot, finish_cost localBound⟩
  | some v =>
    have nt := nonrootFind_some s.roots v foundEq
    have dimensions := valid_nonroot_dimensions s bound h v nt
    cases n with
    | zero => omega
    | succ m =>
      have positive : 0 < m := by omega
      let zero := zeroFind s.capacity
      have zeroCost : zero.2 ≤ zeroCeiling N B := zero_uniform s.capacity N B rootsSize wb.2
      cases zeroEq : zero.1 with
      | some i =>
        have capacityZero : capacities s i = 0 := zeroFind_some s.capacity i zeroEq
        have rootsLarge := valid_zero_root_dimensions s bound h v nt i capacityZero
        cases k with
        | zero => exact Fin.elim0 i
        | succ l =>
          have positiveRoots : 0 < l := by omega
          let prepared := terminalStep s i positive
          have preparedValid := terminalStep_valid s i positive positiveRoots bound h capacityZero
          have preparedBound := terminalStep_bounds s i positive B wb
          let child := solveNormalized N B bound prepared.1.1 preparedValid preparedBound (by omega)
          let restored := restoreTerminal (root s i) i prepared.1.2 child.1.1
          have preparedCost : prepared.2 ≤ terminalStepBudget N N := terminal_uniform s i positive N size rootsSize
          have restoredCost : restored.2 ≤ singleRestoreCeiling N :=
            restoreTerminal_uniform (root s i) i prepared.1.2 child.1.1 N size
          have localBound : found.2 + zero.2 + prepared.2 + restored.2 + 20 ≤ universalBudget N B := by
            unfold universalBudget
            omega
          have total := recursive_cost localBound child.2.2 (show m < m + 1 by omega)
          exact ⟨(restored.1, found.2 + zero.2 + prepared.2 + restored.2 + 20 + child.1.2),
            terminalStep_restore s i positive positiveRoots bound h child.1.1 child.2.1, total⟩
      | none =>
        have capacitiesPositive : ∀ i, 0 < capacities s i := zeroFind_none s.capacity zeroEq
        let reduced := reduceInput s B
        have reducedValid := reduceInput_valid s B bound wb h
        have reducedBound := reduceInput_bounds s B wb
        have reducedCost : reduced.2 ≤ reduceInputBudget N N B := reduce_uniform s N B size rootsSize wb
        let sole := findSole reduced.1.graph reduced.1.roots
        have soleCost : sole.2 ≤ soleBudget N N := sole_uniform reduced.1.graph reduced.1.roots N size rootsSize
        cases soleEq : sole.1 with
        | some a =>
          have localMove := findSole_some reduced.1.graph reduced.1.roots a soleEq
          let prepared := contractStep reduced.1 a.2 a.1 positive
          have preparedValid := contractStep_valid reduced.1 a.2 a.1 positive bound reducedValid
            localMove.1 localMove.2.1 localMove.2.2
          have preparedBound := contractStep_bounds reduced.1 a.2 a.1 positive B reducedBound
          let child := solveNormalized N B bound prepared.1.1 preparedValid preparedBound (by omega)
          let restored := restoreContract a.2 a.1 prepared.1.2 child.1.1
          have preparedCost : prepared.2 ≤ contractStepBudget N N B :=
            contract_uniform reduced.1 a.2 a.1 positive N B size rootsSize reducedBound
          have restoredCost : restored.2 ≤ singleRestoreCeiling N :=
            restoreContract_uniform a.2 a.1 prepared.1.2 child.1.1 N size
          have localBound : found.2 + zero.2 + reduced.2 + sole.2 + prepared.2 + restored.2 + 20 ≤ universalBudget N B := by
            unfold universalBudget
            omega
          have total := recursive_cost localBound child.2.2 (show m < m + 1 by omega)
          have part := contractStep_restore reduced.1 a.2 a.1 positive bound reducedValid
            localMove.1 localMove.2.1 localMove.2.2 child.1.1 child.2.1
          exact ⟨(restored.1, found.2 + zero.2 + reduced.2 + sole.2 + prepared.2 + restored.2 + 20 + child.1.2),
            reduceInput_restore s B bound wb h restored.1 part, total⟩
        | none =>
          have hk : 0 < k := by obtain ⟨j, _⟩ := dimensions.2; exact Nat.zero_lt_of_lt j.isLt
          have failure := reduceInput_no_sole s B bound wb h hk soleEq
          let data := roundData reduced.1.graph reduced.1.roots failure
          have dataCorrect := roundData_correct reduced.1.graph reduced.1.roots reducedValid.injective failure
          let shape := roundShape reduced.1 data.1.1
          let rounded := roundedLabels reduced.1.roots data.1.2
          have dataCost : data.2 ≤ roundDataBudget N N := roundData_uniform reduced.1.graph reduced.1.roots failure N size rootsSize
          have shapeCost : shape.2 ≤ roundShapeBudget N N := shape_uniform reduced.1 data.1.1 N size rootsSize
          have roundedCost : rounded.2 ≤ roundedCeiling N := rounded_uniform reduced.1.roots data.1.2 N size rootsSize
          by_cases empty : shape.1.rootsCount = 0
          · have part := roundData_finishes reduced.1 bound reducedValid capacitiesPositive failure empty
            have localBound : found.2 + zero.2 + reduced.2 + sole.2 + data.2 + shape.2 + rounded.2 + 20 ≤ universalBudget N B := by
              unfold universalBudget
              omega
            exact ⟨(rounded.1, found.2 + zero.2 + reduced.2 + sole.2 + data.2 + shape.2 + rounded.2 + 20),
              reduceInput_restore s B bound wb h rounded.1 part, finish_cost localBound⟩
          · have positiveRoots : 0 < shape.1.rootsCount := Nat.pos_of_ne_zero empty
            have positiveVertices : 0 < shape.1.verticesCount :=
              roundShape_positive reduced.1 data.1.1 reducedValid.injective positiveRoots
            have smaller : shape.1.verticesCount < m + 1 := roundShape_smaller reduced.1 data.1.1 dataCorrect.1
            have counts := roundShape_counts reduced.1 data.1.1
            let prepared := remainingStep reduced.1 shape.1 positiveVertices
            have preparedValid := remainingStep_valid reduced.1 data.1.1 positiveVertices positiveRoots bound
              reducedValid dataCorrect.2.2.2
            have preparedBound := remainingStep_bounds reduced.1 shape.1 positiveVertices B reducedBound
            let child := solveNormalized N B bound prepared.1.1 preparedValid preparedBound (by omega)
            let restored := restoreRemaining shape.1 prepared.1.2 child.1.1 rounded.1
            have preparedCost : prepared.2 ≤ remainingStepBudget N N N :=
              remaining_uniform reduced.1 shape.1 positiveVertices N size (counts.1.trans size) (counts.2.trans rootsSize)
            have restoredCost : restored.2 ≤ remainingRestoreCeiling N :=
              restoreRemaining_uniform shape.1 prepared.1.2 child.1.1 rounded.1 N size
            have localBound : found.2 + zero.2 + reduced.2 + sole.2 + data.2 + shape.2 + rounded.2 + prepared.2 + restored.2 + 20 ≤ universalBudget N B := by
              unfold universalBudget
              omega
            have total := recursive_cost localBound child.2.2 smaller
            have parts := roundData_partition reduced.1 bound reducedValid capacitiesPositive failure
            have part := remainingStep_restore reduced.1 data.1.1 positiveVertices positiveRoots bound reducedValid
              child.1.1 rounded.1 parts child.2.1
            exact ⟨(restored.1, found.2 + zero.2 + reduced.2 + sole.2 + data.2 + shape.2 + rounded.2 + prepared.2 + restored.2 + 20 + child.1.2),
              reduceInput_restore s B bound wb h restored.1 part, total⟩
termination_by n
decreasing_by
  all_goals simp_wf
  all_goals first | assumption | omega | (convert smaller using 1)

end GyoriLovasz.WordInstance
