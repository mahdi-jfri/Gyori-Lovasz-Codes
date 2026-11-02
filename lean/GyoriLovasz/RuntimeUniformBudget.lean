import GyoriLovasz.RuntimeBudgetMonotonicity
import GyoriLovasz.RuntimeRemainingRestore
import GyoriLovasz.RuntimeRoundFinish
import GyoriLovasz.RuntimeBranchSearch
import GyoriLovasz.RuntimeContractRestore

namespace GyoriLovasz.WordInstance
open BudgetMonotonicity TransportNetwork

def nonrootCeiling (N : Nat) := rootMaskBudget N N + 2 * N * N + 7 * N + 3
def zeroCeiling (N B : Nat) := 2 * N * N + 2 * N + N * (9 * B + 7) + 3
def baseCeiling (N : Nat) := 2 * N * N + N * (2 * N * N + 7 * N + 10) + 3
def singleRestoreCeiling (N : Nat) := 2 * N * N + 12 * N + 3
def roundedCeiling (N : Nat) := 2 * N * N + N * (2 * N * N + 7 * N + 11) + 3
def remainingRestoreCeiling (N : Nat) := 4 * N * N + 20 * N + 7

def universalBudget (N B : Nat) :=
  nonrootCeiling N + zeroCeiling N B + baseCeiling N +
  reduceInputBudget N N B + soleBudget N N +
  contractStepBudget N N B + terminalStepBudget N N + singleRestoreCeiling N +
  roundDataBudget N N + roundShapeBudget N N + roundedCeiling N +
  remainingStepBudget N N N + remainingRestoreCeiling N + 50

theorem nonroot_uniform (roots : Vector (Fin n) k) (N : Nat) (hn : n ≤ N) (hk : k ≤ N) :
    (nonrootFind roots).2 ≤ nonrootCeiling N := by
  apply (nonrootFind_cost roots).trans
  unfold nonrootCeiling
  gcongr

theorem zero_uniform (capacity : Vector (List Bool) k) (N B : Nat) (hk : k ≤ N)
    (h : ∀ i : Fin k, capacity[i.val].length ≤ B) : (zeroFind capacity).2 ≤ zeroCeiling N B := by
  apply (zeroFind_cost capacity B h).trans
  unfold zeroCeiling
  gcongr

theorem base_uniform (roots : Vector (Fin n) k) (allroot : ∀ v, RootSet (fun i => roots[i.val]) v)
    (N : Nat) (hn : n ≤ N) (hk : k ≤ N) : (baseLabels roots allroot).2 ≤ baseCeiling N := by
  apply (baseLabels_cost roots allroot).trans
  unfold baseCeiling
  gcongr

theorem reduce_uniform (s : Input n k) (N B : Nat) (hn : n ≤ N) (hk : k ≤ N) (h : Bounded s B) :
    (reduceInput s B).2 ≤ reduceInputBudget N N B :=
  (reduceInput_cost s B h).trans (WordInstance_reduceInputBudget_mono hn hk (Nat.le_refl B))

theorem sole_uniform (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (N : Nat) (hn : n ≤ N) (hk : k ≤ N) : (findSole E roots).2 ≤ soleBudget N N :=
  (findSole_cost E roots).trans (soleBudget_mono hn hk)

theorem contract_uniform (s : Input (m + 1) k) (p : Fin (m + 1)) (i : Fin k) (positive : 0 < m)
    (N B : Nat) (hn : m + 1 ≤ N) (hk : k ≤ N) (h : Bounded s B) :
    (contractStep s p i positive).2 ≤ contractStepBudget N N B :=
  (contractStep_cost s p i positive B h).trans
    (WordInstance_contractStepBudget_mono (by omega) hk (Nat.le_refl B))

theorem terminal_uniform (s : Input (m + 1) (l + 1)) (i : Fin (l + 1)) (positive : 0 < m)
    (N : Nat) (hn : m + 1 ≤ N) (hk : l + 1 ≤ N) :
    (terminalStep s i positive).2 ≤ terminalStepBudget N N :=
  (terminalStep_cost s i positive).trans (WordInstance_terminalStepBudget_mono (by omega) (by omega))

theorem restoreContract_uniform (p : Fin (m + 1)) (i : Fin k) (reverse : Vector (Fin m) (m + 1))
    (labels : Vector (Fin k) m) (N : Nat) (hn : m + 1 ≤ N) :
    (restoreContract p i reverse labels).2 ≤ singleRestoreCeiling N := by
  apply (restoreContract_cost p i reverse labels).trans
  unfold singleRestoreCeiling
  gcongr; omega

theorem restoreTerminal_uniform (p : Fin (m + 1)) (i : Fin (l + 1)) (reverse : Vector (Fin m) (m + 1))
    (labels : Vector (Fin l) m) (N : Nat) (hn : m + 1 ≤ N) :
    (restoreTerminal p i reverse labels).2 ≤ singleRestoreCeiling N := by
  apply (restoreTerminal_cost p i reverse labels).trans
  unfold singleRestoreCeiling
  gcongr

theorem roundData_uniform (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (failure : ¬Saturates (fun i v => (rootNeighbors E roots).1[i.val][v.val]) (fun _ => true))
    (N : Nat) (hn : n ≤ N) (hk : k ≤ N) : (roundData E roots failure).2 ≤ roundDataBudget N N :=
  (roundData_cost E roots failure).trans (roundDataBudget_mono hn hk)

theorem shape_uniform (s : Input n k) (selected : Vector Bool k)
    (N : Nat) (hn : n ≤ N) (hk : k ≤ N) : (roundShape s selected).2 ≤ roundShapeBudget N N :=
  (roundShape_cost s selected).trans (roundShapeBudget_mono hn hk)

theorem rounded_uniform (roots : Vector (Fin n) k) (assignment : Vector (Fin k) n)
    (N : Nat) (hn : n ≤ N) (hk : k ≤ N) : (roundedLabels roots assignment).2 ≤ roundedCeiling N := by
  apply (roundedLabels_cost roots assignment).trans
  unfold roundedCeiling
  gcongr

theorem remaining_uniform (s : Input n k) (shape : Shape n k) (positive : 0 < shape.verticesCount)
    (N : Nat) (hn : n ≤ N) (hm : shape.verticesCount ≤ N) (hl : shape.rootsCount ≤ N) :
    (remainingStep s shape positive).2 ≤ remainingStepBudget N N N :=
  (remainingStep_cost s shape positive).trans (WordInstance_remainingStepBudget_mono hn hm hl)

theorem restoreRemaining_uniform (shape : Shape n k) (reverse : Vector (Fin shape.verticesCount) n)
    (labels : Vector (Fin shape.rootsCount) shape.verticesCount) (rounded : Vector (Fin k) n)
    (N : Nat) (hn : n ≤ N) : (restoreRemaining shape reverse labels rounded).2 ≤ remainingRestoreCeiling N := by
  apply (restoreRemaining_cost shape reverse labels rounded).trans
  unfold remainingRestoreCeiling
  gcongr

theorem valid_root_count (s : Input n k) (bound : Nat) (h : Valid s bound) : k ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (root s) h.injective

theorem finish_cost {localCost U n : Nat} (h : localCost ≤ U) : localCost ≤ (n + 1) * U :=
  h.trans (by simpa using Nat.mul_le_mul_right U (show 1 ≤ n + 1 by omega))

theorem recursive_cost {localCost childCost U n m : Nat}
    (localBound : localCost ≤ U) (childBound : childCost ≤ (m + 1) * U) (smaller : m < n) :
    localCost + childCost ≤ (n + 1) * U := by
  have product := Nat.mul_le_mul_right U (show m + 1 ≤ n by omega)
  rw [Nat.add_mul, Nat.one_mul]
  omega

end GyoriLovasz.WordInstance
