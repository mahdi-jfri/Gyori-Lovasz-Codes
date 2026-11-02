import GyoriLovasz.RuntimeRemainingStep
import GyoriLovasz.RuntimeTerminalRestore
import GyoriLovasz.RuntimeReduceInput
import GyoriLovasz.RuntimeRoundData

namespace GyoriLovasz.BudgetMonotonicity

@[gcongr] theorem WordShortest_stepBudget_mono
    {n L B n' L' B' : Nat} (hn : n ≤ n') (hL : L ≤ L') (hB : B ≤ B') :
    WordShortest.stepBudget n L B ≤ WordShortest.stepBudget n' L' B' := by
  unfold WordShortest.stepBudget
  gcongr

@[gcongr] theorem WordPath_budget_mono
    {n B n' B' : Nat} (hn : n ≤ n') (hB : B ≤ B') :
    WordPath.budget n B ≤ WordPath.budget n' B' := by
  unfold WordPath.budget
  gcongr

@[gcongr] theorem Flow_residualBuildBudget_mono
    {n m B n' m' B' : Nat} (hn : n ≤ n') (hm : m ≤ m') (hB : B ≤ B') :
    Flow.residualBuildBudget n m B ≤ Flow.residualBuildBudget n' m' B' := by
  unfold Flow.residualBuildBudget
  gcongr

@[gcongr] theorem Flow_graphBudget_mono
    {n n' : Nat} (hn : n ≤ n') :
    Flow.graphBudget n ≤ Flow.graphBudget n' := by
  unfold Flow.graphBudget
  gcongr

@[gcongr] theorem Flow_routeBudget_mono
    {n B n' B' : Nat} (hn : n ≤ n') (hB : B ≤ B') :
    Flow.routeBudget n B ≤ Flow.routeBudget n' B' := by
  unfold Flow.routeBudget
  gcongr

@[gcongr] theorem Flow_distanceBudget_mono
    {n B n' B' : Nat} (hn : n ≤ n') (hB : B ≤ B') :
    Flow.distanceBudget n B ≤ Flow.distanceBudget n' B' := by
  unfold Flow.distanceBudget
  gcongr

@[gcongr] theorem Flow_augmentBudget_mono
    {m B L m' B' L' : Nat} (hm : m ≤ m') (hB : B ≤ B') (hL : L ≤ L') :
    Flow.augmentBudget m B L ≤ Flow.augmentBudget m' B' L' := by
  unfold Flow.augmentBudget
  gcongr

@[gcongr] theorem Flow_repairBudget_mono
    {n m B n' m' B' : Nat} (hn : n ≤ n') (hm : m ≤ m') (hB : B ≤ B') :
    Flow.repairBudget n m B ≤ Flow.repairBudget n' m' B' := by
  unfold Flow.repairBudget
  gcongr

@[gcongr] theorem Flow_opBudget_mono
    {n m B n' m' B' : Nat} (hn : n ≤ n') (hm : m ≤ m') (hB : B ≤ B') :
    Flow.opBudget n m B ≤ Flow.opBudget n' m' B' := by
  unfold Flow.opBudget
  gcongr

@[gcongr] theorem Flow_storedBudget_mono
    {n m B n' m' B' : Nat} (hn : n ≤ n') (hm : m ≤ m') (hB : B ≤ B') :
    Flow.storedBudget n m B ≤ Flow.storedBudget n' m' B' := by
  unfold Flow.storedBudget
  gcongr

@[gcongr] theorem Flow_returnBudget_mono
    {m B m' B' : Nat} (hm : m ≤ m') (hB : B ≤ B') :
    Flow.returnBudget m B ≤ Flow.returnBudget m' B' := by
  unfold Flow.returnBudget
  gcongr

@[gcongr] theorem Flow_throughputBudget_mono
    {m m' : Nat} (hm : m ≤ m') :
    Flow.throughputBudget m ≤ Flow.throughputBudget m' := by
  unfold Flow.throughputBudget
  gcongr

@[gcongr] theorem Flow_maxFlowBudget_mono
    {n m B n' m' B' : Nat} (hn : n ≤ n') (hm : m ≤ m') (hB : B ≤ B') :
    Flow.maxFlowBudget n m B ≤ Flow.maxFlowBudget n' m' B' := by
  unfold Flow.maxFlowBudget
  gcongr

@[gcongr] theorem Flow_maxFlowWordLength_mono
    {n m B n' m' B' : Nat} (hn : n ≤ n') (hm : m ≤ m') (hB : B ≤ B') :
    Flow.maxFlowWordLength n m B ≤ Flow.maxFlowWordLength n' m' B' := by
  unfold Flow.maxFlowWordLength
  gcongr

@[gcongr] theorem VertexNetwork_buildBudget_mono
    {n n' : Nat} (hn : n ≤ n') :
    VertexNetwork.buildBudget n ≤ VertexNetwork.buildBudget n' := by
  unfold VertexNetwork.buildBudget
  gcongr

@[gcongr] theorem VertexNetwork_essentialBudget_mono
    {n n' : Nat} (hn : n ≤ n') :
    VertexNetwork.essentialBudget n ≤ VertexNetwork.essentialBudget n' := by
  unfold VertexNetwork.essentialBudget
  gcongr

@[gcongr] theorem TransportNetwork_buildBudget_mono
    {l r l' r' : Nat} (hl : l ≤ l') (hr : r ≤ r') :
    TransportNetwork.buildBudget l r ≤ TransportNetwork.buildBudget l' r' := by
  unfold TransportNetwork.buildBudget
  gcongr

@[gcongr] theorem TransportNetwork_matrixBudget_mono
    {l r B l' r' B' : Nat} (hl : l ≤ l') (hr : r ≤ r') (hB : B ≤ B') :
    TransportNetwork.matrixBudget l r B ≤ TransportNetwork.matrixBudget l' r' B' := by
  unfold TransportNetwork.matrixBudget
  gcongr

@[gcongr] theorem rootMaskBudget_mono
    {n k n' k' : Nat} (hn : n ≤ n') (hk : k ≤ k') :
    rootMaskBudget n k ≤ rootMaskBudget n' k' := by
  unfold rootMaskBudget
  gcongr

@[gcongr] theorem splitInputBudget_mono
    {n k n' k' : Nat} (hn : n ≤ n') (hk : k ≤ k') :
    splitInputBudget n k ≤ splitInputBudget n' k' := by
  unfold splitInputBudget
  gcongr

@[gcongr] theorem SafeEdges_eraseBudget_mono
    {n n' : Nat} (hn : n ≤ n') :
    SafeEdges.eraseBudget n ≤ SafeEdges.eraseBudget n' := by
  unfold SafeEdges.eraseBudget
  gcongr

@[gcongr] theorem SafeEdges_testBudget_mono
    {n k B n' k' B' : Nat} (hn : n ≤ n') (hk : k ≤ k') (hB : B ≤ B') :
    SafeEdges.testBudget n k B ≤ SafeEdges.testBudget n' k' B' := by
  unfold SafeEdges.testBudget
  gcongr

@[gcongr] theorem SafeEdges_chooseBudget_mono
    {n k B n' k' B' : Nat} (hn : n ≤ n') (hk : k ≤ k') (hB : B ≤ B') :
    SafeEdges.chooseBudget n k B ≤ SafeEdges.chooseBudget n' k' B' := by
  unfold SafeEdges.chooseBudget
  gcongr

@[gcongr] theorem WordInstance_reduceInputBudget_mono
    {n k B n' k' B' : Nat} (hn : n ≤ n') (hk : k ≤ k') (hB : B ≤ B') :
    WordInstance.reduceInputBudget n k B ≤ WordInstance.reduceInputBudget n' k' B' := by
  unfold WordInstance.reduceInputBudget
  gcongr

@[gcongr] theorem rootNeighborBudget_mono
    {n k n' k' : Nat} (hn : n ≤ n') (hk : k ≤ k') :
    rootNeighborBudget n k ≤ rootNeighborBudget n' k' := by
  unfold rootNeighborBudget
  gcongr

@[gcongr] theorem TransportNetwork_matrixWordsBudget_mono
    {l r B l' r' B' : Nat} (hl : l ≤ l') (hr : r ≤ r') (hB : B ≤ B') :
    TransportNetwork.matrixWordsBudget l r B ≤ TransportNetwork.matrixWordsBudget l' r' B' := by
  unfold TransportNetwork.matrixWordsBudget
  gcongr

@[gcongr] theorem TransportNetwork_pickBudget_mono
    {r B r' B' : Nat} (hr : r ≤ r') (hB : B ≤ B') :
    TransportNetwork.pickBudget r B ≤ TransportNetwork.pickBudget r' B' := by
  unfold TransportNetwork.pickBudget
  gcongr

@[gcongr] theorem TransportNetwork_matchingWitnessBudget_mono
    {l r l' r' : Nat} (hl : l ≤ l') (hr : r ≤ r') :
    TransportNetwork.matchingWitnessBudget l r ≤ TransportNetwork.matchingWitnessBudget l' r' := by
  unfold TransportNetwork.matchingWitnessBudget
  gcongr
  exact TransportNetwork_matrixWordsBudget_mono hl hr (Nat.le_refl 1)

@[gcongr] theorem SaturationPrune_iterationBudget_mono
    {l r l' r' : Nat} (hl : l ≤ l') (hr : r ≤ r') :
    SaturationPrune.iterationBudget l r ≤ SaturationPrune.iterationBudget l' r' := by
  unfold SaturationPrune.iterationBudget
  gcongr
  exact TransportNetwork_matrixBudget_mono hl hr (Nat.le_refl 1)

@[gcongr] theorem prunedSetBudget_mono
    {k n k' n' : Nat} (hk : k ≤ k') (hn : n ≤ n') :
    prunedSetBudget k n ≤ prunedSetBudget k' n' := by
  unfold prunedSetBudget
  gcongr

@[gcongr] theorem roundAssignmentBudget_mono
    {n k n' k' : Nat} (hn : n ≤ n') (hk : k ≤ k') :
    roundAssignmentBudget n k ≤ roundAssignmentBudget n' k' := by
  unfold roundAssignmentBudget
  gcongr

@[gcongr] theorem roundDataBudget_mono
    {n k n' k' : Nat} (hn : n ≤ n') (hk : k ≤ k') :
    roundDataBudget n k ≤ roundDataBudget n' k' := by
  unfold roundDataBudget
  gcongr

@[gcongr] theorem roundShapeBudget_mono
    {n k n' k' : Nat} (hn : n ≤ n') (hk : k ≤ k') :
    WordInstance.roundShapeBudget n k ≤ WordInstance.roundShapeBudget n' k' := by
  unfold WordInstance.roundShapeBudget
  gcongr

@[gcongr] theorem soleBudget_mono
    {n k n' k' : Nat} (hn : n ≤ n') (hk : k ≤ k') :
    soleBudget n k ≤ soleBudget n' k' := by
  unfold soleBudget
  gcongr

@[gcongr] theorem ComputedReindex_eraseIndexBudget_mono
    {m m' : Nat} (hm : m ≤ m') :
    ComputedReindex.eraseIndexBudget m ≤ ComputedReindex.eraseIndexBudget m' := by
  unfold ComputedReindex.eraseIndexBudget
  gcongr

@[gcongr] theorem WordInstance_projectBudget_mono
    {m j m' j' : Nat} (hm : m ≤ m') (hj : j ≤ j') :
    WordInstance.projectBudget m j ≤ WordInstance.projectBudget m' j' := by
  unfold WordInstance.projectBudget
  gcongr

@[gcongr] theorem WordInstance_contractStepBudget_mono
    {m k B m' k' B' : Nat} (hm : m ≤ m') (hk : k ≤ k') (hB : B ≤ B') :
    WordInstance.contractStepBudget m k B ≤ WordInstance.contractStepBudget m' k' B' := by
  unfold WordInstance.contractStepBudget
  gcongr

@[gcongr] theorem WordInstance_terminalStepBudget_mono
    {m l m' l' : Nat} (hm : m ≤ m') (hl : l ≤ l') :
    WordInstance.terminalStepBudget m l ≤ WordInstance.terminalStepBudget m' l' := by
  unfold WordInstance.terminalStepBudget
  gcongr

@[gcongr] theorem WordInstance_remainingStepBudget_mono
    {n m l n' m' l' : Nat} (hn : n ≤ n') (hm : m ≤ m') (hl : l ≤ l') :
    WordInstance.remainingStepBudget n m l ≤ WordInstance.remainingStepBudget n' m' l' := by
  unfold WordInstance.remainingStepBudget
  gcongr

end GyoriLovasz.BudgetMonotonicity
