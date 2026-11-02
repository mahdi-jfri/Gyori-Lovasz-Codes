import GyoriLovasz.RuntimeRemainingStep
import GyoriLovasz.RuntimeGlue

namespace GyoriLovasz.WordInstance

def remainingLift (shape : Shape n k) (reverse : Vector (Fin shape.verticesCount) n)
    (labels : Vector (Fin shape.rootsCount) shape.verticesCount) : Costed.Computation (Vector (Fin k) n) :=
  Costed.tabulate n (fun v => (shape.indices[labels[reverse[v.val].val].val], 4))

theorem remainingLift_cost (shape : Shape n k) (reverse : Vector (Fin shape.verticesCount) n)
    (labels : Vector (Fin shape.rootsCount) shape.verticesCount) :
    (remainingLift shape reverse labels).2 ≤ 2 * n * n + 10 * n + 3 := by
  simpa only [Nat.mul_comm n 10] using Costed.tabulate_cost n
    (fun v => (shape.indices[labels[reverse[v.val].val].val], 4)) 4 (by intros; rfl)

theorem remainingLift_correct (s : Input n k) (selected : Vector Bool k)
    (positive : 0 < (roundShape s selected).1.verticesCount)
    (positiveRoots : 0 < (roundShape s selected).1.rootsCount)
    (bound : Nat) (h : Valid s bound)
    (labels : Vector (Fin (roundShape s selected).1.rootsCount) (roundShape s selected).1.verticesCount)
    (part : WeightedPartitionOn Finset.univ Finset.univ (relation (remainingStep s (roundShape s selected).1 positive).1.1)
      (root (remainingStep s (roundShape s selected).1 positive).1.1)
      (weights (remainingStep s (roundShape s selected).1 positive).1.1)
      (fun j => capacities (remainingStep s (roundShape s selected).1 positive).1.1 j + bound - 1)
      (fun v => labels[v.val])) :
    WeightedPartitionOn (Finset.univ \ blockSet s selected) (Finset.univ \ selectedRoots selected)
      (relation s) (root s) (weights s) (fun j => capacities s j + bound - 1)
      (fun v => (remainingLift (roundShape s selected).1 (remainingStep s (roundShape s selected).1 positive).1.2 labels).1[v.val]) := by
  classical
  let shape := (roundShape s selected).1
  have reindex := remainingStep_reindex s selected positive
  have reindexJ := ComputedReindex.graphReindex shape.indices ⟨0, positiveRoots⟩
    (roundShape_indices_inj s selected) (fun _ _ => False) (fun _ => False)
    (fun _ _ he => False.elim he) (fun _ he => False.elim he)
  have dne (j : Fin shape.rootsCount) : shape.indices[j.val] ∉ selectedRoots selected := by
    have mem := reindexJ.image_mem j
    rw [roundShape_indices] at mem
    exact of_decide_eq_true (List.mem_filter.mp mem).2
  have rootmem (j : Fin shape.rootsCount) : root s shape.indices[j.val] ∈ GyoriLovasz.retain (List.finRange n) (blockSet s selected) := by
    apply reindex.terminals
    refine ⟨⟨shape.indices[j.val], rfl⟩, ?_⟩
    intro mem
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp mem
    exact dne j (h.injective he ▸ ha)
  rw [remainingStep_graph, roundShape_removed, remainingStep_roots, remainingStep_weights, remainingStep_capacities] at part
  have lifted := weighted_partition_reindex (limit := fun j => capacities s j + bound - 1)
    reindex (roundShape_indices_inj s selected) rootmem part
  have image := reindexJ.image_univ
  rw [roundShape_indices, retain_finRange_toFinset] at image
  rw [retain_finRange_toFinset, image] at lifted
  have original := lifted.mono_edges (fun _ _ he => he.1)
  simpa only [remainingLift, Costed.tabulate_value] using original

def restoreRemaining (shape : Shape n k) (reverse : Vector (Fin shape.verticesCount) n)
    (labels : Vector (Fin shape.rootsCount) shape.verticesCount) (rounded : Vector (Fin k) n) :
    Costed.Computation (Vector (Fin k) n) :=
  let lifted := remainingLift shape reverse labels
  let joined := joinLabels shape.removed lifted.1 rounded
  (joined.1, lifted.2 + joined.2 + 1)

theorem restoreRemaining_cost (shape : Shape n k) (reverse : Vector (Fin shape.verticesCount) n)
    (labels : Vector (Fin shape.rootsCount) shape.verticesCount) (rounded : Vector (Fin k) n) :
    (restoreRemaining shape reverse labels rounded).2 ≤ 4 * n * n + 20 * n + 7 := by
  have hl := remainingLift_cost shape reverse labels
  have hj := joinLabels_cost shape.removed (remainingLift shape reverse labels).1 rounded
  dsimp only [restoreRemaining]
  rw [show 4 * n * n = 2 * (2 * n * n) by ring]
  omega

theorem remainingStep_restore (s : Input n k) (selected : Vector Bool k)
    (positive : 0 < (roundShape s selected).1.verticesCount)
    (positiveRoots : 0 < (roundShape s selected).1.rootsCount)
    (bound : Nat) (h : Valid s bound)
    (labels : Vector (Fin (roundShape s selected).1.rootsCount) (roundShape s selected).1.verticesCount)
    (rounded : Vector (Fin k) n)
    (parts : WeightedPartitionOn (blockSet s selected) (selectedRoots selected) (relation s) (root s)
      (weights s) (fun j => capacities s j + bound - 1) (fun v => rounded[v.val]))
    (part : WeightedPartitionOn Finset.univ Finset.univ (relation (remainingStep s (roundShape s selected).1 positive).1.1)
      (root (remainingStep s (roundShape s selected).1 positive).1.1)
      (weights (remainingStep s (roundShape s selected).1 positive).1.1)
      (fun j => capacities (remainingStep s (roundShape s selected).1 positive).1.1 j + bound - 1)
      (fun v => labels[v.val])) :
    WeightedPartitionOn Finset.univ Finset.univ (relation s) (root s) (weights s)
      (fun j => capacities s j + bound - 1)
      (fun v => (restoreRemaining (roundShape s selected).1
        (remainingStep s (roundShape s selected).1 positive).1.2 labels rounded).1[v.val]) := by
  have lifted := remainingLift_correct s selected positive positiveRoots bound h labels part
  have result := joinLabels_correct (roundShape s selected).1.removed
    (remainingLift (roundShape s selected).1 (remainingStep s (roundShape s selected).1 positive).1.2 labels).1
    rounded (relation s) (root s) (weights s) (fun j => capacities s j + bound - 1) (selectedRoots selected)
    (by simpa only [roundShape_removed] using lifted) (by simpa only [roundShape_removed] using parts)
  exact result

end GyoriLovasz.WordInstance
