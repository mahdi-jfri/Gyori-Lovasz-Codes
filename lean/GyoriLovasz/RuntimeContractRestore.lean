import GyoriLovasz.RuntimeContractStep

namespace GyoriLovasz.WordInstance

def restoreContract (p : Fin (m + 1)) (i : Fin k) (reverse : Vector (Fin m) (m + 1))
    (labels : Vector (Fin k) m) : Costed.Computation (Vector (Fin k) (m + 1)) :=
  Costed.tabulate (m + 1) (fun v => (if v = p then i else labels[reverse[v.val].val], 5))

theorem restoreContract_value (p : Fin (m + 1)) (i : Fin k) (reverse : Vector (Fin m) (m + 1))
    (labels : Vector (Fin k) m) :
    (fun v : Fin (m + 1) => (restoreContract p i reverse labels).1[v.val]) =
      restoreLabel (fun v => labels[reverse[v.val].val]) p i := by
  funext v
  simp only [restoreContract, Costed.tabulate_value, restoreLabel]

theorem restoreContract_cost (p : Fin (m + 1)) (i : Fin k) (reverse : Vector (Fin m) (m + 1))
    (labels : Vector (Fin k) m) :
    (restoreContract p i reverse labels).2 ≤ 2 * (m + 1) * (m + 1) + 11 * (m + 1) + 3 := by
  simpa only [Nat.mul_comm (m + 1) 11] using Costed.tabulate_cost (m + 1)
    (fun v => (if v = p then i else labels[reverse[v.val].val], 5)) 5 (by intros; rfl)

theorem contractStep_restore (s : Input (m + 1) k) (p : Fin (m + 1)) (i : Fin k) (positive : 0 < m)
    (bound : Nat) (h : Valid s bound) (nt : ¬RootSet (root s) p) (edge : relation s p (root s i))
    (sole : ∀ y, relation s p y → y = root s i) (labels : Vector (Fin k) m)
    (part : WeightedPartitionOn Finset.univ Finset.univ (relation (contractStep s p i positive).1.1)
      (root (contractStep s p i positive).1.1) (weights (contractStep s p i positive).1.1)
      (fun j => capacities (contractStep s p i positive).1.1 j + bound - 1) (fun v => labels[v.val])) :
    WeightedPartitionOn Finset.univ Finset.univ (relation s) (root s) (weights s)
      (fun j => capacities s j + bound - 1)
      (fun v => (restoreContract p i (contractStep s p i positive).1.2 labels).1[v.val]) := by
  classical
  obtain ⟨x, hx⟩ := h.split
  have fits := (split_sole_neighbor h.injective hx nt edge sole).2.1
  have reindex := ComputedReindex.eraseIndex_graph p positive (Contract (relation s) p (root s i))
    (RootSet (root s)) (fun _ _ he => ⟨he.1, he.2.1⟩) nt
  rw [contractStep_graph, contractStep_roots, contractStep_weights, contractStep_capacities s p i positive fits] at part
  have lifted := weighted_partition_reindex (d := id)
    (limit := fun j => capacities s j - (if j = i then weights s p else 0) + bound - 1)
    reindex Function.injective_id (fun j => reindex.terminals (root s j) ⟨j, rfl⟩) part
  simp only [Finset.image_id, finRange_erase_toFinset, id_eq] at lifted
  have restored := weighted_reconstruct_contraction (Finset.mem_univ p) (Finset.mem_univ i) edge lifted
  have bounded := restored.mono_limit (b := fun j => capacities s j + bound - 1) (by
    intro j _
    by_cases ji : j = i
    · subst j
      simp only [if_pos rfl]
      exact weighted_contraction_bound fits h.boundPositive (Nat.le_refl _)
    · simp [ji, Ne.symm ji])
  rw [restoreContract_value]
  exact bounded

end GyoriLovasz.WordInstance
