import GyoriLovasz.RuntimeTerminalStep

namespace GyoriLovasz.WordInstance

def restoreTerminal (p : Fin (m + 1)) (i : Fin (l + 1)) (reverse : Vector (Fin m) (m + 1))
    (labels : Vector (Fin l) m) : Costed.Computation (Vector (Fin (l + 1)) (m + 1)) :=
  Costed.tabulate (m + 1) (fun v => (if v = p then i else i.succAbove labels[reverse[v.val].val], 6))

theorem restoreTerminal_value (p : Fin (m + 1)) (i : Fin (l + 1)) (reverse : Vector (Fin m) (m + 1))
    (labels : Vector (Fin l) m) :
    (fun v : Fin (m + 1) => (restoreTerminal p i reverse labels).1[v.val]) =
      restoreLabel (fun v => i.succAbove labels[reverse[v.val].val]) p i := by
  funext v
  simp only [restoreTerminal, Costed.tabulate_value, restoreLabel]

theorem restoreTerminal_cost (p : Fin (m + 1)) (i : Fin (l + 1)) (reverse : Vector (Fin m) (m + 1))
    (labels : Vector (Fin l) m) :
    (restoreTerminal p i reverse labels).2 ≤ 2 * (m + 1) * (m + 1) + 12 * (m + 1) + 3 := by
  simpa only [Nat.mul_comm (m + 1) 12] using Costed.tabulate_cost (m + 1)
    (fun v => (if v = p then i else i.succAbove labels[reverse[v.val].val], 6)) 6 (by intros; rfl)

theorem terminalStep_restore (s : Input (m + 1) (l + 1)) (i : Fin (l + 1)) (positive : 0 < m)
    (positiveRoots : 0 < l) (bound : Nat) (h : Valid s bound) (labels : Vector (Fin l) m)
    (part : WeightedPartitionOn Finset.univ Finset.univ (relation (terminalStep s i positive).1.1)
      (root (terminalStep s i positive).1.1) (weights (terminalStep s i positive).1.1)
      (fun j => capacities (terminalStep s i positive).1.1 j + bound - 1) (fun v => labels[v.val])) :
    WeightedPartitionOn Finset.univ Finset.univ (relation s) (root s) (weights s)
      (fun j => capacities s j + bound - 1)
      (fun v => (restoreTerminal (root s i) i (terminalStep s i positive).1.2 labels).1[v.val]) := by
  classical
  have reindex := ComputedReindex.eraseIndex_graph (root s i) positive (DeleteVertex (relation s) (root s i))
    (WithoutTerminal (RootSet (root s)) (root s i)) (fun _ _ he => he.2) (fun he => he.2 rfl)
  have reindexJ := ComputedReindex.eraseIndex_graph i positiveRoots (fun _ _ => False) (fun _ => False)
    (fun _ _ he => False.elim he) (fun he => he)
  have rootmem (j : Fin l) : root s (i.succAbove j) ∈ (List.finRange (m + 1)).erase (root s i) :=
    reindex.terminals _ ⟨⟨i.succAbove j, rfl⟩, fun he => Fin.succAbove_ne i j (h.injective he)⟩
  rw [terminalStep_graph, terminalStep_roots, terminalStep_weights, terminalStep_capacities] at part
  have lifted := weighted_partition_reindex (limit := fun j => capacities s j + bound - 1)
    reindex Fin.succAbove_right_injective rootmem part
  have image := reindexJ.image_univ.trans (finRange_erase_toFinset i)
  rw [finRange_erase_toFinset, image] at lifted
  have restored := weighted_reconstruct_terminal (Finset.mem_univ _) (Finset.mem_univ _) (h.rootzero i) lifted
  rw [restoreTerminal_value]
  exact restored

end GyoriLovasz.WordInstance
