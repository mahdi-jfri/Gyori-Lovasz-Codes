import GyoriLovasz.RuntimeContractStep

namespace GyoriLovasz.WordInstance

def terminalStep (s : Input (m + 1) (l + 1)) (i : Fin (l + 1)) (positive : 0 < m) :
    Costed.Computation (Input m l × Vector (Fin m) (m + 1)) :=
  let reverse := ComputedReindex.eraseIndex (root s i) positive
  let graph := Costed.tabulate₂ m (fun x y =>
    (s.graph[((root s i).succAbove x).val][((root s i).succAbove y).val], 3))
  let roots := Costed.tabulate l (fun j => (reverse.1[(root s (i.succAbove j)).val], 4))
  let weight := Costed.tabulate m (fun x => (s.weight[((root s i).succAbove x).val], 2))
  let capacity := Costed.tabulate l (fun j => (s.capacity[(i.succAbove j).val], 2))
  ((⟨graph.1, roots.1, weight.1, capacity.1⟩, reverse.1),
    reverse.2 + graph.2 + roots.2 + weight.2 + capacity.2 + 4)

theorem terminalStep_graph (s : Input (m + 1) (l + 1)) (i : Fin (l + 1)) (positive : 0 < m) :
    relation (terminalStep s i positive).1.1 =
      fun x y => DeleteVertex (relation s) (root s i) ((root s i).succAbove x) ((root s i).succAbove y) := by
  funext x y
  simp only [relation, terminalStep, Costed.tabulate₂_value, DeleteVertex,
    Fin.succAbove_ne (root s i) x, Fin.succAbove_ne (root s i) y, and_true]
  apply propext
  exact ⟨fun h => ⟨h, Fin.succAbove_ne (root s i) x, Fin.succAbove_ne (root s i) y⟩, fun h => h.1⟩

theorem terminalStep_roots (s : Input (m + 1) (l + 1)) (i : Fin (l + 1)) (positive : 0 < m) :
    root (terminalStep s i positive).1.1 =
      fun j => (ComputedReindex.eraseIndex (root s i) positive).1[(root s (i.succAbove j)).val] := by
  funext j
  simp only [root, terminalStep, Costed.tabulate_value]

theorem terminalStep_weights (s : Input (m + 1) (l + 1)) (i : Fin (l + 1)) (positive : 0 < m) :
    weights (terminalStep s i positive).1.1 = fun x => weights s ((root s i).succAbove x) := by
  funext x
  simp only [weights, terminalStep, Costed.tabulate_value]

theorem terminalStep_capacities (s : Input (m + 1) (l + 1)) (i : Fin (l + 1)) (positive : 0 < m) :
    capacities (terminalStep s i positive).1.1 = fun j => capacities s (i.succAbove j) := by
  funext j
  simp only [capacities, terminalStep, Costed.tabulate_value]

theorem terminalStep_bounds (s : Input (m + 1) (l + 1)) (i : Fin (l + 1)) (positive : 0 < m)
    (B : Nat) (h : Bounded s B) : Bounded (terminalStep s i positive).1.1 B := by
  constructor
  · intro x
    simpa only [terminalStep, Costed.tabulate_value] using h.1 ((root s i).succAbove x)
  · intro j
    simpa only [terminalStep, Costed.tabulate_value] using h.2 (i.succAbove j)

theorem terminalStep_valid (s : Input (m + 1) (l + 1)) (i : Fin (l + 1)) (positive : 0 < m)
    (positiveRoots : 0 < l) (bound : Nat) (h : Valid s bound) (zero : capacities s i = 0) :
    Valid (terminalStep s i positive).1.1 bound := by
  obtain ⟨x, hx⟩ := h.split
  have reindex := ComputedReindex.eraseIndex_graph (root s i) positive (DeleteVertex (relation s) (root s i))
    (WithoutTerminal (RootSet (root s)) (root s i)) (fun _ _ he => he.2) (fun he => he.2 rfl)
  have reduced := weighted_terminal_reindexed h.injective hx zero
    (ComputedReindex.eraseIndex_inverse i positiveRoots) (ComputedReindex.eraseIndex_retract i positiveRoots)
    (Fin.succAbove_ne i) reindex
  have rootmem (j : Fin l) : root s (i.succAbove j) ∈ (List.finRange (m + 1)).erase (root s i) :=
    reindex.terminals _ ⟨⟨i.succAbove j, rfl⟩, fun he => Fin.succAbove_ne i j (h.injective he)⟩
  constructor
  · rw [terminalStep_roots]
    exact reduced.1
  · intro j
    rw [terminalStep_roots, terminalStep_weights]
    dsimp only
    rw [reindex.retract _ (rootmem j)]
    exact h.rootzero _
  · exact h.boundPositive
  · intro v hv
    rw [terminalStep_weights]
    apply h.weightBounds
    rintro ⟨a, ha⟩
    have ai : a ≠ i := by
      intro eq
      subst a
      exact Fin.succAbove_ne (root s i) v ha.symm
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq ai
    apply hv
    rw [terminalStep_roots]
    refine ⟨j, ?_⟩
    dsimp only
    rw [hj, ha, reindex.inverse]
  · rw [terminalStep_graph, terminalStep_roots, terminalStep_weights, terminalStep_capacities]
    exact ⟨_, reduced.2⟩

def terminalStepBudget (m l : Nat) := ComputedReindex.eraseIndexBudget m +
  (2 * m * m * m + m * m * 11 + 9 * m + 3) + (2 * l * l + 10 * l + 3) +
  (2 * m * m + 8 * m + 3) + (2 * l * l + 8 * l + 3) + 4

theorem terminalStep_cost (s : Input (m + 1) (l + 1)) (i : Fin (l + 1)) (positive : 0 < m) :
    (terminalStep s i positive).2 ≤ terminalStepBudget m l := by
  have hr := ComputedReindex.eraseIndex_cost (root s i) positive
  have hg := Costed.tabulate₂_cost m (fun x y =>
    (s.graph[((root s i).succAbove x).val][((root s i).succAbove y).val], 3)) 3 (by intros; rfl)
  have ht := Costed.tabulate_cost l
    (fun j => ((ComputedReindex.eraseIndex (root s i) positive).1[(root s (i.succAbove j)).val], 4)) 4 (by intros; rfl)
  have hw := Costed.tabulate_cost m (fun x => (s.weight[((root s i).succAbove x).val], 2)) 2 (by intros; rfl)
  have hc := Costed.tabulate_cost l (fun j => (s.capacity[(i.succAbove j).val], 2)) 2 (by intros; rfl)
  dsimp only [terminalStep, terminalStepBudget]
  norm_num only at hg ht hw hc
  simp only [Nat.mul_comm l 10, Nat.mul_comm m 8, Nat.mul_comm l 8] at ht hw hc
  omega

end GyoriLovasz.WordInstance
