import GyoriLovasz.RuntimeEraseIndex
import GyoriLovasz.RuntimeBasePartition

namespace GyoriLovasz.WordInstance
open Binary

def contractStep (s : Input (m + 1) k) (p : Fin (m + 1)) (i : Fin k) (positive : 0 < m) :
    Costed.Computation (Input m k × Vector (Fin m) (m + 1)) :=
  let reverse := ComputedReindex.eraseIndex p positive
  let graph := Costed.tabulate₂ m (fun x y =>
    (s.graph[(p.succAbove x).val][(p.succAbove y).val] ||
      (s.graph[(p.succAbove x).val][p.val] && decide (p.succAbove y = root s i)), 6))
  let roots := Costed.tabulate k (fun j => (reverse.1[(root s j).val], 3))
  let weight := Costed.tabulate m (fun x => (s.weight[(p.succAbove x).val], 2))
  let capacity := subtractCapacity s.capacity i s.weight[p.val]
  ((⟨graph.1, roots.1, weight.1, capacity.1⟩, reverse.1),
    reverse.2 + graph.2 + roots.2 + weight.2 + capacity.2 + 4)

theorem contractStep_graph (s : Input (m + 1) k) (p : Fin (m + 1)) (i : Fin k) (positive : 0 < m) :
    relation (contractStep s p i positive).1.1 =
      fun x y => Contract (relation s) p (root s i) (p.succAbove x) (p.succAbove y) := by
  funext x y
  simp only [relation, contractStep, Costed.tabulate₂_value, Contract, Fin.succAbove_ne p x, Fin.succAbove_ne p y,
    not_false_eq_true, true_and, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  apply propext
  exact ⟨fun h => ⟨Fin.succAbove_ne p x, Fin.succAbove_ne p y, h⟩, fun h => h.2.2⟩

theorem contractStep_roots (s : Input (m + 1) k) (p : Fin (m + 1)) (i : Fin k) (positive : 0 < m) :
    root (contractStep s p i positive).1.1 =
      fun j => (ComputedReindex.eraseIndex p positive).1[(root s j).val] := by
  funext j
  simp only [root, contractStep, Costed.tabulate_value]

theorem contractStep_weights (s : Input (m + 1) k) (p : Fin (m + 1)) (i : Fin k) (positive : 0 < m) :
    weights (contractStep s p i positive).1.1 = fun x => weights s (p.succAbove x) := by
  funext x
  simp only [weights, contractStep, Costed.tabulate_value]

theorem contractStep_capacities (s : Input (m + 1) k) (p : Fin (m + 1)) (i : Fin k) (positive : 0 < m)
    (fits : weights s p ≤ capacities s i) :
    capacities (contractStep s p i positive).1.1 =
      fun j => capacities s j - if j = i then weights s p else 0 := by
  funext j
  exact subtractCapacity_value s.capacity i j s.weight[p.val] fits

theorem contractStep_bounds (s : Input (m + 1) k) (p : Fin (m + 1)) (i : Fin k) (positive : 0 < m)
    (B : Nat) (h : Bounded s B) : Bounded (contractStep s p i positive).1.1 B := by
  constructor
  · intro x
    simpa only [contractStep, Costed.tabulate_value] using h.1 (p.succAbove x)
  · intro j
    simp only [contractStep, subtractCapacity, Costed.tabulate_value]
    exact subtractEntry_length s.capacity i j s.weight[p.val] B h.2 (h.1 p)

structure Valid (s : Input n k) (bound : Nat) : Prop where
  injective : Function.Injective (root s)
  rootzero : ∀ i, weights s (root s i) = 0
  boundPositive : 0 < bound
  weightBounds : ∀ v, ¬RootSet (root s) v → 0 < weights s v ∧ weights s v ≤ bound
  split : ∃ x, SplitFeasible (relation s) (root s) (weights s) (capacities s) x

theorem contractStep_valid (s : Input (m + 1) k) (p : Fin (m + 1)) (i : Fin k) (positive : 0 < m)
    (bound : Nat) (h : Valid s bound) (nt : ¬RootSet (root s) p) (edge : relation s p (root s i))
    (sole : ∀ y, relation s p y → y = root s i) : Valid (contractStep s p i positive).1.1 bound := by
  obtain ⟨x, hx⟩ := h.split
  have fits := (split_sole_neighbor h.injective hx nt edge sole).2.1
  have reindex := ComputedReindex.eraseIndex_graph p positive (Contract (relation s) p (root s i))
    (RootSet (root s)) (fun _ _ he => ⟨he.1, he.2.1⟩) nt
  have reduced := weighted_contraction_reindexed h.injective hx nt edge sole reindex
  constructor
  · rw [contractStep_roots]
    have inj := reindex_roots_injective reindex h.injective
    exact inj
  · intro j
    rw [contractStep_roots, contractStep_weights]
    dsimp only
    have mem := reindex.terminals (root s j) ⟨j, rfl⟩
    rw [reindex.retract _ mem]
    exact h.rootzero j
  · exact h.boundPositive
  · intro v hv
    rw [contractStep_weights]
    apply h.weightBounds
    intro ht
    apply hv
    rw [contractStep_roots]
    exact (reindex_rootSet reindex v).mp ht
  · rw [contractStep_graph, contractStep_roots, contractStep_weights, contractStep_capacities s p i positive fits]
    exact ⟨_, reduced⟩

def contractStepBudget (m k B : Nat) := ComputedReindex.eraseIndexBudget m +
  (2 * m * m * m + m * m * 14 + 9 * m + 3) + (2 * k * k + 9 * k + 3) +
  (2 * m * m + 8 * m + 3) + (2 * k * k + k * (9 * B + 10) + 3) + 4

theorem contractStep_cost (s : Input (m + 1) k) (p : Fin (m + 1)) (i : Fin k) (positive : 0 < m)
    (B : Nat) (h : Bounded s B) : (contractStep s p i positive).2 ≤ contractStepBudget m k B := by
  have hr := ComputedReindex.eraseIndex_cost p positive
  have hg := Costed.tabulate₂_cost m (fun x y =>
    (s.graph[(p.succAbove x).val][(p.succAbove y).val] ||
      (s.graph[(p.succAbove x).val][p.val] && decide (p.succAbove y = root s i)), 6)) 6 (by intros; rfl)
  have ht := Costed.tabulate_cost k
    (fun j => ((ComputedReindex.eraseIndex p positive).1[(root s j).val], 3)) 3 (by intros; rfl)
  have hw := Costed.tabulate_cost m (fun x => (s.weight[(p.succAbove x).val], 2)) 2 (by intros; rfl)
  have hc := subtractCapacity_cost s.capacity i s.weight[p.val] B h.2 (h.1 p)
  dsimp only [contractStep, contractStepBudget]
  norm_num only at hg ht hw
  simp only [Nat.mul_comm k 9, Nat.mul_comm m 8] at ht hw
  omega

end GyoriLovasz.WordInstance
