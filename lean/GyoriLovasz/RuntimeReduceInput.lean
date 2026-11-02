import GyoriLovasz.RuntimeContractStep
import GyoriLovasz.RuntimeSoleNeighbor
import GyoriLovasz.RuntimeRoundSelection

namespace GyoriLovasz.WordInstance

def reduceInput (s : Input n k) (B : Nat) : Costed.Computation (Input n k) :=
  let reduced := SafeEdges.reduce s.graph s.roots s.weight s.capacity B
  ({s with graph := reduced.1}, reduced.2 + 1)

theorem reduceInput_subgraph (s : Input n k) (B bound : Nat) (wb : Bounded s B) (h : Valid s bound) :
    ∀ x y, relation (reduceInput s B).1 x y → relation s x y := by
  have result := SafeEdges.run_correct s.roots s.weight s.capacity B wb.1 wb.2 (n * n) s.graph
    (edgeCount_le_square _) h.split
  exact result.1

theorem reduceInput_valid (s : Input n k) (B bound : Nat) (wb : Bounded s B) (h : Valid s bound) :
    Valid (reduceInput s B).1 bound := by
  have result := SafeEdges.run_correct s.roots s.weight s.capacity B wb.1 wb.2 (n * n) s.graph
    (edgeCount_le_square _) h.split
  exact ⟨h.injective, h.rootzero, h.boundPositive, h.weightBounds, result.2.1⟩

theorem reduceInput_bounds (s : Input n k) (B : Nat) (h : Bounded s B) : Bounded (reduceInput s B).1 B := h

theorem reduceInput_no_sole (s : Input n k) (B bound : Nat) (wb : Bounded s B) (h : Valid s bound)
    (hk : 0 < k) (none : (findSole (reduceInput s B).1.graph s.roots).1 = none) :
    ¬TransportNetwork.Saturates
      (fun i v => (rootNeighbors (reduceInput s B).1.graph s.roots).1[i.val][v.val]) (fun _ => true) := by
  have result := SafeEdges.reduce_correct s.graph s.roots s.weight s.capacity B wb.1 wb.2 hk h.split
  have no := findSole_none (reduceInput s B).1.graph s.roots none
  have failure := result.2.2.resolve_left no
  exact fun sat => failure ((root_matching_iff (reduceInput s B).1.graph s.roots).mp sat)

theorem reduceInput_restore (s : Input n k) (B bound : Nat) (wb : Bounded s B) (h : Valid s bound)
    (labels : Vector (Fin k) n)
    (part : WeightedPartitionOn Finset.univ Finset.univ (relation (reduceInput s B).1)
      (root (reduceInput s B).1) (weights (reduceInput s B).1)
      (fun i => capacities (reduceInput s B).1 i + bound - 1) (fun v => labels[v.val])) :
    WeightedPartitionOn Finset.univ Finset.univ (relation s) (root s) (weights s)
      (fun i => capacities s i + bound - 1) (fun v => labels[v.val]) :=
  part.mono_edges (reduceInput_subgraph s B bound wb h)

def reduceInputBudget (n k B : Nat) := n * n * (SafeEdges.chooseBudget n k B + SafeEdges.eraseBudget n + 3) + 2

theorem reduceInput_cost (s : Input n k) (B : Nat) (h : Bounded s B) :
    (reduceInput s B).2 ≤ reduceInputBudget n k B := by
  have hr := SafeEdges.reduce_cost s.graph s.roots s.weight s.capacity B h.1 h.2
  dsimp only [reduceInput, reduceInputBudget]
  omega

end GyoriLovasz.WordInstance
