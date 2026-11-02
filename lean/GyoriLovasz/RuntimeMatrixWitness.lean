import GyoriLovasz.RuntimeWordTransport

namespace GyoriLovasz.TransportNetwork
open Flow Binary
open scoped BigOperators

def matrixWords (allowed : Vector (Vector Bool r) l) (supply : Vector (List Bool) l)
    (capacity : Vector (List Bool) r) (B : Nat) :
    Costed.Computation (Vector (Vector (List Bool) r) l) :=
  let built := build allowed supply capacity
  let solved := maxFlowWords built.1 0 sinkNode (B + l + r + 2)
  let result := Costed.tabulate l (fun i => Costed.tabulate r
    (fun j => (solved.1.flow[(cellArc i j).succ.val], 5)))
  (result.1, built.2 + solved.2 + result.2 + 2)

theorem matrixWords_correct (allowed : Vector (Vector Bool r) l) (supply : Vector (List Bool) l)
    (capacity : Vector (List Bool) r) (B : Nat)
    (sb : ∀ i : Fin l, supply[i.val].length ≤ B) (cb : ∀ j : Fin r, capacity[j.val].length ≤ B)
    (existsMatrix : ∃ x, MatrixFeasible (fun i j => allowed[i.val][j.val]) (fun i => value supply[i.val])
      (fun j => value capacity[j.val]) x) :
    MatrixFeasible (fun i j => allowed[i.val][j.val]) (fun i => value supply[i.val])
      (fun j => value capacity[j.val]) (fun i j => value (matrixWords allowed supply capacity B).1[i.val][j.val]) := by
  have h := maxFlowWords_correct (build allowed supply capacity).1 (build_codes allowed supply capacity)
    0 sinkNode (Ne.symm sink_ne_zero) (B + l + r + 2) (build_bounds allowed supply capacity B sb cb)
  rw [build_network] at h
  have full := (maximum_flow_decides_matrix _ _ _ _ _ _ h.1 h.2).mp existsMatrix
  have feasible := h.1
  rw [full] at feasible
  have result := full_flow_matrix _ _ _ _ _ feasible
  simpa only [matrixWords, Costed.tabulate_value, decodeFlow] using result

theorem matrixWords_length (allowed : Vector (Vector Bool r) l) (supply : Vector (List Bool) l)
    (capacity : Vector (List Bool) r) (B : Nat)
    (sb : ∀ i : Fin l, supply[i.val].length ≤ B) (cb : ∀ j : Fin r, capacity[j.val].length ≤ B)
    (i : Fin l) (j : Fin r) :
    (matrixWords allowed supply capacity B).1[i.val][j.val].length ≤
      maxFlowWordLength (l + r + 2) (l + (l * r + r)) (B + l + r + 2) := by
  have h := ((maxFlowWords_bounds (build allowed supply capacity).1 (build_codes allowed supply capacity)
    0 sinkNode (B + l + r + 2) (build_bounds allowed supply capacity B sb cb)).1 (cellArc i j).succ).2.1
  simpa only [matrixWords, Costed.tabulate_value] using h

def matrixWordsBudget (l r B : Nat) := buildBudget l r +
  maxFlowBudget (l + r + 2) (l + (l * r + r)) (B + l + r + 2) +
    (2 * l * l + l * (2 * r * r + 11 * r + 9) + 3) + 2

set_option maxHeartbeats 800000 in
theorem matrixWords_cost (allowed : Vector (Vector Bool r) l) (supply : Vector (List Bool) l)
    (capacity : Vector (List Bool) r) (B : Nat)
    (sb : ∀ i : Fin l, supply[i.val].length ≤ B) (cb : ∀ j : Fin r, capacity[j.val].length ≤ B) :
    (matrixWords allowed supply capacity B).2 ≤ matrixWordsBudget l r B := by
  have hb := build_cost allowed supply capacity
  have hs := maxFlowWords_cost (build allowed supply capacity).1 (build_codes allowed supply capacity)
    0 sinkNode (B + l + r + 2) (build_bounds allowed supply capacity B sb cb)
  have ht := Costed.tabulate_cost l (fun i => Costed.tabulate r
    (fun j => ((maxFlowWords (build allowed supply capacity).1 0 sinkNode (B + l + r + 2)).1.flow[(cellArc i j).succ.val], 5)))
    (2 * r * r + r * (5 + 6) + 3) (fun i => Costed.tabulate_cost r _ 5 (by intros; rfl))
  dsimp only [matrixWords, matrixWordsBudget]
  norm_num only at ht
  simp only [Nat.mul_comm r 11, Nat.add_assoc] at hb hs ht ⊢
  norm_num only at ht
  omega

end GyoriLovasz.TransportNetwork
