import GyoriLovasz.RuntimeWordSolver
import Mathlib.Algebra.BigOperators.Fin

namespace GyoriLovasz.Flow
open scoped BigOperators

/-- A directed source-to-sink flow with explicitly recorded throughput.
The conservation equation also covers the source and sink. -/
def STFeasible (G : Network n m) (source sink : Fin n) (f : Fin m → Nat) (amount : Nat) : Prop :=
  (∀ e, f e ≤ G.capacity e) ∧
  ∀ v : Fin n,
    (∑ e, if G.tail e = v then (f e : Int) else 0) + (if sink = v then (amount : Int) else 0) =
      (∑ e, if G.head e = v then (f e : Int) else 0) + (if source = v then (amount : Int) else 0)

/-- One return arc turns throughput maximization into minimum-cost circulation.
The original network's costs are intentionally replaced by zero. -/
def throughputNetwork (G : Network n m) (source sink : Fin n) (limit : Nat) : Network n (m + 1) where
  tail := Fin.cases sink G.tail
  head := Fin.cases source G.head
  capacity := Fin.cases limit G.capacity
  cost := Fin.cases (-1) (fun _ => 0)

def closeFlow (f : Fin m → Nat) (amount : Nat) : Fin (m + 1) → Nat := Fin.cases amount f

theorem closeFlow_feasible (G : Network n m) (source sink : Fin n) (limit : Nat)
    (f : Fin m → Nat) (amount : Nat) :
    Feasible (throughputNetwork G source sink limit) (closeFlow f amount) ↔
      amount ≤ limit ∧ STFeasible G source sink f amount := by
  constructor
  · intro h
    refine ⟨h.1 0, (fun e => h.1 e.succ), ?_⟩
    intro v
    have h := h.2 v
    simpa [throughputNetwork, closeFlow, Fin.sum_univ_succ, add_comm] using h
  · rintro ⟨limitBound, cap, balance⟩
    constructor
    · intro e
      refine Fin.cases ?_ ?_ e
      · exact limitBound
      · intro i; exact cap i
    · intro v
      simpa [throughputNetwork, closeFlow, Fin.sum_univ_succ, add_comm] using balance v

theorem closeFlow_cost (G : Network n m) (source sink : Fin n) (limit : Nat)
    (f : Fin m → Nat) (amount : Nat) :
    totalCost (throughputNetwork G source sink limit) (closeFlow f amount) = -(amount : Int) := by
  simp [totalCost, throughputNetwork, closeFlow, Fin.sum_univ_succ]

theorem closeFlow_restrict (f : Fin (m + 1) → Nat) : closeFlow (fun e => f e.succ) (f 0) = f := by
  funext e
  refine Fin.cases ?_ ?_ e <;> intros <;> rfl

/-- An optimal circulation in the return-arc network is a maximum throughput
flow among all flows with throughput at most the return-arc capacity. -/
theorem minimumCost_maximumFlow (G : Network n m) (source sink : Fin n) (limit : Nat)
    (f : Fin (m + 1) → Nat)
    (feasible : Feasible (throughputNetwork G source sink limit) f)
    (optimal : ∀ other, Feasible (throughputNetwork G source sink limit) other →
      totalCost (throughputNetwork G source sink limit) f ≤
        totalCost (throughputNetwork G source sink limit) other) :
    STFeasible G source sink (fun e => f e.succ) (f 0) ∧
      ∀ other amount, STFeasible G source sink other amount → amount ≤ limit → amount ≤ f 0 := by
  have hf : Feasible (throughputNetwork G source sink limit) (closeFlow (fun e => f e.succ) (f 0)) := by
    rw [closeFlow_restrict]; exact feasible
  refine ⟨((closeFlow_feasible G source sink limit _ _).mp hf).2, ?_⟩
  intro other amount good bounded
  have h := optimal (closeFlow other amount) ((closeFlow_feasible G source sink limit _ _).mpr ⟨bounded, good⟩)
  have cost : totalCost (throughputNetwork G source sink limit) f = -(f 0 : Int) := by
    rw [← closeFlow_restrict f]
    exact closeFlow_cost G source sink limit _ _
  rw [cost, closeFlow_cost] at h
  omega

theorem throughput_le_capacity_sum (G : Network n m) (source sink : Fin n) (distinct : source ≠ sink)
    (f : Fin m → Nat) (amount : Nat) (feasible : STFeasible G source sink f amount) :
    amount ≤ ∑ e, G.capacity e := by
  have balance := feasible.2 source
  simp only [Ne.symm distinct, if_false, if_true, add_zero] at balance
  have incoming : 0 ≤ ∑ e, if G.head e = source then (f e : Int) else 0 :=
    Finset.sum_nonneg (fun e _ => by split <;> omega)
  have outgoing : (∑ e, if G.tail e = source then (f e : Int) else 0) ≤
      ∑ e, (G.capacity e : Int) := by
    apply Finset.sum_le_sum
    intro e _
    have h := feasible.1 e
    split <;> omega
  have cast : (∑ e, (G.capacity e : Int)) = ((∑ e, G.capacity e : Nat) : Int) := by simp
  rw [cast] at outgoing
  omega

theorem minimumCost_unboundedMaximumFlow (G : Network n m) (source sink : Fin n)
    (distinct : source ≠ sink) (limit : Nat) (large : (∑ e, G.capacity e) ≤ limit)
    (f : Fin (m + 1) → Nat)
    (feasible : Feasible (throughputNetwork G source sink limit) f)
    (optimal : ∀ other, Feasible (throughputNetwork G source sink limit) other →
      totalCost (throughputNetwork G source sink limit) f ≤
        totalCost (throughputNetwork G source sink limit) other) :
    STFeasible G source sink (fun e => f e.succ) (f 0) ∧
      ∀ other amount, STFeasible G source sink other amount → amount ≤ f 0 := by
  have h := minimumCost_maximumFlow G source sink limit f feasible optimal
  exact ⟨h.1, fun other amount hf => h.2 other amount hf
    (Nat.le_trans (throughput_le_capacity_sum G source sink distinct other amount hf) large)⟩

end GyoriLovasz.Flow
