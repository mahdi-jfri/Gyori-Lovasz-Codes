import GyoriLovasz.RuntimeMaxFlow

namespace GyoriLovasz.Flow
open scoped BigOperators

def rewardNetwork (G : Network n m) (source sink : Fin n) (limit : Nat) (reward : Int) : Network n (m + 1) :=
  {throughputNetwork G source sink limit with cost := Fin.cases (-reward) G.cost}

theorem reward_closed_feasible (G : Network n m) (source sink : Fin n) (limit : Nat) (reward : Int)
    (f : Fin m → Nat) (amount : Nat) :
    Feasible (rewardNetwork G source sink limit reward) (closeFlow f amount) ↔
      amount ≤ limit ∧ STFeasible G source sink f amount :=
  closeFlow_feasible G source sink limit f amount

theorem reward_closed_cost (G : Network n m) (source sink : Fin n) (limit : Nat) (reward : Int)
    (f : Fin m → Nat) (amount : Nat) :
    totalCost (rewardNetwork G source sink limit reward) (closeFlow f amount) =
      totalCost G f - reward * (amount : Int) := by
  simp [totalCost, rewardNetwork, closeFlow, Fin.sum_univ_succ]
  ring

theorem nonnegative_totalCost (G : Network n m) (costs : ∀ e, 0 ≤ G.cost e) (f : Fin m → Nat) :
    0 ≤ totalCost G f :=
  Finset.sum_nonneg (fun e _ => mul_nonneg (costs e) (Int.natCast_nonneg _))

theorem totalCost_capacity_bound (G : Network n m) (costs : ∀ e, 0 ≤ G.cost e)
    (f : Fin m → Nat) (capacity : ∀ e, f e ≤ G.capacity e) :
    totalCost G f ≤ ∑ e, G.cost e * (G.capacity e : Int) := by
  apply Finset.sum_le_sum
  intro e _
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast capacity e) (costs e)

/-- A sufficiently large reward enforces the desired throughput while retaining
minimum original cost among all flows of that throughput. The feasible witness
is a logical hypothesis, not an input oracle to the circulation solver. -/
theorem reward_minCost_fullFlow (G : Network n m) (source sink : Fin n) (limit : Nat)
    (reward : Int) (positive : 0 < reward) (costs : ∀ e, 0 ≤ G.cost e)
    (existsFull : ∃ other, STFeasible G source sink other limit ∧ totalCost G other < reward)
    (f : Fin (m + 1) → Nat)
    (feasible : Feasible (rewardNetwork G source sink limit reward) f)
    (optimal : ∀ other, Feasible (rewardNetwork G source sink limit reward) other →
      totalCost (rewardNetwork G source sink limit reward) f ≤
        totalCost (rewardNetwork G source sink limit reward) other) :
    f 0 = limit ∧ STFeasible G source sink (fun e => f e.succ) limit ∧
      ∀ other, STFeasible G source sink other limit → totalCost G (fun e => f e.succ) ≤ totalCost G other := by
  have hf : Feasible (rewardNetwork G source sink limit reward) (closeFlow (fun e => f e.succ) (f 0)) := by
    rw [closeFlow_restrict]; exact feasible
  have hspec := (reward_closed_feasible G source sink limit reward _ _).mp hf
  have fcost : totalCost (rewardNetwork G source sink limit reward) f =
      totalCost G (fun e => f e.succ) - reward * (f 0 : Int) := by
    rw [← closeFlow_restrict f]
    exact reward_closed_cost G source sink limit reward _ _
  have full : f 0 = limit := by
    obtain ⟨other, good, small⟩ := existsFull
    have ho := optimal (closeFlow other limit)
      ((reward_closed_feasible G source sink limit reward _ _).mpr ⟨Nat.le_refl _, good⟩)
    rw [fcost, reward_closed_cost] at ho
    have nonneg := nonnegative_totalCost G costs (fun e => f e.succ)
    by_contra ne
    have less : (f 0 : Int) + 1 ≤ (limit : Int) := by omega
    have scaled := mul_le_mul_of_nonneg_left less positive.le
    rw [mul_add, mul_one] at scaled
    omega
  refine ⟨full, full ▸ hspec.2, ?_⟩
  intro other good
  have ho := optimal (closeFlow other limit)
    ((reward_closed_feasible G source sink limit reward _ _).mpr ⟨Nat.le_refl _, good⟩)
  rw [fcost, reward_closed_cost, full] at ho
  omega

end GyoriLovasz.Flow
