import GyoriLovasz.RuntimeRewardFlow

namespace GyoriLovasz.TransportNetwork
open Flow
open scoped BigOperators

def leftNode (i : Fin l) : Fin (l + r + 2) := (Fin.castAdd r i).succ.succ
def rightNode (j : Fin r) : Fin (l + r + 2) := (Fin.natAdd l j).succ.succ
def sinkNode : Fin (l + r + 2) := (0 : Fin (l + r + 1)).succ

@[simp] theorem left_eq_left (i j : Fin l) : (leftNode i : Fin (l + r + 2)) = leftNode j ↔ i = j := by
  simp [leftNode]
@[simp] theorem right_eq_right (i j : Fin r) : (rightNode i : Fin (l + r + 2)) = rightNode j ↔ i = j := by
  simp [rightNode]
@[simp] theorem left_ne_right (i : Fin l) (j : Fin r) : (leftNode i : Fin (l + r + 2)) ≠ rightNode j := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [leftNode, rightNode] at hv
  omega
@[simp] theorem right_ne_left (j : Fin r) (i : Fin l) : (rightNode j : Fin (l + r + 2)) ≠ leftNode i :=
  Ne.symm (left_ne_right i j)
@[simp] theorem left_ne_zero (i : Fin l) : (leftNode i : Fin (l + r + 2)) ≠ 0 := Fin.succ_ne_zero _
@[simp] theorem right_ne_zero (j : Fin r) : (rightNode j : Fin (l + r + 2)) ≠ 0 := Fin.succ_ne_zero _
@[simp] theorem left_ne_sink (i : Fin l) : (leftNode i : Fin (l + r + 2)) ≠ sinkNode := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [leftNode, sinkNode] at hv
  omega
@[simp] theorem right_ne_sink (j : Fin r) : (rightNode j : Fin (l + r + 2)) ≠ sinkNode := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [rightNode, sinkNode] at hv
  omega
@[simp] theorem sink_ne_zero : (sinkNode : Fin (l + r + 2)) ≠ 0 := Fin.succ_ne_zero _

def network (allowed : Fin l → Fin r → Bool) (supply : Fin l → Nat) (capacity : Fin r → Nat)
    (cost : Fin l → Fin r → Int) : Network (l + r + 2) (l + (l * r + r)) where
  tail := Fin.addCases (fun _ => 0)
    (Fin.addCases (fun a => leftNode (finProdFinEquiv.symm a).1) rightNode)
  head := Fin.addCases leftNode
    (Fin.addCases (fun a => rightNode (finProdFinEquiv.symm a).2) (fun _ => sinkNode))
  capacity := Fin.addCases supply
    (Fin.addCases (fun a => if allowed (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2
      then supply (finProdFinEquiv.symm a).1 else 0) capacity)
  cost := Fin.addCases (fun _ => 0)
    (Fin.addCases (fun a => cost (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2) (fun _ => 0))

def supplyArc (i : Fin l) : Fin (l + (l * r + r)) := Fin.castAdd (l * r + r) i
def cellArc (i : Fin l) (j : Fin r) : Fin (l + (l * r + r)) :=
  Fin.natAdd l (Fin.castAdd r (finProdFinEquiv (i, j)))
def demandArc (j : Fin r) : Fin (l + (l * r + r)) := Fin.natAdd l (Fin.natAdd (l * r) j)

theorem sumPairIndex {α : Type*} [AddCommMonoid α] (f : Fin (l * r) → α) :
    (∑ a, f a) = ∑ i : Fin l, ∑ j : Fin r, f (finProdFinEquiv (i, j)) := by
  rw [← finProdFinEquiv.sum_comp f, Fintype.sum_prod_type]

theorem flow_left_balance (allowed : Fin l → Fin r → Bool) (supply : Fin l → Nat)
    (capacity : Fin r → Nat) (cost : Fin l → Fin r → Int)
    (f : Fin (l + (l * r + r)) → Nat) (amount : Nat)
    (feasible : STFeasible (network allowed supply capacity cost) 0 sinkNode f amount) (i : Fin l) :
    f (supplyArc i) = ∑ j : Fin r, f (cellArc i j) := by
  have h := feasible.2 (leftNode i)
  simp only [network, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right] at h
  simp only [sumPairIndex, Equiv.symm_apply_apply] at h
  simp [Ne.symm (left_ne_zero i), Ne.symm (left_ne_sink i), supplyArc, cellArc] at h
  exact_mod_cast h.symm

theorem flow_right_balance (allowed : Fin l → Fin r → Bool) (supply : Fin l → Nat)
    (capacity : Fin r → Nat) (cost : Fin l → Fin r → Int)
    (f : Fin (l + (l * r + r)) → Nat) (amount : Nat)
    (feasible : STFeasible (network allowed supply capacity cost) 0 sinkNode f amount) (j : Fin r) :
    f (demandArc j) = ∑ i : Fin l, f (cellArc i j) := by
  have h := feasible.2 (rightNode j)
  simp only [network, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right] at h
  simp only [sumPairIndex, Equiv.symm_apply_apply] at h
  simp [Ne.symm (right_ne_zero j), Ne.symm (right_ne_sink j), demandArc, cellArc] at h
  exact_mod_cast h

theorem flow_source_balance (allowed : Fin l → Fin r → Bool) (supply : Fin l → Nat)
    (capacity : Fin r → Nat) (cost : Fin l → Fin r → Int)
    (f : Fin (l + (l * r + r)) → Nat) (amount : Nat)
    (feasible : STFeasible (network allowed supply capacity cost) 0 sinkNode f amount) :
    (∑ i : Fin l, f (supplyArc i)) = amount := by
  have h := feasible.2 0
  simp only [network, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right] at h
  simp [supplyArc] at h
  exact_mod_cast h

def MatrixFeasible (allowed : Fin l → Fin r → Bool) (supply : Fin l → Nat) (capacity : Fin r → Nat)
    (x : Fin l → Fin r → Nat) : Prop :=
  (∀ i j, 0 < x i j → allowed i j = true) ∧
  (∀ i, ∑ j, x i j = supply i) ∧ (∀ j, ∑ i, x i j ≤ capacity j)

theorem full_flow_matrix (allowed : Fin l → Fin r → Bool) (supply : Fin l → Nat)
    (capacity : Fin r → Nat) (cost : Fin l → Fin r → Int)
    (f : Fin (l + (l * r + r)) → Nat)
    (feasible : STFeasible (network allowed supply capacity cost) 0 sinkNode f (∑ i, supply i)) :
    MatrixFeasible allowed supply capacity (fun i j => f (cellArc i j)) := by
  have caps (i : Fin l) : f (supplyArc i) ≤ supply i := by
    simpa [network, supplyArc] using feasible.1 (supplyArc i)
  have sum := flow_source_balance allowed supply capacity cost f _ feasible
  have saturated (i : Fin l) : f (supplyArc i) = supply i := by
    have h := Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin l))) => caps i)
    exact h.mp sum i (Finset.mem_univ i)
  refine ⟨?_, ?_, ?_⟩
  · intro i j positive
    dsimp only [cellArc] at positive
    have cap := feasible.1 (cellArc i j)
    simp only [network, cellArc, Fin.addCases_right, Fin.addCases_left, Equiv.symm_apply_apply] at cap
    cases h : allowed i j <;> simp_all
  · intro i
    rw [← flow_left_balance allowed supply capacity cost f _ feasible i]
    exact saturated i
  · intro j
    rw [← flow_right_balance allowed supply capacity cost f _ feasible j]
    simpa [network, demandArc] using feasible.1 (demandArc j)

def matrixFlow (x : Fin l → Fin r → Nat) : Fin (l + (l * r + r)) → Nat :=
  Fin.addCases (fun i => ∑ j, x i j)
    (Fin.addCases (fun a => x (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2) (fun j => ∑ i, x i j))

theorem matrix_full_flow (allowed : Fin l → Fin r → Bool) (supply : Fin l → Nat)
    (capacity : Fin r → Nat) (cost : Fin l → Fin r → Int) (x : Fin l → Fin r → Nat)
    (feasible : MatrixFeasible allowed supply capacity x) :
    STFeasible (network allowed supply capacity cost) 0 sinkNode (matrixFlow x) (∑ i, supply i) := by
  constructor
  · intro e
    refine Fin.addCases ?_ ?_ e
    · intro i
      simpa only [network, matrixFlow, Fin.addCases_left] using (feasible.2.1 i).le
    · intro a
      refine Fin.addCases ?_ ?_ a
      · intro ij
        simp only [network, matrixFlow, Fin.addCases_right, Fin.addCases_left]
        have hb : x (finProdFinEquiv.symm ij).1 (finProdFinEquiv.symm ij).2 ≤ supply (finProdFinEquiv.symm ij).1 := by
          rw [← feasible.2.1]
          exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ _)
        by_cases pos : 0 < x (finProdFinEquiv.symm ij).1 (finProdFinEquiv.symm ij).2
        · rw [if_pos (feasible.1 _ _ pos)]
          exact hb
        · have zero : x (finProdFinEquiv.symm ij).1 (finProdFinEquiv.symm ij).2 = 0 := by omega
          rw [zero]
          exact Nat.zero_le _
      · intro j
        simpa only [network, matrixFlow, Fin.addCases_right] using feasible.2.2 j
  · intro v
    refine Fin.cases ?_ (fun w => Fin.cases ?_ (fun z => Fin.addCases ?_ ?_ z) w) v
    · simp only [network, matrixFlow, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
      simp [feasible.2.1]
    · change (∑ e, if (network allowed supply capacity cost).tail e = sinkNode then (matrixFlow x e : Int) else 0) +
        (if sinkNode = (sinkNode : Fin (l + r + 2)) then (∑ i, supply i : Nat) else 0) =
        (∑ e, if (network allowed supply capacity cost).head e = sinkNode then (matrixFlow x e : Int) else 0) +
        (if (0 : Fin (l + r + 2)) = sinkNode then (∑ i, supply i : Nat) else 0)
      simp only [network, matrixFlow, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
      have sum : (∑ j, ∑ i, (x i j : Int)) = ∑ i, (supply i : Int) := by
        rw [Finset.sum_comm]
        simp [← Nat.cast_sum, feasible.2.1]
      simpa [Ne.symm (sink_ne_zero (l := l) (r := r)), ← Nat.cast_sum, feasible.2.1] using sum.symm
    · intro i
      change (∑ e, if (network allowed supply capacity cost).tail e = leftNode i then (matrixFlow x e : Int) else 0) +
        (if (sinkNode : Fin (l + r + 2)) = leftNode i then (∑ a, supply a : Nat) else 0) =
        (∑ e, if (network allowed supply capacity cost).head e = leftNode i then (matrixFlow x e : Int) else 0) +
        (if (0 : Fin (l + r + 2)) = leftNode i then (∑ a, supply a : Nat) else 0)
      simp only [network, matrixFlow, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
      simp only [sumPairIndex, Equiv.symm_apply_apply]
      simp [Ne.symm (left_ne_zero i), Ne.symm (left_ne_sink i)]
    · intro j
      change (∑ e, if (network allowed supply capacity cost).tail e = rightNode j then (matrixFlow x e : Int) else 0) +
        (if (sinkNode : Fin (l + r + 2)) = rightNode j then (∑ a, supply a : Nat) else 0) =
        (∑ e, if (network allowed supply capacity cost).head e = rightNode j then (matrixFlow x e : Int) else 0) +
        (if (0 : Fin (l + r + 2)) = rightNode j then (∑ a, supply a : Nat) else 0)
      simp only [network, matrixFlow, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
      simp only [sumPairIndex, Equiv.symm_apply_apply]
      simp [Ne.symm (right_ne_zero j), Ne.symm (right_ne_sink j)]

theorem flow_cost_matrix (allowed : Fin l → Fin r → Bool) (supply : Fin l → Nat)
    (capacity : Fin r → Nat) (cost : Fin l → Fin r → Int) (f : Fin (l + (l * r + r)) → Nat) :
    totalCost (network allowed supply capacity cost) f = ∑ i, ∑ j, cost i j * (f (cellArc i j) : Int) := by
  simp only [totalCost, network, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
  simp only [sumPairIndex, Equiv.symm_apply_apply]
  simp [cellArc]

theorem matrixFlow_cell (x : Fin l → Fin r → Nat) (i : Fin l) (j : Fin r) :
    matrixFlow x (cellArc i j) = x i j := by
  simp only [matrixFlow, cellArc, Fin.addCases_left, Fin.addCases_right, Equiv.symm_apply_apply]

theorem matrixFlow_cost (allowed : Fin l → Fin r → Bool) (supply : Fin l → Nat)
    (capacity : Fin r → Nat) (cost : Fin l → Fin r → Int) (x : Fin l → Fin r → Nat) :
    totalCost (network allowed supply capacity cost) (matrixFlow x) = ∑ i, ∑ j, cost i j * (x i j : Int) := by
  rw [flow_cost_matrix]
  simp only [matrixFlow_cell]

theorem flow_throughput_le_supply (allowed : Fin l → Fin r → Bool) (supply : Fin l → Nat)
    (capacity : Fin r → Nat) (cost : Fin l → Fin r → Int)
    (f : Fin (l + (l * r + r)) → Nat) (amount : Nat)
    (feasible : STFeasible (network allowed supply capacity cost) 0 sinkNode f amount) :
    amount ≤ ∑ i, supply i := by
  rw [← flow_source_balance allowed supply capacity cost f amount feasible]
  apply Finset.sum_le_sum
  intro i _
  simpa [network, supplyArc] using feasible.1 (supplyArc i)

theorem maximum_flow_decides_matrix (allowed : Fin l → Fin r → Bool) (supply : Fin l → Nat)
    (capacity : Fin r → Nat) (cost : Fin l → Fin r → Int)
    (f : Fin (l + (l * r + r)) → Nat) (amount : Nat)
    (feasible : STFeasible (network allowed supply capacity cost) 0 sinkNode f amount)
    (maximum : ∀ other a, STFeasible (network allowed supply capacity cost) 0 sinkNode other a → a ≤ amount) :
    (∃ x, MatrixFeasible allowed supply capacity x) ↔ amount = ∑ i, supply i := by
  constructor
  · rintro ⟨x, good⟩
    have h := maximum (matrixFlow x) _ (matrix_full_flow allowed supply capacity cost x good)
    have upper := flow_throughput_le_supply allowed supply capacity cost f amount feasible
    omega
  · intro eq
    subst amount
    exact ⟨_, full_flow_matrix allowed supply capacity cost f feasible⟩

end GyoriLovasz.TransportNetwork

