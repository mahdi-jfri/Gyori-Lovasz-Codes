import GyoriLovasz.RuntimeMatrixWitness
import GyoriLovasz.RuntimeMatchingMatrix

namespace GyoriLovasz.TransportNetwork
open Binary Flow
open scoped BigOperators

def positiveWord (word : List Bool) : Bool × Nat :=
  let cmp := compareWords [] word
  (cmp.1.1, cmp.2 + 2)

theorem positiveWord_correct (word : List Bool) : (positiveWord word).1 = true ↔ 0 < value word := by
  simpa only [positiveWord, value] using (compareWords_correct [] word).1

theorem positiveWord_cost (word : List Bool) (B : Nat) (bound : word.length ≤ B) :
    (positiveWord word).2 ≤ 9 * B + 4 := by
  have h := compareWords_steps [] word
  simp only [List.length_nil, Nat.zero_max] at h
  dsimp only [positiveWord]
  omega

def pickRow (row : Vector (List Bool) r) : Costed.Computation (Option (Fin r)) :=
  let indices := Costed.enumerateIndices r
  let result := Costed.find (fun j => positiveWord row[j.val]) indices.1
  (result.1, indices.2 + result.2 + 1)

theorem pickRow_some (row : Vector (List Bool) r) (j : Fin r) (h : (pickRow row).1 = some j) :
    0 < value row[j.val] := by
  rw [pickRow, Costed.find_value] at h
  have yes := List.find?_some h
  exact (positiveWord_correct _).mp yes

theorem pickRow_exists (row : Vector (List Bool) r) (h : ∃ j : Fin r, 0 < value row[j.val]) :
    ∃ j, (pickRow row).1 = some j := by
  cases hr : (pickRow row).1 with
  | some j => exact ⟨j, rfl⟩
  | none =>
    rw [pickRow, Costed.find_value] at hr
    obtain ⟨j, hj⟩ := h
    have no := List.find?_eq_none.mp hr j (by simp [Costed.enumerateIndices_value])
    have yes := (positiveWord_correct _).mpr hj
    simp [yes] at no

def pickBudget (r B : Nat) := 2 * r * r + 2 * r + r * (9 * B + 7) + 3

theorem pickRow_cost (row : Vector (List Bool) r) (B : Nat) (bound : ∀ j : Fin r, row[j.val].length ≤ B) :
    (pickRow row).2 ≤ pickBudget r B := by
  have hi := Costed.enumerateIndices_cost r
  have hf := Costed.find_cost (fun j : Fin r => positiveWord row[j.val]) (Costed.enumerateIndices r).1
    (9 * B + 4) (fun j _ => positiveWord_cost _ B (bound j))
  simp only [Costed.enumerateIndices_value, List.length_finRange, Nat.add_assoc] at hf
  norm_num only at hf
  dsimp only [pickRow, pickBudget]
  simp only [Costed.enumerateIndices_value]
  omega

def pickMatrix (matrix : Vector (Vector (List Bool) r) l) : Costed.Computation (Vector (Option (Fin r)) l) :=
  Costed.tabulate l (fun i => pickRow matrix[i.val])

theorem pickMatrix_some (matrix : Vector (Vector (List Bool) r) l) (i : Fin l) (j : Fin r)
    (h : (pickMatrix matrix).1[i.val] = some j) : 0 < value matrix[i.val][j.val] := by
  rw [pickMatrix, Costed.tabulate_value] at h
  exact pickRow_some _ j h

theorem pickMatrix_correct (matrix : Vector (Vector (List Bool) r) l)
    (allowed : Fin l → Fin r → Bool) (selected : Fin l → Bool)
    (h : MatrixFeasible allowed (fun i => if selected i then 1 else 0) (fun _ => 1)
      (fun i j => value matrix[i.val][j.val])) :
    (∀ i, selected i = true → ∃ j, (pickMatrix matrix).1[i.val] = some j ∧ allowed i j = true) ∧
      (∀ (i a : Fin l) (j : Fin r), (pickMatrix matrix).1[i.val] = some j → (pickMatrix matrix).1[a.val] = some j → i = a) := by
  classical
  constructor
  · intro i hi
    have positive : ∃ j : Fin r, 0 < value matrix[i.val][j.val] := by
      by_contra hn
      have zero : ∀ j : Fin r, value matrix[i.val][j.val] = 0 := by
        intro j
        have no : ¬0 < value matrix[i.val][j.val] := fun hp => hn ⟨j, hp⟩
        omega
      have row := h.2.1 i
      simp [hi, zero] at row
    obtain ⟨j, hj⟩ := pickRow_exists matrix[i.val] positive
    exact ⟨j, by simpa only [pickMatrix, Costed.tabulate_value] using hj,
      h.1 i j (pickRow_some _ j hj)⟩
  · intro i a j hi ha
    by_contra ne
    have pi := pickMatrix_some matrix i j hi
    have pa := pickMatrix_some matrix a j ha
    have both : value matrix[i.val][j.val] + value matrix[a.val][j.val] ≤
        ∑ b : Fin l, value matrix[b.val][j.val] := by
      calc
        _ = ∑ b ∈ ({i, a} : Finset (Fin l)), value matrix[b.val][j.val] := by simp [ne]
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have col := h.2.2 j
    dsimp only at col
    omega

theorem pickMatrix_cost (matrix : Vector (Vector (List Bool) r) l) (B : Nat)
    (bound : ∀ (i : Fin l) (j : Fin r), matrix[i.val][j.val].length ≤ B) :
    (pickMatrix matrix).2 ≤ 2 * l * l + l * (pickBudget r B + 6) + 3 :=
  Costed.tabulate_cost l _ (pickBudget r B) (fun i => pickRow_cost _ B (bound i))

def matchingWitness (allowed : Vector (Vector Bool r) l) (selected : Vector Bool l) :
    Costed.Computation (Vector (Option (Fin r)) l) :=
  let supply := Costed.tabulate l (fun i => (if selected[i.val] then [true] else [], 3))
  let capacity := Costed.tabulate r (fun _ => ([true], 1))
  let matrix := matrixWords allowed supply.1 capacity.1 1
  let result := pickMatrix matrix.1
  (result.1, supply.2 + capacity.2 + matrix.2 + result.2 + 3)

theorem matchingWitness_correct (allowed : Vector (Vector Bool r) l) (selected : Vector Bool l)
    (sat : Saturates (fun i j => allowed[i.val][j.val]) (fun i => selected[i.val])) :
    (∀ i : Fin l, selected[i.val] = true → ∃ j : Fin r,
      (matchingWitness allowed selected).1[i.val] = some j ∧ allowed[i.val][j.val] = true) ∧
      (∀ (i a : Fin l) (j : Fin r), (matchingWitness allowed selected).1[i.val] = some j →
        (matchingWitness allowed selected).1[a.val] = some j → i = a) := by
  let supply := Costed.tabulate l (fun i => (if selected[i.val] then [true] else [], 3))
  let capacity := Costed.tabulate r (fun _ => ([true], 1))
  have supplyValue (i : Fin l) : value supply.1[i.val] = if selected[i.val] then 1 else 0 := by
    simp only [supply, Costed.tabulate_value]
    split <;> simp [value]
  have capacityValue (j : Fin r) : value capacity.1[j.val] = 1 := by simp [capacity, Costed.tabulate_value, value]
  have ex := saturates_unit_matrix _ _ sat
  have prepared : ∃ x, MatrixFeasible (fun i j => allowed[i.val][j.val]) (fun i => value supply.1[i.val])
      (fun j => value capacity.1[j.val]) x := by simpa only [supplyValue, capacityValue] using ex
  have h := matrixWords_correct allowed supply.1 capacity.1 1
    (by intro i; simp only [supply, Costed.tabulate_value]; split <;> simp)
    (by intro j; simp [capacity, Costed.tabulate_value]) prepared
  simp only [supplyValue, capacityValue] at h
  exact pickMatrix_correct _ _ _ h

def matchingWitnessBudget (l r : Nat) :=
  (2 * l * l + 9 * l + 3) + (2 * r * r + 7 * r + 3) + matrixWordsBudget l r 1 +
    (2 * l * l + l * (pickBudget r (maxFlowWordLength (l + r + 2) (l + (l * r + r)) (1 + l + r + 2)) + 6) + 3) + 3

theorem matchingWitness_cost (allowed : Vector (Vector Bool r) l) (selected : Vector Bool l) :
    (matchingWitness allowed selected).2 ≤ matchingWitnessBudget l r := by
  let supply := Costed.tabulate l (fun i => (if selected[i.val] then [true] else [], 3))
  let capacity := Costed.tabulate r (fun _ => ([true], 1))
  have sb (i : Fin l) : supply.1[i.val].length ≤ 1 := by
    simp only [supply, Costed.tabulate_value]; split <;> simp
  have cb (j : Fin r) : capacity.1[j.val].length ≤ 1 := by simp [capacity, Costed.tabulate_value]
  have hs := Costed.tabulate_cost l (fun i => (if selected[i.val] then [true] else [], 3)) 3 (by intros; rfl)
  have hc := Costed.tabulate_cost r (fun _ => ([true], 1)) 1 (by intros; rfl)
  have hm := matrixWords_cost allowed supply.1 capacity.1 1 sb cb
  have hp := pickMatrix_cost (matrixWords allowed supply.1 capacity.1 1).1 _
    (matrixWords_length allowed supply.1 capacity.1 1 sb cb)
  dsimp only [matchingWitness, matchingWitnessBudget]
  dsimp only [supply, capacity] at hm hp
  norm_num only at hs hc
  simp only [Nat.mul_comm l 9, Nat.mul_comm r 7] at hs hc
  omega

end GyoriLovasz.TransportNetwork
