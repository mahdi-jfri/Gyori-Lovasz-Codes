import GyoriLovasz.RuntimeWordSolver

namespace GyoriLovasz.Flow
open Binary

theorem binaryCapacity_append (xs ys : List (Vector Bool m)) (c : Fin m → Nat) :
    binaryCapacity (xs ++ ys) c = binaryCapacity ys (binaryCapacity xs c) := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => exact ih _

/-- Convert padded little-endian arc words to most-significant-first columns.
Tail/head operations read list references; append and all tabulations are charged. -/
def encodeColumns : Nat → Vector (List Bool) m → Costed.Computation (List (Vector Bool m))
  | 0, _ => ([], 1)
  | fuel + 1, words =>
    let low := Costed.tabulate m (fun e => (words[e.val].headD false, 2))
    let high := Costed.tabulate m (fun e => (words[e.val].tail, 2))
    let rest := encodeColumns fuel high.1
    let joined := Costed.append rest.1 [low.1]
    (joined.1, low.2 + high.2 + rest.2 + joined.2 + 3)

theorem encodeColumns_length (fuel : Nat) (words : Vector (List Bool) m) :
    (encodeColumns fuel words).1.length = fuel := by
  induction fuel generalizing words with
  | zero => rfl
  | succ fuel ih => simp [encodeColumns, Costed.append_value, ih]

theorem encodeColumns_value (fuel : Nat) (words : Vector (List Bool) m)
    (bound : ∀ e : Fin m, words[e.val].length ≤ fuel) :
    binaryCapacity (encodeColumns fuel words).1 (fun _ => 0) = fun e => value words[e.val] := by
  induction fuel generalizing words with
  | zero =>
    funext e
    have h : words[e.val] = [] := List.length_eq_zero.mp (Nat.eq_zero_of_le_zero (bound e))
    simp [encodeColumns, binaryCapacity, h, value]
  | succ fuel ih =>
    have tails : ∀ e : Fin m,
        (Costed.tabulate m (fun e => (words[e.val].tail, 2))).1[e.val].length ≤ fuel := by
      intro e
      rw [Costed.tabulate_value]
      have h := bound e
      simp only [List.length_tail]
      omega
    simp only [encodeColumns, Costed.append_value, binaryCapacity_append, ih _ tails]
    funext e
    simp only [binaryCapacity, Costed.tabulate_value]
    cases h : words[e.val] <;> simp [value, Nat.add_comm]

theorem encodeColumns_cost (fuel : Nat) (words : Vector (List Bool) m) :
    (encodeColumns fuel words).2 ≤ fuel * (4 * m * m + 16 * m + 2 * fuel + 12) + 1 := by
  induction fuel generalizing words with
  | zero => simp [encodeColumns]
  | succ fuel ih =>
    have hl := Costed.tabulate_cost m (fun e => (words[e.val].headD false, 2)) 2
      (by intros; exact Nat.le_refl _)
    have hh := Costed.tabulate_cost m (fun e => (words[e.val].tail, 2)) 2
      (by intros; exact Nat.le_refl _)
    have hr := ih (Costed.tabulate m (fun e => (words[e.val].tail, 2))).1
    have mono := Nat.mul_le_mul_left fuel
      (show 4 * m * m + 16 * m + 2 * fuel + 12 ≤
        4 * m * m + 16 * m + 2 * (fuel + 1) + 12 by omega)
    simp only [encodeColumns, Costed.append_cost, encodeColumns_length, Nat.add_mul, Nat.one_mul]
    ring_nf at hl hh hr mono ⊢
    omega

def solveStored (s : WordResidual n m) (B : Nat) : Costed.Computation (WordResidual n m) :=
  let columns := encodeColumns B s.capacity
  let solved := solveWords s columns.1
  (solved.1, columns.2 + solved.2 + 1)

theorem solveStored_optimal (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (B : Nat) (bound : ∀ e : Fin m, s.capacity[e.val].length ≤ B) :
    Feasible (decodeNetwork s) (decodeFlow (solveStored s B).1) ∧
      ∀ other, Feasible (decodeNetwork s) other →
        totalCost (decodeNetwork s) (decodeFlow (solveStored s B).1) ≤ totalCost (decodeNetwork s) other := by
  have h := solveWords_optimal s correct (encodeColumns B s.capacity).1
  rw [encodeColumns_value B s.capacity bound] at h
  exact h

theorem solveStored_cost (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (B : Nat) (bound : WordResidualBound s B) :
    (solveStored s B).2 ≤
      B * (4 * m * m + 16 * m + 2 * B + 12) +
      B * (2 * m * m + 13 * m + 10) +
      (2 * m * m + 8 * m + 2 * n * n + 8 * n + 7) +
      ((m + 1) * B) * (opBudget n m (B + ((m + 1) * B) * (n + 6)) + 1) + 6 := by
  have he := encodeColumns_cost B s.capacity
  have hs := solveWords_cost s correct (encodeColumns B s.capacity).1 B
    (fun e => (bound.1 e).2.2) (fun v => (bound.2 v).1)
  rw [encodeColumns_length] at hs
  dsimp only [solveStored]
  omega

theorem solveStored_network (s : WordResidual n m) (B : Nat)
    (bound : ∀ e : Fin m, s.capacity[e.val].length ≤ B) :
    decodeNetwork (solveStored s B).1 = decodeNetwork s := by
  have h := wordExecute_network (compileBits (encodeColumns B s.capacity).1) (zeroWords s).1
  have hz : decodeNetwork (zeroWords s).1 = {decodeNetwork s with capacity := fun _ => 0} := by
    simp [decodeNetwork, zeroWords, Costed.tabulate_value, value]
  rw [hz, compileBits_capacity, encodeColumns_value B s.capacity bound] at h
  simpa only [solveStored, solveWords, compileWords_value] using h

theorem solveStored_dual (s : WordResidual n m) (correct : VertexCodesCorrect s) (B : Nat)
    (bound : ∀ e : Fin m, s.capacity[e.val].length ≤ B) :
    DualFeasible (decodeNetwork s) (decodeFlow (solveStored s B).1) (decodePotential (solveStored s B).1) := by
  have h := (solveWords_dual s correct (encodeColumns B s.capacity).1).2
  change DualFeasible (decodeNetwork (solveStored s B).1) _ _ at h
  rw [solveStored_network s B bound] at h
  exact h

theorem solveStored_bounds (s : WordResidual n m) (correct : VertexCodesCorrect s) (B : Nat)
    (bound : WordResidualBound s B) :
    WordResidualBound (solveStored s B).1 (B + ((m + 1) * B) * (n + 6)) := by
  have h := solveWords_bounds s correct (encodeColumns B s.capacity).1 B
    (fun e => (bound.1 e).2.2) (fun v => (bound.2 v).1)
  rw [encodeColumns_length] at h
  exact h

theorem wordResidualBound_mono (s : WordResidual n m) (B C : Nat)
    (bound : WordResidualBound s B) (le : B ≤ C) : WordResidualBound s C :=
  ⟨fun e => ⟨Nat.le_trans (bound.1 e).1 le, Nat.le_trans (bound.1 e).2.1 le,
    Nat.le_trans (bound.1 e).2.2 le⟩,
    fun v => ⟨Nat.le_trans (bound.2 v).1 le, Nat.le_trans (bound.2 v).2 le⟩⟩

def storedBudget (n m B : Nat) :=
  B * (4 * m * m + 16 * m + 2 * B + 12) + B * (2 * m * m + 13 * m + 10) +
  (2 * m * m + 8 * m + 2 * n * n + 8 * n + 7) +
  ((m + 1) * B) * (opBudget n m (B + ((m + 1) * B) * (n + 6)) + 1) + 6

end GyoriLovasz.Flow
