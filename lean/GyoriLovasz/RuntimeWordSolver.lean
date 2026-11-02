import GyoriLovasz.RuntimeWordScaling

namespace GyoriLovasz.Flow
open Binary

def compileColumnWords (bits : Vector Bool m) : Costed.Computation (List (ScalingOp m)) :=
  let indices := Costed.enumerateIndices m
  let selected := Costed.filter (fun e => (bits[e.val], 1)) indices.1
  let mapped := Costed.map (fun e => (ScalingOp.increment e, 2)) selected.1
  (.double :: mapped.1, indices.2 + selected.2 + mapped.2 + 2)

theorem compileColumnWords_value (bits : Vector Bool m) :
    (compileColumnWords bits).1 = bitColumn bits := by
  simp [compileColumnWords, Costed.map_value, Costed.filter_value, Costed.enumerateIndices_value, bitColumn]

theorem compileColumnWords_cost (bits : Vector Bool m) :
    (compileColumnWords bits).2 ≤ 2 * m * m + 11 * m + 5 := by
  have hf := Costed.filter_cost (fun e : Fin m => (bits[e.val], 1)) (List.finRange m) 1
    (by intros; exact Nat.le_refl _)
  have hm := Costed.map_cost (fun e : Fin m => (ScalingOp.increment e, 2))
    ((List.finRange m).filter (fun e => bits[e.val])) 2 (by intros; exact Nat.le_refl _)
  have hl := List.length_filter_le (fun e : Fin m => bits[e.val]) (List.finRange m)
  simp only [List.length_finRange] at hf hl
  simp only [compileColumnWords, Costed.enumerateIndices_value, Costed.enumerateIndices_cost,
    Costed.filter_value]
  omega

def compileWords : List (Vector Bool m) → Costed.Computation (List (ScalingOp m))
  | [] => ([], 1)
  | bits :: columns =>
    let first := compileColumnWords bits
    let rest := compileWords columns
    let joined := Costed.append first.1 rest.1
    (joined.1, first.2 + rest.2 + joined.2 + 2)

theorem compileWords_value (columns : List (Vector Bool m)) :
    (compileWords columns).1 = compileBits columns := by
  induction columns with
  | nil => rfl
  | cons bits columns ih => simp [compileWords, Costed.append_value, compileColumnWords_value, ih, compileBits]

theorem compileWords_cost (columns : List (Vector Bool m)) :
    (compileWords columns).2 ≤ columns.length * (2 * m * m + 13 * m + 10) + 1 := by
  induction columns with
  | nil => simp [compileWords]
  | cons bits columns ih =>
    have hc := compileColumnWords_cost bits
    have hl := bitColumn_length bits
    simp only [compileWords, Costed.append_cost, compileColumnWords_value, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

def solveWords (s : WordResidual n m) (columns : List (Vector Bool m)) :
    Costed.Computation (WordResidual n m) :=
  let program := compileWords columns
  let start := zeroWords s
  let result := wordExecute program.1 start.1
  (result.1, program.2 + start.2 + result.2 + 2)

theorem solveWords_optimal (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (columns : List (Vector Bool m)) :
    let target := {decodeNetwork s with capacity := binaryCapacity columns (fun _ => 0)}
    Feasible target (decodeFlow (solveWords s columns).1) ∧
      ∀ other, Feasible target other →
        totalCost target (decodeFlow (solveWords s columns).1) ≤ totalCost target other := by
  have h := wordExecute_zero_optimal (compileBits columns) s correct
  simpa only [solveWords, compileWords_value, compileBits_capacity] using h

/-- Full binary capacity-scaling program bound in the explicit bit-gate /
reference-RAM model of these executable routines. The bound includes input
column compilation, state initialization, all repairs, and all loop steps.
It is not a compiler timing theorem or a partition running-time theorem. -/
theorem solveWords_cost (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (columns : List (Vector Bool m)) (B : Nat)
    (costBound : ∀ e : Fin m, s.cost[e.val].digits.length ≤ B)
    (codeBound : ∀ v : Fin n, s.vertexCode[v.val].length ≤ B) :
    (solveWords s columns).2 ≤
      columns.length * (2 * m * m + 13 * m + 10) +
      (2 * m * m + 8 * m + 2 * n * n + 8 * n + 7) +
      ((m + 1) * columns.length) *
        (opBudget n m (B + ((m + 1) * columns.length) * (n + 6)) + 1) + 4 := by
  have hc := compileWords_cost columns
  have hz := zeroWords_cost s
  have he := wordExecute_cost (compileBits columns) (zeroWords s).1 (zeroWords_codes s correct)
    B (zeroWords_bounds s B costBound codeBound)
  have hl := compileBits_length columns
  have hm := Nat.mul_le_mul hl (Nat.add_le_add_right
    (opBudget_mono n m _ _ (Nat.add_le_add_left (Nat.mul_le_mul_right (n + 6) hl) B)) 1)
  dsimp only [solveWords]
  rw [compileWords_value]
  omega

theorem solveWords_dual (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (columns : List (Vector Bool m)) :
    WordInvariant (solveWords s columns).1 := by
  exact wordExecute_invariant _ _ (zeroWords_codes s correct) (zeroWords_invariant s)

theorem solveWords_bounds (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (columns : List (Vector Bool m)) (B : Nat)
    (costBound : ∀ e : Fin m, s.cost[e.val].digits.length ≤ B)
    (codeBound : ∀ v : Fin n, s.vertexCode[v.val].length ≤ B) :
    WordResidualBound (solveWords s columns).1 (B + ((m + 1) * columns.length) * (n + 6)) := by
  have h := wordExecute_bounds (compileBits columns) (zeroWords s).1 (zeroWords_codes s correct)
    B (zeroWords_bounds s B costBound codeBound)
  have len := compileBits_length columns
  have mono := Nat.mul_le_mul_right (n + 6) len
  simp only [solveWords, compileWords_value]
  exact ⟨fun e => ⟨Nat.le_trans (h.1 e).1 (by omega), Nat.le_trans (h.1 e).2.1 (by omega),
    Nat.le_trans (h.1 e).2.2 (by omega)⟩,
    fun v => ⟨Nat.le_trans (h.2 v).1 (by omega), Nat.le_trans (h.2 v).2 (by omega)⟩⟩

end GyoriLovasz.Flow
