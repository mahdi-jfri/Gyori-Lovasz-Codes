import GyoriLovasz.RuntimeConnectedWeighted

namespace GyoriLovasz.WordInstance
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def measuredLength : List Bool → Costed.Computation Nat
  | [] => (0, 1)
  | _ :: xs => let old := measuredLength xs; (old.1 + 1, old.2 + 2)

theorem measuredLength_value (xs : List Bool) : (measuredLength xs).1 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [measuredLength, ih]

theorem measuredLength_cost (xs : List Bool) : (measuredLength xs).2 = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [measuredLength, ih]; omega

def measuredLengths : List (List Bool) → Costed.Computation Nat
  | [] => (0, 1)
  | x :: xs =>
    let here := measuredLength x
    let rest := measuredLengths xs
    (here.1 + rest.1, here.2 + rest.2 + 3)

theorem measuredLengths_value (xs : List (List Bool)) :
    (measuredLengths xs).1 = (xs.map List.length).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [measuredLengths, measuredLength_value, ih]

theorem measuredLengths_cost (xs : List (List Bool)) :
    (measuredLengths xs).2 = 2 * (xs.map List.length).sum + 4 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [measuredLengths, measuredLength_cost, ih]; omega

/-- Size in stored Boolean cells and reference/index cells. The graph is a
Boolean adjacency matrix; weight and capacity payloads are binary lists. -/
def inputSize (s : Input n k) : Nat := n * n + n + k +
  (s.weight.toList.map List.length).sum + (s.capacity.toList.map List.length).sum + 1

def measureInput (s : Input n k) : Costed.Computation Nat :=
  let w := measuredLengths s.weight.toList
  let c := measuredLengths s.capacity.toList
  (w.1 + c.1 + 1, w.2 + c.2 + n + k + 3)

theorem measureInput_value (s : Input n k) : (measureInput s).1 =
    (s.weight.toList.map List.length).sum + (s.capacity.toList.map List.length).sum + 1 := by
  simp [measureInput, measuredLengths_value]

theorem vector_length_le (v : Vector (List Bool) n) (i : Fin n) :
    v[i.val].length ≤ (v.toList.map List.length).sum := by
  apply List.single_le_sum (fun x _ => Nat.zero_le x)
  exact List.mem_map_of_mem (by simpa only [Vector.mem_toList_iff] using Vector.getElem_mem i.isLt)

theorem measureInput_bounds (s : Input n k) : Bounded s (measureInput s).1 := by
  rw [measureInput_value]
  constructor
  · intro v
    have h := vector_length_le s.weight v
    omega
  · intro i
    have h := vector_length_le s.capacity i
    omega

theorem measureInput_cost (s : Input n k) : (measureInput s).2 ≤ 5 * inputSize s + 5 := by
  simp only [measureInput, measuredLengths_cost, Vector.length_toList, inputSize]
  omega

theorem measureInput_size (s : Input n k) : n ≤ inputSize s ∧ (measureInput s).1 ≤ inputSize s := by
  rw [measureInput_value]
  unfold inputSize
  omega

def weightedFromInput (s : Input n k) (bound : Nat)
    (inj : Function.Injective (root s)) (positive : 0 < bound)
    (weightBounds : ∀ v, ¬RootSet (root s) v → 0 < weights s v ∧ weights s v ≤ bound)
    (initial : ∃ x, SplitFeasible (relation s) (root s) (weights s) (capacities s) x) :
    Costed.Computation (Vector (Fin k) n) :=
  let measured := measureInput s
  let answer := weightedProgram s measured.1 bound inj positive weightBounds initial (measureInput_bounds s)
  (answer.1, measured.2 + answer.2 + 1)

theorem generalized_weighted_input_polynomial_time :
    ∃ p : Polynomial Nat, ∀ (n k : Nat) (s : Input n k) (bound : Nat)
      (inj : Function.Injective (root s)) (positive : 0 < bound)
      (weightBounds : ∀ v, ¬RootSet (root s) v → 0 < weights s v ∧ weights s v ≤ bound)
      (initial : ∃ x, SplitFeasible (relation s) (root s) (weights s) (capacities s) x),
      LabelCorrect s bound (weightedFromInput s bound inj positive weightBounds initial).1 ∧
      (weightedFromInput s bound inj positive weightBounds initial).2 ≤ p.eval (inputSize s) := by
  have polynomial := RuntimePolynomial.polynomial_add RuntimePolynomial.diagonal_polynomial
    (RuntimePolynomial.polynomial_add
      (RuntimePolynomial.polynomial_mul (RuntimePolynomial.polynomial_constant 5) RuntimePolynomial.polynomial_identity)
      (RuntimePolynomial.polynomial_constant 6))
  obtain ⟨p, hp⟩ := polynomial
  refine ⟨p, fun n k s bound inj positive weightBounds initial => ?_⟩
  refine ⟨weightedProgram_correct s (measureInput s).1 bound inj positive weightBounds initial (measureInput_bounds s), ?_⟩
  have hc := weightedProgram_cost s (measureInput s).1 bound inj positive weightBounds initial (measureInput_bounds s)
  have hm := measureInput_cost s
  have hs := measureInput_size s
  have mono := RuntimePolynomial.weighted_mono hs.1 hs.2
  rw [← hp]
  change (measureInput s).2 + (weightedProgram s (measureInput s).1 bound inj positive weightBounds initial (measureInput_bounds s)).2 + 1 ≤ _
  dsimp only
  omega

/-- The connectivity corollary with the binary-length bound measured by the
program itself and its measurement charged to the counter. -/
def connectedWeightedFromInput (s : Input n k) (bound : Nat) (hk : 0 < k)
    (connected : KConnected (relation s) k) (inj : Function.Injective (root s))
    (positive : 0 < bound)
    (weightBounds : ∀ v, ¬RootSet (root s) v → 0 < weights s v ∧ weights s v ≤ bound)
    (balance : (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet (root s) v), weights s v) ≤ ∑ i, capacities s i) :
    Costed.Computation (Vector (Fin k) n) :=
  weightedFromInput s bound inj positive weightBounds
    (kconnected_initialize_split (root s) (weights s) (capacities s) hk connected inj balance)

theorem weighted_input_polynomial_time :
    ∃ p : Polynomial Nat, ∀ (n k : Nat) (s : Input n k) (bound : Nat) (hk : 0 < k)
      (connected : KConnected (relation s) k) (inj : Function.Injective (root s))
      (positive : 0 < bound)
      (weightBounds : ∀ v, ¬RootSet (root s) v → 0 < weights s v ∧ weights s v ≤ bound)
      (balance : (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet (root s) v), weights s v) ≤ ∑ i, capacities s i),
      LabelCorrect s bound (connectedWeightedFromInput s bound hk connected inj positive weightBounds balance).1 ∧
      (connectedWeightedFromInput s bound hk connected inj positive weightBounds balance).2 ≤ p.eval (inputSize s) := by
  obtain ⟨p, hp⟩ := generalized_weighted_input_polynomial_time
  refine ⟨p, fun n k s bound hk connected inj positive weightBounds balance => ?_⟩
  exact hp n k s bound inj positive weightBounds
    (kconnected_initialize_split (root s) (weights s) (capacities s) hk connected inj balance)

end GyoriLovasz.WordInstance
