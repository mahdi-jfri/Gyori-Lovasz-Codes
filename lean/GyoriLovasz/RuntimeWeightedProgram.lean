import GyoriLovasz.RuntimePartitionProgram
import GyoriLovasz.RuntimePolynomial

namespace GyoriLovasz.WordInstance
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem normalize_valid (s : Input n k) (bound : Nat)
    (inj : Function.Injective (root s)) (positive : 0 < bound)
    (weightBounds : ∀ v, ¬RootSet (root s) v → 0 < weights s v ∧ weights s v ≤ bound)
    (initial : ∃ x, SplitFeasible (relation s) (root s) (weights s) (capacities s) x) :
    Valid (normalize s).1 bound := by
  obtain ⟨x, hx⟩ := initial
  refine ⟨inj, normalize_zero s, positive, ?_, ?_⟩
  · intro v hv
    rw [normalize_nonroot s v hv]
    exact weightBounds v hv
  · refine ⟨x, hx.1, ?_, hx.2.2⟩
    intro v hv
    exact (hx.2.1 v hv).trans (normalize_nonroot s v hv).symm

def weightedProgram (s : Input n k) (B bound : Nat)
    (inj : Function.Injective (root s)) (positive : 0 < bound)
    (weightBounds : ∀ v, ¬RootSet (root s) v → 0 < weights s v ∧ weights s v ≤ bound)
    (initial : ∃ x, SplitFeasible (relation s) (root s) (weights s) (capacities s) x)
    (wb : Bounded s B) : Costed.Computation (Vector (Fin k) n) :=
  let normalized := normalize s
  let solved := solveNormalized n B bound normalized.1 (normalize_valid s bound inj positive weightBounds initial)
    (normalize_bounds s B wb) (Nat.le_refl n)
  (solved.1.1, normalized.2 + solved.1.2 + 1)

def LabelCorrect (s : Input n k) (bound : Nat) (labels : Vector (Fin k) n) : Prop :=
  (∀ i, labels[(root s i).val] = i) ∧
  (∀ i, (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet (root s) v ∧ labels[v.val] = i), weights s v)
    ≤ capacities s i + bound - 1) ∧
  (∀ i v, labels[v.val] = i → ReachWithin (relation s) (fun x => labels[x.val] = i) v (root s i))

theorem normalized_weight_value (s : Input n k) (v : Fin n) :
    weights (normalize s).1 v = if RootSet (root s) v then 0 else weights s v := by
  classical
  by_cases ht : RootSet (root s) v
  · obtain ⟨i, hi⟩ := ht
    have zero := normalize_zero s i
    simpa only [hi, show RootSet (root s) v from ⟨i, hi⟩, ↓reduceIte] using zero
  · simpa only [ht, ↓reduceIte] using normalize_nonroot s v ht

theorem weightedProgram_correct (s : Input n k) (B bound : Nat)
    (inj : Function.Injective (root s)) (positive : 0 < bound)
    (weightBounds : ∀ v, ¬RootSet (root s) v → 0 < weights s v ∧ weights s v ≤ bound)
    (initial : ∃ x, SplitFeasible (relation s) (root s) (weights s) (capacities s) x)
    (wb : Bounded s B) : LabelCorrect s bound (weightedProgram s B bound inj positive weightBounds initial wb).1 := by
  classical
  let solved := solveNormalized n B bound (normalize s).1 (normalize_valid s bound inj positive weightBounds initial)
    (normalize_bounds s B wb) (Nat.le_refl n)
  let label := fun v : Fin n => solved.1.1[v.val]
  have part := solved.2.1
  refine ⟨fun i => (part.2.1 i (Finset.mem_univ _)).2, ?_, ?_⟩
  · intro i
    have eq : (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet (root s) v ∧ label v = i), weights s v) =
        partLoad Finset.univ (weights (normalize s).1) label i := by
      rw [Finset.sum_filter]
      unfold partLoad
      apply Finset.sum_congr rfl
      intro v _
      by_cases ht : RootSet (root s) v <;> by_cases hl : label v = i <;>
        simp [normalized_weight_value, ht, hl]
    change (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet (root s) v ∧ label v = i), weights s v) ≤ _
    rw [eq]
    exact part.2.2.1 i (Finset.mem_univ _)
  · intro i v hv
    exact (part.2.2.2 i (Finset.mem_univ _) v (Finset.mem_univ _) hv).mono_allowed (fun _ hx => hx.2)

theorem weightedProgram_cost (s : Input n k) (B bound : Nat)
    (inj : Function.Injective (root s)) (positive : 0 < bound)
    (weightBounds : ∀ v, ¬RootSet (root s) v → 0 < weights s v ∧ weights s v ≤ bound)
    (initial : ∃ x, SplitFeasible (relation s) (root s) (weights s) (capacities s) x)
    (wb : Bounded s B) :
    (weightedProgram s B bound inj positive weightBounds initial wb).2 ≤ RuntimePolynomial.weightedBudget n B := by
  let solved := solveNormalized n B bound (normalize s).1 (normalize_valid s bound inj positive weightBounds initial)
    (normalize_bounds s B wb) (Nat.le_refl n)
  have hs := solved.2.2
  have hk := valid_root_count (normalize s).1 bound (normalize_valid s bound inj positive weightBounds initial)
  have hn : (normalize s).2 ≤ RuntimePolynomial.normalizeCeiling n := by
    apply (normalize_cost s).trans
    unfold RuntimePolynomial.normalizeCeiling
    gcongr
    unfold rootMaskBudget
    gcongr
  change (normalize s).2 + solved.1.2 + 1 ≤ _
  unfold RuntimePolynomial.weightedBudget
  omega

theorem generalized_weighted_polynomial_time :
    ∃ p : Polynomial Nat, ∀ (n k : Nat) (s : Input n k) (B bound : Nat)
      (inj : Function.Injective (root s)) (positive : 0 < bound)
      (weightBounds : ∀ v, ¬RootSet (root s) v → 0 < weights s v ∧ weights s v ≤ bound)
      (initial : ∃ x, SplitFeasible (relation s) (root s) (weights s) (capacities s) x)
      (wb : Bounded s B),
      LabelCorrect s bound (weightedProgram s B bound inj positive weightBounds initial wb).1 ∧
      (weightedProgram s B bound inj positive weightBounds initial wb).2 ≤ p.eval (n + B + 1) := by
  obtain ⟨p, hp⟩ := RuntimePolynomial.weighted_polynomial_bound
  refine ⟨p, fun n k s B bound inj positive weightBounds initial wb => ?_⟩
  exact ⟨weightedProgram_correct s B bound inj positive weightBounds initial wb,
    (weightedProgram_cost s B bound inj positive weightBounds initial wb).trans (hp n B)⟩

end GyoriLovasz.WordInstance
