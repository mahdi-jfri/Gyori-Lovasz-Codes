import GyoriLovasz.RuntimeWeightedProgram
import GyoriLovasz.WeightedInitialization

namespace GyoriLovasz.WordInstance
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Connectivity and total capacity supply the generalized algorithm's
logical feasibility precondition; no split is computed by token expansion. -/
def connectedWeightedProgram (s : Input n k) (B bound : Nat) (hk : 0 < k)
    (connected : KConnected (relation s) k) (inj : Function.Injective (root s))
    (positive : 0 < bound)
    (weightBounds : ∀ v, ¬RootSet (root s) v → 0 < weights s v ∧ weights s v ≤ bound)
    (balance : (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet (root s) v), weights s v) ≤ ∑ i, capacities s i)
    (wb : Bounded s B) : Costed.Computation (Vector (Fin k) n) :=
  weightedProgram s B bound inj positive weightBounds
    (kconnected_initialize_split (root s) (weights s) (capacities s) hk connected inj balance) wb

theorem weighted_polynomial_time :
    ∃ p : Polynomial Nat, ∀ (n k : Nat) (s : Input n k) (B bound : Nat) (hk : 0 < k)
      (connected : KConnected (relation s) k) (inj : Function.Injective (root s))
      (positive : 0 < bound)
      (weightBounds : ∀ v, ¬RootSet (root s) v → 0 < weights s v ∧ weights s v ≤ bound)
      (balance : (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet (root s) v), weights s v) ≤ ∑ i, capacities s i)
      (wb : Bounded s B),
      LabelCorrect s bound (connectedWeightedProgram s B bound hk connected inj positive weightBounds balance wb).1 ∧
      (connectedWeightedProgram s B bound hk connected inj positive weightBounds balance wb).2 ≤ p.eval (n + B + 1) := by
  obtain ⟨p, hp⟩ := generalized_weighted_polynomial_time
  refine ⟨p, fun n k s B bound hk connected inj positive weightBounds balance wb => ?_⟩
  exact hp n k s B bound inj positive weightBounds
    (kconnected_initialize_split (root s) (weights s) (capacities s) hk connected inj balance) wb

end GyoriLovasz.WordInstance
