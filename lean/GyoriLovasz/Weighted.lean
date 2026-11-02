import GyoriLovasz.Main
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace GyoriLovasz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Integral flow-essential split assignment. Weights and loads exclude roots. -/
def SplitFeasible (E : Fin n → Fin n → Prop) (roots : Fin k → Fin n)
    (weight : Fin n → Nat) (capacity : Fin k → Nat)
    (split : Fin n → Fin k → Nat) : Prop :=
  (∀ v, ∀ hv : ¬RootSet roots v, ∀ i, 0 < split v i →
    Essential E (RootSet roots) v hv (roots i)) ∧
  (∀ v, ¬RootSet roots v → ∑ i, split v i = weight v) ∧
  (∀ i, ∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots v), split v i ≤ capacity i)

/-- Connected rooted partition with the additive error of the weighted theorem.
`bound` is a positive upper bound on the weight of any non-terminal. -/
def WeightedPartition (E : Fin n → Fin n → Prop) (roots : Fin k → Fin n)
    (weight : Fin n → Nat) (capacity : Fin k → Nat) (bound : Nat) : Prop :=
  ∃ label : Fin n → Fin k,
    (∀ i, label (roots i) = i) ∧
    (∀ i, (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots v ∧ label v = i), weight v)
      ≤ capacity i + bound - 1) ∧
    (∀ i x, label x = i → ReachWithin E (fun y => label y = i) x (roots i))

/-- Specification of the generalized weighted existence theorem, proved by
`generalized_weighted_gyori_lovasz` in `WeightedMain`. No running-time assertion
is included. -/
def WeightedTheoremStatement : Prop :=
  ∀ (n k : Nat) (E : Fin n → Fin n → Prop) (roots : Fin k → Fin n)
    (weight : Fin n → Nat) (capacity : Fin k → Nat) (bound : Nat),
    Function.Injective roots → 0 < bound →
    (∀ v, ¬RootSet roots v → 0 < weight v ∧ weight v ≤ bound) →
    (∃ split, SplitFeasible E roots weight capacity split) →
    WeightedPartition E roots weight capacity bound

theorem split_entry_le_capacity {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {weight : Fin n → Nat} {capacity : Fin k → Nat}
    {split : Fin n → Fin k → Nat} (feasible : SplitFeasible E roots weight capacity split)
    {v : Fin n} (hv : ¬RootSet roots v) (i : Fin k) : split v i ≤ capacity i := by
  classical
  have mem : v ∈ Finset.univ.filter (fun x => ¬RootSet roots x) := by simp [hv]
  have h := Finset.sum_erase_add (Finset.univ.filter (fun x => ¬RootSet roots x))
    (fun x => split x i) mem
  dsimp only at h
  have hc := feasible.2.2 i
  omega

theorem split_zero_capacity {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {weight : Fin n → Nat} {capacity : Fin k → Nat}
    {split : Fin n → Fin k → Nat} (feasible : SplitFeasible E roots weight capacity split)
    {v : Fin n} (hv : ¬RootSet roots v) {i : Fin k} (zero : capacity i = 0) : split v i = 0 := by
  have h := split_entry_le_capacity feasible hv i
  omega

theorem split_delete_noncritical {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {weight : Fin n → Nat} {capacity : Fin k → Nat}
    {split : Fin n → Fin k → Nat} {p q : Fin n}
    (feasible : SplitFeasible E roots weight capacity split)
    (free : ∀ v, ∀ hv : ¬RootSet roots v, ∀ i, 0 < split v i →
      ¬Critical E (RootSet roots) v hv p q (roots i)) :
    SplitFeasible (DeleteEdge E p q) roots weight capacity split := by
  classical
  refine ⟨?_, feasible.2⟩
  intro v hv i positive
  by_cases h : Essential (DeleteEdge E p q) (RootSet roots) v hv (roots i)
  · exact h
  · exact False.elim (free v hv i positive ⟨feasible.1 v hv i positive, h⟩)

theorem weighted_rounding_bound {w c bound : Nat} (positive : 0 < c) (upper : w ≤ bound) :
    w ≤ c + bound - 1 := by omega

theorem weighted_contraction_bound {load c w bound : Nat}
    (fits : w ≤ c) (positive : 0 < bound) (residual : load ≤ c - w + bound - 1) :
    load + w ≤ c + bound - 1 := by omega

end GyoriLovasz
