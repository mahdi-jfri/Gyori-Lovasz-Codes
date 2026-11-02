import GyoriLovasz.WeightedUnits
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace GyoriLovasz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sum_countTrue_fibers {α β : Type} [DecidableEq β] (xs : List α)
    (indices : Finset β) (f : α → β) (P : α → Prop)
    (closed : ∀ x, x ∈ xs → f x ∈ indices) :
    (∑ i ∈ indices, countTrue xs (fun x => P x ∧ f x = i)) = countTrue xs P := by
  classical
  induction xs with
  | nil => simp [countTrue]
  | cons x xs ih =>
    have hx := closed x (by simp)
    have ht := ih (fun y hy => closed y (by simp [hy]))
    simp only [countTrue]
    rw [Finset.sum_add_distrib, ht]
    congr 1
    by_cases hp : P x
    · simp [hp, hx]
    · simp [hp]

noncomputable def unitMatrix (origin : Fin m → Fin n) (assigned : Fin m → Fin k)
    (v : Fin n) (i : Fin k) : Nat :=
  countTrue (List.finRange m) (fun u => origin u = v ∧ assigned u = i)

theorem unitMatrix_positive {origin : Fin m → Fin n} {assigned : Fin m → Fin k}
    {v : Fin n} {i : Fin k} (positive : 0 < unitMatrix origin assigned v i) :
    ∃ u, origin u = v ∧ assigned u = i := by
  classical
  rw [unitMatrix, countTrue_filter_length] at positive
  obtain ⟨u, hu⟩ := List.exists_mem_of_length_pos positive
  exact ⟨u, by simpa using (List.mem_filter.mp hu).2⟩

theorem unitMatrix_feasible {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {weight : Fin n → Nat} {capacity : Fin k → Nat}
    {origin : Fin m → Fin n} {assigned : Fin m → Fin k}
    (feasible : UnitSplitFeasible E roots weight capacity origin assigned) :
    SplitFeasible E roots weight capacity (unitMatrix origin assigned) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro v hv i positive
    obtain ⟨u, hu, hi⟩ := unitMatrix_positive positive
    subst v
    have he := feasible.2.1 u hv
    simpa only [hi] using he
  · intro v hv
    exact (sum_countTrue_fibers (List.finRange m) Finset.univ assigned (fun u => origin u = v)
      (fun _ _ => Finset.mem_univ _)).trans (feasible.2.2.1 v hv)
  · intro i
    let indices := Finset.univ.filter (fun v => ¬RootSet roots v)
    have he : (∑ v ∈ indices, unitMatrix origin assigned v i) =
        ∑ v ∈ indices, countTrue (List.finRange m) (fun u => assigned u = i ∧ origin u = v) := by
      apply Finset.sum_congr rfl
      intro v _
      exact countTrue_congr _ (fun _ _ => and_comm)
    have counted := sum_countTrue_fibers (List.finRange m) indices origin (fun u => assigned u = i)
      (fun u _ => by simp [indices, feasible.1 u])
    exact (he.trans counted).le.trans (feasible.2.2.2 i)

/-- In the unit representation, a matching yields an actual integral split
assignment that survives deletion of a secondary edge. -/
theorem unit_removable_edge {E : Fin n → Fin n → Prop} {roots p q : Fin k → Fin n}
    {weight : Fin n → Nat} {capacity : Fin k → Nat} {origin : Fin m → Fin n}
    (hk : 0 < k) (initial : ∃ assigned, UnitSplitFeasible E roots weight capacity origin assigned)
    (matching : ∀ i, E (p i) (roots i)) (secondary : ∀ i, q i ≠ roots i)
    (distinct : ∀ i j, i ≠ j → p i ≠ p j) :
    ∃ split, SplitFeasible E roots weight capacity split ∧
      ∃ i, SplitFeasible (DeleteEdge E (p i) (q i)) roots weight capacity split := by
  obtain ⟨assigned, hf, i, free⟩ := unit_noncritical_secondary hk initial matching secondary distinct
  have hm := unitMatrix_feasible hf
  refine ⟨unitMatrix origin assigned, hm, i, split_delete_noncritical hm ?_⟩
  intro v hv j positive
  obtain ⟨u, hu, hj⟩ := unitMatrix_positive positive
  subst v
  have notcrit := free u hv
  simpa only [hj] using notcrit

end GyoriLovasz
