import GyoriLovasz.WeightedReduction

namespace GyoriLovasz

/-- A graph with no feasible single-edge deletion already permits contraction
or Hall rounding. Only local irreducibility is needed by the executable scan. -/
theorem weighted_irreducible {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {weight : Fin n → Nat} {capacity : Fin k → Nat}
    (hk : 0 < k) (feasible : ∃ split, SplitFeasible E roots weight capacity split)
    (irreducible : ∀ p q, E p q → ¬∃ split, SplitFeasible (DeleteEdge E p q) roots weight capacity split) :
    (∃ i p, ¬RootSet roots p ∧ E p (roots i) ∧ (∀ y, E p y → y = roots i)) ∨
      ¬∃ p : Fin k → Fin n, Function.Injective p ∧
        (∀ i, ¬RootSet roots (p i)) ∧ (∀ i, E (p i) (roots i)) := by
  classical
  by_cases matching : ∃ p : Fin k → Fin n, Function.Injective p ∧
      (∀ i, ¬RootSet roots (p i)) ∧ (∀ i, E (p i) (roots i))
  · obtain ⟨p, pinj, pnt, pedge⟩ := matching
    by_cases sole : ∃ i, ∀ y, E (p i) y → y = roots i
    · obtain ⟨i, hi⟩ := sole
      exact Or.inl ⟨i, p i, pnt i, pedge i, hi⟩
    · have second : ∀ i, ∃ y, E (p i) y ∧ y ≠ roots i := by
        intro i
        by_contra h
        apply sole
        exact ⟨i, fun y he => by by_contra hn; exact h ⟨y, he, hn⟩⟩
      let q := fun i => Classical.choose (second i)
      have qspec := fun i => Classical.choose_spec (second i)
      obtain ⟨split, _, i, hd⟩ := split_removable_edge (q := q) hk feasible
        pedge (fun i => (qspec i).2) (fun i j hne he => hne (pinj he))
      exact False.elim (irreducible (p i) (q i) (qspec i).1 ⟨split, hd⟩)
  · exact Or.inr matching

end GyoriLovasz

