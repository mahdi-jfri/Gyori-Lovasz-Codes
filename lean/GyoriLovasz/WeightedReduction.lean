import GyoriLovasz.WeightedTokens
import GyoriLovasz.WeightedHall

namespace GyoriLovasz

/-- Safe edge deletions terminate at a feasible subgraph with either a sole
terminal neighbor or no matching saturating all roots. The latter alternative
is precisely the input to the checked Hall rounding theorem. -/
theorem weighted_reduction {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {weight : Fin n → Nat} {capacity : Fin k → Nat}
    (hk : 0 < k) (initial : ∃ split, SplitFeasible E roots weight capacity split) :
    ∃ F : Fin n → Fin n → Prop, (∀ x y, F x y → E x y) ∧
      (∃ split, SplitFeasible F roots weight capacity split) ∧
      ((∃ i p, ¬RootSet roots p ∧ F p (roots i) ∧ (∀ y, F p y → y = roots i)) ∨
        ¬∃ p : Fin k → Fin n, Function.Injective p ∧
          (∀ i, ¬RootSet roots (p i)) ∧ (∀ i, F (p i) (roots i))) := by
  classical
  have ex : ∃ m, ∃ F : Fin n → Fin n → Prop,
      (∀ x y, F x y → E x y) ∧
      (∃ split, SplitFeasible F roots weight capacity split) ∧ edgeCount F = m :=
    ⟨edgeCount E, E, fun _ _ h => h, initial, rfl⟩
  obtain ⟨m, ⟨F, sub, feasible, hm⟩, minimal⟩ := exists_minimal_nat _ ex
  refine ⟨F, sub, feasible, ?_⟩
  by_cases matching : ∃ p : Fin k → Fin n, Function.Injective p ∧
      (∀ i, ¬RootSet roots (p i)) ∧ (∀ i, F (p i) (roots i))
  · obtain ⟨p, pinj, pnt, pedge⟩ := matching
    by_cases sole : ∃ i, ∀ y, F (p i) y → y = roots i
    · obtain ⟨i, hi⟩ := sole
      exact Or.inl ⟨i, p i, pnt i, pedge i, hi⟩
    · have second : ∀ i, ∃ y, F (p i) y ∧ y ≠ roots i := by
        intro i
        by_contra h
        apply sole
        refine ⟨i, ?_⟩
        intro y he
        by_contra hne
        exact h ⟨y, he, hne⟩
      let q := fun i => Classical.choose (second i)
      have qspec := fun i => Classical.choose_spec (second i)
      obtain ⟨split, _, i, hd⟩ := split_removable_edge (q := q) hk feasible
        pedge (fun i => (qspec i).2) (fun i j hne he => hne (pinj he))
      have lower := minimal (edgeCount (DeleteEdge F (p i) (q i)))
        ⟨DeleteEdge F (p i) (q i), fun x y he => sub x y he.1, ⟨split, hd⟩, rfl⟩
      have upper : edgeCount (DeleteEdge F (p i) (q i)) < edgeCount F :=
        edgeCount_delete_lt (qspec i).1
      omega
  · exact Or.inr matching

end GyoriLovasz

