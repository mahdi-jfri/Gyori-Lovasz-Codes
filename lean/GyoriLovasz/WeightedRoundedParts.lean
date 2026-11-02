import GyoriLovasz.Weighted

namespace GyoriLovasz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Each part created by rounding has a root and at most one neighbor.
This proves both its weight bound and connectivity, before global reconstruction. -/
theorem rounded_parts_valid {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {weight : Fin n → Nat} {capacity : Fin k → Nat} {bound : Nat}
    (S : Finset (Fin k)) (N : Finset (Fin n)) (f : Fin n → Fin k)
    (injective : Set.InjOn f N)
    (edges : ∀ p ∈ N, E p (roots (f p)))
    (nonterminal : ∀ p ∈ N, ¬RootSet roots p)
    (positive : ∀ i ∈ S, 0 < capacity i)
    (upper : ∀ p ∈ N, weight p ≤ bound) :
    ∀ i ∈ S,
      (∑ p ∈ N.filter (fun p => f p = i), weight p) ≤ capacity i + bound - 1 ∧
      (∀ x, x = roots i ∨ (x ∈ N ∧ f x = i) →
        ReachWithin E (fun y => y = roots i ∨ (y ∈ N ∧ f y = i)) x (roots i)) ∧
      (∀ x ∈ N.filter (fun p => f p = i), ¬RootSet roots x) := by
  classical
  intro i hi
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : ∃ p ∈ N, f p = i
    · obtain ⟨p, hp, hpi⟩ := h
      have singleton : N.filter (fun q => f q = i) = {p} := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro hq
          exact injective hq.1 hp (hq.2.trans hpi.symm)
        · intro he
          subst q
          exact ⟨hp, hpi⟩
      rw [singleton, Finset.sum_singleton]
      exact weighted_rounding_bound (positive i hi) (upper p hp)
    · have empty : N.filter (fun p => f p = i) = ∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro p hp
        exact h ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
      rw [empty, Finset.sum_empty]
      exact Nat.zero_le _
  · intro x hx
    rcases hx with he | hn
    · subst x
      exact .refl _ (Or.inl rfl)
    · exact .step (Or.inr hn) (by simpa [hn.2] using edges x hn.1)
        (.refl _ (Or.inl rfl))
  · intro x hx
    exact nonterminal x (Finset.mem_filter.mp hx).1

end GyoriLovasz
