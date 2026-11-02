import Mathlib.Data.Fintype.Prod
import GyoriLovasz.Matching

namespace GyoriLovasz
open Side

theorem feasible_delete_noncritical {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {capacity : Fin k → Nat} {label : Fin n → Fin k}
    {p q : Fin n} (feasible : FeasibleAssignment E roots capacity label)
    (free : ∀ v, ∀ hv : ¬RootSet roots v,
      ¬Critical E (RootSet roots) v hv p q (roots (label v))) :
    FeasibleAssignment (DeleteEdge E p q) roots capacity label := by
  classical
  refine ⟨?_, feasible.2⟩
  intro v hv
  by_contra h
  exact free v hv ⟨feasible.1 v hv, h⟩

noncomputable def edgeCount (E : Fin n → Fin n → Prop) : Nat := by
  classical
  exact (Finset.univ.filter (fun e : Fin n × Fin n => E e.1 e.2)).card

theorem edgeCount_delete_lt {E : Fin n → Fin n → Prop} {p q : Fin n}
    (edge : E p q) : edgeCount (DeleteEdge E p q) < edgeCount E := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, (Finset.mem_filter.mp he).2.1⟩
  · intro he
    have hpq : (p,q) ∈ Finset.univ.filter (fun e : Fin n × Fin n => E e.1 e.2) := by
      simp [edge]
    rw [← he] at hpq
    simp [DeleteEdge] at hpq

/-- The outer reduction has a contractible vertex after finitely many safe edge
deletions. This is an existence result; minimization is not an implementation. -/
theorem exists_contractible_subgraph {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {capacity : Fin k → Nat}
    (hk : 0 < k) (hinj : Function.Injective roots)
    (positive : ∀ i, 0 < capacity i)
    (initial : ∃ label, FeasibleAssignment E roots capacity label) :
    ∃ F : Fin n → Fin n → Prop, (∀ x y, F x y → E x y) ∧
      ∃ label, FeasibleAssignment F roots capacity label ∧
        ∃ i p, ¬RootSet roots p ∧ F p (roots i) ∧
          (∀ y, F p y → y = roots i) := by
  classical
  have ex : ∃ m, ∃ F : Fin n → Fin n → Prop,
      (∀ x y, F x y → E x y) ∧
      (∃ label, FeasibleAssignment F roots capacity label) ∧ edgeCount F = m :=
    ⟨edgeCount E, E, fun _ _ h => h, initial, rfl⟩
  obtain ⟨m, ⟨F, sub, ⟨label, feasible⟩, hm⟩, minimal⟩ := exists_minimal_nat _ ex
  obtain ⟨p, pinj, pnt, pedge⟩ := preterminal_matching hinj positive feasible
  by_cases sole : ∃ i, ∀ y, F (p i) y → y = roots i
  · obtain ⟨i, hi⟩ := sole
    exact ⟨F, sub, label, feasible, i, p i, pnt i, pedge i, hi⟩
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
    obtain ⟨better, hb, i, free⟩ := exists_noncritical_secondary (q := q) hk
      ⟨label, feasible⟩ pedge (fun i => (qspec i).2)
      (fun i j hne he => hne (pinj he))
    have hd := feasible_delete_noncritical hb free
    have lower := minimal (edgeCount (DeleteEdge F (p i) (q i)))
      ⟨DeleteEdge F (p i) (q i), fun x y he => sub x y he.1, ⟨better, hd⟩, rfl⟩
    have upper : edgeCount (DeleteEdge F (p i) (q i)) < edgeCount F := edgeCount_delete_lt (qspec i).1
    omega

/-- A vertex with just one outgoing terminal neighbor can only be assigned to
that terminal. This fact supplies the capacity decrement in contraction. -/
theorem sole_neighbor_assignment {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {capacity : Fin k → Nat} {label : Fin n → Fin k}
    {p : Fin n} {i : Fin k} (hinj : Function.Injective roots)
    (feasible : FeasibleAssignment E roots capacity label)
    (pnt : ¬RootSet roots p) (edge : E p (roots i))
    (sole : ∀ y, E p y → y = roots i) : label p = i := by
  classical
  have tp : roots i ≠ p := fun h => pnt ⟨i, h⟩
  let C : Cut (Fin n) := fun x => if x = p then right else if x = roots i then sep else left
  have validC : Valid E (RootSet roots) p C := by
    refine ⟨by simp [C], ?_, ?_⟩
    · intro t ht
      have htne : t ≠ p := fun h => pnt (h ▸ ht)
      by_cases he : t = roots i <;> simp [C, htne, he, tp]
    · intro x y he hx hy
      have xp : x = p := by
        by_cases h : x = p
        · exact h
        · by_cases ht : x = roots i <;> simp [C, h, ht, tp] at hx
      subst x
      have yt := sole y he
      simp [C, yt, tp] at hy
  have sizeC : size (List.finRange n) C = 1 := by
    rw [size_eq_separator_card]
    have he : Finset.univ.filter (fun x => C x = sep) = {roots i} := by
      ext x
      by_cases hp : x = p
      · subst x; simp [C, tp.symm]
      · simp [C, hp]
    rw [he]; simp
  obtain ⟨D, hd, hdu⟩ := feasible.1 p pnt
  have lower := (cutRank_spec E (RootSet roots) p pnt).lower C validC
  have nr := hd.1.terminals (roots i) ⟨i, rfl⟩
  have nl := hd.1.no_cross p (roots i) edge hd.1.source
  have dt : D (roots i) = sep := by
    cases h : D (roots i) with
    | left => exact False.elim (nl h)
    | sep => rfl
    | right => exact False.elim (nr h)
  by_cases different : label p = i
  · exact different
  exfalso
  have rootdiff : roots (label p) ≠ roots i := fun h => different (hinj h)
  have sub : {roots (label p), roots i} ⊆ Finset.univ.filter (fun x => D x = sep) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hdu, dt]
  have bound := Finset.card_le_card sub
  have pair : ({roots (label p), roots i} : Finset (Fin n)).card = 2 := by simp [rootdiff]
  have sz := size_eq_separator_card D
  have rank := hd.2
  omega

end GyoriLovasz

