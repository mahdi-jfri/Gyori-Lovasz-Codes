import GyoriLovasz.Weighted

namespace GyoriLovasz
open Side
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sole_neighbor_essential {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {j : Fin k}
    {p : Fin n} {i : Fin k} (hinj : Function.Injective roots)
    (pnt : ¬RootSet roots p) (edge : E p (roots i))
    (sole : ∀ y, E p y → y = roots i)
    (essential : Essential E (RootSet roots) p pnt (roots j)) : j = i := by
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
  obtain ⟨D, hd, hdu⟩ := essential
  have lower := (cutRank_spec E (RootSet roots) p pnt).lower C validC
  have nr := hd.1.terminals (roots i) ⟨i, rfl⟩
  have nl := hd.1.no_cross p (roots i) edge hd.1.source
  have dt : D (roots i) = sep := by
    cases h : D (roots i) with
    | left => exact False.elim (nl h)
    | sep => rfl
    | right => exact False.elim (nr h)
  by_cases different : j = i
  · exact different
  exfalso
  have rootdiff : roots (j) ≠ roots i := fun h => different (hinj h)
  have sub : {roots (j), roots i} ⊆ Finset.univ.filter (fun x => D x = sep) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hdu, dt]
  have bound := Finset.card_le_card sub
  have pair : ({roots (j), roots i} : Finset (Fin n)).card = 2 := by simp [rootdiff]
  have sz := size_eq_separator_card D
  have rank := hd.2
  omega


theorem split_sole_neighbor {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {weight : Fin n → Nat} {capacity : Fin k → Nat}
    {split : Fin n → Fin k → Nat} {p : Fin n} {i : Fin k}
    (hinj : Function.Injective roots) (feasible : SplitFeasible E roots weight capacity split)
    (pnt : ¬RootSet roots p) (edge : E p (roots i)) (sole : ∀ y, E p y → y = roots i) :
    split p i = weight p ∧ weight p ≤ capacity i ∧ (∀ j, j ≠ i → split p j = 0) := by
  classical
  have others : ∀ j, j ≠ i → split p j = 0 := by
    intro j hji
    by_cases hz : split p j = 0
    · exact hz
    · have positive : 0 < split p j := by omega
      exact False.elim (hji (sole_neighbor_essential hinj pnt edge sole (feasible.1 p pnt j positive)))
  have total : (∑ j, split p j) = split p i :=
    Finset.sum_eq_single i (fun j _ hji => others j hji) (by simp)
  have row := feasible.2.1 p pnt
  have equal : split p i = weight p := total.symm.trans row
  exact ⟨equal, equal ▸ split_entry_le_capacity feasible pnt i, others⟩

end GyoriLovasz
