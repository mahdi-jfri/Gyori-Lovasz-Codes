import GyoriLovasz.RuntimeUnweightedEncoding

namespace GyoriLovasz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem fiber_card_nonroots (roots : Fin k → Fin n) (label : Fin n → Fin k)
    (fixed : ∀ i, label (roots i) = i) (i : Fin k) :
    (Finset.univ.filter (fun v => label v = i)).card =
      (Finset.univ.filter (fun v => ¬RootSet roots v ∧ label v = i)).card + 1 := by
  classical
  have sets : Finset.univ.filter (fun v => label v = i) =
      insert (roots i) (Finset.univ.filter (fun v => ¬RootSet roots v ∧ label v = i)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hv
      by_cases ht : RootSet roots v
      · obtain ⟨j, hj⟩ := ht
        have ji : j = i := (fixed j).symm.trans (hj ▸ hv)
        exact Or.inl (hj.symm.trans (congrArg roots ji))
      · exact Or.inr ⟨ht, hv⟩
    · rintro (rfl | ⟨_, hv⟩)
      · exact fixed i
      · exact hv
  rw [sets, Finset.card_insert_of_not_mem]
  simp [RootSet]

theorem fiber_cards_sum (label : Fin n → Fin k) :
    (∑ i, (Finset.univ.filter (fun v => label v = i)).card) = n := by
  classical
  have h := sum_countTrue_fibers (List.finRange n) Finset.univ label (fun _ => True)
    (fun _ _ => Finset.mem_univ _)
  simpa only [true_and, countTrue_eq_card_filter, Finset.filter_True, Finset.card_univ, Fintype.card_fin] using h

theorem exact_of_total {a b : Fin k → Nat} (le : ∀ i, a i ≤ b i)
    (total : (∑ i, a i) = ∑ i, b i) (i : Fin k) : a i = b i := by
  have ha := Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)
  have hb := Finset.sum_erase_add Finset.univ b (Finset.mem_univ i)
  have rest := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ => le j)
  have here := le i
  omega

theorem unit_upper_bounds_exact (roots : Fin k → Fin n) (sizes : Fin k → Nat)
    (label : Fin n → Fin k) (fixed : ∀ i, label (roots i) = i)
    (positive : ∀ i, 0 < sizes i) (total : (∑ i, sizes i) = n)
    (upper : ∀ i, (Finset.univ.filter (fun v => ¬RootSet roots v ∧ label v = i)).card ≤ sizes i - 1) :
    ∀ i, countTrue (List.finRange n) (fun v => label v = i) = sizes i := by
  classical
  have le (i : Fin k) : (Finset.univ.filter (fun v => label v = i)).card ≤ sizes i := by
    rw [fiber_card_nonroots roots label fixed]
    have hu := upper i
    have hp := positive i
    omega
  intro i
  rw [countTrue_eq_card_filter]
  exact exact_of_total le ((fiber_cards_sum label).trans total.symm) i

end GyoriLovasz
