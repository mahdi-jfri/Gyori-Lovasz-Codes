import GyoriLovasz.WeightedRoundingTransport

namespace GyoriLovasz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def totalNonterminalWeight (roots : Fin k → Fin n) (weight : Fin n → Nat) : Nat :=
  ∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots v), weight v

theorem split_entry_le_weight {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {weight : Fin n → Nat} {capacity : Fin k → Nat} {split : Fin n → Fin k → Nat}
    (feasible : SplitFeasible E roots weight capacity split) {v : Fin n}
    (hv : ¬RootSet roots v) (i : Fin k) : split v i ≤ weight v := by
  rw [← feasible.2.1 v hv]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Capacities larger than total supply may be clamped before running flow.
This preserves the split witness and bounds every network capacity by supply. -/
theorem split_clamp_capacity {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {weight : Fin n → Nat} {capacity : Fin k → Nat} {split : Fin n → Fin k → Nat}
    (feasible : SplitFeasible E roots weight capacity split) :
    SplitFeasible E roots weight (fun i => min (capacity i) (totalNonterminalWeight roots weight)) split := by
  refine ⟨feasible.1, feasible.2.1, ?_⟩
  intro i
  apply le_min (feasible.2.2 i)
  apply Finset.sum_le_sum
  intro v hv
  exact split_entry_le_weight feasible (Finset.mem_filter.mp hv).2 i

theorem totalNonterminalWeight_le {roots : Fin k → Fin n} {weight : Fin n → Nat} {bound : Nat}
    (upper : ∀ v, ¬RootSet roots v → weight v ≤ bound) :
    totalNonterminalWeight roots weight ≤ n * bound := by
  have le : totalNonterminalWeight roots weight ≤
      ∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots v), bound := by
    apply Finset.sum_le_sum
    intro v hv
    exact upper v (Finset.mem_filter.mp hv).2
  have card : (Finset.univ.filter (fun v => ¬RootSet roots v)).card ≤ n :=
    (Finset.card_filter_le _ _).trans (by simp)
  have counted : (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots v), bound) =
      (Finset.univ.filter (fun v => ¬RootSet roots v)).card * bound := by simp
  rw [counted] at le
  exact le.trans (Nat.mul_le_mul_right bound card)

end GyoriLovasz
