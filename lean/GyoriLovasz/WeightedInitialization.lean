import GyoriLovasz.WeightedTokens

namespace GyoriLovasz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem countTrue_sublist {xs ys : List α} (h : xs.Sublist ys) (P : α → Prop) :
    countTrue xs P ≤ countTrue ys P := by
  induction h with
  | slnil => simp [countTrue]
  | cons x h ih => simp only [countTrue]; omega
  | cons₂ x h ih => simp only [countTrue]; omega

theorem initialize_split {E : Fin n → Fin n → Prop} (roots : Fin k → Fin n)
    (weight : Fin n → Nat) (capacity : Fin k → Nat) (hk : 0 < k)
    (allessential : ∀ v, ∀ hv : ¬RootSet roots v, ∀ i,
      Essential E (RootSet roots) v hv (roots i))
    (balance : (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots v), weight v) ≤ ∑ i, capacity i) :
    ∃ split, SplitFeasible E roots weight capacity split := by
  classical
  let units := capacitySlots (nonterminals roots) weight
  let slots := capacitySlots (List.finRange k) capacity
  have he : (nonterminals roots).toFinset = Finset.univ.filter (fun v => ¬RootSet roots v) := by
    ext v
    simp [mem_nonterminals]
  have hlen : units.length ≤ slots.length := by
    dsimp only [units, slots]
    rw [capacitySlots_length, capacitySlots_length, sumValues_finRange,
      sumValues_toFinset _ (nonterminals_nodup roots), he]
    exact balance
  have truncated : (List.finRange units.length).length = (slots.take units.length).length := by
    simp [Nat.min_eq_left hlen]
  obtain ⟨assigned, hassigned⟩ := exists_label_from_slots (List.finRange units.length)
    (slots.take units.length) ⟨0, hk⟩ (finRange_nodup units.length) truncated
  let origin := fun u : Fin units.length => units.get u
  have hnt (u : Fin units.length) : ¬RootSet roots (origin u) := by
    have hm := List.get_mem units u
    obtain ⟨v, hv, hu⟩ := List.mem_flatMap.mp hm
    have eq := (List.mem_replicate.mp hu).2
    change ¬RootSet roots (units.get u)
    rw [eq]
    exact mem_nonterminals.mp hv
  have unitfeasible : UnitSplitFeasible E roots weight capacity origin assigned := by
    refine ⟨hnt, fun u hu => allessential (origin u) hu (assigned u), ?_, ?_⟩
    · intro v hv
      change countTrue (List.finRange units.length) (fun u => units.get u = v) = weight v
      rw [countTrue_get units (fun x => x = v)]
      exact (capacitySlots_count (nonterminals roots) weight v (nonterminals_nodup roots)).trans
        (if_pos (mem_nonterminals.mpr hv))
    · intro i
      rw [hassigned i]
      have taken : (slots.take units.length).Sublist slots := List.take_sublist units.length slots
      have le := countTrue_sublist taken (fun x => x = i)
      have eq := capacitySlots_count (List.finRange k) capacity i (finRange_nodup k)
      have full : countTrue slots (fun x => x = i) = capacity i := by
        simpa [slots, mem_finRange i] using eq
      exact le.trans_eq full
  exact ⟨unitMatrix origin assigned, unitMatrix_feasible unitfeasible⟩

theorem kconnected_initialize_split {E : Fin n → Fin n → Prop} (roots : Fin k → Fin n)
    (weight : Fin n → Nat) (capacity : Fin k → Nat) (hk : 0 < k)
    (connected : KConnected E k) (hinj : Function.Injective roots)
    (balance : (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots v), weight v) ≤ ∑ i, capacity i) :
    ∃ split, SplitFeasible E roots weight capacity split :=
  initialize_split roots weight capacity hk
    (fun _ hv i => initial_all_essential hv connected (fun _ _ he => hinj he) i) balance

end GyoriLovasz
