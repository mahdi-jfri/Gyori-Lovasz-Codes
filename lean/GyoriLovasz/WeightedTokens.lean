import GyoriLovasz.WeightedUnitMatrix
import Mathlib.Data.List.OfFn

namespace GyoriLovasz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem countTrue_flatMap (xs : List α) (f : α → List β) (P : β → Prop) :
    countTrue (xs.flatMap f) P = sumValues xs (fun x => countTrue (f x) P) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, countTrue_append, sumValues, ih]

theorem sumValues_toFinset [DecidableEq α] (xs : List α) (hn : xs.Nodup) (f : α → Nat) :
    sumValues xs f = ∑ x ∈ xs.toFinset, f x := by
  rw [sumValues_eq_map_sum, ← List.sum_toFinset f hn]

theorem sumValues_finRange (f : Fin m → Nat) : sumValues (List.finRange m) f = ∑ i, f i := by
  rw [sumValues_toFinset _ (finRange_nodup m)]
  have he : (List.finRange m).toFinset = Finset.univ := by ext x; simp [mem_finRange x]
  rw [he]

noncomputable def splitTokens (roots : Fin k → Fin n) (split : Fin n → Fin k → Nat) :
    List (Fin n × Fin k) :=
  (nonterminals roots).flatMap (fun v => (List.finRange k).flatMap (fun i => List.replicate (split v i) (v,i)))

theorem splitTokens_count (roots : Fin k → Fin n) (split : Fin n → Fin k → Nat)
    (P : Fin n × Fin k → Prop) : countTrue (splitTokens roots split) P =
      ∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots v), ∑ i, if P (v,i) then split v i else 0 := by
  classical
  rw [splitTokens, countTrue_flatMap, sumValues_toFinset _ (nonterminals_nodup roots)]
  have he : (nonterminals roots).toFinset = Finset.univ.filter (fun v => ¬RootSet roots v) := by
    ext x
    simp [mem_nonterminals]
  rw [he]
  apply Finset.sum_congr rfl
  intro v _
  rw [countTrue_flatMap, sumValues_finRange]
  apply Finset.sum_congr rfl
  intro i _
  exact countTrue_replicate _ _ _

theorem splitTokens_mem {roots : Fin k → Fin n} {split : Fin n → Fin k → Nat} {x : Fin n × Fin k}
    (hx : x ∈ splitTokens roots split) : ¬RootSet roots x.1 ∧ 0 < split x.1 x.2 := by
  obtain ⟨v, hv, hi⟩ := List.mem_flatMap.mp hx
  obtain ⟨i, _, hp⟩ := List.mem_flatMap.mp hi
  have he := List.mem_replicate.mp hp
  obtain ⟨positive, equal⟩ := he
  subst x
  exact ⟨mem_nonterminals.mp hv, Nat.pos_of_ne_zero positive⟩

theorem countTrue_get (xs : List α) (P : α → Prop) :
    countTrue (List.finRange xs.length) (fun u => P (xs.get u)) = countTrue xs P := by
  rw [← countTrue_map]
  have he : (List.finRange xs.length).map (fun u => xs.get u) = xs := by
    rw [List.finRange, List.map_ofFn]
    exact List.ofFn_get xs
  rw [he]

/-- Any integral split assignment has a finite unit representation. This
expansion proves existence, not a polynomial bound in the binary input size. -/
theorem split_to_units {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {weight : Fin n → Nat} {capacity : Fin k → Nat} {split : Fin n → Fin k → Nat}
    (feasible : SplitFeasible E roots weight capacity split) :
    ∃ m, ∃ origin : Fin m → Fin n, ∃ assigned : Fin m → Fin k,
      UnitSplitFeasible E roots weight capacity origin assigned := by
  classical
  let xs := splitTokens roots split
  let origin := fun u : Fin xs.length => (xs.get u).1
  let assigned := fun u : Fin xs.length => (xs.get u).2
  have mem (u : Fin xs.length) : xs.get u ∈ xs := List.get_mem xs u
  have valid := fun u => splitTokens_mem (mem u)
  refine ⟨xs.length, origin, assigned, ⟨fun u => (valid u).1, ?_, ?_, ?_⟩⟩
  · intro u hu
    exact feasible.1 (origin u) hu (assigned u) (valid u).2
  · intro v hv
    change countTrue (List.finRange xs.length) (fun u => (xs.get u).1 = v) = weight v
    rw [countTrue_get xs (fun x => x.1 = v)]
    change countTrue (splitTokens roots split) (fun x => x.1 = v) = weight v
    rw [splitTokens_count]
    dsimp only
    calc
      _ = ∑ x ∈ Finset.univ.filter (fun x => ¬RootSet roots x),
          if x = v then ∑ j, split x j else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = v
        · simp only [if_pos hx]
        · simp only [if_neg hx, Finset.sum_const_zero]
      _ = ∑ j, split v j := Finset.sum_ite_eq_of_mem' _ v _ (by simp [hv])
      _ = weight v := feasible.2.1 v hv
  · intro i
    change countTrue (List.finRange xs.length) (fun u => (xs.get u).2 = i) ≤ capacity i
    rw [countTrue_get xs (fun x => x.2 = i)]
    change countTrue (splitTokens roots split) (fun x => x.2 = i) ≤ capacity i
    rw [splitTokens_count]
    dsimp only
    calc
      _ = ∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots v), split v i := by
        apply Finset.sum_congr rfl
        intro v _
        refine (Finset.sum_eq_single i ?_ ?_).trans ?_
        · intro j _ hji
          simp only [if_neg hji]
        · simp
        · simp
      _ ≤ capacity i := feasible.2.2 i

theorem split_removable_edge {E : Fin n → Fin n → Prop} {roots p q : Fin k → Fin n}
    {weight : Fin n → Nat} {capacity : Fin k → Nat}
    (hk : 0 < k) (initial : ∃ split, SplitFeasible E roots weight capacity split)
    (matching : ∀ i, E (p i) (roots i)) (secondary : ∀ i, q i ≠ roots i)
    (distinct : ∀ i j, i ≠ j → p i ≠ p j) :
    ∃ split, SplitFeasible E roots weight capacity split ∧
      ∃ i, SplitFeasible (DeleteEdge E (p i) (q i)) roots weight capacity split := by
  obtain ⟨split, hf⟩ := initial
  obtain ⟨m, origin, assigned, hu⟩ := split_to_units hf
  exact unit_removable_edge hk ⟨assigned, hu⟩ matching secondary distinct

end GyoriLovasz
