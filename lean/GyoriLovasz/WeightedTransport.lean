import GyoriLovasz.WeightedContraction
import GyoriLovasz.WeightedTokens
import GyoriLovasz.ActiveReindex

namespace GyoriLovasz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem GraphReindex.sum_filter {vertices : List (Fin n)}
    {E : Fin n → Fin n → Prop} {T : Fin n → Prop} {e : Fin m → Fin n} {r : Fin n → Fin m}
    (h : GraphReindex vertices (List.finRange m) E T e r)
    (P : Fin n → Prop) [DecidablePred P] (f : Fin n → Nat) :
    (∑ x ∈ Finset.univ.filter (fun x => P (e x)), f (e x)) =
      ∑ x ∈ vertices.toFinset.filter P, f x := by
  classical
  apply Finset.sum_bij (fun x _ => e x)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (h.image_mem x), (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ he
    exact (h.inverse x).symm.trans ((congrArg r he).trans (h.inverse y))
  · intro y hy
    have ym := List.mem_toFinset.mp (Finset.mem_filter.mp hy).1
    refine ⟨r y, ?_, h.retract y ym⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h.retract y ym]; exact (Finset.mem_filter.mp hy).2⟩
  · intro _ _
    rfl

/-- The integral split invariant after contraction, on the smaller vertex type.
Exactly the contracted vertex's weight is deducted from its root's capacity. -/
theorem weighted_contraction_reindexed {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {weight : Fin n → Nat} {capacity : Fin k → Nat}
    {split : Fin n → Fin k → Nat} {p : Fin n} {i : Fin k}
    {e : Fin m → Fin n} {r : Fin n → Fin m}
    (hinj : Function.Injective roots) (feasible : SplitFeasible E roots weight capacity split)
    (pnt : ¬RootSet roots p) (edge : E p (roots i))
    (sole : ∀ y, E p y → y = roots i)
    (h : GraphReindex ((List.finRange n).erase p) (List.finRange m)
      (Contract E p (roots i)) (RootSet roots) e r) :
    SplitFeasible (fun x y => Contract E p (roots i) (e x) (e y))
      (fun j => r (roots j)) (fun x => weight (e x))
      (fun j => capacity j - if j = i then weight p else 0) (fun x j => split (e x) j) := by
  classical
  let G := fun x y => Contract E p (roots i) (e x) (e y)
  let roots' := fun j => r (roots j)
  have pred : (fun x => RootSet roots (e x)) = RootSet roots' := by
    funext x
    exact propext (reindex_rootSet h x)
  have evne (v : Fin m) : e v ≠ p := by
    intro he
    exact List.Nodup.not_mem_erase (finRange_nodup n) (he ▸ h.image_mem v)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv j positive
    have hnt : ¬RootSet roots (e v) := fun ht => hv ((reindex_rootSet h v).mp ht)
    obtain ⟨s, hs⟩ := exists_rank ((List.finRange n).erase p)
      (Contract E p (roots i)) (RootSet roots) (e v) hnt
    obtain ⟨_, ess⟩ := contraction_preserves_essential (finRange_nodup n) (mem_finRange p)
      (mem_finRange (roots i)) (evne v) pnt (show RootSet roots (roots i) from ⟨i, rfl⟩)
      (show RootSet roots (roots j) from ⟨j, rfl⟩) edge sole
      (cutRank_spec E (RootSet roots) (e v) hnt) hs (feasible.1 (e v) hnt j positive)
    have pulledRank := h.rank hs
    rw [pred] at pulledRank
    have eqrank := hasRank_unique pulledRank (cutRank_spec G (RootSet roots') v hv)
    have ht := h.retract (roots j) (h.terminals _ ⟨j, rfl⟩)
    rw [← ht] at ess
    have pulled := h.essential ess
    rw [pred, eqrank] at pulled
    exact pulled
  · intro v hv
    exact feasible.2.1 (e v) (fun ht => hv ((reindex_rootSet h v).mp ht))
  · intro j
    have cnt := h.sum_filter (fun x => ¬RootSet roots x) (fun x => split x j)
    have seteq : ((List.finRange n).erase p).toFinset.filter (fun x => ¬RootSet roots x) =
        (Finset.univ.filter (fun x => ¬RootSet roots x)).erase p := by
      ext x
      simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, true_and]
      constructor
      · intro hx
        exact ⟨fun he => List.Nodup.not_mem_erase (finRange_nodup n) (he ▸ hx.1), hx.2⟩
      · intro hx
        exact ⟨(List.mem_erase_of_ne hx.1).mpr (mem_finRange x), hx.2⟩
    rw [seteq] at cnt
    have pp : p ∈ Finset.univ.filter (fun x => ¬RootSet roots x) := by simp [pnt]
    have total := Finset.sum_erase_add (Finset.univ.filter (fun x => ¬RootSet roots x))
      (fun x => split x j) pp
    have load := feasible.2.2 j
    have soleSplit := split_sole_neighbor hinj feasible pnt edge sole
    have cnt' : (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots' v), split (e v) j) =
        ∑ v ∈ (Finset.univ.filter (fun x => ¬RootSet roots x)).erase p, split v j := by
      rw [← pred]
      exact cnt
    change (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots' v), split (e v) j) ≤ _
    rw [cnt']
    dsimp only
    by_cases ji : j = i
    · subst j
      rw [if_pos rfl]
      have eq := soleSplit.1
      dsimp only at total
      omega
    · rw [if_neg ji, Nat.sub_zero]
      have eq := soleSplit.2.2 j ji
      dsimp only at total
      omega

theorem sum_erase_reindex {i : Fin k} {d : Fin l → Fin k} {s : Fin k → Fin l}
    (dinv : ∀ j, s (d j) = j) (dret : ∀ j, j ≠ i → d (s j) = j)
    (dne : ∀ j, d j ≠ i) (f : Fin k → Nat) :
    (∑ j, f (d j)) = ∑ j ∈ Finset.univ.erase i, f j := by
  classical
  apply Finset.sum_bij (fun j _ => d j)
  · intro j _; exact Finset.mem_erase.mpr ⟨dne j, Finset.mem_univ _⟩
  · intro x _ y _ he
    exact (dinv x).symm.trans ((congrArg s he).trans (dinv y))
  · intro j hj
    exact ⟨s j, Finset.mem_univ _, dret j (Finset.mem_erase.mp hj).1⟩
  · intro _ _; rfl

/-- Delete a zero-capacity root, with both vertex and root index types reduced. -/
theorem weighted_terminal_reindexed {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {weight : Fin n → Nat} {capacity : Fin k → Nat}
    {split : Fin n → Fin k → Nat} {i : Fin k}
    {e : Fin m → Fin n} {r : Fin n → Fin m} {d : Fin l → Fin k} {s : Fin k → Fin l}
    (hinj : Function.Injective roots) (feasible : SplitFeasible E roots weight capacity split)
    (zero : capacity i = 0)
    (dinv : ∀ j, s (d j) = j) (dret : ∀ j, j ≠ i → d (s j) = j) (dne : ∀ j, d j ≠ i)
    (h : GraphReindex ((List.finRange n).erase (roots i)) (List.finRange m)
      (DeleteVertex E (roots i)) (WithoutTerminal (RootSet roots) (roots i)) e r) :
    Function.Injective (fun j => r (roots (d j))) ∧
    SplitFeasible (fun x y => DeleteVertex E (roots i) (e x) (e y))
      (fun j => r (roots (d j))) (fun x => weight (e x)) (fun j => capacity (d j))
      (fun x j => split (e x) (d j)) := by
  classical
  let G := fun x y => DeleteVertex E (roots i) (e x) (e y)
  let roots' := fun j => r (roots (d j))
  have evne (v : Fin m) : e v ≠ roots i := by
    intro he
    exact List.Nodup.not_mem_erase (finRange_nodup n) (he ▸ h.image_mem v)
  have root_mem (j : Fin l) : roots (d j) ∈ (List.finRange n).erase (roots i) :=
    h.terminals _ ⟨⟨d j, rfl⟩, fun he => dne j (hinj he)⟩
  have root_eq (j : Fin l) : e (roots' j) = roots (d j) := h.retract _ (root_mem j)
  have root_iff (v : Fin m) : RootSet roots (e v) ↔ RootSet roots' v := by
    constructor
    · rintro ⟨j, he⟩
      have jne : j ≠ i := by intro eq; subst j; exact evne v he.symm
      refine ⟨s j, ?_⟩
      change r (roots (d (s j))) = v
      rw [dret j jne, he, h.inverse v]
    · rintro ⟨j, he⟩
      exact ⟨d j, (root_eq j).symm.trans (congrArg e he)⟩
  have pred : (fun x => WithoutTerminal (RootSet roots) (roots i) (e x)) = RootSet roots' := by
    funext x
    apply propext
    exact ⟨fun ht => (root_iff x).mp ht.1, fun ht => ⟨(root_iff x).mpr ht, evne x⟩⟩
  have oldpred : (fun x => RootSet roots (e x)) = RootSet roots' := funext (fun x => propext (root_iff x))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b he
    have eq : d a = d b := hinj ((root_eq a).symm.trans ((congrArg e he).trans (root_eq b)))
    exact (dinv a).symm.trans ((congrArg s eq).trans (dinv b))
  · intro v hv j positive
    have hnt : ¬RootSet roots (e v) := fun ht => hv ((root_iff v).mp ht)
    obtain ⟨rank, hs⟩ := exists_rank ((List.finRange n).erase (roots i))
      (DeleteVertex E (roots i)) (WithoutTerminal (RootSet roots) (roots i)) (e v) (fun ht => hnt ht.1)
    have ess := terminal_removal_preserves_essential (finRange_nodup n) (mem_finRange (roots i))
      (evne v) (show RootSet roots (roots i) from ⟨i, rfl⟩)
      (show RootSet roots (roots (d j)) from ⟨d j, rfl⟩)
      (show roots (d j) ≠ roots i from fun he => dne j (hinj he))
      (cutRank_spec E (RootSet roots) (e v) hnt) hs (feasible.1 (e v) hnt (d j) positive)
    rw [← root_eq j] at ess
    have pulled := h.essential ess
    have pulledRank := h.rank hs
    rw [pred] at pulled pulledRank
    have eqrank := hasRank_unique pulledRank (cutRank_spec G (RootSet roots') v hv)
    rw [eqrank] at pulled
    exact pulled
  · intro v hv
    have hnt : ¬RootSet roots (e v) := fun ht => hv ((root_iff v).mp ht)
    have eq := sum_erase_reindex dinv dret dne (split (e v))
    have total := Finset.sum_erase_add Finset.univ (split (e v)) (Finset.mem_univ i)
    have zi := split_zero_capacity feasible hnt zero
    have row := feasible.2.1 (e v) hnt
    dsimp only at total ⊢
    omega
  · intro j
    have cnt := h.sum_filter (fun x => ¬RootSet roots x) (fun x => split x (d j))
    have seteq : ((List.finRange n).erase (roots i)).toFinset.filter (fun x => ¬RootSet roots x) =
        Finset.univ.filter (fun x => ¬RootSet roots x) := by
      ext x
      simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_univ, true_and]
      constructor
      · exact fun hx => hx.2
      · intro hx
        exact ⟨(List.mem_erase_of_ne (fun he => hx ⟨i, he.symm⟩)).mpr (mem_finRange x), hx⟩
    rw [seteq] at cnt
    change (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots' v), split (e v) (d j)) ≤ _
    rw [← oldpred, cnt]
    exact feasible.2.2 (d j)

end GyoriLovasz
