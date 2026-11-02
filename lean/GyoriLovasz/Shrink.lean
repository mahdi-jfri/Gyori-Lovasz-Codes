import GyoriLovasz.Reduction
import GyoriLovasz.Reconstruction
import GyoriLovasz.Transport

namespace GyoriLovasz

theorem reindex_rootSet {vertices : List (Fin n)} {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {e : Fin m → Fin n} {r : Fin n → Fin m}
    (h : GraphReindex vertices (List.finRange m) E (RootSet roots) e r) (v : Fin m) :
    RootSet roots (e v) ↔ RootSet (fun i => r (roots i)) v := by
  constructor
  · rintro ⟨i, he⟩
    exact ⟨i, (congrArg r he).trans (h.inverse v)⟩
  · rintro ⟨i, he⟩
    have hr := h.retract (roots i) (h.terminals _ ⟨i, rfl⟩)
    exact ⟨i, hr.symm.trans (congrArg e he)⟩

theorem reindex_roots_injective {vertices : List (Fin n)} {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {e : Fin m → Fin n} {r : Fin n → Fin m}
    (h : GraphReindex vertices (List.finRange m) E (RootSet roots) e r)
    (hinj : Function.Injective roots) : Function.Injective (fun i => r (roots i)) := by
  intro i j he
  apply hinj
  have hi := h.retract (roots i) (h.terminals _ ⟨i, rfl⟩)
  have hj := h.retract (roots j) (h.terminals _ ⟨j, rfl⟩)
  exact hi.symm.trans ((congrArg e he).trans hj)

/-- The full capacitated invariant after contraction, now on a smaller `Fin m`
vertex type. This combines the cut theorem, reindexing, and exact count update. -/
theorem contraction_feasible_reindexed {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {capacity : Fin k → Nat} {label : Fin n → Fin k}
    {p : Fin n} {i : Fin k} {e : Fin m → Fin n} {r : Fin n → Fin m}
    (hinj : Function.Injective roots) (feasible : FeasibleAssignment E roots capacity label)
    (pnt : ¬RootSet roots p) (edge : E p (roots i))
    (sole : ∀ y, E p y → y = roots i)
    (h : GraphReindex ((List.finRange n).erase p) (List.finRange m)
      (Contract E p (roots i)) (RootSet roots) e r) :
    FeasibleAssignment (fun x y => Contract E p (roots i) (e x) (e y))
      (fun j => r (roots j)) (fun j => capacity j - if i = j then 1 else 0)
      (fun x => label (e x)) := by
  classical
  let G := fun x y => Contract E p (roots i) (e x) (e y)
  let roots' := fun j => r (roots j)
  have pred : (fun x => RootSet roots (e x)) = RootSet roots' := by
    funext x
    exact propext (reindex_rootSet h x)
  have evne (v : Fin m) : e v ≠ p := by
    intro he
    exact List.Nodup.not_mem_erase (finRange_nodup n) (he ▸ h.image_mem v)
  refine ⟨?_, ?_⟩
  · intro v hv
    have hnt : ¬RootSet roots (e v) := fun ht => hv ((reindex_rootSet h v).mp ht)
    obtain ⟨s, hs⟩ := exists_rank ((List.finRange n).erase p)
      (Contract E p (roots i)) (RootSet roots) (e v) hnt
    obtain ⟨_, ess⟩ := contraction_preserves_essential (finRange_nodup n) (mem_finRange p)
      (mem_finRange (roots i)) (evne v) pnt (show RootSet roots (roots i) from ⟨i, rfl⟩)
      (show RootSet roots (roots (label (e v))) from ⟨_, rfl⟩) edge sole
      (cutRank_spec E (RootSet roots) (e v) hnt) hs (feasible.1 (e v) hnt)
    have pulledRank := h.rank hs
    rw [pred] at pulledRank
    have eqrank := hasRank_unique pulledRank (cutRank_spec G (RootSet roots') v hv)
    have ht := h.retract (roots (label (e v))) (h.terminals _ ⟨_, rfl⟩)
    rw [← ht] at ess
    have pulled := h.essential ess
    rw [pred, eqrank] at pulled
    exact pulled
  · intro j
    have ei : Function.Injective e := by
      intro x y he
      exact (h.inverse x).symm.trans ((congrArg r he).trans (h.inverse y))
    have perm : ((nonterminals roots').map e).Perm ((nonterminals roots).erase p) := by
      apply nodup_perm_of_same_mem
        (nodup_map_of_injective (nonterminals_nodup roots') e (fun _ _ he => ei he))
        ((nonterminals_nodup roots).erase p)
      intro x
      constructor
      · rintro hx
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
        apply (List.mem_erase_of_ne (evne v)).mpr
        apply mem_nonterminals.mpr
        intro ht
        exact (mem_nonterminals.mp hv) ((reindex_rootSet h v).mp ht)
      · intro hx
        have xnt := mem_nonterminals.mp (List.mem_of_mem_erase hx)
        have xne : x ≠ p := fun he => List.Nodup.not_mem_erase (nonterminals_nodup roots) (he ▸ hx)
        have xm : x ∈ (List.finRange n).erase p := (List.mem_erase_of_ne xne).mpr (mem_finRange x)
        have ex := h.retract x xm
        refine List.mem_map.mpr ⟨r x, ?_, ex⟩
        apply mem_nonterminals.mpr
        intro ht
        have ht' := (reindex_rootSet h (r x)).mpr ht
        rw [ex] at ht'
        exact xnt ht'
    have cnt := countTrue_perm perm (fun x => label x = j)
    rw [countTrue_map] at cnt
    have oldcnt := countTrue_erase (mem_nonterminals.mpr pnt) (fun x => label x = j)
    have pi := sole_neighbor_assignment hinj feasible pnt edge sole
    rw [feasible.2 j, pi, ← cnt] at oldcnt
    change countTrue (nonterminals roots') (fun x => label (e x) = j) =
      capacity j - (if i = j then 1 else 0)
    omega

/-- A canonical erasure reindexing, using `Fin.succAbove`. -/
theorem exists_erase_reindex {n : Nat} (hn : 0 < n) (p : Fin (n + 1))
    (E : Fin (n + 1) → Fin (n + 1) → Prop) (T : Fin (n + 1) → Prop)
    (edges : ∀ x y, E x y → x ≠ p ∧ y ≠ p) (terminal : ¬T p) :
    ∃ r : Fin (n + 1) → Fin n,
      GraphReindex ((List.finRange (n + 1)).erase p) (List.finRange n) E T p.succAbove r := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let r := Function.invFun p.succAbove
  have inverse : ∀ x, r (p.succAbove x) = x := Function.leftInverse_invFun Fin.succAbove_right_injective
  have retract (x : Fin (n + 1)) (hx : x ≠ p) : p.succAbove (r x) = x :=
    Function.invFun_eq (Fin.exists_succAbove_eq hx)
  refine ⟨r, mem_finRange, inverse, ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply retract
    intro he
    exact List.Nodup.not_mem_erase (finRange_nodup (n+1)) (he ▸ hx)
  · apply nodup_perm_of_same_mem
      (nodup_map_of_injective (finRange_nodup n) p.succAbove (fun _ _ he => Fin.succAbove_right_injective he))
      ((finRange_nodup (n+1)).erase p)
    intro x
    constructor
    · intro hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
      exact (List.mem_erase_of_ne (Fin.succAbove_ne p v)).mpr (mem_finRange _)
    · intro hx
      have hxp : x ≠ p := fun he => List.Nodup.not_mem_erase (finRange_nodup (n+1)) (he ▸ hx)
      exact List.mem_map.mpr ⟨r x, mem_finRange _, retract x hxp⟩
  · intro x y he
    exact ⟨(List.mem_erase_of_ne (edges x y he).1).mpr (mem_finRange x),
      (List.mem_erase_of_ne (edges x y he).2).mpr (mem_finRange y)⟩
  · intro x hx
    have hxp : x ≠ p := fun he => terminal (he ▸ hx)
    exact (List.mem_erase_of_ne hxp).mpr (mem_finRange x)

end GyoriLovasz
