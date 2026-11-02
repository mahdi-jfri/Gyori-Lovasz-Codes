import GyoriLovasz.Shrink
import GyoriLovasz.PartitionTransport

namespace GyoriLovasz

theorem terminal_feasible_reindexed {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {capacity : Fin k → Nat} {label : Fin n → Fin k}
    {i : Fin k} {e : Fin m → Fin n} {r : Fin n → Fin m}
    {d : Fin l → Fin k} {s : Fin k → Fin l}
    (hinj : Function.Injective roots) (feasible : FeasibleAssignment E roots capacity label)
    (zero : capacity i = 0)
    (dinv : ∀ j, s (d j) = j) (dret : ∀ j, j ≠ i → d (s j) = j)
    (dne : ∀ j, d j ≠ i)
    (h : GraphReindex ((List.finRange n).erase (roots i)) (List.finRange m)
      (DeleteVertex E (roots i)) (WithoutTerminal (RootSet roots) (roots i)) e r) :
    Function.Injective (fun j => r (roots (d j))) ∧
    FeasibleAssignment (fun x y => DeleteVertex E (roots i) (e x) (e y))
      (fun j => r (roots (d j))) (fun j => capacity (d j)) (fun x => s (label (e x))) := by
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
  have d_inj : Function.Injective d := by
    intro a b he
    exact (dinv a).symm.trans ((congrArg s he).trans (dinv b))
  refine ⟨?_, ?_, ?_⟩
  · intro a b he
    apply d_inj
    apply hinj
    exact (root_eq a).symm.trans ((congrArg e he).trans (root_eq b))
  · intro v hv
    have hnt : ¬RootSet roots (e v) := fun ht => hv ((root_iff v).mp ht)
    have hnt' : ¬WithoutTerminal (RootSet roots) (roots i) (e v) := fun ht => hnt ht.1
    have labne := zero_capacity_not_assigned feasible zero hnt
    obtain ⟨rank, hs⟩ := exists_rank ((List.finRange n).erase (roots i))
      (DeleteVertex E (roots i)) (WithoutTerminal (RootSet roots) (roots i)) (e v) hnt'
    have ess := terminal_removal_preserves_essential (finRange_nodup n) (mem_finRange (roots i))
      (evne v) (show RootSet roots (roots i) from ⟨i, rfl⟩)
      (show RootSet roots (roots (label (e v))) from ⟨_, rfl⟩)
      (show roots (label (e v)) ≠ roots i from fun he => labne (hinj he))
      (cutRank_spec E (RootSet roots) (e v) hnt) hs (feasible.1 (e v) hnt)
    have target : e (roots' (s (label (e v)))) = roots (label (e v)) := by
      rw [root_eq, dret _ labne]
    rw [← target] at ess
    have pulled := h.essential ess
    have pulledRank := h.rank hs
    rw [pred] at pulled pulledRank
    have eqrank := hasRank_unique pulledRank (cutRank_spec G (RootSet roots') v hv)
    rw [eqrank] at pulled
    exact pulled
  · intro j
    have ei : Function.Injective e := by
      intro x y he
      exact (h.inverse x).symm.trans ((congrArg r he).trans (h.inverse y))
    have perm : ((nonterminals roots').map e).Perm (nonterminals roots) := by
      apply nodup_perm_of_same_mem
        (nodup_map_of_injective (nonterminals_nodup roots') e (fun _ _ he => ei he))
        (nonterminals_nodup roots)
      intro x
      constructor
      · intro hx
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
        exact mem_nonterminals.mpr (fun ht => (mem_nonterminals.mp hv) ((root_iff v).mp ht))
      · intro hx
        have xnt := mem_nonterminals.mp hx
        have xne : x ≠ roots i := fun he => xnt ⟨i, he.symm⟩
        have xm := (List.mem_erase_of_ne xne).mpr (mem_finRange x)
        have ex := h.retract x xm
        refine List.mem_map.mpr ⟨r x, ?_, ex⟩
        apply mem_nonterminals.mpr
        intro ht
        have ht' := (root_iff (r x)).mpr ht
        rw [ex] at ht'
        exact xnt ht'
    have cnt := countTrue_perm perm (fun x => label x = d j)
    rw [countTrue_map, feasible.2 (d j)] at cnt
    have same : countTrue (nonterminals roots') (fun x => s (label (e x)) = j) =
        countTrue (nonterminals roots') (fun x => label (e x) = d j) := by
      apply countTrue_congr
      intro x hx
      have hnt : ¬RootSet roots (e x) := fun ht => (mem_nonterminals.mp hx) ((root_iff x).mp ht)
      have ne := zero_capacity_not_assigned feasible zero hnt
      exact ⟨fun he => (dret _ ne).symm.trans (congrArg d he),
        fun he => (congrArg s he).trans (dinv j)⟩
    exact same.trans cnt

end GyoriLovasz
