import GyoriLovasz.WeightedTransport
import GyoriLovasz.WeightedSplitRounding

namespace GyoriLovasz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem weighted_rounding_reindexed {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {weight : Fin n → Nat} {capacity : Fin k → Nat}
    {split : Fin n → Fin k → Nat} (hinj : Function.Injective roots)
    (feasible : SplitFeasible E roots weight capacity split) (S : Finset (Fin k))
    (nonessential : ∀ i ∈ S, ∀ v, ∀ hv : ¬RootSet roots v,
      v ∉ S.biUnion (predecessorSet E roots) → ¬Essential E (RootSet roots) v hv (roots i))
    {e : Fin m → Fin n} {r : Fin n → Fin m} {d : Fin l → Fin k} {s : Fin k → Fin l}
    (dinv : ∀ j, s (d j) = j) (dret : ∀ j, j ∉ S → d (s j) = j) (dne : ∀ j, d j ∉ S)
    (h : GraphReindex (retain (List.finRange n) (S.image roots ∪ S.biUnion (predecessorSet E roots)))
      (List.finRange m) (RemoveVertices E (S.image roots ∪ S.biUnion (predecessorSet E roots)))
      (RemoveTerminals (RootSet roots) (S.image roots)) e r) :
    Function.Injective (fun j => r (roots (d j))) ∧
    (∀ v, RootSet roots (e v) ↔ RootSet (fun j => r (roots (d j))) v) ∧
    SplitFeasible (fun x y => RemoveVertices E (S.image roots ∪ S.biUnion (predecessorSet E roots)) (e x) (e y))
      (fun j => r (roots (d j))) (fun x => weight (e x)) (fun j => capacity (d j))
      (fun x j => split (e x) (d j)) := by
  classical
  let N := S.biUnion (predecessorSet E roots)
  let D := S.image roots ∪ N
  let G := fun x y => RemoveVertices E D (e x) (e y)
  let roots' := fun j => r (roots (d j))
  have evout (v : Fin m) : e v ∉ D := of_decide_eq_true (List.mem_filter.mp (h.image_mem v)).2
  have root_mem (j : Fin l) : roots (d j) ∈ retain (List.finRange n) D := by
    apply h.terminals
    refine ⟨⟨d j, rfl⟩, ?_⟩
    intro ht
    obtain ⟨a, ha, eq⟩ := Finset.mem_image.mp ht
    exact dne j (hinj eq ▸ ha)
  have root_eq (j : Fin l) : e (roots' j) = roots (d j) := h.retract _ (root_mem j)
  have root_iff (v : Fin m) : RootSet roots (e v) ↔ RootSet roots' v := by
    constructor
    · rintro ⟨j, he⟩
      have jne : j ∉ S := fun hj => evout v (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hj, he⟩))
      refine ⟨s j, ?_⟩
      change r (roots (d (s j))) = v
      rw [dret j jne, he, h.inverse v]
    · rintro ⟨j, he⟩
      exact ⟨d j, (root_eq j).symm.trans (congrArg e he)⟩
  have pred : (fun x => RemoveTerminals (RootSet roots) (S.image roots) (e x)) = RootSet roots' := by
    funext x
    apply propext
    exact ⟨fun ht => (root_iff x).mp ht.1, fun ht => ⟨(root_iff x).mpr ht,
      fun hx => evout x (Finset.mem_union_left _ hx)⟩⟩
  have oldpred : (fun x => RootSet roots (e x)) = RootSet roots' := funext (fun x => propext (root_iff x))
  have restricted := rounding_split_restriction feasible S nonessential
  have vmem (v : Fin m) (hv : ¬RootSet roots' v) :
      e v ∈ Finset.univ.filter (fun x => ¬RootSet roots x ∧ x ∉ N) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ht => hv ((root_iff v).mp ht),
      fun hn => evout v (Finset.mem_union_right _ hn)⟩
  refine ⟨?_, root_iff, ?_, ?_, ?_⟩
  · intro a b he
    have eq : d a = d b := hinj ((root_eq a).symm.trans ((congrArg e he).trans (root_eq b)))
    exact (dinv a).symm.trans ((congrArg s eq).trans (dinv b))
  · intro v hv j positive
    obtain ⟨rank, hr, ess⟩ := restricted.2.2 (e v) (vmem v hv) (d j) (dne j) positive
    rw [← root_eq j] at ess
    have pulled := h.essential ess
    have pulledRank := h.rank hr
    rw [pred] at pulled pulledRank
    have eqrank := hasRank_unique pulledRank (cutRank_spec G (RootSet roots') v hv)
    rw [eqrank] at pulled
    exact pulled
  · intro v hv
    have cnt : (∑ j, split (e v) (d j)) =
        ∑ j ∈ Finset.univ.filter (fun j => j ∉ S), split (e v) j := by
      apply Finset.sum_bij (fun j _ => d j)
      · intro j _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, dne j⟩
      · intro a _ b _ he
        exact (dinv a).symm.trans ((congrArg s he).trans (dinv b))
      · intro j hj
        exact ⟨s j, Finset.mem_univ _, dret j (Finset.mem_filter.mp hj).2⟩
      · intro _ _; rfl
    exact cnt.trans (restricted.1 (e v) (vmem v hv))
  · intro j
    have cnt := h.sum_filter (fun x => ¬RootSet roots x) (fun x => split x (d j))
    have seteq : (retain (List.finRange n) D).toFinset.filter (fun x => ¬RootSet roots x) =
        Finset.univ.filter (fun x => ¬RootSet roots x ∧ x ∉ N) := by
      ext x
      simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_univ, true_and]
      constructor
      · intro hx
        have outside : x ∉ D := by simpa [retain] using (List.mem_filter.mp hx.1).2
        exact ⟨hx.2, fun hn => outside (Finset.mem_union_right _ hn)⟩
      · intro hx
        refine ⟨?_, hx.1⟩
        have outside : x ∉ D := by
          intro hd
          rcases Finset.mem_union.mp hd with hr | hn
          · obtain ⟨a, _, he⟩ := Finset.mem_image.mp hr
            exact hx.1 ⟨a, he⟩
          · exact hx.2 hn
        simp [retain, mem_finRange, outside]
    change (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots' v), split (e v) (d j)) ≤ _
    rw [← oldpred]
    rw [seteq] at cnt
    rw [cnt]
    exact restricted.2.1 (d j)

end GyoriLovasz
