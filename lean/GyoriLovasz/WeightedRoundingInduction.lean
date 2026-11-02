import GyoriLovasz.WeightedAssembly

namespace GyoriLovasz
open scoped BigOperators

theorem weighted_rounding_induction {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {weight : Fin n → Nat} {capacity : Fin k → Nat} {bound : Nat}
    {split : Fin n → Fin k → Nat} (ih : ∀ m, m < n → NormalizedWeightedStatement m)
    (hinj : Function.Injective roots) (rootzero : ∀ i, weight (roots i) = 0) (hb : 0 < bound)
    (weights : ∀ v, ¬RootSet roots v → 0 < weight v ∧ weight v ≤ bound)
    (feasible : SplitFeasible E roots weight capacity split) (positive : ∀ i, 0 < capacity i)
    (S : Finset (Fin k)) (nonempty : S.Nonempty) (f : Fin n → Fin k)
    (fi : Set.InjOn f (S.biUnion (predecessorSet E roots)))
    (fm : ∀ p ∈ S.biUnion (predecessorSet E roots), f p ∈ S ∧ E p (roots (f p)))
    (nonessential : ∀ i ∈ S, ∀ v, ∀ hv : ¬RootSet roots v,
      v ∉ S.biUnion (predecessorSet E roots) → ¬Essential E (RootSet roots) v hv (roots i)) :
    ∃ label, WeightedPartitionOn Finset.univ Finset.univ E roots weight
      (fun i => capacity i + bound - 1) label := by
  classical
  let N := S.biUnion (predecessorSet E roots)
  let D := S.image roots ∪ N
  have nnt : ∀ x ∈ N, ¬RootSet roots x := by
    intro x hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hj).2.1
  obtain ⟨rounded, parts⟩ := weighted_rounded_partition hinj rootzero S N f fi
    (fun p hp => (fm p hp).1) (fun p hp => (fm p hp).2) nnt (fun i _ => positive i)
    (fun p hp => (weights p (nnt p hp)).2)
  by_cases allS : S = Finset.univ
  · have allD : D = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro x
      by_cases ht : RootSet roots x
      · obtain ⟨i, hi⟩ := ht
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, allS.symm ▸ Finset.mem_univ _, hi⟩)
      · by_cases hn : x ∈ N
        · exact Finset.mem_union_right _ hn
        · have zero : ∀ i, split x i = 0 := by
            intro i
            by_contra hz
            exact nonessential i (allS.symm ▸ Finset.mem_univ _) x ht hn
              (feasible.1 x ht i (Nat.pos_of_ne_zero hz))
          have row := feasible.2.1 x ht
          have pos := (weights x ht).1
          simp [zero] at row
          omega
    rw [show S.image roots ∪ N = Finset.univ from allD, allS] at parts
    exact ⟨rounded, parts⟩
  · have some : ∃ j, j ∉ S := by
      by_contra h
      apply allS
      apply Finset.eq_univ_of_forall
      intro j
      by_contra hj
      exact h ⟨j, hj⟩
    obtain ⟨j, hj⟩ := some
    let J := retain (List.finRange k) S
    let V := retain (List.finRange n) D
    have jmem : j ∈ J := by simp [J, retain, mem_finRange, hj]
    have jpos : 0 < J.length := List.length_pos_of_mem jmem
    have rootout : roots j ∉ D := by
      intro hd
      rcases Finset.mem_union.mp hd with hr | hn
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hr
        exact hj (hinj he ▸ ha)
      · exact nnt _ hn ⟨j, rfl⟩
    have vmem : roots j ∈ V := by simp [V, retain, mem_finRange, rootout]
    have vpos : 0 < V.length := List.length_pos_of_mem vmem
    have jnodup : J.Nodup := List.Pairwise.filter _ (finRange_nodup k)
    have vnodup : V.Nodup := List.Pairwise.filter _ (finRange_nodup n)
    obtain ⟨s, hs⟩ := exists_active_reindex J jnodup jpos
      (fun _ _ => False) (fun _ => False) (fun _ _ h => False.elim h) (fun _ h => False.elim h)
    obtain ⟨r, hr⟩ := exists_active_reindex V vnodup vpos
      (RemoveVertices E D) (RemoveTerminals (RootSet roots) (S.image roots))
      (fun x y he => ⟨by simp [V, retain, mem_finRange, he.2.1], by simp [V, retain, mem_finRange, he.2.2]⟩)
      (fun x hx => by
        have outside : x ∉ D := by
          intro hd
          rcases Finset.mem_union.mp hd with ht | hn
          · exact hx.2 ht
          · exact nnt x hn hx.1
        simp [V, retain, mem_finRange, outside])
    have dne (a : Fin J.length) : J.get a ∉ S := of_decide_eq_true (List.mem_filter.mp (hs.image_mem a)).2
    have dret (a : Fin k) (ha : a ∉ S) : J.get (s a) = a :=
      hs.retract a (by simp [J, retain, mem_finRange, ha])
    obtain ⟨newinj, rootiff, newfeasible⟩ := weighted_rounding_reindexed hinj feasible S nonessential
      hs.inverse dret dne hr
    have rootmem (a : Fin J.length) : roots (J.get a) ∈ V := by
      apply hr.terminals
      refine ⟨⟨J.get a, rfl⟩, ?_⟩
      intro ht
      obtain ⟨b, hb, he⟩ := Finset.mem_image.mp ht
      exact dne a (hinj he ▸ hb)
    have smaller : V.length < n := by
      apply retained_length_lt
      obtain ⟨a, ha⟩ := nonempty
      exact ⟨roots a, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)⟩
    obtain ⟨label, part⟩ := ih V.length smaller J.length
      (fun x y => RemoveVertices E D (V.get x) (V.get y))
      (fun a => r (roots (J.get a))) (fun x => weight (V.get x)) (fun a => capacity (J.get a)) bound
      newinj (fun a => by dsimp only; rw [hr.retract _ (rootmem a)]; exact rootzero _)
      hb (fun x hx => weights (V.get x) (fun ht => hx ((rootiff x).mp ht))) ⟨_, newfeasible⟩
    have dinj : Function.Injective J.get := List.nodup_iff_injective_get.mp jnodup
    have lifted := weighted_partition_reindex (weight := weight) (limit := fun a => capacity a + bound - 1)
      hr dinj rootmem part
    have veq : V.toFinset = Finset.univ \ D := retain_finRange_toFinset D
    have jeq : Finset.univ.image J.get = Finset.univ \ S := hs.image_univ.trans (retain_finRange_toFinset S)
    rw [veq, jeq] at lifted
    exact weighted_reconstruct_rounding D S (lifted.mono_edges (fun _ _ he => he.1)) parts

end GyoriLovasz
