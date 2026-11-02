import GyoriLovasz.Weighted

namespace GyoriLovasz
open scoped BigOperators

noncomputable def partLoad (V : Finset (Fin n)) (weight : Fin n → Nat)
    (label : Fin n → Fin k) (i : Fin k) : Nat := by
  classical
  exact ∑ x ∈ V, if label x = i then weight x else 0

/-- A partition on active vertices and root indices. Weights at roots are zero
when this interface is used for the generalized weighted theorem. -/
def WeightedPartitionOn (V : Finset (Fin n)) (J : Finset (Fin k))
    (E : Fin n → Fin n → Prop) (roots : Fin k → Fin n)
    (weight : Fin n → Nat) (limit : Fin k → Nat) (label : Fin n → Fin k) : Prop :=
  (∀ x ∈ V, label x ∈ J) ∧
  (∀ i ∈ J, roots i ∈ V ∧ label (roots i) = i) ∧
  (∀ i ∈ J, partLoad V weight label i ≤ limit i) ∧
  (∀ i ∈ J, ∀ x ∈ V, label x = i → ReachWithin E (fun y => y ∈ V ∧ label y = i) x (roots i))

theorem partLoad_restore {V : Finset (Fin n)} {weight : Fin n → Nat}
    {label : Fin n → Fin k} {p : Fin n} {i j : Fin k} (hp : p ∈ V) :
    partLoad V weight (restoreLabel label p i) j =
      partLoad (V.erase p) weight label j + if i = j then weight p else 0 := by
  classical
  unfold partLoad
  rw [← Finset.sum_erase_add V _ hp, restoreLabel_same]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [restoreLabel_other (Finset.mem_erase.mp hx).1]

theorem weighted_reconstruct_contraction {V : Finset (Fin n)} {J : Finset (Fin k)}
    {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n} {weight : Fin n → Nat}
    {limit : Fin k → Nat} {label : Fin n → Fin k} {p : Fin n} {i : Fin k}
    (hp : p ∈ V) (hi : i ∈ J) (edge : E p (roots i))
    (partition : WeightedPartitionOn (V.erase p) J (Contract E p (roots i)) roots weight limit label) :
    WeightedPartitionOn V J E roots weight (fun j => limit j + if i = j then weight p else 0)
      (restoreLabel label p i) := by
  classical
  have old (x : Fin n) (hx : x ∈ V.erase p) : restoreLabel label p i x = label x :=
    restoreLabel_other (Finset.mem_erase.mp hx).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases he : x = p
    · simpa [he, restoreLabel_same] using hi
    · rw [restoreLabel_other he]
      exact partition.1 x (Finset.mem_erase.mpr ⟨he, hx⟩)
  · intro j hj
    have root := partition.2.1 j hj
    exact ⟨Finset.mem_of_mem_erase root.1, (old _ root.1).trans root.2⟩
  · intro j hj
    rw [partLoad_restore hp]
    exact Nat.add_le_add_right (partition.2.2.1 j hj) _
  · intro j hj x hx hl
    by_cases he : x = p
    · subst x
      have ij : i = j := (restoreLabel_same label p i).symm.trans hl
      cases ij
      have root := partition.2.1 i hi
      exact .step ⟨hp, restoreLabel_same label p i⟩ edge
        (.refl _ ⟨Finset.mem_of_mem_erase root.1, (old _ root.1).trans root.2⟩)
    · have hx' := Finset.mem_erase.mpr ⟨he, hx⟩
      have path := partition.2.2.2 j hj x hx' ((old x hx').symm.trans hl)
      apply path.lift_contraction edge
      · intro y hy
        exact ⟨Finset.mem_of_mem_erase hy.1, (old y hy.1).trans hy.2⟩
      · intro ht
        exact ⟨hp, (restoreLabel_same label p i).trans ((partition.2.1 i hi).2.symm.trans ht.2)⟩

theorem weighted_reconstruct_terminal {V : Finset (Fin n)} {J : Finset (Fin k)}
    {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n} {weight : Fin n → Nat}
    {limit : Fin k → Nat} {label : Fin n → Fin k} {i : Fin k}
    (ht : roots i ∈ V) (hi : i ∈ J) (zero : weight (roots i) = 0)
    (partition : WeightedPartitionOn (V.erase (roots i)) (J.erase i)
      (DeleteVertex E (roots i)) roots weight limit label) :
    WeightedPartitionOn V J E roots weight limit (restoreLabel label (roots i) i) := by
  classical
  have old (x : Fin n) (hx : x ∈ V.erase (roots i)) :
      restoreLabel label (roots i) i x = label x := restoreLabel_other (Finset.mem_erase.mp hx).1
  have no_i (x : Fin n) (hx : x ∈ V.erase (roots i)) : label x ≠ i :=
    (Finset.mem_erase.mp (partition.1 x hx)).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases he : x = roots i
    · simpa [he, restoreLabel_same] using hi
    · have hx' := Finset.mem_erase.mpr ⟨he, hx⟩
      rw [old x hx']
      exact Finset.mem_of_mem_erase (partition.1 x hx')
  · intro j hj
    by_cases he : j = i
    · subst j; exact ⟨ht, restoreLabel_same label (roots i) i⟩
    · have root := partition.2.1 j (Finset.mem_erase.mpr ⟨he, hj⟩)
      exact ⟨Finset.mem_of_mem_erase root.1, (old _ root.1).trans root.2⟩
  · intro j hj
    rw [partLoad_restore ht]
    have hz : (if i = j then weight (roots i) else 0) = 0 := by simp [zero]
    rw [hz, Nat.add_zero]
    by_cases he : j = i
    · subst j
      have empty : partLoad (V.erase (roots i)) weight label i = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        exact if_neg (no_i x hx)
      rw [empty]
      exact Nat.zero_le _
    · exact partition.2.2.1 j (Finset.mem_erase.mpr ⟨he, hj⟩)
  · intro j hj x hx hl
    by_cases he : x = roots i
    · subst x
      have ij := (restoreLabel_same label (roots i) i).symm.trans hl
      cases ij
      exact .refl _ ⟨ht, restoreLabel_same label (roots i) i⟩
    · have hx' := Finset.mem_erase.mpr ⟨he, hx⟩
      have original := (old x hx').symm.trans hl
      have ji : j ≠ i := fun h => no_i x hx' (original.trans h)
      have path := partition.2.2.2 j (Finset.mem_erase.mpr ⟨ji, hj⟩) x hx' original
      exact (path.mono_edges (fun _ _ h => h.1)).mono_allowed
        (fun y hy => ⟨Finset.mem_of_mem_erase hy.1, (old y hy.1).trans hy.2⟩)

theorem WeightedPartitionOn.mono_edges {V : Finset (Fin n)} {J : Finset (Fin k)}
    {E F : Fin n → Fin n → Prop} {roots : Fin k → Fin n} {weight : Fin n → Nat}
    {limit : Fin k → Nat} {label : Fin n → Fin k}
    (part : WeightedPartitionOn V J E roots weight limit label) (sub : ∀ x y, E x y → F x y) :
    WeightedPartitionOn V J F roots weight limit label :=
  ⟨part.1, part.2.1, part.2.2.1, fun i hi x hx hl => (part.2.2.2 i hi x hx hl).mono_edges sub⟩

theorem WeightedPartitionOn.mono_limit {V : Finset (Fin n)} {J : Finset (Fin k)}
    {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n} {weight : Fin n → Nat}
    {a b : Fin k → Nat} {label : Fin n → Fin k}
    (part : WeightedPartitionOn V J E roots weight a label) (le : ∀ i ∈ J, a i ≤ b i) :
    WeightedPartitionOn V J E roots weight b label :=
  ⟨part.1, part.2.1, fun i hi => (part.2.2.1 i hi).trans (le i hi), part.2.2.2⟩

/-- Glue the rounded parts to the partition on all surviving vertices.
Disjoint root indices ensure that no load from the two pieces is combined. -/
theorem weighted_reconstruct_rounding {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {weight : Fin n → Nat} {limit : Fin k → Nat}
    (D : Finset (Fin n)) (S : Finset (Fin k)) {old rounded : Fin n → Fin k}
    (remaining : WeightedPartitionOn (Finset.univ \ D) (Finset.univ \ S) E roots weight limit old)
    (parts : WeightedPartitionOn D S E roots weight limit rounded) :
    ∃ label, WeightedPartitionOn Finset.univ Finset.univ E roots weight limit label := by
  classical
  let label := fun x => if x ∈ D then rounded x else old x
  have onD (x : Fin n) (hx : x ∈ D) : label x = rounded x := by simp [label, hx]
  have offD (x : Fin n) (hx : x ∈ Finset.univ \ D) : label x = old x := by
    simp [label, (Finset.mem_sdiff.mp hx).2]
  have loads (i : Fin k) : partLoad Finset.univ weight label i =
      partLoad (Finset.univ \ D) weight old i + partLoad D weight rounded i := by
    unfold partLoad
    rw [← Finset.sum_sdiff (Finset.subset_univ D)]
    congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      rw [offD x hx]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [onD x hx]
  refine ⟨label, (fun _ _ => Finset.mem_univ _), ?_, ?_, ?_⟩
  · intro i _
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hi : i ∈ S
    · have root := parts.2.1 i hi
      exact (onD _ root.1).trans root.2
    · have root := remaining.2.1 i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)
      exact (offD _ root.1).trans root.2
  · intro i _
    rw [loads]
    by_cases hi : i ∈ S
    · have zero : partLoad (Finset.univ \ D) weight old i = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        exact if_neg (fun (he : old x = i) => (Finset.mem_sdiff.mp (remaining.1 x hx)).2 (he.symm ▸ hi))
      rw [zero, Nat.zero_add]
      exact parts.2.2.1 i hi
    · have zero : partLoad D weight rounded i = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        exact if_neg (fun (he : rounded x = i) => hi (he ▸ parts.1 x hx))
      rw [zero, Nat.add_zero]
      exact remaining.2.2.1 i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)
  · intro i _ x _ hl
    by_cases hx : x ∈ D
    · have original := (onD x hx).symm.trans hl
      have hi : i ∈ S := original ▸ parts.1 x hx
      exact (parts.2.2.2 i hi x hx original).mono_allowed
        (fun y hy => ⟨Finset.mem_univ _, (onD y hy.1).trans hy.2⟩)
    · have hx' := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
      have original := (offD x hx').symm.trans hl
      have hi : i ∈ Finset.univ \ S := original ▸ remaining.1 x hx'
      exact (remaining.2.2.2 i hi x hx' original).mono_allowed
        (fun y hy => ⟨Finset.mem_univ _, (offD y hy.1).trans hy.2⟩)

end GyoriLovasz
