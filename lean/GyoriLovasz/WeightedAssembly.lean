import GyoriLovasz.WeightedPartitionTransport
import GyoriLovasz.WeightedRoundingTransport
import GyoriLovasz.WeightedRoundedPartition
import GyoriLovasz.WeightedReduction

namespace GyoriLovasz
open scoped BigOperators

theorem GraphReindex.image_univ {vertices : List (Fin n)}
    {E : Fin n → Fin n → Prop} {T : Fin n → Prop} {e : Fin m → Fin n} {r : Fin n → Fin m}
    (h : GraphReindex vertices (List.finRange m) E T e r) :
    Finset.univ.image e = vertices.toFinset := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr (h.image_mem y)
  · intro hx
    exact Finset.mem_image.mpr ⟨r x, Finset.mem_univ _, h.retract x (List.mem_toFinset.mp hx)⟩

theorem finRange_erase_toFinset (p : Fin n) :
    ((List.finRange n).erase p).toFinset = Finset.univ.erase p := by
  classical
  ext x
  simp only [List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true]
  exact ⟨fun hx he => List.Nodup.not_mem_erase (finRange_nodup n) (he ▸ hx),
    fun hx => (List.mem_erase_of_ne hx).mpr (mem_finRange x)⟩

theorem retain_finRange_toFinset (D : Finset (Fin n)) :
    (retain (List.finRange n) D).toFinset = Finset.univ \ D := by
  classical
  ext x
  simp [retain, mem_finRange]

theorem retained_length_lt {D : Finset (Fin n)} (nonempty : D.Nonempty) :
    (retain (List.finRange n) D).length < n := by
  classical
  have hn : (retain (List.finRange n) D).Nodup := List.Pairwise.filter _ (finRange_nodup n)
  rw [← List.toFinset_card_of_nodup hn, retain_finRange_toFinset]
  have strict : Finset.univ \ D ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro he
    obtain ⟨x, hx⟩ := nonempty
    have h : x ∈ Finset.univ \ D := he.symm ▸ Finset.mem_univ x
    exact (Finset.mem_sdiff.mp h).2 hx
  simpa using Finset.card_lt_card strict

theorem weighted_positive_root {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {weight : Fin n → Nat} {capacity : Fin k → Nat} {split : Fin n → Fin k → Nat}
    (feasible : SplitFeasible E roots weight capacity split) {v : Fin n}
    (hv : ¬RootSet roots v) (positive : 0 < weight v) : ∃ i, 0 < capacity i := by
  classical
  have some : ∃ i, 0 < split v i := by
    by_contra h
    have zero : ∀ i, split v i = 0 := by intro i; have hi : ¬0 < split v i := fun hp => h ⟨i, hp⟩; omega
    have row := feasible.2.1 v hv
    simp [zero] at row
    omega
  obtain ⟨i, hi⟩ := some
  exact ⟨i, lt_of_lt_of_le hi (split_entry_le_capacity feasible hv i)⟩

theorem weighted_all_roots {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {weight : Fin n → Nat} {limit : Fin k → Nat} (hinj : Function.Injective roots)
    (rootzero : ∀ i, weight (roots i) = 0) (allroot : ∀ v, RootSet roots v) :
    ∃ label, WeightedPartitionOn Finset.univ Finset.univ E roots weight limit label := by
  classical
  let label := fun v => Classical.choose (allroot v)
  have root_label (v : Fin n) : roots (label v) = v := Classical.choose_spec (allroot v)
  have label_root (i : Fin k) : label (roots i) = i := hinj (root_label _)
  have zero (v : Fin n) : weight v = 0 := (congrArg weight (root_label v)).symm.trans (rootzero _)
  refine ⟨label, (fun _ _ => Finset.mem_univ _), (fun i _ => ⟨Finset.mem_univ _, label_root i⟩), ?_, ?_⟩
  · intro i _
    have load : partLoad Finset.univ weight label i = 0 := by simp [partLoad, zero]
    rw [load]; exact Nat.zero_le _
  · intro i _ x _ hx
    have he : x = roots i := (root_label x).symm.trans (congrArg roots hx)
    subst x
    exact .refl _ ⟨Finset.mem_univ _, label_root i⟩

/-- Normalized form used for induction: root weights are zero and loads count
all vertices. The public theorem restores the original root-excluding notation. -/
def NormalizedWeightedStatement (n : Nat) : Prop :=
  ∀ (k : Nat) (E : Fin n → Fin n → Prop) (roots : Fin k → Fin n)
    (weight : Fin n → Nat) (capacity : Fin k → Nat) (bound : Nat),
    Function.Injective roots → (∀ i, weight (roots i) = 0) → 0 < bound →
    (∀ v, ¬RootSet roots v → 0 < weight v ∧ weight v ≤ bound) →
    (∃ split, SplitFeasible E roots weight capacity split) →
    ∃ label, WeightedPartitionOn Finset.univ Finset.univ E roots weight
      (fun i => capacity i + bound - 1) label

end GyoriLovasz
