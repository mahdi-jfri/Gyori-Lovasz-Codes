import GyoriLovasz.RuntimeRootMatching
import GyoriLovasz.WeightedReconstruction

namespace GyoriLovasz
open scoped BigOperators

theorem glued_partition {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {weight : Fin n → Nat} {limit : Fin k → Nat}
    (D : Finset (Fin n)) (S : Finset (Fin k)) {old rounded : Fin n → Fin k}
    (remaining : WeightedPartitionOn (Finset.univ \ D) (Finset.univ \ S) E roots weight limit old)
    (parts : WeightedPartitionOn D S E roots weight limit rounded) :
    WeightedPartitionOn Finset.univ Finset.univ E roots weight limit (fun x => if x ∈ D then rounded x else old x) := by
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
  refine ⟨(fun _ _ => Finset.mem_univ _), ?_, ?_, ?_⟩
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

def joinLabels (removed : Vector Bool n) (old rounded : Vector (Fin k) n) :
    Costed.Computation (Vector (Fin k) n) :=
  Costed.tabulate n (fun v => (if removed[v.val] then rounded[v.val] else old[v.val], 4))

theorem joinLabels_value (removed : Vector Bool n) (old rounded : Vector (Fin k) n) (v : Fin n) :
    (joinLabels removed old rounded).1[v.val] =
      if v ∈ SaturationPrune.selectedSet removed then rounded[v.val] else old[v.val] := by
  simp only [joinLabels, Costed.tabulate_value, SaturationPrune.mem_selectedSet]

theorem joinLabels_cost (removed : Vector Bool n) (old rounded : Vector (Fin k) n) :
    (joinLabels removed old rounded).2 ≤ 2 * n * n + 10 * n + 3 := by
  simpa only [Nat.mul_comm n 10] using Costed.tabulate_cost n
    (fun v => (if removed[v.val] then rounded[v.val] else old[v.val], 4)) 4 (by intros; rfl)

theorem joinLabels_correct (removed : Vector Bool n) (old rounded : Vector (Fin k) n)
    (E : Fin n → Fin n → Prop) (roots : Fin k → Fin n) (weight : Fin n → Nat) (limit : Fin k → Nat)
    (S : Finset (Fin k))
    (remaining : WeightedPartitionOn (Finset.univ \ SaturationPrune.selectedSet removed) (Finset.univ \ S)
      E roots weight limit (fun v => old[v.val]))
    (parts : WeightedPartitionOn (SaturationPrune.selectedSet removed) S E roots weight limit (fun v => rounded[v.val])) :
    WeightedPartitionOn Finset.univ Finset.univ E roots weight limit
      (fun v => (joinLabels removed old rounded).1[v.val]) := by
  simp only [joinLabels_value]
  exact glued_partition _ S remaining parts

end GyoriLovasz

