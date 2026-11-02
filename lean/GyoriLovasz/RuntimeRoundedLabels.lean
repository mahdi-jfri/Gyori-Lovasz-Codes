import GyoriLovasz.RuntimeReindex
import GyoriLovasz.WeightedRoundedPartition

namespace GyoriLovasz
open scoped BigOperators

def roundedLabels (roots : Vector (Fin n) k) (assignment : Vector (Fin k) n) :
    Costed.Computation (Vector (Fin k) n) :=
  Costed.tabulate n (fun v => let located := ComputedReindex.locate roots v;
    (located.1.getD assignment[v.val], located.2 + 2))

theorem roundedLabels_root (roots : Vector (Fin n) k) (assignment : Vector (Fin k) n)
    (inj : Function.Injective (fun i : Fin k => roots[i.val])) (i : Fin k) :
    (roundedLabels roots assignment).1[roots[i.val].val] = i := by
  obtain ⟨j, hj⟩ := ComputedReindex.locate_exists roots roots[i.val] ⟨i, rfl⟩
  have eq := inj (ComputedReindex.locate_some roots roots[i.val] j hj)
  simp only [roundedLabels, Costed.tabulate_value, hj, Option.getD_some, eq]

theorem roundedLabels_nonroot (roots : Vector (Fin n) k) (assignment : Vector (Fin k) n)
    (v : Fin n) (nt : ¬RootSet (fun i => roots[i.val]) v) :
    (roundedLabels roots assignment).1[v.val] = assignment[v.val] := by
  cases hs : (ComputedReindex.locate roots v).1 with
  | none => simp only [roundedLabels, Costed.tabulate_value, hs, Option.getD_none]
  | some i => exact False.elim (nt ⟨i, ComputedReindex.locate_some roots v i hs⟩)

theorem roundedLabels_cost (roots : Vector (Fin n) k) (assignment : Vector (Fin k) n) :
    (roundedLabels roots assignment).2 ≤ 2 * n * n + n * (2 * k * k + 7 * k + 11) + 3 := by
  have h := Costed.tabulate_cost n (fun v => let located := ComputedReindex.locate roots v;
    (located.1.getD assignment[v.val], located.2 + 2)) (2 * k * k + 7 * k + 5)
    (by intro v; have h := ComputedReindex.locate_cost roots v; dsimp only; omega)
  simpa only [roundedLabels, Nat.add_assoc] using h

theorem rounded_partition_from_labels {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {weight : Fin n → Nat} {capacity : Fin k → Nat} {bound : Nat}
    (rootzero : ∀ i, weight (roots i) = 0)
    (S : Finset (Fin k)) (N : Finset (Fin n)) (f label : Fin n → Fin k)
    (injective : Set.InjOn f N) (targets : ∀ p ∈ N, f p ∈ S)
    (edges : ∀ p ∈ N, E p (roots (f p))) (nonterminal : ∀ p ∈ N, ¬RootSet roots p)
    (positive : ∀ i ∈ S, 0 < capacity i) (upper : ∀ p ∈ N, weight p ≤ bound)
    (rootlabel : ∀ i, label (roots i) = i) (neighborlabel : ∀ x ∈ N, label x = f x) :
    WeightedPartitionOn (S.image roots ∪ N) S E roots weight (fun i => capacity i + bound - 1) label := by
  classical
  have basic := rounded_parts_valid S N f injective edges nonterminal positive upper
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with root | neighbor
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp root
      rw [rootlabel]
      exact hj
    · rw [neighborlabel x neighbor]
      exact targets x neighbor
  · intro i hi
    exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩), rootlabel i⟩
  · intro i hi
    have sumN : partLoad (S.image roots ∪ N) weight label i =
        ∑ x ∈ N, if label x = i then weight x else 0 := by
      unfold partLoad
      apply Finset.sum_union_eq_right
      intro x hx _
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      simp [rootzero]
    rw [sumN]
    have same : (∑ x ∈ N, if label x = i then weight x else 0) =
        ∑ x ∈ N.filter (fun x => f x = i), weight x := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      rw [neighborlabel x hx]
    rw [same]
    exact (basic i hi).1
  · intro i hi x hx hl
    have shape : x = roots i ∨ (x ∈ N ∧ f x = i) := by
      rcases Finset.mem_union.mp hx with root | neighbor
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp root
        have ji := (rootlabel j).symm.trans hl
        exact Or.inl (congrArg roots ji)
      · exact Or.inr ⟨neighbor, (neighborlabel x neighbor).symm.trans hl⟩
    exact ((basic i hi).2.1 x shape).mono_allowed (fun y hy => by
      rcases hy with he | neighbor
      · subst y
        exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩), rootlabel i⟩
      · exact ⟨Finset.mem_union_right _ neighbor.1, (neighborlabel y neighbor.1).trans neighbor.2⟩)

theorem roundedLabels_partition (E : Fin n → Fin n → Prop) (roots : Vector (Fin n) k)
    (weight : Fin n → Nat) (capacity : Fin k → Nat) (bound : Nat)
    (inj : Function.Injective (fun i : Fin k => roots[i.val])) (rootzero : ∀ i : Fin k, weight roots[i.val] = 0)
    (S : Finset (Fin k)) (N : Finset (Fin n)) (assignment : Vector (Fin k) n)
    (injective : Set.InjOn (fun v : Fin n => assignment[v.val]) N)
    (targets : ∀ p ∈ N, assignment[p.val] ∈ S)
    (edges : ∀ p ∈ N, E p roots[assignment[p.val].val])
    (nt : ∀ p ∈ N, ¬RootSet (fun i => roots[i.val]) p)
    (positive : ∀ i ∈ S, 0 < capacity i) (upper : ∀ p ∈ N, weight p ≤ bound) :
    WeightedPartitionOn (S.image (fun i => roots[i.val]) ∪ N) S E (fun i => roots[i.val]) weight
      (fun i => capacity i + bound - 1) (fun v => (roundedLabels roots assignment).1[v.val]) :=
  rounded_partition_from_labels rootzero S N _ _ injective targets edges nt positive upper
    (roundedLabels_root roots assignment inj) (fun v hv => roundedLabels_nonroot roots assignment v (nt v hv))

end GyoriLovasz
