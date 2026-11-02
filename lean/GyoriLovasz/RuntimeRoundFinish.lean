import GyoriLovasz.RuntimeRoundShape
import GyoriLovasz.RuntimeRoundData
import GyoriLovasz.RuntimeRoundedLabels

namespace GyoriLovasz.WordInstance
open TransportNetwork

theorem roundShape_no_roots (s : Input n k) (selected : Vector Bool k)
    (empty : (roundShape s selected).1.rootsCount = 0) : selectedRoots selected = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  by_contra outside
  have mem : i ∈ (roundShape s selected).1.indices.toList := by
    rw [roundShape_indices]
    simp [GyoriLovasz.retain, outside]
  have len := List.length_pos_of_mem mem
  simp [empty] at len

theorem roundShape_no_vertices (s : Input n k) (selected : Vector Bool k) (bound : Nat) (h : Valid s bound)
    (empty : (roundShape s selected).1.rootsCount = 0)
    (nonessential : ∀ i ∈ selectedRoots selected, ∀ v, ∀ hv : ¬RootSet (root s) v,
      v ∉ neighborSet s selected → ¬Essential (relation s) (RootSet (root s)) v hv (root s i)) :
    blockSet s selected = Finset.univ := by
  classical
  have allS := roundShape_no_roots s selected empty
  obtain ⟨split, feasible⟩ := h.split
  apply Finset.eq_univ_of_forall
  intro v
  by_cases ht : RootSet (root s) v
  · obtain ⟨i, hi⟩ := ht
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, allS.symm ▸ Finset.mem_univ _, hi⟩)
  · by_cases hn : v ∈ neighborSet s selected
    · exact Finset.mem_union_right _ hn
    · have zero : ∀ i, split v i = 0 := by
        intro i
        by_contra hz
        exact nonessential i (allS.symm ▸ Finset.mem_univ _) v ht hn
          (feasible.1 v ht i (Nat.pos_of_ne_zero hz))
      have row := feasible.2.1 v ht
      have positive := (h.weightBounds v ht).1
      simp [zero] at row
      omega

theorem roundData_partition (s : Input n k) (bound : Nat) (h : Valid s bound)
    (positive : ∀ i, 0 < capacities s i)
    (failure : ¬Saturates (fun i v => (rootNeighbors s.graph s.roots).1[i.val][v.val]) (fun _ => true)) :
    let data := (roundData s.graph s.roots failure).1
    WeightedPartitionOn (blockSet s data.1) (selectedRoots data.1) (relation s) (root s) (weights s)
      (fun i => capacities s i + bound - 1) (fun v => (roundedLabels s.roots data.2).1[v.val]) := by
  have d := roundData_correct s.graph s.roots h.injective failure
  let data := (roundData s.graph s.roots failure).1
  exact roundedLabels_partition (relation s) s.roots (weights s) (capacities s) bound h.injective h.rootzero
    (selectedRoots data.1) (neighborSet s data.1) data.2 d.2.1 (fun p hp => (d.2.2.1 p hp).1)
    (fun p hp => (d.2.2.1 p hp).2) (neighborSet_nonroot s data.1)
    (fun i _ => positive i) (fun p hp => (h.weightBounds p (neighborSet_nonroot s data.1 p hp)).2)

theorem roundData_finishes (s : Input n k) (bound : Nat) (h : Valid s bound)
    (positive : ∀ i, 0 < capacities s i)
    (failure : ¬Saturates (fun i v => (rootNeighbors s.graph s.roots).1[i.val][v.val]) (fun _ => true))
    (empty : (roundShape s (roundData s.graph s.roots failure).1.1).1.rootsCount = 0) :
    WeightedPartitionOn Finset.univ Finset.univ (relation s) (root s) (weights s)
      (fun i => capacities s i + bound - 1)
      (fun v => (roundedLabels s.roots (roundData s.graph s.roots failure).1.2).1[v.val]) := by
  have d := roundData_correct s.graph s.roots h.injective failure
  have allD := roundShape_no_vertices s (roundData s.graph s.roots failure).1.1 bound h empty d.2.2.2
  have allS := roundShape_no_roots s (roundData s.graph s.roots failure).1.1 empty
  have part := roundData_partition s bound h positive failure
  dsimp only at part
  rwa [allD, allS] at part

end GyoriLovasz.WordInstance
