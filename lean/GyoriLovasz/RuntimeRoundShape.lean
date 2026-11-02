import GyoriLovasz.RuntimeActiveGeometry
import GyoriLovasz.RuntimeContractStep

namespace GyoriLovasz.WordInstance

structure Shape (n k : Nat) where
  removed : Vector Bool n
  verticesCount : Nat
  rootsCount : Nat
  vertices : Vector (Fin n) verticesCount
  indices : Vector (Fin k) rootsCount

def roundShape (s : Input n k) (selected : Vector Bool k) : Costed.Computation (Shape n k) :=
  let neighbors := rootNeighbors s.graph s.roots
  let removed := roundBlock neighbors.1 s.roots selected
  let keepVertices := complementMask removed.1
  let keepRoots := complementMask selected
  let vertices := ComputedReindex.active keepVertices.1
  let indices := ComputedReindex.active keepRoots.1
  (⟨removed.1, vertices.1.1, indices.1.1, vertices.1.2, indices.1.2⟩,
    neighbors.2 + removed.2 + keepVertices.2 + keepRoots.2 + vertices.2 + indices.2 + 5)

def selectedRoots (selected : Vector Bool k) := SaturationPrune.selectedSet selected
noncomputable def neighborSet (s : Input n k) (selected : Vector Bool k) :=
  (selectedRoots selected).biUnion (predecessorSet (relation s) (root s))
noncomputable def blockSet (s : Input n k) (selected : Vector Bool k) :=
  (selectedRoots selected).image (root s) ∪ neighborSet s selected

theorem roundShape_removed (s : Input n k) (selected : Vector Bool k) :
    SaturationPrune.selectedSet (roundShape s selected).1.removed = blockSet s selected :=
  roundBlock_set s.graph s.roots selected

theorem roundShape_vertices (s : Input n k) (selected : Vector Bool k) :
    (roundShape s selected).1.vertices.toList = GyoriLovasz.retain (List.finRange n) (blockSet s selected) := by
  have h := ComputedReindex.active_complement_list (roundBlock (rootNeighbors s.graph s.roots).1 s.roots selected).1
  rw [roundBlock_set] at h
  exact h

theorem roundShape_indices (s : Input n k) (selected : Vector Bool k) :
    (roundShape s selected).1.indices.toList = GyoriLovasz.retain (List.finRange k) (selectedRoots selected) :=
  ComputedReindex.active_complement_list selected

theorem roundShape_vertices_inj (s : Input n k) (selected : Vector Bool k) :
    Function.Injective (fun j : Fin (roundShape s selected).1.verticesCount => (roundShape s selected).1.vertices[j.val]) :=
  ComputedReindex.active_injective _

theorem roundShape_indices_inj (s : Input n k) (selected : Vector Bool k) :
    Function.Injective (fun j : Fin (roundShape s selected).1.rootsCount => (roundShape s selected).1.indices[j.val]) :=
  ComputedReindex.active_injective _

theorem neighborSet_nonroot (s : Input n k) (selected : Vector Bool k) (v : Fin n)
    (hv : v ∈ neighborSet s selected) : ¬RootSet (root s) v := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
  exact (Finset.mem_filter.mp hi).2.1

theorem roundShape_smaller (s : Input n k) (selected : Vector Bool k) (nonempty : (selectedRoots selected).Nonempty) :
    (roundShape s selected).1.verticesCount < n := by
  obtain ⟨i, hi⟩ := nonempty
  have mem : root s i ∈ blockSet s selected := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  rw [← roundShape_removed, SaturationPrune.mem_selectedSet] at mem
  apply ComputedReindex.active_size_lt
  refine ⟨root s i, ?_⟩
  simp only [complementMask, Costed.tabulate_value, show (roundShape s selected).1.removed =
    (roundBlock (rootNeighbors s.graph s.roots).1 s.roots selected).1 from rfl] at mem ⊢
  simp only [mem, Bool.not_true]

theorem roundShape_root_outside (s : Input n k) (selected : Vector Bool k) (inj : Function.Injective (root s))
    (i : Fin k) (hi : i ∉ selectedRoots selected) : root s i ∉ blockSet s selected := by
  intro mem
  rcases Finset.mem_union.mp mem with roots | neighbor
  · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp roots
    exact hi (inj he ▸ hj)
  · exact neighborSet_nonroot s selected (root s i) neighbor ⟨i, rfl⟩

theorem roundShape_positive (s : Input n k) (selected : Vector Bool k) (inj : Function.Injective (root s))
    (positiveRoots : 0 < (roundShape s selected).1.rootsCount) :
    0 < (roundShape s selected).1.verticesCount := by
  let j : Fin (roundShape s selected).1.rootsCount := ⟨0, positiveRoots⟩
  let i := (roundShape s selected).1.indices[j.val]
  have mem : i ∈ (roundShape s selected).1.indices.toList := by simp [i]
  rw [roundShape_indices] at mem
  have outside : i ∉ selectedRoots selected := of_decide_eq_true (List.mem_filter.mp mem).2
  have rootout := roundShape_root_outside s selected inj i outside
  apply ComputedReindex.active_positive
  refine ⟨root s i, ?_⟩
  apply complementMask_correct _ _ |>.mpr
  intro hm
  apply rootout
  rw [← roundShape_removed, SaturationPrune.mem_selectedSet]
  exact hm

theorem roundShape_counts (s : Input n k) (selected : Vector Bool k) :
    (roundShape s selected).1.verticesCount ≤ n ∧ (roundShape s selected).1.rootsCount ≤ k :=
  ⟨ComputedReindex.active_size_le _, ComputedReindex.active_size_le _⟩

def roundShapeBudget (n k : Nat) := rootNeighborBudget n k +
  (2 * n * n + n * (2 * k * k + 11 * k + 9) + 3) + (2 * n * n + 8 * n + 3) +
  (2 * k * k + 8 * k + 3) + (2 * n * n + 7 * n + 4) + (2 * k * k + 7 * k + 4) + 5

theorem roundShape_cost (s : Input n k) (selected : Vector Bool k) :
    (roundShape s selected).2 ≤ roundShapeBudget n k := by
  have hn := rootNeighbors_cost s.graph s.roots
  have hr := roundBlock_cost (rootNeighbors s.graph s.roots).1 s.roots selected
  have hv := complementMask_cost (roundBlock (rootNeighbors s.graph s.roots).1 s.roots selected).1
  have hi := complementMask_cost selected
  have av := ComputedReindex.active_cost (complementMask (roundBlock (rootNeighbors s.graph s.roots).1 s.roots selected).1).1
  have ai := ComputedReindex.active_cost (complementMask selected).1
  dsimp only [roundShape, roundShapeBudget]
  omega

end GyoriLovasz.WordInstance
