import GyoriLovasz.RuntimeRoundShape

namespace GyoriLovasz.WordInstance

def remainingStep (s : Input n k) (shape : Shape n k) (positive : 0 < shape.verticesCount) :
    Costed.Computation (Input shape.verticesCount shape.rootsCount × Vector (Fin shape.verticesCount) n) :=
  let reverse := ComputedReindex.inverse shape.vertices ⟨0, positive⟩
  let removed := removeGraph s.graph shape.removed
  let projected := project {s with graph := removed.1} shape.vertices shape.indices reverse.1
  ((projected.1, reverse.1), reverse.2 + removed.2 + projected.2 + 2)

theorem remainingStep_graph (s : Input n k) (shape : Shape n k) (positive : 0 < shape.verticesCount) :
    relation (remainingStep s shape positive).1.1 =
      fun x y => RemoveVertices (relation s) (SaturationPrune.selectedSet shape.removed)
        shape.vertices[x.val] shape.vertices[y.val] := by
  funext x y
  rw [show relation (remainingStep s shape positive).1.1 x y =
      relation {s with graph := (removeGraph s.graph shape.removed).1} shape.vertices[x.val] shape.vertices[y.val]
      from project_graph _ _ _ _ x y]
  exact congrFun (congrFun (removeGraph_relation s.graph shape.removed) shape.vertices[x.val]) shape.vertices[y.val]

theorem remainingStep_roots (s : Input n k) (shape : Shape n k) (positive : 0 < shape.verticesCount) :
    root (remainingStep s shape positive).1.1 =
      fun j => (ComputedReindex.inverse shape.vertices ⟨0, positive⟩).1[(root s shape.indices[j.val]).val] := by
  funext j
  exact project_root _ _ _ _ j

theorem remainingStep_weights (s : Input n k) (shape : Shape n k) (positive : 0 < shape.verticesCount) :
    weights (remainingStep s shape positive).1.1 = fun x => weights s shape.vertices[x.val] := by
  funext x
  exact project_weight _ _ _ _ x

theorem remainingStep_capacities (s : Input n k) (shape : Shape n k) (positive : 0 < shape.verticesCount) :
    capacities (remainingStep s shape positive).1.1 = fun j => capacities s shape.indices[j.val] := by
  funext j
  exact project_capacity _ _ _ _ j

theorem remainingStep_bounds (s : Input n k) (shape : Shape n k) (positive : 0 < shape.verticesCount)
    (B : Nat) (h : Bounded s B) : Bounded (remainingStep s shape positive).1.1 B :=
  project_bounds _ _ _ _ B h

theorem remainingStep_reindex (s : Input n k) (selected : Vector Bool k)
    (positive : 0 < (roundShape s selected).1.verticesCount) :
    GraphReindex (GyoriLovasz.retain (List.finRange n) (blockSet s selected))
      (List.finRange (roundShape s selected).1.verticesCount)
      (RemoveVertices (relation s) (blockSet s selected))
      (RemoveTerminals (RootSet (root s)) ((selectedRoots selected).image (root s)))
      (fun x => (roundShape s selected).1.vertices[x.val])
      (fun v => (ComputedReindex.inverse (roundShape s selected).1.vertices ⟨0, positive⟩).1[v.val]) := by
  have h := ComputedReindex.graphReindex (roundShape s selected).1.vertices ⟨0, positive⟩
    (roundShape_vertices_inj s selected) (RemoveVertices (relation s) (blockSet s selected))
    (RemoveTerminals (RootSet (root s)) ((selectedRoots selected).image (root s)))
    (by
      intro x y he
      rw [roundShape_vertices]
      simp [GyoriLovasz.retain, he.2.1, he.2.2])
    (by
      intro x hx
      have outside : x ∉ blockSet s selected := by
        intro hd
        rcases Finset.mem_union.mp hd with root | neighbor
        · exact hx.2 root
        · exact neighborSet_nonroot s selected x neighbor hx.1
      rw [roundShape_vertices]
      simp [GyoriLovasz.retain, outside])
  rwa [roundShape_vertices] at h

theorem remainingStep_valid (s : Input n k) (selected : Vector Bool k)
    (positive : 0 < (roundShape s selected).1.verticesCount)
    (positiveRoots : 0 < (roundShape s selected).1.rootsCount)
    (bound : Nat) (h : Valid s bound)
    (nonessential : ∀ i ∈ selectedRoots selected, ∀ v, ∀ hv : ¬RootSet (root s) v,
      v ∉ neighborSet s selected → ¬Essential (relation s) (RootSet (root s)) v hv (root s i)) :
    Valid (remainingStep s (roundShape s selected).1 positive).1.1 bound := by
  classical
  let shape := (roundShape s selected).1
  obtain ⟨x, hx⟩ := h.split
  have reindex := remainingStep_reindex s selected positive
  have reindexJ := ComputedReindex.graphReindex shape.indices ⟨0, positiveRoots⟩
    (roundShape_indices_inj s selected) (fun _ _ => False) (fun _ => False)
    (fun _ _ he => False.elim he) (fun _ he => False.elim he)
  have dne (j : Fin shape.rootsCount) : shape.indices[j.val] ∉ selectedRoots selected := by
    have mem := reindexJ.image_mem j
    rw [roundShape_indices] at mem
    exact of_decide_eq_true (List.mem_filter.mp mem).2
  have dret (j : Fin k) (outside : j ∉ selectedRoots selected) :
      shape.indices[(ComputedReindex.inverse shape.indices ⟨0, positiveRoots⟩).1[j.val].val] = j :=
    reindexJ.retract j (by rw [roundShape_indices]; simp [GyoriLovasz.retain, outside])
  have reduced := weighted_rounding_reindexed h.injective hx (selectedRoots selected) nonessential
    reindexJ.inverse dret dne reindex
  have rootmem (j : Fin shape.rootsCount) : root s shape.indices[j.val] ∈ GyoriLovasz.retain (List.finRange n) (blockSet s selected) := by
    apply reindex.terminals
    refine ⟨⟨shape.indices[j.val], rfl⟩, ?_⟩
    intro mem
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp mem
    exact dne j (h.injective he ▸ ha)
  constructor
  · rw [remainingStep_roots]
    exact reduced.1
  · intro j
    rw [remainingStep_roots, remainingStep_weights]
    dsimp only
    rw [reindex.retract _ (rootmem j)]
    exact h.rootzero _
  · exact h.boundPositive
  · intro v hv
    rw [remainingStep_weights]
    apply h.weightBounds
    intro ht
    apply hv
    rw [remainingStep_roots]
    exact (reduced.2.1 v).mp ht
  · rw [remainingStep_graph, roundShape_removed, remainingStep_roots, remainingStep_weights, remainingStep_capacities]
    exact ⟨_, reduced.2.2⟩

def remainingStepBudget (n m l : Nat) :=
  (2 * n * n + n * (2 * m * m + 7 * m + 10) + 3) +
  (2 * n * n * n + n * n * 13 + 9 * n + 3) + projectBudget m l + 2

theorem remainingStep_cost (s : Input n k) (shape : Shape n k) (positive : 0 < shape.verticesCount) :
    (remainingStep s shape positive).2 ≤ remainingStepBudget n shape.verticesCount shape.rootsCount := by
  have hi := ComputedReindex.inverse_cost shape.vertices ⟨0, positive⟩
  have hr := removeGraph_cost s.graph shape.removed
  have hp := project_cost {s with graph := (removeGraph s.graph shape.removed).1} shape.vertices shape.indices
    (ComputedReindex.inverse shape.vertices ⟨0, positive⟩).1
  dsimp only [remainingStep, remainingStepBudget]
  omega

end GyoriLovasz.WordInstance
