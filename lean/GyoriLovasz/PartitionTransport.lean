import GyoriLovasz.Reconstruction
import GyoriLovasz.Transport
import GyoriLovasz.Matching

namespace GyoriLovasz

theorem ReachWithin.map {α β : Type} {E : α → α → Prop} {F : β → β → Prop}
    {A : α → Prop} {B : β → Prop} (e : α → β)
    (edges : ∀ x y, E x y → F (e x) (e y))
    (allowed : ∀ x, A x → B (e x)) {x y : α} (path : ReachWithin E A x y) :
    ReachWithin F B (e x) (e y) := by
  induction path with
  | refl x hx => exact .refl _ (allowed x hx)
  | step hx he rest ih => exact .step (allowed _ hx) (edges _ _ he) ih

theorem reindex_partition {vertices : List (Fin n)} {E : Fin n → Fin n → Prop}
    {T : Fin n → Prop} {roots : Fin k → Fin n} {sizes : Fin k → Nat}
    {e : Fin m → Fin n} {r : Fin n → Fin m}
    (h : GraphReindex vertices (List.finRange m) E T e r)
    (hroots : ∀ i, roots i ∈ vertices)
    (partition : PrescribedPartition (fun x y => E (e x) (e y)) (fun i => r (roots i)) sizes) :
    ∃ label, PartitionOn vertices (List.finRange k) E roots sizes label := by
  obtain ⟨label, rootlabels, counts, paths⟩ := partition
  refine ⟨fun x => label (r x), ⟨fun _ _ => mem_finRange _, ?_, ?_, ?_⟩⟩
  · intro i _
    exact ⟨hroots i, rootlabels i⟩
  · intro i _
    rw [← countTrue_perm h.enumeration, countTrue_map]
    have he : countTrue (List.finRange m) (fun x => label (r (e x)) = i) =
        countTrue (List.finRange m) (fun x => label x = i) := by
      apply countTrue_congr
      intro x _
      rw [h.inverse x]
    exact he.trans (counts i)
  · intro i _ x hx hl
    have path := (paths i (r x) hl).map e (fun _ _ he => he)
      (B := fun y => y ∈ vertices ∧ label (r y) = i)
      (fun y hy => ⟨h.image_mem y, by simpa [h.inverse y] using hy⟩)
    rw [h.retract x hx, h.retract (roots i) (hroots i)] at path
    exact path

theorem PartitionOn.map_indices {α β γ : Type} {vertices : List α} {indices : List β}
    {E : α → α → Prop} {roots : γ → α} {sizes : γ → Nat} {label : α → β}
    (d : β → γ) (inj : Function.Injective d)
    (partition : PartitionOn vertices indices E (fun j => roots (d j))
      (fun j => sizes (d j)) label) :
    PartitionOn vertices (indices.map d) E roots sizes (fun x => d (label x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact List.mem_map.mpr ⟨label x, partition.1 x hx, rfl⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hr, hl⟩ := partition.2.1 j hj
    exact ⟨hr, congrArg d hl⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have he := countTrue_congr vertices (P := fun x => d (label x) = d j)
      (Q := fun x => label x = j) (fun _ _ => ⟨fun he => inj he, congrArg d⟩)
    exact he.trans (partition.2.2.1 j hj)
  · intro i hi x hx hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact (partition.2.2.2 j hj x hx (inj hl)).mono_allowed
      (fun _ hy => ⟨hy.1, congrArg d hy.2⟩)

theorem PartitionOn.indices_perm {α β : Type} {vertices : List α} {indices indices' : List β}
    {E : α → α → Prop} {roots : β → α} {sizes : β → Nat} {label : α → β}
    (h : indices.Perm indices') (partition : PartitionOn vertices indices E roots sizes label) :
    PartitionOn vertices indices' E roots sizes label :=
  ⟨fun x hx => h.mem_iff.mp (partition.1 x hx),
    fun i hi => partition.2.1 i (h.mem_iff.mpr hi),
    fun i hi => partition.2.2.1 i (h.mem_iff.mpr hi),
    fun i hi => partition.2.2.2 i (h.mem_iff.mpr hi)⟩

theorem PartitionOn.to_prescribed {E F : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {sizes : Fin k → Nat} {label : Fin n → Fin k}
    (partition : PartitionOn (List.finRange n) (List.finRange k) F roots sizes label)
    (sub : ∀ x y, F x y → E x y) : PrescribedPartition E roots sizes := by
  refine ⟨label, fun i => (partition.2.1 i (mem_finRange i)).2,
    fun i => partition.2.2.1 i (mem_finRange i), ?_⟩
  intro i x hx
  exact ((partition.2.2.2 i (mem_finRange i) x (mem_finRange x) hx).mono_edges sub).mono_allowed
    (fun _ hy => hy.2)

theorem zero_capacity_not_assigned {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {capacity : Fin k → Nat} {label : Fin n → Fin k}
    (feasible : FeasibleAssignment E roots capacity label) {i : Fin k}
    (zero : capacity i = 0) {v : Fin n} (hv : ¬RootSet roots v) : label v ≠ i := by
  classical
  intro he
  have cnt := feasible.2 i
  rw [zero, countTrue_filter_length] at cnt
  have mem : v ∈ (nonterminals roots).filter (fun x => decide (label x = i)) := by
    simp [mem_nonterminals.mpr hv, he]
  have empty := List.length_eq_zero_iff.mp cnt
  rw [empty] at mem
  exact List.not_mem_nil mem

theorem all_zero_partition {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {capacity : Fin k → Nat} {label : Fin n → Fin k}
    (hinj : Function.Injective roots) (feasible : FeasibleAssignment E roots capacity label)
    (zero : ∀ i, capacity i = 0) : PrescribedPartition E roots (fun i => capacity i + 1) := by
  classical
  have allroot : ∀ v, RootSet roots v := by
    intro v
    by_cases hv : RootSet roots v
    · exact hv
    · exact False.elim (zero_capacity_not_assigned feasible (zero (label v)) hv rfl)
  let a := fun v => Classical.choose (allroot v)
  have root_a : ∀ v, roots (a v) = v := fun v => Classical.choose_spec (allroot v)
  have ar : ∀ i, a (roots i) = i := fun i => hinj (root_a (roots i))
  refine ⟨a, ar, ?_, ?_⟩
  · intro i
    have same : ∀ x, a x = i ↔ x = roots i := by
      intro x
      constructor
      · intro he; exact (root_a x).symm.trans (congrArg roots he)
      · intro he; subst x; exact ar i
    rw [countTrue_eq_card_filter]
    have he : Finset.univ.filter (fun x => a x = i) = {roots i} := by
      ext x
      simp [same x]
    rw [he]
    simp [zero i]
  · intro i x hx
    have he : x = roots i := (root_a x).symm.trans (congrArg roots hx)
    rw [he]
    exact .refl _ (ar i)

end GyoriLovasz

