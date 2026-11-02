import GyoriLovasz.TerminalRemoval
import GyoriLovasz.Specification
import GyoriLovasz.InputBridge
import Mathlib.Data.Finset.Card

namespace GyoriLovasz

variable {α β : Type*}

theorem ReachWithin.mono_edges {E F : α → α → Prop} {A : α → Prop} {x y : α}
    (h : ∀ u v, E u v → F u v) (path : ReachWithin E A x y) : ReachWithin F A x y := by
  induction path with
  | refl x hx => exact .refl x hx
  | step hx edge rest ih => exact .step hx (h _ _ edge) ih

theorem ReachWithin.trans {E : α → α → Prop} {A : α → Prop} {x y z : α}
    (first : ReachWithin E A x y) (second : ReachWithin E A y z) :
    ReachWithin E A x z := by
  induction first with
  | refl _ _ => exact second
  | step hx edge rest ih => exact .step hx edge (ih second)

/-- Expand every redirected arc through the vertex removed by contraction. -/
theorem ReachWithin.lift_contraction {E : α → α → Prop} {A B : α → Prop}
    {p t x y : α} (edge : E p t) (incl : ∀ v, A v → B v)
    (via : A t → B p) (path : ReachWithin (Contract E p t) A x y) :
    ReachWithin E B x y := by
  induction path with
  | refl x hx => exact .refl x (incl x hx)
  | @step x z y hx he rest ih =>
    rcases he.2.2 with old | redirected
    · exact .step (incl x hx) old ih
    · obtain ⟨xp, zt⟩ := redirected
      subst z
      exact .step (incl x hx) xp (.step (via rest.start_allowed) edge ih)

noncomputable def restoreLabel (label : α → β) (p : α) (i : β) : α → β := by
  classical
  exact fun x => if x = p then i else label x

theorem restoreLabel_same (label : α → β) (p : α) (i : β) : restoreLabel label p i p = i := by
  classical
  simp [restoreLabel]

theorem restoreLabel_other {label : α → β} {p x : α} {i : β} (h : x ≠ p) :
    restoreLabel label p i x = label x := by
  classical
  simp [restoreLabel, h]

theorem countTrue_erase [DecidableEq α] {vertices : List α} {p : α}
    (hp : p ∈ vertices) (P : α → Prop) [DecidablePred P] :
    countTrue vertices P = (if P p then 1 else 0) + countTrue (vertices.erase p) P := by
  have perm := List.perm_cons_erase hp
  rw [countTrue_perm perm]
  simp [countTrue]

theorem restoreLabel_count [DecidableEq α] [DecidableEq β] {vertices : List α}
    {label : α → β} {p : α} {i j : β} (hn : vertices.Nodup) (hp : p ∈ vertices) :
    countTrue vertices (fun x => restoreLabel label p i x = j) =
      (if i = j then 1 else 0) + countTrue (vertices.erase p) (fun x => label x = j) := by
  classical
  rw [countTrue_erase hp, restoreLabel_same]
  congr 1
  apply countTrue_congr
  intro x hx
  have hxp : x ≠ p := fun h => List.Nodup.not_mem_erase hn (h ▸ hx)
  rw [restoreLabel_other hxp]

/-- Partition data on a shrinking list of vertices and a shrinking list of
terminal indices. The label is total, but only active vertices are constrained. -/
def PartitionOn (vertices : List α) (indices : List β) (E : α → α → Prop)
    (roots : β → α) (sizes : β → Nat) (label : α → β) : Prop :=
  (∀ x, x ∈ vertices → label x ∈ indices) ∧
  (∀ i, i ∈ indices → roots i ∈ vertices ∧ label (roots i) = i) ∧
  (∀ i, i ∈ indices → countTrue vertices (fun x => label x = i) = sizes i) ∧
  (∀ i, i ∈ indices → ∀ x, x ∈ vertices → label x = i →
    ReachWithin E (fun y => y ∈ vertices ∧ label y = i) x (roots i))

/-- Reconstruct a connected partition after absorbing `p` into terminal `i`.
The part containing `i` gains exactly one vertex. -/
theorem reconstruct_contraction [DecidableEq α] [DecidableEq β]
    {vertices : List α} {indices : List β} {E : α → α → Prop}
    {roots : β → α} {sizes : β → Nat} {label : α → β} {p : α} {i : β}
    (hn : vertices.Nodup) (hp : p ∈ vertices) (hi : i ∈ indices)
    (edge : E p (roots i))
    (partition : PartitionOn (vertices.erase p) indices (Contract E p (roots i)) roots sizes label) :
    PartitionOn vertices indices E roots
      (fun j => sizes j + if i = j then 1 else 0) (restoreLabel label p i) := by
  classical
  have absent : p ∉ vertices.erase p := List.Nodup.not_mem_erase hn
  have old (x : α) (hx : x ∈ vertices.erase p) : restoreLabel label p i x = label x :=
    restoreLabel_other (fun h => absent (h ▸ hx))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxp : x = p
    · simpa [hxp, restoreLabel_same] using hi
    · have hxe := (List.mem_erase_of_ne hxp).mpr hx
      rw [old x hxe]
      exact partition.1 x hxe
  · intro j hj
    obtain ⟨hr, hl⟩ := partition.2.1 j hj
    exact ⟨List.mem_of_mem_erase hr, (old _ hr).trans hl⟩
  · intro j hj
    rw [restoreLabel_count hn hp, partition.2.2.1 j hj, Nat.add_comm]
  · intro j hj x hx hlabel
    have root := partition.2.1 j hj
    by_cases hxp : x = p
    · subst x
      have ij : i = j := (restoreLabel_same label p i).symm.trans hlabel
      cases ij
      exact .step ⟨hp, restoreLabel_same label p i⟩ edge
        (.refl _ ⟨List.mem_of_mem_erase root.1, (old _ root.1).trans root.2⟩)
    · have hxe := (List.mem_erase_of_ne hxp).mpr hx
      have original : label x = j := (old x hxe).symm.trans hlabel
      have path := partition.2.2.2 j hj x hxe original
      apply path.lift_contraction edge
      · intro y hy
        exact ⟨List.mem_of_mem_erase hy.1, (old y hy.1).trans hy.2⟩
      · intro ht
        have ij : i = j := (partition.2.1 i hi).2.symm.trans ht.2
        exact ⟨hp, (restoreLabel_same label p i).trans ij⟩

/-- Reinsert a removed zero-capacity terminal as a singleton part. -/
theorem reconstruct_terminal [DecidableEq α] [DecidableEq β]
    {vertices : List α} {indices : List β} {E : α → α → Prop}
    {roots : β → α} {sizes : β → Nat} {label : α → β} {i : β}
    (hn : vertices.Nodup) (hind : indices.Nodup) (hi : i ∈ indices)
    (ht : roots i ∈ vertices) (one : sizes i = 1)
    (partition : PartitionOn (vertices.erase (roots i)) (indices.erase i)
      (DeleteVertex E (roots i)) roots sizes label) :
    PartitionOn vertices indices E roots sizes (restoreLabel label (roots i) i) := by
  classical
  have absent : roots i ∉ vertices.erase (roots i) := List.Nodup.not_mem_erase hn
  have old (x : α) (hx : x ∈ vertices.erase (roots i)) :
      restoreLabel label (roots i) i x = label x :=
    restoreLabel_other (fun h => absent (h ▸ hx))
  have no_i (x : α) (hx : x ∈ vertices.erase (roots i)) : label x ≠ i := by
    intro he
    have mem := partition.1 x hx
    rw [he] at mem
    exact List.Nodup.not_mem_erase hind mem
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxt : x = roots i
    · simpa [hxt, restoreLabel_same] using hi
    · have hxe := (List.mem_erase_of_ne hxt).mpr hx
      rw [old x hxe]
      exact List.mem_of_mem_erase (partition.1 x hxe)
  · intro j hj
    by_cases hji : j = i
    · subst j; exact ⟨ht, restoreLabel_same label (roots i) i⟩
    · obtain ⟨hr, hl⟩ := partition.2.1 j ((List.mem_erase_of_ne hji).mpr hj)
      exact ⟨List.mem_of_mem_erase hr, (old _ hr).trans hl⟩
  · intro j hj
    rw [restoreLabel_count hn ht]
    by_cases hij : i = j
    · subst j
      have zero : countTrue (vertices.erase (roots i)) (fun x => label x = i) = 0 := by
        calc
          _ = countTrue (vertices.erase (roots i)) (fun _ => False) :=
            countTrue_congr _ (fun x hx => ⟨fun h => no_i x hx h, False.elim⟩)
          _ = 0 := by simp [countTrue_filter_length]
      simp [zero, one]
    · rw [if_neg hij, Nat.zero_add, partition.2.2.1 j ((List.mem_erase_of_ne (Ne.symm hij)).mpr hj)]
  · intro j hj x hx hlabel
    by_cases hxt : x = roots i
    · subst x
      have hij : i = j := (restoreLabel_same label (roots i) i).symm.trans hlabel
      cases hij
      exact .refl _ ⟨ht, restoreLabel_same label (roots i) i⟩
    · have hxe := (List.mem_erase_of_ne hxt).mpr hx
      have original : label x = j := (old x hxe).symm.trans hlabel
      have hji : j ≠ i := fun h => no_i x hxe (original.trans h)
      have path := partition.2.2.2 j ((List.mem_erase_of_ne hji).mpr hj) x hxe original
      exact (path.mono_edges (fun _ _ h => h.1)).mono_allowed
        (fun y hy => ⟨List.mem_of_mem_erase hy.1, (old y hy.1).trans hy.2⟩)

end GyoriLovasz


