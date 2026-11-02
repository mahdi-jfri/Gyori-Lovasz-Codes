import Std

/-!
Concrete cut algebra for directed graphs, following Sections 2--4 of
arXiv:2608.30945v1. This file does NOT assume the Gyori--Lovasz theorem.
Vertices are an arbitrary type; `size` counts separators over a supplied list.
For a finite graph use `Fin n` and `List.ofFn (fun i : Fin n => i)`.
-/
namespace GyoriLovasz

inductive Side where
  | left | sep | right
  deriving DecidableEq, Repr

open Side

def Side.union : Side → Side → Side
  | left, _ => left
  | _, left => left
  | sep, _ => sep
  | _, sep => sep
  | right, right => right

def Side.inter : Side → Side → Side
  | right, _ => right
  | _, right => right
  | sep, _ => sep
  | _, sep => sep
  | left, left => left

@[simp] theorem union_left (a b : Side) :
    a.union b = left ↔ a = left ∨ b = left := by
  cases a <;> cases b <;> simp [Side.union]

@[simp] theorem union_right (a b : Side) :
    a.union b = right ↔ a = right ∧ b = right := by
  cases a <;> cases b <;> simp [Side.union]

@[simp] theorem inter_left (a b : Side) :
    a.inter b = left ↔ a = left ∧ b = left := by
  cases a <;> cases b <;> simp [Side.inter]

@[simp] theorem inter_right (a b : Side) :
    a.inter b = right ↔ a = right ∨ b = right := by
  cases a <;> cases b <;> simp [Side.inter]

def Side.weight : Side → Nat
  | sep => 1
  | _ => 0

theorem weight_modular (a b : Side) :
    a.weight + b.weight = (a.union b).weight + (a.inter b).weight := by
  cases a <;> cases b <;> rfl

abbrev Cut (α : Type) := α → Side
def union (C D : Cut α) : Cut α := fun x => (C x).union (D x)
def inter (C D : Cut α) : Cut α := fun x => (C x).inter (D x)

def size (vertices : List α) (C : Cut α) : Nat :=
  match vertices with
  | [] => 0
  | x :: xs => (C x).weight + size xs C

theorem size_modular (vertices : List α) (C D : Cut α) :
    size vertices C + size vertices D =
      size vertices (union C D) + size vertices (inter C D) := by
  induction vertices with
  | nil => rfl
  | cons x xs ih =>
    have h := weight_modular (C x) (D x)
    simp only [size, union, inter] at *
    omega

structure Valid (E : α → α → Prop) (T : α → Prop) (v : α) (C : Cut α) : Prop where
  source : C v = right
  terminals : ∀ t, T t → C t ≠ right
  no_cross : ∀ x y, E x y → C x = right → C y ≠ left

theorem valid_union {E : α → α → Prop} {T : α → Prop} {v : α}
    {C D : Cut α} (hC : Valid E T v C) (hD : Valid E T v D) :
    Valid E T v (union C D) := by
  constructor
  · simp [union, hC.source, hD.source, Side.union]
  · intro t ht hr
    exact hC.terminals t ht ((union_right _ _).mp hr).1
  · intro x y he hx hy
    obtain ⟨hxC, hxD⟩ := (union_right _ _).mp hx
    rcases (union_left _ _).mp hy with hyC | hyD
    · exact hC.no_cross x y he hxC hyC
    · exact hD.no_cross x y he hxD hyD

theorem valid_inter {E : α → α → Prop} {T : α → Prop} {v : α}
    {C D : Cut α} (hC : Valid E T v C) (hD : Valid E T v D) :
    Valid E T v (inter C D) := by
  constructor
  · simp [inter, hC.source, hD.source, Side.inter]
  · intro t ht hr
    rcases (inter_right _ _).mp hr with h | h
    · exact hC.terminals t ht h
    · exact hD.terminals t ht h
  · intro x y he hx hy
    obtain ⟨hyC, hyD⟩ := (inter_left _ _).mp hy
    rcases (inter_right _ _).mp hx with hxC | hxD
    · exact hC.no_cross x y he hxC hyC
    · exact hD.no_cross x y he hxD hyD

def Minimum (vertices : List α) (E : α → α → Prop)
    (T : α → Prop) (v : α) (C : Cut α) : Prop :=
  Valid E T v C ∧ ∀ D, Valid E T v D → size vertices C ≤ size vertices D

theorem minimum_union_inter {vertices : List α} {E : α → α → Prop}
    {T : α → Prop} {v : α} {C D : Cut α}
    (hC : Minimum vertices E T v C) (hD : Minimum vertices E T v D) :
    Minimum vertices E T v (union C D) ∧
    Minimum vertices E T v (inter C D) := by
  have hu := valid_union hC.1 hD.1
  have hi := valid_inter hC.1 hD.1
  have hcu := hC.2 _ hu
  have hci := hC.2 _ hi
  have hcd := hC.2 _ hD.1
  have hdc := hD.2 _ hC.1
  have hm := size_modular vertices C D
  have eu : size vertices (union C D) = size vertices C := by omega
  have ei : size vertices (inter C D) = size vertices C := by omega
  exact ⟨⟨hu, fun F hF => eu ▸ hC.2 F hF⟩,
    ⟨hi, fun F hF => ei ▸ hC.2 F hF⟩⟩

def DeleteEdge (E : α → α → Prop) (p q : α) : α → α → Prop :=
  fun x y => E x y ∧ ¬(x = p ∧ y = q)

theorem valid_delete {E : α → α → Prop} {T : α → Prop} {v p q : α}
    {C : Cut α} (h : Valid E T v C) : Valid (DeleteEdge E p q) T v C :=
  ⟨h.source, h.terminals, fun x y he => h.no_cross x y he.1⟩

theorem valid_restore {E : α → α → Prop} {T : α → Prop} {v p q : α}
    {C : Cut α} (h : Valid (DeleteEdge E p q) T v C)
    (safe : ¬(C p = right ∧ C q = left)) : Valid E T v C := by
  classical
  refine ⟨h.source, h.terminals, ?_⟩
  intro x y he hx hy
  by_cases hpq : x = p ∧ y = q
  · obtain ⟨rfl, rfl⟩ := hpq
    exact safe ⟨hx, hy⟩
  · exact h.no_cross x y ⟨he, hpq⟩ hx hy

theorem invalid_restore_crosses {E : α → α → Prop} {T : α → Prop} {v p q : α}
    {C : Cut α} (h : Valid (DeleteEdge E p q) T v C)
    (invalid : ¬Valid E T v C) : C p = right ∧ C q = left := by
  classical
  by_cases crosses : C p = right ∧ C q = left
  · exact crosses
  · exact False.elim (invalid (valid_restore h crosses))

end GyoriLovasz
