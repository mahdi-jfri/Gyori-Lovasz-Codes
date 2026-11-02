import GyoriLovasz.RuntimeCostedScan
import Mathlib.Tactic.Ring

namespace GyoriLovasz.Costed

def liftIndices : List (Fin n) → Computation (List (Fin (n + 1)))
  | [] => ([], 1)
  | i :: is =>
    let rest := liftIndices is
    (i.succ :: rest.1, rest.2 + 4)

theorem liftIndices_value (xs : List (Fin n)) : (liftIndices xs).1 = xs.map Fin.succ := by
  induction xs with
  | nil => rfl
  | cons i is ih => simp [liftIndices, ih]

theorem liftIndices_cost (xs : List (Fin n)) : (liftIndices xs).2 = 4 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons i is ih => simp [liftIndices, ih, Nat.mul_add, Nat.add_assoc]

/-- Explicit finite-index enumeration. Successor on an index is a reference-RAM
operation; the intentionally simple algorithm has a quadratic operation count. -/
def enumerateIndices : (n : Nat) → Computation (List (Fin n))
  | 0 => ([], 1)
  | n + 1 =>
    let old := enumerateIndices n
    let lifted := liftIndices old.1
    (0 :: lifted.1, old.2 + lifted.2 + 3)

theorem enumerateIndices_value (n : Nat) : (enumerateIndices n).1 = List.finRange n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [enumerateIndices, liftIndices_value, ih, List.finRange_succ]

theorem enumerateIndices_cost (n : Nat) : (enumerateIndices n).2 = 2 * n * n + 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [enumerateIndices, liftIndices_cost, enumerateIndices_value, List.length_finRange, ih]
    ring

def pairDirections : List α → Computation (List (α × Bool))
  | [] => ([], 1)
  | e :: es =>
    let rest := pairDirections es
    ((e, false) :: (e, true) :: rest.1, rest.2 + 5)

theorem pairDirections_value (xs : List α) :
    (pairDirections xs).1 = xs.flatMap (fun e => [(e, false), (e, true)]) := by
  induction xs with
  | nil => rfl
  | cons e es ih => simp [pairDirections, ih]

theorem pairDirections_cost (xs : List α) : (pairDirections xs).2 = 5 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons e es ih => simp [pairDirections, ih, Nat.mul_add, Nat.add_assoc]

def enumerateArcs (m : Nat) : Computation (List (Fin m × Bool)) :=
  let indices := enumerateIndices m
  let pairs := pairDirections indices.1
  (pairs.1, indices.2 + pairs.2 + 1)

theorem enumerateArcs_value (m : Nat) :
    (enumerateArcs m).1 = (List.finRange m).flatMap (fun e => [(e, false), (e, true)]) := by
  simp [enumerateArcs, pairDirections_value, enumerateIndices_value]

theorem enumerateArcs_cost (m : Nat) : (enumerateArcs m).2 = 2 * m * m + 7 * m + 3 := by
  simp only [enumerateArcs, enumerateIndices_cost, pairDirections_cost,
    enumerateIndices_value, List.length_finRange]
  ring

def append (xs ys : List α) : Computation (List α) :=
  match xs with
  | [] => (ys, 1)
  | x :: rest =>
    let tail := append rest ys
    (x :: tail.1, tail.2 + 2)

theorem append_value (xs ys : List α) : (append xs ys).1 = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, ih]

theorem append_cost (xs ys : List α) : (append xs ys).2 = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, ih, Nat.mul_add, Nat.add_assoc]

def pairWith (u : α) : List β → Computation (List (α × β))
  | [] => ([], 1)
  | v :: vs =>
    let rest := pairWith u vs
    ((u, v) :: rest.1, rest.2 + 4)

theorem pairWith_value (u : α) (vs : List β) : (pairWith u vs).1 = vs.map (u, ·) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [pairWith, ih]

theorem pairWith_cost (u : α) (vs : List β) : (pairWith u vs).2 = 4 * vs.length + 1 := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [pairWith, ih, Nat.mul_add, Nat.add_assoc]

def pairs (us : List α) (vs : List β) : Computation (List (α × β)) :=
  match us with
  | [] => ([], 1)
  | u :: rest =>
    let row := pairWith u vs
    let tail := pairs rest vs
    let joined := append row.1 tail.1
    (joined.1, row.2 + tail.2 + joined.2 + 1)

theorem pairs_value (us : List α) (vs : List β) :
    (pairs us vs).1 = us.flatMap (fun u => vs.map (u, ·)) := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [pairs, append_value, pairWith_value, ih]

theorem pairs_cost (us : List α) (vs : List β) :
    (pairs us vs).2 = us.length * (6 * vs.length + 3) + 1 := by
  induction us with
  | nil => simp [pairs]
  | cons u us ih =>
    simp only [pairs, pairWith_cost, append_cost, pairWith_value, List.length_map, List.length_cons, ih]
    ring

def enumeratePairs (n : Nat) : Computation (List (Fin n × Fin n)) :=
  let indices := enumerateIndices n
  let result := pairs indices.1 indices.1
  (result.1, indices.2 + result.2 + 1)

theorem enumeratePairs_value (n : Nat) :
    (enumeratePairs n).1 = (List.finRange n).flatMap (fun u => (List.finRange n).map (u, ·)) := by
  simp [enumeratePairs, pairs_value, enumerateIndices_value]

theorem enumeratePairs_cost (n : Nat) : (enumeratePairs n).2 = 8 * n * n + 5 * n + 3 := by
  simp only [enumeratePairs, enumerateIndices_cost, pairs_cost, enumerateIndices_value, List.length_finRange]
  ring

end GyoriLovasz.Costed
