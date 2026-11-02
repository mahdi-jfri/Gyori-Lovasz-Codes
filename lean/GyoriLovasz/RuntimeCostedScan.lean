import GyoriLovasz.RuntimeCompare
import Mathlib.Data.List.MinMax

namespace GyoriLovasz.Costed

/-- Cost-accounted computations. Callbacks carry their costs explicitly;
no unaccounted callback is declared to take constant time. -/
abbrev Computation (α : Type) := α × Nat

/-- Charges one dispatch at termination. Each nonempty case charges dispatch
and branch; retaining an element also charges its list constructor. -/
def filter (p : α → Computation Bool) : List α → Computation (List α)
  | [] => ([], 1)
  | x :: xs =>
    let test := p x
    let rest := filter p xs
    if test.1 then (x :: rest.1, test.2 + rest.2 + 3)
    else (rest.1, test.2 + rest.2 + 2)

theorem filter_value (p : α → Computation Bool) (xs : List α) :
    (filter p xs).1 = xs.filter (fun x => (p x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [filter, List.filter_cons]; split <;> simp_all

theorem filter_cost (p : α → Computation Bool) (xs : List α) (C : Nat)
    (bound : ∀ x ∈ xs, (p x).2 ≤ C) : (filter p xs).2 ≤ xs.length * (C + 3) + 1 := by
  induction xs with
  | nil => simp [filter]
  | cons x xs ih =>
    have here := bound x (by simp)
    have rest := ih (fun y hy => bound y (by simp [hy]))
    simp only [filter, List.length_cons]
    split <;> simp only [Nat.add_mul, Nat.one_mul] <;> omega

/-- A short-circuiting search; callback cost is paid only for inspected elements. -/
def find (p : α → Computation Bool) : List α → Computation (Option α)
  | [] => (none, 1)
  | x :: xs =>
    let test := p x
    if test.1 then (some x, test.2 + 3) else
      let rest := find p xs
      (rest.1, test.2 + rest.2 + 2)

theorem find_value (p : α → Computation Bool) (xs : List α) :
    (find p xs).1 = xs.find? (fun x => (p x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [find, List.find?_cons]; split <;> simp_all

theorem find_cost (p : α → Computation Bool) (xs : List α) (C : Nat)
    (bound : ∀ x ∈ xs, (p x).2 ≤ C) : (find p xs).2 ≤ xs.length * (C + 3) + 1 := by
  induction xs with
  | nil => simp [find]
  | cons x xs ih =>
    have here := bound x (by simp)
    have rest := ih (fun y hy => bound y (by simp [hy]))
    simp only [find, List.length_cons]
    split <;> simp only [Nat.add_mul, Nat.one_mul] <;> omega

/-- Minimum selection explicitly evaluates and pays for both scores and their
comparison. The first minimum is retained on ties, as in List.argmin. -/
def argminLoop (score : α → Computation Int) (less : Int → Int → Computation Bool) :
    List α → Option α → Computation (Option α)
  | [], best => (best, 1)
  | x :: xs, none =>
    let rest := argminLoop score less xs (some x)
    (rest.1, rest.2 + 3)
  | x :: xs, some best =>
    let sx := score x
    let sb := score best
    let comparison := less sx.1 sb.1
    let next := if comparison.1 then x else best
    let rest := argminLoop score less xs (some next)
    (rest.1, sx.2 + sb.2 + comparison.2 + rest.2 + 4)

theorem argminLoop_value (score : α → Computation Int)
    (less : Int → Int → Computation Bool)
    (correct : ∀ x y, (less x y).1 = decide (x < y)) (xs : List α) (best : Option α) :
    (argminLoop score less xs best).1 =
      xs.foldl (List.argAux (fun x y => (score x).1 < (score y).1)) best := by
  induction xs generalizing best with
  | nil => rfl
  | cons x xs ih =>
    cases best with
    | none => simpa only [argminLoop, List.foldl_cons, List.argAux] using ih (some x)
    | some best =>
      simp only [argminLoop, List.foldl_cons, List.argAux, correct, decide_eq_true_eq, ih]
      split <;> rfl

theorem argminLoop_cost (score : α → Computation Int)
    (less : Int → Int → Computation Bool) (xs : List α) (best : Option α) (S C : Nat)
    (scoreBound : ∀ x, (score x).2 ≤ S)
    (compareBound : ∀ x y, (less (score x).1 (score y).1).2 ≤ C) :
    (argminLoop score less xs best).2 ≤ xs.length * (2 * S + C + 4) + 1 := by
  induction xs generalizing best with
  | nil => simp [argminLoop]
  | cons x xs ih =>
    cases best with
    | none =>
      have rest := ih (some x)
      simp only [argminLoop, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    | some best =>
      have sx := scoreBound x
      have sb := scoreBound best
      have cmp := compareBound x best
      have rest := ih (some (if (less (score x).1 (score best).1).1 then x else best))
      simp only [argminLoop, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

def argmin (score : α → Computation Int) (less : Int → Int → Computation Bool)
    (xs : List α) : Computation (Option α) := argminLoop score less xs none

theorem argmin_value (score : α → Computation Int) (less : Int → Int → Computation Bool)
    (correct : ∀ x y, (less x y).1 = decide (x < y)) (xs : List α) :
    (argmin score less xs).1 = xs.argmin (fun x => (score x).1) :=
  argminLoop_value score less correct xs none

/-- Compose candidate filtering and minimum selection without dropping either
callback's cost or the cost of traversing the retained candidate list. -/
def filterArgmin (p : α → Computation Bool) (score : α → Computation Int)
    (less : Int → Int → Computation Bool) (xs : List α) : Computation (Option α) :=
  let kept := filter p xs
  let selected := argmin score less kept.1
  (selected.1, kept.2 + selected.2)

theorem filterArgmin_value (p : α → Computation Bool) (score : α → Computation Int)
    (less : Int → Int → Computation Bool)
    (correct : ∀ x y, (less x y).1 = decide (x < y)) (xs : List α) :
    (filterArgmin p score less xs).1 =
      (xs.filter (fun x => (p x).1)).argmin (fun x => (score x).1) := by
  simp only [filterArgmin, argmin_value score less correct, filter_value]

theorem filterArgmin_cost (p : α → Computation Bool) (score : α → Computation Int)
    (less : Int → Int → Computation Bool) (xs : List α) (P S C : Nat)
    (predicateBound : ∀ x, (p x).2 ≤ P) (scoreBound : ∀ x, (score x).2 ≤ S)
    (compareBound : ∀ x y, (less (score x).1 (score y).1).2 ≤ C) :
    (filterArgmin p score less xs).2 ≤ xs.length * (P + 2 * S + C + 7) + 2 := by
  have filtering := filter_cost p xs P (fun x _ => predicateBound x)
  have selection := argminLoop_cost score less (filter p xs).1 none S C scoreBound compareBound
  have length : (filter p xs).1.length ≤ xs.length := by
    rw [filter_value]
    exact List.length_filter_le _ _
  have scale := Nat.mul_le_mul_right (2 * S + C + 4) length
  change (filter p xs).2 + (argminLoop score less (filter p xs).1 none).2 ≤ _
  calc
    _ ≤ (xs.length * (P + 3) + 1) + (xs.length * (2 * S + C + 4) + 1) := by omega
    _ = _ := by simp only [Nat.mul_add]; omega

end GyoriLovasz.Costed
