import GyoriLovasz.RuntimeBinary

namespace GyoriLovasz.Binary

/-- Seven Boolean gates combine one digit with the comparison of higher digits.
The first output is strict less-than; the second is equality. -/
def compareDigit (a b : Bool) (higher : Bool × Bool) : Bool × Bool :=
  (higher.1 || (higher.2 && (!a && b)), (!(xor a b)) && higher.2)

theorem compareDigit_correct (a b : Bool) (x y : Nat) (higher : Bool × Bool)
    (less : higher.1 = true ↔ x < y) (equal : higher.2 = true ↔ x = y) :
    ((compareDigit a b higher).1 = true ↔
      (if a then 1 else 0) + 2 * x < (if b then 1 else 0) + 2 * y) ∧
    ((compareDigit a b higher).2 = true ↔
      (if a then 1 else 0) + 2 * x = (if b then 1 else 0) + 2 * y) := by
  cases a <;> cases b <;> simp [compareDigit, less, equal] <;> omega

/-- Little-endian comparison with zero padding. The counter charges seven
Boolean gates and two control/result operations per digit, and two for the
base case. It describes this explicit circuit model, not compiled Lean timing. -/
def compareWords : List Bool → List Bool → (Bool × Bool) × Nat
  | [], [] => ((false, true), 2)
  | a :: as, [] =>
    let rest := compareWords as []
    (compareDigit a false rest.1, rest.2 + 9)
  | [], b :: bs =>
    let rest := compareWords [] bs
    (compareDigit false b rest.1, rest.2 + 9)
  | a :: as, b :: bs =>
    let rest := compareWords as bs
    (compareDigit a b rest.1, rest.2 + 9)
termination_by a b => a.length + b.length

theorem compareWords_correct (a b : List Bool) :
    ((compareWords a b).1.1 = true ↔ value a < value b) ∧
      ((compareWords a b).1.2 = true ↔ value a = value b) := by
  induction a generalizing b with
  | nil =>
    induction b with
    | nil => simp [compareWords, value]
    | cons b bs ih =>
      have digit := compareDigit_correct false b (value []) (value bs)
        (compareWords [] bs).1 ih.1 ih.2
      simpa only [compareWords, value, Bool.false_eq_true, if_false, Nat.zero_add, Nat.mul_zero] using digit
  | cons a as ih =>
    cases b with
    | nil =>
      have rest := ih []
      have digit := compareDigit_correct a false (value as) (value [])
        (compareWords as []).1 rest.1 rest.2
      simpa only [compareWords, value, Bool.false_eq_true, if_false, Nat.zero_add, Nat.mul_zero] using digit
    | cons b bs =>
      have rest := ih bs
      have digit := compareDigit_correct a b (value as) (value bs)
        (compareWords as bs).1 rest.1 rest.2
      simpa only [compareWords, value] using digit

theorem compareWords_steps (a b : List Bool) :
    (compareWords a b).2 = 9 * max a.length b.length + 2 := by
  induction a generalizing b with
  | nil =>
    induction b with
    | nil => simp [compareWords]
    | cons b bs ih => simp [compareWords, ih, Nat.mul_add, Nat.add_assoc]
  | cons a as ih =>
    cases b with
    | nil => simp [compareWords, ih, Nat.mul_add, Nat.add_assoc]
    | cons b bs => simp [compareWords, ih, Nat.mul_add, Nat.add_assoc, Nat.succ_max_succ]

end GyoriLovasz.Binary
