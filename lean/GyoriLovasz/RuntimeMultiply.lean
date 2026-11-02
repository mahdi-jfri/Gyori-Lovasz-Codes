import GyoriLovasz.RuntimeBinary
import Mathlib.Tactic.Ring

namespace GyoriLovasz.Binary

/-- Shift-and-add multiplication with an explicit Boolean/control counter. -/
def multiplyWords : List Bool → List Bool → List Bool × Nat
  | [], _ => ([], 1)
  | a :: as, b =>
    let rest := multiplyWords as b
    if a then
      let sum := addCarry b (false :: rest.1) false
      (sum.1, rest.2 + sum.2 + 4)
    else (false :: rest.1, rest.2 + 4)

theorem multiplyWords_value (a b : List Bool) : value (multiplyWords a b).1 = value a * value b := by
  induction a with
  | nil => simp [multiplyWords, value]
  | cons a as ih =>
    cases a <;> simp [multiplyWords, addCarry_correct, value, ih] <;> ring

theorem multiplyWords_length (a b : List Bool) :
    (multiplyWords a b).1.length ≤ 2 * a.length + b.length := by
  induction a with
  | nil => simp [multiplyWords]
  | cons a as ih =>
    have h := addCarry_length b (false :: (multiplyWords as b).1) false
    simp only [List.length_cons] at h
    cases a <;> simp only [multiplyWords, Bool.false_eq_true, if_false, if_true, List.length_cons]
    · omega
    · omega

theorem multiplyWords_cost (a b : List Bool) :
    (multiplyWords a b).2 ≤ a.length * (7 * (2 * a.length + b.length + 1) + 6) + 1 := by
  induction a with
  | nil => simp [multiplyWords]
  | cons a as ih =>
    have hl := multiplyWords_length as b
    have hc := addCarry_steps b (false :: (multiplyWords as b).1) false
    simp only [List.length_cons] at hc
    have hm := Nat.mul_le_mul_left as.length
      (show 7 * (2 * as.length + b.length + 1) + 6 ≤
        7 * (2 * (as.length + 1) + b.length + 1) + 6 by omega)
    cases a <;> simp only [multiplyWords, Bool.false_eq_true, if_false, if_true, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    · omega
    · omega

end GyoriLovasz.Binary
