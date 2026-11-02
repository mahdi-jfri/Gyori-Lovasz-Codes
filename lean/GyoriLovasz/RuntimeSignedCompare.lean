import GyoriLovasz.RuntimeCompare

namespace GyoriLovasz.Binary

/-- A sign and a binary natural. Negative words denote -(value+1), matching
Lean's Int.negSucc representation and avoiding a separate negative zero. -/
structure SignedWord where
  negative : Bool
  digits : List Bool

def signedValue (x : SignedWord) : Int :=
  if x.negative then -((value x.digits : Int) + 1) else (value x.digits : Int)

/-- Compare magnitudes once, then combine their flags with the signs.
The counter adds a fixed five-operation sign-selection allowance. -/
def compareSigned (x y : SignedWord) : Bool × Nat :=
  let magnitude := compareWords x.digits y.digits
  let answer := if x.negative then
      if y.negative then !(magnitude.1.1 || magnitude.1.2) else true
    else if y.negative then false else magnitude.1.1
  (answer, magnitude.2 + 5)

theorem compareSigned_correct (x y : SignedWord) :
    (compareSigned x y).1 = true ↔ signedValue x < signedValue y := by
  obtain ⟨xn, xd⟩ := x
  obtain ⟨yn, yd⟩ := y
  have comparisons := compareWords_correct xd yd
  cases xn <;> cases yn <;>
    simp [compareSigned, signedValue, Bool.eq_false_iff, comparisons.1, comparisons.2] <;> omega

theorem compareSigned_steps (x y : SignedWord) :
    (compareSigned x y).2 = 9 * max x.digits.length y.digits.length + 7 := by
  simp [compareSigned, compareWords_steps, Nat.add_assoc]

theorem compareSigned_cost_bound (x y : SignedWord) (B : Nat)
    (hx : x.digits.length ≤ B) (hy : y.digits.length ≤ B) :
    (compareSigned x y).2 ≤ 9 * B + 7 := by
  rw [compareSigned_steps]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 9 (Nat.max_le.mpr ⟨hx, hy⟩)) 7

end GyoriLovasz.Binary
