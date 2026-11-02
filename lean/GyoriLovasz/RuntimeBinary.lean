import GyoriLovasz.Counting

namespace GyoriLovasz.Binary

/-- Little-endian binary words. Trailing zero bits are allowed. -/
def value : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * value bs

/-- Two XOR, two AND, and one OR gate. -/
def fullAdder (a b carry : Bool) : Bool × Bool :=
  let ab := xor a b
  (xor ab carry, (a && b) || (ab && carry))

theorem fullAdder_correct (a b carry : Bool) :
    (if (fullAdder a b carry).1 then 1 else 0) +
      2 * (if (fullAdder a b carry).2 then 1 else 0) =
    (if a then 1 else 0) + (if b then 1 else 0) + (if carry then 1 else 0) := by
  cases a <;> cases b <;> cases carry <;> decide

/-- Counted ripple-carry addition: seven bit-machine operations per digit
(five Boolean gates, one output cons, one branch), and two for termination. -/
def addCarry : List Bool → List Bool → Bool → List Bool × Nat
  | [], [], carry => (if carry then [true] else [], 2)
  | a :: as, [], carry =>
    let digit := fullAdder a false carry
    let rest := addCarry as [] digit.2
    (digit.1 :: rest.1, rest.2 + 7)
  | [], b :: bs, carry =>
    let digit := fullAdder false b carry
    let rest := addCarry [] bs digit.2
    (digit.1 :: rest.1, rest.2 + 7)
  | a :: as, b :: bs, carry =>
    let digit := fullAdder a b carry
    let rest := addCarry as bs digit.2
    (digit.1 :: rest.1, rest.2 + 7)
termination_by a b _ => a.length + b.length

theorem addCarry_correct (a b : List Bool) (carry : Bool) :
    value (addCarry a b carry).1 = value a + value b + (if carry then 1 else 0) := by
  induction a generalizing b carry with
  | nil =>
    induction b generalizing carry with
    | nil => cases carry <;> simp [addCarry, value]
    | cons b bs ih =>
      have digit := fullAdder_correct false b carry
      have rest := ih (fullAdder false b carry).2
      simp only [addCarry, value] at rest ⊢
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at digit
      omega
  | cons a as ih =>
    cases b with
    | nil =>
      have digit := fullAdder_correct a false carry
      have rest := ih [] (fullAdder a false carry).2
      simp only [addCarry, value] at rest ⊢
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at digit
      omega
    | cons b bs =>
      have digit := fullAdder_correct a b carry
      have rest := ih bs (fullAdder a b carry).2
      simp only [addCarry, value] at rest ⊢
      omega

theorem addCarry_steps (a b : List Bool) (carry : Bool) :
    (addCarry a b carry).2 = 7 * max a.length b.length + 2 := by
  induction a generalizing b carry with
  | nil =>
    induction b generalizing carry with
    | nil => simp [addCarry]
    | cons b bs ih => simp [addCarry, ih, Nat.mul_add, Nat.add_assoc]
  | cons a as ih =>
    cases b with
    | nil => simp [addCarry, ih, Nat.mul_add, Nat.add_assoc]
    | cons b bs => simp [addCarry, ih, Nat.mul_add, Nat.add_assoc, Nat.succ_max_succ]

theorem addCarry_length (a b : List Bool) (carry : Bool) :
    (addCarry a b carry).1.length ≤ max a.length b.length + 1 := by
  induction a generalizing b carry with
  | nil =>
    induction b generalizing carry with
    | nil => cases carry <;> simp [addCarry]
    | cons b bs ih => simpa [addCarry] using Nat.add_le_add_right (ih (fullAdder false b carry).2) 1
  | cons a as ih =>
    cases b with
    | nil => simpa [addCarry, Nat.add_assoc] using Nat.add_le_add_right (ih [] (fullAdder a false carry).2) 1
    | cons b bs => simpa [addCarry, Nat.succ_max_succ, Nat.add_assoc] using
        Nat.add_le_add_right (ih bs (fullAdder a b carry).2) 1

end GyoriLovasz.Binary
