import GyoriLovasz.RuntimeBinary

namespace GyoriLovasz.Binary

/-- Seven gates implement one digit of subtraction with borrow. -/
def fullSubtractor (a b borrow : Bool) : Bool × Bool :=
  (xor (xor a b) borrow, ((!a) && (b || borrow)) || (b && borrow))

theorem fullSubtractor_correct (a b borrow : Bool) :
    (if (fullSubtractor a b borrow).1 then 1 else 0) +
      (if b then 1 else 0) + (if borrow then 1 else 0) =
    (if a then 1 else 0) + 2 * (if (fullSubtractor a b borrow).2 then 1 else 0) := by
  cases a <;> cases b <;> cases borrow <;> decide

/-- Zero-padded subtraction. The final Boolean reports underflow. Each digit
charges seven gates, a branch, and an output cons in the bit-operation model. -/
def subBorrow : List Bool → List Bool → Bool → (List Bool × Bool) × Nat
  | [], [], borrow => (([], borrow), 2)
  | a :: as, [], borrow =>
    let digit := fullSubtractor a false borrow
    let rest := subBorrow as [] digit.2
    ((digit.1 :: rest.1.1, rest.1.2), rest.2 + 9)
  | [], b :: bs, borrow =>
    let digit := fullSubtractor false b borrow
    let rest := subBorrow [] bs digit.2
    ((digit.1 :: rest.1.1, rest.1.2), rest.2 + 9)
  | a :: as, b :: bs, borrow =>
    let digit := fullSubtractor a b borrow
    let rest := subBorrow as bs digit.2
    ((digit.1 :: rest.1.1, rest.1.2), rest.2 + 9)
termination_by a b _ => a.length + b.length

theorem subBorrow_length (a b : List Bool) (borrow : Bool) :
    (subBorrow a b borrow).1.1.length = max a.length b.length := by
  induction a generalizing b borrow with
  | nil =>
    induction b generalizing borrow with
    | nil => simp [subBorrow]
    | cons b bs ih => simp [subBorrow, ih]
  | cons a as ih =>
    cases b with
    | nil => simp [subBorrow, ih]
    | cons b bs => simp [subBorrow, ih, Nat.succ_max_succ]

theorem subBorrow_steps (a b : List Bool) (borrow : Bool) :
    (subBorrow a b borrow).2 = 9 * max a.length b.length + 2 := by
  induction a generalizing b borrow with
  | nil =>
    induction b generalizing borrow with
    | nil => simp [subBorrow]
    | cons b bs ih => simp [subBorrow, ih, Nat.mul_add, Nat.add_assoc]
  | cons a as ih =>
    cases b with
    | nil => simp [subBorrow, ih, Nat.mul_add, Nat.add_assoc]
    | cons b bs => simp [subBorrow, ih, Nat.mul_add, Nat.add_assoc, Nat.succ_max_succ]

theorem subBorrow_correct (a b : List Bool) (borrow : Bool) :
    value (subBorrow a b borrow).1.1 + value b + (if borrow then 1 else 0) =
      value a + 2 ^ max a.length b.length * (if (subBorrow a b borrow).1.2 then 1 else 0) := by
  induction a generalizing b borrow with
  | nil =>
    induction b generalizing borrow with
    | nil => cases borrow <;> simp [subBorrow, value]
    | cons b bs ih =>
      have digit := fullSubtractor_correct false b borrow
      have rest := ih (fullSubtractor false b borrow).2
      simp only [subBorrow, value, List.length_cons, List.length_nil, Nat.zero_max, Nat.pow_succ]
      simp only [value, List.length_nil, Nat.zero_max] at rest
      cases h : (subBorrow [] bs (fullSubtractor false b borrow).2).1.2 <;>
        simp only [h, Bool.false_eq_true, if_false, if_true, Nat.mul_zero, Nat.mul_one] at * <;> omega
  | cons a as ih =>
    cases b with
    | nil =>
      have digit := fullSubtractor_correct a false borrow
      have rest := ih [] (fullSubtractor a false borrow).2
      simp only [subBorrow, value, List.length_cons, List.length_nil, Nat.max_zero, Nat.pow_succ]
      simp only [value, List.length_nil, Nat.max_zero] at rest
      cases h : (subBorrow as [] (fullSubtractor a false borrow).2).1.2 <;>
        simp only [h, Bool.false_eq_true, if_false, if_true, Nat.mul_zero, Nat.mul_one] at * <;> omega
    | cons b bs =>
      have digit := fullSubtractor_correct a b borrow
      have rest := ih bs (fullSubtractor a b borrow).2
      simp only [subBorrow, value, List.length_cons, Nat.succ_max_succ, Nat.pow_succ]
      cases h : (subBorrow as bs (fullSubtractor a b borrow).2).1.2 <;>
        simp only [h, Bool.false_eq_true, if_false, if_true, Nat.mul_zero, Nat.mul_one] at * <;> omega

theorem value_lt_pow_length (a : List Bool) : value a < 2 ^ a.length := by
  induction a with
  | nil => simp [value]
  | cons b bs ih => cases b <;> simp only [value, List.length_cons, Nat.pow_succ,
      Bool.false_eq_true, if_false, if_true] <;> omega

theorem subBorrow_no_underflow (a b : List Bool) (borrow : Bool)
    (ordered : value b + (if borrow then 1 else 0) ≤ value a) :
    (subBorrow a b borrow).1.2 = false ∧
      value (subBorrow a b borrow).1.1 + value b + (if borrow then 1 else 0) = value a := by
  have correct := subBorrow_correct a b borrow
  have upper := value_lt_pow_length (subBorrow a b borrow).1.1
  rw [subBorrow_length] at upper
  cases h : (subBorrow a b borrow).1.2 with
  | false => exact ⟨rfl, by simpa [h] using correct⟩
  | true =>
    simp only [h, if_true, Nat.mul_one] at correct
    omega

end GyoriLovasz.Binary
