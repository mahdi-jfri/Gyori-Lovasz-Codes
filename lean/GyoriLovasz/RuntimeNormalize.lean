import GyoriLovasz.RuntimeSignedArithmetic
import Mathlib.Data.Nat.Size

namespace GyoriLovasz.Binary

/-- Remove redundant most-significant zeroes from a little-endian word.
Six charged control/gate/constructor operations per input digit. -/
def normalize : List Bool → List Bool × Nat
  | [] => ([], 1)
  | b :: bs =>
    let rest := normalize bs
    if rest.1.isEmpty && !b then ([], rest.2 + 6)
    else (b :: rest.1, rest.2 + 6)

theorem normalize_value (xs : List Bool) : value (normalize xs).1 = value xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    cases eq : (normalize bs).1 with
    | nil =>
      have zero : value bs = 0 := by rw [eq] at ih; simpa [value] using ih.symm
      cases b <;> simp [normalize, eq, value, zero]
    | cons c cs =>
      cases b <;> simp [normalize, eq, value] at ih ⊢ <;> omega

theorem normalize_steps (xs : List Bool) : (normalize xs).2 = 6 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    dsimp only [normalize]
    split <;> simp [ih, Nat.mul_add, Nat.add_assoc]

theorem normalize_eq_bits (xs : List Bool) : (normalize xs).1 = (value xs).bits := by
  induction xs with
  | nil => simp [normalize, value]
  | cons b bs ih =>
    cases b with
    | true =>
      dsimp only [normalize]
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false, value, if_true, ih]
      simpa only [Nat.add_comm] using (Nat.bit1_bits (value bs)).symm
    | false =>
      by_cases zero : value bs = 0
      · simp [normalize, ih, value, zero]
      · have nonempty : (normalize bs).1 ≠ [] := by
          intro eq
          have correct := normalize_value bs
          rw [eq] at correct
          exact zero (by simpa [value] using correct.symm)
        have emptiness : (normalize bs).1.isEmpty = false := by
          cases h : (normalize bs).1 with
          | nil => exact False.elim (nonempty h)
          | cons c cs => rfl
        dsimp only [normalize]
        rw [emptiness]
        simp only [Bool.false_and, Bool.false_eq_true, if_false, value, Nat.zero_add, ih]
        exact (Nat.bit0_bits (value bs) zero).symm

theorem normalize_length (xs : List Bool) : (normalize xs).1.length = (value xs).size := by
  rw [normalize_eq_bits, Nat.size_eq_bits_len]

theorem normalize_length_le (xs : List Bool) : (normalize xs).1.length ≤ xs.length := by
  rw [normalize_length]
  exact Nat.size_le.mpr (value_lt_pow_length xs)

def normalizeSigned (x : SignedWord) : SignedWord × Nat :=
  let normal := normalize x.digits
  (⟨x.negative, normal.1⟩, normal.2 + 1)

theorem normalizeSigned_value (x : SignedWord) :
    signedValue (normalizeSigned x).1 = signedValue x := by
  simp [normalizeSigned, signedValue, normalize_value]

theorem normalizeSigned_steps (x : SignedWord) :
    (normalizeSigned x).2 = 6 * x.digits.length + 2 := by
  simp [normalizeSigned, normalize_steps, Nat.add_assoc]

/-- Normalization connects the actual stored word length to mathematical
integer bit length, even for inputs with arbitrarily many redundant zeroes. -/
theorem normalizeSigned_length (x : SignedWord) :
    (normalizeSigned x).1.digits.length ≤ (signedValue x).natAbs.size := by
  simp only [normalizeSigned, normalize_length]
  apply Nat.size_le_size
  obtain ⟨negative, digits⟩ := x
  cases negative <;> simp [signedValue]
  omega

theorem normalizeSigned_length_of_value (x : SignedWord) (z : Int) (B : Nat)
    (valueCorrect : signedValue x = z) (bitBound : z.natAbs.size ≤ B) :
    (normalizeSigned x).1.digits.length ≤ B := by
  have bound := normalizeSigned_length x
  rw [valueCorrect] at bound
  exact Nat.le_trans bound bitBound

end GyoriLovasz.Binary
