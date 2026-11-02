import GyoriLovasz.RuntimeSignedCompare
import GyoriLovasz.RuntimeSubtract

namespace GyoriLovasz.Binary

/-- Add a nonnegative word to a negative word in negSucc convention. -/
def mixedAdd (positive negative : List Bool) : SignedWord × Nat :=
  let cmp := compareWords negative positive
  if cmp.1.1 then
    let difference := subBorrow positive negative true
    (⟨false, difference.1.1⟩, cmp.2 + difference.2 + 3)
  else
    let difference := subBorrow negative positive false
    (⟨true, difference.1.1⟩, cmp.2 + difference.2 + 3)

theorem mixedAdd_correct (positive negative : List Bool) :
    signedValue (mixedAdd positive negative).1 =
      (value positive : Int) - ((value negative : Int) + 1) := by
  have compare := (compareWords_correct negative positive).1
  dsimp only [mixedAdd]
  split
  · rename_i lt
    have order : value negative + 1 ≤ value positive := by have := compare.mp lt; omega
    have subtraction := (subBorrow_no_underflow positive negative true order).2
    simp only [signedValue, Bool.false_eq_true, if_false]
    simp only [if_true] at subtraction
    omega
  · rename_i nlt
    have order : value positive + 0 ≤ value negative := by
      have : ¬value negative < value positive := fun h => nlt (compare.mpr h)
      omega
    have subtraction := (subBorrow_no_underflow negative positive false order).2
    simp only [signedValue, if_true]
    simp only [Bool.false_eq_true, if_false, Nat.add_zero] at subtraction
    omega

theorem mixedAdd_steps (positive negative : List Bool) :
    (mixedAdd positive negative).2 = 18 * max positive.length negative.length + 7 := by
  dsimp only [mixedAdd]
  split <;> simp [compareWords_steps, subBorrow_steps, Nat.max_comm] <;> omega

theorem mixedAdd_length (positive negative : List Bool) :
    (mixedAdd positive negative).1.digits.length = max positive.length negative.length := by
  dsimp only [mixedAdd]
  split <;> simp [subBorrow_length, Nat.max_comm]

def addSigned (x y : SignedWord) : SignedWord × Nat :=
  if x.negative then
    if y.negative then
      let sum := addCarry x.digits y.digits true
      (⟨true, sum.1⟩, sum.2 + 3)
    else
      let sum := mixedAdd y.digits x.digits
      (sum.1, sum.2 + 2)
  else
    if y.negative then
      let sum := mixedAdd x.digits y.digits
      (sum.1, sum.2 + 2)
    else
      let sum := addCarry x.digits y.digits false
      (⟨false, sum.1⟩, sum.2 + 3)

theorem addSigned_correct (x y : SignedWord) :
    signedValue (addSigned x y).1 = signedValue x + signedValue y := by
  obtain ⟨xn, xd⟩ := x
  obtain ⟨yn, yd⟩ := y
  cases xn <;> cases yn
  · have sum := addCarry_correct xd yd false
    simp only [addSigned, signedValue, Bool.false_eq_true, if_false]
    simp only [Bool.false_eq_true, if_false, Nat.add_zero] at sum
    omega
  · simp only [addSigned, Bool.false_eq_true, if_false, if_true]
    rw [mixedAdd_correct]
    simp only [signedValue, Bool.false_eq_true, if_false, if_true]
    omega
  · simp only [addSigned, Bool.false_eq_true, if_false, if_true]
    rw [mixedAdd_correct]
    simp only [signedValue, Bool.false_eq_true, if_false, if_true]
    omega
  · have sum := addCarry_correct xd yd true
    simp only [addSigned, signedValue, if_true]
    simp only [if_true] at sum
    omega

theorem addSigned_cost_bound (x y : SignedWord) :
    (addSigned x y).2 ≤ 18 * max x.digits.length y.digits.length + 9 := by
  unfold addSigned
  split <;> split <;> simp only [addCarry_steps, mixedAdd_steps, Nat.max_comm] <;> omega

theorem addSigned_length (x y : SignedWord) :
    (addSigned x y).1.digits.length ≤ max x.digits.length y.digits.length + 1 := by
  unfold addSigned
  split <;> split
  · exact addCarry_length _ _ _
  · simp [mixedAdd_length, Nat.max_comm]
  · simp [mixedAdd_length]
  · exact addCarry_length _ _ _

def negateSigned (x : SignedWord) : SignedWord × Nat :=
  if x.negative then
    let increment := addCarry x.digits [] true
    (⟨false, increment.1⟩, increment.2 + 3)
  else
    let positive := compareWords [] x.digits
    if positive.1.1 then
      let decrement := subBorrow x.digits [] true
      (⟨true, decrement.1.1⟩, positive.2 + decrement.2 + 4)
    else (⟨false, []⟩, positive.2 + 4)

theorem negateSigned_correct (x : SignedWord) :
    signedValue (negateSigned x).1 = -signedValue x := by
  dsimp only [negateSigned]
  split
  · rename_i neg
    have sum := addCarry_correct x.digits [] true
    simp only [value, if_true, Nat.add_zero] at sum
    simp only [signedValue, neg, if_true, Bool.false_eq_true, if_false]
    omega
  · rename_i nonneg
    have cmp := (compareWords_correct [] x.digits).1
    simp only [value] at cmp
    split
    · rename_i pos
      have order : value [] + 1 ≤ value x.digits := by
        have := cmp.mp pos
        simp only [value]
        omega
      have sub := (subBorrow_no_underflow x.digits [] true order).2
      simp only [value, if_true, Nat.add_zero] at sub
      simp only [signedValue, if_true, if_neg nonneg]
      omega
    · rename_i zero
      have eq : value x.digits = 0 := by have := mt cmp.mpr zero; omega
      simp [signedValue, nonneg, value, eq]

theorem negateSigned_cost_bound (x : SignedWord) :
    (negateSigned x).2 ≤ 18 * x.digits.length + 8 := by
  dsimp only [negateSigned]
  split
  · simp [addCarry_steps]; omega
  · split <;> simp [compareWords_steps, subBorrow_steps] <;> omega

theorem negateSigned_length (x : SignedWord) :
    (negateSigned x).1.digits.length ≤ x.digits.length + 1 := by
  dsimp only [negateSigned]
  split
  · simpa using addCarry_length x.digits [] true
  · split <;> simp [subBorrow_length]

def subSigned (x y : SignedWord) : SignedWord × Nat :=
  let negative := negateSigned y
  let difference := addSigned x negative.1
  (difference.1, negative.2 + difference.2 + 2)

theorem subSigned_correct (x y : SignedWord) :
    signedValue (subSigned x y).1 = signedValue x - signedValue y := by
  simp only [subSigned, addSigned_correct, negateSigned_correct, Int.sub_eq_add_neg]

theorem subSigned_cost_bound (x y : SignedWord) :
    (subSigned x y).2 ≤ 36 * max x.digits.length y.digits.length + 37 := by
  have neg := negateSigned_cost_bound y
  have len := negateSigned_length y
  have sum := addSigned_cost_bound x (negateSigned y).1
  have maxbound : max x.digits.length (negateSigned y).1.digits.length ≤
      max x.digits.length y.digits.length + 1 := by omega
  dsimp only [subSigned]
  omega

theorem subSigned_length (x y : SignedWord) :
    (subSigned x y).1.digits.length ≤ max x.digits.length y.digits.length + 2 := by
  have neg := negateSigned_length y
  have sum := addSigned_length x (negateSigned y).1
  dsimp only [subSigned]
  omega

/-- Bit-level implementation of cost + tailPotential - headPotential. -/
def reducedCostWord (cost tailPotential headPotential : SignedWord) : SignedWord × Nat :=
  let sum := addSigned cost tailPotential
  let result := subSigned sum.1 headPotential
  (result.1, sum.2 + result.2 + 2)

theorem reducedCostWord_correct (cost tailPotential headPotential : SignedWord) :
    signedValue (reducedCostWord cost tailPotential headPotential).1 =
      signedValue cost + signedValue tailPotential - signedValue headPotential := by
  simp only [reducedCostWord, subSigned_correct, addSigned_correct]

theorem reducedCostWord_cost_bound (cost tailPotential headPotential : SignedWord) (B : Nat)
    (hc : cost.digits.length ≤ B) (ht : tailPotential.digits.length ≤ B)
    (hh : headPotential.digits.length ≤ B) :
    (reducedCostWord cost tailPotential headPotential).2 ≤ 54 * B + 84 := by
  have sum := addSigned_cost_bound cost tailPotential
  have len := addSigned_length cost tailPotential
  have sub := subSigned_cost_bound (addSigned cost tailPotential).1 headPotential
  have max₁ : max cost.digits.length tailPotential.digits.length ≤ B := by omega
  have max₂ : max (addSigned cost tailPotential).1.digits.length headPotential.digits.length ≤ B + 1 := by omega
  dsimp only [reducedCostWord]
  omega

theorem reducedCostWord_length (cost tailPotential headPotential : SignedWord) (B : Nat)
    (hc : cost.digits.length ≤ B) (ht : tailPotential.digits.length ≤ B)
    (hh : headPotential.digits.length ≤ B) :
    (reducedCostWord cost tailPotential headPotential).1.digits.length ≤ B + 3 := by
  have sum := addSigned_length cost tailPotential
  have sub := subSigned_length (addSigned cost tailPotential).1 headPotential
  dsimp only [reducedCostWord]
  omega

end GyoriLovasz.Binary
