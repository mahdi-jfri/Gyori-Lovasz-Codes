import GyoriLovasz.RuntimeSignedArithmetic
import GyoriLovasz.RuntimeCostedScan

namespace GyoriLovasz.Costed
open Binary

/-- Minimum selection with the implemented signed-word comparison circuit. -/
def argminWordsLoop (score : α → Computation SignedWord) :
    List α → Option α → Computation (Option α)
  | [], best => (best, 1)
  | x :: xs, none =>
    let rest := argminWordsLoop score xs (some x)
    (rest.1, rest.2 + 3)
  | x :: xs, some best =>
    let sx := score x
    let sb := score best
    let comparison := compareSigned sx.1 sb.1
    let next := if comparison.1 then x else best
    let rest := argminWordsLoop score xs (some next)
    (rest.1, sx.2 + sb.2 + comparison.2 + rest.2 + 4)

theorem argminWordsLoop_value (score : α → Computation SignedWord)
    (xs : List α) (best : Option α) :
    (argminWordsLoop score xs best).1 =
      xs.foldl (List.argAux (fun x y => signedValue (score x).1 < signedValue (score y).1)) best := by
  induction xs generalizing best with
  | nil => rfl
  | cons x xs ih =>
    cases best with
    | none => simpa only [argminWordsLoop, List.foldl_cons, List.argAux] using ih (some x)
    | some best =>
      simp only [argminWordsLoop, List.foldl_cons, List.argAux, ih, compareSigned_correct]
      split <;> rfl

theorem argminWordsLoop_cost (score : α → Computation SignedWord)
    (xs : List α) (best : Option α) (S B : Nat)
    (scoreBound : ∀ x, (score x).2 ≤ S)
    (lengthBound : ∀ x, (score x).1.digits.length ≤ B) :
    (argminWordsLoop score xs best).2 ≤ xs.length * (2 * S + 9 * B + 11) + 1 := by
  induction xs generalizing best with
  | nil => simp [argminWordsLoop]
  | cons x xs ih =>
    cases best with
    | none =>
      have rest := ih (some x)
      simp only [argminWordsLoop, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    | some best =>
      have sx := scoreBound x
      have sb := scoreBound best
      have cmp := compareSigned_cost_bound (score x).1 (score best).1 B (lengthBound x) (lengthBound best)
      have rest := ih (some (if (compareSigned (score x).1 (score best).1).1 then x else best))
      simp only [argminWordsLoop, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

def filterArgminWords (eligible : α → Computation Bool) (score : α → Computation SignedWord)
    (xs : List α) : Computation (Option α) :=
  let kept := filter eligible xs
  let selected := argminWordsLoop score kept.1 none
  (selected.1, kept.2 + selected.2)

theorem filterArgminWords_value (eligible : α → Computation Bool)
    (score : α → Computation SignedWord) (xs : List α) :
    (filterArgminWords eligible score xs).1 =
      (xs.filter (fun x => (eligible x).1)).argmin (fun x => signedValue (score x).1) := by
  simp only [filterArgminWords, argminWordsLoop_value, filter_value, List.argmin]

theorem filterArgminWords_cost (eligible : α → Computation Bool)
    (score : α → Computation SignedWord) (xs : List α) (P S B : Nat)
    (predicateBound : ∀ x, (eligible x).2 ≤ P) (scoreBound : ∀ x, (score x).2 ≤ S)
    (lengthBound : ∀ x, (score x).1.digits.length ≤ B) :
    (filterArgminWords eligible score xs).2 ≤ xs.length * (P + 2 * S + 9 * B + 14) + 2 := by
  have filtering := filter_cost eligible xs P (fun x _ => predicateBound x)
  have selection := argminWordsLoop_cost score (filter eligible xs).1 none S B scoreBound lengthBound
  have len : (filter eligible xs).1.length ≤ xs.length := by
    rw [filter_value]
    exact List.length_filter_le _ _
  have scale := Nat.mul_le_mul_right (2 * S + 9 * B + 11) len
  change (filter eligible xs).2 + (argminWordsLoop score (filter eligible xs).1 none).2 ≤ _
  calc
    _ ≤ (xs.length * (P + 3) + 1) + (xs.length * (2 * S + 9 * B + 11) + 1) := by omega
    _ = _ := by simp only [Nat.mul_add]; omega

end GyoriLovasz.Costed
