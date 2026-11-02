import GyoriLovasz.RuntimeWordResidualGraph
import GyoriLovasz.RuntimeAugment

namespace GyoriLovasz.Flow
open Binary

/-- Arc-index equality is a reference-RAM operation, charged together with
direction selection. Signed arithmetic is performed on explicit bit lists. -/
def deltaWord (a : ResidualArc m) (e : Fin m) : SignedWord :=
  if a.1 = e then if a.2 then ⟨true, []⟩ else ⟨false, [true]⟩ else ⟨false, []⟩

theorem deltaWord_value (a : ResidualArc m) (e : Fin m) :
    signedValue (deltaWord a e) = arcDelta a e := by
  simp only [deltaWord, arcDelta]
  split <;> simp_all [signedValue, value]
  split <;> simp [signedValue, value]

theorem deltaWord_length (a : ResidualArc m) (e : Fin m) :
    (deltaWord a e).digits.length ≤ 1 := by
  unfold deltaWord
  split
  · split <;> simp
  · simp

def sumDelta (e : Fin m) : List (ResidualArc m) → Costed.Computation SignedWord
  | [] => (⟨false, []⟩, 1)
  | a :: p =>
    let rest := sumDelta e p
    let sum := addSigned (deltaWord a e) rest.1
    (sum.1, rest.2 + sum.2 + 6)

theorem sumDelta_value (e : Fin m) (p : List (ResidualArc m)) :
    signedValue (sumDelta e p).1 = routeDelta p e := by
  induction p with
  | nil => simp [sumDelta, routeDelta, signedValue, value]
  | cons a p ih => simp [sumDelta, addSigned_correct, deltaWord_value, ih, routeDelta_cons]

theorem sumDelta_length (e : Fin m) (p : List (ResidualArc m)) :
    (sumDelta e p).1.digits.length ≤ p.length + 1 := by
  induction p with
  | nil => simp [sumDelta]
  | cons a p ih =>
    have hd := deltaWord_length a e
    have ha := addSigned_length (deltaWord a e) (sumDelta e p).1
    simp only [sumDelta, List.length_cons]
    omega

theorem sumDelta_cost (e : Fin m) (p : List (ResidualArc m)) :
    (sumDelta e p).2 ≤ p.length * (18 * (p.length + 1) + 15) + 1 := by
  induction p with
  | nil => simp [sumDelta]
  | cons a p ih =>
    have hd := deltaWord_length a e
    have hr := sumDelta_length e p
    have ha := addSigned_cost_bound (deltaWord a e) (sumDelta e p).1
    have hc : (addSigned (deltaWord a e) (sumDelta e p).1).2 ≤ 18 * (p.length + 1) + 9 := by
      omega
    simp only [sumDelta, List.length_cons]
    have mono : p.length * (18 * (p.length + 1) + 15) ≤
        p.length * (18 * (p.length + 1 + 1) + 15) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.add_mul, Nat.one_mul]
    omega

def augmentCell (flow : Vector (List Bool) m) (p : List (ResidualArc m)) (e : Fin m) :
    Costed.Computation (List Bool) :=
  let delta := sumDelta e p
  let sum := addSigned ⟨false, flow[e.val]⟩ delta.1
  (naturalWord sum.1, delta.2 + sum.2 + 5)

theorem augmentCell_value (flow : Vector (List Bool) m) (p : List (ResidualArc m)) (e : Fin m) :
    value (augmentCell flow p e).1 = augment (fun e => value flow[e.val]) (routeDelta p) e := by
  dsimp only [augmentCell]
  rw [naturalWord_value, addSigned_correct, sumDelta_value]
  simp [signedValue, augment]

theorem augmentCell_cost (flow : Vector (List Bool) m) (B : Nat)
    (bound : ∀ e : Fin m, flow[e.val].length ≤ B) (p : List (ResidualArc m)) (e : Fin m) :
    (augmentCell flow p e).2 ≤
      p.length * (18 * (p.length + 1) + 15) + 18 * (B + p.length + 1) + 15 := by
  have hd := sumDelta_cost e p
  have hl := sumDelta_length e p
  have hb := bound e
  have ha := addSigned_cost_bound ⟨false, flow[e.val]⟩ (sumDelta e p).1
  dsimp only at ha
  dsimp only [augmentCell]
  omega

def augmentWords (flow : Vector (List Bool) m) (p : List (ResidualArc m)) :
    Costed.Computation (Vector (List Bool) m) := Costed.tabulate m (augmentCell flow p)

theorem augmentWords_value (flow : Vector (List Bool) m) (p : List (ResidualArc m)) (e : Fin m) :
    value (augmentWords flow p).1[e.val] = augment (fun e => value flow[e.val]) (routeDelta p) e := by
  rw [augmentWords, Costed.tabulate_value]
  exact augmentCell_value flow p e

theorem augmentWords_cost (flow : Vector (List Bool) m) (B : Nat)
    (bound : ∀ e : Fin m, flow[e.val].length ≤ B) (p : List (ResidualArc m)) :
    (augmentWords flow p).2 ≤ 2 * m * m +
      m * (p.length * (18 * (p.length + 1) + 15) + 18 * (B + p.length + 1) + 21) + 3 := by
  have h := Costed.tabulate_cost m (augmentCell flow p)
    (p.length * (18 * (p.length + 1) + 15) + 18 * (B + p.length + 1) + 15)
    (augmentCell_cost flow B bound p)
  simpa only [augmentWords, Nat.add_assoc] using h

def augmentBudget (m B L : Nat) :=
  2 * m * m + m * (L * (18 * (L + 1) + 15) + 18 * (B + L + 1) + 21) + 3

theorem augmentWords_cost_le (flow : Vector (List Bool) m) (B L : Nat)
    (bound : ∀ e : Fin m, flow[e.val].length ≤ B) (p : List (ResidualArc m))
    (length : p.length ≤ L) : (augmentWords flow p).2 ≤ augmentBudget m B L := by
  have h := augmentWords_cost flow B bound p
  have hmul := Nat.mul_le_mul length
    (show 18 * (p.length + 1) + 15 ≤ 18 * (L + 1) + 15 by omega)
  have houter := Nat.mul_le_mul_left m
    (show p.length * (18 * (p.length + 1) + 15) + 18 * (B + p.length + 1) + 21 ≤
      L * (18 * (L + 1) + 15) + 18 * (B + L + 1) + 21 by omega)
  unfold augmentBudget
  omega

theorem augmentWords_length (flow : Vector (List Bool) m) (B : Nat)
    (bound : ∀ e : Fin m, flow[e.val].length ≤ B) (p : List (ResidualArc m)) (e : Fin m) :
    (augmentWords flow p).1[e.val].length ≤ B + p.length + 2 := by
  have hd := sumDelta_length e p
  have hb := bound e
  have ha := addSigned_length ⟨false, flow[e.val]⟩ (sumDelta e p).1
  have hn := naturalWord_length (addSigned ⟨false, flow[e.val]⟩ (sumDelta e p).1).1
  simp only [augmentWords, Costed.tabulate_value, augmentCell]
  dsimp only at ha
  omega

end GyoriLovasz.Flow
