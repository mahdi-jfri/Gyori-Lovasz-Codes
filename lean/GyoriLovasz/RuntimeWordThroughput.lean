import GyoriLovasz.RuntimeWordEncoding
import GyoriLovasz.RuntimeMaxFlow

namespace GyoriLovasz.Flow
open Binary
open scoped BigOperators

def sumCapLoop (caps : Vector (List Bool) m) : List (Fin m) → Costed.Computation (List Bool)
  | [] => ([], 1)
  | e :: es =>
    let rest := sumCapLoop caps es
    let sum := addCarry caps[e.val] rest.1 false
    (sum.1, rest.2 + sum.2 + 3)

theorem sumCapLoop_value (caps : Vector (List Bool) m) (es : List (Fin m)) :
    value (sumCapLoop caps es).1 = (es.map (fun e => value caps[e.val])).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [sumCapLoop, addCarry_correct, ih]

theorem sumCapLoop_length (caps : Vector (List Bool) m) (B : Nat)
    (bound : ∀ e : Fin m, caps[e.val].length ≤ B) (es : List (Fin m)) :
    (sumCapLoop caps es).1.length ≤ B + es.length := by
  induction es with
  | nil => simp [sumCapLoop]
  | cons e es ih =>
    have hb := bound e
    have ha := addCarry_length caps[e.val] (sumCapLoop caps es).1 false
    simp only [sumCapLoop, List.length_cons]
    omega

theorem sumCapLoop_cost (caps : Vector (List Bool) m) (B : Nat)
    (bound : ∀ e : Fin m, caps[e.val].length ≤ B) (es : List (Fin m)) :
    (sumCapLoop caps es).2 ≤ es.length * (7 * (B + es.length) + 5) + 1 := by
  induction es with
  | nil => simp [sumCapLoop]
  | cons e es ih =>
    have hb := bound e
    have hl := sumCapLoop_length caps B bound es
    have ha := addCarry_steps caps[e.val] (sumCapLoop caps es).1 false
    have hm := Nat.mul_le_mul_left es.length
      (show 7 * (B + es.length) + 5 ≤ 7 * (B + (es.length + 1)) + 5 by omega)
    simp only [sumCapLoop, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

def returnCapacity (caps : Vector (List Bool) m) : Costed.Computation (List Bool) :=
  let es := Costed.enumerateIndices m
  let sum := sumCapLoop caps es.1
  let inc := addCarry sum.1 [] true
  (inc.1, es.2 + sum.2 + inc.2 + 2)

theorem returnCapacity_value (caps : Vector (List Bool) m) :
    value (returnCapacity caps).1 = (∑ e : Fin m, value caps[e.val]) + 1 := by
  simp [returnCapacity, addCarry_correct, sumCapLoop_value, Costed.enumerateIndices_value,
    List.finRange, List.map_ofFn, List.sum_ofFn, value]

theorem returnCapacity_bounds (caps : Vector (List Bool) m) (B : Nat)
    (bound : ∀ e : Fin m, caps[e.val].length ≤ B) :
    (returnCapacity caps).1.length ≤ B + m + 1 ∧
      (returnCapacity caps).2 ≤ 2 * m * m + 2 * m + m * (7 * (B + m) + 5) + 7 * (B + m) + 6 := by
  have hl := sumCapLoop_length caps B bound (List.finRange m)
  have hc := sumCapLoop_cost caps B bound (List.finRange m)
  have ha := addCarry_length (sumCapLoop caps (List.finRange m)).1 [] true
  have hs := addCarry_steps (sumCapLoop caps (List.finRange m)).1 [] true
  simp only [List.length_finRange, List.length_nil, Nat.max_zero] at hl hc ha hs
  simp only [returnCapacity, Costed.enumerateIndices_value, Costed.enumerateIndices_cost]
  exact ⟨by omega, by omega⟩

def throughputWords (s : WordResidual n m) (source sink : Fin n) (limit : List Bool) :
    Costed.Computation (WordResidual n (m + 1)) :=
  let tails := Costed.tabulate (m + 1) (fun e => (Fin.cases (motive := fun _ => Fin n) sink (fun e => s.tail[e.val]) e, 2))
  let heads := Costed.tabulate (m + 1) (fun e => (Fin.cases (motive := fun _ => Fin n) source (fun e => s.head[e.val]) e, 2))
  let caps := Costed.tabulate (m + 1) (fun e => (Fin.cases (motive := fun _ => List Bool) limit (fun e => s.capacity[e.val]) e, 2))
  let costs := Costed.tabulate (m + 1) (fun e =>
    (Fin.cases (motive := fun _ => SignedWord) (⟨true, []⟩ : SignedWord) (fun _ => (⟨false, []⟩ : SignedWord)) e, 2))
  (⟨tails.1, heads.1, s.vertexCode, caps.1, caps.1, costs.1, s.potential⟩,
    tails.2 + heads.2 + caps.2 + costs.2 + 1)

theorem throughputWords_network (s : WordResidual n m) (source sink : Fin n) (limit : List Bool) :
    decodeNetwork (throughputWords s source sink limit).1 =
      throughputNetwork (decodeNetwork s) source sink (value limit) := by
  simp only [decodeNetwork, throughputWords, Costed.tabulate_value, throughputNetwork]
  congr 1 <;> funext e <;> refine Fin.cases ?_ ?_ e <;> intros <;> simp [signedValue, value]

theorem throughputWords_codes (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source sink : Fin n) (limit : List Bool) :
    VertexCodesCorrect (throughputWords s source sink limit).1 := correct

theorem throughputWords_bounds (s : WordResidual n m) (B : Nat) (bound : WordResidualBound s B)
    (source sink : Fin n) (limit : List Bool) (lb : limit.length ≤ B) :
    WordResidualBound (throughputWords s source sink limit).1 B := by
  constructor
  · intro e
    simp only [throughputWords, Costed.tabulate_value]
    refine Fin.cases ?_ ?_ e
    · exact ⟨lb, lb, by simp⟩
    · intro i; exact ⟨(bound.1 i).1, (bound.1 i).1, by simp⟩
  · exact bound.2

theorem throughputWords_cost (s : WordResidual n m) (source sink : Fin n) (limit : List Bool) :
    (throughputWords s source sink limit).2 ≤ 8 * (m + 1) * (m + 1) + 32 * (m + 1) + 13 := by
  have h₁ := Costed.tabulate_cost (m + 1) (fun e => (Fin.cases (motive := fun _ => Fin n) sink (fun e => s.tail[e.val]) e, 2)) 2
    (by intros; exact Nat.le_refl _)
  have h₂ := Costed.tabulate_cost (m + 1) (fun e => (Fin.cases (motive := fun _ => Fin n) source (fun e => s.head[e.val]) e, 2)) 2
    (by intros; exact Nat.le_refl _)
  have h₃ := Costed.tabulate_cost (m + 1) (fun e => (Fin.cases (motive := fun _ => List Bool) limit (fun e => s.capacity[e.val]) e, 2)) 2
    (by intros; exact Nat.le_refl _)
  have h₄ := Costed.tabulate_cost (m + 1) (fun e =>
    (Fin.cases (motive := fun _ => SignedWord) (⟨true, []⟩ : SignedWord) (fun _ => (⟨false, []⟩ : SignedWord)) e, 2)) 2
    (by intros; exact Nat.le_refl _)
  dsimp only [throughputWords]
  ring_nf at h₁ h₂ h₃ h₄ ⊢
  omega

end GyoriLovasz.Flow

