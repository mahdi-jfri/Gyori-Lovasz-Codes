import GyoriLovasz.RuntimeWordSolver

namespace GyoriLovasz.Flow
open Binary

def thresholdCell (p : Vector SignedWord n) (source v : Fin n) : Bool × Nat :=
  let cmp := compareSigned p[source.val] p[v.val]
  (!cmp.1, cmp.2 + 3)

theorem thresholdCell_value (p : Vector SignedWord n) (source v : Fin n) :
    (thresholdCell p source v).1 = decide (signedValue p[v.val] ≤ signedValue p[source.val]) := by
  apply Bool.eq_iff_iff.mpr
  have h := compareSigned_correct p[source.val] p[v.val]
  simp only [thresholdCell, Bool.not_eq_true', decide_eq_true_eq]
  cases hc : (compareSigned p[source.val] p[v.val]).1 <;> simp_all

theorem thresholdCell_cost (p : Vector SignedWord n) (B : Nat)
    (bound : ∀ v : Fin n, p[v.val].digits.length ≤ B) (source v : Fin n) :
    (thresholdCell p source v).2 ≤ 9 * B + 10 := by
  have h := compareSigned_steps p[source.val] p[v.val]
  have hs := bound source
  have hv := bound v
  dsimp only [thresholdCell]
  omega

def thresholdWords (p : Vector SignedWord n) (source : Fin n) : Costed.Computation (Vector Bool n) :=
  Costed.tabulate n (thresholdCell p source)

theorem thresholdWords_value (p : Vector SignedWord n) (source v : Fin n) :
    (thresholdWords p source).1[v.val] = decide (signedValue p[v.val] ≤ signedValue p[source.val]) := by
  rw [thresholdWords, Costed.tabulate_value, thresholdCell_value]

theorem thresholdWords_cost (p : Vector SignedWord n) (B : Nat)
    (bound : ∀ v : Fin n, p[v.val].digits.length ≤ B) (source : Fin n) :
    (thresholdWords p source).2 ≤ 2 * n * n + n * (9 * B + 16) + 3 :=
  Costed.tabulate_cost n _ (9 * B + 10) (thresholdCell_cost p B bound source)

end GyoriLovasz.Flow
