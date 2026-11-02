import GyoriLovasz.RuntimeCostedScan
import GyoriLovasz.RuntimeResidual

namespace GyoriLovasz.Flow

def allResidualArcs (m : Nat) : List (ResidualArc m) :=
  (List.finRange m).flatMap (fun e => [(e, false), (e, true)])

theorem allResidualArcs_length (m : Nat) : (allResidualArcs m).length = 2 * m := by
  have length (xs : List (Fin m)) :
      (xs.flatMap (fun e => [(e, false), (e, true)])).length = 2 * xs.length := by
    induction xs with
    | nil => simp
    | cons e xs ih => simp [ih, Nat.mul_add, Nat.add_comm]; omega
  simpa [allResidualArcs] using length (List.finRange m)

/-- Refines bestArc using explicitly costed eligibility, score, and comparison
callbacks. Their correctness and costs remain visible premises. -/
def bestArcCosted (eligible : ResidualArc m → Costed.Computation Bool)
    (score : ResidualArc m → Costed.Computation Int)
    (less : Int → Int → Costed.Computation Bool) : Costed.Computation (Option (ResidualArc m)) :=
  Costed.filterArgmin eligible score less (allResidualArcs m)

theorem bestArcCosted_value (G : Network n m) (f : Fin m → Nat) (potential : Fin n → Int)
    (u v : Fin n) (eligible : ResidualArc m → Costed.Computation Bool)
    (score : ResidualArc m → Costed.Computation Int)
    (less : Int → Int → Costed.Computation Bool)
    (eligibleCorrect : ∀ a, (eligible a).1 =
      (available G f a && decide (arcTail G a = u ∧ arcHead G a = v)))
    (scoreCorrect : ∀ a, (score a).1 = arcCost G potential a)
    (lessCorrect : ∀ x y, (less x y).1 = decide (x < y)) :
    (bestArcCosted eligible score less).1 = bestArc G f potential u v := by
  simp only [bestArcCosted, Costed.filterArgmin_value eligible score less lessCorrect,
    eligibleCorrect, scoreCorrect, bestArc, residualCandidates, allResidualArcs]

theorem bestArcCosted_cost (eligible : ResidualArc m → Costed.Computation Bool)
    (score : ResidualArc m → Costed.Computation Int)
    (less : Int → Int → Costed.Computation Bool) (P S C : Nat)
    (predicateBound : ∀ a, (eligible a).2 ≤ P)
    (scoreBound : ∀ a, (score a).2 ≤ S)
    (compareBound : ∀ a b, (less (score a).1 (score b).1).2 ≤ C) :
    (bestArcCosted eligible score less).2 ≤ 2 * m * (P + 2 * S + C + 7) + 2 := by
  have cost := Costed.filterArgmin_cost eligible score less (allResidualArcs m)
    P S C predicateBound scoreBound compareBound
  simpa only [bestArcCosted, allResidualArcs_length] using cost

end GyoriLovasz.Flow
