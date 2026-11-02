import GyoriLovasz.RuntimeUniformBudget
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace GyoriLovasz.RuntimePolynomial
open WordInstance

/-- Exact representation by a natural-coefficient polynomial. -/
def IsPolynomial (f : Nat → Nat) : Prop :=
  ∃ p : Polynomial Nat, ∀ x, f x = p.eval x

theorem polynomial_constant (c : Nat) : IsPolynomial (fun _ => c) :=
  ⟨Polynomial.C c, by simp⟩

theorem polynomial_identity : IsPolynomial (fun x => x) :=
  ⟨Polynomial.X, by simp⟩

theorem polynomial_add {f g : Nat → Nat} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (fun x => f x + g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, by intro x; simp [hp, hq]⟩

theorem polynomial_mul {f g : Nat → Nat} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (fun x => f x * g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, by intro x; simp [hp, hq]⟩

def normalizeCeiling (N : Nat) := rootMaskBudget N N + 2 * N * N + 9 * N + 4
def weightedBudget (N B : Nat) := normalizeCeiling N + (N + 1) * universalBudget N B + 1
def encodingBudget (N : Nat) := (2 * N * N + 7 * N + 3) +
  (2 * N * N + N * (N * (7 * N + 3) + 7) + 3) + 1
def unweightedBudget (N : Nat) := encodingBudget N + weightedBudget N N + 1

noncomputable def poly_ComputedReindex_eraseIndexBudget (m : Polynomial Nat) : Polynomial Nat :=
  (2 * m * m + 9 * m + 3) +
  (2 * (m + 1) * (m + 1) + (m + 1) * (2 * m * m + 7 * m + 10) + 3) + 1

theorem eval_poly_ComputedReindex_eraseIndexBudget (x : Nat) (m : Polynomial Nat) :
    (poly_ComputedReindex_eraseIndexBudget m).eval x = ComputedReindex.eraseIndexBudget (m.eval x) := by
  simp only [poly_ComputedReindex_eraseIndexBudget, ComputedReindex.eraseIndexBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_WordInstance_contractStepBudget (m k B : Polynomial Nat) : Polynomial Nat :=
  poly_ComputedReindex_eraseIndexBudget m +
  (2 * m * m * m + m * m * 14 + 9 * m + 3) + (2 * k * k + 9 * k + 3) +
  (2 * m * m + 8 * m + 3) + (2 * k * k + k * (9 * B + 10) + 3) + 4

theorem eval_poly_WordInstance_contractStepBudget (x : Nat) (m k B : Polynomial Nat) :
    (poly_WordInstance_contractStepBudget m k B).eval x = WordInstance.contractStepBudget (m.eval x) (k.eval x) (B.eval x) := by
  simp only [poly_WordInstance_contractStepBudget, WordInstance.contractStepBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_ComputedReindex_eraseIndexBudget]

noncomputable def poly_TransportNetwork_pickBudget (r B : Polynomial Nat) : Polynomial Nat :=
  2 * r * r + 2 * r + r * (9 * B + 7) + 3

theorem eval_poly_TransportNetwork_pickBudget (x : Nat) (r B : Polynomial Nat) :
    (poly_TransportNetwork_pickBudget r B).eval x = TransportNetwork.pickBudget (r.eval x) (B.eval x) := by
  simp only [poly_TransportNetwork_pickBudget, TransportNetwork.pickBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_TransportNetwork_buildBudget (l r : Polynomial Nat) : Polynomial Nat :=
  (2 * l * l + 2 * r * r + 7 * l * r + 5 * l + 2 * r + 5) +
  (7 * (l + r + 2) * (l + r + 2) + 6 * (l + r + 2) + 2) +
  2 * (2 * (l + (l * r + r)) * (l + (l * r + r)) + (l + (l * r + r)) * 16 + 3) +
  (2 * (l + (l * r + r)) * (l + (l * r + r)) + (l + (l * r + r)) * 12 + 3) +
  (2 * (l + (l * r + r)) * (l + (l * r + r)) + (l + (l * r + r)) * 7 + 3) +
  (2 * (l + r + 2) * (l + r + 2) + (l + r + 2) * 7 + 3) + 1

theorem eval_poly_TransportNetwork_buildBudget (x : Nat) (l r : Polynomial Nat) :
    (poly_TransportNetwork_buildBudget l r).eval x = TransportNetwork.buildBudget (l.eval x) (r.eval x) := by
  simp only [poly_TransportNetwork_buildBudget, TransportNetwork.buildBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_Flow_returnBudget (m B : Polynomial Nat) : Polynomial Nat :=
  2 * m * m + 2 * m + m * (7 * (B + m) + 5) + 7 * (B + m) + 6

theorem eval_poly_Flow_returnBudget (x : Nat) (m B : Polynomial Nat) :
    (poly_Flow_returnBudget m B).eval x = Flow.returnBudget (m.eval x) (B.eval x) := by
  simp only [poly_Flow_returnBudget, Flow.returnBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_Flow_throughputBudget (m : Polynomial Nat) : Polynomial Nat :=
  8 * (m + 1) * (m + 1) + 32 * (m + 1) + 13

theorem eval_poly_Flow_throughputBudget (x : Nat) (m : Polynomial Nat) :
    (poly_Flow_throughputBudget m).eval x = Flow.throughputBudget (m.eval x) := by
  simp only [poly_Flow_throughputBudget, Flow.throughputBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_Flow_residualBuildBudget (n m B : Polynomial Nat) : Polynomial Nat :=
  2 * n * n * n + n * n * (2 * m * m + 7 * m + 2 * m * (180 * B + 398) + 72 * B + 172) + 9 * n + 3

theorem eval_poly_Flow_residualBuildBudget (x : Nat) (n m B : Polynomial Nat) :
    (poly_Flow_residualBuildBudget n m B).eval x = Flow.residualBuildBudget (n.eval x) (m.eval x) (B.eval x) := by
  simp only [poly_Flow_residualBuildBudget, Flow.residualBuildBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_Flow_graphBudget (n : Polynomial Nat) : Polynomial Nat :=
  4 * n * n * n + 25 * n * n + 18 * n + 7

theorem eval_poly_Flow_graphBudget (x : Nat) (n : Polynomial Nat) :
    (poly_Flow_graphBudget n).eval x = Flow.graphBudget (n.eval x) := by
  simp only [poly_Flow_graphBudget, Flow.graphBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_WordShortest_stepBudget (n L B : Polynomial Nat) : Polynomial Nat :=
  4 * n * n + 2 * n + n * (2 * L * (9 * B + 7) + 25 * B + 48) + 10

theorem eval_poly_WordShortest_stepBudget (x : Nat) (n L B : Polynomial Nat) :
    (poly_WordShortest_stepBudget n L B).eval x = WordShortest.stepBudget (n.eval x) (L.eval x) (B.eval x) := by
  simp only [poly_WordShortest_stepBudget, WordShortest.stepBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_Flow_distanceBudget (n B : Polynomial Nat) : Polynomial Nat :=
  2 * n * n + n * (9 * B + 12) + n * (poly_WordShortest_stepBudget n n (B + n) + 1) + 6

theorem eval_poly_Flow_distanceBudget (x : Nat) (n B : Polynomial Nat) :
    (poly_Flow_distanceBudget n B).eval x = Flow.distanceBudget (n.eval x) (B.eval x) := by
  simp only [poly_Flow_distanceBudget, Flow.distanceBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_WordShortest_stepBudget]

noncomputable def poly_WordPath_budget (n B : Polynomial Nat) : Polynomial Nat :=
  29 * n * n + n * (9 * B + 17) + 12

theorem eval_poly_WordPath_budget (x : Nat) (n B : Polynomial Nat) :
    (poly_WordPath_budget n B).eval x = WordPath.budget (n.eval x) (B.eval x) := by
  simp only [poly_WordPath_budget, WordPath.budget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_Flow_routeBudget (n B : Polynomial Nat) : Polynomial Nat :=
  (2 * n * n + n * (9 * B + 12) + n * (poly_WordShortest_stepBudget n n (B + n) + 1) + 6) +
  (2 * n * n * n + n * n * (16 * (B + n) + 29) + 9 * n + 4) +
  (2 * n * n + n * (9 * B + 12) + n * (poly_WordPath_budget n B + 1) + 5) + 2

theorem eval_poly_Flow_routeBudget (x : Nat) (n B : Polynomial Nat) :
    (poly_Flow_routeBudget n B).eval x = Flow.routeBudget (n.eval x) (B.eval x) := by
  simp only [poly_Flow_routeBudget, Flow.routeBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_WordShortest_stepBudget, eval_poly_WordPath_budget]

noncomputable def poly_Flow_augmentBudget (m B L : Polynomial Nat) : Polynomial Nat :=
  2 * m * m + m * (L * (18 * (L + 1) + 15) + 18 * (B + L + 1) + 21) + 3

theorem eval_poly_Flow_augmentBudget (x : Nat) (m B L : Polynomial Nat) :
    (poly_Flow_augmentBudget m B L).eval x = Flow.augmentBudget (m.eval x) (B.eval x) (L.eval x) := by
  simp only [poly_Flow_augmentBudget, Flow.augmentBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_Flow_repairBudget (n m B : Polynomial Nat) : Polynomial Nat :=
  (54 * B + 91) + (18 * (B + 3) + 8) +
  (poly_Flow_residualBuildBudget n m B + poly_Flow_graphBudget n + poly_Flow_distanceBudget n (B + 4) + 2) +
  (2 * n * n + n * (18 * (B + 4 + n) + 18) + 3) +
  (9 * (B + 4 + n) + 2) +
  (poly_Flow_residualBuildBudget n m B + poly_Flow_graphBudget n + poly_Flow_routeBudget n (B + 4) + 8 * n + 4) +
  poly_Flow_augmentBudget m B n + 16

theorem eval_poly_Flow_repairBudget (x : Nat) (n m B : Polynomial Nat) :
    (poly_Flow_repairBudget n m B).eval x = Flow.repairBudget (n.eval x) (m.eval x) (B.eval x) := by
  simp only [poly_Flow_repairBudget, Flow.repairBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_Flow_residualBuildBudget, eval_poly_Flow_graphBudget, eval_poly_Flow_distanceBudget, eval_poly_Flow_routeBudget, eval_poly_Flow_augmentBudget]

noncomputable def poly_Flow_opBudget (n m B : Polynomial Nat) : Polynomial Nat :=
  poly_Flow_repairBudget n m B + 6 * m * m + m * (7 * B + 31) + 11

theorem eval_poly_Flow_opBudget (x : Nat) (n m B : Polynomial Nat) :
    (poly_Flow_opBudget n m B).eval x = Flow.opBudget (n.eval x) (m.eval x) (B.eval x) := by
  simp only [poly_Flow_opBudget, Flow.opBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_Flow_repairBudget]

noncomputable def poly_Flow_storedBudget (n m B : Polynomial Nat) : Polynomial Nat :=
  B * (4 * m * m + 16 * m + 2 * B + 12) + B * (2 * m * m + 13 * m + 10) +
  (2 * m * m + 8 * m + 2 * n * n + 8 * n + 7) +
  ((m + 1) * B) * (poly_Flow_opBudget n m (B + ((m + 1) * B) * (n + 6)) + 1) + 6

theorem eval_poly_Flow_storedBudget (x : Nat) (n m B : Polynomial Nat) :
    (poly_Flow_storedBudget n m B).eval x = Flow.storedBudget (n.eval x) (m.eval x) (B.eval x) := by
  simp only [poly_Flow_storedBudget, Flow.storedBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_Flow_opBudget]

noncomputable def poly_Flow_maxFlowBudget (n m B : Polynomial Nat) : Polynomial Nat :=
  poly_Flow_returnBudget m B + poly_Flow_throughputBudget m + poly_Flow_storedBudget n (m + 1) (B + m + 1) + 2

theorem eval_poly_Flow_maxFlowBudget (x : Nat) (n m B : Polynomial Nat) :
    (poly_Flow_maxFlowBudget n m B).eval x = Flow.maxFlowBudget (n.eval x) (m.eval x) (B.eval x) := by
  simp only [poly_Flow_maxFlowBudget, Flow.maxFlowBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_Flow_returnBudget, eval_poly_Flow_throughputBudget, eval_poly_Flow_storedBudget]

noncomputable def poly_TransportNetwork_matrixWordsBudget (l r B : Polynomial Nat) : Polynomial Nat :=
  poly_TransportNetwork_buildBudget l r +
  poly_Flow_maxFlowBudget (l + r + 2) (l + (l * r + r)) (B + l + r + 2) +
    (2 * l * l + l * (2 * r * r + 11 * r + 9) + 3) + 2

theorem eval_poly_TransportNetwork_matrixWordsBudget (x : Nat) (l r B : Polynomial Nat) :
    (poly_TransportNetwork_matrixWordsBudget l r B).eval x = TransportNetwork.matrixWordsBudget (l.eval x) (r.eval x) (B.eval x) := by
  simp only [poly_TransportNetwork_matrixWordsBudget, TransportNetwork.matrixWordsBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_TransportNetwork_buildBudget, eval_poly_Flow_maxFlowBudget]

noncomputable def poly_Flow_maxFlowWordLength (n m B : Polynomial Nat) : Polynomial Nat :=
  (B + m + 1) + ((m + 2) * (B + m + 1)) * (n + 6)

theorem eval_poly_Flow_maxFlowWordLength (x : Nat) (n m B : Polynomial Nat) :
    (poly_Flow_maxFlowWordLength n m B).eval x = Flow.maxFlowWordLength (n.eval x) (m.eval x) (B.eval x) := by
  simp only [poly_Flow_maxFlowWordLength, Flow.maxFlowWordLength, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_TransportNetwork_matchingWitnessBudget (l r : Polynomial Nat) : Polynomial Nat :=
  (2 * l * l + 9 * l + 3) + (2 * r * r + 7 * r + 3) + poly_TransportNetwork_matrixWordsBudget l r 1 +
    (2 * l * l + l * (poly_TransportNetwork_pickBudget r (poly_Flow_maxFlowWordLength (l + r + 2) (l + (l * r + r)) (1 + l + r + 2)) + 6) + 3) + 3

theorem eval_poly_TransportNetwork_matchingWitnessBudget (x : Nat) (l r : Polynomial Nat) :
    (poly_TransportNetwork_matchingWitnessBudget l r).eval x = TransportNetwork.matchingWitnessBudget (l.eval x) (r.eval x) := by
  simp only [poly_TransportNetwork_matchingWitnessBudget, TransportNetwork.matchingWitnessBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_TransportNetwork_matrixWordsBudget, eval_poly_TransportNetwork_pickBudget, eval_poly_Flow_maxFlowWordLength]

noncomputable def poly_rootMaskBudget (n k : Polynomial Nat) : Polynomial Nat :=
  (7 * n * n + 6 * n + 2) + (2 * k * k + 2 * k + 1) + (4 * k + 1) +
    (2 * n * n + n * (k * (9 * n + 7) + 8) + 3) + 2

theorem eval_poly_rootMaskBudget (x : Nat) (n k : Polynomial Nat) :
    (poly_rootMaskBudget n k).eval x = rootMaskBudget (n.eval x) (k.eval x) := by
  simp only [poly_rootMaskBudget, rootMaskBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_RuntimePolynomial_normalizeCeiling (N : Polynomial Nat) : Polynomial Nat :=
  poly_rootMaskBudget N N + 2 * N * N + 9 * N + 4

theorem eval_poly_RuntimePolynomial_normalizeCeiling (x : Nat) (N : Polynomial Nat) :
    (poly_RuntimePolynomial_normalizeCeiling N).eval x = RuntimePolynomial.normalizeCeiling (N.eval x) := by
  simp only [poly_RuntimePolynomial_normalizeCeiling, RuntimePolynomial.normalizeCeiling, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_rootMaskBudget]

noncomputable def poly_WordInstance_nonrootCeiling (N : Polynomial Nat) : Polynomial Nat :=
  poly_rootMaskBudget N N + 2 * N * N + 7 * N + 3

theorem eval_poly_WordInstance_nonrootCeiling (x : Nat) (N : Polynomial Nat) :
    (poly_WordInstance_nonrootCeiling N).eval x = WordInstance.nonrootCeiling (N.eval x) := by
  simp only [poly_WordInstance_nonrootCeiling, WordInstance.nonrootCeiling, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_rootMaskBudget]

noncomputable def poly_WordInstance_zeroCeiling (N B : Polynomial Nat) : Polynomial Nat :=
  2 * N * N + 2 * N + N * (9 * B + 7) + 3

theorem eval_poly_WordInstance_zeroCeiling (x : Nat) (N B : Polynomial Nat) :
    (poly_WordInstance_zeroCeiling N B).eval x = WordInstance.zeroCeiling (N.eval x) (B.eval x) := by
  simp only [poly_WordInstance_zeroCeiling, WordInstance.zeroCeiling, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_WordInstance_baseCeiling (N : Polynomial Nat) : Polynomial Nat :=
  2 * N * N + N * (2 * N * N + 7 * N + 10) + 3

theorem eval_poly_WordInstance_baseCeiling (x : Nat) (N : Polynomial Nat) :
    (poly_WordInstance_baseCeiling N).eval x = WordInstance.baseCeiling (N.eval x) := by
  simp only [poly_WordInstance_baseCeiling, WordInstance.baseCeiling, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_SafeEdges_eraseBudget (n : Polynomial Nat) : Polynomial Nat :=
  2 * n * n * n + n * n * 13 + 9 * n + 3

theorem eval_poly_SafeEdges_eraseBudget (x : Nat) (n : Polynomial Nat) :
    (poly_SafeEdges_eraseBudget n).eval x = SafeEdges.eraseBudget (n.eval x) := by
  simp only [poly_SafeEdges_eraseBudget, SafeEdges.eraseBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_VertexNetwork_buildBudget (n : Polynomial Nat) : Polynomial Nat :=
  (9 * n * n + 5 * n + 4) + (7 * (n + n + 1) * (n + n + 1) + 6 * (n + n + 1) + 2) +
  ((n + 1) * (7 * (n + 1) + 3) + 1) +
  2 * (2 * (n + (n * n + n)) * (n + (n * n + n)) + (n + (n * n + n)) * 16 + 3) +
  (2 * (n + (n * n + n)) * (n + (n * n + n)) + (n + (n * n + n)) * 12 + 3) +
  (2 * (n + (n * n + n)) * (n + (n * n + n)) + (n + (n * n + n)) * 7 + 3) +
  (2 * (n + n + 1) * (n + n + 1) + (n + n + 1) * 7 + 3) + 1

theorem eval_poly_VertexNetwork_buildBudget (x : Nat) (n : Polynomial Nat) :
    (poly_VertexNetwork_buildBudget n).eval x = VertexNetwork.buildBudget (n.eval x) := by
  simp only [poly_VertexNetwork_buildBudget, VertexNetwork.buildBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_VertexNetwork_essentialBudget (n : Polynomial Nat) : Polynomial Nat :=
  poly_VertexNetwork_buildBudget n + (2 * (n + (n * n + n)) * (n + (n * n + n)) + 10 * (n + (n * n + n)) + 4) +
  2 * (poly_Flow_maxFlowBudget (n + n + 1) (n + (n * n + n)) (n + n + 1) + 2) +
  16 * poly_Flow_maxFlowWordLength (n + n + 1) (n + (n * n + n)) (n + n + 1) + 16

theorem eval_poly_VertexNetwork_essentialBudget (x : Nat) (n : Polynomial Nat) :
    (poly_VertexNetwork_essentialBudget n).eval x = VertexNetwork.essentialBudget (n.eval x) := by
  simp only [poly_VertexNetwork_essentialBudget, VertexNetwork.essentialBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_VertexNetwork_buildBudget, eval_poly_Flow_maxFlowBudget, eval_poly_Flow_maxFlowWordLength]

noncomputable def poly_splitInputBudget (n k : Polynomial Nat) : Polynomial Nat :=
  poly_rootMaskBudget n k +
  (2 * n * n * n + n * n * (poly_VertexNetwork_essentialBudget n + 13) + 9 * n + 3) +
  (2 * n * n + n * (2 * k * k + 9 * k + 9) + 3) + (2 * n * n + 9 * n + 3) + 3

theorem eval_poly_splitInputBudget (x : Nat) (n k : Polynomial Nat) :
    (poly_splitInputBudget n k).eval x = splitInputBudget (n.eval x) (k.eval x) := by
  simp only [poly_splitInputBudget, splitInputBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_rootMaskBudget, eval_poly_VertexNetwork_essentialBudget]

noncomputable def poly_TransportNetwork_matrixBudget (l r B : Polynomial Nat) : Polynomial Nat :=
  poly_TransportNetwork_buildBudget l r + poly_Flow_maxFlowBudget (l + r + 2) (l + (l * r + r)) (B + l + r + 2) + poly_Flow_returnBudget l B +
  16 * (poly_Flow_maxFlowWordLength (l + r + 2) (l + (l * r + r)) (B + l + r + 2) + B + l + 1) + 7

theorem eval_poly_TransportNetwork_matrixBudget (x : Nat) (l r B : Polynomial Nat) :
    (poly_TransportNetwork_matrixBudget l r B).eval x = TransportNetwork.matrixBudget (l.eval x) (r.eval x) (B.eval x) := by
  simp only [poly_TransportNetwork_matrixBudget, TransportNetwork.matrixBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_TransportNetwork_buildBudget, eval_poly_Flow_maxFlowBudget, eval_poly_Flow_returnBudget, eval_poly_Flow_maxFlowWordLength]

noncomputable def poly_SafeEdges_testBudget (n k B : Polynomial Nat) : Polynomial Nat :=
  poly_SafeEdges_eraseBudget n + poly_splitInputBudget n k + poly_TransportNetwork_matrixBudget n k B + 4

theorem eval_poly_SafeEdges_testBudget (x : Nat) (n k B : Polynomial Nat) :
    (poly_SafeEdges_testBudget n k B).eval x = SafeEdges.testBudget (n.eval x) (k.eval x) (B.eval x) := by
  simp only [poly_SafeEdges_testBudget, SafeEdges.testBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_SafeEdges_eraseBudget, eval_poly_splitInputBudget, eval_poly_TransportNetwork_matrixBudget]

noncomputable def poly_SafeEdges_chooseBudget (n k B : Polynomial Nat) : Polynomial Nat :=
  8 * n * n + 5 * n + 3 + n * n * (poly_SafeEdges_testBudget n k B + 3) + 2

theorem eval_poly_SafeEdges_chooseBudget (x : Nat) (n k B : Polynomial Nat) :
    (poly_SafeEdges_chooseBudget n k B).eval x = SafeEdges.chooseBudget (n.eval x) (k.eval x) (B.eval x) := by
  simp only [poly_SafeEdges_chooseBudget, SafeEdges.chooseBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_SafeEdges_testBudget]

noncomputable def poly_WordInstance_reduceInputBudget (n k B : Polynomial Nat) : Polynomial Nat :=
  n * n * (poly_SafeEdges_chooseBudget n k B + poly_SafeEdges_eraseBudget n + 3) + 2

theorem eval_poly_WordInstance_reduceInputBudget (x : Nat) (n k B : Polynomial Nat) :
    (poly_WordInstance_reduceInputBudget n k B).eval x = WordInstance.reduceInputBudget (n.eval x) (k.eval x) (B.eval x) := by
  simp only [poly_WordInstance_reduceInputBudget, WordInstance.reduceInputBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_SafeEdges_chooseBudget, eval_poly_SafeEdges_eraseBudget]

noncomputable def poly_soleBudget (n k : Polynomial Nat) : Polynomial Nat :=
  poly_rootMaskBudget n k + (2 * k * k + 2 * k + 1) +
  (2 * n * n + 2 * n + 1) + (k * (6 * n + 3) + 1) + k * n * (2 * n * n + 9 * n + 10) + 2

theorem eval_poly_soleBudget (x : Nat) (n k : Polynomial Nat) :
    (poly_soleBudget n k).eval x = soleBudget (n.eval x) (k.eval x) := by
  simp only [poly_soleBudget, soleBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_rootMaskBudget]

noncomputable def poly_WordInstance_terminalStepBudget (m l : Polynomial Nat) : Polynomial Nat :=
  poly_ComputedReindex_eraseIndexBudget m +
  (2 * m * m * m + m * m * 11 + 9 * m + 3) + (2 * l * l + 10 * l + 3) +
  (2 * m * m + 8 * m + 3) + (2 * l * l + 8 * l + 3) + 4

theorem eval_poly_WordInstance_terminalStepBudget (x : Nat) (m l : Polynomial Nat) :
    (poly_WordInstance_terminalStepBudget m l).eval x = WordInstance.terminalStepBudget (m.eval x) (l.eval x) := by
  simp only [poly_WordInstance_terminalStepBudget, WordInstance.terminalStepBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_ComputedReindex_eraseIndexBudget]

noncomputable def poly_WordInstance_singleRestoreCeiling (N : Polynomial Nat) : Polynomial Nat :=
  2 * N * N + 12 * N + 3

theorem eval_poly_WordInstance_singleRestoreCeiling (x : Nat) (N : Polynomial Nat) :
    (poly_WordInstance_singleRestoreCeiling N).eval x = WordInstance.singleRestoreCeiling (N.eval x) := by
  simp only [poly_WordInstance_singleRestoreCeiling, WordInstance.singleRestoreCeiling, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_rootNeighborBudget (n k : Polynomial Nat) : Polynomial Nat :=
  poly_rootMaskBudget n k +
  (2 * k * k + k * (2 * n * n + 11 * n + 9) + 3) + 1

theorem eval_poly_rootNeighborBudget (x : Nat) (n k : Polynomial Nat) :
    (poly_rootNeighborBudget n k).eval x = rootNeighborBudget (n.eval x) (k.eval x) := by
  simp only [poly_rootNeighborBudget, rootNeighborBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_rootMaskBudget]

noncomputable def poly_SaturationPrune_iterationBudget (l r : Polynomial Nat) : Polynomial Nat :=
  (2 * l * l + 9 * l + 3) + (2 * l * l + 9 * l + 2 * r * r + 7 * r + poly_TransportNetwork_matrixBudget l r 1 + 8) + 3

theorem eval_poly_SaturationPrune_iterationBudget (x : Nat) (l r : Polynomial Nat) :
    (poly_SaturationPrune_iterationBudget l r).eval x = SaturationPrune.iterationBudget (l.eval x) (r.eval x) := by
  simp only [poly_SaturationPrune_iterationBudget, SaturationPrune.iterationBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_TransportNetwork_matrixBudget]

noncomputable def poly_prunedSetBudget (k n : Polynomial Nat) : Polynomial Nat :=
  (2 * k * k + 7 * k + 3) +
  (2 * k * k + 2 * k + k * poly_SaturationPrune_iterationBudget k n + 3) + 1

theorem eval_poly_prunedSetBudget (x : Nat) (k n : Polynomial Nat) :
    (poly_prunedSetBudget k n).eval x = prunedSetBudget (k.eval x) (n.eval x) := by
  simp only [poly_prunedSetBudget, prunedSetBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_SaturationPrune_iterationBudget]

noncomputable def poly_roundAssignmentBudget (n k : Polynomial Nat) : Polynomial Nat :=
  (2 * k * k + 9 * k + 3) + poly_TransportNetwork_matchingWitnessBudget k n +
  (2 * n * n + n * (2 * k * k + 8 * k + 9) + 3) + (2 * n * n + 8 * n + 3) + 3

theorem eval_poly_roundAssignmentBudget (x : Nat) (n k : Polynomial Nat) :
    (poly_roundAssignmentBudget n k).eval x = roundAssignmentBudget (n.eval x) (k.eval x) := by
  simp only [poly_roundAssignmentBudget, roundAssignmentBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_TransportNetwork_matchingWitnessBudget]

noncomputable def poly_roundDataBudget (n k : Polynomial Nat) : Polynomial Nat :=
  poly_rootNeighborBudget n k + poly_prunedSetBudget k n +
  (2 * k * k + 6 * k + 4) + poly_roundAssignmentBudget n k + 3

theorem eval_poly_roundDataBudget (x : Nat) (n k : Polynomial Nat) :
    (poly_roundDataBudget n k).eval x = roundDataBudget (n.eval x) (k.eval x) := by
  simp only [poly_roundDataBudget, roundDataBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_rootNeighborBudget, eval_poly_prunedSetBudget, eval_poly_roundAssignmentBudget]

noncomputable def poly_WordInstance_roundShapeBudget (n k : Polynomial Nat) : Polynomial Nat :=
  poly_rootNeighborBudget n k +
  (2 * n * n + n * (2 * k * k + 11 * k + 9) + 3) + (2 * n * n + 8 * n + 3) +
  (2 * k * k + 8 * k + 3) + (2 * n * n + 7 * n + 4) + (2 * k * k + 7 * k + 4) + 5

theorem eval_poly_WordInstance_roundShapeBudget (x : Nat) (n k : Polynomial Nat) :
    (poly_WordInstance_roundShapeBudget n k).eval x = WordInstance.roundShapeBudget (n.eval x) (k.eval x) := by
  simp only [poly_WordInstance_roundShapeBudget, WordInstance.roundShapeBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_rootNeighborBudget]

noncomputable def poly_WordInstance_roundedCeiling (N : Polynomial Nat) : Polynomial Nat :=
  2 * N * N + N * (2 * N * N + 7 * N + 11) + 3

theorem eval_poly_WordInstance_roundedCeiling (x : Nat) (N : Polynomial Nat) :
    (poly_WordInstance_roundedCeiling N).eval x = WordInstance.roundedCeiling (N.eval x) := by
  simp only [poly_WordInstance_roundedCeiling, WordInstance.roundedCeiling, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_WordInstance_projectBudget (m j : Polynomial Nat) : Polynomial Nat :=
  (2 * m * m * m + m * m * 11 + 9 * m + 3) + (2 * j * j + 9 * j + 3) +
    (2 * m * m + 8 * m + 3) + (2 * j * j + 8 * j + 3) + 3

theorem eval_poly_WordInstance_projectBudget (x : Nat) (m j : Polynomial Nat) :
    (poly_WordInstance_projectBudget m j).eval x = WordInstance.projectBudget (m.eval x) (j.eval x) := by
  simp only [poly_WordInstance_projectBudget, WordInstance.projectBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_WordInstance_remainingStepBudget (n m l : Polynomial Nat) : Polynomial Nat :=
  (2 * n * n + n * (2 * m * m + 7 * m + 10) + 3) +
  (2 * n * n * n + n * n * 13 + 9 * n + 3) + poly_WordInstance_projectBudget m l + 2

theorem eval_poly_WordInstance_remainingStepBudget (x : Nat) (n m l : Polynomial Nat) :
    (poly_WordInstance_remainingStepBudget n m l).eval x = WordInstance.remainingStepBudget (n.eval x) (m.eval x) (l.eval x) := by
  simp only [poly_WordInstance_remainingStepBudget, WordInstance.remainingStepBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_WordInstance_projectBudget]

noncomputable def poly_WordInstance_remainingRestoreCeiling (N : Polynomial Nat) : Polynomial Nat :=
  4 * N * N + 20 * N + 7

theorem eval_poly_WordInstance_remainingRestoreCeiling (x : Nat) (N : Polynomial Nat) :
    (poly_WordInstance_remainingRestoreCeiling N).eval x = WordInstance.remainingRestoreCeiling (N.eval x) := by
  simp only [poly_WordInstance_remainingRestoreCeiling, WordInstance.remainingRestoreCeiling, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_WordInstance_universalBudget (N B : Polynomial Nat) : Polynomial Nat :=
  poly_WordInstance_nonrootCeiling N + poly_WordInstance_zeroCeiling N B + poly_WordInstance_baseCeiling N +
  poly_WordInstance_reduceInputBudget N N B + poly_soleBudget N N +
  poly_WordInstance_contractStepBudget N N B + poly_WordInstance_terminalStepBudget N N + poly_WordInstance_singleRestoreCeiling N +
  poly_roundDataBudget N N + poly_WordInstance_roundShapeBudget N N + poly_WordInstance_roundedCeiling N +
  poly_WordInstance_remainingStepBudget N N N + poly_WordInstance_remainingRestoreCeiling N + 50

theorem eval_poly_WordInstance_universalBudget (x : Nat) (N B : Polynomial Nat) :
    (poly_WordInstance_universalBudget N B).eval x = WordInstance.universalBudget (N.eval x) (B.eval x) := by
  simp only [poly_WordInstance_universalBudget, WordInstance.universalBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_WordInstance_nonrootCeiling, eval_poly_WordInstance_zeroCeiling, eval_poly_WordInstance_baseCeiling, eval_poly_WordInstance_reduceInputBudget, eval_poly_soleBudget, eval_poly_WordInstance_contractStepBudget, eval_poly_WordInstance_terminalStepBudget, eval_poly_WordInstance_singleRestoreCeiling, eval_poly_roundDataBudget, eval_poly_WordInstance_roundShapeBudget, eval_poly_WordInstance_roundedCeiling, eval_poly_WordInstance_remainingStepBudget, eval_poly_WordInstance_remainingRestoreCeiling]

noncomputable def poly_RuntimePolynomial_weightedBudget (N B : Polynomial Nat) : Polynomial Nat :=
  poly_RuntimePolynomial_normalizeCeiling N + (N + 1) * poly_WordInstance_universalBudget N B + 1

theorem eval_poly_RuntimePolynomial_weightedBudget (x : Nat) (N B : Polynomial Nat) :
    (poly_RuntimePolynomial_weightedBudget N B).eval x = RuntimePolynomial.weightedBudget (N.eval x) (B.eval x) := by
  simp only [poly_RuntimePolynomial_weightedBudget, RuntimePolynomial.weightedBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_RuntimePolynomial_normalizeCeiling, eval_poly_WordInstance_universalBudget]

noncomputable def poly_RuntimePolynomial_encodingBudget (N : Polynomial Nat) : Polynomial Nat :=
  (2 * N * N + 7 * N + 3) +
  (2 * N * N + N * (N * (7 * N + 3) + 7) + 3) + 1

theorem eval_poly_RuntimePolynomial_encodingBudget (x : Nat) (N : Polynomial Nat) :
    (poly_RuntimePolynomial_encodingBudget N).eval x = RuntimePolynomial.encodingBudget (N.eval x) := by
  simp only [poly_RuntimePolynomial_encodingBudget, RuntimePolynomial.encodingBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero]

noncomputable def poly_RuntimePolynomial_unweightedBudget (N : Polynomial Nat) : Polynomial Nat :=
  poly_RuntimePolynomial_encodingBudget N + poly_RuntimePolynomial_weightedBudget N N + 1

theorem eval_poly_RuntimePolynomial_unweightedBudget (x : Nat) (N : Polynomial Nat) :
    (poly_RuntimePolynomial_unweightedBudget N).eval x = RuntimePolynomial.unweightedBudget (N.eval x) := by
  simp only [poly_RuntimePolynomial_unweightedBudget, RuntimePolynomial.unweightedBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero, eval_poly_RuntimePolynomial_encodingBudget, eval_poly_RuntimePolynomial_weightedBudget]

theorem diagonal_polynomial : IsPolynomial (fun L => weightedBudget L L) := by
  refine ⟨poly_RuntimePolynomial_weightedBudget Polynomial.X Polynomial.X, ?_⟩
  intro x
  simpa only [Polynomial.eval_X] using (eval_poly_RuntimePolynomial_weightedBudget x Polynomial.X Polynomial.X).symm

theorem encoding_polynomial : IsPolynomial encodingBudget := by
  refine ⟨poly_RuntimePolynomial_encodingBudget Polynomial.X, ?_⟩
  intro x
  simpa only [Polynomial.eval_X] using (eval_poly_RuntimePolynomial_encodingBudget x Polynomial.X).symm

theorem unweighted_polynomial : IsPolynomial unweightedBudget := by
  refine ⟨poly_RuntimePolynomial_unweightedBudget Polynomial.X, ?_⟩
  intro x
  simpa only [Polynomial.eval_X] using (eval_poly_RuntimePolynomial_unweightedBudget x Polynomial.X).symm

theorem universal_mono {n n' B B' : Nat} (hn : n ≤ n') (hB : B ≤ B') :
    universalBudget n B ≤ universalBudget n' B' := by
  unfold universalBudget nonrootCeiling zeroCeiling baseCeiling singleRestoreCeiling roundedCeiling remainingRestoreCeiling
  gcongr

theorem weighted_mono {n n' B B' : Nat} (hn : n ≤ n') (hB : B ≤ B') :
    weightedBudget n B ≤ weightedBudget n' B' := by
  unfold weightedBudget normalizeCeiling
  gcongr
  exact universal_mono hn hB

theorem weighted_polynomial_bound :
    ∃ p : Polynomial Nat, ∀ n B, weightedBudget n B ≤ p.eval (n + B + 1) := by
  obtain ⟨p, hp⟩ := diagonal_polynomial
  refine ⟨p, fun n B => ?_⟩
  rw [← hp]
  exact weighted_mono (by omega) (by omega)

end GyoriLovasz.RuntimePolynomial

