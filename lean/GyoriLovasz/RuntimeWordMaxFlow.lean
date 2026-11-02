import GyoriLovasz.RuntimeWordThroughput
import GyoriLovasz.RuntimeWordCut
import GyoriLovasz.RuntimeMinCut

namespace GyoriLovasz.Flow
open Binary
open scoped BigOperators

def maxFlowWords (s : WordResidual n m) (source sink : Fin n) (B : Nat) :
    Costed.Computation (WordResidual n (m + 1)) :=
  let limit := returnCapacity s.capacity
  let network := throughputWords s source sink limit.1
  let solved := solveStored network.1 (B + m + 1)
  (solved.1, limit.2 + network.2 + solved.2 + 2)

theorem throughput_prepared_bounds (s : WordResidual n m) (source sink : Fin n)
    (B : Nat) (bound : WordResidualBound s B) :
    WordResidualBound (throughputWords s source sink (returnCapacity s.capacity).1).1 (B + m + 1) :=
  throughputWords_bounds s (B + m + 1) (wordResidualBound_mono s B _ bound (by omega))
    source sink _ (returnCapacity_bounds s.capacity B (fun e => (bound.1 e).1)).1

theorem maxFlowWords_certified (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source sink : Fin n) (B : Nat) (bound : WordResidualBound s B) :
    let G := throughputNetwork (decodeNetwork s) source sink ((∑ e : Fin m, value s.capacity[e.val]) + 1)
    Feasible G (decodeFlow (maxFlowWords s source sink B).1) ∧
      DualFeasible G (decodeFlow (maxFlowWords s source sink B).1)
        (decodePotential (maxFlowWords s source sink B).1) := by
  have hb := throughput_prepared_bounds s source sink B bound
  have hc := throughputWords_codes s correct source sink (returnCapacity s.capacity).1
  have hf := (solveStored_optimal _ hc (B + m + 1) (fun e => (hb.1 e).1)).1
  have hd := solveStored_dual _ hc (B + m + 1) (fun e => (hb.1 e).1)
  rw [throughputWords_network, returnCapacity_value] at hf hd
  exact ⟨hf, hd⟩

theorem maxFlowWords_correct (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source sink : Fin n) (distinct : source ≠ sink) (B : Nat) (bound : WordResidualBound s B) :
    let f := decodeFlow (maxFlowWords s source sink B).1
    STFeasible (decodeNetwork s) source sink (fun e => f e.succ) (f 0) ∧
      ∀ other amount, STFeasible (decodeNetwork s) source sink other amount → amount ≤ f 0 := by
  have h := maxFlowWords_certified s correct source sink B bound
  apply minimumCost_unboundedMaximumFlow (decodeNetwork s) source sink distinct _ (by
    change (∑ e : Fin m, value s.capacity[e.val]) ≤ (∑ e : Fin m, value s.capacity[e.val]) + 1
    omega) _ h.1
  exact dual_optimal h.1 h.2

def returnBudget (m B : Nat) :=
  2 * m * m + 2 * m + m * (7 * (B + m) + 5) + 7 * (B + m) + 6

def throughputBudget (m : Nat) := 8 * (m + 1) * (m + 1) + 32 * (m + 1) + 13

def maxFlowBudget (n m B : Nat) :=
  returnBudget m B + throughputBudget m + storedBudget n (m + 1) (B + m + 1) + 2

theorem maxFlowWords_cost (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source sink : Fin n) (B : Nat) (bound : WordResidualBound s B) :
    (maxFlowWords s source sink B).2 ≤ maxFlowBudget n m B := by
  have hl := (returnCapacity_bounds s.capacity B (fun e => (bound.1 e).1)).2
  have hg := throughputWords_cost s source sink (returnCapacity s.capacity).1
  have hs := solveStored_cost _ (throughputWords_codes s correct source sink _)
    (B + m + 1) (throughput_prepared_bounds s source sink B bound)
  change _ ≤ returnBudget m B at hl
  change _ ≤ throughputBudget m at hg
  change _ ≤ storedBudget n (m + 1) (B + m + 1) at hs
  dsimp only [maxFlowWords, maxFlowBudget]
  omega

def maxFlowWordLength (n m B : Nat) :=
  (B + m + 1) + ((m + 2) * (B + m + 1)) * (n + 6)

theorem maxFlowWords_bounds (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source sink : Fin n) (B : Nat) (bound : WordResidualBound s B) :
    WordResidualBound (maxFlowWords s source sink B).1 (maxFlowWordLength n m B) :=
  solveStored_bounds _ (throughputWords_codes s correct source sink _) _
    (throughput_prepared_bounds s source sink B bound)

def minCutWords (s : WordResidual n m) (source sink : Fin n) (B : Nat) :
    Costed.Computation (Vector Bool n) :=
  let solved := maxFlowWords s source sink B
  let selected := thresholdWords solved.1.potential source
  (selected.1, solved.2 + selected.2 + 1)

theorem minCutWords_correct (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source sink : Fin n) (distinct : source ≠ sink) (B : Nat) (bound : WordResidualBound s B) :
    let S := fun v : Fin n => (minCutWords s source sink B).1[v.val]
    S source = true ∧ S sink = false ∧
      ∀ T, T source = true → T sink = false → cutCapacity (decodeNetwork s) S ≤ cutCapacity (decodeNetwork s) T := by
  have h := maxFlowWords_certified s correct source sink B bound
  have cut := dual_minimum_cut (decodeNetwork s) source sink distinct _
    (show (∑ e, (decodeNetwork s).capacity e) < (∑ e : Fin m, value s.capacity[e.val]) + 1 by
      change (∑ e : Fin m, value s.capacity[e.val]) < (∑ e : Fin m, value s.capacity[e.val]) + 1
      omega) _ _ h.1 h.2
  simpa only [minCutWords, thresholdWords_value, decodePotential] using
    And.intro cut.1 (And.intro cut.2.1 cut.2.2.2)

theorem minCutWords_cost (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source sink : Fin n) (B : Nat) (bound : WordResidualBound s B) :
    (minCutWords s source sink B).2 ≤ maxFlowBudget n m B +
      2 * n * n + n * (9 * maxFlowWordLength n m B + 16) + 4 := by
  have hf := maxFlowWords_cost s correct source sink B bound
  have hb := maxFlowWords_bounds s correct source sink B bound
  have hc := thresholdWords_cost (maxFlowWords s source sink B).1.potential (maxFlowWordLength n m B)
    (fun v => (hb.2 v).2) source
  dsimp only [minCutWords]
  omega

def minValueWords (s : WordResidual n m) (source sink : Fin n) (B : Nat) : Costed.Computation (List Bool) :=
  let solved := maxFlowWords s source sink B
  (solved.1.flow[0], solved.2 + 2)

theorem minValueWords_spec (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source sink : Fin n) (distinct : source ≠ sink) (B : Nat) (bound : WordResidualBound s B) :
    ∃ S : Fin n → Bool, S source = true ∧ S sink = false ∧
      value (minValueWords s source sink B).1 = cutCapacity (decodeNetwork s) S ∧
      ∀ T, T source = true → T sink = false → cutCapacity (decodeNetwork s) S ≤ cutCapacity (decodeNetwork s) T := by
  have h := maxFlowWords_certified s correct source sink B bound
  have cut := dual_minimum_cut (decodeNetwork s) source sink distinct _
    (show (∑ e, (decodeNetwork s).capacity e) < (∑ e : Fin m, value s.capacity[e.val]) + 1 by
      change (∑ e : Fin m, value s.capacity[e.val]) < (∑ e : Fin m, value s.capacity[e.val]) + 1
      omega) _ _ h.1 h.2
  exact ⟨_, cut.1, cut.2.1, cut.2.2.1.symm, cut.2.2.2⟩

theorem minValueWords_cost (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source sink : Fin n) (B : Nat) (bound : WordResidualBound s B) :
    (minValueWords s source sink B).2 ≤ maxFlowBudget n m B + 2 :=
  Nat.add_le_add_right (maxFlowWords_cost s correct source sink B bound) 2

theorem minValueWords_length (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source sink : Fin n) (B : Nat) (bound : WordResidualBound s B) :
    (minValueWords s source sink B).1.length ≤ maxFlowWordLength n m B :=
  ((maxFlowWords_bounds s correct source sink B bound).1 0).2.1

end GyoriLovasz.Flow
