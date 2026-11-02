import GyoriLovasz.RuntimeWordSelection
import GyoriLovasz.RuntimeSelectionCost
import GyoriLovasz.RuntimeEnumeration

namespace GyoriLovasz.Flow
open Binary

/-- Materialized words used by residual selection. The decoding functions are
specifications, not charged computations executed by the word routines. -/
structure WordResidual (n m : Nat) where
  tail : Vector (Fin n) m
  head : Vector (Fin n) m
  vertexCode : Vector (List Bool) n
  capacity : Vector (List Bool) m
  flow : Vector (List Bool) m
  cost : Vector SignedWord m
  potential : Vector SignedWord n

def decodeNetwork (s : WordResidual n m) : Network n m where
  tail := fun e => s.tail[e.val]
  head := fun e => s.head[e.val]
  capacity := fun e => value s.capacity[e.val]
  cost := fun e => signedValue s.cost[e.val]

def decodeFlow (s : WordResidual n m) : Fin m → Nat := fun e => value s.flow[e.val]
def decodePotential (s : WordResidual n m) : Fin n → Int := fun v => signedValue s.potential[v.val]

def VertexCodesCorrect (s : WordResidual n m) : Prop :=
  ∀ v : Fin n, value s.vertexCode[v.val] = v.val

def WordResidualBound (s : WordResidual n m) (B : Nat) : Prop :=
  (∀ e : Fin m, s.capacity[e.val].length ≤ B ∧ s.flow[e.val].length ≤ B ∧ s.cost[e.val].digits.length ≤ B) ∧
  ∀ v : Fin n, s.vertexCode[v.val].length ≤ B ∧ s.potential[v.val].digits.length ≤ B

/-- Eligibility implemented by three binary comparisons. The constant charge
accounts for reference-array accesses, direction selection, and Boolean gates.
Reference accesses are unit operations here; this is not a compiler timing model. -/
def wordEligible (s : WordResidual n m) (u v : Fin n) (a : ResidualArc m) : Bool × Nat :=
  let t := if a.2 then s.head[a.1.val] else s.tail[a.1.val]
  let h := if a.2 then s.tail[a.1.val] else s.head[a.1.val]
  let free := if a.2 then compareWords [] s.flow[a.1.val]
    else compareWords s.flow[a.1.val] s.capacity[a.1.val]
  let tailMatch := compareWords s.vertexCode[t.val] s.vertexCode[u.val]
  let headMatch := compareWords s.vertexCode[h.val] s.vertexCode[v.val]
  (free.1.1 && tailMatch.1.2 && headMatch.1.2, free.2 + tailMatch.2 + headMatch.2 + 32)

theorem wordEligible_value (s : WordResidual n m) (codes : VertexCodesCorrect s)
    (u v : Fin n) (a : ResidualArc m) :
    (wordEligible s u v a).1 =
      (available (decodeNetwork s) (decodeFlow s) a &&
        decide (arcTail (decodeNetwork s) a = u ∧ arcHead (decodeNetwork s) a = v)) := by
  obtain ⟨e, back⟩ := a
  have tailEq : value s.vertexCode[(s.tail[e.val]).val] = (s.tail[e.val]).val := codes _
  have headEq : value s.vertexCode[(s.head[e.val]).val] = (s.head[e.val]).val := codes _
  have uEq := codes u
  have vEq := codes v
  apply Bool.eq_iff_iff.mpr
  cases back <;> simp [wordEligible, available, arcTail, arcHead, decodeNetwork, decodeFlow,
    (compareWords_correct _ _).1, (compareWords_correct _ _).2, value,
    tailEq, headEq, uEq, vEq, and_assoc, Fin.val_inj]

theorem wordEligible_cost (s : WordResidual n m) (B : Nat) (bound : WordResidualBound s B)
    (u v : Fin n) (a : ResidualArc m) : (wordEligible s u v a).2 ≤ 27 * B + 38 := by
  have flow := (bound.1 a.1).2.1
  have cap := (bound.1 a.1).1
  have t := (bound.2 s.tail[a.1.val]).1
  have h := (bound.2 s.head[a.1.val]).1
  have ub := (bound.2 u).1
  have vb := (bound.2 v).1
  obtain ⟨e, back⟩ := a
  dsimp only at flow cap t h
  cases back <;> simp only [wordEligible, Bool.false_eq_true, if_false, if_true,
    compareWords_steps, List.length_nil, Nat.zero_max] <;> omega

def wordScore (s : WordResidual n m) (a : ResidualArc m) : SignedWord × Nat :=
  let rc := reducedCostWord s.cost[a.1.val]
    s.potential[(s.tail[a.1.val]).val] s.potential[(s.head[a.1.val]).val]
  if a.2 then
    let negative := negateSigned rc.1
    (negative.1, rc.2 + negative.2 + 9)
  else (rc.1, rc.2 + 9)

theorem wordScore_value (s : WordResidual n m) (a : ResidualArc m) :
    signedValue (wordScore s a).1 = arcCost (decodeNetwork s) (decodePotential s) a := by
  dsimp only [wordScore]
  split <;> simp_all [negateSigned_correct, reducedCostWord_correct, arcCost,
    reducedCost, decodeNetwork, decodePotential]

theorem wordScore_bounds (s : WordResidual n m) (B : Nat) (bound : WordResidualBound s B)
    (a : ResidualArc m) :
    (wordScore s a).2 ≤ 72 * B + 155 ∧ (wordScore s a).1.digits.length ≤ B + 4 := by
  have cb := (bound.1 a.1).2.2
  have tb := (bound.2 s.tail[a.1.val]).2
  have hb := (bound.2 s.head[a.1.val]).2
  have cost := reducedCostWord_cost_bound _ _ _ B cb tb hb
  have len := reducedCostWord_length _ _ _ B cb tb hb
  have negCost := negateSigned_cost_bound
    (reducedCostWord s.cost[a.1.val] s.potential[(s.tail[a.1.val]).val] s.potential[(s.head[a.1.val]).val]).1
  have negLen := negateSigned_length
    (reducedCostWord s.cost[a.1.val] s.potential[(s.tail[a.1.val]).val] s.potential[(s.head[a.1.val]).val]).1
  dsimp only [wordScore]
  split <;> dsimp only <;> constructor <;> omega

def wordBestArc (s : WordResidual n m) (u v : Fin n) : Costed.Computation (Option (ResidualArc m)) :=
  let arcs := Costed.enumerateArcs m
  let best := Costed.filterArgminWords (wordEligible s u v) (wordScore s) arcs.1
  (best.1, arcs.2 + best.2 + 1)

theorem wordBestArc_value (s : WordResidual n m) (codes : VertexCodesCorrect s) (u v : Fin n) :
    (wordBestArc s u v).1 = bestArc (decodeNetwork s) (decodeFlow s) (decodePotential s) u v := by
  simp only [wordBestArc, Costed.filterArgminWords_value, wordEligible_value s codes,
    wordScore_value, bestArc, residualCandidates, allResidualArcs, Costed.enumerateArcs_value]

/-- No arithmetic/comparison cost oracle appears here. Candidate enumeration
is included. Reference-address bit costs still require machine-model refinement. -/
theorem wordBestArc_cost (s : WordResidual n m) (B : Nat) (bound : WordResidualBound s B)
    (u v : Fin n) : (wordBestArc s u v).2 ≤
      2 * m * m + 7 * m + 2 * m * (180 * B + 398) + 6 := by
  have cost := Costed.filterArgminWords_cost (wordEligible s u v) (wordScore s) (allResidualArcs m)
    (27 * B + 38) (72 * B + 155) (B + 4)
    (wordEligible_cost s B bound u v)
    (fun a => (wordScore_bounds s B bound a).1)
    (fun a => (wordScore_bounds s B bound a).2)
  simp only [allResidualArcs_length] at cost
  have scan : (Costed.filterArgminWords (wordEligible s u v) (wordScore s) (allResidualArcs m)).2 ≤
      2 * m * (180 * B + 398) + 2 := by convert cost using 1; ring
  simp only [wordBestArc, Costed.enumerateArcs_value, Costed.enumerateArcs_cost]
  change (2 * m * m + 7 * m + 3) +
    (Costed.filterArgminWords (wordEligible s u v) (wordScore s) (allResidualArcs m)).2 + 1 ≤ _
  omega

end GyoriLovasz.Flow
