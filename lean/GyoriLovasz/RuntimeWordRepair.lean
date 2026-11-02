import GyoriLovasz.RuntimeWordDistances
import GyoriLovasz.RuntimeWordAugment
import GyoriLovasz.RuntimeRepair

namespace GyoriLovasz.Flow
open Binary

def repairReduced (s : WordResidual n m) (a : Fin m) : SignedWord × Nat :=
  let result := reducedCostWord s.cost[a.val] s.potential[(s.tail[a.val]).val]
    s.potential[(s.head[a.val]).val]
  (result.1, result.2 + 7)

theorem repairReduced_value (s : WordResidual n m) (a : Fin m) :
    signedValue (repairReduced s a).1 = reducedCost (decodeNetwork s) (decodePotential s) a := by
  simp [repairReduced, reducedCostWord_correct, reducedCost, decodeNetwork, decodePotential]

theorem negative_value (w : SignedWord) : w.negative = true ↔ signedValue w < 0 := by
  rcases w with ⟨b, digits⟩
  cases b <;> simp [signedValue] <;> omega

abbrev WordRepairOutput (n m : Nat) := Vector (List Bool) m × Vector SignedWord n

def wordRepair (s : WordResidual n m) (a : Fin m) : Costed.Computation (WordRepairOutput n m) :=
  let red := repairReduced s a
  if red.1.negative then
    let neg := negateSigned red.1
    let bound := naturalWord neg.1
    let d := wordDistances s s.head[a.val] bound
    let updated := updatePotential s.potential d.1
    let cmp := compareWords d.1[(s.tail[a.val]).val] bound
    if cmp.1.1 then
      let path := wordResidualRoute s s.head[a.val] s.tail[a.val] bound
      match path.1 with
      | none => ((s.flow, updated.1), red.2 + neg.2 + d.2 + updated.2 + cmp.2 + path.2 + 14)
      | some p =>
        let augmented := augmentWords s.flow ((a, false) :: p)
        ((augmented.1, updated.1), red.2 + neg.2 + d.2 + updated.2 + cmp.2 + path.2 + augmented.2 + 16)
    else ((s.flow, updated.1), red.2 + neg.2 + d.2 + updated.2 + cmp.2 + 12)
  else ((s.flow, s.potential), red.2 + 2)

def decodeRepair (out : WordRepairOutput n m) : Vector Nat m × Vector Int n :=
  (Vector.ofFn (fun e => value out.1[e.val]), Vector.ofFn (fun v => signedValue out.2[v.val]))

theorem decodeRepair_old (s : WordResidual n m) : decodeRepair (s.flow, s.potential) =
    (Vector.ofFn (decodeFlow s), Vector.ofFn (decodePotential s)) := rfl

theorem decodeRepair_update (s : WordResidual n m) (d : Vector (List Bool) n) :
    decodeRepair (s.flow, (updatePotential s.potential d).1) =
      (Vector.ofFn (decodeFlow s), Vector.ofFn (fun v => decodePotential s v + value d[v.val])) := by
  simp only [decodeRepair, updatePotential_value, decodeFlow, decodePotential]
  rfl

theorem decodeRepair_augment (s : WordResidual n m) (d : Vector (List Bool) n)
    (p : List (ResidualArc m)) :
    decodeRepair ((augmentWords s.flow p).1, (updatePotential s.potential d).1) =
      (Vector.ofFn (augment (decodeFlow s) (routeDelta p)),
        Vector.ofFn (fun v => decodePotential s v + value d[v.val])) := by
  simp only [decodeRepair, augmentWords_value, updatePotential_value, decodeFlow, decodePotential]
  rfl

theorem wordRepair_value (s : WordResidual n m) (correct : VertexCodesCorrect s) (a : Fin m) :
    decodeRepair (wordRepair s a).1 = repairStep (decodeNetwork s) (decodeFlow s) (decodePotential s) a := by
  have neg := negative_value (repairReduced s a).1
  rw [repairReduced_value] at neg
  have bv : value (naturalWord (negateSigned (repairReduced s a).1).1) =
      (-reducedCost (decodeNetwork s) (decodePotential s) a).toNat := by
    rw [naturalWord_value, negateSigned_correct, repairReduced_value]
  have dv := wordDistances_value s correct s.head[a.val]
    (naturalWord (negateSigned (repairReduced s a).1).1)
  have cmp := (compareWords_correct
    (wordDistances s s.head[a.val] (naturalWord (negateSigned (repairReduced s a).1).1)).1[(s.tail[a.val]).val]
    (naturalWord (negateSigned (repairReduced s a).1).1)).1
  rw [dv, bv] at cmp
  have pv := wordResidualRoute_value s correct s.head[a.val] s.tail[a.val]
    (naturalWord (negateSigned (repairReduced s a).1).1)
  rw [bv] at pv
  dsimp only [wordRepair, repairStep]
  simp only [show (decodeNetwork s).head a = s.head[a.val] from rfl,
    show (decodeNetwork s).tail a = s.tail[a.val] from rfl]
  by_cases hn : reducedCost (decodeNetwork s) (decodePotential s) a < 0
  · have hn' : ¬0 ≤ reducedCost (decodeNetwork s) (decodePotential s) a := by omega
    simp only [if_pos (neg.mpr hn), if_neg hn']
    by_cases hc : (compareWords
      (wordDistances s s.head[a.val] (naturalWord (negateSigned (repairReduced s a).1).1)).1[(s.tail[a.val]).val]
      (naturalWord (negateSigned (repairReduced s a).1).1)).1.1 = true
    · rw [if_pos hc, if_pos (cmp.mp hc), pv]
      cases hp : residualShortestRoute (decodeNetwork s) (decodeFlow s) (decodePotential s)
        s.head[a.val] s.tail[a.val] (-reducedCost (decodeNetwork s) (decodePotential s) a).toNat with
      | none => simp only [decodeRepair_update, dv, bv]
      | some p => simp only [decodeRepair_augment, dv, bv]
    · rw [if_neg hc, if_neg (fun h => hc (cmp.mpr h))]
      simp only [decodeRepair_update, dv, bv]
  · have hn' : 0 ≤ reducedCost (decodeNetwork s) (decodePotential s) a := by omega
    simp only [if_neg (fun h => hn (neg.mp h)), if_pos hn']
    rfl

theorem repairReduced_bounds (s : WordResidual n m) (B : Nat)
    (bound : WordResidualBound s B) (a : Fin m) :
    (repairReduced s a).2 ≤ 54 * B + 91 ∧ (repairReduced s a).1.digits.length ≤ B + 3 := by
  have hc := (bound.1 a).2.2
  have ht := (bound.2 s.tail[a.val]).2
  have hh := (bound.2 s.head[a.val]).2
  have hcost := reducedCostWord_cost_bound _ _ _ B hc ht hh
  have hlen := reducedCostWord_length _ _ _ B hc ht hh
  dsimp only [repairReduced]
  exact ⟨by omega, hlen⟩

def repairBudget (n m B : Nat) :=
  (54 * B + 91) + (18 * (B + 3) + 8) +
  (residualBuildBudget n m B + graphBudget n + distanceBudget n (B + 4) + 2) +
  (2 * n * n + n * (18 * (B + 4 + n) + 18) + 3) +
  (9 * (B + 4 + n) + 2) +
  (residualBuildBudget n m B + graphBudget n + routeBudget n (B + 4) + 8 * n + 4) +
  augmentBudget m B n + 16

theorem wordRepair_cost (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (B : Nat) (bound : WordResidualBound s B) (a : Fin m) :
    (wordRepair s a).2 ≤ repairBudget n m B := by
  have hr := repairReduced_bounds s B bound a
  have hn := negateSigned_cost_bound (repairReduced s a).1
  have hnl := negateSigned_length (repairReduced s a).1
  have hb : (naturalWord (negateSigned (repairReduced s a).1).1).length ≤ B + 4 := by
    have h := naturalWord_length (negateSigned (repairReduced s a).1).1
    omega
  have hd := wordDistances_cost s s.head[a.val] _ B bound hb
  have hdl := wordDistances_bounds s s.head[a.val] _ B bound hb
  have hu := updatePotential_cost s.potential
    (wordDistances s s.head[a.val] (naturalWord (negateSigned (repairReduced s a).1).1)).1
    (B + 4 + n) (fun v => Nat.le_trans (bound.2 v).2 (by omega)) hdl
  have hc := compareWords_steps
    (wordDistances s s.head[a.val] (naturalWord (negateSigned (repairReduced s a).1).1)).1[(s.tail[a.val]).val]
    (naturalWord (negateSigned (repairReduced s a).1).1)
  have hdt := hdl s.tail[a.val]
  have hp := wordResidualRoute_cost s correct s.head[a.val] s.tail[a.val] _ B bound hb
  dsimp only [wordRepair]
  unfold repairBudget
  split
  · split
    · split
      · omega
      · rename_i p found
        have hl := wordResidualRoute_length s correct s.head[a.val] s.tail[a.val] _ p found
        have ha := augmentWords_cost_le s.flow B n (fun e => (bound.1 e).2.1)
          ((a, false) :: p) (by simp only [List.length_cons]; omega)
        omega
    · omega
  · omega

theorem wordRepair_correct (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (feasible : Feasible (decodeNetwork s) (decodeFlow s))
    (dual : DualFeasible (decodeNetwork s) (decodeFlow s) (decodePotential s)) (a : Fin m) :
    Feasible (incrementCapacity (decodeNetwork s) a) (fun e => value (wordRepair s a).1.1[e.val]) ∧
    DualFeasible (incrementCapacity (decodeNetwork s) a) (fun e => value (wordRepair s a).1.1[e.val])
      (fun v => signedValue (wordRepair s a).1.2[v.val]) := by
  have h := repairStep_correct feasible dual a
  rw [← wordRepair_value s correct a] at h
  simpa [decodeRepair] using h

theorem wordRepair_bounds (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (B : Nat) (bound : WordResidualBound s B) (a : Fin m) :
    (∀ e : Fin m, (wordRepair s a).1.1[e.val].length ≤ B + n + 6) ∧
    (∀ v : Fin n, (wordRepair s a).1.2[v.val].digits.length ≤ B + n + 6) := by
  have hr := repairReduced_bounds s B bound a
  have hnl := negateSigned_length (repairReduced s a).1
  have hb : (naturalWord (negateSigned (repairReduced s a).1).1).length ≤ B + 4 := by
    have h := naturalWord_length (negateSigned (repairReduced s a).1).1
    omega
  have hdl := wordDistances_bounds s s.head[a.val] _ B bound hb
  have hu := updatePotential_length s.potential
    (wordDistances s s.head[a.val] (naturalWord (negateSigned (repairReduced s a).1).1)).1
    (B + 4 + n) (fun v => Nat.le_trans (bound.2 v).2 (by omega)) hdl
  dsimp only [wordRepair]
  split
  · split
    · split
      · exact ⟨fun e => Nat.le_trans (bound.1 e).2.1 (by omega), fun v => Nat.le_trans (hu v) (by omega)⟩
      · rename_i p found
        have hl := wordResidualRoute_length s correct s.head[a.val] s.tail[a.val] _ p found
        refine ⟨?_, fun v => Nat.le_trans (hu v) (by omega)⟩
        intro e
        have ha := augmentWords_length s.flow B (fun e => (bound.1 e).2.1) ((a, false) :: p) e
        simp only [List.length_cons] at ha
        dsimp only
        omega
    · exact ⟨fun e => Nat.le_trans (bound.1 e).2.1 (by omega), fun v => Nat.le_trans (hu v) (by omega)⟩
  · exact ⟨fun e => Nat.le_trans (bound.1 e).2.1 (by omega), fun v => Nat.le_trans (bound.2 v).2 (by omega)⟩

end GyoriLovasz.Flow
