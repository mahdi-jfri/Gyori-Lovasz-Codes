import GyoriLovasz.RuntimeWordTransport
import GyoriLovasz.RuntimeRootMask
import GyoriLovasz.RuntimeEssentialTable
import GyoriLovasz.Weighted

namespace GyoriLovasz
open Binary TransportNetwork
open scoped BigOperators

def splitInputs (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (weight : Vector (List Bool) n) :
    Costed.Computation (Vector (Vector Bool k) n × Vector (List Bool) n) :=
  let mask := rootMask roots
  let essential := VertexNetwork.essentialTable E mask.1
  let allowed := Costed.tabulate n (fun v => Costed.tabulate k
    (fun i => (essential.1[v.val][roots[i.val].val], 3)))
  let supply := Costed.tabulate n (fun v => (if mask.1[v.val] then [] else weight[v.val], 3))
  ((allowed.1, supply.1), mask.2 + essential.2 + allowed.2 + supply.2 + 3)

theorem splitInputs_allowed (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (weight : Vector (List Bool) n) (v : Fin n) (i : Fin k) :
    (splitInputs E roots weight).1.1[v.val][i.val] = true ↔
      ∃ hv : ¬RootSet (fun j => roots[j.val]) v,
        Essential (fun x y => E[x.val][y.val] = true) (RootSet (fun j => roots[j.val]))
          v hv roots[i.val] := by
  have mask : (fun x : Fin n => (rootMask roots).1[x.val] = true) =
      RootSet (fun j => roots[j.val]) := funext (fun x => propext (rootMask_correct roots x))
  simp only [splitInputs, Costed.tabulate_value]
  have h := VertexNetwork.essentialTable_correct E (rootMask roots).1 v roots[i.val]
  change _ ↔ ∃ hv : ¬(fun x : Fin n => (rootMask roots).1[x.val] = true) v,
    (fun x : Fin n => (rootMask roots).1[x.val] = true) roots[i.val] ∧ _ at h
  rw [mask] at h
  simpa only [show RootSet (fun j => roots[j.val]) roots[i.val] from ⟨i, rfl⟩, true_and] using h

theorem splitInputs_supply (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (weight : Vector (List Bool) n) (v : Fin n) :
    (splitInputs E roots weight).1.2[v.val] =
      if (rootMask roots).1[v.val] then [] else weight[v.val] := by
  simp only [splitInputs, Costed.tabulate_value]

theorem splitInputs_bounds (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (weight : Vector (List Bool) n) (B : Nat) (wb : ∀ v : Fin n, weight[v.val].length ≤ B)
    (v : Fin n) : (splitInputs E roots weight).1.2[v.val].length ≤ B := by
  rw [splitInputs_supply]
  split
  · simp
  · exact wb v

theorem splitInputs_feasible (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (weight : Vector (List Bool) n) (capacity : Vector (List Bool) k) :
    (∃ x, MatrixFeasible (fun v i => (splitInputs E roots weight).1.1[v.val][i.val])
      (fun v => value (splitInputs E roots weight).1.2[v.val])
      (fun i => value capacity[i.val]) x) ↔
    ∃ x, SplitFeasible (fun v u => E[v.val][u.val] = true) (fun i => roots[i.val])
      (fun v => value weight[v.val]) (fun i => value capacity[i.val]) x := by
  classical
  constructor
  · rintro ⟨x, allowed, rows, cols⟩
    refine ⟨x, ?_, ?_, ?_⟩
    · intro v hv i positive
      exact ((splitInputs_allowed E roots weight v i).mp (allowed v i positive)).2
    · intro v hv
      have hm : (rootMask roots).1[v.val] = false :=
        Bool.eq_false_iff.mpr (fun h => hv ((rootMask_correct roots v).mp h))
      simpa only [splitInputs_supply, hm, Bool.false_eq_true, ↓reduceIte] using rows v
    · intro i
      exact le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) (cols i)
  · rintro ⟨x, allowed, rows, cols⟩
    let y := fun v i => if RootSet (fun j => roots[j.val]) v then 0 else x v i
    refine ⟨y, ?_, ?_, ?_⟩
    · intro v i positive
      have hv : ¬RootSet (fun j => roots[j.val]) v := by
        intro h; simp [y, h] at positive
      apply (splitInputs_allowed E roots weight v i).mpr
      exact ⟨hv, allowed v hv i (by simpa [y, hv] using positive)⟩
    · intro v
      by_cases hv : RootSet (fun j => roots[j.val]) v
      · have hm := (rootMask_correct roots v).mpr hv
        simp [y, hv, splitInputs_supply, hm, value]
      · have hm : (rootMask roots).1[v.val] = false :=
          Bool.eq_false_iff.mpr (fun h => hv ((rootMask_correct roots v).mp h))
        simpa [y, hv, splitInputs_supply, hm] using rows v hv
    · intro i
      have h := cols i
      rw [Finset.sum_filter] at h
      simpa only [y, ite_not] using h

def splitCheck (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (weight : Vector (List Bool) n) (capacity : Vector (List Bool) k) (B : Nat) : Bool × Nat :=
  let inputs := splitInputs E roots weight
  let result := matrixCheck inputs.1.1 inputs.1.2 capacity B
  (result.1, inputs.2 + result.2 + 1)

theorem splitCheck_correct (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (weight : Vector (List Bool) n) (capacity : Vector (List Bool) k) (B : Nat)
    (wb : ∀ v : Fin n, weight[v.val].length ≤ B) (cb : ∀ i : Fin k, capacity[i.val].length ≤ B) :
    (splitCheck E roots weight capacity B).1 = true ↔
      ∃ x, SplitFeasible (fun v u => E[v.val][u.val] = true) (fun i => roots[i.val])
        (fun v => value weight[v.val]) (fun i => value capacity[i.val]) x := by
  exact (matrixCheck_correct _ _ capacity B (splitInputs_bounds E roots weight B wb) cb).trans
    (splitInputs_feasible E roots weight capacity)

def splitInputBudget (n k : Nat) := rootMaskBudget n k +
  (2 * n * n * n + n * n * (VertexNetwork.essentialBudget n + 13) + 9 * n + 3) +
  (2 * n * n + n * (2 * k * k + 9 * k + 9) + 3) + (2 * n * n + 9 * n + 3) + 3

theorem splitInputs_cost (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (weight : Vector (List Bool) n) :
    (splitInputs E roots weight).2 ≤ splitInputBudget n k := by
  have hm := rootMask_cost roots
  have he := VertexNetwork.essentialTable_cost E (rootMask roots).1
  have ha := Costed.tabulate_cost n (fun v => Costed.tabulate k
    (fun i => ((VertexNetwork.essentialTable E (rootMask roots).1).1[v.val][roots[i.val].val], 3)))
    (2 * k * k + k * (3 + 6) + 3) (fun v => Costed.tabulate_cost k _ 3 (by intros; rfl))
  have hs := Costed.tabulate_cost n
    (fun v => (if (rootMask roots).1[v.val] then [] else weight[v.val], 3)) 3 (by intros; rfl)
  dsimp only [splitInputs, splitInputBudget]
  simp only [Nat.add_assoc, Nat.mul_comm k 9, Nat.mul_comm n 9] at ha hs
  norm_num only at ha hs ⊢
  simp only [Nat.add_assoc]
  omega

theorem splitCheck_cost (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (weight : Vector (List Bool) n) (capacity : Vector (List Bool) k) (B : Nat)
    (wb : ∀ v : Fin n, weight[v.val].length ≤ B) (cb : ∀ i : Fin k, capacity[i.val].length ≤ B) :
    (splitCheck E roots weight capacity B).2 ≤ splitInputBudget n k + matrixBudget n k B + 1 := by
  have hi := splitInputs_cost E roots weight
  have hm := matrixCheck_cost (splitInputs E roots weight).1.1 (splitInputs E roots weight).1.2
    capacity B (splitInputs_bounds E roots weight B wb) cb
  dsimp only [splitCheck]
  omega

end GyoriLovasz
