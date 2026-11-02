import GyoriLovasz.RuntimeSafeEdges
import GyoriLovasz.RuntimeRootMask

namespace GyoriLovasz

def soleCell (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (mask : Vector Bool n) (a : Fin k × Fin n) : Bool × Nat :=
  let indices := Costed.enumerateIndices n
  let other := Costed.find (fun y => (E[a.2.val][y.val] && decide (y ≠ roots[a.1.val]), 4)) indices.1
  (!mask[a.2.val] && E[a.2.val][roots[a.1.val].val] && other.1.isNone, indices.2 + other.2 + 5)

theorem soleCell_correct (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (a : Fin k × Fin n) : (soleCell E roots (rootMask roots).1 a).1 = true ↔
    ¬RootSet (fun i => roots[i.val]) a.2 ∧ E[a.2.val][roots[a.1.val].val] = true ∧
      ∀ y : Fin n, E[a.2.val][y.val] = true → y = roots[a.1.val] := by
  simp only [soleCell, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
    Costed.find_value, Option.isNone_iff_eq_none, List.find?_eq_none]
  constructor
  · rintro ⟨⟨nt, edge⟩, other⟩
    refine ⟨fun h => nt ((rootMask_correct roots _).mpr h), edge, ?_⟩
    intro y hy
    have no := other y (by simp [Costed.enumerateIndices_value])
    simpa [hy] using no
  · rintro ⟨nt, edge, sole⟩
    refine ⟨⟨fun h => nt ((rootMask_correct roots _).mp h), edge⟩, ?_⟩
    intro y _
    by_cases hy : E[a.2.val][y.val] = true
    · simp [hy, sole y hy]
    · simp [hy]

theorem soleCell_cost (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (mask : Vector Bool n) (a : Fin k × Fin n) :
    (soleCell E roots mask a).2 ≤ 2 * n * n + 9 * n + 7 := by
  have hi := Costed.enumerateIndices_cost n
  have hf := Costed.find_cost (fun y : Fin n => (E[a.2.val][y.val] && decide (y ≠ roots[a.1.val]), 4))
    (Costed.enumerateIndices n).1 4 (by intros; rfl)
  simp only [Costed.enumerateIndices_value, List.length_finRange] at hf
  dsimp only [soleCell]
  simp only [Costed.enumerateIndices_value]
  omega

def findSole (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k) :
    Costed.Computation (Option (Fin k × Fin n)) :=
  let mask := rootMask roots
  let left := Costed.enumerateIndices k
  let right := Costed.enumerateIndices n
  let pairs := Costed.pairs left.1 right.1
  let result := Costed.find (soleCell E roots mask.1) pairs.1
  (result.1, mask.2 + left.2 + right.2 + pairs.2 + result.2 + 1)

theorem findSole_some (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (a : Fin k × Fin n) (h : (findSole E roots).1 = some a) :
    ¬RootSet (fun i => roots[i.val]) a.2 ∧ E[a.2.val][roots[a.1.val].val] = true ∧
      ∀ y : Fin n, E[a.2.val][y.val] = true → y = roots[a.1.val] := by
  rw [findSole, Costed.find_value] at h
  have yes := List.find?_some h
  exact (soleCell_correct E roots a).mp yes

theorem findSole_none (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (h : (findSole E roots).1 = none) :
    ¬∃ (i : Fin k) (p : Fin n), ¬RootSet (fun i => roots[i.val]) p ∧ E[p.val][roots[i.val].val] = true ∧
      ∀ y : Fin n, E[p.val][y.val] = true → y = roots[i.val] := by
  rw [findSole, Costed.find_value] at h
  rintro ⟨i, p, nt, edge, sole⟩
  have mem : (i, p) ∈ (Costed.pairs (Costed.enumerateIndices k).1 (Costed.enumerateIndices n).1).1 := by
    simp [Costed.pairs_value, Costed.enumerateIndices_value]
  have no := List.find?_eq_none.mp h (i, p) mem
  have yes := (soleCell_correct E roots (i, p)).mpr ⟨nt, edge, sole⟩
  simp [yes] at no

def soleBudget (n k : Nat) := rootMaskBudget n k + (2 * k * k + 2 * k + 1) +
  (2 * n * n + 2 * n + 1) + (k * (6 * n + 3) + 1) + k * n * (2 * n * n + 9 * n + 10) + 2

theorem findSole_cost (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k) :
    (findSole E roots).2 ≤ soleBudget n k := by
  have hm := rootMask_cost roots
  have hl := Costed.enumerateIndices_cost k
  have hr := Costed.enumerateIndices_cost n
  have hp := Costed.pairs_cost (Costed.enumerateIndices k).1 (Costed.enumerateIndices n).1
  have hf := Costed.find_cost (soleCell E roots (rootMask roots).1)
    (Costed.pairs (Costed.enumerateIndices k).1 (Costed.enumerateIndices n).1).1
    (2 * n * n + 9 * n + 7) (fun a _ => soleCell_cost E roots (rootMask roots).1 a)
  have len : (Costed.pairs (Costed.enumerateIndices k).1 (Costed.enumerateIndices n).1).1.length = k * n := by
    simp [Costed.pairs_value, Costed.enumerateIndices_value, List.length_flatMap]
  rw [len] at hf
  simp only [Costed.enumerateIndices_value, List.length_finRange] at hp
  dsimp only [findSole, soleBudget]
  simp only [Costed.enumerateIndices_value, Nat.add_assoc] at hp hf ⊢
  norm_num only at hf
  omega

end GyoriLovasz
