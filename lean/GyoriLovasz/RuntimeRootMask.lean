import GyoriLovasz.RuntimeWordCodes
import GyoriLovasz.InputBridge

namespace GyoriLovasz

def rootMask (roots : Vector (Fin n) k) : Costed.Computation (Vector Bool n) :=
  let codes := Binary.wordCodes n
  let indices := Costed.enumerateIndices k
  let vertices := Costed.map (fun i : Fin k => (roots[i.val], 1)) indices.1
  let result := Costed.tabulate n (fun v => WordShortest.memberVertex codes.1 v vertices.1)
  (result.1, codes.2 + indices.2 + vertices.2 + result.2 + 2)

theorem rootMask_correct (roots : Vector (Fin n) k) (v : Fin n) :
    (rootMask roots).1[v.val] = true ↔ RootSet (fun i => roots[i.val]) v := by
  simp only [rootMask, Costed.tabulate_value, WordShortest.memberVertex_value _
    (Binary.wordCodes_correct n), Costed.map_value, Costed.enumerateIndices_value,
    decide_eq_true_eq, List.mem_map, List.mem_finRange, true_and, RootSet]

def rootMaskBudget (n k : Nat) :=
  (7 * n * n + 6 * n + 2) + (2 * k * k + 2 * k + 1) + (4 * k + 1) +
    (2 * n * n + n * (k * (9 * n + 7) + 8) + 3) + 2

theorem rootMask_cost (roots : Vector (Fin n) k) :
    (rootMask roots).2 ≤ rootMaskBudget n k := by
  have hc := Binary.wordCodes_cost n
  have hi := Costed.enumerateIndices_cost k
  have hm := Costed.map_cost (fun i : Fin k => (roots[i.val], 1))
    (Costed.enumerateIndices k).1 1 (by intros; rfl)
  have ht := Costed.tabulate_cost n
    (fun v => WordShortest.memberVertex (Binary.wordCodes n).1 v
      (Costed.map (fun i : Fin k => (roots[i.val], 1)) (Costed.enumerateIndices k).1).1)
    (k * (9 * n + 7) + 2) (by
      intro v
      have h := WordShortest.memberVertex_cost (Binary.wordCodes n).1 n (Binary.wordCodes_length n) v
        (Costed.map (fun i : Fin k => (roots[i.val], 1)) (Costed.enumerateIndices k).1).1
      simpa only [Costed.map_value, List.length_map, Costed.enumerateIndices_value,
        List.length_finRange] using h)
  simp only [Costed.enumerateIndices_value, List.length_finRange] at hm
  dsimp only [rootMask, rootMaskBudget]
  simp only [Costed.enumerateIndices_value, Nat.add_assoc] at hm ht ⊢
  norm_num only at hm ht ⊢
  omega

end GyoriLovasz

