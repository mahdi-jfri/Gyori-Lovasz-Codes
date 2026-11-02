import GyoriLovasz.RuntimeVertexNetwork

namespace GyoriLovasz.Costed

theorem enumeratePairs_ofFn (n : Nat) :
    (enumeratePairs n).1 = List.ofFn (fun a : Fin (n * n) => finProdFinEquiv.symm a) := by
  rw [enumeratePairs_value, List.ofFn_mul]
  simp only [List.finRange, List.flatMap_def, List.map_ofFn, Function.comp_def]
  congr 1
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  have hi : u.val * n + v.val < n * n := by
    have h := (finProdFinEquiv (u, v)).isLt
    simpa [finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using h
  have h : (⟨u.val * n + v.val, hi⟩ : Fin (n * n)) = finProdFinEquiv (u, v) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [h, Equiv.symm_apply_apply]

def pairTable (n : Nat) : Computation (Vector (Fin n × Fin n) (n * n)) :=
  let es := enumeratePairs n
  (⟨es.1.toArray, by simp [es, enumeratePairs_ofFn]⟩, es.2 + n * n + 1)

theorem pairTable_value (n : Nat) (e : Fin (n * n)) :
    (pairTable n).1[e.val] = finProdFinEquiv.symm e := by
  simp [pairTable, enumeratePairs_ofFn]

theorem pairTable_cost (n : Nat) : (pairTable n).2 = 9 * n * n + 5 * n + 4 := by
  simp only [pairTable, enumeratePairs_cost]
  ring

theorem rectangle_ofFn (l r : Nat) :
    (List.finRange l).flatMap (fun u => (List.finRange r).map (u, ·)) =
      List.ofFn (fun a : Fin (l * r) => finProdFinEquiv.symm a) := by
  rw [List.ofFn_mul]
  simp only [List.finRange, List.flatMap_def, List.map_ofFn, Function.comp_def]
  congr 1
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  have hi : u.val * r + v.val < l * r := by
    have h := (finProdFinEquiv (u, v)).isLt
    simpa [finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using h
  have h : (⟨u.val * r + v.val, hi⟩ : Fin (l * r)) = finProdFinEquiv (u, v) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [h, Equiv.symm_apply_apply]

def pairTableRect (l r : Nat) : Computation (Vector (Fin l × Fin r) (l * r)) :=
  let rows := enumerateIndices l
  let cols := enumerateIndices r
  let generated := pairs rows.1 cols.1
  (⟨generated.1.toArray, by simp [generated, rows, cols, pairs_value, enumerateIndices_value, rectangle_ofFn]⟩,
    rows.2 + cols.2 + generated.2 + l * r + 2)

theorem pairTableRect_value (l r : Nat) (e : Fin (l * r)) :
    (pairTableRect l r).1[e.val] = finProdFinEquiv.symm e := by
  simp [pairTableRect, pairs_value, enumerateIndices_value, rectangle_ofFn]

theorem pairTableRect_cost (l r : Nat) :
    (pairTableRect l r).2 = 2 * l * l + 2 * r * r + 7 * l * r + 5 * l + 2 * r + 5 := by
  simp only [pairTableRect, enumerateIndices_cost, pairs_cost, enumerateIndices_value, List.length_finRange]
  ring

end GyoriLovasz.Costed
