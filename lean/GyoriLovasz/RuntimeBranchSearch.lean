import GyoriLovasz.RuntimeContractStep

namespace GyoriLovasz.WordInstance
open Binary

def nonrootFind (roots : Vector (Fin n) k) : Costed.Computation (Option (Fin n)) :=
  let mask := rootMask roots
  let indices := Costed.enumerateIndices n
  let found := Costed.find (fun v => (!mask.1[v.val], 2)) indices.1
  (found.1, mask.2 + indices.2 + found.2 + 1)

theorem nonrootFind_some (roots : Vector (Fin n) k) (v : Fin n) (h : (nonrootFind roots).1 = some v) :
    ¬RootSet (fun i => roots[i.val]) v := by
  rw [nonrootFind, Costed.find_value] at h
  have yes := List.find?_some h
  have no : (rootMask roots).1[v.val] ≠ true := by simpa only [Bool.not_eq_true', Bool.eq_false_iff] using yes
  exact fun ht => no ((rootMask_correct roots v).mpr ht)

theorem nonrootFind_none (roots : Vector (Fin n) k) (h : (nonrootFind roots).1 = none) :
    ∀ v, RootSet (fun i => roots[i.val]) v := by
  rw [nonrootFind, Costed.find_value] at h
  intro v
  have no := List.find?_eq_none.mp h v (by simp [Costed.enumerateIndices_value])
  apply (rootMask_correct roots v).mp
  simpa using no

theorem nonrootFind_cost (roots : Vector (Fin n) k) :
    (nonrootFind roots).2 ≤ rootMaskBudget n k + 2 * n * n + 7 * n + 3 := by
  have hm := rootMask_cost roots
  have hi := Costed.enumerateIndices_cost n
  have hf := Costed.find_cost (fun v : Fin n => (!(rootMask roots).1[v.val], 2))
    (Costed.enumerateIndices n).1 2 (by intros; rfl)
  simp only [Costed.enumerateIndices_value, List.length_finRange] at hf
  dsimp only [nonrootFind]
  simp only [Costed.enumerateIndices_value]
  omega

def zeroWord (word : List Bool) : Bool × Nat :=
  let cmp := compareWords [] word
  (cmp.1.2, cmp.2 + 2)

theorem zeroWord_correct (word : List Bool) : (zeroWord word).1 = true ↔ value word = 0 := by
  simpa only [zeroWord, value, eq_comm] using (compareWords_correct [] word).2

theorem zeroWord_cost (word : List Bool) (B : Nat) (bound : word.length ≤ B) :
    (zeroWord word).2 ≤ 9 * B + 4 := by
  have h := compareWords_steps [] word
  simp only [List.length_nil, Nat.zero_max] at h
  dsimp only [zeroWord]
  omega

def zeroFind (capacity : Vector (List Bool) k) : Costed.Computation (Option (Fin k)) :=
  let indices := Costed.enumerateIndices k
  let found := Costed.find (fun i => zeroWord capacity[i.val]) indices.1
  (found.1, indices.2 + found.2 + 1)

theorem zeroFind_some (capacity : Vector (List Bool) k) (i : Fin k) (h : (zeroFind capacity).1 = some i) :
    value capacity[i.val] = 0 := by
  rw [zeroFind, Costed.find_value] at h
  have yes := List.find?_some h
  exact (zeroWord_correct _).mp yes

theorem zeroFind_none (capacity : Vector (List Bool) k) (h : (zeroFind capacity).1 = none) :
    ∀ i : Fin k, 0 < value capacity[i.val] := by
  rw [zeroFind, Costed.find_value] at h
  intro i
  have no := List.find?_eq_none.mp h i (by simp [Costed.enumerateIndices_value])
  have ne : value capacity[i.val] ≠ 0 := by
    intro hz
    have yes := (zeroWord_correct _).mpr hz
    simp [yes] at no
  omega

theorem zeroFind_cost (capacity : Vector (List Bool) k) (B : Nat)
    (bound : ∀ i : Fin k, capacity[i.val].length ≤ B) :
    (zeroFind capacity).2 ≤ 2 * k * k + 2 * k + k * (9 * B + 7) + 3 := by
  have hi := Costed.enumerateIndices_cost k
  have hf := Costed.find_cost (fun i : Fin k => zeroWord capacity[i.val]) (Costed.enumerateIndices k).1
    (9 * B + 4) (fun i _ => zeroWord_cost _ B (bound i))
  simp only [Costed.enumerateIndices_value, List.length_finRange, Nat.add_assoc] at hf
  norm_num only at hf
  dsimp only [zeroFind]
  simp only [Costed.enumerateIndices_value]
  omega

theorem valid_nonroot_dimensions (s : Input n k) (bound : Nat) (h : Valid s bound)
    (v : Fin n) (nt : ¬RootSet (root s) v) : 1 < n ∧ ∃ j : Fin k, 0 < capacities s j := by
  obtain ⟨x, hx⟩ := h.split
  obtain ⟨j, hj⟩ := weighted_positive_root hx nt (h.weightBounds v nt).1
  refine ⟨?_, j, hj⟩
  by_contra hn
  have eq : root s j = v := Fin.ext (by have h1 := (root s j).isLt; have h2 := v.isLt; omega)
  exact nt ⟨j, eq⟩

theorem valid_zero_root_dimensions (s : Input n k) (bound : Nat) (h : Valid s bound)
    (v : Fin n) (nt : ¬RootSet (root s) v) (i : Fin k) (zero : capacities s i = 0) : 1 < k := by
  obtain ⟨_, j, hj⟩ := valid_nonroot_dimensions s bound h v nt
  by_contra hn
  have eq : i = j := Fin.ext (by have h1 := i.isLt; have h2 := j.isLt; omega)
  rw [← eq, zero] at hj
  omega

end GyoriLovasz.WordInstance
