import GyoriLovasz.RuntimeCostedTable
import GyoriLovasz.ActiveReindex

namespace GyoriLovasz.ComputedReindex

def locate (vertices : Vector (Fin n) m) (v : Fin n) : Costed.Computation (Option (Fin m)) :=
  let indices := Costed.enumerateIndices m
  let found := Costed.find (fun j => (decide (vertices[j.val] = v), 2)) indices.1
  (found.1, indices.2 + found.2 + 1)

theorem locate_some (vertices : Vector (Fin n) m) (v : Fin n) (j : Fin m)
    (h : (locate vertices v).1 = some j) : vertices[j.val] = v := by
  rw [locate, Costed.find_value] at h
  have yes := List.find?_some h
  exact of_decide_eq_true yes

theorem locate_exists (vertices : Vector (Fin n) m) (v : Fin n)
    (h : ∃ j : Fin m, vertices[j.val] = v) : ∃ j, (locate vertices v).1 = some j := by
  cases hs : (locate vertices v).1 with
  | some j => exact ⟨j, rfl⟩
  | none =>
    rw [locate, Costed.find_value] at hs
    obtain ⟨j, hj⟩ := h
    have no := List.find?_eq_none.mp hs j (by simp [Costed.enumerateIndices_value])
    simp [hj] at no

theorem locate_cost (vertices : Vector (Fin n) m) (v : Fin n) :
    (locate vertices v).2 ≤ 2 * m * m + 7 * m + 3 := by
  have hi := Costed.enumerateIndices_cost m
  have hf := Costed.find_cost (fun j : Fin m => (decide (vertices[j.val] = v), 2))
    (Costed.enumerateIndices m).1 2 (by intros; rfl)
  simp only [Costed.enumerateIndices_value, List.length_finRange] at hf
  dsimp only [locate]
  simp only [Costed.enumerateIndices_value]
  omega

def inverse (vertices : Vector (Fin n) m) (fallback : Fin m) : Costed.Computation (Vector (Fin m) n) :=
  Costed.tabulate n (fun v => let found := locate vertices v; (found.1.getD fallback, found.2 + 1))

theorem inverse_retract (vertices : Vector (Fin n) m) (fallback : Fin m) (v : Fin n)
    (h : ∃ j : Fin m, vertices[j.val] = v) :
    vertices[(inverse vertices fallback).1[v.val].val] = v := by
  obtain ⟨j, hj⟩ := locate_exists vertices v h
  simpa only [inverse, Costed.tabulate_value, hj, Option.getD_some] using locate_some vertices v j hj

theorem inverse_left (vertices : Vector (Fin n) m) (fallback : Fin m)
    (inj : Function.Injective (fun j : Fin m => vertices[j.val])) (j : Fin m) :
    (inverse vertices fallback).1[vertices[j.val].val] = j := by
  apply inj
  exact inverse_retract vertices fallback vertices[j.val] ⟨j, rfl⟩

theorem inverse_cost (vertices : Vector (Fin n) m) (fallback : Fin m) :
    (inverse vertices fallback).2 ≤ 2 * n * n + n * (2 * m * m + 7 * m + 10) + 3 := by
  have h := Costed.tabulate_cost n
    (fun v => let found := locate vertices v; (found.1.getD fallback, found.2 + 1))
    (2 * m * m + 7 * m + 4) (by intro v; have h := locate_cost vertices v; dsimp only; omega)
  simpa only [inverse, Nat.add_assoc] using h

theorem enumeration (vertices : Vector (Fin n) m) :
    (List.finRange m).map (fun j : Fin m => vertices[j.val]) = vertices.toList := by
  rw [← List.ofFn_eq_map, ← Vector.toList_ofFn]
  apply congrArg (fun v : Vector (Fin n) m => v.toList)
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]

theorem graphReindex (vertices : Vector (Fin n) m) (fallback : Fin m)
    (inj : Function.Injective (fun j : Fin m => vertices[j.val]))
    (E : Fin n → Fin n → Prop) (T : Fin n → Prop)
    (edges : ∀ x y, E x y → x ∈ vertices.toList ∧ y ∈ vertices.toList)
    (terminals : ∀ x, T x → x ∈ vertices.toList) :
    GraphReindex vertices.toList (List.finRange m) E T
      (fun j => vertices[j.val]) (fun v => (inverse vertices fallback).1[v.val]) := by
  refine ⟨mem_finRange, inverse_left vertices fallback inj, ?_, ?_, edges, terminals⟩
  · intro v hv
    apply inverse_retract
    rw [← enumeration vertices] at hv
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hv
    exact ⟨j, hj⟩
  · rw [enumeration]

def retain (selected : Vector Bool n) : Costed.Computation (List (Fin n)) :=
  let indices := Costed.enumerateIndices n
  let result := Costed.filter (fun v => (selected[v.val], 1)) indices.1
  (result.1, indices.2 + result.2 + 1)

theorem retain_value (selected : Vector Bool n) :
    (retain selected).1 = (List.finRange n).filter (fun v => selected[v.val]) := by
  simp only [retain, Costed.filter_value, Costed.enumerateIndices_value]

theorem retain_nodup (selected : Vector Bool n) : (retain selected).1.Nodup := by
  rw [retain_value]
  exact (List.nodup_finRange n).filter _

theorem retain_cost (selected : Vector Bool n) : (retain selected).2 ≤ 2 * n * n + 6 * n + 3 := by
  have hi := Costed.enumerateIndices_cost n
  have hf := Costed.filter_cost (fun v : Fin n => (selected[v.val], 1)) (Costed.enumerateIndices n).1 1
    (by intros; rfl)
  simp only [Costed.enumerateIndices_value, List.length_finRange] at hf
  dsimp only [retain]
  simp only [Costed.enumerateIndices_value]
  omega

/-- The list is converted once to an indexed vector, charging a write per
retained vertex. The dependent length is the actual retained list length. -/
def active (selected : Vector Bool n) : Costed.Computation ((m : Nat) × Vector (Fin n) m) :=
  let kept := retain selected
  (⟨kept.1.length, ⟨kept.1.toArray, by simp⟩⟩, kept.2 + kept.1.length + 1)

theorem active_list (selected : Vector Bool n) : (active selected).1.2.toList = (retain selected).1 := by
  simp [active]

theorem active_cost (selected : Vector Bool n) : (active selected).2 ≤ 2 * n * n + 7 * n + 4 := by
  have h := retain_cost selected
  have len : (retain selected).1.length ≤ n := by
    rw [retain_value]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  dsimp only [active]
  omega

end GyoriLovasz.ComputedReindex
