import GyoriLovasz.RuntimeWordEssential

namespace GyoriLovasz.VertexNetwork

def essentialCell (E : Vector (Vector Bool n) n) (T : Vector Bool n) (v t : Fin n) : Bool × Nat :=
  if !T[v.val] && T[t.val] then
    let result := essentialWords E T v t
    (result.1, result.2 + 5)
  else (false, 5)

theorem essentialCell_correct (E : Vector (Vector Bool n) n) (T : Vector Bool n) (v t : Fin n) :
    (essentialCell E T v t).1 = true ↔
      ∃ h : ¬T[v.val] = true, T[t.val] = true ∧
        Essential (fun x y => E[x.val][y.val] = true) (fun x => T[x.val] = true) v h t := by
  by_cases hv : T[v.val] = true
  · have cell : (essentialCell E T v t).1 = false := by simp [essentialCell, hv]
    rw [cell]
    constructor
    · intro h; contradiction
    · rintro ⟨h, _⟩; exact False.elim (h hv)
  · have hvf : T[v.val] = false := Bool.eq_false_iff.mpr hv
    by_cases ht : T[t.val] = true
    · have cell : (essentialCell E T v t).1 = (essentialWords E T v t).1 := by
        simp [essentialCell, hvf, ht]
      rw [cell]
      constructor
      · intro h; exact ⟨hv, ht, (essentialWords_correct E T v t hvf ht).mp h⟩
      · rintro ⟨_, _, h⟩; exact (essentialWords_correct E T v t hvf ht).mpr h
    · have cell : (essentialCell E T v t).1 = false := by simp [essentialCell, hvf, ht]
      rw [cell]
      constructor
      · intro h; contradiction
      · rintro ⟨_, h, _⟩; exact False.elim (ht h)

theorem essentialCell_cost (E : Vector (Vector Bool n) n) (T : Vector Bool n) (v t : Fin n) :
    (essentialCell E T v t).2 ≤ essentialBudget n + 5 := by
  have h := essentialWords_cost E T v t
  dsimp only [essentialCell]
  split <;> omega

def essentialTable (E : Vector (Vector Bool n) n) (T : Vector Bool n) :
    Costed.Computation (Vector (Vector Bool n) n) := Costed.tabulate₂ n (essentialCell E T)

theorem essentialTable_correct (E : Vector (Vector Bool n) n) (T : Vector Bool n) (v t : Fin n) :
    (essentialTable E T).1[v.val][t.val] = true ↔
      ∃ h : ¬T[v.val] = true, T[t.val] = true ∧
        Essential (fun x y => E[x.val][y.val] = true) (fun x => T[x.val] = true) v h t := by
  rw [essentialTable, Costed.tabulate₂_value]
  exact essentialCell_correct E T v t

theorem essentialTable_cost (E : Vector (Vector Bool n) n) (T : Vector Bool n) :
    (essentialTable E T).2 ≤ 2 * n * n * n + n * n * (essentialBudget n + 13) + 9 * n + 3 := by
  have h := Costed.tabulate₂_cost n (essentialCell E T) (essentialBudget n + 5) (essentialCell_cost E T)
  simpa only [essentialTable, Nat.add_assoc] using h

end GyoriLovasz.VertexNetwork
