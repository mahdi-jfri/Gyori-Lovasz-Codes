import GyoriLovasz.RuntimeShortestPaths
import Mathlib.Logic.Relation

namespace GyoriLovasz.ShortestPaths

def Tight (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat)
    (d : Fin n → Nat) (u v : Fin n) : Prop :=
  E u v = true ∧ d v = d u + cost u v

/-- Every distance strictly below the truncation bound has a tight path.
The perturbation argument also covers zero-cost edges. -/
theorem greatest_has_tight_path
    {E : Fin n → Fin n → Bool} {cost : Fin n → Fin n → Nat}
    {source : Fin n} {bound : Nat} {d : Fin n → Nat}
    (hd : Admissible E cost source bound d)
    (greatest : ∀ q, Admissible E cost source bound q → ∀ v, q v ≤ d v)
    (target : Fin n) (below : d target < bound) :
    Relation.ReflTransGen (Tight E cost d) source target := by
  classical
  let reachable := fun v => Relation.ReflTransGen (Tight E cost d) source v
  have start : reachable source := Relation.ReflTransGen.refl
  by_contra missing
  let q := fun v => if reachable v then d v else min bound (d v + 1)
  have qbound (v) : q v ≤ bound := by
    dsimp [q]
    split
    · exact hd.2.1 v
    · exact min_le_left _ _
  have qlower (v) : d v ≤ q v := by
    dsimp [q]
    split
    · exact le_rfl
    · exact le_min (hd.2.1 v) (by omega)
  have qupper (v) : q v ≤ d v + 1 := by
    dsimp [q]
    split
    · omega
    · exact min_le_right _ _
  have admissible : Admissible E cost source bound q := by
    refine ⟨?_, qbound, ?_⟩
    · simpa [q, start] using hd.1
    · intro u v edge
      have triangle := hd.2.2 u v edge
      by_cases rv : reachable v
      · have eq : q v = d v := if_pos rv
        rw [eq]
        exact triangle.trans (Nat.add_le_add_right (qlower u) _)
      · by_cases ru : reachable u
        · have slack : d v ≠ d u + cost u v := by
            intro tight
            exact rv (Relation.ReflTransGen.tail ru ⟨edge, tight⟩)
          have up := qupper v
          have low := qlower u
          omega
        · by_cases saturated : d u = bound
          · have up := qbound v
            have low := qlower u
            omega
          · have ub := hd.2.1 u
            have raised : q u = d u + 1 := by
              simp only [q, if_neg ru]
              exact min_eq_right (by omega)
            have up := qupper v
            omega
  have contradiction := greatest q admissible target
  have raised : q target = d target + 1 := by
    have notReach : ¬ reachable target := missing
    change (if reachable target then d target else min bound (d target + 1)) = _
    rw [if_neg notReach]
    exact min_eq_right (by omega)
  omega

theorem dijkstra_has_tight_path (E : Fin n → Fin n → Bool)
    (cost : Fin n → Fin n → Nat) (source target : Fin n) (bound : Nat)
    (below : get (run E cost n (initialState source bound)) target < bound) :
    Relation.ReflTransGen
      (Tight E cost (get (run E cost n (initialState source bound)))) source target := by
  have correct := dijkstra_correct E cost source bound
  exact greatest_has_tight_path correct.1 correct.2 target below

end GyoriLovasz.ShortestPaths
