import GyoriLovasz.RuntimeSplitCheck
import GyoriLovasz.RuntimeReduction
import GyoriLovasz.RuntimeIrreducible

namespace GyoriLovasz.SafeEdges
open Binary

abbrev Graph (n : Nat) := Vector (Vector Bool n) n
def relation (E : Graph n) (u v : Fin n) := E[u.val][v.val] = true

/-- Finite-index comparisons are reference-RAM operations; weights are handled
by the binary-word routines in `splitCheck`. -/
def erase (E : Graph n) (p q : Fin n) : Costed.Computation (Graph n) :=
  Costed.tabulate₂ n (fun u v => (E[u.val][v.val] && !(decide (u = p) && decide (v = q)), 5))

theorem erase_relation (E : Graph n) (p q : Fin n) :
    relation (erase E p q).1 = DeleteEdge (relation E) p q := by
  funext u v
  simp [relation, erase, Costed.tabulate₂_value, DeleteEdge]
  tauto

def eraseBudget (n : Nat) := 2 * n * n * n + n * n * 13 + 9 * n + 3

theorem erase_cost (E : Graph n) (p q : Fin n) : (erase E p q).2 ≤ eraseBudget n :=
  Costed.tabulate₂_cost n _ 5 (by intros; rfl)

def feasible (E : Graph n) (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) : Prop :=
  ∃ x, SplitFeasible (relation E) (fun i => roots[i.val])
    (fun v => value weight[v.val]) (fun i => value capacity[i.val]) x

def test (E : Graph n) (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) (B : Nat) (a : Fin n × Fin n) : Bool × Nat :=
  if E[a.1.val][a.2.val] then
    let next := erase E a.1 a.2
    let checked := splitCheck next.1 roots weight capacity B
    (checked.1, next.2 + checked.2 + 3)
  else (false, 3)

theorem test_correct (E : Graph n) (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) (B : Nat)
    (wb : ∀ v : Fin n, weight[v.val].length ≤ B) (cb : ∀ i : Fin k, capacity[i.val].length ≤ B)
    (a : Fin n × Fin n) :
    (test E roots weight capacity B a).1 = true ↔
      relation E a.1 a.2 ∧ feasible (erase E a.1 a.2).1 roots weight capacity := by
  by_cases he : E[a.1.val][a.2.val] = true
  · simpa only [test, he, ↓reduceIte, relation, true_and, feasible] using
      splitCheck_correct (erase E a.1 a.2).1 roots weight capacity B wb cb
  · simp only [test, he, ↓reduceIte, relation, false_and, Bool.false_eq_true]

def testBudget (n k B : Nat) := eraseBudget n + splitInputBudget n k + TransportNetwork.matrixBudget n k B + 4

theorem test_cost (E : Graph n) (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) (B : Nat)
    (wb : ∀ v : Fin n, weight[v.val].length ≤ B) (cb : ∀ i : Fin k, capacity[i.val].length ≤ B)
    (a : Fin n × Fin n) : (test E roots weight capacity B a).2 ≤ testBudget n k B := by
  have he := erase_cost E a.1 a.2
  have hs := splitCheck_cost (erase E a.1 a.2).1 roots weight capacity B wb cb
  dsimp only [test, testBudget]
  split <;> omega

def choose (E : Graph n) (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) (B : Nat) : Costed.Computation (Option (Fin n × Fin n)) :=
  let pairs := Costed.enumeratePairs n
  let found := Costed.find (test E roots weight capacity B) pairs.1
  (found.1, pairs.2 + found.2 + 1)

theorem choose_some (E : Graph n) (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) (B : Nat)
    (wb : ∀ v : Fin n, weight[v.val].length ≤ B) (cb : ∀ i : Fin k, capacity[i.val].length ≤ B)
    (a : Fin n × Fin n) (h : (choose E roots weight capacity B).1 = some a) :
    relation E a.1 a.2 ∧ feasible (erase E a.1 a.2).1 roots weight capacity := by
  rw [choose, Costed.find_value] at h
  have yes := List.find?_some h
  exact (test_correct E roots weight capacity B wb cb a).mp yes

theorem choose_none (E : Graph n) (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) (B : Nat)
    (wb : ∀ v : Fin n, weight[v.val].length ≤ B) (cb : ∀ i : Fin k, capacity[i.val].length ≤ B)
    (h : (choose E roots weight capacity B).1 = none) :
    ∀ p q, relation E p q → ¬feasible (erase E p q).1 roots weight capacity := by
  rw [choose, Costed.find_value] at h
  intro p q edge good
  have mem : (p, q) ∈ (Costed.enumeratePairs n).1 := by
    simp [Costed.enumeratePairs_value]
  have no := List.find?_eq_none.mp h (p, q) mem
  have yes := (test_correct E roots weight capacity B wb cb (p, q)).mpr ⟨edge, good⟩
  simp [yes] at no

def chooseBudget (n k B : Nat) := 8 * n * n + 5 * n + 3 + n * n * (testBudget n k B + 3) + 2

theorem choose_cost (E : Graph n) (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) (B : Nat)
    (wb : ∀ v : Fin n, weight[v.val].length ≤ B) (cb : ∀ i : Fin k, capacity[i.val].length ≤ B) :
    (choose E roots weight capacity B).2 ≤ chooseBudget n k B := by
  have hp := Costed.enumeratePairs_cost n
  have hf := Costed.find_cost (test E roots weight capacity B) (Costed.enumeratePairs n).1
    (testBudget n k B) (fun a _ => test_cost E roots weight capacity B wb cb a)
  have len : (Costed.enumeratePairs n).1.length = n * n := by
    rw [Costed.enumeratePairs_ofFn]
    simp
  rw [len] at hf
  dsimp only [choose, chooseBudget]
  omega

def run (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) (B : Nat) : Nat → Graph n → Costed.Computation (Graph n)
  | 0, E => (E, 1)
  | fuel + 1, E =>
    let selected := choose E roots weight capacity B
    match selected.1 with
    | none => (E, selected.2 + 2)
    | some a =>
      let next := erase E a.1 a.2
      let result := run roots weight capacity B fuel next.1
      (result.1, selected.2 + next.2 + result.2 + 3)

theorem run_correct (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) (B : Nat)
    (wb : ∀ v : Fin n, weight[v.val].length ≤ B) (cb : ∀ i : Fin k, capacity[i.val].length ≤ B)
    (fuel : Nat) (E : Graph n) (enough : edgeCount (relation E) ≤ fuel)
    (initial : feasible E roots weight capacity) :
    let F := (run roots weight capacity B fuel E).1
    (∀ x y, relation F x y → relation E x y) ∧ feasible F roots weight capacity ∧
      ∀ p q, relation F p q → ¬feasible (erase F p q).1 roots weight capacity := by
  classical
  induction fuel generalizing E with
  | zero =>
    refine ⟨fun _ _ h => h, initial, ?_⟩
    intro p q edge
    have positive : 0 < edgeCount (relation E) := by
      apply Finset.card_pos.mpr
      exact ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_univ _, edge⟩⟩
    omega
  | succ fuel ih =>
    cases hs : (choose E roots weight capacity B).1 with
    | none =>
      simpa only [run, hs] using And.intro (fun x y (h : relation E x y) => h)
        (And.intro initial (choose_none E roots weight capacity B wb cb hs))
    | some a =>
      have step := choose_some E roots weight capacity B wb cb a hs
      have less : edgeCount (relation (erase E a.1 a.2).1) < edgeCount (relation E) := by
        rw [erase_relation]
        exact edgeCount_delete_lt step.1
      have result := ih (erase E a.1 a.2).1 (by omega) step.2
      simp only [run, hs]
      refine ⟨?_, result.2⟩
      intro x y h
      have he := result.1 x y h
      rw [erase_relation] at he
      exact he.1

theorem run_cost (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) (B : Nat)
    (wb : ∀ v : Fin n, weight[v.val].length ≤ B) (cb : ∀ i : Fin k, capacity[i.val].length ≤ B)
    (fuel : Nat) (E : Graph n) :
    (run roots weight capacity B fuel E).2 ≤ fuel * (chooseBudget n k B + eraseBudget n + 3) + 1 := by
  induction fuel generalizing E with
  | zero => simp [run]
  | succ fuel ih =>
    have hc := choose_cost E roots weight capacity B wb cb
    dsimp only [run]
    split
    · simp only [Nat.add_mul, Nat.one_mul]
      omega
    · rename_i a ha
      have he := erase_cost E a.1 a.2
      have hr := ih (erase E a.1 a.2).1
      simp only [Nat.add_mul, Nat.one_mul]
      omega

def reduce (E : Graph n) (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) (B : Nat) := run roots weight capacity B (n * n) E

theorem reduce_correct (E : Graph n) (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) (B : Nat)
    (wb : ∀ v : Fin n, weight[v.val].length ≤ B) (cb : ∀ i : Fin k, capacity[i.val].length ≤ B)
    (hk : 0 < k) (initial : feasible E roots weight capacity) :
    let F := (reduce E roots weight capacity B).1
    (∀ x y, relation F x y → relation E x y) ∧ feasible F roots weight capacity ∧
      ((∃ (i : Fin k) (p : Fin n), ¬RootSet (fun i => roots[i.val]) p ∧ relation F p roots[i.val] ∧
        (∀ y, relation F p y → y = roots[i.val])) ∨
      ¬∃ p : Fin k → Fin n, Function.Injective p ∧
        (∀ i, ¬RootSet (fun i => roots[i.val]) (p i)) ∧ (∀ i, relation F (p i) roots[i.val])) := by
  have h := run_correct roots weight capacity B wb cb (n * n) E (edgeCount_le_square _) initial
  refine ⟨h.1, h.2.1, weighted_irreducible hk h.2.1 ?_⟩
  intro p q edge good
  apply h.2.2 p q edge
  simpa only [feasible, erase_relation] using good

theorem reduce_cost (E : Graph n) (roots : Vector (Fin n) k) (weight : Vector (List Bool) n)
    (capacity : Vector (List Bool) k) (B : Nat)
    (wb : ∀ v : Fin n, weight[v.val].length ≤ B) (cb : ∀ i : Fin k, capacity[i.val].length ≤ B) :
    (reduce E roots weight capacity B).2 ≤ n * n * (chooseBudget n k B + eraseBudget n + 3) + 1 :=
  run_cost roots weight capacity B wb cb (n * n) E

end GyoriLovasz.SafeEdges
