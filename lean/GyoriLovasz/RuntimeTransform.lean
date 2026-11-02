import GyoriLovasz.RuntimeReindex
import GyoriLovasz.RuntimeRootMatching

namespace GyoriLovasz.WordInstance
open Binary

structure Input (n k : Nat) where
  graph : Vector (Vector Bool n) n
  roots : Vector (Fin n) k
  weight : Vector (List Bool) n
  capacity : Vector (List Bool) k

def relation (s : Input n k) (x y : Fin n) : Prop := s.graph[x.val][y.val] = true
def root (s : Input n k) (i : Fin k) := s.roots[i.val]
def weights (s : Input n k) (v : Fin n) := value s.weight[v.val]
def capacities (s : Input n k) (i : Fin k) := value s.capacity[i.val]
def Bounded (s : Input n k) (B : Nat) :=
  (∀ v : Fin n, s.weight[v.val].length ≤ B) ∧ (∀ i : Fin k, s.capacity[i.val].length ≤ B)

def contractGraph (E : Vector (Vector Bool n) n) (p t : Fin n) : Costed.Computation (Vector (Vector Bool n) n) :=
  Costed.tabulate₂ n (fun x y =>
    (decide (x ≠ p) && decide (y ≠ p) && (E[x.val][y.val] || (E[x.val][p.val] && decide (y = t))), 9))

theorem contractGraph_relation (E : Vector (Vector Bool n) n) (p t : Fin n) :
    (fun x y : Fin n => (contractGraph E p t).1[x.val][y.val] = true) =
      Contract (fun x y => E[x.val][y.val] = true) p t := by
  funext x y
  simp only [contractGraph, Costed.tabulate₂_value, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, Contract, and_assoc]

theorem contractGraph_cost (E : Vector (Vector Bool n) n) (p t : Fin n) :
    (contractGraph E p t).2 ≤ 2 * n * n * n + n * n * 17 + 9 * n + 3 :=
  Costed.tabulate₂_cost n _ 9 (by intros; rfl)

def removeGraph (E : Vector (Vector Bool n) n) (removed : Vector Bool n) : Costed.Computation (Vector (Vector Bool n) n) :=
  Costed.tabulate₂ n (fun x y => (E[x.val][y.val] && !removed[x.val] && !removed[y.val], 5))

theorem removeGraph_relation (E : Vector (Vector Bool n) n) (removed : Vector Bool n) :
    (fun x y : Fin n => (removeGraph E removed).1[x.val][y.val] = true) =
      RemoveVertices (fun x y => E[x.val][y.val] = true) (SaturationPrune.selectedSet removed) := by
  funext x y
  simp only [removeGraph, Costed.tabulate₂_value, Bool.and_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, RemoveVertices, SaturationPrune.mem_selectedSet, and_assoc]

theorem removeGraph_cost (E : Vector (Vector Bool n) n) (removed : Vector Bool n) :
    (removeGraph E removed).2 ≤ 2 * n * n * n + n * n * 13 + 9 * n + 3 :=
  Costed.tabulate₂_cost n _ 5 (by intros; rfl)

def subtractEntry (capacity : Vector (List Bool) k) (i j : Fin k) (amount : List Bool) : Costed.Computation (List Bool) :=
  if j = i then
    let result := subBorrow capacity[j.val] amount false
    (result.1.1, result.2 + 2)
  else (capacity[j.val], 2)

theorem subtractEntry_value (capacity : Vector (List Bool) k) (i j : Fin k) (amount : List Bool)
    (fits : value amount ≤ value capacity[i.val]) :
    value (subtractEntry capacity i j amount).1 = value capacity[j.val] - if j = i then value amount else 0 := by
  by_cases eq : j = i
  · subst j
    have h := (subBorrow_no_underflow capacity[i.val] amount false (by simpa using fits)).2
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
    simp only [subtractEntry, ↓reduceIte]
    omega
  · simp [subtractEntry, eq]

theorem subtractEntry_length (capacity : Vector (List Bool) k) (i j : Fin k) (amount : List Bool)
    (B : Nat) (cb : ∀ a : Fin k, capacity[a.val].length ≤ B) (ab : amount.length ≤ B) :
    (subtractEntry capacity i j amount).1.length ≤ B := by
  simp only [subtractEntry]
  split
  · rw [subBorrow_length]
    exact max_le (cb j) ab
  · exact cb j

theorem subtractEntry_cost (capacity : Vector (List Bool) k) (i j : Fin k) (amount : List Bool)
    (B : Nat) (cb : ∀ a : Fin k, capacity[a.val].length ≤ B) (ab : amount.length ≤ B) :
    (subtractEntry capacity i j amount).2 ≤ 9 * B + 4 := by
  have h := subBorrow_steps capacity[j.val] amount false
  have hj := cb j
  dsimp only [subtractEntry]
  split <;> omega

def subtractCapacity (capacity : Vector (List Bool) k) (i : Fin k) (amount : List Bool) :
    Costed.Computation (Vector (List Bool) k) := Costed.tabulate k (fun j => subtractEntry capacity i j amount)

theorem subtractCapacity_value (capacity : Vector (List Bool) k) (i j : Fin k) (amount : List Bool)
    (fits : value amount ≤ value capacity[i.val]) :
    value (subtractCapacity capacity i amount).1[j.val] = value capacity[j.val] - if j = i then value amount else 0 := by
  rw [subtractCapacity, Costed.tabulate_value]
  exact subtractEntry_value capacity i j amount fits

theorem subtractCapacity_cost (capacity : Vector (List Bool) k) (i : Fin k) (amount : List Bool)
    (B : Nat) (cb : ∀ a : Fin k, capacity[a.val].length ≤ B) (ab : amount.length ≤ B) :
    (subtractCapacity capacity i amount).2 ≤ 2 * k * k + k * (9 * B + 10) + 3 := by
  simpa only [subtractCapacity, Nat.add_assoc] using Costed.tabulate_cost k _ (9 * B + 4)
    (fun j => subtractEntry_cost capacity i j amount B cb ab)

/-- Project an already transformed graph and its data to retained vertices
and roots. All tables are materialized once. -/
def project (s : Input n k) (vertices : Vector (Fin n) m) (indices : Vector (Fin k) j)
    (reverse : Vector (Fin m) n) : Costed.Computation (Input m j) :=
  let graph := Costed.tabulate₂ m (fun x y => (s.graph[vertices[x.val].val][vertices[y.val].val], 3))
  let roots := Costed.tabulate j (fun a => (reverse[s.roots[indices[a.val].val].val], 3))
  let weight := Costed.tabulate m (fun x => (s.weight[vertices[x.val].val], 2))
  let capacity := Costed.tabulate j (fun a => (s.capacity[indices[a.val].val], 2))
  (⟨graph.1, roots.1, weight.1, capacity.1⟩, graph.2 + roots.2 + weight.2 + capacity.2 + 3)

theorem project_graph (s : Input n k) (vertices : Vector (Fin n) m) (indices : Vector (Fin k) j)
    (reverse : Vector (Fin m) n) (x y : Fin m) :
    relation (project s vertices indices reverse).1 x y = relation s vertices[x.val] vertices[y.val] := by
  simp only [relation, project, Costed.tabulate₂_value]

theorem project_root (s : Input n k) (vertices : Vector (Fin n) m) (indices : Vector (Fin k) j)
    (reverse : Vector (Fin m) n) (a : Fin j) :
    root (project s vertices indices reverse).1 a = reverse[(root s indices[a.val]).val] := by
  simp only [root, project, Costed.tabulate_value]

theorem project_weight (s : Input n k) (vertices : Vector (Fin n) m) (indices : Vector (Fin k) j)
    (reverse : Vector (Fin m) n) (x : Fin m) :
    weights (project s vertices indices reverse).1 x = weights s vertices[x.val] := by
  simp only [weights, project, Costed.tabulate_value]

theorem project_capacity (s : Input n k) (vertices : Vector (Fin n) m) (indices : Vector (Fin k) j)
    (reverse : Vector (Fin m) n) (a : Fin j) :
    capacities (project s vertices indices reverse).1 a = capacities s indices[a.val] := by
  simp only [capacities, project, Costed.tabulate_value]

theorem project_bounds (s : Input n k) (vertices : Vector (Fin n) m) (indices : Vector (Fin k) j)
    (reverse : Vector (Fin m) n) (B : Nat) (h : Bounded s B) :
    Bounded (project s vertices indices reverse).1 B := by
  constructor
  · intro x
    simpa only [project, Costed.tabulate_value] using h.1 vertices[x.val]
  · intro a
    simpa only [project, Costed.tabulate_value] using h.2 indices[a.val]

def projectBudget (m j : Nat) :=
  (2 * m * m * m + m * m * 11 + 9 * m + 3) + (2 * j * j + 9 * j + 3) +
    (2 * m * m + 8 * m + 3) + (2 * j * j + 8 * j + 3) + 3

theorem project_cost (s : Input n k) (vertices : Vector (Fin n) m) (indices : Vector (Fin k) j)
    (reverse : Vector (Fin m) n) : (project s vertices indices reverse).2 ≤ projectBudget m j := by
  have hg := Costed.tabulate₂_cost m (fun x y => (s.graph[vertices[x.val].val][vertices[y.val].val], 3)) 3 (by intros; rfl)
  have hr := Costed.tabulate_cost j (fun a => (reverse[s.roots[indices[a.val].val].val], 3)) 3 (by intros; rfl)
  have hw := Costed.tabulate_cost m (fun x => (s.weight[vertices[x.val].val], 2)) 2 (by intros; rfl)
  have hc := Costed.tabulate_cost j (fun a => (s.capacity[indices[a.val].val], 2)) 2 (by intros; rfl)
  dsimp only [project, projectBudget]
  norm_num only at hg hr hw hc
  simp only [Nat.mul_comm j 9, Nat.mul_comm m 8, Nat.mul_comm j 8] at hr hw hc
  omega

end GyoriLovasz.WordInstance
