import GyoriLovasz.RuntimeWordPath

namespace GyoriLovasz.WordRoute
open Binary WordShortest

def tightCell (G : Graph n) (d : Vector (List Bool) n) (u v : Fin n) : Bool × Nat :=
  let sum := addCarry d[u.val] G.cost[u.val][v.val] false
  let cmp := compareWords d[v.val] sum.1
  ((edge G u v) && cmp.1.2, sum.2 + cmp.2 + 8)

theorem tightCell_value (G : Graph n) (d : Vector (List Bool) n) (u v : Fin n) :
    (tightCell G d u v).1 =
      PathSearch.tightEdges (edge G) (weight G) (fun v => value d[v.val]) u v := by
  apply Bool.eq_iff_iff.mpr
  simp [tightCell, PathSearch.tightEdges, (compareWords_correct _ _).2,
    addCarry_correct, weight]

theorem tightCell_cost (G : Graph n) (d : Vector (List Bool) n) (B : Nat)
    (db : ∀ v : Fin n, d[v.val].length ≤ B)
    (wb : ∀ u v : Fin n, G.cost[u.val][v.val].length ≤ B) (u v : Fin n) :
    (tightCell G d u v).2 ≤ 16 * B + 21 := by
  have hu := db u
  have hv := db v
  have hw := wb u v
  have hs := addCarry_length d[u.val] G.cost[u.val][v.val] false
  simp only [tightCell, addCarry_steps, compareWords_steps]
  omega

def tightGraph (G : Graph n) (d : Vector (List Bool) n) : Costed.Computation (Graph n) :=
  let table := Costed.tabulate₂ n (tightCell G d)
  (⟨table.1, G.cost⟩, table.2 + 1)

theorem tightGraph_value (G : Graph n) (d : Vector (List Bool) n) :
    edge (tightGraph G d).1 =
      PathSearch.tightEdges (edge G) (weight G) (fun v => value d[v.val]) := by
  funext u v
  simp only [edge, tightGraph, Costed.tabulate₂_value]
  exact tightCell_value G d u v

theorem tightGraph_cost (G : Graph n) (d : Vector (List Bool) n) (B : Nat)
    (db : ∀ v : Fin n, d[v.val].length ≤ B)
    (wb : ∀ u v : Fin n, G.cost[u.val][v.val].length ≤ B) :
    (tightGraph G d).2 ≤ 2 * n * n * n + n * n * (16 * B + 29) + 9 * n + 4 := by
  have h := Costed.tabulate₂_cost n (tightCell G d) (16 * B + 21)
    (tightCell_cost G d B db wb)
  have eq : 16 * B + 21 + 8 = 16 * B + 29 := by omega
  rw [eq] at h
  dsimp only [tightGraph]
  omega

def shortestRoute (G : Graph n) (codes : Vector (List Bool) n)
    (source target : Fin n) (bound : List Bool) : Costed.Computation (Option (List (Fin n))) :=
  let distances := dijkstra G codes source bound
  let tight := tightGraph G distances.1.distance
  let paths := WordPath.search tight.1 codes source
  (PathSearch.lookup paths.1 target, distances.2 + tight.2 + paths.2 + 2)

theorem shortestRoute_value (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (source target : Fin n) (bound : List Bool) :
    (shortestRoute G codes source target bound).1 =
      PathSearch.shortestRoute (edge G) (weight G) source target (value bound) := by
  have distances := dijkstra_value G codes correct source bound
  have getEq : ShortestPaths.get (decode (dijkstra G codes source bound).1) =
      (fun v : Fin n => value (dijkstra G codes source bound).1.distance[v.val]) :=
    funext (decode_get _)
  simp only [shortestRoute, WordPath.search_value _ codes correct, tightGraph_value,
    PathSearch.shortestRoute]
  rw [← distances, getEq]

theorem shortestRoute_cost (G : Graph n) (codes : Vector (List Bool) n)
    (source target : Fin n) (word : List Bool) (B : Nat)
    (cb : ∀ v : Fin n, codes[v.val].length ≤ B)
    (wb : ∀ u v : Fin n, G.cost[u.val][v.val].length ≤ B) (bb : word.length ≤ B) :
    (shortestRoute G codes source target word).2 ≤
      (2 * n * n + n * (9 * B + 12) + n * (stepBudget n n (B + n) + 1) + 6) +
      (2 * n * n * n + n * n * (16 * (B + n) + 29) + 9 * n + 4) +
      (2 * n * n + n * (9 * B + 12) + n * (WordPath.budget n B + 1) + 5) + 2 := by
  have hd := dijkstra_cost G codes source word B cb wb bb
  have hb := dijkstra_bounds G codes source word B cb wb bb
  have ht := tightGraph_cost G (dijkstra G codes source word).1.distance (B + n) hb.2.1 hb.2.2
  have hp := WordPath.search_cost (tightGraph G (dijkstra G codes source word).1.distance).1
    codes B cb source
  dsimp only [shortestRoute]
  omega

theorem shortestRoute_correct (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (source target : Fin n) (bound : List Bool)
    (below : value (dijkstra G codes source bound).1.distance[target.val] < value bound) :
    ∃ p, (shortestRoute G codes source target bound).1 = some p ∧
      PathSearch.Route (PathSearch.tightEdges (edge G) (weight G)
        (fun v => value (dijkstra G codes source bound).1.distance[v.val])) source target p ∧
      (target :: p).Nodup ∧ p.length < n := by
  have distances := dijkstra_value G codes correct source bound
  have getEq : ShortestPaths.get (decode (dijkstra G codes source bound).1) =
      (fun v : Fin n => value (dijkstra G codes source bound).1.distance[v.val]) :=
    funext (decode_get _)
  have below' : ShortestPaths.get
      (ShortestPaths.run (edge G) (weight G) n (ShortestPaths.initialState source (value bound)))
      target < value bound := by rw [← distances, getEq]; exact below
  have h := PathSearch.shortestRoute_correct (edge G) (weight G) source target (value bound) below'
  dsimp only at h
  rw [← distances, getEq] at h
  rw [shortestRoute_value G codes correct]
  exact h

theorem shortestRoute_length (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (source target : Fin n) (bound : List Bool)
    (p : List (Fin n)) (found : (shortestRoute G codes source target bound).1 = some p) :
    p.length < n :=
  WordPath.search_length _ codes correct source target p found

end GyoriLovasz.WordRoute
