import GyoriLovasz.RuntimeWordResidualGraph

namespace GyoriLovasz.Flow
open Binary WordShortest

def wordResidualRoute (s : WordResidual n m) (source target : Fin n) (bound : List Bool) :
    Costed.Computation (Option (List (ResidualArc m))) :=
  let table := buildWordResidual s
  let graph := tableGraph table.1
  let path := WordRoute.shortestRoute graph.1 s.vertexCode source target bound
  match path.1 with
  | none => (none, table.2 + graph.2 + path.2 + 2)
  | some p =>
    let lifted := liftTable table.1 target p
    (lifted.1, table.2 + graph.2 + path.2 + lifted.2 + 3)

theorem wordResidualRoute_value (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source target : Fin n) (bound : List Bool) :
    (wordResidualRoute s source target bound).1 =
      residualShortestRoute (decodeNetwork s) (decodeFlow s) (decodePotential s)
        source target (value bound) := by
  dsimp only [wordResidualRoute]
  rw [WordRoute.shortestRoute_value _ _ correct, builtGraph_edge s correct, builtGraph_weight s correct]
  unfold residualShortestRoute
  cases h : PathSearch.shortestRoute (residualEdges (decodeNetwork s) (decodeFlow s) (decodePotential s))
    (residualCost (decodeNetwork s) (decodeFlow s) (decodePotential s)) source target (value bound) with
  | none => rfl
  | some p => exact liftTable_value s correct target p

def residualBuildBudget (n m B : Nat) :=
  2 * n * n * n + n * n * (2 * m * m + 7 * m + 2 * m * (180 * B + 398) + 72 * B + 172) + 9 * n + 3

def graphBudget (n : Nat) := 4 * n * n * n + 25 * n * n + 18 * n + 7

def routeBudget (n B : Nat) :=
  (2 * n * n + n * (9 * B + 12) + n * (stepBudget n n (B + n) + 1) + 6) +
  (2 * n * n * n + n * n * (16 * (B + n) + 29) + 9 * n + 4) +
  (2 * n * n + n * (9 * B + 12) + n * (WordPath.budget n B + 1) + 5) + 2

theorem wordResidualRoute_cost (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source target : Fin n) (word : List Bool) (B : Nat) (bound : WordResidualBound s B)
    (bb : word.length ≤ B + 4) :
    (wordResidualRoute s source target word).2 ≤
      residualBuildBudget n m B + graphBudget n + routeBudget n (B + 4) + 8 * n + 4 := by
  have ht := buildWordResidual_cost s B bound
  have hg := tableGraph_cost (buildWordResidual s).1
  have hp := WordRoute.shortestRoute_cost (tableGraph (buildWordResidual s).1).1 s.vertexCode
    source target word (B + 4) (fun v => Nat.le_trans (bound.2 v).1 (by omega))
    (builtGraph_bounds s B bound) bb
  change _ ≤ residualBuildBudget n m B at ht
  change _ ≤ graphBudget n at hg
  change _ ≤ routeBudget n (B + 4) at hp
  dsimp only [wordResidualRoute]
  split
  · omega
  · rename_i p found
    have len := WordRoute.shortestRoute_length (tableGraph (buildWordResidual s).1).1
      s.vertexCode correct source target word p found
    have hl := liftTable_cost (buildWordResidual s).1 target p
    omega

theorem wordResidualRoute_length (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source target : Fin n) (word : List Bool) (q : List (ResidualArc m))
    (found : (wordResidualRoute s source target word).1 = some q) : q.length < n := by
  dsimp only [wordResidualRoute] at found
  cases hp : (WordRoute.shortestRoute (tableGraph (buildWordResidual s).1).1
    s.vertexCode source target word).1 with
  | none => simp [hp] at found
  | some p =>
    simp only [hp] at found
    rw [liftTable_length _ _ _ _ found]
    exact WordRoute.shortestRoute_length _ _ correct source target word p hp

end GyoriLovasz.Flow
