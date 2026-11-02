import GyoriLovasz.RuntimeWordResidualRoute

namespace GyoriLovasz.Flow
open Binary WordShortest

def wordDistances (s : WordResidual n m) (source : Fin n) (bound : List Bool) :
    Costed.Computation (Vector (List Bool) n) :=
  let table := buildWordResidual s
  let graph := tableGraph table.1
  let result := dijkstra graph.1 s.vertexCode source bound
  (result.1.distance, table.2 + graph.2 + result.2 + 2)

theorem wordDistances_value (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (source : Fin n) (bound : List Bool) (v : Fin n) :
    value (wordDistances s source bound).1[v.val] =
      (residualDistances (decodeNetwork s) (decodeFlow s) (decodePotential s) source (value bound))[v.val] := by
  have h := congrArg (fun state => ShortestPaths.get state v)
    (dijkstra_value (tableGraph (buildWordResidual s).1).1 s.vertexCode correct source bound)
  dsimp only at h
  rw [decode_get, builtGraph_edge s correct, builtGraph_weight s correct] at h
  exact h

def distanceBudget (n B : Nat) :=
  2 * n * n + n * (9 * B + 12) + n * (stepBudget n n (B + n) + 1) + 6

theorem wordDistances_cost (s : WordResidual n m) (source : Fin n) (word : List Bool)
    (B : Nat) (bound : WordResidualBound s B) (bb : word.length ≤ B + 4) :
    (wordDistances s source word).2 ≤
      residualBuildBudget n m B + graphBudget n + distanceBudget n (B + 4) + 2 := by
  have ht := buildWordResidual_cost s B bound
  have hg := tableGraph_cost (buildWordResidual s).1
  have hd := dijkstra_cost (tableGraph (buildWordResidual s).1).1 s.vertexCode source word
    (B + 4) (fun v => Nat.le_trans (bound.2 v).1 (by omega)) (builtGraph_bounds s B bound) bb
  change _ ≤ residualBuildBudget n m B at ht
  change _ ≤ graphBudget n at hg
  change _ ≤ distanceBudget n (B + 4) at hd
  dsimp only [wordDistances]
  omega

theorem wordDistances_bounds (s : WordResidual n m) (source : Fin n) (word : List Bool)
    (B : Nat) (bound : WordResidualBound s B) (bb : word.length ≤ B + 4) (v : Fin n) :
    (wordDistances s source word).1[v.val].length ≤ B + 4 + n :=
  (dijkstra_bounds (tableGraph (buildWordResidual s).1).1 s.vertexCode source word
    (B + 4) (fun v => Nat.le_trans (bound.2 v).1 (by omega)) (builtGraph_bounds s B bound) bb).2.1 v

def updatePotential (potential : Vector SignedWord n) (d : Vector (List Bool) n) :
    Costed.Computation (Vector SignedWord n) :=
  Costed.tabulate n (fun v =>
    let sum := addSigned potential[v.val] ⟨false, d[v.val]⟩
    (sum.1, sum.2 + 3))

theorem updatePotential_value (potential : Vector SignedWord n) (d : Vector (List Bool) n)
    (v : Fin n) : signedValue (updatePotential potential d).1[v.val] =
      signedValue potential[v.val] + value d[v.val] := by
  simp only [updatePotential, Costed.tabulate_value, addSigned_correct]
  rfl

theorem updatePotential_cost (potential : Vector SignedWord n) (d : Vector (List Bool) n)
    (B : Nat) (pb : ∀ v : Fin n, potential[v.val].digits.length ≤ B)
    (db : ∀ v : Fin n, d[v.val].length ≤ B) :
    (updatePotential potential d).2 ≤ 2 * n * n + n * (18 * B + 18) + 3 := by
  have h := Costed.tabulate_cost n (fun v =>
    let sum := addSigned potential[v.val] ⟨false, d[v.val]⟩
    (sum.1, sum.2 + 3)) (18 * B + 12) (by
      intro v
      have hp := pb v
      have hd := db v
      have ha := addSigned_cost_bound potential[v.val] ⟨false, d[v.val]⟩
      dsimp only at ha ⊢
      omega)
  exact h

theorem updatePotential_length (potential : Vector SignedWord n) (d : Vector (List Bool) n)
    (B : Nat) (pb : ∀ v : Fin n, potential[v.val].digits.length ≤ B)
    (db : ∀ v : Fin n, d[v.val].length ≤ B) (v : Fin n) :
    (updatePotential potential d).1[v.val].digits.length ≤ B + 1 := by
  have hp := pb v
  have hd := db v
  have h := addSigned_length potential[v.val] ⟨false, d[v.val]⟩
  simp only [updatePotential, Costed.tabulate_value]
  dsimp only at h
  omega

end GyoriLovasz.Flow
