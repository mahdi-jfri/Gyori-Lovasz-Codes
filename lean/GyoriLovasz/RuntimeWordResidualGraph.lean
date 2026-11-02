import GyoriLovasz.RuntimeWordRoute
import GyoriLovasz.RuntimeResidualPath

namespace GyoriLovasz.Flow
open Binary

abbrev WordArcTable (n m : Nat) := Vector (Vector (Option (ResidualArc m × SignedWord)) n) n

def naturalWord (w : SignedWord) : List Bool := if w.negative then [] else w.digits

theorem naturalWord_value (w : SignedWord) : value (naturalWord w) = (signedValue w).toNat := by
  rcases w with ⟨b, digits⟩
  cases b <;> simp [naturalWord, signedValue, value]
  omega

theorem naturalWord_length (w : SignedWord) : (naturalWord w).length ≤ w.digits.length := by
  unfold naturalWord
  split <;> simp

def tableGraph (t : WordArcTable n m) : Costed.Computation (WordShortest.Graph n) :=
  let edges := Costed.tabulate₂ n (fun u v => (t[u.val][v.val].isSome, 4))
  let costs := Costed.tabulate₂ n (fun u v =>
    (match t[u.val][v.val] with | none => [] | some a => naturalWord a.2, 5))
  (⟨edges.1, costs.1⟩, edges.2 + costs.2 + 1)

theorem tableGraph_edge (t : WordArcTable n m) (u v : Fin n) :
    WordShortest.edge (tableGraph t).1 u v = t[u.val][v.val].isSome := by
  simp [tableGraph, WordShortest.edge, Costed.tabulate₂_value]

theorem tableGraph_weight (t : WordArcTable n m) (u v : Fin n) :
    WordShortest.weight (tableGraph t).1 u v =
      match t[u.val][v.val] with | none => 0 | some a => (signedValue a.2).toNat := by
  simp only [tableGraph, WordShortest.weight, Costed.tabulate₂_value]
  cases h : t[u.val][v.val] <;> simp [value, naturalWord_value]

theorem tableGraph_cost (t : WordArcTable n m) :
    (tableGraph t).2 ≤ 4 * n * n * n + 25 * n * n + 18 * n + 7 := by
  have he := Costed.tabulate₂_cost n (fun u v => (t[u.val][v.val].isSome, 4)) 4
    (by intros; exact Nat.le_refl _)
  have hc := Costed.tabulate₂_cost n (fun u v =>
    (match t[u.val][v.val] with | none => [] | some a => naturalWord a.2, 5)) 5
    (by intros; exact Nat.le_refl _)
  dsimp only [tableGraph]
  ring_nf at he hc ⊢
  omega

theorem builtGraph_edge (s : WordResidual n m) (correct : VertexCodesCorrect s) :
    WordShortest.edge (tableGraph (buildWordResidual s).1).1 =
      residualEdges (decodeNetwork s) (decodeFlow s) (decodePotential s) := by
  funext u v
  rw [tableGraph_edge]
  have h := congrArg Option.isSome (buildWordResidual_value s correct u v)
  simpa [residualEdges] using h

theorem builtGraph_weight (s : WordResidual n m) (correct : VertexCodesCorrect s) :
    WordShortest.weight (tableGraph (buildWordResidual s).1).1 =
      residualCost (decodeNetwork s) (decodeFlow s) (decodePotential s) := by
  funext u v
  rw [tableGraph_weight]
  have h := congrArg (fun x : Option (ResidualArc m × Int) =>
    match x with | none => 0 | some a => a.2.toNat) (buildWordResidual_value s correct u v)
  cases ht : (buildWordResidual s).1[u.val][v.val] <;>
    cases hb : bestArc (decodeNetwork s) (decodeFlow s) (decodePotential s) u v <;>
    simpa [residualCost, ht, hb] using h

theorem builtGraph_bounds (s : WordResidual n m) (B : Nat) (bound : WordResidualBound s B)
    (u v : Fin n) :
    (tableGraph (buildWordResidual s).1).1.cost[u.val][v.val].length ≤ B + 4 := by
  simp only [tableGraph, Costed.tabulate₂_value, buildWordResidual]
  dsimp only [wordResidualCell]
  cases h : (wordBestArc s u v).1
  · simp
  · rename_i a
    exact Nat.le_trans (naturalWord_length _) (wordScore_bounds s B bound a).2

/-- Lift through the stored selected arcs, without re-running edge selection. -/
def liftTable (t : WordArcTable n m) :
    Fin n → List (Fin n) → Costed.Computation (Option (List (ResidualArc m)))
  | _, [] => (some [], 1)
  | v, u :: p =>
    let rest := liftTable t u p
    (match t[u.val][v.val], rest.1 with
      | some a, some q => some (a.1 :: q)
      | _, _ => none, rest.2 + 8)

theorem liftTable_cost (t : WordArcTable n m) (v : Fin n) (p : List (Fin n)) :
    (liftTable t v p).2 = 8 * p.length + 1 := by
  induction p generalizing v with
  | nil => rfl
  | cons u p ih => simp [liftTable, ih, Nat.mul_add, Nat.add_assoc]

theorem liftTable_value (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (v : Fin n) (p : List (Fin n)) :
    (liftTable (buildWordResidual s).1 v p).1 =
      liftRoute (decodeNetwork s) (decodeFlow s) (decodePotential s) v p := by
  induction p generalizing v with
  | nil => rfl
  | cons u p ih =>
    have h := congrArg (Option.map Prod.fst) (buildWordResidual_value s correct u v)
    simp only [Option.map_map, Function.comp_def] at h
    simp only [liftTable, ih, liftRoute]
    cases ht : (buildWordResidual s).1[u.val][v.val] <;>
      cases hb : bestArc (decodeNetwork s) (decodeFlow s) (decodePotential s) u v <;>
      simp_all
    cases liftRoute (decodeNetwork s) (decodeFlow s) (decodePotential s) u p <;> simp_all

theorem liftTable_length (t : WordArcTable n m) (v : Fin n) (p : List (Fin n))
    (q : List (ResidualArc m)) (found : (liftTable t v p).1 = some q) : q.length = p.length := by
  induction p generalizing v q with
  | nil => simp [liftTable] at found; subst q; rfl
  | cons u p ih =>
    dsimp only [liftTable] at found
    cases ht : t[u.val][v.val] <;> cases hr : (liftTable t u p).1 <;> simp [ht, hr] at found
    subst q
    simp [ih _ _ hr]

end GyoriLovasz.Flow
