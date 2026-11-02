import GyoriLovasz.RuntimeResidual

namespace GyoriLovasz.Flow

inductive ResidualRoute (G : Network n m) (f : Fin m → Nat) (source : Fin n) :
    Fin n → List (ResidualArc m) → Prop where
  | start : ResidualRoute G f source source []
  | extend {u v p a} : ResidualRoute G f source u p → available G f a = true →
      arcTail G a = u → arcHead G a = v → ResidualRoute G f source v (a :: p)

/-- Translate a reverse vertex path into concrete signed network arcs. -/
def liftRoute (G : Network n m) (f : Fin m → Nat) (potential : Fin n → Int) :
    Fin n → List (Fin n) → Option (List (ResidualArc m))
  | _, [] => some []
  | v, u :: p => match bestArc G f potential u v, liftRoute G f potential u p with
    | some a, some rest => some (a :: rest)
    | _, _ => none

theorem liftRoute_correct {G : Network n m} {f : Fin m → Nat}
    {potential : Fin n → Int} (dual : DualFeasible G f potential)
    {d : Fin n → Nat} {source target : Fin n} {p : List (Fin n)}
    (path : PathSearch.Route
      (PathSearch.tightEdges (residualEdges G f potential) (residualCost G f potential) d)
      source target p) :
    ∃ q, liftRoute G f potential target p = some q ∧
      ResidualRoute G f source target q ∧ q.map (arcTail G) = p ∧
      ∀ a ∈ q, reducedCost G (fun x => potential x + d x) a.1 = 0 := by
  induction path with
  | start => exact ⟨[], rfl, .start, rfl, by simp⟩
  | @extend u v p path edge ih =>
    obtain ⟨q, lifted, route, tails, tight⟩ := ih
    have data : residualEdges G f potential u v = true ∧
        d v = d u + residualCost G f potential u v := by
      simpa [PathSearch.tightEdges] using edge
    cases selected : bestArc G f potential u v with
    | none => simp [residualEdges, selected] at data
    | some a =>
      have spec := bestArc_spec selected
      refine ⟨a :: q, ?_, .extend route spec.1 spec.2.1 spec.2.2, ?_, ?_⟩
      · simp [liftRoute, selected, lifted]
      · simp [tails, spec.2.1]
      · intro b hb
        rcases List.mem_cons.mp hb with eq | hb
        · subst b
          exact selected_tight_zero dual selected data.2
        · exact tight b hb

def residualShortestRoute (G : Network n m) (f : Fin m → Nat) (potential : Fin n → Int)
    (source target : Fin n) (bound : Nat) : Option (List (ResidualArc m)) :=
  match PathSearch.shortestRoute (residualEdges G f potential) (residualCost G f potential)
      source target bound with
  | none => none
  | some p => liftRoute G f potential target p

theorem residualShortestRoute_correct {G : Network n m} {f : Fin m → Nat}
    {potential : Fin n → Int} (dual : DualFeasible G f potential)
    (source target : Fin n) (bound : Nat)
    (below : (residualDistances G f potential source bound)[target.val] < bound) :
    ∃ q, residualShortestRoute G f potential source target bound = some q ∧
      ResidualRoute G f source target q ∧
      (target :: q.map (arcTail G)).Nodup ∧ q.length < n ∧
      ∀ a ∈ q, reducedCost G
        (fun x => potential x + (residualDistances G f potential source bound)[x.val]) a.1 = 0 := by
  obtain ⟨p, found, path, simple, bound⟩ := PathSearch.shortestRoute_correct
    (residualEdges G f potential) (residualCost G f potential) source target bound below
  obtain ⟨q, lifted, route, tails, tight⟩ := liftRoute_correct dual path
  refine ⟨q, ?_, route, ?_, ?_, tight⟩
  · simp [residualShortestRoute, found, lifted]
  · simpa [tails] using simple
  · have len := congrArg List.length tails
    simp only [List.length_map] at len
    omega

theorem ResidualRoute.available {G : Network n m} {f : Fin m → Nat}
    {source target : Fin n} {p : List (ResidualArc m)}
    (route : ResidualRoute G f source target p) : ∀ a ∈ p, available G f a = true := by
  induction route with
  | start => simp
  | extend route ha ht hh ih =>
    intro a mem
    rcases List.mem_cons.mp mem with eq | mem
    · subst a; exact ha
    · exact ih a mem

end GyoriLovasz.Flow
