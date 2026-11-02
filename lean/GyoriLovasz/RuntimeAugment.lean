import GyoriLovasz.RuntimeResidualPath
import Mathlib.Data.List.Nodup

namespace GyoriLovasz.Flow
open scoped BigOperators

def routeDelta (p : List (ResidualArc m)) (e : Fin m) : Int :=
  (p.count (e, false) : Int) - (p.count (e, true) : Int)

def arcDelta (a : ResidualArc m) (e : Fin m) : Int :=
  if a.1 = e then if a.2 then -1 else 1 else 0

theorem routeDelta_cons (a : ResidualArc m) (p : List (ResidualArc m)) (e : Fin m) :
    routeDelta (a :: p) e = arcDelta a e + routeDelta p e := by
  obtain ⟨j, b⟩ := a
  by_cases eq : j = e
  · subst j
    cases b <;> simp [routeDelta, arcDelta, List.count_cons] <;> omega
  · cases b <;> simp [routeDelta, arcDelta, List.count_cons, eq, Ne.symm eq]

def divergence (G : Network n m) (delta : Fin m → Int) (v : Fin n) : Int :=
  (∑ e, if G.tail e = v then delta e else 0) - ∑ e, if G.head e = v then delta e else 0

theorem divergence_add (G : Network n m) (d e : Fin m → Int) (v : Fin n) :
    divergence G (fun a => d a + e a) v = divergence G d v + divergence G e v := by
  have splitSum (P : Prop) [Decidable P] (a b : Int) :
      (if P then a + b else 0) = (if P then a else 0) + (if P then b else 0) := by
    by_cases h : P <;> simp [h]
  simp only [divergence, splitSum, Finset.sum_add_distrib]
  ring

theorem arcDelta_divergence (G : Network n m) (a : ResidualArc m) (v : Fin n) :
    divergence G (arcDelta a) v =
      (if arcTail G a = v then 1 else 0) - (if arcHead G a = v then 1 else 0) := by
  have endpoint (ends : Fin m → Fin n) :
      (∑ e, if ends e = v then arcDelta a e else 0) =
        if ends a.1 = v then (if a.2 then -1 else 1) else 0 := by
    rw [Finset.sum_eq_single a.1]
    · simp [arcDelta]
    · intro e _ he
      simp [arcDelta, Ne.symm he]
    · simp
  simp only [divergence, endpoint]
  obtain ⟨e, b⟩ := a
  cases b <;> simp [arcTail, arcHead]
  split <;> split <;> norm_num

theorem ResidualRoute.divergence {G : Network n m} {f : Fin m → Nat}
    {source target : Fin n} {p : List (ResidualArc m)}
    (route : ResidualRoute G f source target p) (v : Fin n) :
    divergence G (routeDelta p) v =
      (if source = v then 1 else 0) - (if target = v then 1 else 0) := by
  induction route with
  | start => simp [Flow.divergence, routeDelta]
  | @extend u w p a route ha ht hh ih =>
    have eq : routeDelta (a :: p) = fun e => arcDelta a e + routeDelta p e :=
      funext (routeDelta_cons a p)
    rw [eq]
    rw [divergence_add, arcDelta_divergence, ht, hh, ih]
    ring

theorem routeDelta_bounds {G : Network n m} {f : Fin m → Nat}
    (feasible : Feasible G f) {p : List (ResidualArc m)} (simple : p.Nodup)
    (available : ∀ a ∈ p, Flow.available G f a = true) (e : Fin m) :
    0 ≤ (f e : Int) + routeDelta p e ∧
      (f e : Int) + routeDelta p e ≤ (G.capacity e : Int) := by
  classical
  have forward : p.count (e, false) ≤ 1 := by
    simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using
      List.nodup_iff_count_le_one.mp simple (e, false)
  have backward : p.count (e, true) ≤ 1 := by
    simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using
      List.nodup_iff_count_le_one.mp simple (e, true)
  have capacity := feasible.1 e
  have lower : 0 < p.count (e, true) → 0 < f e := by
    intro h
    have yes := available (e, true) (List.count_pos_iff.mp h)
    simpa [Flow.available] using yes
  have upper : 0 < p.count (e, false) → f e < G.capacity e := by
    intro h
    have yes := available (e, false) (List.count_pos_iff.mp h)
    simpa [Flow.available] using yes
  have delta : routeDelta p e = (p.count (e, false) : Int) - (p.count (e, true) : Int) := by
    simp only [routeDelta, List.count_eq_countP, Bool.beq_eq_decide_eq]
  rw [delta]
  constructor <;> omega

/-- An executable unit augmentation around a residual cycle preserves all
capacities and conservation equations. Each signed arc occurs at most once. -/
theorem augment_cycle_feasible {G : Network n m} {f : Fin m → Nat}
    (feasible : Feasible G f) {source : Fin n} {p : List (ResidualArc m)}
    (route : ResidualRoute G f source source p) (simple : p.Nodup) :
    Feasible G (augment f (routeDelta p)) := by
  apply augment_feasible feasible
  · intro e
    exact (routeDelta_bounds feasible simple route.available e).1
  · intro e
    exact (routeDelta_bounds feasible simple route.available e).2
  · intro v
    have zero := route.divergence v
    simp only [sub_self] at zero
    exact sub_eq_zero.mp zero

end GyoriLovasz.Flow
