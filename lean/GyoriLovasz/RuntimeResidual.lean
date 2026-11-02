import GyoriLovasz.RuntimePathSearch
import GyoriLovasz.RuntimeFlowDual

namespace GyoriLovasz.Flow

abbrev ResidualArc (m : Nat) := Fin m × Bool

def arcTail (G : Network n m) (a : ResidualArc m) : Fin n :=
  if a.2 then G.head a.1 else G.tail a.1

def arcHead (G : Network n m) (a : ResidualArc m) : Fin n :=
  if a.2 then G.tail a.1 else G.head a.1

def available (G : Network n m) (f : Fin m → Nat) (a : ResidualArc m) : Bool :=
  if a.2 then decide (0 < f a.1) else decide (f a.1 < G.capacity a.1)

def arcCost (G : Network n m) (potential : Fin n → Int) (a : ResidualArc m) : Int :=
  if a.2 then -reducedCost G potential a.1 else reducedCost G potential a.1

def residualCandidates (G : Network n m) (f : Fin m → Nat) (u v : Fin n) : List (ResidualArc m) :=
  ((List.finRange m).flatMap (fun e => [(e, false), (e, true)])).filter
    (fun a => available G f a && decide (arcTail G a = u ∧ arcHead G a = v))

def bestArc (G : Network n m) (f : Fin m → Nat) (potential : Fin n → Int)
    (u v : Fin n) : Option (ResidualArc m) :=
  (residualCandidates G f u v).argmin (arcCost G potential)

def residualEdges (G : Network n m) (f : Fin m → Nat) (potential : Fin n → Int) :=
  fun u v => (bestArc G f potential u v).isSome

def residualCost (G : Network n m) (f : Fin m → Nat) (potential : Fin n → Int) :=
  fun u v => match bestArc G f potential u v with
    | none => 0
    | some a => (arcCost G potential a).toNat

theorem mem_residualCandidates (G : Network n m) (f : Fin m → Nat)
    (u v : Fin n) (a : ResidualArc m) :
    a ∈ residualCandidates G f u v ↔
      available G f a = true ∧ arcTail G a = u ∧ arcHead G a = v := by
  obtain ⟨e, b⟩ := a
  cases b <;> simp [residualCandidates, mem_finRange, and_assoc]

theorem available_nonnegative {G : Network n m} {f : Fin m → Nat}
    {potential : Fin n → Int} (dual : DualFeasible G f potential)
    (a : ResidualArc m) (h : available G f a = true) : 0 ≤ arcCost G potential a := by
  obtain ⟨e, b⟩ := a
  cases b with
  | false => exact dual.1 e (by simpa [available] using h)
  | true =>
    have le := dual.2 e (by simpa [available] using h)
    simpa [arcCost] using neg_nonneg.mpr le

theorem bestArc_spec {G : Network n m} {f : Fin m → Nat}
    {potential : Fin n → Int} {u v : Fin n} {a : ResidualArc m}
    (h : bestArc G f potential u v = some a) :
    available G f a = true ∧ arcTail G a = u ∧ arcHead G a = v :=
  (mem_residualCandidates G f u v a).mp (List.argmin_mem h)

theorem residualCost_le {G : Network n m} {f : Fin m → Nat}
    {potential : Fin n → Int} (dual : DualFeasible G f potential)
    (a : ResidualArc m) (ha : available G f a = true) :
    residualEdges G f potential (arcTail G a) (arcHead G a) = true ∧
      (residualCost G f potential (arcTail G a) (arcHead G a) : Int) ≤ arcCost G potential a := by
  have mem := (mem_residualCandidates G f (arcTail G a) (arcHead G a) a).mpr ⟨ha, rfl, rfl⟩
  cases h : bestArc G f potential (arcTail G a) (arcHead G a) with
  | none =>
    have empty := List.argmin_eq_none.mp h
    rw [empty] at mem
    exact False.elim (List.not_mem_nil mem)
  | some b =>
    have hb := bestArc_spec h
    have nonneg := available_nonnegative dual b hb.1
    have le := List.le_of_mem_argmin mem h
    simpa [residualEdges, residualCost, h, Int.toNat_of_nonneg nonneg] using
      (show True ∧ arcCost G potential b ≤ arcCost G potential a from ⟨True.intro, le⟩)

/-- Materialized shortest distances in the old residual network. -/
def residualDistances (G : Network n m) (f : Fin m → Nat) (potential : Fin n → Int)
    (source : Fin n) (bound : Nat) : Vector Nat n :=
  (ShortestPaths.run (residualEdges G f potential) (residualCost G f potential) n
    (ShortestPaths.initialState source bound)).distance

theorem residualDistances_dual {G : Network n m} {f : Fin m → Nat}
    {potential : Fin n → Int} (dual : DualFeasible G f potential)
    (source : Fin n) (bound : Nat) :
    DualFeasible G f
      (fun v => potential v + (residualDistances G f potential source bound)[v.val]) := by
  have correct := (ShortestPaths.dijkstra_correct
    (residualEdges G f potential) (residualCost G f potential) source bound).1
  apply reweight_dual
  · intro e he
    have edge := residualCost_le dual (e, false) (by simpa [available] using he)
    have triangle := correct.2.2 (G.tail e) (G.head e) edge.1
    have le := edge.2
    simp only [arcTail, arcHead, Bool.false_eq_true, if_false, arcCost] at le
    change (residualDistances G f potential source bound)[(G.head e).val] ≤
      (residualDistances G f potential source bound)[(G.tail e).val] +
        residualCost G f potential (G.tail e) (G.head e) at triangle
    omega
  · intro e he
    have edge := residualCost_le dual (e, true) (by simpa [available] using he)
    have triangle := correct.2.2 (G.head e) (G.tail e) edge.1
    have le := edge.2
    simp only [arcTail, arcHead, if_true, arcCost] at le
    change (residualDistances G f potential source bound)[(G.tail e).val] ≤
      (residualDistances G f potential source bound)[(G.head e).val] +
        residualCost G f potential (G.head e) (G.tail e) at triangle
    omega

theorem residualDistances_source (G : Network n m) (f : Fin m → Nat)
    (potential : Fin n → Int) (source : Fin n) (bound : Nat) :
    (residualDistances G f potential source bound)[source.val] = 0 :=
  (ShortestPaths.dijkstra_correct
    (residualEdges G f potential) (residualCost G f potential) source bound).1.1

theorem residualDistances_bound (G : Network n m) (f : Fin m → Nat)
    (potential : Fin n → Int) (source : Fin n) (bound : Nat) (v : Fin n) :
    (residualDistances G f potential source bound)[v.val] ≤ bound :=
  (ShortestPaths.dijkstra_correct
    (residualEdges G f potential) (residualCost G f potential) source bound).1.2.1 v

/-- The branch in which no sufficiently cheap return path exists needs only
a distance-potential update; the old flow is already optimal at the new capacity. -/
theorem increment_without_augmentation {G : Network n m} {f : Fin m → Nat}
    {potential : Fin n → Int} (feasible : Feasible G f)
    (dual : DualFeasible G f potential) (a : Fin m)
    (negative : reducedCost G potential a < 0)
    (unreached : (residualDistances G f potential (G.head a)
      (-reducedCost G potential a).toNat)[(G.tail a).val] =
        (-reducedCost G potential a).toNat) :
    ∀ other, Feasible (incrementCapacity G a) other →
      totalCost (incrementCapacity G a) f ≤ totalCost (incrementCapacity G a) other := by
  let d := residualDistances G f potential (G.head a) (-reducedCost G potential a).toNat
  have hd := residualDistances_dual dual (G.head a) (-reducedCost G potential a).toNat
  have zero := residualDistances_source G f potential (G.head a) (-reducedCost G potential a).toNat
  have cast : ((-reducedCost G potential a).toNat : Int) = -reducedCost G potential a :=
    Int.toNat_of_nonneg (by omega)
  have rc : 0 ≤ reducedCost G (fun v => potential v + d[v.val]) a := by
    have dt : d[(G.tail a).val] = (-reducedCost G potential a).toNat := unreached
    have dh : d[(G.head a).val] = 0 := zero
    unfold reducedCost at *
    simp only [dt, dh, Nat.cast_zero, add_zero]
    omega
  exact dual_optimal (increment_feasible feasible a) (increment_nonnegative_dual hd a rc)

theorem selected_tight_zero {G : Network n m} {f : Fin m → Nat}
    {potential : Fin n → Int} (dual : DualFeasible G f potential)
    {d : Fin n → Nat} {u v : Fin n} {a : ResidualArc m}
    (selected : bestArc G f potential u v = some a)
    (tight : d v = d u + residualCost G f potential u v) :
    reducedCost G (fun x => potential x + d x) a.1 = 0 := by
  have spec := bestArc_spec selected
  have nonneg := available_nonnegative dual a spec.1
  have cast : ((residualCost G f potential u v) : Int) = arcCost G potential a := by
    simp [residualCost, selected, Int.toNat_of_nonneg nonneg]
  have eq : (d v : Int) = (d u : Int) + arcCost G potential a := by omega
  obtain ⟨e, b⟩ := a
  cases b <;> simp [arcTail, arcHead] at spec <;>
    simp [arcCost, reducedCost] at eq ⊢ <;> simp_all <;> omega

end GyoriLovasz.Flow
