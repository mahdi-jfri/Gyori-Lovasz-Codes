import GyoriLovasz.RuntimeAugment

namespace GyoriLovasz.Flow

theorem ResidualRoute.increment {G : Network n m} {f : Fin m → Nat}
    {source target : Fin n} {p : List (ResidualArc m)}
    (route : ResidualRoute G f source target p) (a : Fin m) :
    ResidualRoute (incrementCapacity G a) f source target p := by
  induction route with
  | start => exact .start
  | @extend u v p b route hb ht hh ih =>
    refine .extend ih ?_ ht hh
    obtain ⟨e, back⟩ := b
    cases back with
    | true => exact hb
    | false =>
      have free : f e < G.capacity e := by simpa [Flow.available] using hb
      simp only [Flow.available, Bool.false_eq_true, if_false, decide_eq_true_eq, incrementCapacity]
      split <;> omega

theorem routeDelta_zero {p : List (ResidualArc m)} {e : Fin m}
    (absent : ∀ a ∈ p, a.1 ≠ e) : routeDelta p e = 0 := by
  have hf : (e, false) ∉ p := fun h => absent _ h rfl
  have hb : (e, true) ∉ p := fun h => absent _ h rfl
  simp [routeDelta, List.count_eq_zero_of_not_mem hf, List.count_eq_zero_of_not_mem hb]

/-- A negative newly enabled arc is repaired by a computed simple residual
path. The resulting flow is feasible and has a feasible dual potential. -/
theorem augmenting_repair_correct {G : Network n m} {f : Fin m → Nat}
    {potential : Fin n → Int} (feasible : Feasible G f)
    (dual : DualFeasible G f potential) (a : Fin m)
    (negative : reducedCost G potential a < 0)
    (below : (residualDistances G f potential (G.head a)
      (-reducedCost G potential a).toNat)[(G.tail a).val] <
        (-reducedCost G potential a).toNat) :
    let d := residualDistances G f potential (G.head a) (-reducedCost G potential a).toNat
    ∃ p, residualShortestRoute G f potential (G.head a) (G.tail a)
        (-reducedCost G potential a).toNat = some p ∧
      Feasible (incrementCapacity G a) (augment f (routeDelta ((a, false) :: p))) ∧
      DualFeasible (incrementCapacity G a) (augment f (routeDelta ((a, false) :: p)))
        (fun v => potential v + d[v.val]) := by
  classical
  let d := residualDistances G f potential (G.head a) (-reducedCost G potential a).toNat
  let π := fun v => potential v + (d[v.val] : Int)
  have hd : DualFeasible G f π := residualDistances_dual dual _ _
  have zero : d[(G.head a).val] = 0 := residualDistances_source G f potential _ _
  have neg : reducedCost G π a < 0 := by
    have cast : ((-reducedCost G potential a).toNat : Int) = -reducedCost G potential a :=
      Int.toNat_of_nonneg (by omega)
    change d[(G.tail a).val] < (-reducedCost G potential a).toNat at below
    have dt : (d[(G.tail a).val] : Int) < -reducedCost G potential a := by omega
    have eq : reducedCost G π a = reducedCost G potential a + (d[(G.tail a).val] : Int) := by
      simp only [π, reducedCost, zero, Nat.cast_zero, add_zero]
      ring
    rw [eq]
    omega
  have saturated : f a = G.capacity a := by
    have upper := feasible.1 a
    have incompatible := dual.1 a
    omega
  obtain ⟨p, found, route, simple, _, tight⟩ := residualShortestRoute_correct dual
    (G.head a) (G.tail a) (-reducedCost G potential a).toNat below
  have absent : ∀ b ∈ p, b.1 ≠ a := by
    intro b hb eq
    have iszero : reducedCost G π b.1 = 0 := tight b hb
    rw [eq] at iszero
    omega
  have fresh : (a, false) ∉ p := fun h => absent _ h rfl
  have simple' : ((a, false) :: p).Nodup :=
    List.nodup_cons.mpr ⟨fresh, List.Nodup.of_map (arcTail G) simple.of_cons⟩
  have cycle : ResidualRoute (incrementCapacity G a) f (G.head a) (G.head a)
      ((a, false) :: p) := by
    apply ResidualRoute.extend (route.increment a)
    · simp [available, incrementCapacity, saturated]
    · rfl
    · rfl
  let g := augment f (routeDelta ((a, false) :: p))
  have hg : Feasible (incrementCapacity G a) g :=
    augment_cycle_feasible (increment_feasible feasible a) cycle simple'
  have ga : g a = G.capacity a + 1 := by
    simp [g, augment, routeDelta_cons, routeDelta_zero absent, arcDelta, saturated]
  have changed : ∀ e, e ≠ a → g e ≠ f e → reducedCost G π e = 0 := by
    intro e ea different
    by_cases present : ∃ b ∈ p, b.1 = e
    · obtain ⟨b, hb, eq⟩ := present
      exact eq ▸ tight b hb
    · have absent' : ∀ b ∈ p, b.1 ≠ e := by
        intro b hb eq
        exact present ⟨b, hb, eq⟩
      have unchanged : g e = f e := by
        simp [g, augment, routeDelta_cons, routeDelta_zero absent', arcDelta, Ne.symm ea]
      exact False.elim (different unchanged)
  refine ⟨p, found, hg, ?_, ?_⟩
  · intro e he
    by_cases ea : e = a
    · subst e
      change g a < (incrementCapacity G a).capacity a at he
      simp [incrementCapacity, ga] at he
    · by_cases eq : g e = f e
      · change g e < (incrementCapacity G a).capacity e at he
        exact hd.1 e (by simpa [incrementCapacity, ea, eq] using he)
      · exact (changed e ea eq).ge
  · intro e he
    by_cases ea : e = a
    · subst e
      exact neg.le
    · by_cases eq : g e = f e
      · change 0 < g e at he
        exact hd.2 e (by simpa [eq] using he)
      · exact (changed e ea eq).le

/-- One capacity increment, with materialized output flow and potential arrays. -/
def repairStep (G : Network n m) (f : Fin m → Nat) (potential : Fin n → Int)
    (a : Fin m) : Vector Nat m × Vector Int n :=
  if 0 ≤ reducedCost G potential a then (Vector.ofFn f, Vector.ofFn potential) else
    let bound := (-reducedCost G potential a).toNat
    let d := residualDistances G f potential (G.head a) bound
    let updated := Vector.ofFn (fun v => potential v + (d[v.val] : Int))
    if d[(G.tail a).val] < bound then
      match residualShortestRoute G f potential (G.head a) (G.tail a) bound with
      | none => (Vector.ofFn f, updated)
      | some p => (Vector.ofFn (augment f (routeDelta ((a, false) :: p))), updated)
    else (Vector.ofFn f, updated)

theorem repairStep_correct {G : Network n m} {f : Fin m → Nat}
    {potential : Fin n → Int} (feasible : Feasible G f)
    (dual : DualFeasible G f potential) (a : Fin m) :
    let output := repairStep G f potential a
    Feasible (incrementCapacity G a) (fun e => output.1[e.val]) ∧
      DualFeasible (incrementCapacity G a) (fun e => output.1[e.val])
        (fun v => output.2[v.val]) := by
  unfold repairStep
  split
  · rename_i nonnegative
    simpa using ⟨increment_feasible feasible a, increment_nonnegative_dual dual a nonnegative⟩
  · rename_i negative
    have neg : reducedCost G potential a < 0 := by omega
    dsimp only
    split
    · rename_i below
      obtain ⟨p, found, hf, hd⟩ := augmenting_repair_correct feasible dual a neg below
      simp only [found, Vector.getElem_ofFn]
      exact ⟨hf, hd⟩
    · rename_i notBelow
      let d := residualDistances G f potential (G.head a) (-reducedCost G potential a).toNat
      have upper := residualDistances_bound G f potential (G.head a)
        (-reducedCost G potential a).toNat (G.tail a)
      change d[(G.tail a).val] ≤ (-reducedCost G potential a).toNat at upper
      change ¬d[(G.tail a).val] < (-reducedCost G potential a).toNat at notBelow
      have eq : d[(G.tail a).val] = (-reducedCost G potential a).toNat := by omega
      have zero : d[(G.head a).val] = 0 := residualDistances_source G f potential _ _
      have cast : ((-reducedCost G potential a).toNat : Int) = -reducedCost G potential a :=
        Int.toNat_of_nonneg (by omega)
      have newcost : 0 ≤ reducedCost G (fun v => potential v + (d[v.val] : Int)) a := by
        have expression : reducedCost G (fun v => potential v + (d[v.val] : Int)) a =
            reducedCost G potential a + (d[(G.tail a).val] : Int) := by
          simp only [reducedCost, zero, Nat.cast_zero, add_zero]
          ring
        rw [expression, eq, cast]
        omega
      have hd := increment_nonnegative_dual
        (residualDistances_dual dual (G.head a) (-reducedCost G potential a).toNat) a newcost
      simpa using ⟨increment_feasible feasible a, hd⟩

theorem repairStep_optimal {G : Network n m} {f : Fin m → Nat}
    {potential : Fin n → Int} (feasible : Feasible G f)
    (dual : DualFeasible G f potential) (a : Fin m) :
    let output := repairStep G f potential a
    ∀ other, Feasible (incrementCapacity G a) other →
      totalCost (incrementCapacity G a) (fun e => output.1[e.val]) ≤
        totalCost (incrementCapacity G a) other := by
  have correct := repairStep_correct feasible dual a
  exact dual_optimal correct.1 correct.2

/-- An explicit magnitude bound for intermediate potentials. It is used to
control integer bit lengths, independently of feasibility or optimality. -/
theorem repairStep_potential_bound (G : Network n m) (f : Fin m → Nat)
    (potential : Fin n → Int) (a : Fin m) (C P : Nat)
    (costBound : ∀ e, -(C : Int) ≤ G.cost e ∧ G.cost e ≤ (C : Int))
    (potentialBound : ∀ v, -(P : Int) ≤ potential v ∧ potential v ≤ (P : Int)) :
    ∀ v : Fin n, -((C + 3 * P : Nat) : Int) ≤ (repairStep G f potential a).2[v.val] ∧
      (repairStep G f potential a).2[v.val] ≤ ((C + 3 * P : Nat) : Int) := by
  intro v
  have pv := potentialBound v
  unfold repairStep
  split
  · simp only [Vector.getElem_ofFn]
    change -((C + 3 * P : Nat) : Int) ≤ potential v ∧ potential v ≤ ((C + 3 * P : Nat) : Int)
    constructor <;> omega
  · rename_i neg
    have negative : reducedCost G potential a < 0 := by omega
    have tail := potentialBound (G.tail a)
    have head := potentialBound (G.head a)
    have cost := costBound a
    have rcBound : -reducedCost G potential a ≤ (C : Int) + 2 * P := by
      unfold reducedCost
      omega
    have cast : ((-reducedCost G potential a).toNat : Int) = -reducedCost G potential a :=
      Int.toNat_of_nonneg (by omega)
    have dv := residualDistances_bound G f potential (G.head a)
      (-reducedCost G potential a).toNat v
    have update : -((C + 3 * P : Nat) : Int) ≤ potential v +
        ((residualDistances G f potential (G.head a) (-reducedCost G potential a).toNat)[v.val] : Int) ∧
      potential v + ((residualDistances G f potential (G.head a)
        (-reducedCost G potential a).toNat)[v.val] : Int) ≤ ((C + 3 * P : Nat) : Int) := by
      constructor <;> omega
    dsimp only
    split
    · split <;> simpa only [Vector.getElem_ofFn] using update
    · simpa only [Vector.getElem_ofFn] using update

end GyoriLovasz.Flow
