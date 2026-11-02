import GyoriLovasz.WeightedMain
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Int

namespace GyoriLovasz.Flow
open scoped BigOperators

/-- Directed multigraph network with integral capacities and signed costs. -/
structure Network (n m : Nat) where
  tail : Fin m → Fin n
  head : Fin m → Fin n
  capacity : Fin m → Nat
  cost : Fin m → Int

def Feasible (G : Network n m) (f : Fin m → Nat) : Prop :=
  (∀ e, f e ≤ G.capacity e) ∧
  ∀ v : Fin n, (∑ e, if G.tail e = v then (f e : Int) else 0) =
    ∑ e, if G.head e = v then (f e : Int) else 0

def totalCost (G : Network n m) (f : Fin m → Nat) : Int :=
  ∑ e, G.cost e * (f e : Int)

def reducedCost (G : Network n m) (potential : Fin n → Int) (e : Fin m) : Int :=
  G.cost e + potential (G.tail e) - potential (G.head e)

/-- Nonnegative costs on every available forward and reverse residual arc. -/
def DualFeasible (G : Network n m) (f : Fin m → Nat) (potential : Fin n → Int) : Prop :=
  (∀ e, f e < G.capacity e → 0 ≤ reducedCost G potential e) ∧
  (∀ e, 0 < f e → reducedCost G potential e ≤ 0)

theorem endpoint_sum (endpoint : Fin m → Fin n) (potential : Fin n → Int) (flow : Fin m → Int) :
    (∑ e, potential (endpoint e) * flow e) =
      ∑ v, potential v * ∑ e, if endpoint e = v then flow e else 0 := by
  symm
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_eq_single (endpoint e)]
  · simp
  · intro v _ hv
    simp [Ne.symm hv]
  · simp

theorem potential_cancels {G : Network n m} {f : Fin m → Nat}
    (feasible : Feasible G f) (potential : Fin n → Int) :
    ∑ e, (potential (G.tail e) - potential (G.head e)) * (f e : Int) = 0 := by
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [endpoint_sum G.tail potential (fun e => (f e : Int)),
    endpoint_sum G.head potential (fun e => (f e : Int))]
  have eq : (∑ v, potential v * ∑ e, if G.tail e = v then (f e : Int) else 0) =
      ∑ v, potential v * ∑ e, if G.head e = v then (f e : Int) else 0 := by
    apply Finset.sum_congr rfl
    intro v _
    rw [feasible.2 v]
  rw [eq, sub_self]

theorem reduced_total_eq {G : Network n m} {f : Fin m → Nat}
    (feasible : Feasible G f) (potential : Fin n → Int) :
    (∑ e, reducedCost G potential e * (f e : Int)) = totalCost G f := by
  have terms (e : Fin m) : reducedCost G potential e * (f e : Int) =
      G.cost e * (f e : Int) + (potential (G.tail e) - potential (G.head e)) * (f e : Int) := by
    unfold reducedCost
    ring
  simp only [terms, Finset.sum_add_distrib, potential_cancels feasible potential, add_zero, totalCost]

/-- A feasible circulation with feasible residual potentials minimizes cost
among all feasible circulations. This is a proved certificate theorem; it does
not assert that a polynomial-time algorithm has yet produced the certificate. -/
theorem dual_optimal {G : Network n m} {f : Fin m → Nat} {potential : Fin n → Int}
    (feasible : Feasible G f) (dual : DualFeasible G f potential) :
    ∀ g, Feasible G g → totalCost G f ≤ totalCost G g := by
  intro g other
  rw [← reduced_total_eq feasible potential, ← reduced_total_eq other potential]
  apply Finset.sum_le_sum
  intro e _
  by_cases eq : f e = g e
  · rw [eq]
  · by_cases le : f e ≤ g e
    · have room : f e < G.capacity e := lt_of_lt_of_le (by omega) (other.1 e)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast le) (dual.1 e room)
    · have used : 0 < f e := by omega
      exact mul_le_mul_of_nonpos_left (by exact_mod_cast (show g e ≤ f e by omega)) (dual.2 e used)

def checkFeasible (G : Network n m) (f : Fin m → Nat) : Bool :=
  (List.finRange m).all (fun e => decide (f e ≤ G.capacity e)) &&
  (List.finRange n).all (fun v => decide
    ((∑ e, if G.tail e = v then (f e : Int) else 0) =
      ∑ e, if G.head e = v then (f e : Int) else 0))

def checkDual (G : Network n m) (f : Fin m → Nat) (potential : Fin n → Int) : Bool :=
  (List.finRange m).all (fun e =>
    decide ((f e < G.capacity e → 0 ≤ reducedCost G potential e) ∧
      (0 < f e → reducedCost G potential e ≤ 0)))

theorem checkFeasible_correct (G : Network n m) (f : Fin m → Nat) :
    checkFeasible G f = true ↔ Feasible G f := by
  simp [checkFeasible, Feasible, List.all_eq_true, mem_finRange]

theorem checkDual_correct (G : Network n m) (f : Fin m → Nat) (potential : Fin n → Int) :
    checkDual G f potential = true ↔ DualFeasible G f potential := by
  constructor
  · intro h
    have each := List.all_eq_true.mp h
    exact ⟨fun e => (of_decide_eq_true (each e (mem_finRange e))).1,
      fun e => (of_decide_eq_true (each e (mem_finRange e))).2⟩
  · intro h
    apply List.all_eq_true.mpr
    intro e _
    exact decide_eq_true ⟨h.1 e, h.2 e⟩

def doubleCapacity (G : Network n m) : Network n m :=
  { G with capacity := fun e => 2 * G.capacity e }

def doubleFlow (f : Fin m → Nat) : Fin m → Nat := fun e => 2 * f e

/-- Capacity scaling preserves the circulation equations. -/
theorem double_feasible {G : Network n m} {f : Fin m → Nat} (hf : Feasible G f) :
    Feasible (doubleCapacity G) (doubleFlow f) := by
  refine ⟨fun e => Nat.mul_le_mul_left 2 (hf.1 e), ?_⟩
  intro v
  have eq := congrArg (fun z : Int => 2 * z) (hf.2 v)
  simpa [doubleCapacity, doubleFlow, Finset.mul_sum, mul_ite] using eq

/-- Doubling flow and capacities leaves the available residual arcs unchanged,
so it preserves the same potential certificate and therefore optimality. -/
theorem double_dual {G : Network n m} {f : Fin m → Nat} {potential : Fin n → Int}
    (hd : DualFeasible G f potential) :
    DualFeasible (doubleCapacity G) (doubleFlow f) potential := by
  constructor
  · intro e he
    exact hd.1 e (by change 2 * f e < 2 * G.capacity e at he; omega)
  · intro e he
    exact hd.2 e (by change 0 < 2 * f e at he; omega)

def incrementCapacity (G : Network n m) (a : Fin m) : Network n m :=
  { G with capacity := fun e => if e = a then G.capacity e + 1 else G.capacity e }

theorem increment_feasible {G : Network n m} {f : Fin m → Nat}
    (hf : Feasible G f) (a : Fin m) : Feasible (incrementCapacity G a) f := by
  refine ⟨?_, hf.2⟩
  intro e
  by_cases he : e = a
  · subst e
    simpa only [incrementCapacity, if_pos rfl] using Nat.le_succ_of_le (hf.1 a)
  · simpa only [incrementCapacity, if_neg he] using hf.1 e

/-- A capacity increment on an arc with nonnegative reduced cost needs no
augmentation: the old optimum remains optimal. Negative increments require
the shortest-path repair subroutine, which is not asserted by this lemma. -/
theorem increment_nonnegative_dual {G : Network n m} {f : Fin m → Nat}
    {potential : Fin n → Int} (hd : DualFeasible G f potential) (a : Fin m)
    (nonnegative : 0 ≤ reducedCost G potential a) :
    DualFeasible (incrementCapacity G a) f potential := by
  refine ⟨?_, hd.2⟩
  intro e he
  by_cases eq : e = a
  · subst e
    exact nonnegative
  · exact hd.1 e (by simpa [incrementCapacity, eq] using he)

/-- Shortest-path edge inequalities are exactly what a potential update needs
to retain nonnegative reduced costs on the old residual network. -/
theorem reweight_dual {G : Network n m} {f : Fin m → Nat} {potential distance : Fin n → Int}
    (forward : ∀ e, f e < G.capacity e →
      distance (G.head e) ≤ distance (G.tail e) + reducedCost G potential e)
    (backward : ∀ e, 0 < f e →
      distance (G.tail e) ≤ distance (G.head e) - reducedCost G potential e) :
    DualFeasible G f (fun v => potential v + distance v) := by
  have eq (e : Fin m) : reducedCost G (fun v => potential v + distance v) e =
      reducedCost G potential e + distance (G.tail e) - distance (G.head e) := by
    unfold reducedCost
    ring
  constructor
  · intro e he
    rw [eq]
    have bound := forward e he
    omega
  · intro e he
    rw [eq]
    have bound := backward e he
    omega

def augment (f : Fin m → Nat) (delta : Fin m → Int) : Fin m → Nat :=
  fun e => ((f e : Int) + delta e).toNat

/-- Signed residual augmentations preserve conservation when their own net
inflow and outflow agree. Capacity and nonnegativity are checked per arc. -/
theorem augment_feasible {G : Network n m} {f : Fin m → Nat} {delta : Fin m → Int}
    (hf : Feasible G f)
    (lower : ∀ e, 0 ≤ (f e : Int) + delta e)
    (upper : ∀ e, (f e : Int) + delta e ≤ (G.capacity e : Int))
    (balanced : ∀ v, (∑ e, if G.tail e = v then delta e else 0) =
      ∑ e, if G.head e = v then delta e else 0) :
    Feasible G (augment f delta) := by
  have cast (e : Fin m) : (augment f delta e : Int) = (f e : Int) + delta e := by
    exact Int.toNat_of_nonneg (lower e)
  refine ⟨?_, ?_⟩
  · intro e
    have bound := upper e
    rw [← cast e] at bound
    exact Int.ofNat_le.mp bound
  · intro v
    have splitSum (P : Prop) [Decidable P] (a b : Int) :
        (if P then a + b else 0) = (if P then a else 0) + (if P then b else 0) := by
      by_cases h : P <;> simp [h]
    simp only [cast, splitSum, Finset.sum_add_distrib]
    rw [hf.2 v, balanced v]

/-- Optimality after a unit-capacity repair. The newly enabled arc is saturated;
other changed arcs are tight for the updated potential. The shortest-path
repair must construct an augmentation satisfying these explicit conditions. -/
theorem repair_optimal {G : Network n m} {f g : Fin m → Nat} {potential : Fin n → Int}
    (a : Fin m) (hg : Feasible (incrementCapacity G a) g)
    (saturated : g a = G.capacity a + 1)
    (newcost : reducedCost G potential a ≤ 0)
    (unchangedForward : ∀ e, e ≠ a → f e < G.capacity e → 0 ≤ reducedCost G potential e)
    (unchangedBackward : ∀ e, e ≠ a → 0 < f e → reducedCost G potential e ≤ 0)
    (tight : ∀ e, e ≠ a → g e ≠ f e → reducedCost G potential e = 0) :
    ∀ other, Feasible (incrementCapacity G a) other →
      totalCost (incrementCapacity G a) g ≤ totalCost (incrementCapacity G a) other := by
  apply dual_optimal hg
  constructor
  · intro e he
    by_cases ea : e = a
    · subst e
      simp [incrementCapacity, saturated] at he
    · by_cases eq : g e = f e
      · exact unchangedForward e ea (by simpa [incrementCapacity, ea, eq] using he)
      · have zero := tight e ea eq
        exact zero.ge
  · intro e he
    by_cases ea : e = a
    · subst e
      exact newcost
    · by_cases eq : g e = f e
      · exact unchangedBackward e ea (eq ▸ he)
      · have zero := tight e ea eq
        exact zero.le

end GyoriLovasz.Flow
