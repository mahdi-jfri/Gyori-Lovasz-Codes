import GyoriLovasz.RuntimeWordRepair
import GyoriLovasz.RuntimeScaling
import Mathlib.Tactic.GCongr

namespace GyoriLovasz.Flow
open Binary

def doubleWords (s : WordResidual n m) : Costed.Computation (WordResidual n m) :=
  let caps := Costed.tabulate m (fun e => (false :: s.capacity[e.val], 3))
  let flow := Costed.tabulate m (fun e => (false :: s.flow[e.val], 3))
  ({s with capacity := caps.1, flow := flow.1}, caps.2 + flow.2 + 1)

def incrementWords (s : WordResidual n m) (a : Fin m) : Costed.Computation (WordResidual n m) :=
  let repaired := wordRepair s a
  let caps := Costed.tabulate m (fun e =>
    if e = a then
      let added := addCarry s.capacity[e.val] [] true
      (added.1, added.2 + 5)
    else (s.capacity[e.val], 5))
  ({s with capacity := caps.1, flow := repaired.1.1, potential := repaired.1.2}, repaired.2 + caps.2 + 1)

def wordOp (s : WordResidual n m) : ScalingOp m → Costed.Computation (WordResidual n m)
  | .double => doubleWords s
  | .increment a => incrementWords s a

def WordInvariant (s : WordResidual n m) : Prop :=
  Feasible (decodeNetwork s) (decodeFlow s) ∧ DualFeasible (decodeNetwork s) (decodeFlow s) (decodePotential s)

theorem doubleWords_network (s : WordResidual n m) :
    decodeNetwork (doubleWords s).1 = doubleCapacity (decodeNetwork s) := by
  simp [decodeNetwork, doubleWords, Costed.tabulate_value, doubleCapacity, value]

theorem doubleWords_flow (s : WordResidual n m) :
    decodeFlow (doubleWords s).1 = doubleFlow (decodeFlow s) := by
  funext e
  simp [decodeFlow, doubleWords, Costed.tabulate_value, doubleFlow, value]

theorem doubleWords_invariant (s : WordResidual n m) (inv : WordInvariant s) :
    WordInvariant (doubleWords s).1 := by
  unfold WordInvariant
  rw [doubleWords_network, doubleWords_flow]
  exact ⟨double_feasible inv.1, double_dual inv.2⟩

theorem incrementWords_network (s : WordResidual n m) (a : Fin m) :
    decodeNetwork (incrementWords s a).1 = incrementCapacity (decodeNetwork s) a := by
  simp only [decodeNetwork, incrementWords, Costed.tabulate_value, incrementCapacity]
  congr 1
  funext e
  split <;> simp [addCarry_correct, value]

theorem incrementWords_invariant (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (inv : WordInvariant s) (a : Fin m) : WordInvariant (incrementWords s a).1 := by
  have h := wordRepair_correct s correct inv.1 inv.2 a
  unfold WordInvariant
  rw [incrementWords_network]
  exact h

theorem wordOp_codes (s : WordResidual n m) (correct : VertexCodesCorrect s) (op : ScalingOp m) :
    VertexCodesCorrect (wordOp s op).1 := by
  cases op <;> exact correct

theorem wordOp_invariant (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (inv : WordInvariant s) (op : ScalingOp m) : WordInvariant (wordOp s op).1 := by
  cases op with
  | double => exact doubleWords_invariant s inv
  | increment a => exact incrementWords_invariant s correct inv a

theorem doubleWords_cost (s : WordResidual n m) :
    (doubleWords s).2 ≤ 4 * m * m + 18 * m + 7 := by
  have hc := Costed.tabulate_cost m (fun e => (false :: s.capacity[e.val], 3)) 3 (by intros; exact Nat.le_refl _)
  have hf := Costed.tabulate_cost m (fun e => (false :: s.flow[e.val], 3)) 3 (by intros; exact Nat.le_refl _)
  dsimp only [doubleWords]
  ring_nf at hc hf ⊢
  omega

theorem incrementWords_cost (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (B : Nat) (bound : WordResidualBound s B) (a : Fin m) :
    (incrementWords s a).2 ≤ repairBudget n m B + 2 * m * m + m * (7 * B + 13) + 4 := by
  have hr := wordRepair_cost s correct B bound a
  have hc := Costed.tabulate_cost m (fun e =>
    if e = a then
      let added := addCarry s.capacity[e.val] [] true
      (added.1, added.2 + 5)
    else (s.capacity[e.val], 5)) (7 * B + 7) (by
      intro e
      have hb := (bound.1 e).1
      dsimp only
      split
      · simp only [addCarry_steps, List.length_nil, Nat.max_zero]; omega
      · omega)
  dsimp only at hc
  dsimp only [incrementWords]
  have eq : 7 * B + 7 + 6 = 7 * B + 13 := by omega
  rw [eq] at hc
  omega

def opBudget (n m B : Nat) := repairBudget n m B + 6 * m * m + m * (7 * B + 31) + 11

theorem wordOp_cost (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (B : Nat) (bound : WordResidualBound s B) (op : ScalingOp m) :
    (wordOp s op).2 ≤ opBudget n m B := by
  have eq : opBudget n m B = (4 * m * m + 18 * m + 7) +
      (repairBudget n m B + 2 * m * m + m * (7 * B + 13) + 4) := by unfold opBudget; ring
  rw [eq]
  cases op with
  | double => have h := doubleWords_cost s; exact Nat.le_trans h (Nat.le_add_right _ _)
  | increment a => have h := incrementWords_cost s correct B bound a; exact Nat.le_trans h (Nat.le_add_left _ _)

theorem wordOp_bounds (s : WordResidual n m) (correct : VertexCodesCorrect s)
    (B : Nat) (bound : WordResidualBound s B) (op : ScalingOp m) :
    WordResidualBound (wordOp s op).1 (B + n + 6) := by
  cases op with
  | double =>
    constructor
    · intro e
      have h := bound.1 e
      simp only [wordOp, doubleWords, Costed.tabulate_value, List.length_cons]
      exact ⟨by omega, by omega, by omega⟩
    · intro v
      have h := bound.2 v
      exact ⟨by dsimp only [wordOp, doubleWords]; omega, by dsimp only [wordOp, doubleWords]; omega⟩
  | increment a =>
    have hr := wordRepair_bounds s correct B bound a
    constructor
    · intro e
      have h := bound.1 e
      refine ⟨?_, hr.1 e, ?_⟩
      · simp only [wordOp, incrementWords, Costed.tabulate_value]
        split
        · have ha := addCarry_length s.capacity[e.val] [] true
          simp only [List.length_nil, Nat.max_zero] at ha
          exact Nat.le_trans ha (by omega)
        · exact Nat.le_trans h.1 (by omega)
      · exact Nat.le_trans h.2.2 (by omega)
    · intro v
      exact ⟨Nat.le_trans (bound.2 v).1 (by omega), hr.2 v⟩

theorem opBudget_mono (n m B C : Nat) (h : B ≤ C) : opBudget n m B ≤ opBudget n m C := by
  unfold opBudget repairBudget residualBuildBudget graphBudget distanceBudget routeBudget
    augmentBudget WordShortest.stepBudget WordPath.budget
  gcongr

def wordExecute : List (ScalingOp m) → WordResidual n m → Costed.Computation (WordResidual n m)
  | [], s => (s, 1)
  | op :: ops, s =>
    let next := wordOp s op
    let rest := wordExecute ops next.1
    (rest.1, next.2 + rest.2 + 1)

theorem wordExecute_invariant (ops : List (ScalingOp m)) (s : WordResidual n m)
    (correct : VertexCodesCorrect s) (inv : WordInvariant s) :
    WordInvariant (wordExecute ops s).1 := by
  induction ops generalizing s with
  | nil => exact inv
  | cons op ops ih => exact ih _ (wordOp_codes s correct op) (wordOp_invariant s correct inv op)

theorem wordExecute_bounds (ops : List (ScalingOp m)) (s : WordResidual n m)
    (correct : VertexCodesCorrect s) (B : Nat) (bound : WordResidualBound s B) :
    WordResidualBound (wordExecute ops s).1 (B + ops.length * (n + 6)) := by
  induction ops generalizing s B with
  | nil => simpa [wordExecute] using bound
  | cons op ops ih =>
    have h := ih _ (wordOp_codes s correct op) (B + n + 6) (wordOp_bounds s correct B bound op)
    simpa only [wordExecute, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using h

theorem wordExecute_cost (ops : List (ScalingOp m)) (s : WordResidual n m)
    (correct : VertexCodesCorrect s) (B : Nat) (bound : WordResidualBound s B) :
    (wordExecute ops s).2 ≤ ops.length * (opBudget n m (B + ops.length * (n + 6)) + 1) + 1 := by
  induction ops generalizing s B with
  | nil => simp [wordExecute]
  | cons op ops ih =>
    have hr := ih _ (wordOp_codes s correct op) (B + n + 6) (wordOp_bounds s correct B bound op)
    have hc := wordOp_cost s correct B bound op
    have eq : B + n + 6 + ops.length * (n + 6) = B + (ops.length + 1) * (n + 6) := by ring
    rw [eq] at hr
    have hm := opBudget_mono n m B (B + (ops.length + 1) * (n + 6)) (by omega)
    simp only [Nat.add_mul, Nat.one_mul] at hr hm
    simp only [wordExecute, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

def zeroWords (s : WordResidual n m) : Costed.Computation (WordResidual n m) :=
  let zeros := Costed.tabulate m (fun _ => (([] : List Bool), 2))
  let pots := Costed.tabulate n (fun _ => ((⟨false, []⟩ : SignedWord), 2))
  ({s with capacity := zeros.1, flow := zeros.1, potential := pots.1}, zeros.2 + pots.2 + 1)

theorem zeroWords_codes (s : WordResidual n m) (correct : VertexCodesCorrect s) :
    VertexCodesCorrect (zeroWords s).1 := correct

theorem zeroWords_invariant (s : WordResidual n m) : WordInvariant (zeroWords s).1 := by
  simp [WordInvariant, Feasible, DualFeasible, decodeNetwork, decodeFlow, decodePotential,
    zeroWords, Costed.tabulate_value, value]

theorem zeroWords_bounds (s : WordResidual n m) (B : Nat)
    (costBound : ∀ e : Fin m, s.cost[e.val].digits.length ≤ B)
    (codeBound : ∀ v : Fin n, s.vertexCode[v.val].length ≤ B) :
    WordResidualBound (zeroWords s).1 B := by
  constructor
  · intro e; simp [zeroWords, Costed.tabulate_value, costBound e]
  · intro v; simp [zeroWords, Costed.tabulate_value, codeBound v]

theorem zeroWords_cost (s : WordResidual n m) :
    (zeroWords s).2 ≤ 2 * m * m + 8 * m + 2 * n * n + 8 * n + 7 := by
  have hz := Costed.tabulate_cost m (fun _ => (([] : List Bool), 2)) 2 (by intros; exact Nat.le_refl _)
  have hp := Costed.tabulate_cost n (fun _ => ((⟨false, []⟩ : SignedWord), 2)) 2 (by intros; exact Nat.le_refl _)
  dsimp only [zeroWords]
  omega

theorem wordOp_network (s : WordResidual n m) (op : ScalingOp m) :
    decodeNetwork (wordOp s op).1 =
      {decodeNetwork s with capacity := capacityOp (decodeNetwork s).capacity op} := by
  cases op with
  | double => exact doubleWords_network s
  | increment a => exact incrementWords_network s a

theorem wordExecute_network (ops : List (ScalingOp m)) (s : WordResidual n m) :
    decodeNetwork (wordExecute ops s).1 =
      {decodeNetwork s with capacity := capacityProgram ops (decodeNetwork s).capacity} := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    simp only [wordExecute, ih, wordOp_network, capacityProgram]

theorem wordExecute_zero_optimal (ops : List (ScalingOp m)) (s : WordResidual n m)
    (correct : VertexCodesCorrect s) :
    let output := (wordExecute ops (zeroWords s).1).1
    let target := {decodeNetwork s with capacity := capacityProgram ops (fun _ => 0)}
    Feasible target (decodeFlow output) ∧
      ∀ other, Feasible target other → totalCost target (decodeFlow output) ≤ totalCost target other := by
  have inv := wordExecute_invariant ops _ (zeroWords_codes s correct) (zeroWords_invariant s)
  have net := wordExecute_network ops (zeroWords s).1
  have znet : decodeNetwork (zeroWords s).1 = {decodeNetwork s with capacity := fun _ => 0} := by
    simp [decodeNetwork, zeroWords, Costed.tabulate_value, value]
  rw [znet] at net
  unfold WordInvariant at inv
  rw [net] at inv
  exact ⟨inv.1, dual_optimal inv.1 inv.2⟩

end GyoriLovasz.Flow

