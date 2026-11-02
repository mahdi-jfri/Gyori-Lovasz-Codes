import GyoriLovasz.RuntimeWordMaxFlow

namespace GyoriLovasz.VertexNetwork
open Flow
open scoped BigOperators

def inside (v : Fin n) : Fin (n + n + 1) := (Fin.castAdd n v).succ
def outside (v : Fin n) : Fin (n + n + 1) := (Fin.natAdd n v).succ

def network (E : Fin n → Fin n → Bool) (T : Fin n → Bool) : Network (n + n + 1) (n + (n * n + n)) where
  tail := Fin.addCases inside (Fin.addCases (fun a => outside (finProdFinEquiv.symm a).1) outside)
  head := Fin.addCases outside (Fin.addCases (fun a => inside (finProdFinEquiv.symm a).2) (fun _ => 0))
  capacity := Fin.addCases (fun _ => 1)
    (Fin.addCases (fun a => if E (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 then n + 1 else 0)
      (fun v => if T v then n + 1 else 0))
  cost := fun _ => 0

def unitArc (v : Fin n) : Fin (n + (n * n + n)) := Fin.castAdd (n * n + n) v
def graphArc (u v : Fin n) : Fin (n + (n * n + n)) :=
  Fin.natAdd n (Fin.castAdd n (finProdFinEquiv (u, v)))
def terminalArc (v : Fin n) : Fin (n + (n * n + n)) := Fin.natAdd n (Fin.natAdd (n * n) v)

@[simp] theorem unitArc_tail (E : Fin n → Fin n → Bool) (T : Fin n → Bool) (v : Fin n) :
    (network E T).tail (unitArc v) = inside v := by simp [network, unitArc]
@[simp] theorem unitArc_head (E : Fin n → Fin n → Bool) (T : Fin n → Bool) (v : Fin n) :
    (network E T).head (unitArc v) = outside v := by simp [network, unitArc]
@[simp] theorem unitArc_capacity (E : Fin n → Fin n → Bool) (T : Fin n → Bool) (v : Fin n) :
    (network E T).capacity (unitArc v) = 1 := by simp [network, unitArc]

@[simp] theorem graphArc_tail (E : Fin n → Fin n → Bool) (T : Fin n → Bool) (u v : Fin n) :
    (network E T).tail (graphArc u v) = outside u := by simp only [network, graphArc, Fin.addCases_left, Fin.addCases_right, Equiv.symm_apply_apply]
@[simp] theorem graphArc_head (E : Fin n → Fin n → Bool) (T : Fin n → Bool) (u v : Fin n) :
    (network E T).head (graphArc u v) = inside v := by simp only [network, graphArc, Fin.addCases_left, Fin.addCases_right, Equiv.symm_apply_apply]
@[simp] theorem graphArc_capacity (E : Fin n → Fin n → Bool) (T : Fin n → Bool) (u v : Fin n) :
    (network E T).capacity (graphArc u v) = if E u v then n + 1 else 0 := by simp only [network, graphArc, Fin.addCases_left, Fin.addCases_right, Equiv.symm_apply_apply]

@[simp] theorem terminalArc_tail (E : Fin n → Fin n → Bool) (T : Fin n → Bool) (v : Fin n) :
    (network E T).tail (terminalArc v) = outside v := by simp [network, terminalArc]
@[simp] theorem terminalArc_head (E : Fin n → Fin n → Bool) (T : Fin n → Bool) (v : Fin n) :
    (network E T).head (terminalArc v) = 0 := by simp [network, terminalArc]
@[simp] theorem terminalArc_capacity (E : Fin n → Fin n → Bool) (T : Fin n → Bool) (v : Fin n) :
    (network E T).capacity (terminalArc v) = if T v then n + 1 else 0 := by simp [network, terminalArc]

theorem crossing_capacity_le (G : Network n m) (S : Fin n → Bool) (e : Fin m)
    (tail : S (G.tail e) = true) (head : S (G.head e) = false) : G.capacity e ≤ cutCapacity G S := by
  have h := Finset.single_le_sum (fun e (_ : e ∈ (Finset.univ : Finset (Fin m))) =>
    Nat.zero_le (if S (G.tail e) && !S (G.head e) then G.capacity e else 0)) (Finset.mem_univ e)
  simpa [cutCapacity, tail, head] using h

theorem small_cut_graph_closed (E : Fin n → Fin n → Bool) (T : Fin n → Bool)
    (S : Fin (n + n + 1) → Bool) (small : cutCapacity (network E T) S ≤ n)
    (u v : Fin n) (edge : E u v = true) (hu : S (outside u) = true) : S (inside v) = true := by
  cases hv : S (inside v) with
  | true => rfl
  | false =>
    have h := crossing_capacity_le (network E T) S (graphArc u v) (by simpa using hu) (by simpa using hv)
    simp [edge] at h
    omega

theorem small_cut_terminal_out (E : Fin n → Fin n → Bool) (T : Fin n → Bool)
    (S : Fin (n + n + 1) → Bool) (small : cutCapacity (network E T) S ≤ n)
    (sink : S 0 = false) (v : Fin n) (terminal : T v = true) : S (outside v) = false := by
  cases hv : S (outside v) with
  | false => rfl
  | true =>
    have h := crossing_capacity_le (network E T) S (terminalArc v) (by simpa using hv) (by simpa using sink)
    simp [terminal] at h
    omega

def decodeCut (S : Fin (n + n + 1) → Bool) (v : Fin n) : Side :=
  if S (outside v) then .right else if S (inside v) then .sep else .left

theorem decodeCut_valid (E : Fin n → Fin n → Bool) (T : Fin n → Bool) (v : Fin n)
    (S : Fin (n + n + 1) → Bool) (source : S (outside v) = true) (sink : S 0 = false)
    (small : cutCapacity (network E T) S ≤ n) :
    Valid (fun x y => E x y = true) (fun t => T t = true) v (decodeCut S) := by
  constructor
  · simp [decodeCut, source]
  · intro t ht
    have h := small_cut_terminal_out E T S small sink t ht
    simp [decodeCut, h]
    split <;> decide
  · intro x y he hx
    have hx' : S (outside x) = true := by
      cases ho : S (outside x) <;> cases hi : S (inside x) <;> simp_all [decodeCut]
    have hy := small_cut_graph_closed E T S small x y he hx'
    simp [decodeCut, hy]
    split <;> decide

def encodeCut (C : Cut (Fin n)) : Fin (n + n + 1) → Bool :=
  Fin.cases false (Fin.addCases (fun v => decide (C v ≠ .left)) (fun v => decide (C v = .right)))

@[simp] theorem encodeCut_inside (C : Cut (Fin n)) (v : Fin n) :
    encodeCut C (inside v) = decide (C v ≠ .left) := by
  simp only [encodeCut, inside, Fin.cases_succ, Fin.addCases_left]
@[simp] theorem encodeCut_outside (C : Cut (Fin n)) (v : Fin n) :
    encodeCut C (outside v) = decide (C v = .right) := by
  simp only [encodeCut, outside, Fin.cases_succ, Fin.addCases_right]
@[simp] theorem encodeCut_sink (C : Cut (Fin n)) : encodeCut C 0 = false := rfl

theorem size_list_sum (xs : List α) (C : Cut α) : size xs C = (xs.map (fun x => (C x).weight)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [size, ih]

theorem size_fin_sum (C : Cut (Fin n)) : size (List.finRange n) C = ∑ v, (C v).weight := by
  simp [size_list_sum, List.finRange, List.map_ofFn, List.sum_ofFn]

theorem encodeCut_capacity (E : Fin n → Fin n → Bool) (T : Fin n → Bool) (v : Fin n)
    (C : Cut (Fin n)) (valid : Valid (fun x y => E x y = true) (fun t => T t = true) v C) :
    cutCapacity (network E T) (encodeCut C) = size (List.finRange n) C := by
  have node (x : Fin n) :
      (if encodeCut C (inside x) && !encodeCut C (outside x) then 1 else 0) = (C x).weight := by
    simp only [encodeCut_inside, encodeCut_outside]
    cases C x <;> rfl
  have graph (a : Fin (n * n)) :
      (if encodeCut C (outside (finProdFinEquiv.symm a).1) &&
          !encodeCut C (inside (finProdFinEquiv.symm a).2) then
        (if E (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 then n + 1 else 0) else 0) = 0 := by
    by_cases edge : E (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 = true
    · have h := valid.no_cross _ _ edge
      simp only [encodeCut_inside, encodeCut_outside]
      cases hx : C (finProdFinEquiv.symm a).1 <;> cases hy : C (finProdFinEquiv.symm a).2 <;>
        simp_all
    · simp only [if_neg edge, ite_self]
  have terminal (x : Fin n) :
      (if encodeCut C (outside x) && !encodeCut C 0 then (if T x then n + 1 else 0) else 0) = 0 := by
    by_cases ht : T x = true
    · have h := valid.terminals x ht
      simp [h]
    · simp [ht]
  simp only [cutCapacity, Fin.sum_univ_add, network, Fin.addCases_left, Fin.addCases_right,
    node, graph, terminal, Finset.sum_const_zero, add_zero]
  exact (size_fin_sum C).symm

theorem decodeCut_size_le (E : Fin n → Fin n → Bool) (T : Fin n → Bool)
    (S : Fin (n + n + 1) → Bool) : size (List.finRange n) (decodeCut S) ≤ cutCapacity (network E T) S := by
  have node (x : Fin n) :
      (decodeCut S x).weight = if S (inside x) && !S (outside x) then 1 else 0 := by
    cases ho : S (outside x) <;> cases hi : S (inside x) <;> simp [decodeCut, ho, hi, Side.weight]
  rw [size_fin_sum]
  simp only [node, cutCapacity, Fin.sum_univ_add, network, Fin.addCases_left, Fin.addCases_right]
  omega

theorem valid_size_le_n (C : Cut (Fin n)) : size (List.finRange n) C ≤ n := by
  rw [size_fin_sum]
  calc
    _ ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum (fun v _ => by cases C v <;> simp [Side.weight])
    _ = n := by simp

theorem minimum_network_decodes (E : Fin n → Fin n → Bool) (T : Fin n → Bool)
    (v : Fin n) (nonterminal : T v = false) (S : Fin (n + n + 1) → Bool)
    (source : S (outside v) = true) (sink : S 0 = false)
    (minimum : ∀ U, U (outside v) = true → U 0 = false →
      cutCapacity (network E T) S ≤ cutCapacity (network E T) U) :
    Minimum (List.finRange n) (fun x y => E x y = true) (fun t => T t = true) v (decodeCut S) := by
  let C : Cut (Fin n) := fun x => if T x then .sep else .right
  have valid : Valid (fun x y => E x y = true) (fun t => T t = true) v C := by
    constructor
    · simp [C, nonterminal]
    · intro t ht; simp [C, ht]
    · intro x y he hx; simp [C]; split <;> decide
  have upper := minimum (encodeCut C) (by simp [valid.source]) rfl
  rw [encodeCut_capacity E T v C valid] at upper
  have small := Nat.le_trans upper (valid_size_le_n C)
  refine ⟨decodeCut_valid E T v S source sink small, ?_⟩
  intro D hd
  have min := minimum (encodeCut D) (by simp [hd.source]) rfl
  rw [encodeCut_capacity E T v D hd] at min
  exact Nat.le_trans (decodeCut_size_le E T S) min

theorem minimum_network_rank (E : Fin n → Fin n → Bool) (T : Fin n → Bool)
    (v : Fin n) (nonterminal : T v = false) (S : Fin (n + n + 1) → Bool)
    (source : S (outside v) = true) (sink : S 0 = false)
    (minimum : ∀ U, U (outside v) = true → U 0 = false →
      cutCapacity (network E T) S ≤ cutCapacity (network E T) U) :
    HasRank (List.finRange n) (fun x y => E x y = true) (fun t => T t = true) v
      (cutCapacity (network E T) S) := by
  have hd := minimum_network_decodes E T v nonterminal S source sink minimum
  have upper := decodeCut_size_le E T S
  have lower := minimum (encodeCut (decodeCut S)) (by simp [hd.1.source]) rfl
  rw [encodeCut_capacity E T v (decodeCut S) hd.1] at lower
  refine ⟨⟨decodeCut S, hd.1, by omega⟩, ?_⟩
  intro D valid
  have h := minimum (encodeCut D) (by simp [valid.source]) rfl
  rwa [encodeCut_capacity E T v D valid] at h

end GyoriLovasz.VertexNetwork

