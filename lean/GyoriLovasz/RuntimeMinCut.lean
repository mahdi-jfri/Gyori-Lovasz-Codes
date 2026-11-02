import GyoriLovasz.RuntimeMaxFlow

namespace GyoriLovasz.Flow
open scoped BigOperators

theorem st_potential_sum (G : Network n m) (source sink : Fin n) (f : Fin m → Nat)
    (amount : Nat) (feasible : STFeasible G source sink f amount) (p : Fin n → Int) :
    (∑ e, (p (G.tail e) - p (G.head e)) * (f e : Int)) =
      (p source - p sink) * (amount : Int) := by
  calc
    _ = ∑ v, p v * ((∑ e, if G.tail e = v then (f e : Int) else 0) -
        ∑ e, if G.head e = v then (f e : Int) else 0) := by
      simp only [sub_mul, Finset.sum_sub_distrib, mul_sub]
      rw [endpoint_sum G.tail p, endpoint_sum G.head p]
    _ = ∑ v, p v * ((if source = v then (amount : Int) else 0) -
        (if sink = v then (amount : Int) else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      have h := feasible.2 v
      congr 1
      omega
    _ = _ := by
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero]
      simp [sub_mul]

def cutCapacity (G : Network n m) (S : Fin n → Bool) : Nat :=
  ∑ e, if S (G.tail e) && !S (G.head e) then G.capacity e else 0

def cutIndicator (S : Fin n → Bool) (v : Fin n) : Int := if S v then 1 else 0

theorem flow_le_cut (G : Network n m) (source sink : Fin n) (f : Fin m → Nat)
    (amount : Nat) (feasible : STFeasible G source sink f amount)
    (S : Fin n → Bool) (hs : S source = true) (ht : S sink = false) : amount ≤ cutCapacity G S := by
  have balance := st_potential_sum G source sink f amount feasible (cutIndicator S)
  simp only [cutIndicator, hs, ht, if_true, Bool.false_eq_true, if_false] at balance
  have upper : (∑ e, ((if S (G.tail e) then 1 else 0) - (if S (G.head e) then 1 else 0)) * (f e : Int)) ≤
      ∑ e, (if S (G.tail e) && !S (G.head e) then (G.capacity e : Int) else 0) := by
    apply Finset.sum_le_sum
    intro e _
    have cap := feasible.1 e
    cases h₁ : S (G.tail e) <;> cases h₂ : S (G.head e) <;> simp <;> omega
  have cast : (∑ e, (if S (G.tail e) && !S (G.head e) then (G.capacity e : Int) else 0)) =
      (cutCapacity G S : Int) := by simp [cutCapacity]
  rw [cast] at upper
  simp only [sub_zero, one_mul] at balance
  omega

theorem saturated_cut_eq (G : Network n m) (source sink : Fin n) (f : Fin m → Nat)
    (amount : Nat) (feasible : STFeasible G source sink f amount)
    (S : Fin n → Bool) (hs : S source = true) (ht : S sink = false)
    (forward : ∀ e, S (G.tail e) = true → S (G.head e) = false → f e = G.capacity e)
    (backward : ∀ e, S (G.tail e) = false → S (G.head e) = true → f e = 0) :
    amount = cutCapacity G S := by
  have balance := st_potential_sum G source sink f amount feasible (cutIndicator S)
  have eq : (∑ e, (cutIndicator S (G.tail e) - cutIndicator S (G.head e)) * (f e : Int)) =
      (cutCapacity G S : Int) := by
    simp only [cutCapacity, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro e _
    cases h₁ : S (G.tail e) <;> cases h₂ : S (G.head e) <;>
      simp [cutIndicator, h₁, h₂, forward e, backward e]
  rw [eq] at balance
  simp [cutIndicator, hs, ht] at balance
  omega

/-- A threshold of the computed dual potential supplies a minimum cut.
The return capacity is strictly above the sum of original capacities, so the
return arc is unsaturated and forces the source/sink potentials to separate. -/
theorem dual_minimum_cut (G : Network n m) (source sink : Fin n) (distinct : source ≠ sink)
    (limit : Nat) (large : (∑ e, G.capacity e) < limit) (f : Fin (m + 1) → Nat)
    (p : Fin n → Int) (feasible : Feasible (throughputNetwork G source sink limit) f)
    (dual : DualFeasible (throughputNetwork G source sink limit) f p) :
    let S := fun v => decide (p v ≤ p source)
    S source = true ∧ S sink = false ∧ cutCapacity G S = f 0 ∧
      ∀ T, T source = true → T sink = false → cutCapacity G S ≤ cutCapacity G T := by
  have hf : STFeasible G source sink (fun e => f e.succ) (f 0) := by
    have h := feasible
    rw [← closeFlow_restrict f] at h
    exact ((closeFlow_feasible G source sink limit _ _).mp h).2
  have amountBound := throughput_le_capacity_sum G source sink distinct _ _ hf
  have returnCost := dual.1 0 (show f 0 < (throughputNetwork G source sink limit).capacity 0 by
    change f 0 < limit; omega)
  change 0 ≤ -1 + p sink - p source at returnCost
  let S := fun v => decide (p v ≤ p source)
  have hs : S source = true := by simp [S]
  have ht : S sink = false := by simp [S]; omega
  have eq : f 0 = cutCapacity G S := by
    apply saturated_cut_eq G source sink _ _ hf S hs ht
    · intro e he₁ he₂
      have cap := hf.1 e
      dsimp only at cap
      have h := dual.1 e.succ
      change f e.succ < G.capacity e → 0 ≤ 0 + p (G.tail e) - p (G.head e) at h
      simp only [S, decide_eq_true_eq, decide_eq_false_iff_not] at he₁ he₂
      omega
    · intro e he₁ he₂
      have h := dual.2 e.succ
      change 0 < f e.succ → 0 + p (G.tail e) - p (G.head e) ≤ 0 at h
      simp only [S, decide_eq_true_eq, decide_eq_false_iff_not] at he₁ he₂
      omega
  exact ⟨hs, ht, eq.symm, fun T hTs hTt => eq ▸ flow_le_cut G source sink _ _ hf T hTs hTt⟩

end GyoriLovasz.Flow
