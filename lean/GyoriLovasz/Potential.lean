import GyoriLovasz.FiniteGraph

namespace GyoriLovasz

noncomputable def countTrue (xs : List α) (P : α → Prop) : Nat := by
  classical
  exact match xs with
  | [] => 0
  | x :: rest => (if P x then 1 else 0) + countTrue rest P

theorem countTrue_le_length (xs : List α) (P : α → Prop) :
    countTrue xs P ≤ xs.length := by
  classical
  induction xs with
  | nil => simp [countTrue]
  | cons x xs ih =>
    by_cases h : P x <;> simp [countTrue, h] <;> omega

theorem countTrue_mono (xs : List α) {P Q : α → Prop}
    (h : ∀ x, x ∈ xs → P x → Q x) : countTrue xs P ≤ countTrue xs Q := by
  classical
  induction xs with
  | nil => simp [countTrue]
  | cons x xs ih =>
    have ht := ih (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    by_cases hp : P x <;> by_cases hq : Q x <;>
      simp_all [countTrue] <;> omega

theorem countTrue_strict (xs : List α) {P Q : α → Prop}
    (h : ∀ x, x ∈ xs → P x → Q x)
    (strict : ∃ x, x ∈ xs ∧ Q x ∧ ¬P x) : countTrue xs P < countTrue xs Q := by
  classical
  induction xs with
  | nil => simp at strict
  | cons x xs ih =>
    have ht : ∀ y, y ∈ xs → P y → Q y := fun y hy => h y (by simp [hy])
    obtain ⟨y, hy, hqy, hpy⟩ := strict
    rcases List.mem_cons.mp hy with he | he
    · subst y
      have le := countTrue_mono xs ht
      simp [countTrue, hqy, hpy]
      omega
    · have lt := ih ht ⟨y, he, hqy, hpy⟩
      have hx := h x (by simp)
      by_cases hp : P x <;> by_cases hq : Q x <;>
        simp_all [countTrue] <;> omega

noncomputable def criticalCost (E : Fin n → Fin n → Prop) (T : Fin n → Prop)
    (v : Fin n) (hv : ¬T v) (p q : Fin k → Fin n) (t : Fin n) : Nat :=
  countTrue (List.finRange k) (fun j => Critical E T v hv (p j) (q j) t)

theorem criticalCost_le (E : Fin n → Fin n → Prop) (T : Fin n → Prop)
    (v : Fin n) (hv : ¬T v) (p q : Fin k → Fin n) (t : Fin n) :
    criticalCost E T v hv p q t ≤ k := by
  have h := countTrue_le_length (List.finRange k)
    (fun j => Critical E T v hv (p j) (q j) t)
  simpa [criticalCost] using h

/-- A moved vertex's cost strictly decreases; this is the local numerical
ingredient for the paper's cycle potential. It does not assume transfer. -/
theorem reassignment_cost_decreases {E : Fin n → Fin n → Prop} {T : Fin n → Prop}
    {v t : Fin n} (hv : ¬T v) (ht : T t)
    (p q root : Fin k → Fin n) (i : Fin k)
    (hroot : T (root i)) (hedge : E (p i) (root i)) (hsecondary : q i ≠ root i)
    (hdistinct : ∀ j, i ≠ j → p i ≠ p j)
    (hcritical : Critical E T v hv (p i) (q i) t) :
    criticalCost E T v hv p q (root i) < criticalCost E T v hv p q t := by
  classical
  apply countTrue_strict
  · intro j _ hc
    by_cases hij : i = j
    · subst j
      exact False.elim (finite_secondary_not_critical hv hroot hedge hsecondary hc)
    · exact finite_transfer_criticality hv ht hroot hedge hsecondary
        (hdistinct j hij) hcritical hc
  · exact ⟨i, mem_finRange i, hcritical,
      finite_secondary_not_critical hv hroot hedge hsecondary⟩

/-- Pure termination arithmetic: a natural-valued potential cannot strictly
decrease for more transitions than its initial value. -/
theorem descending_sequence_bound (f : Nat → Nat) (steps : Nat)
    (h : ∀ i, i < steps → f (i + 1) < f i) : steps + f steps ≤ f 0 := by
  induction steps with
  | zero => simp
  | succ steps ih =>
    have first := ih (fun i hi => h i (by omega))
    have last := h steps (by omega)
    omega

theorem descending_steps_le (f : Nat → Nat) (steps : Nat)
    (h : ∀ i, i < steps → f (i + 1) < f i) : steps ≤ f 0 := by
  have hb := descending_sequence_bound f steps h
  omega

end GyoriLovasz
