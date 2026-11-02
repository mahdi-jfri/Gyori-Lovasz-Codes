import GyoriLovasz.Shift

namespace GyoriLovasz

inductive RunUntil (step : α → α → Prop) (done : α → Prop) : α → Nat → α → Prop where
  | stop {x : α} (h : done x) : RunUntil step done x 0 x
  | next {x y z : α} {m : Nat} (h : step x y) (tail : RunUntil step done y m z) :
      RunUntil step done x (m + 1) z

theorem RunUntil.ends_done {step : α → α → Prop} {done : α → Prop}
    {x z : α} {m : Nat} (h : RunUntil step done x m z) : done z := by
  induction h with
  | stop hd => exact hd
  | next _ _ ih => exact ih

theorem runUntil_exists_bounded (step : α → α → Prop) (done : α → Prop)
    (measure : α → Nat)
    (progress : ∀ x, ¬done x → ∃ y, step x y)
    (decreases : ∀ x y, step x y → measure y < measure x) (start : α) :
    ∃ steps final, RunUntil step done start steps final ∧ steps ≤ measure start := by
  classical
  have aux : ∀ m, ∀ x, measure x = m →
      ∃ steps final, RunUntil step done x steps final ∧ steps ≤ measure x := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro x hx
      by_cases hd : done x
      · exact ⟨0, x, .stop hd, Nat.zero_le _⟩
      · obtain ⟨y, hxy⟩ := progress x hd
        have hm := decreases x y hxy
        obtain ⟨steps, final, run, bound⟩ := ih (measure y) (by omega) y rfl
        exact ⟨steps + 1, final, .next hxy run, by omega⟩
  exact aux (measure start) start rfl

/-- A whole inner reassignment run reaches a noncritical secondary edge in at
most (#nonterminals)*k improvements. This is a bound on the number of shifts,
not a time bound for an executable maximum-flow implementation. -/
theorem bounded_reassignment_run {E : Fin n → Fin n → Prop}
    {roots p q : Fin k → Fin n} {capacity : Fin k → Nat}
    (hk : 0 < k) (matching : ∀ i, E (p i) (roots i))
    (secondary : ∀ i, q i ≠ roots i)
    (distinct : ∀ i j, i ≠ j → p i ≠ p j)
    (start : {label : Fin n → Fin k // FeasibleAssignment E roots capacity label}) :
    ∃ steps, ∃ final : {label : Fin n → Fin k // FeasibleAssignment E roots capacity label},
      RunUntil
        (fun a b => assignmentPotential E roots p q b.val < assignmentPotential E roots p q a.val)
        (fun a => ∃ i, ∀ v, ∀ hv : ¬RootSet roots v,
          ¬Critical E (RootSet roots) v hv (p i) (q i) (roots (a.val v)))
        start steps final ∧ steps ≤ (nonterminals roots).length * k := by
  classical
  let State := {label : Fin n → Fin k // FeasibleAssignment E roots capacity label}
  let measure := fun a : State => assignmentPotential E roots p q a.val
  let step := fun a b : State => measure b < measure a
  let done := fun a : State => ∃ i, ∀ v, ∀ hv : ¬RootSet roots v,
    ¬Critical E (RootSet roots) v hv (p i) (q i) (roots (a.val v))
  have progress : ∀ a, ¬done a → ∃ b, step a b := by
    intro a hnot
    have witness : ∀ i, ∃ v, ∃ hv : ¬RootSet roots v,
        Critical E (RootSet roots) v hv (p i) (q i) (roots (a.val v)) := by
      intro i
      by_cases h : ∃ v, ∃ hv : ¬RootSet roots v,
          Critical E (RootSet roots) v hv (p i) (q i) (roots (a.val v))
      · exact h
      · exact False.elim (hnot ⟨i, fun v hv hc => h ⟨v, hv, hc⟩⟩)
    let blocker := fun i => Classical.choose (witness i)
    have hb := fun i => Classical.choose_spec (witness i)
    let nonterm := fun i => (hb i).choose
    have crit := fun i => (hb i).choose_spec
    obtain ⟨improved, hf, hlt⟩ := shift_improves (blocker := blocker)
      hk a.property matching secondary distinct nonterm crit
    exact ⟨⟨improved, hf⟩, hlt⟩
  obtain ⟨steps, final, hrun, bound⟩ := runUntil_exists_bounded step done measure progress
    (fun _ _ h => h) start
  have globalBound := assignmentPotential_bound E roots p q start.val
  exact ⟨steps, final, hrun, Nat.le_trans bound globalBound⟩

end GyoriLovasz
