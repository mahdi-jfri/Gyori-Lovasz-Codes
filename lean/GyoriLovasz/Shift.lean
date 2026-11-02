import GyoriLovasz.InputBridge
import GyoriLovasz.Reassignment

namespace GyoriLovasz

noncomputable def nonterminals (roots : Fin k → Fin n) : List (Fin n) := by
  classical
  exact (List.finRange n).filter (fun v => decide (¬RootSet roots v))

theorem mem_nonterminals {roots : Fin k → Fin n} {v : Fin n} :
    v ∈ nonterminals roots ↔ ¬RootSet roots v := by
  classical
  simp [nonterminals, mem_finRange v]

theorem nonterminals_nodup (roots : Fin k → Fin n) : (nonterminals roots).Nodup := by
  classical
  exact List.Pairwise.filter _ (finRange_nodup n)

def FeasibleAssignment (E : Fin n → Fin n → Prop) (roots : Fin k → Fin n)
    (capacity : Fin k → Nat) (label : Fin n → Fin k) : Prop :=
  (∀ v, ∀ hv : ¬RootSet roots v, Essential E (RootSet roots) v hv (roots (label v))) ∧
  (∀ i, countTrue (nonterminals roots) (fun v => label v = i) = capacity i)

noncomputable def vertexCost (E : Fin n → Fin n → Prop) (roots : Fin k → Fin n)
    (p q : Fin k → Fin n) (label : Fin n → Fin k) (v : Fin n) : Nat := by
  classical
  exact if hv : ¬RootSet roots v then
    criticalCost E (RootSet roots) v hv p q (roots (label v)) else 0

noncomputable def assignmentPotential (E : Fin n → Fin n → Prop)
    (roots p q : Fin k → Fin n) (label : Fin n → Fin k) : Nat :=
  sumValues (nonterminals roots) (vertexCost E roots p q label)

theorem assignmentPotential_bound (E : Fin n → Fin n → Prop)
    (roots p q : Fin k → Fin n) (label : Fin n → Fin k) :
    assignmentPotential E roots p q label ≤ (nonterminals roots).length * k := by
  classical
  have h : ∀ v, v ∈ nonterminals roots → vertexCost E roots p q label v ≤ k := by
    intro v hv
    have hnt := mem_nonterminals.mp hv
    simpa [vertexCost, hnt] using criticalCost_le E (RootSet roots) v hnt p q (roots (label v))
  have hb := sumValues_mono (nonterminals roots) h
  rw [sumValues_const] at hb
  exact hb

/-- Full simultaneous reassignment step: construct a nonempty union of cycles,
preserve feasibility and every capacity, and strictly decrease total potential.
The pre-terminal matching and critical blockers are explicit input data. -/
theorem shift_improves {E : Fin n → Fin n → Prop}
    {roots p q blocker : Fin k → Fin n} {capacity : Fin k → Nat}
    {label : Fin n → Fin k} (hk : 0 < k)
    (feasible : FeasibleAssignment E roots capacity label)
    (matching : ∀ i, E (p i) (roots i))
    (secondary : ∀ i, q i ≠ roots i)
    (distinct : ∀ i j, i ≠ j → p i ≠ p j)
    (blocker_nonterminal : ∀ i, ¬RootSet roots (blocker i))
    (blocked : ∀ i, Critical E (RootSet roots) (blocker i) (blocker_nonterminal i)
      (p i) (q i) (roots (label (blocker i)))) :
    ∃ improved : Fin n → Fin k,
      FeasibleAssignment E roots capacity improved ∧
      assignmentPotential E roots p q improved < assignmentPotential E roots p q label := by
  classical
  obtain ⟨selected, hne, hnd, hperm⟩ := exists_terminal_cycles (fun i => label (blocker i)) hk
  let improved := reassign selected blocker label
  have mapnd : (selected.map (fun i => label (blocker i))).Nodup := hperm.symm.nodup hnd
  have inj : ∀ a, a ∈ selected → ∀ b, b ∈ selected → blocker a = blocker b → a = b := by
    intro a ha b hb he
    exact map_nodup_injOn mapnd ha hb (congrArg label he)
  have moved_label (i : Fin k) (hi : i ∈ selected) : improved (blocker i) = i :=
    reassign_selected inj hi
  have unchanged (v : Fin n) (hv : v ∉ selected.map blocker) : improved v = label v :=
    reassign_unchanged hv
  have improves (i : Fin k) (hi : i ∈ selected) :
      vertexCost E roots p q improved (blocker i) < vertexCost E roots p q label (blocker i) := by
    have localDecrease := reassignment_cost_decreases (blocker_nonterminal i)
      (show RootSet roots (roots (label (blocker i))) from ⟨_, rfl⟩)
      p q roots i ⟨i, rfl⟩ (matching i) (secondary i) (distinct i) (blocked i)
    simpa [vertexCost, blocker_nonterminal i, moved_label i hi] using localDecrease
  refine ⟨improved, ⟨?_, ?_⟩, ?_⟩
  · intro v hv
    by_cases touched : v ∈ selected.map blocker
    · obtain ⟨i, hi, he⟩ := List.mem_map.mp touched
      subst v
      rw [moved_label i hi]
      exact finite_criticality_assignable (blocker_nonterminal i) ⟨i, rfl⟩
        (matching i) (secondary i) (blocked i)
    · rw [unchanged v touched]
      exact feasible.1 v hv
  · intro i
    have hc := reassignment_preserves_counts (nonterminals roots) selected blocker label
      (nonterminals_nodup roots) hnd
      (fun j _ => mem_nonterminals.mpr (blocker_nonterminal j)) hperm i
    exact hc.trans (feasible.2 i)
  · apply sumValues_strict
    · intro v _
      by_cases touched : v ∈ selected.map blocker
      · obtain ⟨i, hi, he⟩ := List.mem_map.mp touched
        subst v
        exact Nat.le_of_lt (improves i hi)
      · have he := unchanged v touched
        simp [vertexCost, he]
    · obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil selected hne
      exact ⟨blocker i, mem_nonterminals.mpr (blocker_nonterminal i), improves i hi⟩

/-- Existence version of the noncritical-edge step, given a matching.
Minimizing over assignments is noncomputable here; this theorem does not
claim an efficient implementation of that minimization. -/
theorem exists_noncritical_secondary {E : Fin n → Fin n → Prop}
    {roots p q : Fin k → Fin n} {capacity : Fin k → Nat}
    (hk : 0 < k) (exists_assignment : ∃ label, FeasibleAssignment E roots capacity label)
    (matching : ∀ i, E (p i) (roots i))
    (secondary : ∀ i, q i ≠ roots i)
    (distinct : ∀ i j, i ≠ j → p i ≠ p j) :
    ∃ label, FeasibleAssignment E roots capacity label ∧ ∃ i,
      ∀ v, ∀ hv : ¬RootSet roots v,
        ¬Critical E (RootSet roots) v hv (p i) (q i) (roots (label v)) := by
  classical
  have ex : ∃ m, ∃ label, FeasibleAssignment E roots capacity label ∧
      assignmentPotential E roots p q label = m := by
    obtain ⟨label, hf⟩ := exists_assignment
    exact ⟨_, label, hf, rfl⟩
  obtain ⟨m, ⟨label, hf, hm⟩, hmin⟩ := exists_minimal_nat _ ex
  refine ⟨label, hf, ?_⟩
  by_cases free : ∃ i, ∀ v, ∀ hv : ¬RootSet roots v,
      ¬Critical E (RootSet roots) v hv (p i) (q i) (roots (label v))
  · exact free
  · have witness : ∀ i, ∃ v, ∃ hv : ¬RootSet roots v,
        Critical E (RootSet roots) v hv (p i) (q i) (roots (label v)) := by
      intro i
      by_cases hw : ∃ v, ∃ hv : ¬RootSet roots v,
          Critical E (RootSet roots) v hv (p i) (q i) (roots (label v))
      · exact hw
      · exact False.elim (free ⟨i, fun v hv hc => hw ⟨v, hv, hc⟩⟩)
    let blocker := fun i => Classical.choose (witness i)
    have hblock : ∀ i, ∃ hv : ¬RootSet roots (blocker i),
        Critical E (RootSet roots) (blocker i) hv (p i) (q i) (roots (label (blocker i))) :=
      fun i => Classical.choose_spec (witness i)
    let hnt := fun i => (hblock i).choose
    have hcrit := fun i => (hblock i).choose_spec
    obtain ⟨better, hb, hlt⟩ := shift_improves (blocker := blocker) hk hf matching secondary distinct hnt hcrit
    have lower := hmin _ ⟨better, hb, rfl⟩
    omega

end GyoriLovasz
