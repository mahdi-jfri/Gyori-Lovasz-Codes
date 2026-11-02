import GyoriLovasz.Weighted

namespace GyoriLovasz

/-- A unit-token representation of a split assignment. This is finite even for
arbitrary integer weights, but its size can be exponential in their bit length. -/
def UnitSplitFeasible (E : Fin n → Fin n → Prop) (roots : Fin k → Fin n)
    (weight : Fin n → Nat) (capacity : Fin k → Nat)
    (origin : Fin m → Fin n) (assigned : Fin m → Fin k) : Prop :=
  (∀ u, ¬RootSet roots (origin u)) ∧
  (∀ u, ∀ hu : ¬RootSet roots (origin u), Essential E (RootSet roots) (origin u) hu (roots (assigned u))) ∧
  (∀ v, ¬RootSet roots v → countTrue (List.finRange m) (fun u => origin u = v) = weight v) ∧
  (∀ i, countTrue (List.finRange m) (fun u => assigned u = i) ≤ capacity i)

noncomputable def unitPotential (E : Fin n → Fin n → Prop) (roots p q : Fin k → Fin n)
    (origin : Fin m → Fin n) (assigned : Fin m → Fin k) : Nat :=
  sumValues (List.finRange m) (fun u => vertexCost E roots p q (fun _ => assigned u) (origin u))

/-- A weighted cycle shift. Different tokens may have the same origin vertex;
the proof never assumes that the underlying graph vertices are distinct. -/
theorem unit_shift_improves {E : Fin n → Fin n → Prop}
    {roots p q : Fin k → Fin n} {weight : Fin n → Nat} {capacity : Fin k → Nat}
    {origin : Fin m → Fin n} {assigned : Fin m → Fin k} {blocker : Fin k → Fin m}
    (hk : 0 < k) (feasible : UnitSplitFeasible E roots weight capacity origin assigned)
    (matching : ∀ i, E (p i) (roots i)) (secondary : ∀ i, q i ≠ roots i)
    (distinct : ∀ i j, i ≠ j → p i ≠ p j)
    (blocked : ∀ i, Critical E (RootSet roots) (origin (blocker i)) (feasible.1 (blocker i))
      (p i) (q i) (roots (assigned (blocker i)))) :
    ∃ improved, UnitSplitFeasible E roots weight capacity origin improved ∧
      unitPotential E roots p q origin improved < unitPotential E roots p q origin assigned := by
  classical
  obtain ⟨selected, hne, hnd, hperm⟩ := exists_terminal_cycles (fun i => assigned (blocker i)) hk
  let improved := reassign selected blocker assigned
  have mapnd : (selected.map (fun i => assigned (blocker i))).Nodup := hperm.symm.nodup hnd
  have inj : ∀ a, a ∈ selected → ∀ b, b ∈ selected → blocker a = blocker b → a = b := by
    intro a ha b hb he
    exact map_nodup_injOn mapnd ha hb (congrArg assigned he)
  have moved (i : Fin k) (hi : i ∈ selected) : improved (blocker i) = i := reassign_selected inj hi
  have unchanged (u : Fin m) (hu : u ∉ selected.map blocker) : improved u = assigned u :=
    reassign_unchanged hu
  have improves (i : Fin k) (hi : i ∈ selected) :
      vertexCost E roots p q (fun _ => improved (blocker i)) (origin (blocker i)) <
        vertexCost E roots p q (fun _ => assigned (blocker i)) (origin (blocker i)) := by
    have decrease := reassignment_cost_decreases (feasible.1 (blocker i))
      (show RootSet roots (roots (assigned (blocker i))) from ⟨_, rfl⟩)
      p q roots i ⟨i, rfl⟩ (matching i) (secondary i) (distinct i) (blocked i)
    simpa [vertexCost, feasible.1, moved i hi] using decrease
  refine ⟨improved, ⟨feasible.1, ?_, feasible.2.2.1, ?_⟩, ?_⟩
  · intro u hu
    by_cases touched : u ∈ selected.map blocker
    · obtain ⟨i, hi, he⟩ := List.mem_map.mp touched
      subst u
      rw [moved i hi]
      exact finite_criticality_assignable hu ⟨i, rfl⟩ (matching i) (secondary i) (blocked i)
    · rw [unchanged u touched]
      exact feasible.2.1 u hu
  · intro i
    have eq := reassignment_preserves_counts (List.finRange m) selected blocker assigned
      (finRange_nodup m) hnd (fun u _ => mem_finRange (blocker u)) hperm i
    exact eq.le.trans (feasible.2.2.2 i)
  · apply sumValues_strict
    · intro u _
      by_cases touched : u ∈ selected.map blocker
      · obtain ⟨i, hi, he⟩ := List.mem_map.mp touched
        subst u
        exact Nat.le_of_lt (improves i hi)
      · simp only [unchanged u touched, le_refl]
    · obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil selected hne
      exact ⟨blocker i, mem_finRange _, improves i hi⟩

/-- The weighted minimum-potential argument gives a secondary edge safe for
every positively assigned unit. No running-time claim is made for minimization. -/
theorem unit_noncritical_secondary {E : Fin n → Fin n → Prop}
    {roots p q : Fin k → Fin n} {weight : Fin n → Nat} {capacity : Fin k → Nat}
    {origin : Fin m → Fin n} (hk : 0 < k)
    (initial : ∃ assigned, UnitSplitFeasible E roots weight capacity origin assigned)
    (matching : ∀ i, E (p i) (roots i)) (secondary : ∀ i, q i ≠ roots i)
    (distinct : ∀ i j, i ≠ j → p i ≠ p j) :
    ∃ assigned, UnitSplitFeasible E roots weight capacity origin assigned ∧
      ∃ i, ∀ u, ∀ hu : ¬RootSet roots (origin u),
        ¬Critical E (RootSet roots) (origin u) hu (p i) (q i) (roots (assigned u)) := by
  classical
  have ex : ∃ z, ∃ a, UnitSplitFeasible E roots weight capacity origin a ∧
      unitPotential E roots p q origin a = z := by
    obtain ⟨a, ha⟩ := initial
    exact ⟨_, a, ha, rfl⟩
  obtain ⟨z, ⟨a, ha, hz⟩, minimal⟩ := exists_minimal_nat _ ex
  refine ⟨a, ha, ?_⟩
  by_cases free : ∃ i, ∀ u, ∀ hu : ¬RootSet roots (origin u),
      ¬Critical E (RootSet roots) (origin u) hu (p i) (q i) (roots (a u))
  · exact free
  · have witnesses : ∀ i, ∃ u, Critical E (RootSet roots) (origin u) (ha.1 u) (p i) (q i) (roots (a u)) := by
      intro i
      by_cases h : ∃ u, Critical E (RootSet roots) (origin u) (ha.1 u) (p i) (q i) (roots (a u))
      · exact h
      · exact False.elim (free ⟨i, fun u _ hc => h ⟨u, hc⟩⟩)
    let blocker := fun i => Classical.choose (witnesses i)
    have blocked := fun i => Classical.choose_spec (witnesses i)
    obtain ⟨better, hb, decrease⟩ := unit_shift_improves (blocker := blocker) hk ha matching secondary distinct blocked
    have lower := minimal _ ⟨better, hb, rfl⟩
    omega

end GyoriLovasz
