import GyoriLovasz.RuntimeRoundAssignment

namespace GyoriLovasz
open TransportNetwork

def selectedIndex (selected : Vector Bool k) (nonempty : ∃ i : Fin k, selected[i.val] = true) :
    Costed.Computation (Fin k) :=
  let indices := Costed.enumerateIndices k
  let found := Costed.find (fun i => (selected[i.val], 1)) indices.1
  (found.1.get (by
    apply Option.isSome_iff_exists.mpr
    cases hs : found.1 with
    | some i => exact ⟨i, rfl⟩
    | none =>
      obtain ⟨i, hi⟩ := nonempty
      have no := hs
      rw [show found.1 = (indices.1.find? (fun i => selected[i.val])) from Costed.find_value _ _] at no
      have no' := List.find?_eq_none.mp no i (by simp [indices, Costed.enumerateIndices_value])
      simp [hi] at no'), indices.2 + found.2 + 2)

theorem selectedIndex_correct (selected : Vector Bool k) (nonempty : ∃ i : Fin k, selected[i.val] = true) :
    selected[(selectedIndex selected nonempty).1.val] = true := by
  have h : (Costed.find (fun i : Fin k => (selected[i.val], 1)) (Costed.enumerateIndices k).1).1 =
      some (selectedIndex selected nonempty).1 := by
    exact (Option.some_get _).symm
  rw [Costed.find_value] at h
  have yes := List.find?_some h
  exact yes

theorem selectedIndex_cost (selected : Vector Bool k) (nonempty : ∃ i : Fin k, selected[i.val] = true) :
    (selectedIndex selected nonempty).2 ≤ 2 * k * k + 6 * k + 4 := by
  have hi := Costed.enumerateIndices_cost k
  have hf := Costed.find_cost (fun i : Fin k => (selected[i.val], 1)) (Costed.enumerateIndices k).1 1
    (by intros; rfl)
  simp only [Costed.enumerateIndices_value, List.length_finRange] at hf
  dsimp only [selectedIndex]
  simp only [Costed.enumerateIndices_value]
  omega

theorem root_matching_iff (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k) :
    Saturates (fun i v => (rootNeighbors E roots).1[i.val][v.val]) (fun _ => true) ↔
      ∃ p : Fin k → Fin n, Function.Injective p ∧
        (∀ i, ¬RootSet (fun i => roots[i.val]) (p i)) ∧ (∀ i, E[(p i).val][roots[i.val].val] = true) := by
  constructor
  · rintro ⟨f, inj, edge⟩
    refine ⟨fun i => f ⟨i, rfl⟩, ?_, ?_, ?_⟩
    · intro i j he
      exact congrArg (fun a : {i : Fin k // true = true} => a.val) (inj he)
    · intro i; exact ((rootNeighbors_correct E roots i (f ⟨i, rfl⟩)).mp (edge ⟨i, rfl⟩)).1
    · intro i; exact ((rootNeighbors_correct E roots i (f ⟨i, rfl⟩)).mp (edge ⟨i, rfl⟩)).2
  · rintro ⟨p, inj, nt, edge⟩
    exact ⟨fun i => p i.val, fun i j he => Subtype.ext (inj he),
      fun i => (rootNeighbors_correct E roots i.val (p i.val)).mpr ⟨nt i.val, edge i.val⟩⟩

def allSelected (k : Nat) : Costed.Computation (Vector Bool k) := Costed.tabulate k (fun _ => (true, 1))

theorem allSelected_value (i : Fin k) : (allSelected k).1[i.val] = true := Costed.tabulate_value k _ i

def prunedSet (neighbors : Vector (Vector Bool n) k) : Costed.Computation (Vector Bool k) :=
  let selected := allSelected k
  let pruned := SaturationPrune.prune neighbors selected.1
  (pruned.1, selected.2 + pruned.2 + 1)

theorem prunedSet_spec (neighbors : Vector (Vector Bool n) k)
    (failure : ¬Saturates (fun i v => neighbors[i.val][v.val]) (fun _ => true)) :
    (∃ i : Fin k, (prunedSet neighbors).1[i.val] = true) ∧
      SaturationPrune.bad neighbors (SaturationPrune.selectedSet (prunedSet neighbors).1) = true ∧
      ∀ U, U ⊂ SaturationPrune.selectedSet (prunedSet neighbors).1 → SaturationPrune.bad neighbors U = false := by
  have hn : ¬Saturates (fun i v => neighbors[i.val][v.val]) (fun i => (allSelected k).1[i.val]) := by
    simpa only [allSelected_value] using failure
  have h := SaturationPrune.prune_correct neighbors (allSelected k).1 hn
  refine ⟨?_, h.2.2.1, h.2.2.2⟩
  obtain ⟨i, hi⟩ := h.1
  exact ⟨i, (SaturationPrune.mem_selectedSet _ i).mp hi⟩

theorem prunedSet_clear_saturates (neighbors : Vector (Vector Bool n) k)
    (failure : ¬Saturates (fun i v => neighbors[i.val][v.val]) (fun _ => true))
    (i : Fin k) (hi : (prunedSet neighbors).1[i.val] = true) :
    Saturates (fun a v => neighbors[a.val][v.val]) (fun a => (SaturationPrune.clear (prunedSet neighbors).1 i).1[a.val]) := by
  classical
  have h := prunedSet_spec neighbors failure
  have proper := Finset.erase_ssubset ((SaturationPrune.mem_selectedSet _ i).mpr hi)
  have good := h.2.2 _ proper
  have sat : Saturates (fun a v => neighbors[a.val][v.val])
      (fun a => decide (a ∈ (SaturationPrune.selectedSet (prunedSet neighbors).1).erase i)) := by
    by_contra hn
    have bad := (SaturationPrune.bad_correct neighbors _).mpr hn
    rw [good] at bad
    contradiction
  have masks := SaturationPrune.ofSet_selectedSet (SaturationPrune.clear (prunedSet neighbors).1 i).1
  rw [SaturationPrune.clear_set] at masks
  have eq : (fun a : Fin k => decide (a ∈ (SaturationPrune.selectedSet (prunedSet neighbors).1).erase i)) =
      (fun a => (SaturationPrune.clear (prunedSet neighbors).1 i).1[a.val]) := by
    funext a
    have ha := congrArg (fun v : Vector Bool k => v[a.val]) masks
    simpa only [SaturationPrune.ofSet, Vector.getElem_ofFn] using ha
  rwa [eq] at sat

def prunedSetBudget (k n : Nat) := (2 * k * k + 7 * k + 3) +
  (2 * k * k + 2 * k + k * SaturationPrune.iterationBudget k n + 3) + 1

theorem prunedSet_cost (neighbors : Vector (Vector Bool n) k) :
    (prunedSet neighbors).2 ≤ prunedSetBudget k n := by
  have ha := Costed.tabulate_cost k (fun _ => (true, 1)) 1 (by intros; rfl)
  have hp := SaturationPrune.prune_cost neighbors (allSelected k).1
  dsimp only [prunedSet, prunedSetBudget]
  change (allSelected k).2 ≤ _ at ha
  norm_num only at ha
  simp only [Nat.mul_comm k 7] at ha
  omega

end GyoriLovasz
