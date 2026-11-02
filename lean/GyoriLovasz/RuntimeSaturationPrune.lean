import GyoriLovasz.RuntimeMatchingMatrix
import GyoriLovasz.RuntimeHallPrune

namespace GyoriLovasz.SaturationPrune
open TransportNetwork

def selectedSet (selected : Vector Bool l) : Finset (Fin l) :=
  Finset.univ.filter (fun i => selected[i.val] = true)

@[simp] theorem mem_selectedSet (selected : Vector Bool l) (i : Fin l) :
    i ∈ selectedSet selected ↔ selected[i.val] = true := by simp [selectedSet]

def ofSet (S : Finset (Fin l)) : Vector Bool l := Vector.ofFn (fun i => decide (i ∈ S))

theorem ofSet_selectedSet (selected : Vector Bool l) : ofSet (selectedSet selected) = selected := by
  ext i hi
  simp [ofSet, selectedSet]

def clear (selected : Vector Bool l) (i : Fin l) : Costed.Computation (Vector Bool l) :=
  Costed.tabulate l (fun j => (selected[j.val] && decide (j ≠ i), 3))

theorem clear_set (selected : Vector Bool l) (i : Fin l) :
    selectedSet (clear selected i).1 = (selectedSet selected).erase i := by
  ext j
  simp [clear, Costed.tabulate_value, and_comm]

theorem clear_cost (selected : Vector Bool l) (i : Fin l) :
    (clear selected i).2 ≤ 2 * l * l + 9 * l + 3 := by
  simpa only [Nat.mul_comm l 9] using Costed.tabulate_cost l
    (fun j => (selected[j.val] && decide (j ≠ i), 3)) 3 (by intros; rfl)

def bad (allowed : Vector (Vector Bool r) l) (S : Finset (Fin l)) : Bool :=
  !(saturationCheck allowed (ofSet S)).1

theorem bad_correct (allowed : Vector (Vector Bool r) l) (S : Finset (Fin l)) :
    bad allowed S = true ↔ ¬Saturates (fun i j => allowed[i.val][j.val]) (fun i => decide (i ∈ S)) := by
  rw [bad, Bool.not_eq_true', Bool.eq_false_iff]
  exact not_congr (by simpa only [ofSet, Vector.getElem_ofFn] using saturationCheck_correct allowed (ofSet S))

theorem saturates_subset (allowed : Fin l → Fin r → Bool) (A B : Finset (Fin l))
    (sub : A ⊆ B) (h : Saturates allowed (fun i => decide (i ∈ B))) :
    Saturates allowed (fun i => decide (i ∈ A)) := by
  obtain ⟨f, inj, edge⟩ := h
  let embed : {i : Fin l // decide (i ∈ A) = true} → {i : Fin l // decide (i ∈ B) = true} :=
    fun i => ⟨i.val, by simpa using sub (of_decide_eq_true i.property)⟩
  refine ⟨fun i => f (embed i), ?_, fun i => edge (embed i)⟩
  intro i j he
  exact Subtype.ext (show i.val = j.val from congrArg
    (fun a : {i : Fin l // decide (i ∈ B) = true} => a.val) (inj he))

theorem bad_upward (allowed : Vector (Vector Bool r) l) (A B : Finset (Fin l))
    (sub : A ⊆ B) (h : bad allowed A = true) : bad allowed B = true := by
  rw [bad_correct] at h ⊢
  exact fun sat => h (saturates_subset _ A B sub sat)

theorem bad_empty (allowed : Vector (Vector Bool r) l) : bad allowed ∅ = false := by
  apply Bool.eq_false_iff.mpr
  intro hb
  have h := (bad_correct allowed ∅).mp hb
  apply h
  refine ⟨fun i => False.elim (by simpa using i.property), ?_, ?_⟩
  · intro i; exact False.elim (by simpa using i.property)
  · intro i; exact False.elim (by simpa using i.property)

def run (allowed : Vector (Vector Bool r) l) : List (Fin l) → Vector Bool l → Costed.Computation (Vector Bool l)
  | [], selected => (selected, 1)
  | i :: rest, selected =>
    let erased := clear selected i
    let tested := saturationCheck allowed erased.1
    let next := if tested.1 then selected else erased.1
    let result := run allowed rest next
    (result.1, erased.2 + tested.2 + result.2 + 3)

theorem run_refines (allowed : Vector (Vector Bool r) l) (indices : List (Fin l)) (selected : Vector Bool l) :
    selectedSet (run allowed indices selected).1 =
      (pruneCandidates (bad allowed) indices (selectedSet selected)).1 := by
  induction indices generalizing selected with
  | nil => rfl
  | cons i rest ih =>
    have hb : bad allowed ((selectedSet selected).erase i) =
        !(saturationCheck allowed (clear selected i).1).1 := by
      rw [← clear_set, bad, ofSet_selectedSet]
    simp only [run, pruneCandidates, hb]
    cases ht : (saturationCheck allowed (clear selected i).1).1 <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_eq]
    · simpa only [clear_set] using ih (clear selected i).1
    · exact ih selected

def iterationBudget (l r : Nat) :=
  (2 * l * l + 9 * l + 3) + (2 * l * l + 9 * l + 2 * r * r + 7 * r + matrixBudget l r 1 + 8) + 3

theorem run_cost (allowed : Vector (Vector Bool r) l) (indices : List (Fin l)) (selected : Vector Bool l) :
    (run allowed indices selected).2 ≤ indices.length * iterationBudget l r + 1 := by
  induction indices generalizing selected with
  | nil => simp [run]
  | cons i rest ih =>
    have he := clear_cost selected i
    have ht := saturationCheck_cost allowed (clear selected i).1
    have hr := ih (if (saturationCheck allowed (clear selected i).1).1 then selected else (clear selected i).1)
    dsimp only [run, iterationBudget] at *
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

def prune (allowed : Vector (Vector Bool r) l) (selected : Vector Bool l) : Costed.Computation (Vector Bool l) :=
  let indices := Costed.enumerateIndices l
  let result := run allowed indices.1 selected
  (result.1, indices.2 + result.2 + 1)

theorem prune_correct (allowed : Vector (Vector Bool r) l) (selected : Vector Bool l)
    (initial : ¬Saturates (fun i j => allowed[i.val][j.val]) (fun i => selected[i.val])) :
    let S := selectedSet (prune allowed selected).1
    S.Nonempty ∧ S ⊆ selectedSet selected ∧ bad allowed S = true ∧
      ∀ U, U ⊂ S → bad allowed U = false := by
  have hb : bad allowed (selectedSet selected) = true := by
    rw [bad, ofSet_selectedSet, Bool.not_eq_true', Bool.eq_false_iff]
    exact fun h => initial ((saturationCheck_correct allowed selected).mp h)
  have h := pruneCandidates_minimal (bad allowed) (bad_upward allowed) (bad_empty allowed)
    (selectedSet selected) hb (Costed.enumerateIndices l).1
    (by intros; simp [Costed.enumerateIndices_value])
  dsimp only [prune]
  rw [run_refines]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem prune_cost (allowed : Vector (Vector Bool r) l) (selected : Vector Bool l) :
    (prune allowed selected).2 ≤ 2 * l * l + 2 * l + l * iterationBudget l r + 3 := by
  have hi := Costed.enumerateIndices_cost l
  have hr := run_cost allowed (Costed.enumerateIndices l).1 selected
  simp only [Costed.enumerateIndices_value, List.length_finRange] at hr
  dsimp only [prune]
  simp only [Costed.enumerateIndices_value]
  omega

end GyoriLovasz.SaturationPrune
