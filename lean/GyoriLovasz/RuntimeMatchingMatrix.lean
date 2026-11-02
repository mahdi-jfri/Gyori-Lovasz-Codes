import GyoriLovasz.RuntimeWordTransport

namespace GyoriLovasz.TransportNetwork
open scoped BigOperators

def Saturates (allowed : Fin l → Fin r → Bool) (selected : Fin l → Bool) : Prop :=
  ∃ f : {i : Fin l // selected i = true} → Fin r,
    Function.Injective f ∧ ∀ i, allowed i.val (f i) = true

theorem unit_matrix_saturates (allowed : Fin l → Fin r → Bool) (selected : Fin l → Bool)
    (x : Fin l → Fin r → Nat)
    (h : MatrixFeasible allowed (fun i => if selected i then 1 else 0) (fun _ => 1) x) :
    Saturates allowed selected := by
  classical
  have positive : ∀ i : {i : Fin l // selected i = true}, ∃ j, 0 < x i.val j := by
    intro i
    by_contra hn
    have zero : ∀ j, x i.val j = 0 := by
      intro j
      have no : ¬0 < x i.val j := fun hp => hn ⟨j, hp⟩
      omega
    have row := h.2.1 i.val
    simp [zero, i.property] at row
  let f := fun i => Classical.choose (positive i)
  have fp := fun i => Classical.choose_spec (positive i)
  refine ⟨f, ?_, fun i => h.1 i.val (f i) (fp i)⟩
  intro i j eq
  by_contra ne
  have different : i.val ≠ j.val := fun he => ne (Subtype.ext he)
  have both : x i.val (f i) + x j.val (f i) ≤ ∑ a, x a (f i) := by
    calc
      _ = ∑ a ∈ ({i.val, j.val} : Finset (Fin l)), x a (f i) := by simp [different]
      _ ≤ ∑ a, x a (f i) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have pi := fp i
  have pj := fp j
  change 0 < x i.val (f i) at pi
  change 0 < x j.val (f j) at pj
  rw [← eq] at pj
  have col := h.2.2 (f i)
  dsimp only at col
  omega

theorem saturates_unit_matrix (allowed : Fin l → Fin r → Bool) (selected : Fin l → Bool)
    (h : Saturates allowed selected) :
    ∃ x, MatrixFeasible allowed (fun i => if selected i then 1 else 0) (fun _ => 1) x := by
  classical
  obtain ⟨f, inj, edge⟩ := h
  let x := fun i j => if hi : selected i = true then if f ⟨i, hi⟩ = j then 1 else 0 else 0
  refine ⟨x, ?_, ?_, ?_⟩
  · intro i j positive
    by_cases hi : selected i = true
    · by_cases eq : f ⟨i, hi⟩ = j
      · simpa only [eq] using edge ⟨i, hi⟩
      · simp [x, hi, eq] at positive
    · simp [x, hi] at positive
  · intro i
    by_cases hi : selected i = true
    · simp [x, hi]
    · simp [x, hi]
  · intro j
    by_cases ex : ∃ i, x i j ≠ 0
    · obtain ⟨i, hi⟩ := ex
      have active : selected i = true := by by_contra hn; simp [x, hn] at hi
      have hits : f ⟨i, active⟩ = j := by by_contra hn; simp [x, active, hn] at hi
      have rest : ∀ a, a ≠ i → x a j = 0 := by
        intro a ne
        by_cases ha : selected a = true
        · have miss : f ⟨a, ha⟩ ≠ j := by
            intro he
            have eq := congrArg Subtype.val (inj (he.trans hits.symm))
            exact ne eq
          simp [x, ha, miss]
        · simp [x, ha]
      rw [Finset.sum_eq_single i (fun a _ hn => rest a hn) (by simp)]
      simp [x, active, hits]
    · have zero : ∀ i, x i j = 0 := by simpa using ex
      simp [zero]

theorem unit_matrix_iff_saturates (allowed : Fin l → Fin r → Bool) (selected : Fin l → Bool) :
    (∃ x, MatrixFeasible allowed (fun i => if selected i then 1 else 0) (fun _ => 1) x) ↔
      Saturates allowed selected :=
  ⟨fun ⟨x, h⟩ => unit_matrix_saturates allowed selected x h, saturates_unit_matrix allowed selected⟩

def saturationCheck (allowed : Vector (Vector Bool r) l) (selected : Vector Bool l) : Bool × Nat :=
  let supply := Costed.tabulate l (fun i => (if selected[i.val] then [true] else [], 3))
  let capacity := Costed.tabulate r (fun _ => ([true], 1))
  let checked := matrixCheck allowed supply.1 capacity.1 1
  (checked.1, supply.2 + capacity.2 + checked.2 + 2)

theorem saturationCheck_correct (allowed : Vector (Vector Bool r) l) (selected : Vector Bool l) :
    (saturationCheck allowed selected).1 = true ↔
      Saturates (fun i j => allowed[i.val][j.val]) (fun i => selected[i.val]) := by
  have h := matrixCheck_correct allowed
    (Costed.tabulate l (fun i => (if selected[i.val] then [true] else [], 3))).1
    (Costed.tabulate r (fun _ => ([true], 1))).1 1
    (by intro i; simp only [Costed.tabulate_value]; split <;> simp)
    (by intro j; simp [Costed.tabulate_value])
  have values (i : Fin l) : Binary.value (if selected[i.val] then [true] else []) =
      if selected[i.val] then 1 else 0 := by split <;> simp [Binary.value]
  simp only [Costed.tabulate_value, values, Binary.value] at h
  exact h.trans (unit_matrix_iff_saturates _ _)

theorem saturationCheck_cost (allowed : Vector (Vector Bool r) l) (selected : Vector Bool l) :
    (saturationCheck allowed selected).2 ≤
      2 * l * l + 9 * l + 2 * r * r + 7 * r + matrixBudget l r 1 + 8 := by
  have hs := Costed.tabulate_cost l (fun i => (if selected[i.val] then [true] else [], 3)) 3 (by intros; rfl)
  have hc := Costed.tabulate_cost r (fun _ => ([true], 1)) 1 (by intros; rfl)
  have hm := matrixCheck_cost allowed
    (Costed.tabulate l (fun i => (if selected[i.val] then [true] else [], 3))).1
    (Costed.tabulate r (fun _ => ([true], 1))).1 1
    (by intro i; simp only [Costed.tabulate_value]; split <;> simp)
    (by intro j; simp [Costed.tabulate_value])
  dsimp only [saturationCheck]
  norm_num only at hs hc
  simp only [Nat.mul_comm l 9, Nat.mul_comm r 7] at hs hc
  omega

end GyoriLovasz.TransportNetwork
