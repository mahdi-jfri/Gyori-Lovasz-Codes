import GyoriLovasz.WeightedHall

namespace GyoriLovasz

/-- Executable deletion scan. The counter counts calls to `bad`, not the
implementation cost of that callback. Saturation tests will instantiate it. -/
def pruneCandidates [DecidableEq α] (bad : Finset α → Bool) : List α → Finset α → Finset α × Nat
  | [], S => (S, 0)
  | x :: xs, S =>
    let next := if bad (S.erase x) then S.erase x else S
    let answer := pruneCandidates bad xs next
    (answer.1, answer.2 + 1)

theorem pruneCandidates_calls [DecidableEq α] (bad : Finset α → Bool) (xs : List α) (S : Finset α) :
    (pruneCandidates bad xs S).2 = xs.length := by
  induction xs generalizing S with
  | nil => rfl
  | cons x xs ih => simp [pruneCandidates, ih]

theorem pruneCandidates_spec [DecidableEq α] (bad : Finset α → Bool)
    (upward : ∀ A B, A ⊆ B → bad A = true → bad B = true)
    (xs : List α) (S : Finset α) (initial : bad S = true) :
    let T := (pruneCandidates bad xs S).1
    T ⊆ S ∧ bad T = true ∧ ∀ x ∈ xs, x ∈ T → bad (T.erase x) = false := by
  induction xs generalizing S with
  | nil => exact ⟨Finset.Subset.refl _, initial, fun _ hx => False.elim (List.not_mem_nil hx)⟩
  | cons x xs ih =>
    by_cases remove : bad (S.erase x) = true
    · have result := ih (S.erase x) remove
      simp only [pruneCandidates, remove, Bool.true_eq, ↓reduceIte]
      refine ⟨result.1.trans (Finset.erase_subset _ _), result.2.1, ?_⟩
      intro y hy hym
      rcases List.mem_cons.mp hy with he | ht
      · subst y
        exact False.elim (Finset.not_mem_erase x S (result.1 hym))
      · exact result.2.2 y ht hym
    · have result := ih S initial
      have nremove : bad (S.erase x) = false := Bool.eq_false_iff.mpr remove
      simp only [pruneCandidates, nremove, Bool.false_eq_true, ↓reduceIte]
      refine ⟨result.1, result.2.1, ?_⟩
      intro y hy hym
      rcases List.mem_cons.mp hy with he | ht
      · subst y
        apply Bool.eq_false_iff.mpr
        intro ht
        apply remove
        apply upward _ _ (Finset.erase_subset_erase x result.1) ht
      · exact result.2.2 y ht hym

/-- Inclusion-minimal unsaturated sets need only one deletion scan, because
saturability is inherited by subsets. The number of saturation queries is k. -/
theorem pruneCandidates_minimal [DecidableEq α] (bad : Finset α → Bool)
    (upward : ∀ A B, A ⊆ B → bad A = true → bad B = true)
    (empty : bad ∅ = false) (S : Finset α) (initial : bad S = true)
    (xs : List α) (covers : ∀ x ∈ S, x ∈ xs) :
    let answer := pruneCandidates bad xs S
    answer.1.Nonempty ∧ answer.1 ⊆ S ∧ bad answer.1 = true ∧
      (∀ U, U ⊂ answer.1 → bad U = false) ∧ answer.2 = xs.length := by
  have spec := pruneCandidates_spec bad upward xs S initial
  let T := (pruneCandidates bad xs S).1
  have nonempty : T.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have ht := spec.2.1
    rw [show (pruneCandidates bad xs S).1 = ∅ from he, empty] at ht
    exact Bool.noConfusion ht
  refine ⟨nonempty, spec.1, spec.2.1, ?_, pruneCandidates_calls bad xs S⟩
  intro U proper
  obtain ⟨x, hx, hxu⟩ := Finset.exists_of_ssubset proper
  have good := spec.2.2 x (covers x (spec.1 hx)) hx
  apply Bool.eq_false_iff.mpr
  intro hu
  have sub : U ⊆ T.erase x := by
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun he => hxu (he ▸ hy), (Finset.ssubset_iff_subset_ne.mp proper).1 hy⟩
  have badErase := upward U (T.erase x) sub hu
  rw [good] at badErase
  exact Bool.noConfusion badErase

end GyoriLovasz
