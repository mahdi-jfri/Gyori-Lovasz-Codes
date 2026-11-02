import GyoriLovasz.RuntimeMatchingMatrix
import GyoriLovasz.WeightedHall

namespace GyoriLovasz.TransportNetwork

def neighborFamily (allowed : Fin l → Fin r → Bool) (i : Fin l) : Finset (Fin r) :=
  Finset.univ.filter (fun j => allowed i j = true)

theorem saturates_card (allowed : Fin l → Fin r → Bool) (S : Finset (Fin l))
    (h : Saturates allowed (fun i => decide (i ∈ S))) :
    S.card ≤ (S.biUnion (neighborFamily allowed)).card := by
  classical
  obtain ⟨f, inj, edge⟩ := h
  let g : S → ↥(S.biUnion (neighborFamily allowed)) := fun i =>
    ⟨f ⟨i.val, by simpa using i.property⟩,
      Finset.mem_biUnion.mpr ⟨i.val, i.property,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, edge ⟨i.val, by simpa using i.property⟩⟩⟩⟩
  have gi : Function.Injective g := by
    intro i j he
    have eq := inj (congrArg Subtype.val he)
    exact Subtype.ext (show i.val = j.val from congrArg
      (fun a : {i : Fin l // decide (i ∈ S) = true} => a.val) eq)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g gi

theorem hall_saturates (allowed : Fin l → Fin r → Bool) (S : Finset (Fin l))
    (hall : ∀ U, U ⊆ S → U.card ≤ (U.biUnion (neighborFamily allowed)).card) :
    Saturates allowed (fun i => decide (i ∈ S)) := by
  classical
  have localHall : ∀ F : Finset S, F.card ≤ (F.biUnion (fun i => neighborFamily allowed i.val)).card := by
    intro F
    let U := F.image (fun i => i.val)
    have sub : U ⊆ S := by
      intro i hi
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
      exact a.property
    have h := hall U sub
    simpa [U, Finset.card_image_of_injective, Subtype.coe_injective, Finset.image_biUnion] using h
  obtain ⟨f, inj, edge⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' (fun i : S => neighborFamily allowed i.val)).mp localHall
  let embed : {i : Fin l // decide (i ∈ S) = true} → S := fun i => ⟨i.val, of_decide_eq_true i.property⟩
  refine ⟨fun i => f (embed i), ?_, ?_⟩
  · intro i j he
    exact Subtype.ext (show i.val = j.val from congrArg (fun a : S => a.val) (inj he))
  · intro i
    exact (Finset.mem_filter.mp (edge (embed i))).2

theorem minimal_unsaturated_deficient (allowed : Fin l → Fin r → Bool) (S : Finset (Fin l))
    (failure : ¬Saturates allowed (fun i => decide (i ∈ S)))
    (minimal : ∀ U, U ⊂ S → Saturates allowed (fun i => decide (i ∈ U))) :
    (S.biUnion (neighborFamily allowed)).card < S.card ∧
      ∀ U, U ⊂ S → U.card ≤ (U.biUnion (neighborFamily allowed)).card := by
  have proper := fun U h => saturates_card allowed U (minimal U h)
  refine ⟨?_, proper⟩
  by_contra hn
  apply failure
  apply hall_saturates allowed S
  intro U sub
  by_cases eq : U = S
  · subst U; omega
  · exact proper U (Finset.ssubset_iff_subset_ne.mpr ⟨sub, eq⟩)

end GyoriLovasz.TransportNetwork
