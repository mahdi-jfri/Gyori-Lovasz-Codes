import GyoriLovasz.Matching

namespace GyoriLovasz
attribute [local instance] Classical.propDecidable

theorem deficient_bijection_local {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    (S : Finset (Fin k))
    (deficient : (S.biUnion (predecessorSet E roots)).card < S.card)
    (minimal : ∀ U : Finset (Fin k), U ⊂ S → U.card ≤ (U.biUnion (predecessorSet E roots)).card)
    {i : Fin k} (hi : i ∈ S) :
    ∃ f : Fin n → Fin k,
      Set.InjOn f (S.biUnion (predecessorSet E roots)) ∧
      ∀ p ∈ S.biUnion (predecessorSet E roots), f p ∈ S ∧ f p ≠ i ∧ E p (roots (f p)) := by
  classical
  let family := predecessorSet E roots
  let N := S.biUnion family
  have hall : ∀ F : Finset (S.erase i), F.card ≤ (F.biUnion (fun a => family a.val)).card := by
    intro F
    let U := F.image (fun a => a.val)
    have sub : U ⊆ S := by
      intro j hj
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_of_mem_erase a.property
    have noti : i ∉ U := by
      intro h
      obtain ⟨a, _, he⟩ := Finset.mem_image.mp h
      exact (Finset.mem_erase.mp a.property).1 he
    have lt : U ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨sub, fun he => noti (he.symm ▸ hi)⟩
    have good := minimal U lt
    simpa [U, family, Finset.card_image_of_injective, Subtype.coe_injective, Finset.image_biUnion] using good
  obtain ⟨g, ginj, gedge⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' (fun a : S.erase i => family a.val)).mp hall
  have image_sub : Finset.univ.image g ⊆ N := by
    intro p hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_biUnion.mpr ⟨a.val, Finset.mem_of_mem_erase a.property, gedge a⟩
  have image_card : (Finset.univ.image g).card = S.card - 1 := by
    rw [Finset.card_image_of_injective _ ginj, Finset.card_univ, Fintype.card_coe, Finset.card_erase_of_mem hi]
  have image_eq : Finset.univ.image g = N :=
    Finset.eq_of_subset_of_card_le image_sub (by change N.card < S.card at deficient; omega)
  have surj : ∀ p, p ∈ N → ∃ a, g a = p := by
    intro p hp
    have him : p ∈ Finset.univ.image g := image_eq.symm ▸ hp
    obtain ⟨a, _, he⟩ := Finset.mem_image.mp him
    exact ⟨a, he⟩
  let f := fun p => if hp : p ∈ N then (Classical.choose (surj p hp)).val else i
  have fv (p : Fin n) (hp : p ∈ N) : f p = (Classical.choose (surj p hp)).val := by simp [f, hp]
  refine ⟨f, ?_, ?_⟩
  · intro p hp q hq he
    rw [fv p hp, fv q hq] at he
    have ab : Classical.choose (surj p hp) = Classical.choose (surj q hq) := Subtype.ext he
    exact (Classical.choose_spec (surj p hp)).symm.trans
      ((congrArg g ab).trans (Classical.choose_spec (surj q hq)))
  · intro p hp
    let a := Classical.choose (surj p hp)
    have ga : g a = p := Classical.choose_spec (surj p hp)
    have ae : E (g a) (roots a.val) := (Finset.mem_filter.mp (gedge a)).2.2
    rw [fv p hp]
    exact ⟨Finset.mem_of_mem_erase a.property, (Finset.mem_erase.mp a.property).1, by simpa [ga] using ae⟩

theorem deficient_bijection {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    (S : Finset (Fin k))
    (deficient : (S.biUnion (predecessorSet E roots)).card < S.card)
    (minimal : ∀ U : Finset (Fin k), U.card < S.card → U.card ≤ (U.biUnion (predecessorSet E roots)).card)
    {i : Fin k} (hi : i ∈ S) :
    ∃ f : Fin n → Fin k,
      Set.InjOn f (S.biUnion (predecessorSet E roots)) ∧
      ∀ p ∈ S.biUnion (predecessorSet E roots), f p ∈ S ∧ f p ≠ i ∧ E p (roots (f p)) :=
  deficient_bijection_local S deficient (fun U h => minimal U (Finset.card_lt_card h)) hi

/-- Complete combinatorial data for rounding when the terminal matching fails. -/
theorem hall_rounding_data {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    (hinj : Function.Injective roots)
    (failure : ¬∃ p : Fin k → Fin n, Function.Injective p ∧
      (∀ i, ¬RootSet roots (p i)) ∧ (∀ i, E (p i) (roots i))) :
    ∃ S : Finset (Fin k), S.Nonempty ∧ ∃ f : Fin n → Fin k,
      Set.InjOn f (S.biUnion (predecessorSet E roots)) ∧
      (∀ p ∈ S.biUnion (predecessorSet E roots), f p ∈ S ∧ E p (roots (f p))) ∧
      (∀ i ∈ S, ∀ v, ∀ hv : ¬RootSet roots v,
        v ∉ S.biUnion (predecessorSet E roots) → ¬Essential E (RootSet roots) v hv (roots i)) := by
  classical
  let family := predecessorSet E roots
  have nohall : ¬∀ S : Finset (Fin k), S.card ≤ (S.biUnion family).card := by
    intro hall
    obtain ⟨p, hp, edges⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' family).mp hall
    exact failure ⟨p, hp, (fun i => (Finset.mem_filter.mp (edges i)).2.1),
      fun i => (Finset.mem_filter.mp (edges i)).2.2⟩
  have ex : ∃ m, ∃ S : Finset (Fin k), (S.biUnion family).card < S.card ∧ S.card = m := by
    obtain ⟨S, hs⟩ := not_forall.mp nohall
    exact ⟨S.card, S, by omega, rfl⟩
  obtain ⟨m, ⟨S, deficient, hm⟩, least⟩ := exists_minimal_nat _ ex
  have minimal : ∀ U : Finset (Fin k), U.card < S.card → U.card ≤ (U.biUnion family).card := by
    intro U smaller
    by_cases h : U.card ≤ (U.biUnion family).card
    · exact h
    · have lower := least U.card ⟨U, by omega, rfl⟩
      omega
  have nonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := nonempty
  have snonempty : S.Nonempty := ⟨i, hi⟩
  obtain ⟨f, fi, fm⟩ := deficient_bijection S deficient minimal hi
  refine ⟨S, snonempty, f, fi, (fun p hp => ⟨(fm p hp).1, (fm p hp).2.2⟩), ?_⟩
  intro j hj v hv outside
  obtain ⟨g, gi, gm⟩ := deficient_bijection S deficient minimal hj
  apply neighborhood_matching_nonessential (S.image roots) (S.biUnion family) (fun p => roots (g p))
    (fun x hx => by obtain ⟨a, _, he⟩ := Finset.mem_image.mp hx; exact ⟨a, he⟩)
    (fun p hp => by
      obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_filter.mp ha).2.1)
    (fun x y hnt hy edge => by
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hy
      exact Finset.mem_biUnion.mpr ⟨a, ha, by simp [family, predecessorSet, hnt, he, edge]⟩)
    (fun p hp => ⟨Finset.mem_image.mpr ⟨g p, (gm p hp).1, rfl⟩,
      fun he => (gm p hp).2.1 (hinj he), (gm p hp).2.2⟩)
    (fun _ hp _ hq he => gi hp hq (hinj he))
    (Finset.mem_image.mpr ⟨j, hj, rfl⟩) outside (cutRank_spec E (RootSet roots) v hv)

end GyoriLovasz

