import Mathlib.Combinatorics.Hall.Finite
import GyoriLovasz.Initialization

namespace GyoriLovasz
open Side Finset

theorem countTrue_eq_card_filter (P : Fin n → Prop) [DecidablePred P] :
    countTrue (List.finRange n) P = (Finset.univ.filter P).card := by
  classical
  rw [countTrue_filter_length]
  have h : (Finset.univ : Finset (Fin n)) = ⟨List.finRange n, finRange_nodup n⟩ := by
    ext x
    simp [mem_finRange x]
  rw [h]
  rfl

theorem size_eq_separator_card (C : Cut (Fin n)) :
    size (List.finRange n) C = (Finset.univ.filter (fun x => C x = sep)).card := by
  rw [size_eq_countTrue, countTrue_eq_card_filter]

/-- If the neighborhood can be matched injectively to a terminal set avoiding
`t`, then `t` cannot be essential outside that neighborhood. The proof removes
terminal separators and replaces them by matched predecessors. -/
theorem neighborhood_matching_nonessential {E : Fin n → Fin n → Prop}
    {T : Fin n → Prop} {v t : Fin n} {r : Nat}
    (A N : Finset (Fin n)) (f : Fin n → Fin n)
    (terminals : ∀ x ∈ A, T x) (neighbors_nonterminal : ∀ p ∈ N, ¬T p)
    (covers : ∀ x y, ¬T x → y ∈ A → E x y → x ∈ N)
    (maps : ∀ p ∈ N, f p ∈ A ∧ f p ≠ t ∧ E p (f p))
    (inj : Set.InjOn f N) (ht : t ∈ A) (outside : v ∉ N)
    (rank : HasRank (List.finRange n) E T v r) :
    ¬CutEssential (List.finRange n) E T v r t := by
  classical
  rintro ⟨C, hc, hct⟩
  let P := Finset.univ.filter (fun x => C x = sep)
  let B := N.filter (fun x => C x = right)
  let D : Cut (Fin n) := fun x => if x ∈ A then left else if x ∈ B then sep else C x
  have B_not_A : ∀ x ∈ B, x ∉ A := by
    intro x hx ha
    exact neighbors_nonterminal x (Finset.mem_filter.mp hx).1 (terminals x ha)
  have source_not_A : v ∉ A := by
    intro h
    exact hc.1.terminals v (terminals v h) hc.1.source
  have source_not_B : v ∉ B := fun h => outside (Finset.mem_filter.mp h).1
  have validD : Valid E T v D := by
    refine ⟨by simp [D, source_not_A, source_not_B, hc.1.source], ?_, ?_⟩
    · intro x hx
      by_cases ha : x ∈ A
      · simp [D, ha]
      · by_cases hb : x ∈ B
        · simp [D, ha, hb]
        · simpa [D, ha, hb] using hc.1.terminals x hx
    · intro x y edge hxr hyl
      have xa : x ∉ A := by intro h; simp [D, h] at hxr
      have xb : x ∉ B := by intro h; simp [D, xa, h] at hxr
      have xc : C x = right := by simpa [D, xa, xb] using hxr
      have xnt : ¬T x := fun h => hc.1.terminals x h xc
      by_cases ya : y ∈ A
      · have xn := covers x y xnt ya edge
        exact xb (Finset.mem_filter.mpr ⟨xn, xc⟩)
      · have yb : y ∉ B := by intro h; simp [D, ya, h] at hyl
        have yc : C y = left := by simpa [D, ya, yb] using hyl
        exact hc.1.no_cross x y edge xc yc
  have fmap : B.image f ⊆ (P ∩ A).erase t := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨xn, xr⟩ := Finset.mem_filter.mp hx
    obtain ⟨fa, ft, edge⟩ := maps x xn
    have nl := hc.1.no_cross x (f x) edge xr
    have nr := hc.1.terminals (f x) (terminals (f x) fa)
    have fs : C (f x) = sep := by
      cases h : C (f x) with
      | left => exact False.elim (nl h)
      | sep => rfl
      | right => exact False.elim (nr h)
    exact Finset.mem_erase.mpr ⟨ft, Finset.mem_inter.mpr ⟨by simp [P, fs], fa⟩⟩
  have injB : Set.InjOn f B := fun x hx y hy he =>
    inj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 he
  have bcard := Finset.card_le_card fmap
  rw [Finset.card_image_of_injOn injB] at bcard
  have tin : t ∈ P ∩ A := by simp [P, hct, ht]
  have ercard := Finset.card_erase_of_mem tin
  have tpositive : 0 < (P ∩ A).card := Finset.card_pos.mpr ⟨t, tin⟩
  have sepD : Finset.univ.filter (fun x => D x = sep) = (P \ A) ∪ B := by
    ext x
    by_cases xa : x ∈ A
    · have xb : x ∉ B := fun h => B_not_A x h xa
      simp [D, P, xa, xb]
    · by_cases xb : x ∈ B
      · simp [D, P, xa, xb]
      · simp [D, P, xa, xb]
  have disj : Disjoint (P \ A) B := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    have xs : C x = sep := by simpa [P] using (Finset.mem_sdiff.mp hx).1
    have xr := (Finset.mem_filter.mp hb).2
    rw [xs] at xr
    cases xr
  have splitcard : (P \ A).card + (P ∩ A).card = P.card := by
    have he : P \ (P ∩ A) = P \ A := by ext x; simp
    have h := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left (s₁ := P) (s₂ := A))
    rw [he] at h
    exact h
  have dsize := size_eq_separator_card D
  rw [sepD, Finset.card_union_of_disjoint disj] at dsize
  have csize : size (List.finRange n) C = P.card := size_eq_separator_card C
  have lower := rank.lower D validD
  have cs := hc.2
  omega

noncomputable def predecessorSet (E : Fin n → Fin n → Prop)
    (roots : Fin k → Fin n) (i : Fin k) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun p => ¬RootSet roots p ∧ E p (roots i))

/-- The pre-terminal matching required by the unweighted algorithm. -/
theorem preterminal_matching {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {capacity : Fin k → Nat} {label : Fin n → Fin k}
    (hinj : Function.Injective roots) (positive : ∀ i, 0 < capacity i)
    (feasible : FeasibleAssignment E roots capacity label) :
    ∃ p : Fin k → Fin n, Function.Injective p ∧
      (∀ i, ¬RootSet roots (p i)) ∧ (∀ i, E (p i) (roots i)) := by
  classical
  let family := predecessorSet E roots
  suffices hall : ∀ S : Finset (Fin k), S.card ≤ (S.biUnion family).card by
    obtain ⟨p, hp, edges⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' family).mp hall
    exact ⟨p, hp, (fun i => (Finset.mem_filter.mp (edges i)).2.1),
      fun i => (Finset.mem_filter.mp (edges i)).2.2⟩
  by_cases hall : ∀ S : Finset (Fin k), S.card ≤ (S.biUnion family).card
  · exact hall
  · have ex : ∃ m, ∃ S : Finset (Fin k), (S.biUnion family).card < S.card ∧ S.card = m := by
      obtain ⟨S, hs⟩ := not_forall.mp hall
      exact ⟨S.card, S, by omega, rfl⟩
    obtain ⟨m, ⟨S, deficient, hm⟩, minimal⟩ := exists_minimal_nat _ ex
    let N := S.biUnion family
    let A := S.image roots
    have tnonessential : ∀ i ∈ S, ∀ v, ∀ hv : ¬RootSet roots v, v ∉ N →
        ¬Essential E (RootSet roots) v hv (roots i) := by
      intro i hi v hv outside
      have restrictedHall : ∀ F : Finset (S.erase i),
          F.card ≤ (F.biUnion (fun a => family a.val)).card := by
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
        have lt : U.card < S.card := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨sub, fun he => noti (he.symm ▸ hi)⟩)
        have good : U.card ≤ (U.biUnion family).card := by
          by_cases h : U.card ≤ (U.biUnion family).card
          · exact h
          · have low := minimal U.card ⟨U, by omega, rfl⟩
            omega
        simpa [U, Finset.card_image_of_injective, Subtype.coe_injective, Finset.image_biUnion] using good
      obtain ⟨g, ginj, gedge⟩ :=
        (Finset.all_card_le_biUnion_card_iff_existsInjective'
          (fun a : S.erase i => family a.val)).mp restrictedHall
      have image_sub : Finset.univ.image g ⊆ N := by
        intro p hp
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_biUnion.mpr ⟨a.val, Finset.mem_of_mem_erase a.property, gedge a⟩
      have image_card : (Finset.univ.image g).card = S.card - 1 := by
        rw [Finset.card_image_of_injective _ ginj, Finset.card_univ,
          Fintype.card_coe, Finset.card_erase_of_mem hi]
      have image_eq : Finset.univ.image g = N :=
        Finset.eq_of_subset_of_card_le image_sub (by change N.card < S.card at deficient; omega)
      have surj : ∀ p, p ∈ N → ∃ a, g a = p := by
        intro p hp
        have him : p ∈ Finset.univ.image g := image_eq.symm ▸ hp
        obtain ⟨a, _, he⟩ := Finset.mem_image.mp him
        exact ⟨a, he⟩
      let f := fun p => if hp : p ∈ N then roots (Classical.choose (surj p hp)).val else roots i
      have fvalue (p : Fin n) (hp : p ∈ N) : f p = roots (Classical.choose (surj p hp)).val := by
        simp [f, hp]
      have maps : ∀ p ∈ N, f p ∈ A ∧ f p ≠ roots i ∧ E p (f p) := by
        intro p hp
        let a := Classical.choose (surj p hp)
        have ga : g a = p := Classical.choose_spec (surj p hp)
        have ae : E (g a) (roots a.val) := (Finset.mem_filter.mp (gedge a)).2.2
        rw [fvalue p hp]
        refine ⟨Finset.mem_image.mpr ⟨a.val, Finset.mem_of_mem_erase a.property, rfl⟩, ?_, ?_⟩
        · intro he
          exact (Finset.mem_erase.mp a.property).1 (hinj he)
        · simpa [ga] using ae
      have finj : Set.InjOn f N := by
        intro p hp q hq he
        rw [fvalue p hp, fvalue q hq] at he
        have va := hinj he
        have ab : Classical.choose (surj p hp) = Classical.choose (surj q hq) := Subtype.ext va
        have gp := Classical.choose_spec (surj p hp)
        have gq := Classical.choose_spec (surj q hq)
        exact gp.symm.trans ((congrArg g ab).trans gq)
      apply neighborhood_matching_nonessential A N f
        (fun x hx => by obtain ⟨j, _, he⟩ := Finset.mem_image.mp hx; exact ⟨j, he⟩)
        (fun p hp => by
          obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
          exact (Finset.mem_filter.mp hj).2.1)
        (fun x y hnt hy edge => by
          obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hy
          exact Finset.mem_biUnion.mpr ⟨j, hj, by simp [family, predecessorSet, hnt, he, edge]⟩)
        maps finj (Finset.mem_image.mpr ⟨i, hi, rfl⟩) outside
        (cutRank_spec E (RootSet roots) v hv)
    have assigned : ∀ i, ∃ v, ¬RootSet roots v ∧ label v = i := by
      intro i
      have hc : 0 < countTrue (nonterminals roots) (fun v => label v = i) := by
        rw [feasible.2 i]
        exact positive i
      rw [countTrue_filter_length] at hc
      obtain ⟨v, hv⟩ := List.exists_mem_of_length_pos hc
      obtain ⟨hvnt, hvi⟩ := List.mem_filter.mp hv
      exact ⟨v, mem_nonterminals.mp hvnt, by simpa using hvi⟩
    let rep := fun i => Classical.choose (assigned i)
    have hrep := fun i => Classical.choose_spec (assigned i)
    have repinj : Function.Injective rep := by
      intro i j he
      exact (hrep i).2.symm.trans ((congrArg label he).trans (hrep j).2)
    have rep_sub : S.image rep ⊆ N := by
      intro v hmem
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hmem
      subst v
      by_cases hv : rep i ∈ N
      · exact hv
      · have he := feasible.1 (rep i) (hrep i).1
        have hlabel : label (rep i) = i := (hrep i).2
        have he' : Essential E (RootSet roots) (rep i) (hrep i).1 (roots i) :=
          (congrArg (fun j => Essential E (RootSet roots) (rep i) (hrep i).1 (roots j)) hlabel).mp he
        exact False.elim (tnonessential i hi (rep i) (hrep i).1 hv he')
    have bound := Finset.card_le_card rep_sub
    rw [Finset.card_image_of_injective _ repinj] at bound
    change N.card < S.card at deficient
    omega

end GyoriLovasz


