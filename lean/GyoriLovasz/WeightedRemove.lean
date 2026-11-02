import GyoriLovasz.WeightedRounding

namespace GyoriLovasz
attribute [local instance] Classical.propDecidable

def RemoveVertices (E : Fin n → Fin n → Prop) (S : Finset (Fin n)) : Fin n → Fin n → Prop :=
  fun x y => E x y ∧ x ∉ S ∧ y ∉ S

def RemoveTerminals (T : Fin n → Prop) (S : Finset (Fin n)) : Fin n → Prop :=
  fun x => T x ∧ x ∉ S

noncomputable def retain (vertices : List (Fin n)) (S : Finset (Fin n)) : List (Fin n) :=
  vertices.filter (fun x => decide (x ∉ S))

theorem retain_insert (vertices : List (Fin n)) (hn : vertices.Nodup) (S : Finset (Fin n)) (a : Fin n) :
    retain vertices (insert a S) = (retain vertices S).erase a := by
  classical
  have hret : (retain vertices S).Nodup := List.Pairwise.filter _ hn
  rw [List.Nodup.erase_eq_filter hret]
  unfold retain
  rw [List.filter_filter]
  congr 1
  funext x
  by_cases h : x = a <;> simp [h, and_comm]

/-- Delete any collection of terminals while preserving another terminal's
essentiality. This discharges the second stage of the rounding cut argument. -/
theorem remove_terminals_essential {vertices : List (Fin n)} {E : Fin n → Fin n → Prop}
    {T : Fin n → Prop} {v t : Fin n} {rank : Nat} (S : Finset (Fin n))
    (hn : vertices.Nodup) (hmem : ∀ x ∈ S, x ∈ vertices) (hterm : ∀ x ∈ S, T x)
    (hv : ¬T v) (ht : T t) (outside : t ∉ S)
    (hr : HasRank vertices E T v rank) (essential : CutEssential vertices E T v rank t) :
    ∃ r, HasRank (retain vertices S) (RemoveVertices E S) (RemoveTerminals T S) v r ∧
      CutEssential (retain vertices S) (RemoveVertices E S) (RemoveTerminals T S) v r t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have ee : RemoveVertices E ∅ = E := by funext x y; simp [RemoveVertices]
    have tt : RemoveTerminals T ∅ = T := by funext x; simp [RemoveTerminals]
    simpa [retain, ee, tt] using (show ∃ r, HasRank vertices E T v r ∧ CutEssential vertices E T v r t from ⟨rank, hr, essential⟩)
  | @insert a S ha ih =>
    have amem := hmem a (by simp)
    have aterm := hterm a (by simp)
    have notS : t ∉ S := fun h => outside (by simp [h])
    obtain ⟨r, hr', he'⟩ := ih (fun x hx => hmem x (by simp [hx]))
      (fun x hx => hterm x (by simp [hx])) notS
    have aactive : a ∈ retain vertices S := by simp [retain, amem, ha]
    have ant : RemoveTerminals T S a := ⟨aterm, ha⟩
    have tnt : RemoveTerminals T S t := ⟨ht, notS⟩
    have vne : v ≠ a := fun he => hv (he.symm ▸ aterm)
    have tne : t ≠ a := by intro he; subst t; exact outside (by simp)
    obtain ⟨s, hs⟩ := exists_rank ((retain vertices S).erase a)
      (DeleteVertex (RemoveVertices E S) a) (WithoutTerminal (RemoveTerminals T S) a) v
      (fun h => hv h.1.1)
    have kept := terminal_removal_preserves_essential (List.Pairwise.filter _ hn) aactive
      vne ant tnt tne hr' hs he'
    have ee : DeleteVertex (RemoveVertices E S) a = RemoveVertices E (insert a S) := by
      funext x y
      simp only [DeleteVertex, RemoveVertices, Finset.mem_insert, not_or]
      apply propext
      constructor
      · rintro ⟨⟨he, hx, hy⟩, hxa, hya⟩; exact ⟨he, ⟨hxa, hx⟩, ⟨hya, hy⟩⟩
      · rintro ⟨he, ⟨hxa, hx⟩, ⟨hya, hy⟩⟩; exact ⟨⟨he, hx, hy⟩, hxa, hya⟩
    have tt : WithoutTerminal (RemoveTerminals T S) a = RemoveTerminals T (insert a S) := by
      funext x
      simp only [WithoutTerminal, RemoveTerminals, Finset.mem_insert, not_or]
      apply propext
      exact ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩
    rw [ee, tt] at hs kept
    rw [retain_insert vertices hn]
    exact ⟨s, hs, kept⟩

/-- Essentiality survives the entire deletion of a terminal set together with
its pre-terminal neighborhood, under the nonessentiality supplied by Hall. -/
theorem rounding_essential {E : Fin n → Fin n → Prop} {T : Fin n → Prop}
    {v t : Fin n} {rank : Nat} (S N : Finset (Fin n))
    (terminals : ∀ x ∈ S, T x) (neighbors_nonterminal : ∀ x ∈ N, ¬T x)
    (covers : ∀ x y, ¬T x → y ∈ S → E x y → x ∈ N)
    (neighbors : ∀ x ∈ N, ∃ y ∈ S, E x y)
    (hv : ¬T v) (ht : T t) (outside : v ∉ N) (toutside : t ∉ S)
    (hr : HasRank (List.finRange n) E T v rank)
    (nonessential : ∀ x ∈ S, ¬CutEssential (List.finRange n) E T v rank x)
    (essential : CutEssential (List.finRange n) E T v rank t) :
    ∃ r, HasRank (retain (List.finRange n) (S ∪ N))
        (RemoveVertices E (S ∪ N)) (RemoveTerminals T S) v r ∧
      CutEssential (retain (List.finRange n) (S ∪ N))
        (RemoveVertices E (S ∪ N)) (RemoveTerminals T S) v r t := by
  classical
  have vnt : ¬PromoteTerminals T S N v := by rintro (h | h); exact hv h.1; exact outside h
  obtain ⟨q, hq⟩ := exists_rank (retain (List.finRange n) S) (PromoteGraph E S N) (PromoteTerminals T S N) v vnt
  have promoted := (promotion_preserves_essential S N terminals neighbors_nonterminal covers neighbors
    hv outside hr hq nonessential essential).2
  have ntS (x : Fin n) (hx : x ∈ N) : x ∉ S := fun h => neighbors_nonterminal x hx (terminals x h)
  have tnotN : t ∉ N := fun h => neighbors_nonterminal t h ht
  have hnd : (retain (List.finRange n) S).Nodup := List.Pairwise.filter _ (finRange_nodup n)
  obtain ⟨r, hrr, herr⟩ := remove_terminals_essential
    (E := PromoteGraph E S N) (T := PromoteTerminals T S N) (v := v) (t := t) N hnd
    (fun x hx => by simp [retain, mem_finRange x, ntS x hx])
    (fun _ hx => Or.inr hx) vnt (Or.inl ⟨ht, toutside⟩) tnotN hq promoted
  have vv : retain (retain (List.finRange n) S) N = retain (List.finRange n) (S ∪ N) := by
    unfold retain
    rw [List.filter_filter]
    congr 1
    funext x
    simp [Bool.and_comm]
  have ee : RemoveVertices (PromoteGraph E S N) N = RemoveVertices E (S ∪ N) := by
    funext x y
    simp only [RemoveVertices, PromoteGraph, Finset.mem_union, not_or]
    apply propext
    exact ⟨fun h => ⟨h.1.1, ⟨h.1.2.1, h.2.1⟩, ⟨h.1.2.2.1, h.2.2⟩⟩,
      fun h => ⟨⟨h.1, h.2.1.1, h.2.2.1, h.2.1.2⟩, h.2.1.2, h.2.2.2⟩⟩
  have tt : RemoveTerminals (PromoteTerminals T S N) N = RemoveTerminals T S := by
    funext x
    apply propext
    constructor
    · rintro ⟨h | h, hn⟩
      · exact h
      · exact False.elim (hn h)
    · intro h
      exact ⟨Or.inl h, fun hn => neighbors_nonterminal x hn h.1⟩
  rw [vv, ee, tt] at hrr herr
  exact ⟨r, hrr, herr⟩

end GyoriLovasz
