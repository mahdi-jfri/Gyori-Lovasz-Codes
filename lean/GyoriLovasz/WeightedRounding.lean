import GyoriLovasz.Weighted

namespace GyoriLovasz
open Side
attribute [local instance] Classical.propDecidable

def PromoteGraph (E : Fin n → Fin n → Prop) (S N : Finset (Fin n)) : Fin n → Fin n → Prop :=
  fun x y => E x y ∧ x ∉ S ∧ y ∉ S ∧ x ∉ N

def PromoteTerminals (T : Fin n → Prop) (S N : Finset (Fin n)) : Fin n → Prop :=
  fun x => (T x ∧ x ∉ S) ∨ x ∈ N

noncomputable def leftOn (S : Finset (Fin n)) (D : Cut (Fin n)) : Cut (Fin n) :=
  fun x => if x ∈ S then left else D x

theorem size_leftOn (vertices : List (Fin n)) (S : Finset (Fin n)) (D : Cut (Fin n)) :
    size vertices (leftOn S D) = size (vertices.filter (fun x => decide (x ∉ S))) D := by
  classical
  induction vertices with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x ∈ S <;> simp [leftOn, size, hx, ih, Side.weight]

theorem size_filter_left (vertices : List (Fin n)) (S : Finset (Fin n)) (C : Cut (Fin n))
    (lefts : ∀ x ∈ S, C x = left) :
    size (vertices.filter (fun x => decide (x ∉ S))) C = size vertices C := by
  classical
  induction vertices with
  | nil => rfl
  | cons x xs ih =>
    have ih' : size (xs.filter (fun x => !decide (x ∈ S))) C = size xs C := by
      simpa only [decide_not] using ih
    by_cases hx : x ∈ S <;> simp [size, hx, ih, ih', lefts, Side.weight]

/-- The first, cut-theoretic stage of the Hall-deficient rounding argument:
replace the removed terminals by their pre-terminal neighborhood. -/
theorem promotion_preserves_essential {E : Fin n → Fin n → Prop} {T : Fin n → Prop}
    {v t : Fin n} {rank newrank : Nat} (S N : Finset (Fin n))
    (terminals : ∀ x ∈ S, T x) (_neighbors_nonterminal : ∀ x ∈ N, ¬T x)
    (covers : ∀ x y, ¬T x → y ∈ S → E x y → x ∈ N)
    (neighbors : ∀ x ∈ N, ∃ y ∈ S, E x y)
    (hv : ¬T v) (_outside : v ∉ N)
    (hr : HasRank (List.finRange n) E T v rank)
    (hs : HasRank ((List.finRange n).filter (fun x => decide (x ∉ S)))
      (PromoteGraph E S N) (PromoteTerminals T S N) v newrank)
    (nonessential : ∀ x ∈ S, ¬CutEssential (List.finRange n) E T v rank x)
    (essential : CutEssential (List.finRange n) E T v rank t) :
    newrank = rank ∧
      CutEssential ((List.finRange n).filter (fun x => decide (x ∉ S)))
        (PromoteGraph E S N) (PromoteTerminals T S N) v newrank t := by
  classical
  have vs : v ∉ S := fun h => hv (terminals v h)
  obtain ⟨C, hc, hct⟩ := essential
  have lefts : ∀ x ∈ S, C x = left := fun x hx => nonessential_left (terminals x hx) hc (nonessential x hx)
  have validC : Valid (PromoteGraph E S N) (PromoteTerminals T S N) v C := by
    refine ⟨hc.1.source, ?_, fun x y he => hc.1.no_cross x y he.1⟩
    intro x hx
    rcases hx with old | neighbor
    · exact hc.1.terminals x old.1
    · obtain ⟨y, hy, edge⟩ := neighbors x neighbor
      exact fun hright => hc.1.no_cross x y edge hright (lefts y hy)
  have csize := size_filter_left (List.finRange n) S C lefts
  have lower := hs.lower C validC
  obtain ⟨D, hd⟩ := hs.witness
  have lifted : Valid E T v (leftOn S D) := by
    refine ⟨by simp [leftOn, vs, hd.1.source], ?_, ?_⟩
    · intro x hx
      by_cases xs : x ∈ S
      · simp [leftOn, xs]
      · simpa [leftOn, xs] using hd.1.terminals x (Or.inl ⟨hx, xs⟩)
    · intro x y edge hxr hyl
      have xs : x ∉ S := by intro hx; simp [leftOn, hx] at hxr
      have xr : D x = right := by simpa [leftOn, xs] using hxr
      have xn : x ∉ N := fun hx => hd.1.terminals x (Or.inr hx) xr
      have xnt : ¬T x := fun ht => hd.1.terminals x (Or.inl ⟨ht, xs⟩) xr
      by_cases ys : y ∈ S
      · exact xn (covers x y xnt ys edge)
      · have yl : D y = left := by simpa [leftOn, ys] using hyl
        exact hd.1.no_cross x y ⟨edge, xs, ys, xn⟩ xr yl
  have upper := hr.lower _ lifted
  have lsize := size_leftOn (List.finRange n) S D
  have cs := hc.2
  have ds := hd.2
  have equal : newrank = rank := by omega
  exact ⟨equal, C, ⟨validC, by omega⟩, hct⟩

end GyoriLovasz
