import GyoriLovasz.RuntimeVertexNetwork

namespace GyoriLovasz.Flow
open scoped BigOperators

def discountArc (G : Network n m) (a : Fin m) : Network n m :=
  {G with capacity := fun e => if e = a then 0 else G.capacity e}

theorem discount_cut_identity (G : Network n m) (a : Fin m) (unit : G.capacity a = 1)
    (S : Fin n → Bool) :
    cutCapacity G S = cutCapacity (discountArc G a) S +
      if S (G.tail a) && !S (G.head a) then 1 else 0 := by
  have term (e : Fin m) :
      (if S (G.tail e) && !S (G.head e) then G.capacity e else 0) =
        (if S ((discountArc G a).tail e) && !S ((discountArc G a).head e)
          then (discountArc G a).capacity e else 0) +
        (if e = a then (if S (G.tail a) && !S (G.head a) then 1 else 0) else 0) := by
    by_cases eq : e = a
    · subst e; simp [discountArc, unit]
    · simp [discountArc, eq]
  unfold cutCapacity
  simp_rw [term, Finset.sum_add_distrib]
  simp

end GyoriLovasz.Flow

namespace GyoriLovasz.VertexNetwork
open Flow

theorem minimum_discount_essential (E : Fin n → Fin n → Bool) (T : Fin n → Bool)
    (v t : Fin n) (nonterminal : T v = false) (terminal : T t = true) (r : Nat)
    (rank : HasRank (List.finRange n) (fun x y => E x y = true) (fun x => T x = true) v r)
    (S : Fin (n + n + 1) → Bool) (source : S (outside v) = true) (sink : S 0 = false)
    (minimum : ∀ U, U (outside v) = true → U 0 = false →
      cutCapacity (discountArc (network E T) (unitArc t)) S ≤
        cutCapacity (discountArc (network E T) (unitArc t)) U) :
    CutEssential (List.finRange n) (fun x y => E x y = true) (fun x => T x = true) v r t ↔
      cutCapacity (discountArc (network E T) (unitArc t)) S + 1 = r := by
  let C : Cut (Fin n) := fun x => if T x then .sep else .right
  have valid : Valid (fun x y => E x y = true) (fun x => T x = true) v C := by
    constructor
    · simp [C, nonterminal]
    · intro x hx; simp [C, hx]
    · intro x y he hx; simp [C]; split <;> decide
  have initial := discount_cut_identity (network E T) (unitArc t) (unitArc_capacity E T t) (encodeCut C)
  rw [encodeCut_capacity E T v C valid] at initial
  simp only [unitArc_tail, unitArc_head, encodeCut_inside, encodeCut_outside] at initial
  have ct : C t = .sep := by simp [C, terminal]
  simp [ct] at initial
  have min := minimum (encodeCut C) (by simp [valid.source]) rfl
  have smallC := valid_size_le_n C
  have identity := discount_cut_identity (network E T) (unitArc t) (unitArc_capacity E T t) S
  simp only [unitArc_tail, unitArc_head] at identity
  have bitBound : (if S (inside t) && !S (outside t) then 1 else 0) ≤ 1 := by split <;> omega
  have small : cutCapacity (network E T) S ≤ n := by omega
  have vd := decodeCut_valid E T v S source sink small
  have lower := rank.lower (decodeCut S) vd
  have upper := decodeCut_size_le E T S
  have rankLower : r ≤ cutCapacity (discountArc (network E T) (unitArc t)) S + 1 := by omega
  constructor
  · rintro ⟨D, hd, ht⟩
    have dcost := discount_cut_identity (network E T) (unitArc t) (unitArc_capacity E T t) (encodeCut D)
    rw [encodeCut_capacity E T v D hd.1, hd.2] at dcost
    simp only [unitArc_tail, unitArc_head, encodeCut_inside, encodeCut_outside, ht] at dcost
    simp at dcost
    have minD := minimum (encodeCut D) (by simp [hd.1.source]) rfl
    omega
  · intro eq
    have sep : decodeCut S t = .sep := by
      cases hi : S (inside t) <;> cases ho : S (outside t) <;>
        simp [hi, ho] at identity <;> try omega
      simp [decodeCut, hi, ho]
    exact ⟨decodeCut S, ⟨vd, by omega⟩, sep⟩

end GyoriLovasz.VertexNetwork
