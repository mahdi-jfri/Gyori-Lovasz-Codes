import GyoriLovasz.RuntimeWordVertexNetwork
import GyoriLovasz.RuntimeEssentialCut

namespace GyoriLovasz.Flow
open Binary

def discountWords (s : WordResidual n m) (a : Fin m) : Costed.Computation (WordResidual n m) :=
  let caps := Costed.tabulate m (fun e => (if e = a then [] else s.capacity[e.val], 4))
  ({s with capacity := caps.1}, caps.2 + 1)

theorem discountWords_network (s : WordResidual n m) (a : Fin m) :
    decodeNetwork (discountWords s a).1 = discountArc (decodeNetwork s) a := by
  simp only [decodeNetwork, discountWords, Costed.tabulate_value, discountArc]
  congr 1
  funext e
  split <;> rfl

theorem discountWords_codes (s : WordResidual n m) (correct : VertexCodesCorrect s) (a : Fin m) :
    VertexCodesCorrect (discountWords s a).1 := correct

theorem discountWords_bounds (s : WordResidual n m) (B : Nat) (bound : WordResidualBound s B) (a : Fin m) :
    WordResidualBound (discountWords s a).1 B := by
  constructor
  · intro e
    refine ⟨?_, (bound.1 e).2⟩
    simp only [discountWords, Costed.tabulate_value]
    split
    · simp
    · exact (bound.1 e).1
  · exact bound.2

theorem discountWords_cost (s : WordResidual n m) (a : Fin m) :
    (discountWords s a).2 ≤ 2 * m * m + 10 * m + 4 := by
  have h := Costed.tabulate_cost m (fun e => (if e = a then [] else s.capacity[e.val], 4)) 4
    (by intros; exact Nat.le_refl _)
  dsimp only [discountWords]
  omega

end GyoriLovasz.Flow

namespace GyoriLovasz.VertexNetwork
open Flow Binary

def essentialWords (E : Vector (Vector Bool n) n) (T : Vector Bool n) (v t : Fin n) : Bool × Nat :=
  let built := build E T
  let discounted := discountWords built.1 (unitArc t)
  let normal := minValueWords built.1 (outside v) 0 (n + n + 1)
  let lowered := minValueWords discounted.1 (outside v) 0 (n + n + 1)
  let plus := addCarry lowered.1 [] true
  let cmp := compareWords plus.1 normal.1
  (cmp.1.2, built.2 + discounted.2 + normal.2 + lowered.2 + plus.2 + cmp.2 + 3)

theorem essentialWords_correct (E : Vector (Vector Bool n) n) (T : Vector Bool n) (v t : Fin n)
    (nonterminal : T[v.val] = false) (terminal : T[t.val] = true) :
    (essentialWords E T v t).1 = true ↔
      Essential (fun x y => E[x.val][y.val] = true) (fun x => T[x.val] = true) v
        (by simp [nonterminal]) t := by
  have distinct : outside v ≠ (0 : Fin (n + n + 1)) := Fin.succ_ne_zero _
  obtain ⟨S, hs, ht, hv, hmin⟩ := minValueWords_spec (build E T).1 (build_codes E T)
    (outside v) 0 distinct (n + n + 1) (build_bounds E T)
  rw [build_network] at hv hmin
  have rank := minimum_network_rank (fun x y => E[x.val][y.val]) (fun x => T[x.val]) v nonterminal S hs ht hmin
  obtain ⟨D, ds, dt, dv, dmin⟩ := minValueWords_spec (discountWords (build E T).1 (unitArc t)).1
    (discountWords_codes _ (build_codes E T) _) (outside v) 0 distinct (n + n + 1)
    (discountWords_bounds _ _ (build_bounds E T) _)
  rw [discountWords_network, build_network] at dv dmin
  have eq := hasRank_unique (cutRank_spec (fun x y => E[x.val][y.val] = true)
    (fun x => T[x.val] = true) v (by simp [nonterminal])) rank
  have detect := minimum_discount_essential (fun x y => E[x.val][y.val]) (fun x => T[x.val])
    v t nonterminal terminal _ rank D ds dt dmin
  dsimp only [essentialWords]
  rw [(compareWords_correct _ _).2, addCarry_correct]
  simp only [value, Nat.add_zero, if_true]
  rw [hv, dv]
  unfold Essential
  rw [eq]
  exact detect.symm

def essentialBudget (n : Nat) :=
  buildBudget n + (2 * (n + (n * n + n)) * (n + (n * n + n)) + 10 * (n + (n * n + n)) + 4) +
  2 * (maxFlowBudget (n + n + 1) (n + (n * n + n)) (n + n + 1) + 2) +
  16 * maxFlowWordLength (n + n + 1) (n + (n * n + n)) (n + n + 1) + 16

theorem essentialWords_cost (E : Vector (Vector Bool n) n) (T : Vector Bool n) (v t : Fin n) :
    (essentialWords E T v t).2 ≤ essentialBudget n := by
  have hb := build_cost E T
  have hd := discountWords_cost (build E T).1 (unitArc t)
  have hn := minValueWords_cost (build E T).1 (build_codes E T) (outside v) 0 _ (build_bounds E T)
  have hl := minValueWords_cost (discountWords (build E T).1 (unitArc t)).1
    (discountWords_codes _ (build_codes E T) _) (outside v) 0 _ (discountWords_bounds _ _ (build_bounds E T) _)
  have hnl := minValueWords_length (build E T).1 (build_codes E T) (outside v) 0 _ (build_bounds E T)
  have hll := minValueWords_length (discountWords (build E T).1 (unitArc t)).1
    (discountWords_codes _ (build_codes E T) _) (outside v) 0 _ (discountWords_bounds _ _ (build_bounds E T) _)
  have ha := addCarry_steps (minValueWords (discountWords (build E T).1 (unitArc t)).1 (outside v) 0 (n + n + 1)).1 [] true
  have hal := addCarry_length (minValueWords (discountWords (build E T).1 (unitArc t)).1 (outside v) 0 (n + n + 1)).1 [] true
  have hc := compareWords_steps
    (addCarry (minValueWords (discountWords (build E T).1 (unitArc t)).1 (outside v) 0 (n + n + 1)).1 [] true).1
    (minValueWords (build E T).1 (outside v) 0 (n + n + 1)).1
  simp only [List.length_nil, Nat.max_zero] at ha hal
  dsimp only [essentialWords, essentialBudget]
  omega

end GyoriLovasz.VertexNetwork
