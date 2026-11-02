import GyoriLovasz.RuntimePartitionProgram
import GyoriLovasz.WeightedInitialization

namespace GyoriLovasz.WordInstance
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def encodeUnweighted (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (sizes : Vector Nat k) : Costed.Computation (Input n k) :=
  let w := Costed.tabulate n (fun _ => ([true], 1))
  let c := Costed.tabulate k (fun i => Binary.countWord (sizes[i.val] - 1))
  (⟨E, roots, w.1, c.1⟩, w.2 + c.2 + 1)

@[simp] theorem encodeUnweighted_weight (E : Vector (Vector Bool n) n)
    (roots : Vector (Fin n) k) (sizes : Vector Nat k) (v : Fin n) :
    weights (encodeUnweighted E roots sizes).1 v = 1 := by
  simp [weights, encodeUnweighted, Costed.tabulate_value, Binary.value]

@[simp] theorem encodeUnweighted_capacity (E : Vector (Vector Bool n) n)
    (roots : Vector (Fin n) k) (sizes : Vector Nat k) (i : Fin k) :
    capacities (encodeUnweighted E roots sizes).1 i = sizes[i.val] - 1 := by
  simp [capacities, encodeUnweighted, Costed.tabulate_value, Binary.countWord_value]

theorem prescribed_size_le (sizes : Vector Nat k) (total : (∑ i : Fin k, sizes[i.val]) = n)
    (i : Fin k) : sizes[i.val] ≤ n := by
  rw [← total]
  exact Finset.single_le_sum (f := fun i : Fin k => sizes[i.val]) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem encodeUnweighted_bounds (E : Vector (Vector Bool n) n)
    (roots : Vector (Fin n) k) (sizes : Vector Nat k) (hn : 0 < n)
    (total : (∑ i : Fin k, sizes[i.val]) = n) : Bounded (encodeUnweighted E roots sizes).1 n := by
  constructor
  · intro v
    simpa [encodeUnweighted, Costed.tabulate_value] using hn
  · intro i
    simp only [encodeUnweighted, Costed.tabulate_value]
    exact (Binary.countWord_length _).trans ((Nat.sub_le _ _).trans (prescribed_size_le sizes total i))

theorem unit_balance (roots : Fin k → Fin n) (sizes : Fin k → Nat)
    (inj : Function.Injective roots) (positive : ∀ i, 0 < sizes i)
    (total : (∑ i, sizes i) = n) :
    (∑ _v ∈ Finset.univ.filter (fun v => ¬RootSet roots v), (1 : Nat)) ≤ ∑ i, (sizes i - 1) := by
  have hp := positive_capacity_sum (List.finRange k) sizes (fun i _ => positive i)
  rw [sumValues_finRange, sumValues_finRange, List.length_finRange, total] at hp
  have hl := nonterminals_length roots (fun _ _ h => inj h)
  have listset : (nonterminals roots).toFinset = Finset.univ.filter (fun v => ¬RootSet roots v) := by
    ext v
    simp [mem_nonterminals]
  have hc := List.toFinset_card_of_nodup (nonterminals_nodup roots)
  rw [listset] at hc
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  omega

theorem encodeUnweighted_initial (E : Vector (Vector Bool n) n)
    (roots : Vector (Fin n) k) (sizes : Vector Nat k)
    (hk : 0 < k) (connected : KConnected (fun x y : Fin n => E[x.val][y.val] = true) k)
    (inj : Function.Injective (fun i : Fin k => roots[i.val]))
    (positive : ∀ i : Fin k, 0 < sizes[i.val]) (total : (∑ i : Fin k, sizes[i.val]) = n) :
    ∃ x, SplitFeasible (relation (encodeUnweighted E roots sizes).1)
      (root (encodeUnweighted E roots sizes).1) (weights (encodeUnweighted E roots sizes).1)
      (capacities (encodeUnweighted E roots sizes).1) x := by
  apply kconnected_initialize_split _ _ _ hk connected inj
  simpa only [encodeUnweighted_weight, encodeUnweighted_capacity] using unit_balance _ _ inj positive total

end GyoriLovasz.WordInstance
