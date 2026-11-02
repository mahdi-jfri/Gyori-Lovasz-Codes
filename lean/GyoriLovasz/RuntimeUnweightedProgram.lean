import GyoriLovasz.RuntimeWeightedProgram
import GyoriLovasz.RuntimeUnitCardinality

namespace GyoriLovasz.WordInstance
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def unweightedProgram (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (sizes : Vector Nat k) (hk : 0 < k)
    (connected : KConnected (fun x y : Fin n => E[x.val][y.val] = true) k)
    (inj : Function.Injective (fun i : Fin k => roots[i.val]))
    (positive : ∀ i : Fin k, 0 < sizes[i.val]) (total : (∑ i : Fin k, sizes[i.val]) = n) :
    Costed.Computation (Vector (Fin k) n) :=
  let s := encodeUnweighted E roots sizes
  let result := weightedProgram s.1 n 1 inj (by omega)
    (by intro v _; have hw : weights s.1 v = 1 := encodeUnweighted_weight E roots sizes v; omega)
    (encodeUnweighted_initial E roots sizes hk connected inj positive total)
    (encodeUnweighted_bounds E roots sizes (by have h := connected.1; omega) total)
  (result.1, s.2 + result.2 + 1)

def PrescribedLabels (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (sizes : Vector Nat k) (labels : Vector (Fin k) n) : Prop :=
  (∀ i : Fin k, labels[roots[i.val].val] = i) ∧
  (∀ i : Fin k, countTrue (List.finRange n) (fun v => labels[v.val] = i) = sizes[i.val]) ∧
  (∀ i v, labels[v.val] = i → ReachWithin (fun x y : Fin n => E[x.val][y.val] = true)
    (fun x => labels[x.val] = i) v roots[i.val])

theorem unweightedProgram_correct (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (sizes : Vector Nat k) (hk : 0 < k)
    (connected : KConnected (fun x y : Fin n => E[x.val][y.val] = true) k)
    (inj : Function.Injective (fun i : Fin k => roots[i.val]))
    (positive : ∀ i : Fin k, 0 < sizes[i.val]) (total : (∑ i : Fin k, sizes[i.val]) = n) :
    PrescribedLabels E roots sizes (unweightedProgram E roots sizes hk connected inj positive total).1 := by
  have result := weightedProgram_correct (encodeUnweighted E roots sizes).1 n 1 inj (by omega)
    (by intros; simp only [encodeUnweighted_weight]; omega)
    (encodeUnweighted_initial E roots sizes hk connected inj positive total)
    (encodeUnweighted_bounds E roots sizes (by have h := connected.1; omega) total)
  refine ⟨result.1, ?_, result.2.2⟩
  apply unit_upper_bounds_exact (fun i : Fin k => roots[i.val]) (fun i : Fin k => sizes[i.val])
    (fun v : Fin n => (unweightedProgram E roots sizes hk connected inj positive total).1[v.val])
    result.1 positive total
  intro i
  have h := result.2.1 i
  simpa only [encodeUnweighted_weight, encodeUnweighted_capacity, Nat.add_sub_cancel,
    Finset.sum_const, smul_eq_mul, mul_one] using h

theorem encodeUnweighted_cost (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (sizes : Vector Nat k) (hk : k ≤ n) (total : (∑ i : Fin k, sizes[i.val]) = n) :
    (encodeUnweighted E roots sizes).2 ≤ RuntimePolynomial.encodingBudget n := by
  have hw := Costed.tabulate_cost n (fun _ => ([true], 1)) 1 (by intros; rfl)
  have hc := Costed.tabulate_cost k (fun i => Binary.countWord (sizes[i.val] - 1))
    (n * (7 * n + 3) + 1) (by
      intro i
      apply (Binary.countWord_cost _).trans
      have hi := (Nat.sub_le sizes[i.val] 1).trans (prescribed_size_le sizes total i)
      gcongr)
  have bound : 2 * k * k + k * (n * (7 * n + 3) + 1 + 6) + 3 ≤
      2 * n * n + n * (n * (7 * n + 3) + 7) + 3 := by gcongr
  change (Costed.tabulate n (fun _ => ([true], 1))).2 +
    (Costed.tabulate k (fun i => Binary.countWord (sizes[i.val] - 1))).2 + 1 ≤ _
  unfold RuntimePolynomial.encodingBudget
  norm_num only at hw hc
  omega

theorem unweightedProgram_cost (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (sizes : Vector Nat k) (hk : 0 < k)
    (connected : KConnected (fun x y : Fin n => E[x.val][y.val] = true) k)
    (inj : Function.Injective (fun i : Fin k => roots[i.val]))
    (positive : ∀ i : Fin k, 0 < sizes[i.val]) (total : (∑ i : Fin k, sizes[i.val]) = n) :
    (unweightedProgram E roots sizes hk connected inj positive total).2 ≤ RuntimePolynomial.unweightedBudget n := by
  have he := encodeUnweighted_cost E roots sizes (Nat.le_of_lt connected.1) total
  have hw := weightedProgram_cost (encodeUnweighted E roots sizes).1 n 1 inj (by omega)
    (by intros; simp only [encodeUnweighted_weight]; omega)
    (encodeUnweighted_initial E roots sizes hk connected inj positive total)
    (encodeUnweighted_bounds E roots sizes (by have h := connected.1; omega) total)
  change _ + _ + 1 ≤ _
  unfold RuntimePolynomial.unweightedBudget
  exact Nat.add_le_add_right (Nat.add_le_add he hw) 1

theorem unweighted_polynomial_time :
    ∃ p : Polynomial Nat, ∀ (n k : Nat) (E : Vector (Vector Bool n) n)
      (roots : Vector (Fin n) k) (sizes : Vector Nat k) (hk : 0 < k)
      (connected : KConnected (fun x y : Fin n => E[x.val][y.val] = true) k)
      (inj : Function.Injective (fun i : Fin k => roots[i.val]))
      (positive : ∀ i : Fin k, 0 < sizes[i.val]) (total : (∑ i : Fin k, sizes[i.val]) = n),
      PrescribedLabels E roots sizes (unweightedProgram E roots sizes hk connected inj positive total).1 ∧
      (unweightedProgram E roots sizes hk connected inj positive total).2 ≤ p.eval n := by
  obtain ⟨p, hp⟩ := RuntimePolynomial.unweighted_polynomial
  refine ⟨p, fun n k E roots sizes hk connected inj positive total => ?_⟩
  exact ⟨unweightedProgram_correct E roots sizes hk connected inj positive total,
    (unweightedProgram_cost E roots sizes hk connected inj positive total).trans_eq (hp n)⟩

end GyoriLovasz.WordInstance
