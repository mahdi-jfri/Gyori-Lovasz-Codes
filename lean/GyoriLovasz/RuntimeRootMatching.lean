import GyoriLovasz.RuntimeRootMask
import GyoriLovasz.RuntimeSaturationPrune
import GyoriLovasz.RuntimeMatchingHall

namespace GyoriLovasz
open TransportNetwork

def rootNeighbors (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k) :
    Costed.Computation (Vector (Vector Bool n) k) :=
  let mask := rootMask roots
  let result := Costed.tabulate k (fun i => Costed.tabulate n
    (fun v => (!mask.1[v.val] && E[v.val][roots[i.val].val], 5)))
  (result.1, mask.2 + result.2 + 1)

theorem rootNeighbors_correct (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (i : Fin k) (v : Fin n) :
    (rootNeighbors E roots).1[i.val][v.val] = true ↔
      ¬RootSet (fun i => roots[i.val]) v ∧ E[v.val][roots[i.val].val] = true := by
  simp only [rootNeighbors, Costed.tabulate_value, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff]
  exact and_congr (not_congr (rootMask_correct roots v)) Iff.rfl

def rootNeighborBudget (n k : Nat) := rootMaskBudget n k +
  (2 * k * k + k * (2 * n * n + 11 * n + 9) + 3) + 1

theorem rootNeighbors_cost (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k) :
    (rootNeighbors E roots).2 ≤ rootNeighborBudget n k := by
  have hm := rootMask_cost roots
  have ht := Costed.tabulate_cost k (fun i => Costed.tabulate n
    (fun v => (!(rootMask roots).1[v.val] && E[v.val][roots[i.val].val], 5)))
    (2 * n * n + n * (5 + 6) + 3) (fun i => Costed.tabulate_cost n _ 5 (by intros; rfl))
  dsimp only [rootNeighbors, rootNeighborBudget]
  norm_num only at ht
  simp only [Nat.mul_comm n 11, Nat.add_assoc] at ht ⊢
  norm_num only at ht
  omega

theorem rootNeighbors_family (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k) :
    neighborFamily (fun i v => (rootNeighbors E roots).1[i.val][v.val]) =
      predecessorSet (fun x y => E[x.val][y.val] = true) (fun i => roots[i.val]) := by
  classical
  funext i
  ext v
  simp only [neighborFamily, predecessorSet, Finset.mem_filter, Finset.mem_univ, true_and,
    rootNeighbors_correct]

/-- Inclusion-minimal matching failure suffices for the nonessentiality
certificate needed when removing a rounded block. -/
theorem local_hall_nonessential {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    (hinj : Function.Injective roots) (S : Finset (Fin k))
    (deficient : (S.biUnion (predecessorSet E roots)).card < S.card)
    (minimal : ∀ U, U ⊂ S → U.card ≤ (U.biUnion (predecessorSet E roots)).card) :
    ∀ i ∈ S, ∀ v, ∀ hv : ¬RootSet roots v,
      v ∉ S.biUnion (predecessorSet E roots) → ¬Essential E (RootSet roots) v hv (roots i) := by
  classical
  intro j hj v hv outside
  obtain ⟨g, gi, gm⟩ := deficient_bijection_local S deficient minimal hj
  apply neighborhood_matching_nonessential (S.image roots) (S.biUnion (predecessorSet E roots)) (fun p => roots (g p))
    (fun x hx => by obtain ⟨a, _, he⟩ := Finset.mem_image.mp hx; exact ⟨a, he⟩)
    (fun p hp => by
      obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_filter.mp ha).2.1)
    (fun x y hnt hy edge => by
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hy
      exact Finset.mem_biUnion.mpr ⟨a, ha, by simp [predecessorSet, hnt, he, edge]⟩)
    (fun p hp => ⟨Finset.mem_image.mpr ⟨g p, (gm p hp).1, rfl⟩,
      fun he => (gm p hp).2.1 (hinj he), (gm p hp).2.2⟩)
    (fun _ hp _ hq he => gi hp hq (hinj he))
    (Finset.mem_image.mpr ⟨j, hj, rfl⟩) outside (cutRank_spec E (RootSet roots) v hv)

theorem pruned_roots_deficient (E : Vector (Vector Bool n) n) (roots : Vector (Fin n) k)
    (selected : Vector Bool k)
    (failure : ¬Saturates (fun i v => (rootNeighbors E roots).1[i.val][v.val]) (fun i => selected[i.val])) :
    let S := SaturationPrune.selectedSet (SaturationPrune.prune (rootNeighbors E roots).1 selected).1
    S.Nonempty ∧
      (S.biUnion (predecessorSet (fun x y => E[x.val][y.val] = true) (fun i => roots[i.val]))).card < S.card ∧
      ∀ U, U ⊂ S → U.card ≤
        (U.biUnion (predecessorSet (fun x y => E[x.val][y.val] = true) (fun i => roots[i.val]))).card := by
  have h := SaturationPrune.prune_correct (rootNeighbors E roots).1 selected failure
  have bad := (SaturationPrune.bad_correct _ _).mp h.2.2.1
  have minimal : ∀ U, U ⊂ SaturationPrune.selectedSet (SaturationPrune.prune (rootNeighbors E roots).1 selected).1 →
      Saturates (fun i v => (rootNeighbors E roots).1[i.val][v.val]) (fun i => decide (i ∈ U)) := by
    intro U hu
    have good := h.2.2.2 U hu
    by_contra hn
    have no := (SaturationPrune.bad_correct _ _).mpr hn
    rw [good] at no
    contradiction
  have result := minimal_unsaturated_deficient _ _ bad minimal
  rw [rootNeighbors_family] at result
  exact ⟨h.1, result⟩

end GyoriLovasz
