import GyoriLovasz.WeightedRoundingInduction
import GyoriLovasz.WeightedInitialization

namespace GyoriLovasz
open scoped BigOperators

/-- Complete induction for the normalized generalized weighted theorem. -/
theorem normalized_weighted_partition : ∀ n, NormalizedWeightedStatement n := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k E roots weight capacity bound hinj rootzero hb weights initial
    obtain ⟨split, feasible⟩ := initial
    by_cases allroot : ∀ v, RootSet roots v
    · exact weighted_all_roots hinj rootzero allroot
    · obtain ⟨v, hv⟩ := not_forall.mp allroot
      obtain ⟨j, positivej⟩ := weighted_positive_root feasible hv (weights v hv).1
      have hn : 1 < n := by
        by_contra h
        have he : roots j = v := Fin.ext (by have h1 := (roots j).isLt; have h2 := v.isLt; omega)
        exact hv ⟨j, he⟩
      cases n with
      | zero => omega
      | succ m =>
        have hm : 0 < m := by omega
        by_cases zero : ∃ i, capacity i = 0
        · obtain ⟨i, hi⟩ := zero
          cases k with
          | zero => exact Fin.elim0 i
          | succ l =>
            have hl : 0 < l := by
              by_contra h
              have eqij : i = j := Fin.ext (by have h1 := i.isLt; have h2 := j.isLt; omega)
              have hi' : capacity j = 0 := eqij ▸ hi
              omega
            obtain ⟨s, hs⟩ := exists_erase_reindex hl i
              (fun _ _ => False) (fun _ => False) (fun _ _ h => False.elim h) (fun h => h)
            obtain ⟨r, hr⟩ := exists_erase_reindex hm (roots i)
              (DeleteVertex E (roots i)) (WithoutTerminal (RootSet roots) (roots i))
              (fun _ _ h => h.2) (fun h => h.2 rfl)
            have sret (a : Fin (l+1)) (ha : a ≠ i) : i.succAbove (s a) = a :=
              hs.retract a ((List.mem_erase_of_ne ha).mpr (mem_finRange a))
            obtain ⟨newinj, newfeasible⟩ := weighted_terminal_reindexed hinj feasible hi hs.inverse
              sret (Fin.succAbove_ne i) hr
            have rootmem (a : Fin l) : roots (i.succAbove a) ∈ (List.finRange (m+1)).erase (roots i) :=
              hr.terminals _ ⟨⟨i.succAbove a, rfl⟩, fun he => Fin.succAbove_ne i a (hinj he)⟩
            have oldnt (x : Fin m)
                (hx : ¬RootSet (fun a => r (roots (i.succAbove a))) x) :
                ¬RootSet roots ((roots i).succAbove x) := by
              rintro ⟨a, ha⟩
              have ai : a ≠ i := by intro he; subst a; exact Fin.succAbove_ne (roots i) x ha.symm
              apply hx
              refine ⟨s a, ?_⟩
              dsimp only
              rw [sret a ai, ha, hr.inverse x]
            obtain ⟨label, part⟩ := ih m (by omega) l
              (fun x y => DeleteVertex E (roots i) ((roots i).succAbove x) ((roots i).succAbove y))
              (fun a => r (roots (i.succAbove a))) (fun x => weight ((roots i).succAbove x))
              (fun a => capacity (i.succAbove a)) bound newinj
              (fun a => by dsimp only; rw [hr.retract _ (rootmem a)]; exact rootzero _)
              hb (fun x hx => weights _ (oldnt x hx)) ⟨_, newfeasible⟩
            have lifted := weighted_partition_reindex (limit := fun a => capacity a + bound - 1)
              hr Fin.succAbove_right_injective rootmem part
            have ieq := hs.image_univ.trans (finRange_erase_toFinset i)
            rw [finRange_erase_toFinset, ieq] at lifted
            exact ⟨_, weighted_reconstruct_terminal (Finset.mem_univ _) (Finset.mem_univ _) (rootzero i) lifted⟩
        · have positive : ∀ i, 0 < capacity i := by
            intro i
            have ne : capacity i ≠ 0 := fun he => zero ⟨i, he⟩
            omega
          have hk : 0 < k := by have hj := j.isLt; omega
          obtain ⟨F, sub, ⟨newsplit, newfeasible⟩, reduction⟩ := weighted_reduction hk ⟨split, feasible⟩
          rcases reduction with contract | round
          · obtain ⟨i, p, pnt, edge, sole⟩ := contract
            obtain ⟨r, hr⟩ := exists_erase_reindex hm p (Contract F p (roots i)) (RootSet roots)
              (fun _ _ he => ⟨he.1, he.2.1⟩) pnt
            have newinj := reindex_roots_injective hr hinj
            have reduced := weighted_contraction_reindexed hinj newfeasible pnt edge sole hr
            have rootmem (a : Fin k) := hr.terminals (roots a) ⟨a, rfl⟩
            obtain ⟨label, part⟩ := ih m (by omega) k
              (fun x y => Contract F p (roots i) (p.succAbove x) (p.succAbove y))
              (fun a => r (roots a)) (fun x => weight (p.succAbove x))
              (fun a => capacity a - if a = i then weight p else 0) bound newinj
              (fun a => by dsimp only; rw [hr.retract _ (rootmem a)]; exact rootzero _)
              hb (fun x hx => weights _ (fun ht => hx ((reindex_rootSet hr x).mp ht))) ⟨_, reduced⟩
            have lifted := weighted_partition_reindex (d := id)
              (limit := fun a => capacity a - (if a = i then weight p else 0) + bound - 1)
              hr Function.injective_id rootmem part
            simp only [Finset.image_id, finRange_erase_toFinset, id_eq] at lifted
            have restored := weighted_reconstruct_contraction (Finset.mem_univ p) (Finset.mem_univ i) edge lifted
            have fits := (split_sole_neighbor hinj newfeasible pnt edge sole).2.1
            have bounded := restored.mono_limit (b := fun a => capacity a + bound - 1) (by
              intro a _
              by_cases ai : a = i
              · subst a
                simp only [if_pos rfl]
                exact weighted_contraction_bound fits hb (Nat.le_refl _)
              · simp [ai, Ne.symm ai])
            exact ⟨_, bounded.mono_edges sub⟩
          · obtain ⟨S, snonempty, f, fi, fm, nonessential⟩ := hall_rounding_data hinj round
            obtain ⟨label, part⟩ := weighted_rounding_induction ih hinj rootzero hb weights
              newfeasible positive S snonempty f fi fm nonessential
            exact ⟨label, part.mono_edges sub⟩

/-- The generalized weighted Győri–Lovász existence theorem for all finite
numbers of roots and arbitrary positive integral nonterminal weights. -/
theorem generalized_weighted_gyori_lovasz : WeightedTheoremStatement := by
  classical
  intro n k E roots weight capacity bound hinj hb weights initial
  obtain ⟨split, feasible⟩ := initial
  let w := fun v => if RootSet roots v then 0 else weight v
  have nonroot (v : Fin n) (hv : ¬RootSet roots v) : w v = weight v := by simp [w, hv]
  have normalized : SplitFeasible E roots w capacity split :=
    ⟨feasible.1, fun v hv => (feasible.2.1 v hv).trans (nonroot v hv).symm, feasible.2.2⟩
  obtain ⟨label, part⟩ := normalized_weighted_partition n k E roots w capacity bound hinj
    (fun i => by simp [w, show RootSet roots (roots i) from ⟨i, rfl⟩]) hb
    (fun v hv => by rw [nonroot v hv]; exact weights v hv) ⟨split, normalized⟩
  refine ⟨label, fun i => (part.2.1 i (Finset.mem_univ _)).2, ?_, ?_⟩
  · intro i
    have eq : (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots v ∧ label v = i), weight v) =
        partLoad Finset.univ w label i := by
      rw [Finset.sum_filter]
      unfold partLoad
      apply Finset.sum_congr rfl
      intro v _
      by_cases ht : RootSet roots v <;> by_cases hl : label v = i <;> simp [w, ht, hl]
    rw [eq]
    exact part.2.2.1 i (Finset.mem_univ _)
  · intro i x hx
    exact (part.2.2.2 i (Finset.mem_univ _) x (Finset.mem_univ _) hx).mono_allowed (fun _ hy => hy.2)

attribute [local instance] Classical.propDecidable

/-- The weighted connectivity corollary: sufficient total capacity initializes
the integral split required by the generalized theorem. -/
theorem weighted_gyori_lovasz {E : Fin n → Fin n → Prop} (roots : Fin k → Fin n)
    (weight : Fin n → Nat) (capacity : Fin k → Nat) (bound : Nat)
    (hk : 0 < k) (connected : KConnected E k) (hinj : Function.Injective roots)
    (hb : 0 < bound) (weights : ∀ v, ¬RootSet roots v → 0 < weight v ∧ weight v ≤ bound)
    (balance : (∑ v ∈ Finset.univ.filter (fun v => ¬RootSet roots v), weight v) ≤ ∑ i, capacity i) :
    WeightedPartition E roots weight capacity bound :=
  generalized_weighted_gyori_lovasz n k E roots weight capacity bound hinj hb weights
    (kconnected_initialize_split roots weight capacity hk connected hinj balance)

end GyoriLovasz
