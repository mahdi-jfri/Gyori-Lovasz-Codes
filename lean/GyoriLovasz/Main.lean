import GyoriLovasz.ShrinkTerminal

namespace GyoriLovasz

theorem positive_capacity_vertex {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {capacity : Fin k → Nat} {label : Fin n → Fin k}
    (feasible : FeasibleAssignment E roots capacity label) {i : Fin k}
    (positive : 0 < capacity i) : ∃ v, ¬RootSet roots v ∧ label v = i := by
  classical
  have cnt := feasible.2 i
  rw [countTrue_filter_length] at cnt
  have len : 0 < ((nonterminals roots).filter (fun x => decide (label x = i))).length := by omega
  obtain ⟨v, hv⟩ := List.exists_mem_of_length_pos len
  obtain ⟨hm, hl⟩ := List.mem_filter.mp hv
  exact ⟨v, mem_nonterminals.mp hm, by simpa using hl⟩

theorem positive_capacity_two_vertices {E : Fin n → Fin n → Prop}
    {roots : Fin k → Fin n} {capacity : Fin k → Nat} {label : Fin n → Fin k}
    (feasible : FeasibleAssignment E roots capacity label) {i : Fin k}
    (positive : 0 < capacity i) : 1 < n := by
  obtain ⟨v, hv, _⟩ := positive_capacity_vertex feasible positive
  by_cases hn : 1 < n
  · exact hn
  · have he : roots i = v := Fin.ext (by have h1 := (roots i).isLt; have h2 := v.isLt; omega)
    exact False.elim (hv ⟨i, he⟩)

/-- Every cut-essential capacitated assignment produces a connected rooted
partition. The induction handles terminal removal and contraction on genuinely
smaller graphs; no recursive partition hypothesis is left as an axiom. -/
theorem feasible_partition : ∀ (n k : Nat) (E : Fin n → Fin n → Prop)
    (roots : Fin k → Fin n) (capacity : Fin k → Nat) (label : Fin n → Fin k),
    Function.Injective roots → FeasibleAssignment E roots capacity label →
      PrescribedPartition E roots (fun i => capacity i + 1) := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k E roots capacity label hinj feasible
    by_cases allzero : ∀ i, capacity i = 0
    · exact all_zero_partition hinj feasible allzero
    · obtain ⟨j, hj⟩ := not_forall.mp allzero
      have positivej : 0 < capacity j := by omega
      have hn := positive_capacity_two_vertices feasible positivej
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
              by_cases hl : 0 < l
              · exact hl
              · have eqij : i = j := Fin.ext (by have h1 := i.isLt; have h2 := j.isLt; omega)
                have hi' : capacity j = 0 := eqij ▸ hi
                omega
            obtain ⟨s, hs⟩ := exists_erase_reindex hl i
              (fun _ _ => False) (fun _ => False) (fun _ _ h => False.elim h) (fun h => h)
            obtain ⟨r, hr⟩ := exists_erase_reindex hm (roots i)
              (DeleteVertex E (roots i)) (WithoutTerminal (RootSet roots) (roots i))
              (fun _ _ h => h.2) (fun h => h.2 rfl)
            have sret (a : Fin (l+1)) (ha : a ≠ i) : i.succAbove (s a) = a :=
              hs.retract a ((List.mem_erase_of_ne ha).mpr (mem_finRange a))
            obtain ⟨newinj, newfeasible⟩ := terminal_feasible_reindexed hinj feasible hi hs.inverse
              sret (Fin.succAbove_ne i) hr
            -- Use the explicitly reindexed graph and assignment in the induction.
            have part := ih m (by omega) l
              (fun x y => DeleteVertex E (roots i) ((roots i).succAbove x) ((roots i).succAbove y))
              (fun a => r (roots (i.succAbove a))) (fun a => capacity (i.succAbove a))
              (fun x => s (label ((roots i).succAbove x))) newinj newfeasible
            have rootmem (a : Fin l) : roots (i.succAbove a) ∈ (List.finRange (m+1)).erase (roots i) :=
              hr.terminals _ ⟨⟨i.succAbove a, rfl⟩, fun he => Fin.succAbove_ne i a (hinj he)⟩
            obtain ⟨oldlabel, oldpart⟩ := reindex_partition hr rootmem part
            have indexed := PartitionOn.map_indices (roots := roots)
              (sizes := fun a => capacity a + 1) i.succAbove Fin.succAbove_right_injective oldpart
            have aligned := indexed.indices_perm hs.enumeration
            have restored := reconstruct_terminal (finRange_nodup (m+1)) (finRange_nodup (l+1))
              (mem_finRange i) (mem_finRange (roots i)) (by simp [hi]) aligned
            exact restored.to_prescribed (fun _ _ he => he)
        · have positive : ∀ i, 0 < capacity i := by
            intro i
            have ne : capacity i ≠ 0 := fun he => zero ⟨i, he⟩
            omega
          have hk : 0 < k := by have hj := j.isLt; omega
          obtain ⟨F, sub, newlabel, newfeasible, i, p, pnt, edge, sole⟩ :=
            exists_contractible_subgraph hk hinj positive ⟨label, feasible⟩
          obtain ⟨r, hr⟩ := exists_erase_reindex hm p (Contract F p (roots i)) (RootSet roots)
            (fun _ _ he => ⟨he.1, he.2.1⟩) pnt
          have newinj := reindex_roots_injective hr hinj
          have reduced := contraction_feasible_reindexed hinj newfeasible pnt edge sole hr
          have part := ih m (by omega) k
            (fun x y => Contract F p (roots i) (p.succAbove x) (p.succAbove y))
            (fun a => r (roots a)) (fun a => capacity a - if i = a then 1 else 0)
            (fun x => newlabel (p.succAbove x)) newinj reduced
          obtain ⟨oldlabel, oldpart⟩ := reindex_partition hr (fun a => hr.terminals _ ⟨a, rfl⟩) part
          have restored := reconstruct_contraction (finRange_nodup (m+1)) (mem_finRange p)
            (mem_finRange i) edge oldpart
          have sizes : (fun a => (capacity a - (if i = a then 1 else 0) + 1) +
              (if i = a then 1 else 0)) = (fun a => capacity a + 1) := by
            funext a
            have ha := positive a
            by_cases he : i = a
            · simp only [if_pos he]
              omega
            · simp only [if_neg he, Nat.sub_zero, Nat.add_zero]
          rw [sizes] at restored
          exact restored.to_prescribed sub

/-- The Győri–Lovász existence theorem for every finite `k`, with prescribed
distinct roots and positive part sizes. This theorem makes no running-time claim. -/
theorem gyori_lovasz : MainTheoremStatement := by
  intro n k E roots sizes hk _simple connected hinj positive total
  obtain ⟨label, feasible⟩ := initialize_prescribed_sizes roots sizes hk connected hinj positive total
  have partition := feasible_partition n k E roots (fun i => sizes i - 1) label
    (fun _ _ he => hinj _ _ he) feasible
  have he : (fun i => sizes i - 1 + 1) = sizes := by
    funext i
    have hi := positive i
    omega
  rw [he] at partition
  exact partition

end GyoriLovasz
