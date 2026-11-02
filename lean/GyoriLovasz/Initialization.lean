import GyoriLovasz.Shift

namespace GyoriLovasz

theorem exists_label_from_slots (vertices : List β) (slots : List α) (defaultLabel : α)
    (hn : vertices.Nodup) (hlen : vertices.length = slots.length) :
    ∃ label : β → α, ∀ t,
      countTrue vertices (fun v => label v = t) = countTrue slots (fun u => u = t) := by
  classical
  induction vertices generalizing slots with
  | nil =>
    have hs : slots = [] := List.length_eq_zero_iff.mp hlen.symm
    subst slots
    exact ⟨fun _ => defaultLabel, fun _ => rfl⟩
  | cons v rest ih =>
    cases slots with
    | nil => simp at hlen
    | cons t tail =>
      obtain ⟨notmem, nd⟩ := List.nodup_cons.mp hn
      have lengths : rest.length = tail.length := by simpa using hlen
      obtain ⟨label, hl⟩ := ih tail nd lengths
      let extended := fun x => if x = v then t else label x
      refine ⟨extended, ?_⟩
      intro target
      have same : countTrue rest (fun x => extended x = target) =
          countTrue rest (fun x => label x = target) := by
        apply countTrue_congr
        intro x hx
        have hne : x ≠ v := by intro h; subst x; exact notmem hx
        simp [extended, hne]
      simp only [countTrue]
      change (if extended v = target then 1 else 0) + countTrue rest (fun x => extended x = target) =
        (if t = target then 1 else 0) + countTrue tail (fun u => u = target)
      rw [same, hl target]
      simp [extended]

def capacitySlots (indices : List α) (capacity : α → Nat) : List α :=
  indices.flatMap (fun i => List.replicate (capacity i) i)

theorem capacitySlots_length (indices : List α) (capacity : α → Nat) :
    (capacitySlots indices capacity).length = sumValues indices capacity := by
  induction indices with
  | nil => simp [capacitySlots, sumValues]
  | cons i indices ih =>
    change (List.replicate (capacity i) i ++ capacitySlots indices capacity).length = _
    simp [sumValues, ih]

theorem countTrue_replicate (m : Nat) (x : α) (P : α → Prop) [DecidablePred P] :
    countTrue (List.replicate m x) P = if P x then m else 0 := by
  classical
  induction m with
  | zero => simp [countTrue]
  | succ m ih => by_cases h : P x <;> simp [List.replicate_succ, countTrue, h, ih, Nat.add_comm]

theorem capacitySlots_count (indices : List α) (capacity : α → Nat) (t : α)
    [DecidableEq α] (hn : indices.Nodup) :
    countTrue (capacitySlots indices capacity) (fun u => u = t) =
      if t ∈ indices then capacity t else 0 := by
  classical
  induction indices with
  | nil => simp [capacitySlots, countTrue]
  | cons i indices ih =>
    obtain ⟨notmem, nd⟩ := List.nodup_cons.mp hn
    change countTrue (List.replicate (capacity i) i ++ capacitySlots indices capacity) _ = _
    rw [countTrue_append, countTrue_replicate, ih nd]
    by_cases hit : i = t
    · subst i; simp [notmem]
    · simp [hit, Ne.symm hit]

/-- Initialize the invariant using the original connectivity assumption and
any nonnegative capacity vector with the required total. -/
theorem initialize_feasible_assignment {E : Fin n → Fin n → Prop}
    (roots : Fin k → Fin n) (capacity : Fin k → Nat)
    (hk : 0 < k) (connected : KConnected E k)
    (hinj : ∀ i j, roots i = roots j → i = j)
    (balance : sumValues (List.finRange k) capacity = (nonterminals roots).length) :
    ∃ label, FeasibleAssignment E roots capacity label := by
  classical
  let slots := capacitySlots (List.finRange k) capacity
  have hlen : (nonterminals roots).length = slots.length := by
    rw [capacitySlots_length]
    exact balance.symm
  obtain ⟨label, hlabel⟩ := exists_label_from_slots (nonterminals roots) slots
    ⟨0, hk⟩ (nonterminals_nodup roots) hlen
  refine ⟨label, ⟨?_, ?_⟩⟩
  · intro v hv
    exact initial_all_essential hv connected hinj (label v)
  · intro i
    have hc := capacitySlots_count (List.finRange k) capacity i (finRange_nodup k)
    have he : countTrue slots (fun u => u = i) = capacity i := by
      simpa [slots, mem_finRange i] using hc
    exact (hlabel i).trans he

theorem sumValues_eq_map_sum (xs : List α) (f : α → Nat) :
    sumValues xs f = (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumValues, ih]

theorem positive_capacity_sum (xs : List α) (sizes : α → Nat)
    (positive : ∀ i, i ∈ xs → 0 < sizes i) :
    sumValues xs (fun i => sizes i - 1) + xs.length = sumValues xs sizes := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := positive x (by simp)
    have ht := ih (fun y hy => positive y (by simp [hy]))
    simp only [sumValues, List.length_cons]
    omega

theorem nonterminals_length (roots : Fin k → Fin n)
    (hinj : ∀ i j, roots i = roots j → i = j) :
    (nonterminals roots).length + k = n := by
  classical
  let terminals := (List.finRange n).filter (fun x => decide (RootSet roots x))
  have tlength : terminals.length = k := by
    have hsz := terminalCut_size roots hinj
    rw [size_eq_countTrue] at hsz
    have he := countTrue_congr (List.finRange n)
      (P := fun x => terminalCut roots x = Side.sep) (Q := RootSet roots)
      (fun x _ => by simp [terminalCut])
    rw [he, countTrue_filter_length] at hsz
    exact hsz
  have hpart := List.filter_append_perm (fun x : Fin n => decide (RootSet roots x)) (List.finRange n)
  have hl := hpart.length_eq
  have hn : (List.finRange n).filter (fun x => !decide (RootSet roots x)) = nonterminals roots := by
    unfold nonterminals
    congr 1
    funext x
    simp
  rw [hn, List.length_append, List.length_finRange] at hl
  change terminals.length + (nonterminals roots).length = n at hl
  omega

theorem initialize_prescribed_sizes {E : Fin n → Fin n → Prop}
    (roots : Fin k → Fin n) (sizes : Fin k → Nat)
    (hk : 0 < k) (connected : KConnected E k)
    (hinj : ∀ i j, roots i = roots j → i = j)
    (positive : ∀ i, 0 < sizes i) (total : ((List.finRange k).map sizes).sum = n) :
    ∃ label, FeasibleAssignment E roots (fun i => sizes i - 1) label := by
  apply initialize_feasible_assignment roots _ hk connected hinj
  have hp := positive_capacity_sum (List.finRange k) sizes (fun i _ => positive i)
  have hl := nonterminals_length roots hinj
  rw [sumValues_eq_map_sum (List.finRange k) sizes, total, List.length_finRange] at hp
  omega

end GyoriLovasz
