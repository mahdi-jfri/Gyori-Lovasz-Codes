import GyoriLovasz.Specification
import GyoriLovasz.Counting

namespace GyoriLovasz
open Side

theorem ReachWithin.start_allowed {E : α → α → Prop} {A : α → Prop} {x y : α}
    (h : ReachWithin E A x y) : A x := by
  cases h with
  | refl _ hx => exact hx
  | step hx _ _ => exact hx

theorem ReachWithin.end_allowed {E : α → α → Prop} {A : α → Prop} {x y : α}
    (h : ReachWithin E A x y) : A y := by
  induction h with
  | refl _ hx => exact hx
  | step _ _ _ ih => exact ih

/-- A path avoiding a separator cannot escape the cut's right side. -/
theorem reach_stays_right {E : α → α → Prop} {T : α → Prop}
    {v x y : α} {C : Cut α} (hc : Valid E T v C)
    (path : ReachWithin E (fun z => C z ≠ sep) x y) (hx : C x = right) :
    C y = right := by
  induction path with
  | refl _ _ => exact hx
  | @step a b z _ edge rest ih =>
    apply ih
    have nl := hc.no_cross a b edge hx
    have ns := rest.start_allowed
    cases h : C b with
    | left => exact False.elim (nl h)
    | sep => exact False.elim (ns h)
    | right => rfl

theorem ReachWithin.mono_allowed {E : α → α → Prop} {A B : α → Prop} {x y : α}
    (h : ReachWithin E A x y) (hab : ∀ z, A z → B z) : ReachWithin E B x y := by
  induction h with
  | refl z hz => exact .refl z (hab z hz)
  | step hx he _ ih => exact .step (hab _ hx) he ih

def RootSet (roots : Fin k → Fin n) (x : Fin n) : Prop := ∃ i, roots i = x

noncomputable def terminalCut (roots : Fin k → Fin n) : Cut (Fin n) := by
  classical
  exact fun x => if RootSet roots x then sep else right

theorem terminalCut_valid {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {v : Fin n} (hv : ¬RootSet roots v) : Valid E (RootSet roots) v (terminalCut roots) := by
  classical
  constructor
  · simp [terminalCut, hv]
  · intro t ht
    simp [terminalCut, ht]
  · intro x y _ _
    simp only [terminalCut]
    split <;> simp

theorem terminalCut_size (roots : Fin k → Fin n)
    (hinj : ∀ i j, roots i = roots j → i = j) :
    size (List.finRange n) (terminalCut roots) = k := by
  classical
  let rootsList := (List.finRange k).map roots
  let terminals := (List.finRange n).filter (fun x => decide (RootSet roots x))
  have hnRoots : rootsList.Nodup := nodup_map_of_injective (finRange_nodup k) roots hinj
  have hnTerm : terminals.Nodup := List.Pairwise.filter _ (finRange_nodup n)
  have root_mem (x : Fin n) : x ∈ rootsList ↔ RootSet roots x := by
    simp only [rootsList, List.mem_map, RootSet]
    constructor
    · rintro ⟨i, _, hi⟩; exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩; exact ⟨i, mem_finRange i, hi⟩
  have terminal_mem (x : Fin n) : x ∈ terminals ↔ RootSet roots x := by
    simp [terminals, mem_finRange x]
  have hle := nodup_length_le_of_subset hnRoots (fun x hx => (terminal_mem x).mpr ((root_mem x).mp hx))
  have hge := nodup_length_le_of_subset hnTerm (fun x hx => (root_mem x).mpr ((terminal_mem x).mp hx))
  have root_len : rootsList.length = k := by simp [rootsList]
  rw [size_eq_countTrue]
  have heq : countTrue (List.finRange n) (fun x => terminalCut roots x = sep) =
      countTrue (List.finRange n) (RootSet roots) := by
    apply countTrue_congr
    intro x _
    simp [terminalCut]
  rw [heq, countTrue_filter_length]
  change terminals.length = k
  omega

/-- Ordinary vertex connectivity gives the required minimum-cut lower bound.
This bridge uses separator-avoiding reachability directly; it assumes no
version of Menger's theorem and no partition theorem. -/
theorem kconnected_cut_lower {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {v : Fin n} (connected : KConnected E k)
    (hinj : ∀ i j, roots i = roots j → i = j)
    {C : Cut (Fin n)} (hc : Valid E (RootSet roots) v C) :
    k ≤ size (List.finRange n) C := by
  classical
  by_cases hle : k ≤ size (List.finRange n) C
  · exact hle
  · have hlt : size (List.finRange n) C < k := by omega
    let deleted := (List.finRange n).filter (fun x => decide (C x = sep))
    have hmem (x : Fin n) : x ∈ deleted ↔ C x = sep := by
      simp [deleted, mem_finRange x]
    have hd : deleted.Nodup := List.Pairwise.filter _ (finRange_nodup n)
    have hlen : deleted.length = size (List.finRange n) C := by
      rw [size_eq_countTrue, countTrue_filter_length]
    have root_outside : ∃ i, C (roots i) ≠ sep := by
      by_cases h : ∃ i, C (roots i) ≠ sep
      · exact h
      · have all_in : ∀ i, C (roots i) = sep := by
          intro i
          by_cases hi : C (roots i) = sep
          · exact hi
          · exact False.elim (h ⟨i, hi⟩)
        have hn := nodup_map_of_injective (finRange_nodup k) roots hinj
        have hsub : ∀ x, x ∈ (List.finRange k).map roots → x ∈ deleted := by
          intro x hx
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
          exact (hmem _).mpr (all_in i)
        have hb := nodup_length_le_of_subset hn hsub
        have root_len : ((List.finRange k).map roots).length = k := by simp
        omega
    obtain ⟨i, hi⟩ := root_outside
    have hv_out : v ∉ deleted := by
      intro h
      have he := (hmem v).mp h
      rw [hc.source] at he
      cases he
    have hi_out : roots i ∉ deleted := fun h => hi ((hmem _).mp h)
    have path := connected.2 deleted hd (by omega) v (roots i) hv_out hi_out
    have path' : ReachWithin E (fun z => C z ≠ sep) v (roots i) :=
      path.mono_allowed (fun z hz hsep => hz ((hmem z).mpr hsep))
    have hr := reach_stays_right hc path' hc.source
    exact False.elim (hc.terminals (roots i) ⟨i, rfl⟩ hr)

theorem kconnected_hasRank {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {v : Fin n} (hv : ¬RootSet roots v) (connected : KConnected E k)
    (hinj : ∀ i j, roots i = roots j → i = j) :
    HasRank (List.finRange n) E (RootSet roots) v k :=
  ⟨⟨terminalCut roots, terminalCut_valid hv, terminalCut_size roots hinj⟩,
    fun _ hc => kconnected_cut_lower connected hinj hc⟩

theorem initial_all_essential {E : Fin n → Fin n → Prop} {roots : Fin k → Fin n}
    {v : Fin n} (hv : ¬RootSet roots v) (connected : KConnected E k)
    (hinj : ∀ i j, roots i = roots j → i = j) (i : Fin k) :
    Essential E (RootSet roots) v hv (roots i) := by
  classical
  have hr := kconnected_hasRank hv connected hinj
  have chosen := cutRank_spec E (RootSet roots) v hv
  obtain ⟨C, hc⟩ := chosen.witness
  have h1 := hr.lower C hc.1
  have h2 := chosen.lower (terminalCut roots) (terminalCut_valid hv)
  have hsz := terminalCut_size roots hinj
  have heq := hc.2
  have rank_eq : cutRank E (RootSet roots) v hv = k := by omega
  unfold Essential CutEssential
  refine ⟨terminalCut roots, ⟨terminalCut_valid hv, hsz.trans rank_eq.symm⟩, ?_⟩
  simp [terminalCut, RootSet]

end GyoriLovasz
