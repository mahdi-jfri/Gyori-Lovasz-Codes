import GyoriLovasz.RankBridge

namespace GyoriLovasz
open Side

theorem hasRank_of_valid {vertices : List α} {E : α → α → Prop}
    {T : α → Prop} {v : α} (existsCut : ∃ C, Valid E T v C) :
    ∃ r, HasRank vertices E T v r := by
  classical
  have least : ∀ m, ∀ C, Valid E T v C → size vertices C = m →
      ∃ r, HasRank vertices E T v r := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro C hc hm
      by_cases hmin : ∀ D, Valid E T v D → size vertices C ≤ size vertices D
      · exact ⟨m, ⟨⟨C, hc, hm⟩, fun D hd => hm ▸ hmin D hd⟩⟩
      · obtain ⟨D, hd⟩ := Classical.not_forall.mp hmin
        have hv : Valid E T v D := by
          by_cases hv : Valid E T v D
          · exact hv
          · exact False.elim (hd (fun h => False.elim (hv h)))
        have hlt : size vertices D < m := by
          have hn : ¬size vertices C ≤ size vertices D := fun h => hd (fun _ => h)
          omega
        exact ih (size vertices D) hlt D hv rfl
  obtain ⟨C, hc⟩ := existsCut
  exact least (size vertices C) C hc rfl

theorem exists_rank (vertices : List α) (E : α → α → Prop) (T : α → Prop)
    (v : α) (hv : ¬T v) : ∃ r, HasRank vertices E T v r := by
  classical
  apply hasRank_of_valid
  let C : Cut α := fun x => if T x then sep else right
  refine ⟨C, ⟨?_, ?_, ?_⟩⟩
  · simp [C, hv]
  · intro t ht
    simp [C, ht]
  · intro x y _ _
    simp only [C]
    split <;> simp

theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.nodup_cons]
    constructor
    · simp [Fin.succ_ne_zero]
    · apply List.pairwise_map.mpr
      exact List.Pairwise.imp (fun hne he => hne (Fin.succ_inj.mp he)) ih

theorem mem_finRange (x : Fin n) : x ∈ List.finRange n := by
  apply List.mem_ofFn.mpr
  exact ⟨x, rfl⟩

noncomputable def cutRank (E : Fin n → Fin n → Prop) (T : Fin n → Prop)
    (v : Fin n) (hv : ¬T v) : Nat :=
  Classical.choose (exists_rank (List.finRange n) E T v hv)

theorem cutRank_spec (E : Fin n → Fin n → Prop) (T : Fin n → Prop)
    (v : Fin n) (hv : ¬T v) :
    HasRank (List.finRange n) E T v (cutRank E T v hv) :=
  Classical.choose_spec (exists_rank (List.finRange n) E T v hv)

def Essential (E : Fin n → Fin n → Prop) (T : Fin n → Prop)
    (v : Fin n) (hv : ¬T v) (t : Fin n) : Prop :=
  CutEssential (List.finRange n) E T v (cutRank E T v hv) t

def Critical (E : Fin n → Fin n → Prop) (T : Fin n → Prop)
    (v : Fin n) (hv : ¬T v) (p q t : Fin n) : Prop :=
  Essential E T v hv t ∧ ¬Essential (DeleteEdge E p q) T v hv t

/-- Concrete finite-graph, cut-based version of the criticality-transfer lemma.
All minimum-rank existence hypotheses from the intermediate development
are discharged by `cutRank_spec` here. No graph-theoretic axiom is assumed. -/
theorem finite_transfer_criticality {E : Fin n → Fin n → Prop} {T : Fin n → Prop}
    {v p q p' q' t u : Fin n} (hv : ¬T v)
    (ht : T t) (hu : T u) (hp : E p u) (hqu : q ≠ u) (hpp' : p ≠ p')
    (critical_i : Critical E T v hv p q t)
    (critical_j : Critical E T v hv p' q' u) : Critical E T v hv p' q' t := by
  refine ⟨critical_i.1, ?_⟩
  exact transfer_criticality (finRange_nodup n) (mem_finRange q) (mem_finRange q')
    (cutRank_spec E T v hv)
    (cutRank_spec (DeleteEdge E p q) T v hv)
    (cutRank_spec (DeleteEdge E p' q') T v hv)
    (cutRank_spec (DeleteEdge (DeleteEdge E p' q') p q) T v hv)
    ht hu hp hqu hpp' critical_i.1 critical_i.2 critical_j.2

theorem finite_secondary_not_critical {E : Fin n → Fin n → Prop} {T : Fin n → Prop}
    {v p q t : Fin n} (hv : ¬T v) (ht : T t) (hp : E p t) (hqt : q ≠ t) :
    ¬Critical E T v hv p q t := by
  intro h
  exact h.2 (secondary_not_critical (cutRank_spec E T v hv)
    (cutRank_spec (DeleteEdge E p q) T v hv) ht hp hqt h.1)

theorem finite_criticality_assignable {E : Fin n → Fin n → Prop} {T : Fin n → Prop}
    {v p q t u : Fin n} (hv : ¬T v) (hu : T u) (hp : E p u) (hqu : q ≠ u)
    (h : Critical E T v hv p q t) : Essential E T v hv u :=
  criticality_assignable (finRange_nodup n) (mem_finRange q)
    (cutRank_spec E T v hv) (cutRank_spec (DeleteEdge E p q) T v hv)
    hu hp hqu h.1 h.2

end GyoriLovasz
