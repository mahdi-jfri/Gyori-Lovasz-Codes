import GyoriLovasz.WeightedMain
import GyoriLovasz.BoundedRun

namespace GyoriLovasz

theorem edgeCount_le_square (E : Fin n → Fin n → Prop) : edgeCount E ≤ n * n := by
  classical
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem edgeCount_mono {E F : Fin n → Fin n → Prop} (sub : ∀ x y, E x y → F x y) :
    edgeCount E ≤ edgeCount F := by
  classical
  apply Finset.card_le_card
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub _ _ (Finset.mem_filter.mp ha).2⟩

/-- Redirecting incoming edges during contraction cannot increase edge count:
each redirected edge is charged to its distinct original edge into `p`. -/
theorem edgeCount_contract_le (E : Fin n → Fin n → Prop) (p t : Fin n) :
    edgeCount (Contract E p t) ≤ edgeCount E := by
  classical
  let source := fun a : Fin n × Fin n => if E a.1 a.2 then a else (a.1, p)
  apply Finset.card_le_card_of_injOn source
  · intro a ha
    have he := (Finset.mem_filter.mp ha).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases old : E a.1 a.2
    · simp [source, old]
    · have redirected := he.2.2.resolve_left old
      simpa [source, old] using redirected.1
  · intro a ha b hb eq
    have ea := (Finset.mem_filter.mp ha).2
    have eb := (Finset.mem_filter.mp hb).2
    by_cases oa : E a.1 a.2 <;> by_cases ob : E b.1 b.2
    · simpa [source, oa, ob] using eq
    · have snd := congrArg Prod.snd eq
      have ap : a.2 = p := by simpa [source, oa, ob] using snd
      exact False.elim (ea.2.1 ap)
    · have snd := congrArg Prod.snd eq
      have bp : b.2 = p := by simpa [source, oa, ob] using snd.symm
      exact False.elim (eb.2.1 bp)
    · have fst := congrArg Prod.fst eq
      apply Prod.ext
      · simpa [source, oa, ob] using fst
      · exact (ea.2.2.resolve_left oa).2.trans (eb.2.2.resolve_left ob).2.symm

theorem GraphReindex.edgeCount {vertices : List (Fin n)}
    {E : Fin n → Fin n → Prop} {T : Fin n → Prop} {e : Fin m → Fin n} {r : Fin n → Fin m}
    (h : GraphReindex vertices (List.finRange m) E T e r) :
    edgeCount (fun x y => E (e x) (e y)) = edgeCount E := by
  classical
  apply Finset.card_bij (fun a _ => (e a.1, e a.2))
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ he
    apply Prod.ext
    · exact (h.inverse a.1).symm.trans ((congrArg r (congrArg Prod.fst he)).trans (h.inverse b.1))
    · exact (h.inverse a.2).symm.trans ((congrArg r (congrArg Prod.snd he)).trans (h.inverse b.2))
  · intro a ha
    have edge := (Finset.mem_filter.mp ha).2
    have mem := h.edges _ _ edge
    refine ⟨(r a.1, r a.2), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp only
      rw [h.retract _ mem.1, h.retract _ mem.2]
      exact edge
    · exact Prod.ext (h.retract _ mem.1) (h.retract _ mem.2)

/-- Concrete outer-reduction configurations. This relation records graph
changes, not the time taken to select them or compute their witnesses. -/
structure ReductionGraph where
  vertices : Nat
  edges : Fin vertices → Fin vertices → Prop

noncomputable def ReductionGraph.measure (G : ReductionGraph) : Nat :=
  G.vertices + edgeCount G.edges

inductive OuterReduction : ReductionGraph → ReductionGraph → Prop where
  | delete {n : Nat} {E : Fin n → Fin n → Prop} {p q : Fin n} (edge : E p q) :
      OuterReduction ⟨n, E⟩ ⟨n, DeleteEdge E p q⟩
  | shrink {n m : Nat} {E F : Fin n → Fin n → Prop}
      {vertices : List (Fin n)} {T : Fin n → Prop} {e : Fin m → Fin n} {r : Fin n → Fin m}
      (smaller : m < n) (count : edgeCount F ≤ edgeCount E)
      (h : GraphReindex vertices (List.finRange m) F T e r) :
      OuterReduction ⟨n, E⟩ ⟨m, fun x y => F (e x) (e y)⟩

theorem OuterReduction.decreases {G H : ReductionGraph} (step : OuterReduction G H) :
    H.measure < G.measure := by
  cases step with
  | delete edge =>
    have strict := edgeCount_delete_lt edge
    simp only [ReductionGraph.measure]
    omega
  | shrink smaller count h =>
    simp only [ReductionGraph.measure]
    rw [h.edgeCount]
    omega

theorem outer_reductions_bounded {G H : ReductionGraph} {steps : Nat} {done : ReductionGraph → Prop}
    (run : RunUntil OuterReduction done G steps H) : steps ≤ G.measure := by
  induction run with
  | stop _ => exact Nat.zero_le _
  | next step _ ih =>
    have strict := step.decreases
    omega

theorem outer_reductions_quadratic {n : Nat} {E : Fin n → Fin n → Prop}
    {H : ReductionGraph} {steps : Nat} {done : ReductionGraph → Prop}
    (run : RunUntil OuterReduction done ⟨n, E⟩ steps H) : steps ≤ n + n * n :=
  (outer_reductions_bounded run).trans (Nat.add_le_add_left (edgeCount_le_square E) n)

end GyoriLovasz
