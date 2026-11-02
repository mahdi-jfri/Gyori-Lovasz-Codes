import GyoriLovasz.Weighted
import Mathlib.Data.List.MinMax
import Init.Data.Vector.OfFn

namespace GyoriLovasz.ShortestPaths

structure State (n : Nat) where
  settled : Finset (Fin n)
  distance : Vector Nat n

def get (s : State n) (v : Fin n) : Nat := s.distance[v.val]

def initialState (source : Fin n) (bound : Nat) : State n :=
  ⟨∅, Vector.ofFn (fun v => if v = source then 0 else bound)⟩

def relax (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat)
    (s : State n) (u : Fin n) : State n :=
  ⟨insert u s.settled, Vector.ofFn (fun v =>
    if v ∈ s.settled then get s v else
      if E u v then min (get s v) (get s u + cost u v) else get s v)⟩

def choose (s : State n) : Option (Fin n) :=
  ((List.finRange n).filter (fun v => decide (v ∉ s.settled))).argmin (get s)

def step (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat) (s : State n) : State n :=
  match choose s with
  | none => s
  | some u => relax E cost s u

def run (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat) : Nat → State n → State n
  | 0, s => s
  | fuel + 1, s => run E cost fuel (step E cost s)

def Admissible (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat)
    (source : Fin n) (bound : Nat) (d : Fin n → Nat) : Prop :=
  d source = 0 ∧ (∀ v, d v ≤ bound) ∧ ∀ u v, E u v = true → d v ≤ d u + cost u v

def Invariant (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat)
    (source : Fin n) (bound : Nat) (s : State n) : Prop :=
  get s source = 0 ∧ (∀ v, get s v ≤ bound) ∧
  (∀ d, Admissible E cost source bound d → ∀ v, d v ≤ get s v) ∧
  (∀ u ∈ s.settled, ∀ v, v ∉ s.settled → get s u ≤ get s v) ∧
  (∀ u ∈ s.settled, ∀ v, E u v = true → get s v ≤ get s u + cost u v)

theorem initialState_invariant (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat)
    (source : Fin n) (bound : Nat) : Invariant E cost source bound (initialState source bound) := by
  refine ⟨by simp [get, initialState], ?_, ?_, ?_, ?_⟩
  · intro v
    by_cases h : v = source <;> simp [get, initialState, h]
  · intro d hd v
    by_cases h : v = source
    · subst v; simp [get, initialState, hd.1]
    · simpa [get, initialState, h] using hd.2.1 v
  · intro u hu
    exact False.elim (Finset.not_mem_empty u hu)
  · intro u hu
    exact False.elim (Finset.not_mem_empty u hu)

theorem relax_get (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat)
    (s : State n) (u v : Fin n) : get (relax E cost s u) v =
      if v ∈ s.settled then get s v else
        if E u v then min (get s v) (get s u + cost u v) else get s v := by
  simp [get, relax]

theorem relax_le (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat)
    (s : State n) (u v : Fin n) : get (relax E cost s u) v ≤ get s v := by
  rw [relax_get]
  split
  · exact Nat.le_refl _
  · split
    · exact min_le_left _ _
    · exact Nat.le_refl _

theorem relax_self (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat)
    (s : State n) (u : Fin n) : get (relax E cost s u) u = get s u := by
  rw [relax_get]
  split
  · rfl
  · split
    · exact min_eq_left (Nat.le_add_right _ _)
    · rfl

theorem relax_invariant {E : Fin n → Fin n → Bool} {cost : Fin n → Fin n → Nat}
    {source : Fin n} {bound : Nat} {s : State n} {u : Fin n}
    (inv : Invariant E cost source bound s) (unused : u ∉ s.settled)
    (least : ∀ v, v ∉ s.settled → get s u ≤ get s v) :
    Invariant E cost source bound (relax E cost s u) := by
  have old (v : Fin n) (hv : v ∈ s.settled) : get (relax E cost s u) v = get s v := by
    rw [relax_get, if_pos hv]
  have lower (v : Fin n) (hv : v ∉ s.settled) : get s u ≤ get (relax E cost s u) v := by
    rw [relax_get, if_neg hv]
    split
    · exact le_min (least v hv) (Nat.le_add_right _ _)
    · exact least v hv
  refine ⟨?_, (fun v => (relax_le E cost s u v).trans (inv.2.1 v)), ?_, ?_, ?_⟩
  · have le := relax_le E cost s u source
    have zero := inv.1
    omega
  · intro d hd v
    rw [relax_get]
    split
    · exact inv.2.2.1 d hd v
    · rename_i hv
      split
      · rename_i edge
        exact le_min (inv.2.2.1 d hd v)
          ((hd.2.2 u v edge).trans (Nat.add_le_add_right (inv.2.2.1 d hd u) _))
      · exact inv.2.2.1 d hd v
  · intro a ha v hv
    have vout : v ∉ s.settled := fun h => hv (Finset.mem_insert_of_mem h)
    rcases Finset.mem_insert.mp ha with he | ha
    · subst a
      rw [relax_self]
      exact lower v vout
    · rw [old a ha]
      exact (inv.2.2.2.1 a ha u unused).trans (lower v vout)
  · intro a ha v edge
    rcases Finset.mem_insert.mp ha with he | ha
    · subst a
      rw [relax_self]
      by_cases hv : v ∈ s.settled
      · rw [old v hv]
        exact (inv.2.2.2.1 v hv u unused).trans (Nat.le_add_right _ _)
      · rw [relax_get, if_neg hv, if_pos edge]
        exact min_le_right _ _
    · rw [old a ha]
      exact (relax_le E cost s u v).trans (inv.2.2.2.2 a ha v edge)

theorem choose_spec {s : State n} {u : Fin n} (chosen : choose s = some u) :
    u ∉ s.settled ∧ ∀ v, v ∉ s.settled → get s u ≤ get s v := by
  have mem : u ∈ ((List.finRange n).filter (fun v => decide (v ∉ s.settled))).argmin (get s) := chosen
  refine ⟨of_decide_eq_true (List.mem_filter.mp (List.argmin_mem mem)).2, ?_⟩
  intro v hv
  exact List.le_of_mem_argmin (by simp [mem_finRange, hv]) mem

theorem step_invariant {E : Fin n → Fin n → Bool} {cost : Fin n → Fin n → Nat}
    {source : Fin n} {bound : Nat} {s : State n} (inv : Invariant E cost source bound s) :
    Invariant E cost source bound (step E cost s) := by
  unfold step
  split
  · exact inv
  · rename_i u chosen
    exact relax_invariant inv (choose_spec chosen).1 (choose_spec chosen).2

theorem run_invariant {E : Fin n → Fin n → Bool} {cost : Fin n → Fin n → Nat}
    {source : Fin n} {bound : Nat} (fuel : Nat) {s : State n}
    (inv : Invariant E cost source bound s) : Invariant E cost source bound (run E cost fuel s) := by
  induction fuel generalizing s with
  | zero => exact inv
  | succ fuel ih => exact ih (step_invariant inv)

theorem run_settles (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat)
    (fuel : Nat) (s : State n) (enough : n ≤ s.settled.card + fuel) :
    (run E cost fuel s).settled = Finset.univ := by
  classical
  induction fuel generalizing s with
  | zero =>
    apply Finset.eq_univ_of_card
    have upper : s.settled.card ≤ n := (Finset.card_le_univ s.settled).trans (by simp)
    dsimp only [run]
    simp only [Fintype.card_fin]
    omega
  | succ fuel ih =>
    apply ih
    unfold step
    split
    · rename_i chosen
      have empty := List.argmin_eq_none.mp chosen
      have all : s.settled = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro v
        by_contra hv
        have mem : v ∈ (List.finRange n).filter (fun v => decide (v ∉ s.settled)) := by simp [mem_finRange, hv]
        rw [empty] at mem
        exact List.not_mem_nil mem
      simp [all]
    · rename_i u chosen
      have unused := (choose_spec chosen).1
      simp only [relax, Finset.card_insert_of_not_mem unused]
      omega

/-- The materialized distance table after n rounds is the greatest bounded
feasible distance potential. In particular it satisfies every edge inequality.
This theorem concerns shortest paths, not the completed partition runtime. -/
theorem dijkstra_correct (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat)
    (source : Fin n) (bound : Nat) :
    let result := run E cost n (initialState source bound)
    Admissible E cost source bound (get result) ∧
      ∀ d, Admissible E cost source bound d → ∀ v, d v ≤ get result v := by
  have inv := run_invariant n (initialState_invariant E cost source bound)
  have all := run_settles E cost n (initialState source bound) (by simp [initialState])
  refine ⟨⟨inv.1, inv.2.1, ?_⟩, inv.2.2.1⟩
  intro u v edge
  exact inv.2.2.2.2 u (by rw [all]; exact Finset.mem_univ _) v edge

end GyoriLovasz.ShortestPaths
