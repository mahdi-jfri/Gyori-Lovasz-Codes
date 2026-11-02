import GyoriLovasz.RuntimeTightPaths

namespace GyoriLovasz.PathSearch

/-- A reverse path stores the predecessors of its current endpoint. -/
inductive Route (E : Fin n → Fin n → Bool) (source : Fin n) :
    Fin n → List (Fin n) → Prop where
  | start : Route E source source []
  | extend {u v p} : Route E source u p → E u v = true → Route E source v (u :: p)

abbrev Table (n : Nat) := Vector (Option (List (Fin n))) n

def lookup (s : Table n) (v : Fin n) := s[v.val]

def initial (source : Fin n) : Table n :=
  Vector.ofFn (fun v => if v = source then some [] else none)

def put (s : Table n) (v : Fin n) (p : List (Fin n)) : Table n :=
  Vector.ofFn (fun x => if x = v then some p else lookup s x)

def known (s : Table n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (lookup s v).isSome)

def candidates (n : Nat) := (List.finRange n).flatMap (fun u => (List.finRange n).map (u, ·))

def eligible (E : Fin n → Fin n → Bool) (s : Table n) (uv : Fin n × Fin n) : Bool :=
  (lookup s uv.1).isSome && (lookup s uv.2).isNone && E uv.1 uv.2

def choose (E : Fin n → Fin n → Bool) (s : Table n) :=
  (candidates n).find? (eligible E s)

def step (E : Fin n → Fin n → Bool) (s : Table n) : Table n :=
  match choose E s with
  | none => s
  | some (u, v) => match lookup s u with
    | none => s
    | some p => put s v (u :: p)

def run (E : Fin n → Fin n → Bool) : Nat → Table n → Table n
  | 0, s => s
  | fuel + 1, s => run E fuel (step E s)

def Invariant (E : Fin n → Fin n → Bool) (source : Fin n) (s : Table n) : Prop :=
  lookup s source = some [] ∧
  ∀ v p, lookup s v = some p →
    Route E source v p ∧ (v :: p).Nodup ∧ ∀ x ∈ p, x ∈ known s

@[simp] theorem mem_known (s : Table n) (v : Fin n) :
    v ∈ known s ↔ ∃ p, lookup s v = some p := by
  simp [known, Option.isSome_iff_exists]

@[simp] theorem lookup_put (s : Table n) (v x : Fin n) (p : List (Fin n)) :
    lookup (put s v p) x = if x = v then some p else lookup s x := by
  simp [lookup, put]

theorem known_put (s : Table n) (v : Fin n) (p : List (Fin n)) :
    known (put s v p) = insert v (known s) := by
  ext x
  by_cases h : x = v <;> simp [h]

theorem initial_invariant (E : Fin n → Fin n → Bool) (source : Fin n) :
    Invariant E source (initial source) := by
  refine ⟨by simp [lookup, initial], ?_⟩
  intro v p h
  by_cases eq : v = source
  · subst v
    have hp : p = [] := by simpa [lookup, initial] using h.symm
    subst p
    exact ⟨Route.start, by simp, by simp⟩
  · simp [lookup, initial, eq] at h

theorem put_invariant {E : Fin n → Fin n → Bool} {source : Fin n} {s : Table n}
    (inv : Invariant E source s) {u v : Fin n} {p : List (Fin n)}
    (hu : lookup s u = some p) (hv : lookup s v = none) (edge : E u v = true) :
    Invariant E source (put s v (u :: p)) := by
  have nv : v ∉ known s := by simp [hv]
  have us : u ∈ known s := (mem_known s u).mpr ⟨p, hu⟩
  have old := inv.2 u p hu
  have vs : source ≠ v := by intro eq; subst v; rw [inv.1] at hv; contradiction
  have vu : v ≠ u := by intro eq; subst v; exact nv us
  have vp : v ∉ p := fun h => nv (old.2.2 v h)
  refine ⟨by simp [vs, inv.1], ?_⟩
  intro x q hx
  by_cases xv : x = v
  · subst x
    have pq : q = u :: p := by simpa using hx.symm
    subst q
    refine ⟨Route.extend old.1 edge, ?_, ?_⟩
    · simp [vu, vp, old.2.1]
    · intro x hx
      rw [known_put]
      apply Finset.mem_insert_of_mem
      rcases List.mem_cons.mp hx with eq | hx
      · exact eq ▸ us
      · exact old.2.2 x hx
  · have hx' : lookup s x = some q := by simpa [xv] using hx
    have good := inv.2 x q hx'
    refine ⟨good.1, good.2.1, ?_⟩
    intro y hy
    rw [known_put]
    exact Finset.mem_insert_of_mem (good.2.2 y hy)

theorem choose_spec {E : Fin n → Fin n → Bool} {s : Table n} {u v : Fin n}
    (h : choose E s = some (u, v)) :
    (∃ p, lookup s u = some p) ∧ lookup s v = none ∧ E u v = true := by
  have yes := List.find?_some h
  simpa [eligible, Bool.and_eq_true, Option.isSome_iff_exists, and_assoc] using yes

theorem step_invariant {E : Fin n → Fin n → Bool} {source : Fin n} {s : Table n}
    (inv : Invariant E source s) : Invariant E source (step E s) := by
  unfold step
  split
  · exact inv
  · rename_i uv chosen
    obtain ⟨⟨p, hp⟩, hv, edge⟩ := choose_spec chosen
    rw [hp]
    exact put_invariant inv hp hv edge

theorem run_invariant {E : Fin n → Fin n → Bool} {source : Fin n}
    (fuel : Nat) {s : Table n} (inv : Invariant E source s) :
    Invariant E source (run E fuel s) := by
  induction fuel generalizing s with
  | zero => exact inv
  | succ fuel ih => exact ih (step_invariant inv)

def Closed (E : Fin n → Fin n → Bool) (s : Table n) : Prop :=
  ∀ u v, u ∈ known s → E u v = true → v ∈ known s

theorem choose_none_closed {E : Fin n → Fin n → Bool} {s : Table n}
    (h : choose E s = none) : Closed E s := by
  intro u v hu edge
  obtain ⟨p, hp⟩ := (mem_known s u).mp hu
  have all := List.find?_eq_none.mp h
  have mem : (u, v) ∈ candidates n := by simp [candidates, mem_finRange]
  have no := all (u, v) mem
  cases hv : lookup s v with
  | none => simp [eligible, hp, hv, edge] at no
  | some q => exact (mem_known s v).mpr ⟨q, hv⟩

theorem step_progress {E : Fin n → Fin n → Bool} {s : Table n} :
    step E s = s ∧ Closed E s ∨
      (known (step E s)).card = (known s).card + 1 := by
  unfold step
  split
  · rename_i h
    exact Or.inl ⟨rfl, choose_none_closed h⟩
  · rename_i uv chosen
    obtain ⟨⟨p, hp⟩, hv, _⟩ := choose_spec chosen
    rw [hp]
    right
    rw [known_put, Finset.card_insert_of_not_mem]
    simp [hv]

theorem run_of_fixed {E : Fin n → Fin n → Bool} {s : Table n}
    (h : step E s = s) (fuel : Nat) : run E fuel s = s := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [run, h] using ih

theorem run_closed (E : Fin n → Fin n → Bool) (fuel : Nat) (s : Table n)
    (enough : n ≤ (known s).card + fuel) : Closed E (run E fuel s) := by
  induction fuel generalizing s with
  | zero =>
    have all : known s = Finset.univ := by
      apply Finset.eq_univ_of_card
      have upper := Finset.card_le_univ (known s)
      simp only [Fintype.card_fin] at upper ⊢
      omega
    intro u v hu edge
    exact all ▸ Finset.mem_univ v
  | succ fuel ih =>
    rcases step_progress (E := E) (s := s) with ⟨fixed, closed⟩ | grows
    · rw [run_of_fixed fixed]
      exact closed
    · exact ih (step E s) (by omega)

/-- After at most n vertex insertions, every reachable vertex has a stored
simple path with fewer than n edges. No reachability oracle is used. -/
theorem search_correct (E : Fin n → Fin n → Bool) (source target : Fin n)
    (reachable : Relation.ReflTransGen (fun u v => E u v = true) source target) :
    ∃ p, lookup (run E n (initial source)) target = some p ∧
      Route E source target p ∧ (target :: p).Nodup ∧ p.length < n := by
  let s := run E n (initial source)
  have inv : Invariant E source s := run_invariant n (initial_invariant E source)
  have closed : Closed E s := run_closed E n (initial source) (by omega)
  have found : target ∈ known s := by
    induction reachable with
    | refl => exact (mem_known s source).mpr ⟨[], inv.1⟩
    | @tail u v _ edge ih => exact closed u v ih edge
  obtain ⟨p, hp⟩ := (mem_known s target).mp found
  have good := inv.2 target p hp
  have bound := good.2.1.length_le_card
  simp only [List.length_cons, Fintype.card_fin] at bound
  exact ⟨p, hp, good.1, good.2.1, by omega⟩

def tightEdges (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat)
    (d : Fin n → Nat) : Fin n → Fin n → Bool :=
  fun u v => E u v && decide (d v = d u + cost u v)

def shortestRoute (E : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat)
    (source target : Fin n) (bound : Nat) : Option (List (Fin n)) :=
  let d := ShortestPaths.get (ShortestPaths.run E cost n (ShortestPaths.initialState source bound))
  lookup (run (tightEdges E cost d) n (initial source)) target

theorem shortestRoute_correct (E : Fin n → Fin n → Bool)
    (cost : Fin n → Fin n → Nat) (source target : Fin n) (bound : Nat)
    (below : ShortestPaths.get
      (ShortestPaths.run E cost n (ShortestPaths.initialState source bound)) target < bound) :
    let d := ShortestPaths.get (ShortestPaths.run E cost n (ShortestPaths.initialState source bound))
    ∃ p, shortestRoute E cost source target bound = some p ∧
      Route (tightEdges E cost d) source target p ∧
      (target :: p).Nodup ∧ p.length < n := by
  have reaches := ShortestPaths.dijkstra_has_tight_path E cost source target bound below
  have reaches' : Relation.ReflTransGen
      (fun u v => tightEdges E cost (ShortestPaths.get
        (ShortestPaths.run E cost n (ShortestPaths.initialState source bound))) u v = true)
      source target := by
    clear below
    induction reaches with
    | refl => exact .refl
    | tail _ edge ih =>
      exact .tail ih (by simpa [tightEdges, ShortestPaths.Tight] using edge)
  exact search_correct _ source target reaches'

end GyoriLovasz.PathSearch
