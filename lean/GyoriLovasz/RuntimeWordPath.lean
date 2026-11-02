import GyoriLovasz.RuntimeWordShortest

namespace GyoriLovasz.WordPath
open WordShortest

/-- Reference-RAM path search, with Boolean adjacency already materialized.
The constant charges cover table reads, option tests, and Boolean operations. -/
def choose (G : Graph n) (s : PathSearch.Table n) :
    Costed.Computation (Option (Fin n × Fin n)) :=
  let candidates := Costed.enumeratePairs n
  let found := Costed.find (fun uv => (PathSearch.eligible (edge G) s uv, 16)) candidates.1
  (found.1, candidates.2 + found.2 + 1)

theorem choose_value (G : Graph n) (s : PathSearch.Table n) :
    (choose G s).1 = PathSearch.choose (edge G) s := by
  simp [choose, Costed.find_value, Costed.enumeratePairs_value, PathSearch.choose,
    PathSearch.candidates]

theorem choose_cost (G : Graph n) (s : PathSearch.Table n) :
    (choose G s).2 ≤ 27 * n * n + 5 * n + 5 := by
  have h := Costed.find_cost (fun uv => (PathSearch.eligible (edge G) s uv, 16))
    (Costed.enumeratePairs n).1 16 (by intros; exact Nat.le_refl _)
  have len : (Costed.enumeratePairs n).1.length = n * n := by
    simp [Costed.enumeratePairs_value]
  rw [len] at h
  dsimp only [choose]
  rw [Costed.enumeratePairs_cost]
  ring_nf at h ⊢
  omega

def put (codes : Vector (List Bool) n) (s : PathSearch.Table n)
    (v : Fin n) (p : List (Fin n)) : Costed.Computation (PathSearch.Table n) :=
  Costed.tabulate n (fun x =>
    let eq := equalVertex codes x v
    (if eq.1 then some p else PathSearch.lookup s x, eq.2 + 2))

theorem put_value (codes : Vector (List Bool) n) (correct : CodebookCorrect codes)
    (s : PathSearch.Table n) (v : Fin n) (p : List (Fin n)) :
    (put codes s v p).1 = PathSearch.put s v p := by
  apply Vector.ext
  intro i hi
  change (Costed.tabulate n _).1[(⟨i, hi⟩ : Fin n).val] = _
  rw [Costed.tabulate_value]
  simp [equalVertex_value codes correct, PathSearch.put]

theorem put_cost (codes : Vector (List Bool) n) (B : Nat)
    (bound : ∀ v : Fin n, codes[v.val].length ≤ B)
    (s : PathSearch.Table n) (v : Fin n) (p : List (Fin n)) :
    (put codes s v p).2 ≤ 2 * n * n + n * (9 * B + 12) + 3 := by
  have h := Costed.tabulate_cost n (fun x =>
    let eq := equalVertex codes x v
    (if eq.1 then some p else PathSearch.lookup s x, eq.2 + 2)) (9 * B + 6)
    (by intro x; have h := equalVertex_cost codes B bound x v; dsimp only; omega)
  exact h

def step (G : Graph n) (codes : Vector (List Bool) n) (s : PathSearch.Table n) :
    Costed.Computation (PathSearch.Table n) :=
  let chosen := choose G s
  match chosen.1 with
  | none => (s, chosen.2 + 1)
  | some (u, v) => match PathSearch.lookup s u with
    | none => (s, chosen.2 + 3)
    | some p =>
      let updated := put codes s v (u :: p)
      (updated.1, chosen.2 + updated.2 + 4)

theorem step_value (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (s : PathSearch.Table n) :
    (step G codes s).1 = PathSearch.step (edge G) s := by
  dsimp only [step]
  rw [choose_value]
  unfold PathSearch.step
  cases h : PathSearch.choose (edge G) s with
  | none => rfl
  | some uv =>
    rcases uv with ⟨u, v⟩
    dsimp only
    cases h' : PathSearch.lookup s u with
    | none => rfl
    | some p => exact put_value codes correct s v (u :: p)

def budget (n B : Nat) := 29 * n * n + n * (9 * B + 17) + 12

theorem step_cost (G : Graph n) (codes : Vector (List Bool) n) (B : Nat)
    (bound : ∀ v : Fin n, codes[v.val].length ≤ B) (s : PathSearch.Table n) :
    (step G codes s).2 ≤ budget n B := by
  have hc := choose_cost G s
  have eq : budget n B = (27 * n * n + 5 * n + 5) +
      (2 * n * n + n * (9 * B + 12) + 3) + 4 := by unfold budget; ring
  rw [eq]
  dsimp only [step]
  split
  · omega
  · rename_i u v h
    split
    · omega
    · rename_i p hp
      have hu := put_cost codes B bound s v (u :: p)
      omega

def run (G : Graph n) (codes : Vector (List Bool) n) :
    Nat → PathSearch.Table n → Costed.Computation (PathSearch.Table n)
  | 0, s => (s, 1)
  | fuel + 1, s =>
    let next := step G codes s
    let rest := run G codes fuel next.1
    (rest.1, next.2 + rest.2 + 1)

theorem run_value (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (fuel : Nat) (s : PathSearch.Table n) :
    (run G codes fuel s).1 = PathSearch.run (edge G) fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih => simp [run, ih, step_value G codes correct, PathSearch.run]

theorem run_cost (G : Graph n) (codes : Vector (List Bool) n) (B : Nat)
    (bound : ∀ v : Fin n, codes[v.val].length ≤ B) (fuel : Nat) (s : PathSearch.Table n) :
    (run G codes fuel s).2 ≤ fuel * (budget n B + 1) + 1 := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    have hn := step_cost G codes B bound s
    have hr := ih (step G codes s).1
    simp only [run, Nat.succ_mul]
    omega

def initial (codes : Vector (List Bool) n) (source : Fin n) :
    Costed.Computation (PathSearch.Table n) :=
  Costed.tabulate n (fun v =>
    let eq := equalVertex codes v source
    (if eq.1 then some [] else none, eq.2 + 2))

theorem initial_value (codes : Vector (List Bool) n) (correct : CodebookCorrect codes)
    (source : Fin n) : (initial codes source).1 = PathSearch.initial source := by
  apply Vector.ext
  intro i hi
  change (Costed.tabulate n _).1[(⟨i, hi⟩ : Fin n).val] = _
  rw [Costed.tabulate_value]
  simp [equalVertex_value codes correct, PathSearch.initial]

theorem initial_cost (codes : Vector (List Bool) n) (B : Nat)
    (bound : ∀ v : Fin n, codes[v.val].length ≤ B) (source : Fin n) :
    (initial codes source).2 ≤ 2 * n * n + n * (9 * B + 12) + 3 := by
  exact Costed.tabulate_cost n _ (9 * B + 6)
    (by intro v; have h := equalVertex_cost codes B bound v source; dsimp only; omega)

def search (G : Graph n) (codes : Vector (List Bool) n) (source : Fin n) :
    Costed.Computation (PathSearch.Table n) :=
  let start := initial codes source
  let result := run G codes n start.1
  (result.1, start.2 + result.2 + 1)

theorem search_value (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (source : Fin n) :
    (search G codes source).1 = PathSearch.run (edge G) n (PathSearch.initial source) := by
  simp [search, run_value G codes correct, initial_value codes correct]

theorem search_cost (G : Graph n) (codes : Vector (List Bool) n) (B : Nat)
    (bound : ∀ v : Fin n, codes[v.val].length ≤ B) (source : Fin n) :
    (search G codes source).2 ≤
      2 * n * n + n * (9 * B + 12) + n * (budget n B + 1) + 5 := by
  have hi := initial_cost codes B bound source
  have hr := run_cost G codes B bound n (initial codes source).1
  dsimp only [search]
  omega

theorem search_correct (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (source target : Fin n)
    (reachable : Relation.ReflTransGen (fun u v => (edge G) u v = true) source target) :
    ∃ p, PathSearch.lookup (search G codes source).1 target = some p ∧
      PathSearch.Route (edge G) source target p ∧ (target :: p).Nodup ∧ p.length < n := by
  rw [search_value G codes correct]
  exact PathSearch.search_correct (edge G) source target reachable

theorem search_length (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (source target : Fin n) (p : List (Fin n))
    (found : PathSearch.lookup (search G codes source).1 target = some p) : p.length < n := by
  rw [search_value G codes correct] at found
  have inv := PathSearch.run_invariant n (PathSearch.initial_invariant (edge G) source)
  have h := (inv.2 target p found).2.1.length_le_card
  simp only [List.length_cons, Fintype.card_fin] at h
  omega

end GyoriLovasz.WordPath

