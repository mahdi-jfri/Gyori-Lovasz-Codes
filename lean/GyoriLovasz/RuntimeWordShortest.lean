import GyoriLovasz.RuntimeCostedTable

namespace GyoriLovasz.WordShortest
open Binary

def CodebookCorrect (codes : Vector (List Bool) n) : Prop :=
  ∀ v : Fin n, value codes[v.val] = v.val

def equalVertex (codes : Vector (List Bool) n) (u v : Fin n) : Bool × Nat :=
  let cmp := compareWords codes[u.val] codes[v.val]
  (cmp.1.2, cmp.2 + 2)

theorem equalVertex_value (codes : Vector (List Bool) n) (correct : CodebookCorrect codes)
    (u v : Fin n) : (equalVertex codes u v).1 = decide (u = v) := by
  apply Bool.eq_iff_iff.mpr
  simp [equalVertex, (compareWords_correct _ _).2, correct u, correct v, Fin.val_inj]

theorem equalVertex_cost (codes : Vector (List Bool) n) (B : Nat)
    (bound : ∀ v : Fin n, codes[v.val].length ≤ B) (u v : Fin n) :
    (equalVertex codes u v).2 ≤ 9 * B + 4 := by
  have ub := bound u
  have vb := bound v
  simp only [equalVertex, compareWords_steps]
  omega

def memberVertex (codes : Vector (List Bool) n) (v : Fin n) (xs : List (Fin n)) : Bool × Nat :=
  let found := Costed.find (equalVertex codes v) xs
  (found.1.isSome, found.2 + 1)

theorem memberVertex_value (codes : Vector (List Bool) n) (correct : CodebookCorrect codes)
    (v : Fin n) (xs : List (Fin n)) : (memberVertex codes v xs).1 = decide (v ∈ xs) := by
  apply Bool.eq_iff_iff.mpr
  simp [memberVertex, Costed.find_value, List.find?_isSome, equalVertex_value codes correct]

theorem memberVertex_cost (codes : Vector (List Bool) n) (B : Nat)
    (bound : ∀ v : Fin n, codes[v.val].length ≤ B) (v : Fin n) (xs : List (Fin n)) :
    (memberVertex codes v xs).2 ≤ xs.length * (9 * B + 7) + 2 := by
  have scan := Costed.find_cost (equalVertex codes v) xs (9 * B + 4)
    (fun x _ => equalVertex_cost codes B bound v x)
  have sum : 9 * B + 4 + 3 = 9 * B + 7 := by omega
  rw [sum] at scan
  dsimp only [memberVertex]
  omega

structure State (n : Nat) where
  settled : List (Fin n)
  distance : Vector (List Bool) n

def decode (s : State n) : ShortestPaths.State n :=
  ⟨s.settled.toFinset, Vector.ofFn (fun v => value s.distance[v.val])⟩

@[simp] theorem decode_get (s : State n) (v : Fin n) :
    ShortestPaths.get (decode s) v = value s.distance[v.val] := by
  simp [ShortestPaths.get, decode]

def choose (codes : Vector (List Bool) n) (s : State n) : Costed.Computation (Option (Fin n)) :=
  let indices := Costed.enumerateIndices n
  let result := Costed.filterArgminWords
    (fun v => let seen := memberVertex codes v s.settled; (!seen.1, seen.2 + 1))
    (fun v => (⟨false, s.distance[v.val]⟩, 1)) indices.1
  (result.1, indices.2 + result.2 + 1)

theorem choose_value (codes : Vector (List Bool) n) (correct : CodebookCorrect codes) (s : State n) :
    (choose codes s).1 = ShortestPaths.choose (decode s) := by
  simp [choose, Costed.filterArgminWords_value, Costed.enumerateIndices_value,
    memberVertex_value codes correct, signedValue, ShortestPaths.choose,
    decode, ShortestPaths.get]
  simp [List.argmin, List.argAux, ShortestPaths.get]
  congr 2
  funext b c
  simp

theorem choose_cost (codes : Vector (List Bool) n) (s : State n) (B D : Nat)
    (codeBound : ∀ v : Fin n, codes[v.val].length ≤ B)
    (distanceBound : ∀ v : Fin n, s.distance[v.val].length ≤ D) :
    (choose codes s).2 ≤ 2 * n * n + 2 * n +
      n * (s.settled.length * (9 * B + 7) + 9 * D + 19) + 4 := by
  have cost := Costed.filterArgminWords_cost
    (fun v => let seen := memberVertex codes v s.settled; (!seen.1, seen.2 + 1))
    (fun v => (⟨false, s.distance[v.val]⟩, 1)) (List.finRange n)
    (s.settled.length * (9 * B + 7) + 3) 1 D
    (fun v => by have h := memberVertex_cost codes B codeBound v s.settled; dsimp only; omega)
    (fun _ => Nat.le_refl 1) distanceBound
  simp only [List.length_finRange] at cost
  simp only [choose, Costed.enumerateIndices_value, Costed.enumerateIndices_cost]
  have polynomial : s.settled.length * (9 * B + 7) + 3 + 2 * 1 + 9 * D + 14 =
      s.settled.length * (9 * B + 7) + 9 * D + 19 := by omega
  rw [polynomial] at cost
  omega

structure Graph (n : Nat) where
  edges : Vector (Vector Bool n) n
  cost : Vector (Vector (List Bool) n) n

def edge (G : Graph n) (u v : Fin n) : Bool := G.edges[u.val][v.val]
def weight (G : Graph n) (u v : Fin n) : Nat := value G.cost[u.val][v.val]

def relaxCell (G : Graph n) (codes : Vector (List Bool) n) (s : State n) (u v : Fin n) :
    Costed.Computation (List Bool) :=
  let seen := memberVertex codes v s.settled
  if seen.1 then (s.distance[v.val], seen.2 + 2) else
    if edge G u v then
      let candidate := addCarry s.distance[u.val] G.cost[u.val][v.val] false
      let cmp := compareWords candidate.1 s.distance[v.val]
      (if cmp.1.1 then candidate.1 else s.distance[v.val], seen.2 + candidate.2 + cmp.2 + 8)
    else (s.distance[v.val], seen.2 + 3)

theorem relaxCell_value (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (s : State n) (u v : Fin n) :
    value (relaxCell G codes s u v).1 =
      ShortestPaths.get (ShortestPaths.relax (edge G) (weight G) (decode s) u) v := by
  rw [ShortestPaths.relax_get]
  simp only [decode_get]
  have seen := memberVertex_value codes correct v s.settled
  have sum := addCarry_correct s.distance[u.val] G.cost[u.val][v.val] false
  simp only [Bool.false_eq_true, if_false, Nat.add_zero] at sum
  have cmp := (compareWords_correct (addCarry s.distance[u.val] G.cost[u.val][v.val] false).1 s.distance[v.val]).1
  dsimp only [relaxCell]
  rw [seen]
  simp only [decide_eq_true_eq, decode, List.mem_toFinset, weight]
  split
  · rfl
  · split
    · split
      · rename_i less
        have lt := cmp.mp less
        rw [sum] at lt ⊢
        exact (Nat.min_eq_right (by omega)).symm
      · rename_i notLess
        have le : value s.distance[v.val] ≤ value (addCarry s.distance[u.val] G.cost[u.val][v.val] false).1 := by
          have h := mt cmp.mpr notLess
          omega
        rw [sum] at le
        exact (Nat.min_eq_left le).symm
    · rfl

def Bounds (G : Graph n) (codes : Vector (List Bool) n) (s : State n) (B : Nat) : Prop :=
  (∀ v : Fin n, codes[v.val].length ≤ B) ∧
  (∀ v : Fin n, s.distance[v.val].length ≤ B) ∧
  ∀ u v : Fin n, G.cost[u.val][v.val].length ≤ B

theorem relaxCell_bounds (G : Graph n) (codes : Vector (List Bool) n) (s : State n)
    (B : Nat) (bound : Bounds G codes s B) (u v : Fin n) :
    (relaxCell G codes s u v).2 ≤ s.settled.length * (9 * B + 7) + 16 * B + 23 ∧
      (relaxCell G codes s u v).1.length ≤ B + 1 := by
  have member := memberVertex_cost codes B bound.1 v s.settled
  have du := bound.2.1 u
  have dv := bound.2.1 v
  have weight := bound.2.2 u v
  have sumCost := addCarry_steps s.distance[u.val] G.cost[u.val][v.val] false
  have sumLength := addCarry_length s.distance[u.val] G.cost[u.val][v.val] false
  have cmpCost := compareWords_steps (addCarry s.distance[u.val] G.cost[u.val][v.val] false).1 s.distance[v.val]
  dsimp only [relaxCell]
  split
  · constructor <;> dsimp only <;> omega
  · split
    · constructor
      · dsimp only
        omega
      · dsimp only
        split <;> omega
    · constructor <;> dsimp only <;> omega

def relax (G : Graph n) (codes : Vector (List Bool) n) (s : State n) (u : Fin n) :
    Costed.Computation (State n) :=
  let table := Costed.tabulate n (relaxCell G codes s u)
  (⟨u :: s.settled, table.1⟩, table.2 + 2)

theorem decoded_ext (x y : ShortestPaths.State n) (hs : x.settled = y.settled)
    (hd : ∀ v, ShortestPaths.get x v = ShortestPaths.get y v) : x = y := by
  cases x with
  | mk xs xd =>
    cases y with
    | mk ys yd =>
      simp only at hs
      subst ys
      congr 1
      apply Vector.ext
      intro i hi
      exact hd ⟨i, hi⟩

theorem relax_value (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (s : State n) (u : Fin n) :
    decode (relax G codes s u).1 = ShortestPaths.relax (edge G) (weight G) (decode s) u := by
  apply decoded_ext
  · simp [decode, relax, ShortestPaths.relax]
  · intro v
    rw [decode_get]
    simp only [relax, Costed.tabulate_value]
    exact relaxCell_value G codes correct s u v

theorem relax_cost (G : Graph n) (codes : Vector (List Bool) n) (s : State n)
    (B : Nat) (bound : Bounds G codes s B) (u : Fin n) :
    (relax G codes s u).2 ≤
      2 * n * n + n * (s.settled.length * (9 * B + 7) + 16 * B + 29) + 5 := by
  have table := Costed.tabulate_cost n (relaxCell G codes s u)
    (s.settled.length * (9 * B + 7) + 16 * B + 23)
    (fun v => (relaxCell_bounds G codes s B bound u v).1)
  have constants : s.settled.length * (9 * B + 7) + 16 * B + 23 + 6 =
      s.settled.length * (9 * B + 7) + 16 * B + 29 := by omega
  rw [constants] at table
  dsimp only [relax]
  omega

def step (G : Graph n) (codes : Vector (List Bool) n) (s : State n) : Costed.Computation (State n) :=
  let chosen := choose codes s
  match chosen.1 with
  | none => (s, chosen.2 + 1)
  | some u =>
    let next := relax G codes s u
    (next.1, chosen.2 + next.2 + 1)

theorem step_value (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (s : State n) :
    decode (step G codes s).1 = ShortestPaths.step (edge G) (weight G) (decode s) := by
  dsimp only [step, ShortestPaths.step]
  rw [choose_value codes correct]
  cases h : ShortestPaths.choose (decode s) with
  | none => rfl
  | some u => exact relax_value G codes correct s u

def stepBudget (n L B : Nat) := 4 * n * n + 2 * n + n * (2 * L * (9 * B + 7) + 25 * B + 48) + 10

theorem step_cost (G : Graph n) (codes : Vector (List Bool) n) (s : State n)
    (B : Nat) (bound : Bounds G codes s B) :
    (step G codes s).2 ≤ stepBudget n s.settled.length B := by
  have selection := choose_cost codes s B B bound.1 bound.2.1
  have algebra : stepBudget n s.settled.length B =
      (2 * n * n + 2 * n + n * (s.settled.length * (9 * B + 7) + 9 * B + 19) + 4) +
      (2 * n * n + n * (s.settled.length * (9 * B + 7) + 16 * B + 29) + 5) + 1 := by
    unfold stepBudget
    ring
  rw [algebra]
  dsimp only [step]
  split
  · omega
  · rename_i u hu
    have relaxation := relax_cost G codes s B bound u
    omega

theorem step_bounds (G : Graph n) (codes : Vector (List Bool) n) (s : State n)
    (B : Nat) (bound : Bounds G codes s B) :
    Bounds G codes (step G codes s).1 (B + 1) ∧ (step G codes s).1.settled.length ≤ s.settled.length + 1 := by
  have code : ∀ v : Fin n, codes[v.val].length ≤ B + 1 := fun v => Nat.le_succ_of_le (bound.1 v)
  have weights : ∀ u v : Fin n, G.cost[u.val][v.val].length ≤ B + 1 :=
    fun u v => Nat.le_succ_of_le (bound.2.2 u v)
  dsimp only [step]
  split
  · exact ⟨⟨code, (fun v => Nat.le_succ_of_le (bound.2.1 v)), weights⟩, by simp⟩
  · rename_i u hu
    refine ⟨⟨code, ?_, weights⟩, by simp [relax]⟩
    intro v
    simp only [relax, Costed.tabulate_value]
    exact (relaxCell_bounds G codes s B bound u v).2

theorem stepBudget_mono (n L L' B B' : Nat) (hL : L ≤ L') (hB : B ≤ B') :
    stepBudget n L B ≤ stepBudget n L' B' := by
  have product := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hL)
    (show 9 * B + 7 ≤ 9 * B' + 7 by omega)
  have inside : 2 * L * (9 * B + 7) + 25 * B + 48 ≤
      2 * L' * (9 * B' + 7) + 25 * B' + 48 := by omega
  have scaled := Nat.mul_le_mul_left n inside
  unfold stepBudget
  omega

def run (G : Graph n) (codes : Vector (List Bool) n) : Nat → State n → Costed.Computation (State n)
  | 0, s => (s, 1)
  | fuel + 1, s =>
    let next := step G codes s
    let rest := run G codes fuel next.1
    (rest.1, next.2 + rest.2 + 1)

theorem run_value (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (fuel : Nat) (s : State n) :
    decode (run G codes fuel s).1 = ShortestPaths.run (edge G) (weight G) fuel (decode s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [run, ShortestPaths.run, ih, step_value G codes correct]

theorem run_cost (G : Graph n) (codes : Vector (List Bool) n) (fuel : Nat) (s : State n)
    (B : Nat) (bound : Bounds G codes s B) :
    (run G codes fuel s).2 ≤
      fuel * (stepBudget n (s.settled.length + fuel) (B + fuel) + 1) + 1 := by
  induction fuel generalizing s B with
  | zero => simp [run]
  | succ fuel ih =>
    have nextBound := step_bounds G codes s B bound
    have rest := ih (step G codes s).1 (B + 1) nextBound.1
    have current := step_cost G codes s B bound
    have grow := stepBudget_mono n ((step G codes s).1.settled.length + fuel)
      (s.settled.length + (fuel + 1)) ((B + 1) + fuel) (B + (fuel + 1)) (by omega) (by omega)
    have restScale := Nat.mul_le_mul_left fuel (Nat.add_le_add_right grow 1)
    have first := stepBudget_mono n s.settled.length (s.settled.length + (fuel + 1))
      B (B + (fuel + 1)) (by omega) (by omega)
    simp only [run, Nat.succ_mul]
    omega

def initial (codes : Vector (List Bool) n) (source : Fin n) (bound : List Bool) :
    Costed.Computation (State n) :=
  let table := Costed.tabulate n (fun v =>
    let same := equalVertex codes v source
    (if same.1 then [] else bound, same.2 + 2))
  (⟨[], table.1⟩, table.2 + 1)

theorem initial_value (codes : Vector (List Bool) n) (correct : CodebookCorrect codes)
    (source : Fin n) (bound : List Bool) :
    decode (initial codes source bound).1 = ShortestPaths.initialState source (value bound) := by
  apply decoded_ext
  · simp [decode, initial, ShortestPaths.initialState]
  · intro v
    rw [decode_get]
    simp [initial, Costed.tabulate_value, equalVertex_value codes correct,
      ShortestPaths.get, ShortestPaths.initialState, value]
    split <;> rfl

theorem initial_bounds (G : Graph n) (codes : Vector (List Bool) n) (source : Fin n)
    (word : List Bool) (B : Nat)
    (codeBound : ∀ v : Fin n, codes[v.val].length ≤ B)
    (weightBound : ∀ u v : Fin n, G.cost[u.val][v.val].length ≤ B) (wordBound : word.length ≤ B) :
    Bounds G codes (initial codes source word).1 B := by
  refine ⟨codeBound, ?_, weightBound⟩
  intro v
  simp only [initial, Costed.tabulate_value]
  split <;> simp_all

theorem initial_cost (codes : Vector (List Bool) n) (source : Fin n) (word : List Bool) (B : Nat)
    (codeBound : ∀ v : Fin n, codes[v.val].length ≤ B) :
    (initial codes source word).2 ≤ 2 * n * n + n * (9 * B + 12) + 4 := by
  have cost := Costed.tabulate_cost n (fun v =>
    let same := equalVertex codes v source
    (if same.1 then [] else word, same.2 + 2)) (9 * B + 6)
    (fun v => by have h := equalVertex_cost codes B codeBound v source; dsimp only; omega)
  have eq : 9 * B + 6 + 6 = 9 * B + 12 := by omega
  rw [eq] at cost
  dsimp only at cost
  dsimp only [initial]
  omega

def dijkstra (G : Graph n) (codes : Vector (List Bool) n) (source : Fin n) (bound : List Bool) :
    Costed.Computation (State n) :=
  let start := initial codes source bound
  let result := run G codes n start.1
  (result.1, start.2 + result.2 + 1)

theorem dijkstra_value (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (source : Fin n) (bound : List Bool) :
    decode (dijkstra G codes source bound).1 =
      ShortestPaths.run (edge G) (weight G) n (ShortestPaths.initialState source (value bound)) := by
  simp only [dijkstra, run_value G codes correct, initial_value codes correct]

/-- Complete charged loop cost for this word implementation. It includes
enumeration, membership scans, selection, arithmetic, and table reconstruction.
Finite-index/reference operations use the explicit RAM model of the primitives. -/
theorem dijkstra_cost (G : Graph n) (codes : Vector (List Bool) n)
    (source : Fin n) (word : List Bool) (B : Nat)
    (codeBound : ∀ v : Fin n, codes[v.val].length ≤ B)
    (weightBound : ∀ u v : Fin n, G.cost[u.val][v.val].length ≤ B) (wordBound : word.length ≤ B) :
    (dijkstra G codes source word).2 ≤
      2 * n * n + n * (9 * B + 12) + n * (stepBudget n n (B + n) + 1) + 6 := by
  have start := initial_cost codes source word B codeBound
  have looping := run_cost G codes n (initial codes source word).1 B
    (initial_bounds G codes source word B codeBound weightBound wordBound)
  change (run G codes n (initial codes source word).1).2 ≤
    n * (stepBudget n (0 + n) (B + n) + 1) + 1 at looping
  simp only [Nat.zero_add] at looping
  dsimp only [dijkstra]
  omega

theorem dijkstra_correct (G : Graph n) (codes : Vector (List Bool) n)
    (correct : CodebookCorrect codes) (source : Fin n) (bound : List Bool) :
    let d := fun v : Fin n => value (dijkstra G codes source bound).1.distance[v.val]
    ShortestPaths.Admissible (edge G) (weight G) source (value bound) d ∧
      ∀ q, ShortestPaths.Admissible (edge G) (weight G) source (value bound) q → ∀ v, q v ≤ d v := by
  have spec := ShortestPaths.dijkstra_correct (edge G) (weight G) source (value bound)
  rw [← dijkstra_value G codes correct] at spec
  dsimp only at spec
  have getEq : ShortestPaths.get (decode (dijkstra G codes source bound).1) =
      (fun v : Fin n => value (dijkstra G codes source bound).1.distance[v.val]) :=
    funext (decode_get (dijkstra G codes source bound).1)
  rw [getEq] at spec
  exact spec

theorem run_bounds (G : Graph n) (codes : Vector (List Bool) n) (fuel : Nat)
    (s : State n) (B : Nat) (bound : Bounds G codes s B) :
    Bounds G codes (run G codes fuel s).1 (B + fuel) := by
  induction fuel generalizing s B with
  | zero => simpa [run] using bound
  | succ fuel ih =>
    have h := ih (step G codes s).1 (B + 1) (step_bounds G codes s B bound).1
    simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem dijkstra_bounds (G : Graph n) (codes : Vector (List Bool) n)
    (source : Fin n) (word : List Bool) (B : Nat)
    (codeBound : ∀ v : Fin n, codes[v.val].length ≤ B)
    (weightBound : ∀ u v : Fin n, G.cost[u.val][v.val].length ≤ B) (wordBound : word.length ≤ B) :
    Bounds G codes (dijkstra G codes source word).1 (B + n) :=
  run_bounds G codes n _ B (initial_bounds G codes source word B codeBound weightBound wordBound)

end GyoriLovasz.WordShortest
