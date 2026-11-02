import GyoriLovasz.RuntimeWordResidual

namespace GyoriLovasz.Costed

/-- Map with callback costs and three reference/control operations per entry. -/
def map (f : α → Computation β) : List α → Computation (List β)
  | [] => ([], 1)
  | x :: xs =>
    let here := f x
    let rest := map f xs
    (here.1 :: rest.1, here.2 + rest.2 + 3)

theorem map_value (f : α → Computation β) (xs : List α) :
    (map f xs).1 = xs.map (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [map, ih]

theorem map_cost (f : α → Computation β) (xs : List α) (C : Nat)
    (bound : ∀ x ∈ xs, (f x).2 ≤ C) : (map f xs).2 ≤ xs.length * (C + 3) + 1 := by
  induction xs with
  | nil => simp [map]
  | cons x xs ih =>
    have here := bound x (by simp)
    have rest := ih (fun y hy => bound y (by simp [hy]))
    simp only [map, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Tabulate once and store the computed values. Index generation uses the
counted enumerator; conversion charges n reference writes and one allocation.
The callback is not re-evaluated during conversion. -/
def tabulate (n : Nat) (f : Fin n → Computation α) : Computation (Vector α n) :=
  let indices := enumerateIndices n
  let generated := map f indices.1
  (⟨generated.1.toArray, by simp [generated, indices, map_value, enumerateIndices_value]⟩,
    indices.2 + generated.2 + n + 1)

theorem tabulate_value (n : Nat) (f : Fin n → Computation α) (i : Fin n) :
    (tabulate n f).1[i.val] = (f i).1 := by
  simp [tabulate, map_value, enumerateIndices_value]

theorem tabulate_cost (n : Nat) (f : Fin n → Computation α) (C : Nat)
    (bound : ∀ i, (f i).2 ≤ C) : (tabulate n f).2 ≤ 2 * n * n + n * (C + 6) + 3 := by
  have mapped := map_cost f (List.finRange n) C (fun i _ => bound i)
  simp only [List.length_finRange] at mapped
  simp only [tabulate, enumerateIndices_value, enumerateIndices_cost]
  simp only [Nat.mul_add] at mapped ⊢
  omega

def tabulate₂ (n : Nat) (f : Fin n → Fin n → Computation α) :
    Computation (Vector (Vector α n) n) := tabulate n (fun u => tabulate n (f u))

theorem tabulate₂_value (n : Nat) (f : Fin n → Fin n → Computation α) (u v : Fin n) :
    ((tabulate₂ n f).1[u.val])[v.val] = (f u v).1 := by
  simp [tabulate₂, tabulate_value]

theorem tabulate₂_cost (n : Nat) (f : Fin n → Fin n → Computation α) (C : Nat)
    (bound : ∀ u v, (f u v).2 ≤ C) :
    (tabulate₂ n f).2 ≤ 2 * n * n * n + n * n * (C + 8) + 9 * n + 3 := by
  have outer := tabulate_cost n (fun u => tabulate n (f u)) (2 * n * n + n * (C + 6) + 3)
    (fun u => tabulate_cost n (f u) C (bound u))
  change (tabulate n (fun u => tabulate n (f u))).2 ≤ _
  calc
    _ ≤ 2 * n * n + n * (2 * n * n + n * (C + 6) + 3 + 6) + 3 := outer
    _ = _ := by ring

end GyoriLovasz.Costed

namespace GyoriLovasz.Flow
open Binary

/-- Select and materialize an arc together with its word score. -/
def wordResidualCell (s : WordResidual n m) (u v : Fin n) :
    Costed.Computation (Option (ResidualArc m × SignedWord)) :=
  let best := wordBestArc s u v
  match best.1 with
  | none => (none, best.2 + 2)
  | some a =>
    let score := wordScore s a
    (some (a, score.1), best.2 + score.2 + 3)

theorem wordResidualCell_value (s : WordResidual n m) (codes : VertexCodesCorrect s)
    (u v : Fin n) :
    (wordResidualCell s u v).1.map (fun p => (p.1, signedValue p.2)) =
      (bestArc (decodeNetwork s) (decodeFlow s) (decodePotential s) u v).map
        (fun a => (a, arcCost (decodeNetwork s) (decodePotential s) a)) := by
  dsimp only [wordResidualCell]
  have best := wordBestArc_value s codes u v
  cases h : (wordBestArc s u v).1 <;> rw [← best, h] <;> simp [wordScore_value]

theorem wordResidualCell_cost (s : WordResidual n m) (B : Nat) (bound : WordResidualBound s B)
    (u v : Fin n) :
    (wordResidualCell s u v).2 ≤ 2 * m * m + 7 * m + 2 * m * (180 * B + 398) + 72 * B + 164 := by
  have selection := wordBestArc_cost s B bound u v
  dsimp only [wordResidualCell]
  split
  · omega
  · rename_i a ha
    have score := (wordScore_bounds s B bound a).1
    omega

def buildWordResidual (s : WordResidual n m) :
    Costed.Computation (Vector (Vector (Option (ResidualArc m × SignedWord)) n) n) :=
  Costed.tabulate₂ n (wordResidualCell s)

theorem buildWordResidual_value (s : WordResidual n m) (codes : VertexCodesCorrect s)
    (u v : Fin n) :
    (((buildWordResidual s).1[u.val])[v.val]).map (fun p => (p.1, signedValue p.2)) =
      (bestArc (decodeNetwork s) (decodeFlow s) (decodePotential s) u v).map
        (fun a => (a, arcCost (decodeNetwork s) (decodePotential s) a)) := by
  simp only [buildWordResidual, Costed.tabulate₂_value]
  exact wordResidualCell_value s codes u v

/-- Polynomial construction cost in the bit-gate/reference-RAM model used by
the callbacks and tabulation. Address bit costs still require a separate
machine-model refinement; this is not the partition runtime theorem. -/
theorem buildWordResidual_cost (s : WordResidual n m) (B : Nat) (bound : WordResidualBound s B) :
    (buildWordResidual s).2 ≤
      2 * n * n * n + n * n * (2 * m * m + 7 * m + 2 * m * (180 * B + 398) + 72 * B + 172) + 9 * n + 3 := by
  have cost := Costed.tabulate₂_cost n (wordResidualCell s)
    (2 * m * m + 7 * m + 2 * m * (180 * B + 398) + 72 * B + 164) (wordResidualCell_cost s B bound)
  simpa only [buildWordResidual, Nat.add_assoc] using cost

end GyoriLovasz.Flow
