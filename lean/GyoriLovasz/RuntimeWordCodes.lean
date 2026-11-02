import GyoriLovasz.RuntimeWordEncoding

namespace GyoriLovasz.Binary

def codeLoop : Nat → List Bool → Costed.Computation (List (List Bool))
  | 0, _ => ([], 1)
  | fuel + 1, word =>
    let next := addCarry word [] true
    let rest := codeLoop fuel next.1
    (word :: rest.1, next.2 + rest.2 + 3)

theorem codeLoop_length (fuel : Nat) (word : List Bool) : (codeLoop fuel word).1.length = fuel := by
  induction fuel generalizing word with
  | zero => rfl
  | succ fuel ih => simp [codeLoop, ih]

theorem codeLoop_values (fuel : Nat) (word : List Bool) :
    ((codeLoop fuel word).1.map value) = List.ofFn (fun i : Fin fuel => value word + i.val) := by
  induction fuel generalizing word with
  | zero => rfl
  | succ fuel ih =>
    simp only [codeLoop, List.map_cons, ih, List.ofFn_succ]
    simp [addCarry_correct, value, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem codeLoop_wordLength (fuel : Nat) (word : List Bool) (x : List Bool)
    (mem : x ∈ (codeLoop fuel word).1) : x.length ≤ word.length + fuel := by
  induction fuel generalizing word with
  | zero => simp [codeLoop] at mem
  | succ fuel ih =>
    simp only [codeLoop, List.mem_cons] at mem
    rcases mem with eq | mem
    · subst x; omega
    · have h := ih _ mem
      have hn := addCarry_length word [] true
      simp only [List.length_nil, Nat.max_zero] at hn
      omega

theorem codeLoop_cost (fuel : Nat) (word : List Bool) :
    (codeLoop fuel word).2 ≤ fuel * (7 * (word.length + fuel) + 5) + 1 := by
  induction fuel generalizing word with
  | zero => simp [codeLoop]
  | succ fuel ih =>
    have hr := ih (addCarry word [] true).1
    have hn := addCarry_length word [] true
    have hc := addCarry_steps word [] true
    simp only [List.length_nil, Nat.max_zero] at hn hc
    have hm := Nat.mul_le_mul_left fuel
      (show 7 * ((addCarry word [] true).1.length + fuel) + 5 ≤
        7 * (word.length + (fuel + 1)) + 5 by omega)
    simp only [codeLoop, Nat.add_mul, Nat.one_mul]
    omega

def wordCodes (n : Nat) : Costed.Computation (Vector (List Bool) n) :=
  let generated := codeLoop n []
  (⟨generated.1.toArray, by simp [generated, codeLoop_length]⟩, generated.2 + n + 1)

theorem wordCodes_correct (n : Nat) : WordShortest.CodebookCorrect (wordCodes n).1 := by
  intro v
  have h := congrArg (fun xs : List Nat => xs[v.val]!) (codeLoop_values n [])
  have hl : v.val < (codeLoop n []).1.length := by rw [codeLoop_length]; exact v.isLt
  simpa [wordCodes, getElem!_pos, hl, value] using h

theorem wordCodes_length (n : Nat) (v : Fin n) : (wordCodes n).1[v.val].length ≤ n := by
  have hl : v.val < (codeLoop n []).1.length := by rw [codeLoop_length]; exact v.isLt
  have h := codeLoop_wordLength n [] ((codeLoop n []).1[v.val]) (List.getElem_mem hl)
  simpa [wordCodes] using h

theorem wordCodes_cost (n : Nat) : (wordCodes n).2 ≤ 7 * n * n + 6 * n + 2 := by
  have h := codeLoop_cost n []
  simp only [List.length_nil, Nat.zero_add] at h
  dsimp only [wordCodes]
  ring_nf at h ⊢
  omega

def countWord : Nat → Costed.Computation (List Bool)
  | 0 => ([], 1)
  | n + 1 =>
    let old := countWord n
    let next := addCarry old.1 [] true
    (next.1, old.2 + next.2 + 1)

theorem countWord_value (n : Nat) : value (countWord n).1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [countWord, addCarry_correct, value, ih]

theorem countWord_length (n : Nat) : (countWord n).1.length ≤ n := by
  induction n with
  | zero => simp [countWord]
  | succ n ih =>
    have h := addCarry_length (countWord n).1 [] true
    simp only [List.length_nil, Nat.max_zero] at h
    dsimp only [countWord]
    omega

theorem countWord_cost (n : Nat) : (countWord n).2 ≤ n * (7 * n + 3) + 1 := by
  induction n with
  | zero => simp [countWord]
  | succ n ih =>
    have hl := countWord_length n
    have hc := addCarry_steps (countWord n).1 [] true
    simp only [List.length_nil, Nat.max_zero] at hc
    have hm := Nat.mul_le_mul_left n (show 7 * n + 3 ≤ 7 * (n + 1) + 3 by omega)
    simp only [countWord, Nat.add_mul, Nat.one_mul]
    omega

end GyoriLovasz.Binary

