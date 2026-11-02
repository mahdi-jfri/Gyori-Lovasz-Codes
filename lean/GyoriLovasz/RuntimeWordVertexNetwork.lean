import GyoriLovasz.RuntimePairTable
import GyoriLovasz.RuntimeWordCodes

namespace GyoriLovasz.VertexNetwork
open Flow Binary

/-- The pair table supplies graph endpoints by lookup. Finite-index branches
and address additions are reference-RAM operations; no division is executed
to recover a pair from its arc index. -/
def build (E : Vector (Vector Bool n) n) (T : Vector Bool n) :
    Costed.Computation (WordResidual (n + n + 1) (n + (n * n + n))) :=
  let pairs := Costed.pairTable n
  let codes := wordCodes (n + n + 1)
  let high := countWord (n + 1)
  let tails := Costed.tabulate (n + (n * n + n)) (fun e =>
    (Fin.addCases (motive := fun _ => Fin (n + n + 1)) inside
      (Fin.addCases (fun a => outside pairs.1[a.val].1) outside) e, 10))
  let heads := Costed.tabulate (n + (n * n + n)) (fun e =>
    (Fin.addCases (motive := fun _ => Fin (n + n + 1)) outside
      (Fin.addCases (fun a => inside pairs.1[a.val].2) (fun _ => 0)) e, 10))
  let caps := Costed.tabulate (n + (n * n + n)) (fun e =>
    (Fin.addCases (motive := fun _ => List Bool) (fun _ => [true])
      (Fin.addCases (fun a => if E[pairs.1[a.val].1.val][pairs.1[a.val].2.val] then high.1 else [])
        (fun v => if T[v.val] then high.1 else [])) e, 6))
  let costs := Costed.tabulate (n + (n * n + n)) (fun _ => ((⟨false, []⟩ : SignedWord), 1))
  let pots := Costed.tabulate (n + n + 1) (fun _ => ((⟨false, []⟩ : SignedWord), 1))
  (⟨tails.1, heads.1, codes.1, caps.1, caps.1, costs.1, pots.1⟩,
    pairs.2 + codes.2 + high.2 + tails.2 + heads.2 + caps.2 + costs.2 + pots.2 + 1)

theorem build_network (E : Vector (Vector Bool n) n) (T : Vector Bool n) :
    decodeNetwork (build E T).1 = network (fun u v => E[u.val][v.val]) (fun v => T[v.val]) := by
  simp only [decodeNetwork, build, Costed.tabulate_value, Costed.pairTable_value, network]
  congr 1
  · funext e
    refine Fin.addCases ?_ ?_ e
    · intro v; simp [value]
    · intro a
      refine Fin.addCases ?_ ?_ a
      · intro uv; simp only [Fin.addCases_right, Fin.addCases_left]; split <;> simp [countWord_value, value]
      · intro v; simp only [Fin.addCases_right]; split <;> simp [countWord_value, value]

theorem build_codes (E : Vector (Vector Bool n) n) (T : Vector Bool n) :
    VertexCodesCorrect (build E T).1 := wordCodes_correct _

theorem build_bounds (E : Vector (Vector Bool n) n) (T : Vector Bool n) :
    WordResidualBound (build E T).1 (n + n + 1) := by
  constructor
  · intro e
    have cap : (build E T).1.capacity[e.val].length ≤ n + n + 1 := by
      simp only [build, Costed.tabulate_value]
      refine Fin.addCases ?_ ?_ e
      · intro v; simp
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro uv
          simp only [Fin.addCases_right, Fin.addCases_left]
          split
          · exact Nat.le_trans (countWord_length _) (by omega)
          · simp
        · intro v
          simp only [Fin.addCases_right]
          split
          · exact Nat.le_trans (countWord_length _) (by omega)
          · simp
    exact ⟨cap, cap, by simp [build, Costed.tabulate_value]⟩
  · intro v
    exact ⟨wordCodes_length _ v, by simp [build, Costed.tabulate_value]⟩

def buildBudget (n : Nat) :=
  (9 * n * n + 5 * n + 4) + (7 * (n + n + 1) * (n + n + 1) + 6 * (n + n + 1) + 2) +
  ((n + 1) * (7 * (n + 1) + 3) + 1) +
  2 * (2 * (n + (n * n + n)) * (n + (n * n + n)) + (n + (n * n + n)) * 16 + 3) +
  (2 * (n + (n * n + n)) * (n + (n * n + n)) + (n + (n * n + n)) * 12 + 3) +
  (2 * (n + (n * n + n)) * (n + (n * n + n)) + (n + (n * n + n)) * 7 + 3) +
  (2 * (n + n + 1) * (n + n + 1) + (n + n + 1) * 7 + 3) + 1

theorem build_cost (E : Vector (Vector Bool n) n) (T : Vector Bool n) :
    (build E T).2 ≤ buildBudget n := by
  have hp := Costed.pairTable_cost n
  have hc := wordCodes_cost (n + n + 1)
  have hh := countWord_cost (n + 1)
  have tails := Costed.tabulate_cost (n + (n * n + n)) (fun e =>
    (Fin.addCases (motive := fun _ => Fin (n + n + 1)) inside
      (Fin.addCases (fun a => outside (Costed.pairTable n).1[a.val].1) outside) e, 10)) 10
    (by intros; exact Nat.le_refl _)
  have heads := Costed.tabulate_cost (n + (n * n + n)) (fun e =>
    (Fin.addCases (motive := fun _ => Fin (n + n + 1)) outside
      (Fin.addCases (fun a => inside (Costed.pairTable n).1[a.val].2) (fun _ => 0)) e, 10)) 10
    (by intros; exact Nat.le_refl _)
  have caps := Costed.tabulate_cost (n + (n * n + n)) (fun e =>
    (Fin.addCases (motive := fun _ => List Bool) (fun _ => [true])
      (Fin.addCases (fun a => if E[(Costed.pairTable n).1[a.val].1.val][(Costed.pairTable n).1[a.val].2.val]
        then (countWord (n + 1)).1 else []) (fun v => if T[v.val] then (countWord (n + 1)).1 else [])) e, 6)) 6
    (by intros; exact Nat.le_refl _)
  have costs := Costed.tabulate_cost (n + (n * n + n)) (fun _ => ((⟨false, []⟩ : SignedWord), 1)) 1
    (by intros; exact Nat.le_refl _)
  have pots := Costed.tabulate_cost (n + n + 1) (fun _ => ((⟨false, []⟩ : SignedWord), 1)) 1
    (by intros; exact Nat.le_refl _)
  dsimp only [build, buildBudget]
  omega

end GyoriLovasz.VertexNetwork
