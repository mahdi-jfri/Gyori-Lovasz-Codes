import GyoriLovasz.RuntimeTransportNetwork
import GyoriLovasz.RuntimePairTable
import GyoriLovasz.RuntimeWordCodes

namespace GyoriLovasz.TransportNetwork
open Flow Binary

def build (allowed : Vector (Vector Bool r) l) (supply : Vector (List Bool) l)
    (capacity : Vector (List Bool) r) : Costed.Computation (WordResidual (l + r + 2) (l + (l * r + r))) :=
  let pairs := Costed.pairTableRect l r
  let codes := wordCodes (l + r + 2)
  let tails := Costed.tabulate (l + (l * r + r)) (fun e =>
    (Fin.addCases (motive := fun _ => Fin (l + r + 2)) (fun _ => 0)
      (Fin.addCases (fun a => leftNode pairs.1[a.val].1) rightNode) e, 10))
  let heads := Costed.tabulate (l + (l * r + r)) (fun e =>
    (Fin.addCases (motive := fun _ => Fin (l + r + 2)) leftNode
      (Fin.addCases (fun a => rightNode pairs.1[a.val].2) (fun _ => sinkNode)) e, 10))
  let caps := Costed.tabulate (l + (l * r + r)) (fun e =>
    (Fin.addCases (motive := fun _ => List Bool) (fun i => supply[i.val])
      (Fin.addCases (fun a => if allowed[pairs.1[a.val].1.val][pairs.1[a.val].2.val]
        then supply[pairs.1[a.val].1.val] else []) (fun j => capacity[j.val])) e, 6))
  let costs := Costed.tabulate (l + (l * r + r)) (fun _ => ((⟨false, []⟩ : SignedWord), 1))
  let pots := Costed.tabulate (l + r + 2) (fun _ => ((⟨false, []⟩ : SignedWord), 1))
  (⟨tails.1, heads.1, codes.1, caps.1, caps.1, costs.1, pots.1⟩,
    pairs.2 + codes.2 + tails.2 + heads.2 + caps.2 + costs.2 + pots.2 + 1)

theorem build_network (allowed : Vector (Vector Bool r) l) (supply : Vector (List Bool) l)
    (capacity : Vector (List Bool) r) :
    decodeNetwork (build allowed supply capacity).1 =
      network (fun i j => allowed[i.val][j.val]) (fun i => value supply[i.val])
        (fun j => value capacity[j.val]) (fun _ _ => 0) := by
  simp only [decodeNetwork, build, Costed.tabulate_value, Costed.pairTableRect_value, network]
  congr 1
  · funext e
    refine Fin.addCases ?_ ?_ e
    · intro i; simp only [Fin.addCases_left]
    · intro a
      refine Fin.addCases ?_ ?_ a
      · intro ij
        simp only [Fin.addCases_right, Fin.addCases_left]
        split <;> rfl
      · intro j; simp only [Fin.addCases_right]
  · funext e
    refine Fin.addCases ?_ ?_ e
    · intro i; simp [Fin.addCases_left, signedValue, value]
    · intro a
      refine Fin.addCases ?_ ?_ a <;> intro j <;> simp [Fin.addCases_left, Fin.addCases_right, signedValue, value]

theorem build_codes (allowed : Vector (Vector Bool r) l) (supply : Vector (List Bool) l)
    (capacity : Vector (List Bool) r) : VertexCodesCorrect (build allowed supply capacity).1 := wordCodes_correct _

theorem build_bounds (allowed : Vector (Vector Bool r) l) (supply : Vector (List Bool) l)
    (capacity : Vector (List Bool) r) (B : Nat)
    (sb : ∀ i : Fin l, supply[i.val].length ≤ B) (cb : ∀ j : Fin r, capacity[j.val].length ≤ B) :
    WordResidualBound (build allowed supply capacity).1 (B + l + r + 2) := by
  constructor
  · intro e
    have cap : (build allowed supply capacity).1.capacity[e.val].length ≤ B + l + r + 2 := by
      simp only [build, Costed.tabulate_value]
      refine Fin.addCases ?_ ?_ e
      · intro i
        simp only [Fin.addCases_left]
        exact Nat.le_trans (sb i) (by omega)
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro ij
          simp only [Fin.addCases_right, Fin.addCases_left]
          split
          · exact Nat.le_trans (sb _) (by omega)
          · simp
        · intro j
          simp only [Fin.addCases_right]
          exact Nat.le_trans (cb j) (by omega)
    exact ⟨cap, cap, by simp [build, Costed.tabulate_value]⟩
  · intro v
    exact ⟨Nat.le_trans (wordCodes_length _ v) (by omega), by simp [build, Costed.tabulate_value]⟩

def buildBudget (l r : Nat) :=
  (2 * l * l + 2 * r * r + 7 * l * r + 5 * l + 2 * r + 5) +
  (7 * (l + r + 2) * (l + r + 2) + 6 * (l + r + 2) + 2) +
  2 * (2 * (l + (l * r + r)) * (l + (l * r + r)) + (l + (l * r + r)) * 16 + 3) +
  (2 * (l + (l * r + r)) * (l + (l * r + r)) + (l + (l * r + r)) * 12 + 3) +
  (2 * (l + (l * r + r)) * (l + (l * r + r)) + (l + (l * r + r)) * 7 + 3) +
  (2 * (l + r + 2) * (l + r + 2) + (l + r + 2) * 7 + 3) + 1

theorem build_cost (allowed : Vector (Vector Bool r) l) (supply : Vector (List Bool) l)
    (capacity : Vector (List Bool) r) : (build allowed supply capacity).2 ≤ buildBudget l r := by
  have hp := Costed.pairTableRect_cost l r
  have hc := wordCodes_cost (l + r + 2)
  have tails := Costed.tabulate_cost (l + (l * r + r)) (fun e =>
    (Fin.addCases (motive := fun _ => Fin (l + r + 2)) (fun _ => 0)
      (Fin.addCases (fun a => leftNode (Costed.pairTableRect l r).1[a.val].1) rightNode) e, 10)) 10
    (by intros; exact Nat.le_refl _)
  have heads := Costed.tabulate_cost (l + (l * r + r)) (fun e =>
    (Fin.addCases (motive := fun _ => Fin (l + r + 2)) leftNode
      (Fin.addCases (fun a => rightNode (Costed.pairTableRect l r).1[a.val].2) (fun _ => sinkNode)) e, 10)) 10
    (by intros; exact Nat.le_refl _)
  have caps := Costed.tabulate_cost (l + (l * r + r)) (fun e =>
    (Fin.addCases (motive := fun _ => List Bool) (fun i => supply[i.val])
      (Fin.addCases (fun a => if allowed[(Costed.pairTableRect l r).1[a.val].1.val][(Costed.pairTableRect l r).1[a.val].2.val]
        then supply[(Costed.pairTableRect l r).1[a.val].1.val] else []) (fun j => capacity[j.val])) e, 6)) 6
    (by intros; exact Nat.le_refl _)
  have costs := Costed.tabulate_cost (l + (l * r + r)) (fun _ => ((⟨false, []⟩ : SignedWord), 1)) 1
    (by intros; exact Nat.le_refl _)
  have pots := Costed.tabulate_cost (l + r + 2) (fun _ => ((⟨false, []⟩ : SignedWord), 1)) 1
    (by intros; exact Nat.le_refl _)
  dsimp only [build, buildBudget]
  omega

def matrixCheck (allowed : Vector (Vector Bool r) l) (supply : Vector (List Bool) l)
    (capacity : Vector (List Bool) r) (B : Nat) : Bool × Nat :=
  let built := build allowed supply capacity
  let solved := maxFlowWords built.1 0 sinkNode (B + l + r + 2)
  let achieved := addCarry solved.1.flow[0] [] true
  let required := returnCapacity supply
  let cmp := compareWords achieved.1 required.1
  (cmp.1.2, built.2 + solved.2 + achieved.2 + required.2 + cmp.2 + 3)

theorem matrixCheck_correct (allowed : Vector (Vector Bool r) l) (supply : Vector (List Bool) l)
    (capacity : Vector (List Bool) r) (B : Nat)
    (sb : ∀ i : Fin l, supply[i.val].length ≤ B) (cb : ∀ j : Fin r, capacity[j.val].length ≤ B) :
    (matrixCheck allowed supply capacity B).1 = true ↔
      ∃ x, MatrixFeasible (fun i j => allowed[i.val][j.val]) (fun i => value supply[i.val])
        (fun j => value capacity[j.val]) x := by
  have h := maxFlowWords_correct (build allowed supply capacity).1 (build_codes allowed supply capacity)
    0 sinkNode (Ne.symm sink_ne_zero) (B + l + r + 2) (build_bounds allowed supply capacity B sb cb)
  rw [build_network] at h
  have spec := maximum_flow_decides_matrix _ _ _ _ _ _ h.1 h.2
  dsimp only [matrixCheck]
  rw [(compareWords_correct _ _).2, addCarry_correct, returnCapacity_value]
  simp only [value, Nat.add_zero, if_true, Nat.add_right_cancel_iff]
  exact spec.symm

def matrixBudget (l r B : Nat) :=
  buildBudget l r + maxFlowBudget (l + r + 2) (l + (l * r + r)) (B + l + r + 2) + returnBudget l B +
  16 * (maxFlowWordLength (l + r + 2) (l + (l * r + r)) (B + l + r + 2) + B + l + 1) + 7

set_option maxHeartbeats 1600000 in
theorem matrixCheck_cost (allowed : Vector (Vector Bool r) l) (supply : Vector (List Bool) l)
    (capacity : Vector (List Bool) r) (B : Nat)
    (sb : ∀ i : Fin l, supply[i.val].length ≤ B) (cb : ∀ j : Fin r, capacity[j.val].length ≤ B) :
    (matrixCheck allowed supply capacity B).2 ≤ matrixBudget l r B := by
  have hb := build_cost allowed supply capacity
  have hs := maxFlowWords_cost (build allowed supply capacity).1 (build_codes allowed supply capacity)
    0 sinkNode _ (build_bounds allowed supply capacity B sb cb)
  have hl := ((maxFlowWords_bounds (build allowed supply capacity).1 (build_codes allowed supply capacity)
    0 sinkNode _ (build_bounds allowed supply capacity B sb cb)).1 0).2.1
  simp only [Fin.val_zero] at hl
  have hr := returnCapacity_bounds supply B sb
  have ha := addCarry_steps
    (maxFlowWords (build allowed supply capacity).1 0 sinkNode (B + l + r + 2)).1.flow[0] [] true
  have hal := addCarry_length
    (maxFlowWords (build allowed supply capacity).1 0 sinkNode (B + l + r + 2)).1.flow[0] [] true
  have hc := compareWords_steps
    (addCarry (maxFlowWords (build allowed supply capacity).1 0 sinkNode (B + l + r + 2)).1.flow[0] [] true).1
    (returnCapacity supply).1
  simp only [List.length_nil, Nat.max_zero] at ha hal
  dsimp only [matrixCheck, matrixBudget, returnBudget]
  omega

end GyoriLovasz.TransportNetwork

