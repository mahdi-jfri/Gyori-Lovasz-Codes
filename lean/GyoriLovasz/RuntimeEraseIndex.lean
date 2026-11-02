import GyoriLovasz.RuntimeReindex
import GyoriLovasz.Shrink

namespace GyoriLovasz.ComputedReindex

def eraseIndex (p : Fin (m + 1)) (positive : 0 < m) : Costed.Computation (Vector (Fin m) (m + 1)) :=
  let vertices := Costed.tabulate m (fun x => (p.succAbove x, 3))
  let result := inverse vertices.1 ⟨0, positive⟩
  (result.1, vertices.2 + result.2 + 1)

theorem eraseIndex_inverse (p : Fin (m + 1)) (positive : 0 < m) (x : Fin m) :
    (eraseIndex p positive).1[(p.succAbove x).val] = x := by
  have h := inverse_left (Costed.tabulate m (fun x => (p.succAbove x, 3))).1 ⟨0, positive⟩
    (by simpa only [Costed.tabulate_value] using Fin.succAbove_right_injective (p := p)) x
  simpa only [eraseIndex, Costed.tabulate_value] using h

theorem eraseIndex_retract (p : Fin (m + 1)) (positive : 0 < m) (v : Fin (m + 1)) (hne : v ≠ p) :
    p.succAbove (eraseIndex p positive).1[v.val] = v := by
  obtain ⟨x, hx⟩ := Fin.exists_succAbove_eq hne
  rw [← hx, eraseIndex_inverse]

theorem eraseIndex_graph (p : Fin (m + 1)) (positive : 0 < m)
    (E : Fin (m + 1) → Fin (m + 1) → Prop) (T : Fin (m + 1) → Prop)
    (edges : ∀ x y, E x y → x ≠ p ∧ y ≠ p) (terminal : ¬T p) :
    GraphReindex ((List.finRange (m + 1)).erase p) (List.finRange m) E T p.succAbove
      (fun v => (eraseIndex p positive).1[v.val]) := by
  obtain ⟨r, h⟩ := exists_erase_reindex positive p E T edges terminal
  refine ⟨h.complete, eraseIndex_inverse p positive, ?_, h.enumeration, h.edges, h.terminals⟩
  intro v hv
  apply eraseIndex_retract
  intro he
  exact List.Nodup.not_mem_erase (finRange_nodup (m + 1)) (he ▸ hv)

def eraseIndexBudget (m : Nat) := (2 * m * m + 9 * m + 3) +
  (2 * (m + 1) * (m + 1) + (m + 1) * (2 * m * m + 7 * m + 10) + 3) + 1

theorem eraseIndex_cost (p : Fin (m + 1)) (positive : 0 < m) :
    (eraseIndex p positive).2 ≤ eraseIndexBudget m := by
  have hv := Costed.tabulate_cost m (fun x => (p.succAbove x, 3)) 3 (by intros; rfl)
  have hr := inverse_cost (Costed.tabulate m (fun x => (p.succAbove x, 3))).1 ⟨0, positive⟩
  dsimp only [eraseIndex, eraseIndexBudget]
  norm_num only at hv
  simp only [Nat.mul_comm m 9] at hv
  omega

end GyoriLovasz.ComputedReindex
