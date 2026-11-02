import GyoriLovasz.Transport
import GyoriLovasz.FiniteGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup

namespace GyoriLovasz

/-- Reindex any nonempty active vertex list, including deletion of an entire
rounded neighborhood, rather than just deletion of one vertex. -/
theorem exists_active_reindex (vertices : List (Fin n)) (hn : vertices.Nodup)
    (positive : 0 < vertices.length) (E : Fin n → Fin n → Prop) (T : Fin n → Prop)
    (edges : ∀ x y, E x y → x ∈ vertices ∧ y ∈ vertices)
    (terminals : ∀ x, T x → x ∈ vertices) :
    ∃ r : Fin n → Fin vertices.length,
      GraphReindex vertices (List.finRange vertices.length) E T vertices.get r := by
  classical
  letI : Nonempty (Fin vertices.length) := ⟨⟨0, positive⟩⟩
  let r := Function.invFun vertices.get
  refine ⟨r, mem_finRange, Function.leftInverse_invFun (List.nodup_iff_injective_get.mp hn),
    ?_, ?_, edges, terminals⟩
  · intro x hx
    apply Function.invFun_eq
    exact List.mem_iff_get.mp hx
  · rw [List.finRange_map_get]

end GyoriLovasz
