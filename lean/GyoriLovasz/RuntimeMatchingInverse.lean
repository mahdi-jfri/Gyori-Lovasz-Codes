import GyoriLovasz.RuntimeMatchingWitness
import GyoriLovasz.RuntimeRootMatching

namespace GyoriLovasz.TransportNetwork

def inverseEntry (matching : Vector (Option (Fin r)) l) (v : Fin r) : Costed.Computation (Option (Fin l)) :=
  let indices := Costed.enumerateIndices l
  let found := Costed.find (fun i => (decide (matching[i.val] = some v), 3)) indices.1
  (found.1, indices.2 + found.2 + 1)

theorem inverseEntry_some (matching : Vector (Option (Fin r)) l) (v : Fin r) (i : Fin l)
    (h : (inverseEntry matching v).1 = some i) : matching[i.val] = some v := by
  rw [inverseEntry, Costed.find_value] at h
  have yes := List.find?_some h
  exact of_decide_eq_true yes

theorem inverseEntry_exists (matching : Vector (Option (Fin r)) l) (v : Fin r)
    (h : ∃ i : Fin l, matching[i.val] = some v) : ∃ i, (inverseEntry matching v).1 = some i := by
  cases hs : (inverseEntry matching v).1 with
  | some i => exact ⟨i, rfl⟩
  | none =>
    rw [inverseEntry, Costed.find_value] at hs
    obtain ⟨i, hi⟩ := h
    have no := List.find?_eq_none.mp hs i (by simp [Costed.enumerateIndices_value])
    simp [hi] at no

theorem inverseEntry_cost (matching : Vector (Option (Fin r)) l) (v : Fin r) :
    (inverseEntry matching v).2 ≤ 2 * l * l + 8 * l + 3 := by
  have hi := Costed.enumerateIndices_cost l
  have hf := Costed.find_cost (fun i : Fin l => (decide (matching[i.val] = some v), 3))
    (Costed.enumerateIndices l).1 3 (by intros; rfl)
  simp only [Costed.enumerateIndices_value, List.length_finRange] at hf
  dsimp only [inverseEntry]
  simp only [Costed.enumerateIndices_value]
  omega

def inverseMatching (matching : Vector (Option (Fin r)) l) : Costed.Computation (Vector (Option (Fin l)) r) :=
  Costed.tabulate r (inverseEntry matching)

theorem inverseMatching_some (matching : Vector (Option (Fin r)) l) (v : Fin r) (i : Fin l)
    (h : (inverseMatching matching).1[v.val] = some i) : matching[i.val] = some v := by
  rw [inverseMatching, Costed.tabulate_value] at h
  exact inverseEntry_some matching v i h

theorem inverseMatching_exists (matching : Vector (Option (Fin r)) l) (v : Fin r)
    (h : ∃ i : Fin l, matching[i.val] = some v) : ∃ i, (inverseMatching matching).1[v.val] = some i := by
  simpa only [inverseMatching, Costed.tabulate_value] using inverseEntry_exists matching v h

theorem inverseMatching_cost (matching : Vector (Option (Fin r)) l) :
    (inverseMatching matching).2 ≤ 2 * r * r + r * (2 * l * l + 8 * l + 9) + 3 := by
  simpa only [inverseMatching, Nat.add_assoc] using Costed.tabulate_cost r (inverseEntry matching)
    (2 * l * l + 8 * l + 3) (inverseEntry_cost matching)

/-- A matching of all but one member of a deficient set covers its entire
neighbor set. This is the finite-cardinality step used to invert the computed matching. -/
theorem matching_covers_deficiency (matching : Vector (Option (Fin r)) l)
    (S : Finset (Fin l)) (N : Finset (Fin r)) (i : Fin l) (hi : i ∈ S)
    (deficient : N.card < S.card)
    (matched : ∀ a ∈ S.erase i, ∃ v, matching[a.val] = some v ∧ v ∈ N)
    (inj : ∀ (a b : Fin l) (v : Fin r), matching[a.val] = some v → matching[b.val] = some v → a = b) :
    ∀ v ∈ N, ∃ a ∈ S.erase i, matching[a.val] = some v := by
  classical
  let f : ↥(S.erase i) → Fin r := fun a => Classical.choose (matched a.val a.property)
  have spec (a : ↥(S.erase i)) : matching[a.val] = some (f a) ∧ f a ∈ N :=
    Classical.choose_spec (matched a.val a.property)
  have fi : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply inj a.val b.val (f a) (spec a).1
    simpa only [he] using (spec b).1
  have sub : Finset.univ.image f ⊆ N := by
    intro v hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
    exact (spec a).2
  have card : (Finset.univ.image f).card = S.card - 1 := by
    rw [Finset.card_image_of_injective _ fi, Finset.card_univ, Fintype.card_coe, Finset.card_erase_of_mem hi]
  have eq : Finset.univ.image f = N := Finset.eq_of_subset_of_card_le sub (by omega)
  intro v hv
  rw [← eq] at hv
  obtain ⟨a, _, he⟩ := Finset.mem_image.mp hv
  exact ⟨a.val, a.property, by simpa only [he] using (spec a).1⟩

theorem inverse_matching_rounds (matching : Vector (Option (Fin r)) l)
    (S : Finset (Fin l)) (N : Finset (Fin r)) (i : Fin l) (hi : i ∈ S)
    (deficient : N.card < S.card)
    (matched : ∀ a ∈ S.erase i, ∃ v, matching[a.val] = some v ∧ v ∈ N)
    (inj : ∀ (a b : Fin l) (v : Fin r), matching[a.val] = some v → matching[b.val] = some v → a = b) :
    let f := fun v : Fin r => ((inverseMatching matching).1[v.val]).getD i
    Set.InjOn f N ∧ ∀ v ∈ N, f v ∈ S ∧ matching[(f v).val] = some v := by
  have covers := matching_covers_deficiency matching S N i hi deficient matched inj
  have values (v : Fin r) (hv : v ∈ N) :
      ((inverseMatching matching).1[v.val]).getD i ∈ S ∧
        matching[(((inverseMatching matching).1[v.val]).getD i).val] = some v := by
    obtain ⟨a, ha, he⟩ := covers v hv
    obtain ⟨b, hb⟩ := inverseMatching_exists matching v ⟨a, he⟩
    have be := inverseMatching_some matching v b hb
    have ab := inj a b v he be
    simpa only [hb, Option.getD_some, ← ab] using And.intro (Finset.mem_of_mem_erase ha) he
  refine ⟨?_, values⟩
  intro v hv w hw eq
  have first := (values v hv).2
  have second := (values w hw).2
  change ((inverseMatching matching).1[v.val]).getD i = ((inverseMatching matching).1[w.val]).getD i at eq
  rw [eq] at first
  exact Option.some.inj (first.symm.trans second)

end GyoriLovasz.TransportNetwork
