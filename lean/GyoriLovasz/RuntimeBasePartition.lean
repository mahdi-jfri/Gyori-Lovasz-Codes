import GyoriLovasz.RuntimeTransform
import GyoriLovasz.WeightedAssembly

namespace GyoriLovasz.WordInstance

def rootIndex (roots : Vector (Fin n) k) (v : Fin n) (h : RootSet (fun i => roots[i.val]) v) :
    Costed.Computation (Fin k) :=
  let found := ComputedReindex.locate roots v
  (found.1.get (by
    obtain ⟨j, hj⟩ := ComputedReindex.locate_exists roots v h
    simp only [found, hj, Option.isSome_some]), found.2 + 1)

theorem rootIndex_correct (roots : Vector (Fin n) k) (v : Fin n) (h : RootSet (fun i => roots[i.val]) v) :
    roots[(rootIndex roots v h).1.val] = v := by
  obtain ⟨j, hj⟩ := ComputedReindex.locate_exists roots v h
  simpa only [rootIndex, hj, Option.get_some] using ComputedReindex.locate_some roots v j hj

theorem rootIndex_cost (roots : Vector (Fin n) k) (v : Fin n) (h : RootSet (fun i => roots[i.val]) v) :
    (rootIndex roots v h).2 ≤ 2 * k * k + 7 * k + 4 := by
  have hl := ComputedReindex.locate_cost roots v
  dsimp only [rootIndex]
  omega

def baseLabels (roots : Vector (Fin n) k) (allroot : ∀ v, RootSet (fun i => roots[i.val]) v) :
    Costed.Computation (Vector (Fin k) n) := Costed.tabulate n (fun v => rootIndex roots v (allroot v))

theorem baseLabels_root (roots : Vector (Fin n) k) (allroot : ∀ v, RootSet (fun i => roots[i.val]) v)
    (v : Fin n) : roots[(baseLabels roots allroot).1[v.val].val] = v := by
  rw [baseLabels, Costed.tabulate_value]
  exact rootIndex_correct roots v (allroot v)

theorem baseLabels_correct (s : Input n k) (limit : Fin k → Nat)
    (inj : Function.Injective (root s)) (zero : ∀ i, weights s (root s i) = 0)
    (allroot : ∀ v, RootSet (root s) v) :
    WeightedPartitionOn Finset.univ Finset.univ (relation s) (root s) (weights s) limit
      (fun v => (baseLabels s.roots allroot).1[v.val]) := by
  classical
  let label := fun v : Fin n => (baseLabels s.roots allroot).1[v.val]
  have root_label (v : Fin n) : root s (label v) = v := baseLabels_root s.roots allroot v
  have label_root (i : Fin k) : label (root s i) = i := inj (root_label _)
  have allzero (v : Fin n) : weights s v = 0 := (congrArg (weights s) (root_label v)).symm.trans (zero _)
  refine ⟨(fun _ _ => Finset.mem_univ _), (fun i _ => ⟨Finset.mem_univ _, label_root i⟩), ?_, ?_⟩
  · intro i _
    have load : partLoad Finset.univ (weights s) label i = 0 := by simp [partLoad, allzero]
    rw [load]
    exact Nat.zero_le _
  · intro i _ x _ hx
    have he : x = root s i := (root_label x).symm.trans (congrArg (root s) hx)
    subst x
    exact .refl _ ⟨Finset.mem_univ _, label_root i⟩

theorem baseLabels_cost (roots : Vector (Fin n) k) (allroot : ∀ v, RootSet (fun i => roots[i.val]) v) :
    (baseLabels roots allroot).2 ≤ 2 * n * n + n * (2 * k * k + 7 * k + 10) + 3 := by
  simpa only [baseLabels, Nat.add_assoc] using Costed.tabulate_cost n _ (2 * k * k + 7 * k + 4)
    (fun v => rootIndex_cost roots v (allroot v))

def normalize (s : Input n k) : Costed.Computation (Input n k) :=
  let mask := rootMask s.roots
  let weight := Costed.tabulate n (fun v => (if mask.1[v.val] then [] else s.weight[v.val], 3))
  ({s with weight := weight.1}, mask.2 + weight.2 + 1)

theorem normalize_nonroot (s : Input n k) (v : Fin n) (h : ¬RootSet (root s) v) :
    weights (normalize s).1 v = weights s v := by
  have no : (rootMask s.roots).1[v.val] = false :=
    Bool.eq_false_iff.mpr (fun h' => h ((rootMask_correct s.roots v).mp h'))
  simp only [weights, normalize, Costed.tabulate_value, no, Bool.false_eq_true, ↓reduceIte]

theorem normalize_zero (s : Input n k) (i : Fin k) : weights (normalize s).1 (root s i) = 0 := by
  have yes := (rootMask_correct s.roots (root s i)).mpr ⟨i, rfl⟩
  simp only [weights, normalize, Costed.tabulate_value, yes, ↓reduceIte, Binary.value]

theorem normalize_bounds (s : Input n k) (B : Nat) (h : Bounded s B) : Bounded (normalize s).1 B := by
  refine ⟨?_, h.2⟩
  intro v
  simp only [normalize, Costed.tabulate_value]
  split
  · simp
  · exact h.1 v

theorem normalize_cost (s : Input n k) :
    (normalize s).2 ≤ rootMaskBudget n k + 2 * n * n + 9 * n + 4 := by
  have hm := rootMask_cost s.roots
  have hw := Costed.tabulate_cost n (fun v => (if (rootMask s.roots).1[v.val] then [] else s.weight[v.val], 3)) 3
    (by intros; rfl)
  dsimp only [normalize]
  norm_num only at hw
  simp only [Nat.mul_comm n 9] at hw
  omega

end GyoriLovasz.WordInstance
