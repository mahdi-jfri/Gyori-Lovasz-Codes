import GyoriLovasz.RuntimeScaling
import Mathlib.Data.Nat.Size

namespace GyoriLovasz.Flow

def PotentialBound (s : ScalingState n m) (P : Nat) : Prop :=
  ∀ v : Fin n, -(P : Int) ≤ s.potential[v.val] ∧ s.potential[v.val] ≤ (P : Int)

theorem applyOp_potential_bound (G : Network n m) (s : ScalingState n m)
    (C P : Nat) (cost : ∀ e, -(C : Int) ≤ G.cost e ∧ G.cost e ≤ (C : Int))
    (bound : PotentialBound s P) (op : ScalingOp m) :
    PotentialBound (applyOp G s op) (C + 3 * P) := by
  cases op with
  | double =>
    intro v
    have old := bound v
    change -((C + 3 * P : Nat) : Int) ≤ s.potential[v.val] ∧
      s.potential[v.val] ≤ ((C + 3 * P : Nat) : Int)
    constructor <;> omega
  | increment a =>
    exact repairStep_potential_bound (stateNetwork G s) (fun e => s.flow[e.val])
      (fun v => s.potential[v.val]) a C P cost bound

theorem execute_potential_bound (G : Network n m) (ops : List (ScalingOp m))
    (s : ScalingState n m) (C P : Nat)
    (cost : ∀ e, -(C : Int) ≤ G.cost e ∧ G.cost e ≤ (C : Int))
    (bound : PotentialBound s P) :
    PotentialBound (execute G ops s) ((P + C) * 4 ^ ops.length) := by
  induction ops generalizing s P with
  | nil =>
    intro v
    have old := bound v
    simp only [execute, List.length_nil, pow_zero, mul_one]
    constructor <;> omega
  | cons op ops ih =>
    have next := ih (applyOp G s op) (C + 3 * P) (applyOp_potential_bound G s C P cost bound op)
    have scale : ((C + 3 * P) + C) * 4 ^ ops.length ≤ (P + C) * 4 ^ (op :: ops).length := by
      calc
        _ ≤ (4 * (P + C)) * 4 ^ ops.length := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by simp only [List.length_cons, pow_succ]; ring
    intro v
    have nv := next v
    change -(((P + C) * 4 ^ (op :: ops).length : Nat) : Int) ≤
        (execute G ops (applyOp G s op)).potential[v.val] ∧
      (execute G ops (applyOp G s op)).potential[v.val] ≤
        (((P + C) * 4 ^ (op :: ops).length : Nat) : Int)
    constructor <;> omega

theorem zeroState_potential_bound (n m : Nat) : PotentialBound (zeroState n m) 0 := by
  simp [PotentialBound, zeroState]

/-- Applies to every prefix of the actual binary-scaling program, so this
controls intermediate states as well as the solver's final answer. -/
theorem prefix_potential_bound (G : Network n m) (columns : List (Vector Bool m))
    (preOps : List (ScalingOp m)) (isPrefix : preOps.IsPrefix (compileBits columns))
    (C : Nat) (cost : ∀ e, -(C : Int) ≤ G.cost e ∧ G.cost e ≤ (C : Int)) :
    PotentialBound (execute G preOps (zeroState n m))
      (C * 4 ^ ((m + 1) * columns.length)) := by
  have bound := execute_potential_bound G preOps (zeroState n m) C 0 cost (zeroState_potential_bound n m)
  have len : preOps.length ≤ (m + 1) * columns.length :=
    isPrefix.length_le.trans (compileBits_length columns)
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ 4) len
  have scale := Nat.mul_le_mul_left C power
  intro v
  have bv := bound v
  simp only [zero_add] at bv
  constructor <;> omega

theorem natAbs_le_of_bounds {x : Int} {P : Nat} (h : -(P : Int) ≤ x ∧ x ≤ (P : Int)) :
    x.natAbs ≤ P := by
  cases x with
  | ofNat a => simpa using h.2
  | negSucc a => simp_all; omega

/-- If costs have magnitude at most 2^L, every stored potential magnitude has
at most L + 2*(m+1)*B + 1 binary digits. A separate sign bit suffices. -/
theorem prefix_potential_bits (G : Network n m) (columns : List (Vector Bool m))
    (preOps : List (ScalingOp m)) (isPrefix : preOps.IsPrefix (compileBits columns))
    (L : Nat) (cost : ∀ e, -((2 ^ L : Nat) : Int) ≤ G.cost e ∧ G.cost e ≤ ((2 ^ L : Nat) : Int))
    (v : Fin n) :
    ((execute G preOps (zeroState n m)).potential[v.val]).natAbs.size ≤
      L + 2 * ((m + 1) * columns.length) + 1 := by
  have bound := natAbs_le_of_bounds (prefix_potential_bound G columns preOps isPrefix (2 ^ L) cost v)
  have powers : 2 ^ L * 4 ^ ((m + 1) * columns.length) =
      2 ^ (L + 2 * ((m + 1) * columns.length)) := by
    rw [pow_add]
    exact congrArg (fun x => 2 ^ L * x) (pow_mul (2 : Nat) 2 ((m + 1) * columns.length)).symm
  rw [powers] at bound
  apply Nat.size_le.mpr
  have positive : 0 < 2 ^ (L + 2 * ((m + 1) * columns.length)) := pow_pos (by decide) _
  rw [pow_succ]
  omega

theorem capacityProgram_ge (ops : List (ScalingOp m)) (capacity : Fin m → Nat) (e : Fin m) :
    capacity e ≤ capacityProgram ops capacity e := by
  induction ops generalizing capacity with
  | nil => exact le_rfl
  | cons op ops ih =>
    have next := ih (capacityOp capacity op)
    have step : capacity e ≤ capacityOp capacity op e := by
      cases op with
      | double => simp [capacityOp]; omega
      | increment a => simp only [capacityOp]; split <;> omega
    exact step.trans next

theorem binaryCapacity_lt (columns : List (Vector Bool m)) (capacity : Fin m → Nat)
    (L : Nat) (bound : ∀ e, capacity e < 2 ^ L) :
    ∀ e, binaryCapacity columns capacity e < 2 ^ (L + columns.length) := by
  induction columns generalizing L capacity with
  | nil => simpa [binaryCapacity] using bound
  | cons bits columns ih =>
    have next : ∀ e, 2 * capacity e + (if bits[e.val] then 1 else 0) < 2 ^ (L + 1) := by
      intro e
      have old := bound e
      rw [pow_succ]
      split <;> omega
    have result := ih (fun e => 2 * capacity e + if bits[e.val] then 1 else 0) (L + 1) next
    simpa only [binaryCapacity, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

theorem prefix_capacity_lt (G : Network n m) (columns : List (Vector Bool m))
    (preOps : List (ScalingOp m)) (isPrefix : preOps.IsPrefix (compileBits columns))
    (e : Fin m) :
    (execute G preOps (zeroState n m)).capacities[e.val] < 2 ^ columns.length := by
  have final := binaryCapacity_lt columns (fun _ => 0) 0 (by intro e; simp)
  have eq := congrFun (execute_capacity G preOps (zeroState n m)) e
  simp only [zeroState, Vector.getElem_replicate] at eq
  obtain ⟨suffix, hs⟩ := isPrefix
  have below := capacityProgram_ge suffix (capacityProgram preOps (fun _ => 0)) e
  have target : capacityProgram suffix (capacityProgram preOps (fun _ => 0)) e =
      binaryCapacity columns (fun _ => 0) e := by
    rw [← capacityProgram_append, hs, compileBits_capacity]
  rw [target] at below
  change (execute G preOps (zeroState n m)).capacities[e.val] =
    capacityProgram preOps (fun _ => 0) e at eq
  rw [eq]
  exact below.trans_lt (by simpa using final e)

theorem prefix_capacity_bits (G : Network n m) (columns : List (Vector Bool m))
    (preOps : List (ScalingOp m)) (isPrefix : preOps.IsPrefix (compileBits columns))
    (e : Fin m) :
    ((execute G preOps (zeroState n m)).capacities[e.val]).size ≤ columns.length :=
  Nat.size_le.mpr (prefix_capacity_lt G columns preOps isPrefix e)

theorem prefix_flow_bits (G : Network n m) (columns : List (Vector Bool m))
    (preOps : List (ScalingOp m)) (isPrefix : preOps.IsPrefix (compileBits columns))
    (e : Fin m) :
    ((execute G preOps (zeroState n m)).flow[e.val]).size ≤ columns.length := by
  have inv := execute_invariant preOps (zeroState_invariant G)
  have upper := inv.1.1 e
  apply Nat.size_le.mpr
  exact upper.trans_lt (prefix_capacity_lt G columns preOps isPrefix e)

theorem reducedCost_bounds (G : Network n m) (potential : Fin n → Int) (C P : Nat)
    (cost : ∀ e, -(C : Int) ≤ G.cost e ∧ G.cost e ≤ (C : Int))
    (bound : ∀ v, -(P : Int) ≤ potential v ∧ potential v ≤ (P : Int)) (e : Fin m) :
    -((C + 2 * P : Nat) : Int) ≤ reducedCost G potential e ∧
      reducedCost G potential e ≤ ((C + 2 * P : Nat) : Int) := by
  have ec := cost e
  have ht := bound (G.tail e)
  have hh := bound (G.head e)
  unfold reducedCost
  constructor <;> omega

theorem residualCost_bound (G : Network n m) (f : Fin m → Nat)
    (potential : Fin n → Int) (C P : Nat)
    (cost : ∀ e, -(C : Int) ≤ G.cost e ∧ G.cost e ≤ (C : Int))
    (bound : ∀ v, -(P : Int) ≤ potential v ∧ potential v ≤ (P : Int)) (u v : Fin n) :
    residualCost G f potential u v ≤ C + 2 * P := by
  unfold residualCost
  split
  · omega
  · rename_i a chosen
    have rc := reducedCost_bounds G potential C P cost bound a.1
    unfold arcCost
    split <;> apply Int.toNat_le.mpr <;> omega

/-- Every tentative distance table and every relaxation candidate within a
repair stays bounded. This includes intermediate Dijkstra rounds. -/
theorem repair_distance_candidate_bound (G : Network n m) (f : Fin m → Nat)
    (potential : Fin n → Int) (C P : Nat)
    (cost : ∀ e, -(C : Int) ≤ G.cost e ∧ G.cost e ≤ (C : Int))
    (bound : ∀ v, -(P : Int) ≤ potential v ∧ potential v ≤ (P : Int))
    (a : Fin m) (fuel : Nat) (u v : Fin n) :
    let table := ShortestPaths.run (residualEdges G f potential) (residualCost G f potential) fuel
      (ShortestPaths.initialState (G.head a) (-reducedCost G potential a).toNat)
    ShortestPaths.get table u + residualCost G f potential u v ≤ 2 * (C + 2 * P) := by
  have rc := reducedCost_bounds G potential C P cost bound a
  have dc := residualCost_bound G f potential C P cost bound u v
  have inv := ShortestPaths.run_invariant fuel (ShortestPaths.initialState_invariant
    (residualEdges G f potential) (residualCost G f potential) (G.head a)
      (-reducedCost G potential a).toNat)
  have du := inv.2.1 u
  have truncation : (-reducedCost G potential a).toNat ≤ C + 2 * P := by omega
  omega

theorem repair_distance_candidate_bits (G : Network n m) (f : Fin m → Nat)
    (potential : Fin n → Int) (Q : Nat)
    (cost : ∀ e, -((2 ^ Q : Nat) : Int) ≤ G.cost e ∧ G.cost e ≤ ((2 ^ Q : Nat) : Int))
    (bound : ∀ v, -((2 ^ Q : Nat) : Int) ≤ potential v ∧ potential v ≤ ((2 ^ Q : Nat) : Int))
    (a : Fin m) (fuel : Nat) (u v : Fin n) :
    let table := ShortestPaths.run (residualEdges G f potential) (residualCost G f potential) fuel
      (ShortestPaths.initialState (G.head a) (-reducedCost G potential a).toNat)
    (ShortestPaths.get table u + residualCost G f potential u v).size ≤ Q + 3 := by
  have le := repair_distance_candidate_bound G f potential (2 ^ Q) (2 ^ Q) cost bound a fuel u v
  apply Nat.size_le.mpr
  have positive : 0 < 2 ^ Q := pow_pos (by decide) _
  rw [pow_add]
  norm_num only [pow_succ, pow_zero] at *
  omega

/-- The temporary arithmetic bound specialized to an actual intermediate
state of the binary solver, rather than an assumed potential certificate. -/
theorem prefix_repair_candidate_bits (G : Network n m) (columns : List (Vector Bool m))
    (preOps : List (ScalingOp m)) (isPrefix : preOps.IsPrefix (compileBits columns))
    (L : Nat) (cost : ∀ e, -((2 ^ L : Nat) : Int) ≤ G.cost e ∧ G.cost e ≤ ((2 ^ L : Nat) : Int))
    (a : Fin m) (fuel : Nat) (u v : Fin n) :
    let s := execute G preOps (zeroState n m)
    let N := stateNetwork G s
    let f := fun e : Fin m => s.flow[e.val]
    let π := fun x : Fin n => s.potential[x.val]
    let table := ShortestPaths.run (residualEdges N f π) (residualCost N f π) fuel
      (ShortestPaths.initialState (N.head a) (-reducedCost N π a).toNat)
    (ShortestPaths.get table u + residualCost N f π u v).size ≤
      L + 2 * ((m + 1) * columns.length) + 3 := by
  let s := execute G preOps (zeroState n m)
  let Q := L + 2 * ((m + 1) * columns.length)
  have powers : 2 ^ L * 4 ^ ((m + 1) * columns.length) = 2 ^ Q := by
    dsimp [Q]
    rw [pow_add]
    exact congrArg (fun x => 2 ^ L * x) (pow_mul (2 : Nat) 2 ((m + 1) * columns.length)).symm
  have potential : PotentialBound s (2 ^ Q) := by
    have h := prefix_potential_bound G columns preOps isPrefix (2 ^ L) cost
    rwa [powers] at h
  have larger : 2 ^ L ≤ 2 ^ Q := Nat.pow_le_pow_right (by decide) (by dsimp [Q]; omega)
  have costs : ∀ e, -((2 ^ Q : Nat) : Int) ≤ (stateNetwork G s).cost e ∧
      (stateNetwork G s).cost e ≤ ((2 ^ Q : Nat) : Int) := by
    intro e
    have old := cost e
    change -((2 ^ Q : Nat) : Int) ≤ G.cost e ∧ G.cost e ≤ ((2 ^ Q : Nat) : Int)
    constructor <;> omega
  exact repair_distance_candidate_bits (stateNetwork G s) (fun e => s.flow[e.val])
    (fun x => s.potential[x.val]) Q costs potential a fuel u v

end GyoriLovasz.Flow
