import GyoriLovasz.RuntimeRepair

namespace GyoriLovasz.Flow

structure ScalingState (n m : Nat) where
  capacities : Vector Nat m
  flow : Vector Nat m
  potential : Vector Int n

def stateNetwork (G : Network n m) (s : ScalingState n m) : Network n m :=
  { G with capacity := fun e => s.capacities[e.val] }

def ScalingInvariant (G : Network n m) (s : ScalingState n m) : Prop :=
  Feasible (stateNetwork G s) (fun e => s.flow[e.val]) ∧
    DualFeasible (stateNetwork G s) (fun e => s.flow[e.val]) (fun v => s.potential[v.val])

def zeroState (n m : Nat) : ScalingState n m :=
  ⟨Vector.replicate m 0, Vector.replicate m 0, Vector.replicate n 0⟩

def doubleState (s : ScalingState n m) : ScalingState n m :=
  ⟨Vector.ofFn (fun e => 2 * s.capacities[e.val]),
    Vector.ofFn (fun e => 2 * s.flow[e.val]), s.potential⟩

def incrementState (G : Network n m) (s : ScalingState n m) (a : Fin m) : ScalingState n m :=
  let repaired := repairStep (stateNetwork G s) (fun e => s.flow[e.val])
    (fun v => s.potential[v.val]) a
  ⟨Vector.ofFn (fun e => if e = a then s.capacities[e.val] + 1 else s.capacities[e.val]),
    repaired.1, repaired.2⟩

theorem zeroState_invariant (G : Network n m) : ScalingInvariant G (zeroState n m) := by
  simp [ScalingInvariant, zeroState, stateNetwork, Feasible, DualFeasible]

theorem doubleState_invariant {G : Network n m} {s : ScalingState n m}
    (inv : ScalingInvariant G s) : ScalingInvariant G (doubleState s) := by
  have hf := double_feasible inv.1
  have hd := double_dual inv.2
  simpa [ScalingInvariant, doubleState, stateNetwork, doubleCapacity, doubleFlow,
    Feasible, DualFeasible, reducedCost] using And.intro hf hd

theorem incrementState_invariant {G : Network n m} {s : ScalingState n m}
    (inv : ScalingInvariant G s) (a : Fin m) : ScalingInvariant G (incrementState G s a) := by
  have correct := repairStep_correct inv.1 inv.2 a
  simpa [ScalingInvariant, incrementState, stateNetwork, incrementCapacity,
    Feasible, DualFeasible, reducedCost] using correct

inductive ScalingOp (m : Nat) where
  | double : ScalingOp m
  | increment : Fin m → ScalingOp m

def applyOp (G : Network n m) (s : ScalingState n m) : ScalingOp m → ScalingState n m
  | .double => doubleState s
  | .increment a => incrementState G s a

def execute (G : Network n m) : List (ScalingOp m) → ScalingState n m → ScalingState n m
  | [], s => s
  | op :: ops, s => execute G ops (applyOp G s op)

def capacityOp (capacity : Fin m → Nat) : ScalingOp m → Fin m → Nat
  | .double => fun e => 2 * capacity e
  | .increment a => fun e => if e = a then capacity e + 1 else capacity e

def capacityProgram : List (ScalingOp m) → (Fin m → Nat) → Fin m → Nat
  | [], capacity => capacity
  | op :: ops, capacity => capacityProgram ops (capacityOp capacity op)

theorem applyOp_invariant {G : Network n m} {s : ScalingState n m}
    (inv : ScalingInvariant G s) (op : ScalingOp m) : ScalingInvariant G (applyOp G s op) := by
  cases op with
  | double => exact doubleState_invariant inv
  | increment a => exact incrementState_invariant inv a

theorem execute_invariant {G : Network n m} (ops : List (ScalingOp m))
    {s : ScalingState n m} (inv : ScalingInvariant G s) : ScalingInvariant G (execute G ops s) := by
  induction ops generalizing s with
  | nil => exact inv
  | cons op ops ih => exact ih (applyOp_invariant inv op)

theorem applyOp_capacity (G : Network n m) (s : ScalingState n m) (op : ScalingOp m) :
    (fun e : Fin m => (applyOp G s op).capacities[e.val]) =
      capacityOp (fun e => s.capacities[e.val]) op := by
  cases op <;> funext e <;> simp [applyOp, capacityOp, doubleState, incrementState]

theorem execute_capacity (G : Network n m) (ops : List (ScalingOp m)) (s : ScalingState n m) :
    (fun e : Fin m => (execute G ops s).capacities[e.val]) =
      capacityProgram ops (fun e => s.capacities[e.val]) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    simp only [execute, capacityProgram, ih, applyOp_capacity]

/-- Complete executable minimum-cost circulation solver for capacities given
as a scaling program. This is a correctness theorem, not yet a bit-cost theorem. -/
theorem execute_optimal (G : Network n m) (ops : List (ScalingOp m)) :
    let output := execute G ops (zeroState n m)
    let target := { G with capacity := capacityProgram ops (fun _ => 0) }
    Feasible target (fun e => output.flow[e.val]) ∧
      ∀ other, Feasible target other →
        totalCost target (fun e => output.flow[e.val]) ≤ totalCost target other := by
  have inv := execute_invariant ops (zeroState_invariant G)
  have caps := execute_capacity G ops (zeroState n m)
  simp only [zeroState, Vector.getElem_replicate] at caps
  have net : stateNetwork G (execute G ops (zeroState n m)) =
      { G with capacity := capacityProgram ops (fun _ => 0) } := by
    simpa only [stateNetwork, zeroState] using
      congrArg (fun c => { G with capacity := c }) caps
  unfold ScalingInvariant at inv
  rw [net] at inv
  exact ⟨inv.1, dual_optimal inv.1 inv.2⟩

/-- One binary digit column: double once, then increment each arc whose bit is one. -/
def bitColumn (bits : Vector Bool m) : List (ScalingOp m) :=
  .double :: (((List.finRange m).filter (fun e => bits[e.val])).map ScalingOp.increment)

def compileBits (columns : List (Vector Bool m)) : List (ScalingOp m) :=
  columns.flatMap bitColumn

theorem bitColumn_length (bits : Vector Bool m) : (bitColumn bits).length ≤ m + 1 := by
  have le := List.length_filter_le (fun e : Fin m => bits[e.val]) (List.finRange m)
  simpa [bitColumn] using Nat.add_le_add_right le 1

/-- Binary scaling uses at most (m+1) operations per input bit column; each
operation is an implemented doubling or repair, with no flow oracle. Costs
inside those operations still need their separate bit-operation analysis. -/
theorem compileBits_length (columns : List (Vector Bool m)) :
    (compileBits columns).length ≤ (m + 1) * columns.length := by
  induction columns with
  | nil => simp [compileBits]
  | cons bits columns ih =>
    have le := bitColumn_length bits
    simp only [compileBits, List.flatMap_cons, List.length_append, List.length_cons] at *
    calc
      _ ≤ (m + 1) + (m + 1) * columns.length := Nat.add_le_add le ih
      _ = _ := by ring

theorem capacityProgram_append (xs ys : List (ScalingOp m)) (capacity : Fin m → Nat) :
    capacityProgram (xs ++ ys) capacity = capacityProgram ys (capacityProgram xs capacity) := by
  induction xs generalizing capacity with
  | nil => rfl
  | cons op xs ih => exact ih (capacityOp capacity op)

theorem increments_capacity (xs : List (Fin m)) (capacity : Fin m → Nat) (e : Fin m) :
    capacityProgram (xs.map ScalingOp.increment) capacity e = capacity e + xs.count e := by
  induction xs generalizing capacity with
  | nil => simp [capacityProgram]
  | cons a xs ih =>
    simp only [List.map_cons, capacityProgram, ih, capacityOp]
    by_cases eq : a = e
    · subst a
      simp [List.count_cons]
      omega
    · simp [List.count_cons, eq, Ne.symm eq]

theorem bitColumn_capacity (bits : Vector Bool m) (capacity : Fin m → Nat) (e : Fin m) :
    capacityProgram (bitColumn bits) capacity e = 2 * capacity e + if bits[e.val] then 1 else 0 := by
  simp only [bitColumn, capacityProgram, increments_capacity, capacityOp]
  have simple := (List.nodup_finRange m).filter (fun e => bits[e.val])
  have count := List.count_eq_of_nodup (a := e) simple
  simpa [mem_finRange] using congrArg (fun c => 2 * capacity e + c) count

/-- Numeric value of most-significant-bit-first columns, with an initial prefix. -/
def binaryCapacity : List (Vector Bool m) → (Fin m → Nat) → Fin m → Nat
  | [], capacity => capacity
  | bits :: rest, capacity => binaryCapacity rest (fun e => 2 * capacity e + if bits[e.val] then 1 else 0)

theorem compileBits_capacity (columns : List (Vector Bool m)) (capacity : Fin m → Nat) :
    capacityProgram (compileBits columns) capacity = binaryCapacity columns capacity := by
  induction columns generalizing capacity with
  | nil => rfl
  | cons bits columns ih =>
    simp only [compileBits, List.flatMap_cons, capacityProgram_append, binaryCapacity]
    simp only [compileBits] at ih
    rw [ih]
    exact congrArg (binaryCapacity columns) (funext (bitColumn_capacity bits capacity))

def solveBinary (G : Network n m) (columns : List (Vector Bool m)) : ScalingState n m :=
  execute G (compileBits columns) (zeroState n m)

theorem solveBinary_optimal (G : Network n m) (columns : List (Vector Bool m)) :
    let output := solveBinary G columns
    let target := { G with capacity := binaryCapacity columns (fun _ => 0) }
    Feasible target (fun e => output.flow[e.val]) ∧
      ∀ other, Feasible target other →
        totalCost target (fun e => output.flow[e.val]) ≤ totalCost target other := by
  simpa only [compileBits_capacity, solveBinary] using execute_optimal G (compileBits columns)

end GyoriLovasz.Flow
