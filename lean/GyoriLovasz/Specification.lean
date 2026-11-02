import GyoriLovasz.Potential

/-!
The original target is stated here as a proposition. Its proof is
`GyoriLovasz.gyori_lovasz` in `GyoriLovasz/Main.lean`.
-/
namespace GyoriLovasz

inductive ReachWithin (E : α → α → Prop) (allowed : α → Prop) : α → α → Prop where
  | refl (x : α) (hx : allowed x) : ReachWithin E allowed x x
  | step {x y z : α} (hx : allowed x) (edge : E x y)
      (rest : ReachWithin E allowed y z) : ReachWithin E allowed x z

def IsSimpleUndirected (E : Fin n → Fin n → Prop) : Prop :=
  (∀ x, ¬E x x) ∧ (∀ x y, E x y → E y x)

/-- Standard vertex connectivity convention: a k-connected graph has > k vertices. -/
def KConnected (E : Fin n → Fin n → Prop) (k : Nat) : Prop :=
  k < n ∧ ∀ deleted : List (Fin n), deleted.Nodup → deleted.length < k →
    ∀ x y, x ∉ deleted → y ∉ deleted →
      ReachWithin E (fun z => z ∉ deleted) x y

def PrescribedPartition (E : Fin n → Fin n → Prop)
    (roots : Fin k → Fin n) (sizes : Fin k → Nat) : Prop :=
  ∃ label : Fin n → Fin k,
    (∀ i, label (roots i) = i) ∧
    (∀ i, countTrue (List.finRange n) (fun x => label x = i) = sizes i) ∧
    (∀ i x, label x = i → ReachWithin E (fun y => label y = i) x (roots i))

/-- The target proposition, proved by `gyori_lovasz` in `Main.lean`.
No time-complexity claim is encoded in this existential statement. -/
def MainTheoremStatement : Prop :=
  ∀ (n k : Nat) (E : Fin n → Fin n → Prop)
    (roots : Fin k → Fin n) (sizes : Fin k → Nat),
    0 < k → IsSimpleUndirected E → KConnected E k →
    (∀ i j, roots i = roots j → i = j) →
    (∀ i, 0 < sizes i) → ((List.finRange k).map sizes).sum = n →
    PrescribedPartition E roots sizes

end GyoriLovasz
