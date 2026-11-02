import GyoriLovasz
import Lean.Util.CollectAxioms

/-!
Audit every safe project declaration and its transitive dependencies. Reject proof
placeholders (`sorryAx`) and any axiom beyond Lean's usual classical foundations.
Compiler-generated unsafe implementations are not logical declarations.
This file is part of the default Lake build.
-/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.filter fun (name, info) =>
    let text := name.toString
    (text.startsWith "GyoriLovasz." || text.startsWith "_private.GyoriLovasz.") &&
      !info.isUnsafe && !info.isPartial
  let (_, audit) := ((do
    for (name, _) in declarations do
      Lean.CollectAxioms.collect name).run env).run {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in audit.axioms do
    unless allowed.contains axiomName do
      throwError "Unexpected axiom in the formalization: {axiomName}"
  logInfo m!"Axiom audit passed for {declarations.length} project declarations: {audit.axioms.toList}"

#print axioms GyoriLovasz.gyori_lovasz
#print axioms GyoriLovasz.feasible_partition
#print axioms GyoriLovasz.generalized_weighted_gyori_lovasz
#print axioms GyoriLovasz.WordInstance.unweighted_polynomial_time
#print axioms GyoriLovasz.WordInstance.generalized_weighted_input_polynomial_time
#print axioms GyoriLovasz.WordInstance.weighted_input_polynomial_time
