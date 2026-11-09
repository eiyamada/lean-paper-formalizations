import PropertiesOfPALAndBPALOperators
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Audit all declarations in the paper namespace and their transitive dependencies. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names ← env.constants.foldM (init := #[]) fun names n _ => do
    if (`PropertiesOfPALAndBPALOperators).isPrefixOf n then
      return names.push n
    return names
  if names.isEmpty then
    throwError "No declarations from the paper were imported"
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for ax in state.axioms do
    unless allowed.contains ax do
      throwError "Unexpected axiom in paper development: {ax}"
  logInfo m!"Audited {names.size} declarations. Axioms: {state.axioms}"
