import EventualAndStrongEventualNotionsInPublicAnnouncements
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Run after `lake build`:

    lake env lean scripts/EventualAndStrongEventualNotionsInPublicAnnouncementsAxiomAudit.lean

Audit the transitive proof dependencies of every declaration in the paper's
namespace. Only Lean's standard logical axioms are allowed. A shared traversal
state avoids repeatedly walking the same imported proof dependencies.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names ← env.constants.foldM (init := #[]) fun names n _ => do
    if (`EventualAndStrongEventualNotionsInPublicAnnouncements).isPrefixOf n then
      return names.push n
    return names
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for ax in state.axioms do
    unless allowed.contains ax do
      throwError "Unexpected axiom in paper development: {ax}"
  logInfo m!"Audited {names.size} declarations. Axioms: {state.axioms}"
