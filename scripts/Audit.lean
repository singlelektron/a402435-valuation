import Lean.Util.CollectAxioms
import Lean.Elab.Command
import MathMiner

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless `MathMiner |>.isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    let axioms ← collectAxioms name
    let rejected := axioms.filter (!permitted.contains ·)
    unless rejected.isEmpty do
      throwError "{name} depends on unapproved axioms: {rejected}"
    checked := checked + 1
  if checked == 0 then throwError "No project declarations found"
  logInfo m!"Checked axiom dependencies of {checked} project declarations."

#check MathMiner.A402435.solution
#print axioms MathMiner.A402435.solution
