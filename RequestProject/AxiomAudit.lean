import RequestProject.All

/-!
# Axiom audit

A semantic audit of the axioms used by every public theorem of the development:
for each theorem in the `KnotGame` namespace the axiom set is computed with the
same machinery that backs `#print axioms`, and the build fails if any axiom
outside `propext`, `Classical.choice`, `Quot.sound` occurs — in particular if
`sorryAx` occurs.  Nothing here inspects the *text* of the sources.
-/

namespace KnotGame.Audit

open Lean Elab Command

/-- The axioms the commission permits. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mut audited : Nat := 0
  let mut offenders : Array (Name × Array Name) := #[]
  for (nm, ci) in env.constants.toList do
    if (`KnotGame).isPrefixOf nm && !nm.isInternal then
      match ci with
      | .thmInfo _ =>
          let ax ← Lean.collectAxioms nm
          audited := audited + 1
          let bad := ax.filter (fun a => !(allowedAxioms.contains a))
          if !bad.isEmpty then
            offenders := offenders.push (nm, bad)
      | _ => pure ()
  if !offenders.isEmpty then
    throwError "axiom audit failed for {offenders.size} declaration(s): {offenders}"
  logInfo m!"axiom audit passed: {audited} theorems, axioms confined to {allowedAxioms}"

end KnotGame.Audit
