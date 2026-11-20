import Lean
import Rand

/-!
# Axiom audit

Every theorem in `published` may depend only on `propext`, `Classical.choice`
and `Quot.sound`. `scripts/audit.sh` runs this file and fails on any other axiom
(which also catches `native_decide`, via `Lean.ofReduceBool`).
-/

open Lean Elab Command

/-- The published theorems (listed in `PROVEN.md`). Empty until Task 5 onward. -/
def published : List Name := []

def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let mut bad := false
  for n in published do
    let axs ← liftCoreM <| collectAxioms n
    let extra := axs.filter (fun a => !allowedAxioms.contains a)
    logInfo m!"{n}: {axs.toList}"
    if !extra.isEmpty then
      bad := true
      logError m!"{n} depends on disallowed axioms: {extra.toList}"
  if !bad then logInfo m!"audit ok: {published.length} theorem(s)"
