import CopelandErdos

/-!
# Axiom audit

Inspect every declaration in all imported `CopelandErdos` modules. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. The source inventory check in
`scripts/check_lean_inventory.py` separately verifies that the root imports every library file.
-/

open Lean Elab Command

/-- Reject nonstandard axioms in every imported project declaration. -/
elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut mods : Nat := 0
  let mut decls : Nat := 0
  let mut used : NameSet := {}
  let mut bad : Array MessageData := #[]
  for i in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]!
    unless (`CopelandErdos).isPrefixOf mod do continue
    mods := mods + 1
    for c in env.header.moduleData[i]!.constNames do
      decls := decls + 1
      let axs ← collectAxioms c
      used := axs.foldl NameSet.insert used
      let extra := axs.filter (· ∉ allowed)
      unless extra.isEmpty do
        bad := bad.push m!"{c} ({mod}): {extra.toList}"
  if mods == 0 then
    throwError "Axiom audit: no CopelandErdos module was imported"
  unless bad.isEmpty do
    throwError m!"Axiom audit failed: {bad.size} declarations use nonstandard axioms\
      {indentD (MessageData.joinSep bad.toList Format.line)}"
  logInfo m!"Axiom audit passed: {mods} modules, {decls} declarations; axioms: {used.toList}"

#audit_axioms
