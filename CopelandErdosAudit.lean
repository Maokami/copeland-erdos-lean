module

public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

import all CopelandErdos
import all CopelandErdos.Analysis.GeometricBounds
import all CopelandErdos.Digits.BlockStream
import all CopelandErdos.Digits.NatWord
import all CopelandErdos.Digits.PrimeStream
import all CopelandErdos.Digits.RealExpansion
import all CopelandErdos.Normality.BoundaryCriterion
import all CopelandErdos.Normality.NormalDigits
import all CopelandErdos.Normality.PrefixTransfer
import all CopelandErdos.Normality.PrimeConcatenation
import all CopelandErdos.Normality.RealBridge
import all CopelandErdos.NumberTheory.BadIntegerCounting
import all CopelandErdos.NumberTheory.BadIntegers
import all CopelandErdos.NumberTheory.BadPrimeMass
import all CopelandErdos.NumberTheory.PrimeBounds
import all CopelandErdos.NumberTheory.PrimeDigitMass
import all CopelandErdos.NumberTheory.PrimePrefixBounds
import all CopelandErdos.Probability.FiniteMoments
import all CopelandErdos.Words.BadWordArithmetic
import all CopelandErdos.Words.BadWords
import all CopelandErdos.Words.BlockCounts
import all CopelandErdos.Words.Concatenation
import all CopelandErdos.Words.Occurrences
import all CopelandErdos.Words.UniformBlocks

/-!
# Axiom audit

Inspect every declaration, including private helpers, in all imported `CopelandErdos` modules.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The source inventory check in
`scripts/check_lean_inventory.py` verifies both the root imports and these direct `import all`
declarations. Direct imports are needed because ordinary imports do not expose private declarations
in Lean's module system.
-/

meta section

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
