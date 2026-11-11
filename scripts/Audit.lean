/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import Quadrature
import CCLib
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Every theorem defined in a module of `Quadrature` or `CCLib`, private ones included, may depend
only on `propext`, `Classical.choice` and `Quot.sound`, and neither library may declare an axiom.
Declarations are selected by their defining module, not by their namespace. The audit prints the
`Quadrature` modules it saw, so that `check-lean.py` can compare them with the source files, and
the number of theorems of each library.

`scripts/check-lean.py` runs this file after `lake build`.
-/

-- Read `cosine.c` again, so that a stale build of the module that includes it fails here.
example : Quadrature.CSource.Cosine.source =
    (include_str "../Quadrature/CSource/Cosine/cosine.c").toList := by
  decide +kernel

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let library (module : String) : Option String :=
    #["Quadrature", "CCLib"].find? fun root => module == root || module.startsWith (root ++ ".")
  let modules := env.header.moduleNames.filter fun name => library name.toString == "Quadrature"
  logInfo m!"Project modules: {(toJson (modules.map (·.toString))).compress}"
  let mut quadrature : Nat := 0
  let mut clean : Nat := 0
  for (name, info) in env.constants do
    let some index := env.getModuleIdxFor? name | continue
    let some root := library env.header.moduleNames[index.toNat]!.toString | continue
    if info.isAxiom then
      throwError m!"{root} declares the axiom {name}"
    if info.isTheorem then
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError m!"{name} depends on the axiom {axiomName}"
      if root == "Quadrature" then quadrature := quadrature + 1 else clean := clean + 1
  logInfo m!"Audited {quadrature} Quadrature theorems and {clean} CCLib theorems"
