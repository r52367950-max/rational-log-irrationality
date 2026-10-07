import Round2MainReference
import Lean
import Lean.Replay

/-!
An independent exact-type and transitive-axiom guard for the final theorem.
This checks no conditional theorem by silently applying additional arguments.
The command is accompanied by a separately compiled kernel certificate in the
verification script; it is not a claim of nanoda/exported-environment replay.
-/

set_option autoImplicit false

open Lean Elab Command

deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.ConstantInfo

private def builtinRoots : List Name :=
  [``Nat, ``String, ``String.mk, ``Char, ``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind,
    ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod,
    ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft,
    ``Nat.shiftRight, ``String.ofList, ``Char.ofNat, ``List, ``eagerReduce]

private def checkExactMain (n : Name) : CommandElabM Unit := do
  let ci ← getConstInfo n
  unless ci matches .thmInfo _ do
    throwError "The final target must be a theorem: {n}"
  let expected := mkConst ``RationalLogReview.MainReference.StrictRationalLogMain
  let equal ← liftTermElabM <| Meta.isDefEq ci.type expected
  unless equal do
    throwError "FINAL_TYPE_MISMATCH: {n}\nactual: {ci.type}\nexpected: {expected}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms n
  unless axioms.all (fun a => allowed.contains a) do
    throwError "FINAL_AXIOM_REJECTED: {n}: {axioms}"
  logInfo m!"FINAL_TYPE_MATCH {n}"
  logInfo m!"FINAL_TRANSITIVE_AXIOMS {n} {axioms}"

/-- Include mutual inductive blocks and constructors as well as term dependencies.
All constants are subsequently sent to the stock kernel in an empty environment. -/
private partial def constantClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) (constants : Std.HashMap Name ConstantInfo := {}) :
    Except String (Std.HashMap Name ConstantInfo) := do
  match todo with
  | [] => return constants
  | n :: ns =>
    if seen.contains n then return ← constantClosure env ns seen constants
    let some ci := env.find? n | throw s!"Replay dependency unavailable: {n}"
    if ci.isUnsafe || ci.isPartial then
      throw s!"Unsafe/partial replay dependency rejected: {n}"
    let extra := match ci with
      | .inductInfo info => info.all ++ info.ctors
      | .ctorInfo info => [info.induct]
      | .recInfo info => info.rules.map (·.ctor)
      | _ => []
    return ← constantClosure env (ci.getUsedConstantsAsSet.toList ++ extra ++ ns)
      (seen.insert n) (constants.insert n ci)

/-- Load the reference alone in a separate environment, without solution imports,
and compare every definition/proof/inductive used by its statement. -/
private def checkIndependentReference : CommandElabM Unit := do
  let solution ← getEnv
  let reference ← liftIO <| Lean.importModules #[{ module := `Round2MainReference }] {}
  let constants ← match constantClosure reference
      (``RationalLogReview.MainReference.StrictRationalLogMain :: builtinRoots) with
    | .ok m => pure m
    | .error e => throwError "REFERENCE_CLOSURE_FAILURE: {e}"
  for (n, expected) in constants.toList do
    let some actual := solution.find? n |
      throwError "REFERENCE_CONSTANT_MISSING_IN_SOLUTION: {n}"
    unless expected == actual do
      throwError "REFERENCE_CONSTANT_CHANGED_IN_SOLUTION: {n}"
  logInfo m!"INDEPENDENT_REFERENCE_GRAPH_MATCH {constants.size} constants"

/-- Same fresh-kernel replay operation used by the pinned Comparator's
`runBuiltinKernel`; this implementation reads the current imported environment,
and does not claim a sandboxed lean4export or a distinct external kernel. -/
private def replayTheorem (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  let ci ← getConstInfo n
  unless ci matches .thmInfo _ do
    throwError "Replay target must be a theorem: {n}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms n
  unless axioms.all (fun a => allowed.contains a) do
    throwError "REPLAY_AXIOM_REJECTED {n}: {axioms}"
  let roots := [n, ``RationalLogReview.MainReference.StrictRationalLogMain] ++ builtinRoots
  let original ← match constantClosure env roots with
    | .ok m => pure m
    | .error e => throwError "{e}"
  let quotTargets := [`Quot.mk, `Quot.lift, `Quot.ind]
  let constants := quotTargets.foldl (init := original) (·.erase ·)
  logInfo m!"FRESH_KERNEL_REPLAY_START {n} {constants.size} constants"
  let checked ← liftIO do
    let empty ← Lean.mkEmptyEnvironment
    empty.toKernelEnv.replay constants
  for primitive in `Quot :: quotTargets do
    let some expected := original[primitive]? |
      throwError "Quot primitive missing from input: {primitive}"
    let some actual := checked.find? primitive |
      throwError "Quot primitive missing after replay: {primitive}"
    unless expected == actual do
      throwError "Quot primitive mismatch after replay: {primitive}"
  logInfo m!"FRESH_KERNEL_REPLAY_ACCEPTED {n} {constants.size} constants"
  logInfo m!"REPLAY_TRANSITIVE_AXIOMS {n} {axioms}"

elab "#verify_rational_log_main " target:ident : command =>
  checkExactMain target.getId

elab "#replay_checked_theorem " target:ident : command =>
  replayTheorem target.getId

elab "#verify_and_replay_rational_log_main " target:ident : command => do
  checkIndependentReference
  checkExactMain target.getId
  replayTheorem target.getId
