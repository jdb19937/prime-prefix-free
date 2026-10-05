import Lean
/-!
Independent kernel re-check of the main theorem: collect the transitive closure of
`ppf_hasSum_of_RH` (every constant used in any type or value, plus the full
mutual block and constructors of every inductive) and replay it, with the kernel,
into an empty environment. Run: `lake env lean --run scripts/ReplayClosure.lean`.
-/
open Lean

def collect (env : Environment) (root : Name) : IO (Std.HashMap Name ConstantInfo) := do
  let mut todo : Array Name := #[root]
  let mut out : Std.HashMap Name ConstantInfo := {}
  while 0 < todo.size do
    let n := todo.back!
    todo := todo.pop
    if out.contains n then continue
    let some ci := env.find? n | throw (IO.userError s!"missing constant {n}")
    out := out.insert n ci
    todo := todo ++ ci.getUsedConstantsAsSet.toArray
    match ci with
    | .inductInfo v => todo := todo ++ v.all.toArray ++ v.ctors.toArray
    | .ctorInfo v => todo := todo.push v.induct
    | .recInfo v => todo := todo ++ v.all.toArray
    | _ => pure ()
  return out

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  Lean.withImportModules #[{module := `PPF}] {} fun env => do
    let consts ← collect env `ppf_hasSum_of_RH
    let axs := consts.fold (init := #[]) fun acc n ci =>
      match ci with | .axiomInfo _ => acc.push n | _ => acc
    IO.println s!"closure: {consts.size} constants; axioms in closure: {axs}"
    let t0 ← IO.monoMsNow
    let env' ← (← mkEmptyEnvironment).replay consts
    let t1 ← IO.monoMsNow
    let kenv := env'.toKernelEnv
    let replayedAll := consts.fold (init := true) fun ok n ci =>
      ok && (ci.isUnsafe || ci.isPartial || (kenv.find? n).isSome)
    let roots := #[`ppf_hasSum_of_RH]
    let sameType := roots.all fun root => match kenv.find? root, env.find? root with
      | some a, some b => a.type == b.type
      | _, _ => false
    IO.println s!"kernel replay OK in {(t1 - t0) / 1000}s"
    IO.println s!"roots in kernel env: {roots.all (kenv.find? · |>.isSome)}; same types as elaborated: {sameType}"
    IO.println s!"every closure constant present in kernel env: {replayedAll}"
    let stdAxioms := #[``Classical.choice, ``propext, ``Quot.sound]
    unless roots.all (kenv.find? · |>.isSome) && sameType && replayedAll
        && axs.all (stdAxioms.contains ·) do
      throw <| IO.userError "kernel replay check FAILED"
