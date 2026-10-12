import NaturalLatents
open Lean Meta

/-!
Dependency closure of the two headline theorems over this repository's modules.
Run from the repository root after `lake build`:

    lake env lean scripts/DeclClosure.lean

Writes `closure.decls.tsv` (name, module, first line, last line) and `closure.modules.tsv`
(module, declarations used, lines used) to the directory in `outDir`.
-/

/-- Transitive closure of the constants referenced by `roots`. -/
def closureOf (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while stack.size > 0 do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.getUsedConstantsAsSet do
        unless seen.contains c do stack := stack.push c
  return seen

def outDir : String := "scripts/out/"

#eval show MetaM Unit from do
  IO.FS.createDirAll outDir
  let env ← getEnv
  let cl := closureOf env #[`NaturalLatents.table, `NaturalLatents.score]
  let mut decls := "name\tmodule\tstart\tend\n"
  let mut counts : Std.HashMap Name Nat := {}
  let mut rows : Std.HashMap Name (Array (Nat × Nat)) := {}
  for n in cl.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`NaturalLatents).isPrefixOf m do continue
    counts := counts.insert m (counts.getD m 0 + 1)
    match (← findDeclarationRanges? n) with
    | some r =>
      rows := rows.insert m ((rows.getD m #[]).push (r.range.pos.line, r.range.endPos.line))
      decls := decls ++ s!"{n}\t{m}\t{r.range.pos.line}\t{r.range.endPos.line}\n"
    | none => decls := decls ++ s!"{n}\t{m}\t\t\n"
  let mut out := "module\tdecls\tlines_used\n"
  for (m, c) in counts.toList do
    let rs := (rows.getD m #[]).qsort (fun a b => a.1 < b.1)
    let mut total := 0
    let mut cur : Option (Nat × Nat) := none
    for (s, e) in rs do
      match cur with
      | none => cur := some (s, e)
      | some (cs, ce) =>
        if s ≤ ce then cur := some (cs, max ce e)
        else
          total := total + (ce - cs + 1)
          cur := some (s, e)
    if let some (cs, ce) := cur then total := total + (ce - cs + 1)
    out := out ++ s!"{m}\t{c}\t{total}\n"
  IO.FS.writeFile (outDir ++ "closure.modules.tsv") out
  IO.FS.writeFile (outDir ++ "closure.decls.tsv") decls
  IO.println s!"closure {cl.size}, modules {counts.size}"
