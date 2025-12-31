/-
Authors : Malhar A. Patel
-/

import Lean
import LeanScraper.Printercept
import LeanScraper.Inputs

set_option synthInstance.maxHeartbeats 10000000000
set_option maxRecDepth 100000

open Lean Elab Command Meta

def infoToString (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "defn"
  | .thmInfo _    => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"

def constantDecls : CommandElabM <| Array <| Name × ConstantInfo := do
  let env ← getEnv
  IO.println "Environment Loaded!"
  let decls := env.constants.map₁.toArray
  IO.println s!"Number of total Decls : {decls.size}"
  let filtered_decls := decls.filter <| fun (_,info) => checkUseful info
  return filtered_decls

def writeDocs (outFilePath : String) : CommandElabM Unit := do
  -- Get all name values
  let decls ← constantDecls
  IO.println s!"Number of filtered Names : {decls.size}"
  -- Get the print object for each name in names
  let printJsonObjs ← decls.mapM <| fun (name,info) => do
    return Json.mkObj [
      ("name", .str name.toString),
      ("info", .str <| infoToString info),
      ("print", .str <| ← printerceptName name)]
  let handle ← IO.FS.Handle.mk outFilePath IO.FS.Mode.write
  -- Write each object to `outFilePath`
  for obj in printJsonObjs do
    handle.putStrLn obj.compress
  handle.flush
  IO.println s!"Content successfully written to {outFilePath}"

def writeDocsCore (outFilePath : String) : CoreM Unit := do
  liftCommandElabM <| writeDocs outFilePath

unsafe def main : IO Unit := do
  initSearchPath (← Lean.findSysroot) [
    "build/lib",
    "lake-packages/mathlib/build/lib/",
    "lake-packages/std/build/lib/",
    "lake-packages/Qq/build/lib/",
    ]
  withImportModules
    modules
    {entries := []}
  <| fun env => do
    let coreCtx : Core.Context :=
      {fileName := "", fileMap := {source:= "", positions := #[]},
        maxHeartbeats := 10000000000, maxRecDepth := 100000}
    let eio := writeDocsCore dataOutFilePath |>.run' coreCtx {env := env}
    match ← eio.toIO' with
    | Except.ok x => pure x
    | Except.error e =>
        let msg ← e.toMessageData.toString
        IO.throwServerError msg
