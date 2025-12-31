/-
Authors : Malhar A. Patel
-/

import Lean
import LeanScraper.Printercept
import LeanScraper.Inputs

set_option synthInstance.maxHeartbeats 100000000
set_option maxRecDepth 1000

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

def filterDecls (decls : Array <| Name × ConstantInfo)
    : Array <| Name × ConstantInfo :=
  decls.filter <| fun (_, info) => setFilter info

def addDocString (env : Environment) (decls : Array <| Name × ConstantInfo)
    : IO <| Array <| Name × ConstantInfo × String :=
  decls.mapM <| fun (name, info) => do
    match ← findDocString? env name with
    | some doc => return (name, info, doc)
    | none => return (name, info, "")

def addPrint (decls : Array <| Name × ConstantInfo × String)
    : CommandElabM <| Array <| Name × ConstantInfo × String × String :=
  decls.mapM <| fun (name, info, doc) => do
    return (name, info, doc, ← printerceptName name setProofs)

def getDeclsDocPrint : CommandElabM <| Array <| Name × ConstantInfo × String × String := do
  IO.println "Loading Environment..."
  let env ← getEnv
  IO.println "Extracting declarations..."
  let decls := env.constants.map₁.toArray
  IO.println s!"Number of total decls : {decls.size}"
  let filtered_decls := filterDecls decls
  IO.println s!"Number of filtered decls : {filtered_decls.size}"
  IO.println s!"Finding DocStrings..."
  let decls_doc ← addDocString env filtered_decls
  IO.println s!"Getting `#print` outputs..."
  let decls_doc_print ← addPrint decls_doc
  return decls_doc_print

def convertToJson (decls_doc_print : Array <| Name × ConstantInfo × String × String)
    : Array Json :=
  decls_doc_print.map <| fun (name, info, doc, print) =>
    Json.mkObj [
      ("name", .str name.toString),
      ("info", .str <| infoToString info),
      ("docstring", .str doc),
      ("print", .str print)
    ]

def getFinalJsonObjs : CommandElabM <| Array Json := do
  let decls_doc_print ← getDeclsDocPrint
  IO.println "Converting to Json..."
  return convertToJson decls_doc_print

def writeData (outFilePath : String) : CommandElabM Unit := do
  let finalJsonObjs ← getFinalJsonObjs
  let handle ← IO.FS.Handle.mk outFilePath IO.FS.Mode.write
  IO.println s!"Writing into file {outFilePath}..."
  for obj in finalJsonObjs do
    handle.putStrLn obj.compress
  handle.flush
  IO.println s!"Content successfully written to {outFilePath}"

def writeDataCore (outFilePath : String) : CoreM Unit := do
  liftCommandElabM <| writeData outFilePath

unsafe def main : IO Unit := do
  initSearchPath (← Lean.findSysroot) [
    "build/lib",
    "lake-packages/mathlib/build/lib/",
    "lake-packages/std/build/lib/",
    "lake-packages/Qq/build/lib/",
    ]
  withImportModules setModules {entries := []} <| fun env => do
    let coreCtx : Core.Context :=
      {fileName := "", fileMap := {source:= "", positions := #[]},
        maxHeartbeats := 10000000000, maxRecDepth := 100000}
    let eio := writeDataCore setDataOutFilePath |>.run' coreCtx {env := env}
    match ← eio.toIO' with
    | Except.error e =>
        let msg ← e.toMessageData.toString
        IO.throwServerError msg
    | Except.ok x => pure x
