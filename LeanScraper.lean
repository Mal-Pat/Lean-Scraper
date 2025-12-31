/-
Authors : Malhar A. Patel
-/

import LeanScraper.Printercept
import Lean
import Init.System

set_option synthInstance.maxHeartbeats 1000000

set_option maxRecDepth 1000
set_option compiler.extract_closed false

open Lean Elab Command Meta

def checkUseful (info : ConstantInfo) : Bool :=
  match info with
  | .axiomInfo _  => false
  | .defnInfo _   => true
  | .thmInfo _    => true
  | .opaqueInfo _ => false
  | .quotInfo _   => false
  | .inductInfo _ => true
  | .ctorInfo _   => false
  | .recInfo _    => false

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

def constantNames : CommandElabM <| Array Name := do
  let env ← getEnv
  IO.println "got env"
  let decls := env.constants.map₁.toArray
  IO.println s!"got decls : {decls.size}"
  let filtered_decls := decls.filter <| fun (_,info) => checkUseful info
  let filtered_decls_names := filtered_decls.map <| fun (name, _) => name
  return filtered_decls_names

-- TODO:
-- Include constantInfo type as well in the Json

def writeDocs (outFilePath : String) : CommandElabM Unit := do
  -- Get all name values
  let names ← constantNames
  --let names := #[``Nat.div_pos_iff._simp_1]
  IO.println s!"got names : {names.size}"
  -- Get the print object for each name in names
  let printObjs ← names.mapM <| fun name => do
    return Json.mkObj [
      ("name", .str name.toString),
      ("print", .str <| ← printerceptName name)]
  let handle ← IO.FS.Handle.mk outFilePath IO.FS.Mode.write
  -- Write each object to `outFilePath`
  for obj in printObjs do
    handle.putStrLn obj.compress
  handle.flush
  IO.println s!"Content successfully written to {outFilePath}"

-- #eval writeDocs "test.jsonl"

def writeDocsCore (outFilePath : String) : CoreM Unit := do
  liftCommandElabM <| writeDocs outFilePath

#print EIO

def EIO.runToIO' (eio : EIO Exception α) : IO α  := do
  match ← eio.toIO' with
  | Except.ok x =>
      pure x
  | Except.error e =>
      let msg ← e.toMessageData.toString
      IO.throwServerError msg

-- #eval printerceptName ``Nat.div_pos_iff._simp_1

unsafe def main : IO Unit := do
  initSearchPath (← Lean.findSysroot) [
    "build/lib",
    "lake-packages/mathlib/build/lib/",
    -- "lake-packages/std/build/lib/",
    -- "lake-packages/Qq/build/lib/",
    -- "lake-packages/aesop/build/lib/",
    -- "lake-packages/proofwidgets/build/lib"
    ]
  withImportModules
    #[{module := `Lean}]
    {entries := []}
  <| fun env => do
    let coreCtx : Core.Context :=
      {fileName := "", fileMap := {source:= "", positions := #[]},
        maxHeartbeats := 1000000000, maxRecDepth := 10000}
    let outFilePath := "test.jsonl"
    let eio := writeDocsCore outFilePath |>.run' coreCtx {env := env}
    match ← eio.toIO' with
    | Except.ok x => pure x
    | Except.error e =>
        let msg ← e.toMessageData.toString
        IO.throwServerError msg
