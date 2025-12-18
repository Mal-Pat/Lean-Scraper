import Lean
import Lean.Meta
import Init.System

set_option synthInstance.maxHeartbeats 1000000

set_option pp.proofs false

set_option maxRecDepth 1000
set_option compiler.extract_closed false

open Lean Elab Command Meta

def levelParamsToMessageData (levelParams : List Name) : MessageData :=
  match levelParams with
  | []    => ""
  | u::us => Id.run do
    let mut m := m!".\{{u}"
    for u in us do
      m := m ++ ", " ++ toMessageData u
    return m ++ "}"

def mkHeader (kind : String) (id : Name) (levelParams : List Name) (type : Expr)
    (safety : DefinitionSafety) (sig : Bool := true) : CommandElabM MessageData := do
  let mut attrs := #[]
  match (← getReducibilityStatus id) with
  | ReducibilityStatus.irreducible =>   attrs := attrs.push m!"irreducible"
  | ReducibilityStatus.reducible =>     attrs := attrs.push m!"reducible"
  | ReducibilityStatus.semireducible => pure ()
  if defeqAttr.hasTag (← getEnv) id then
    attrs := attrs.push m!"defeq"
  let mut m : MessageData := m!""
  unless attrs.isEmpty do
    m := m ++ "@[" ++ MessageData.joinSep attrs.toList ", " ++ "] "
  match safety with
  | DefinitionSafety.unsafe  => m := m ++ "unsafe "
  | DefinitionSafety.partial => m := m ++ "partial "
  | DefinitionSafety.safe    => pure ()
  if isProtected (← getEnv) id then
    m := m ++ "protected "
  let id' ← match privateToUserName? id with
    | some id' =>
        m := m ++ "private "
        pure id'
    | none => pure id
  --let typeStr := (← ppExpr type).pretty
  if sig then
    return m!"{m}{kind} {id'}{levelParamsToMessageData levelParams} : {type}"
  else
    return m!"{m}{kind}"

partial def getFieldOrigin (structName field : Name) : MetaM StructureFieldInfo := do
  let env ← getEnv
  for parent in getStructureParentInfo env structName do
    if (findField? env parent.structName field).isSome then
      return ← getFieldOrigin parent.structName field
  let some fi := getFieldInfo? env structName field
    | throwError "no such field {field} in {structName}"
  return fi

open Meta in
partial def printStructure (id : Name) (levelParams : List Name) (numParams : Nat)
    (type : Expr) (ctor : Name) (isUnsafe : Bool) : CommandElabM String := do
  let env ← getEnv
  let kind := if isClass env id then "class" else "structure"
  let header ← mkHeader kind id levelParams type
    (if isUnsafe then .unsafe else .safe) (sig := false)
  let levels := levelParams.map Level.param
  liftTermElabM <| forallTelescope (← getConstInfo id).type fun params _ =>
    let s := Expr.const id levels
    withLocalDeclD `self (mkAppN s params) fun self => do
      let mut m : MessageData := header
      m := m ++ " " ++ .ofFormatWithInfosM do
        let (stx, infos) ← PrettyPrinter.delabCore s
          (delab := PrettyPrinter.Delaborator.delabConstWithSignature)
        pure ⟨← PrettyPrinter.ppTerm ⟨stx⟩, infos⟩
      m := m ++ " " ++ m!"number of parameters: {numParams}"
      let parents := getStructureParentInfo env id
      unless parents.isEmpty do
        m := m ++ " " ++ "parents:"
        for parent in parents do
          let ptype ← inferType (mkApp (mkAppN (.const parent.projFn levels) params) self)
          m := m ++ indentD m!"{.ofConstName parent.projFn (fullNames := true)} : {ptype}"
      let flatCtorName := mkFlatCtorOfStructCtorName ctor
      let flatCtorInfo ← getConstInfo flatCtorName
      let autoParams : NameMap Syntax ← forallTelescope flatCtorInfo.type fun args _ =>
        args[numParams...*].foldlM (init := {}) fun set arg => do
          let decl ← arg.fvarId!.getDecl
          if let some (.const tacticDecl _) := decl.type.getAutoParamTactic? then
            let tacticSyntax ← ofExcept <| evalSyntaxConstant (← getEnv) (← getOptions) tacticDecl
            pure <| set.insert decl.userName tacticSyntax
          else
            pure set
      let fields := getStructureFieldsFlattened env id (includeSubobjectFields := false)
      if fields.isEmpty then
        m := m ++ " " ++ "fields: (none)"
      else
        m := m ++ " " ++ "fields:"
        let fieldMap : NameMap Expr ← fields.foldlM (init := {}) fun fieldMap field => do
          pure <| fieldMap.insert field (← mkProjection self field)
        for field in fields do
          let some source := findField? env id field | panic! "missing structure field info"
          let fi ← getFieldOrigin source field
          let proj := fi.projFn
          let modifier := if isPrivateName proj then "private " else ""
          let ftype ← inferType (fieldMap.get! field)
          let value ←
            if let some stx := autoParams.find? field then
              let stx : TSyntax ``Parser.Tactic.tacticSeq := ⟨stx⟩
              pure m!" := by{indentD stx}"
            else if let some defFn := getEffectiveDefaultFnForField? env id field then
              if let some (_, val) ← instantiateStructDefaultValueFn? defFn levels
                  params (pure ∘ fieldMap.find?) then
                pure m!" :={indentExpr val}"
              else
                pure m!" := <error>"
            else
              pure m!""
          m := m ++ indentD (m!"{modifier}{.ofConstName proj (fullNames := true)} : \
            {MessageData.nest 2 ftype}{value}")
      let cinfo := getStructureCtor (← getEnv) id
      let ctorModifier := if isPrivateName cinfo.name then "private " else ""
      m := m ++ " " ++ "constructor:" ++ indentD (ctorModifier ++ .signature cinfo.name)
      let resOrder ← getStructureResolutionOrder id
      if resOrder.size > 1 then
        m := m ++ " " ++ "field notation resolution order:" ++ indentD (MessageData.joinSep
          (resOrder.map (.ofConstName · (fullNames := true))).toList ", ")
      withOptions (fun opts => opts.set pp.proofs.name false) do
        (← addMessageContext m).toString

def printInduct (id : Name) (levelParams : List Name) (numParams : Nat) (type : Expr)
    (ctors : List Name) (isUnsafe : Bool) : CommandElabM String := do
  let mut m ← mkHeader "inductive" id levelParams type (if isUnsafe then .unsafe else .safe)
  m := m ++ " " ++ "number of parameters: " ++ toString numParams
  m := m ++ " " ++ "constructors:"
  for ctor in ctors do
    let cinfo ← getConstInfo ctor
    m := m ++ " " ++ ctor ++ " : " ++ cinfo.type
  --logInfo m
  (← addMessageContext m).toString

def mkOmittedMsg : Option Expr → MessageData
  | none   => "<not imported>"
  | some e => e

def printDef (kind : String) (id : Name) (levelParams : List Name) (type : Expr)
    (value? : Option Expr) (safety := DefinitionSafety.safe) : CommandElabM String := do
  let m ← mkHeader kind id levelParams type safety
  let m := m ++ " :=" ++ " " ++ mkOmittedMsg value?
  --logInfo m
  (← addMessageContext m).toString

/-- Prints the theorem and replaces the proof (value) with `⋯` -/
def printThm (kind : String) (id : Name) (levelParams : List Name)
    (type : Expr) (safety := DefinitionSafety.safe) : CommandElabM String := do
  let m ← mkHeader kind id levelParams type safety
  let m := m ++ " := ⋯"
  --logInfo m
  (← addMessageContext m).toString

/-- Returns the docstring associated with `id : Name` as a String -/
def getDocString (id : Name) : CommandElabM String := do
  let env ← getEnv
  match ← findDocString? env id with
  | some doc => return s!"/--{doc}-/"
  | none => return ""

/-- Used for debugging `getDocString` -/
def displayDocString (s : String) : CommandElabM <| List String := do
  let id := mkIdent s.toName
  let allNames ← liftCoreM <| realizeGlobalConstWithInfos id
  allNames.mapM (getDocString ·)

/-- Joins the docstring and body, along with eliminating `\n` -/
def formatPrint (doc : String) (body : String) : String :=
  (doc ++ " " ++ body).replace "\n" " "

/-- Finds the name's info and calls the appropriate print function -/
def getPrintStr (inp : Name × ConstantInfo) : CommandElabM String := do
  let ⟨id, info⟩ := inp
  match info with
  | ConstantInfo.defnInfo { levelParams := us, type := t, value := v, safety := s, .. } =>
      let body ← printDef "def" id us t v s
      let doc ← getDocString id
      return formatPrint doc body
  | ConstantInfo.thmInfo { levelParams := us, type := t, value := _, .. } =>
      let body ← printThm "theorem" id us t
      let doc ← getDocString id
      return formatPrint doc body
  | ConstantInfo.inductInfo { levelParams := us, numParams, type := t, ctors, isUnsafe := u, .. } =>
    let env ← getEnv
    if isStructure env id then
      let body ← printStructure id us numParams t ctors[0]! u
      let doc ← getDocString id
      return formatPrint doc body
    else
      let body ← printInduct id us numParams t ctors u
      let doc ← getDocString id
      return formatPrint doc body
  | _ => return "<error>"

def checkUseful (info : ConstantInfo) : Bool :=
  match info with
  | .defnInfo _   => true
  | .thmInfo _    => true
  | .inductInfo _ => true
  | _             => false

def constantDecls : CommandElabM <| Array <| Name × ConstantInfo := do
  let env ← getEnv
  logInfo "got env"
  IO.println "got env"
  let decls := env.constants.map₁.toArray
  logInfo m!"got decls : {decls.size}"
  IO.println s!"got decls : {decls.size}"
  let filtered_decls := decls.filter <| fun (_,info) => checkUseful info
  return filtered_decls

def writeDocs (outFilePath : String) : CommandElabM Unit := do
  -- Get all name values
  let names ← constantDecls
  logInfo m!"got names : {names.size}"
  IO.println s!"got names : {names.size}"
  -- Get the print object for each name in names
  let printObjs ← names.mapM <| getPrintStr
  let handle ← IO.FS.Handle.mk outFilePath IO.FS.Mode.write
  -- Write each object to `outFilePath`
  for obj in printObjs do
    handle.putStrLn obj
  handle.flush
  IO.println s!"Content successfully written to {outFilePath}"

def writeDocsCore (outFilePath : String) : CoreM Unit := do
  liftCommandElabM <| writeDocs outFilePath

--#eval writeDocs "LeanScraper/text.txt"

-- def constantNames  : MetaM (Array Name) := do
--   let env ← getEnv
--   let decls := env.constants.map₁.toArray
--   let allNames := decls.map $ fun (name, _) => name
--   let names ← allNames.filterM (isWhiteListed)
--   let names ←  names.filterM fun n => do pure <|
--     !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf n)) && (← isWhiteListed n) && !(isMatchCase n)
--   return names

-- def propNames : MetaM (Array Name) := do
--   (← constantNames).filterM fun name => do
--     let info? := ((← getEnv).find? name)
--     let value? := info? >>= ConstantInfo.value?
--     let check? ← value?.mapM isProof
--     return check?.getD false

#check ConstantInfo.value?

def EIO.runToIO' (eio : EIO Exception α) : IO α  := do
  match ←  eio.toIO' with
  | Except.ok x =>
      pure x
  | Except.error e =>
      let msg ← e.toMessageData.toString
      IO.throwServerError msg

def main : IO Unit := do
  let outFilePath := "LeanScraper/text.txt"
  let env ← importModules (loadExts := true) #[{module := `Mathlib}] {}
  IO.println "Started!"
  let coreCtx : Core.Context :=
    {fileName := "", fileMap := {source:= "", positions := #[]},
      maxHeartbeats := 1000000000, maxRecDepth := 10000}
  let _ ← writeDocsCore outFilePath |>.run' coreCtx {env := env} |>.runToIO'
  IO.println "Success!"
