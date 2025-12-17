import Mathlib
import Lean

set_option pp.proofs false

open Lean Elab Command

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
  let header ← mkHeader kind id levelParams type (if isUnsafe then .unsafe else .safe) (sig := false)
  let levels := levelParams.map Level.param
  liftTermElabM <| forallTelescope (← getConstInfo id).type fun params _ =>
    let s := Expr.const id levels
    withLocalDeclD `self (mkAppN s params) fun self => do
      let mut m : MessageData := header
      -- Signature
      m := m ++ " " ++ .ofFormatWithInfosM do
        let (stx, infos) ← PrettyPrinter.delabCore s (delab := PrettyPrinter.Delaborator.delabConstWithSignature)
        pure ⟨← PrettyPrinter.ppTerm ⟨stx⟩, infos⟩
      m := m ++ " " ++ m!"number of parameters: {numParams}"
      -- Parents
      let parents := getStructureParentInfo env id
      unless parents.isEmpty do
        m := m ++ " " ++ "parents:"
        for parent in parents do
          let ptype ← inferType (mkApp (mkAppN (.const parent.projFn levels) params) self)
          m := m ++ indentD m!"{.ofConstName parent.projFn (fullNames := true)} : {ptype}"
      -- Fields
      -- Collect autoParam tactics, which are all on the flat constructor:
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
        -- Map of fields to projections of `self`
        let fieldMap : NameMap Expr ← fields.foldlM (init := {}) fun fieldMap field => do
          pure <| fieldMap.insert field (← mkProjection self field)
        for field in fields do
          let some source := findField? env id field | panic! "missing structure field info"
          let fi ← getFieldOrigin source field
          let proj := fi.projFn
          let modifier := if isPrivateName proj then "private " else ""
          let ftype ← inferType (fieldMap.find! field)
          let value ←
            if let some stx := autoParams.find? field then
              let stx : TSyntax ``Parser.Tactic.tacticSeq := ⟨stx⟩
              pure m!" := by{indentD stx}"
            else if let some defFn := getEffectiveDefaultFnForField? env id field then
              if let some (_, val) ← instantiateStructDefaultValueFn? defFn levels params (pure ∘ fieldMap.find?) then
                pure m!" :={indentExpr val}"
              else
                pure m!" := <error>"
            else
              pure m!""
          m := m ++ indentD (m!"{modifier}{.ofConstName proj (fullNames := true)} : {MessageData.nest 2 ftype}{value}")
      -- Constructor
      let cinfo := getStructureCtor (← getEnv) id
      let ctorModifier := if isPrivateName cinfo.name then "private " else ""
      m := m ++ " " ++ "constructor:" ++ indentD (ctorModifier ++ .signature cinfo.name)
      -- Resolution order
      let resOrder ← getStructureResolutionOrder id
      if resOrder.size > 1 then
        m := m ++ " " ++ "field notation resolution order:"
          ++ indentD (MessageData.joinSep (resOrder.map (.ofConstName · (fullNames := true))).toList ", ")
      -- Omit proofs; the delaborator enables `pp.proofs` for non-constant proofs, but we don't want this for default values
      withOptions (fun opts => opts.set pp.proofs.name false) do
        --logInfo m
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
def getPrintStrFromName (id : Name) : CommandElabM String := do
  let env ← getEnv
  match env.find? id with
  | ConstantInfo.defnInfo { levelParams := us, type := t, value := v, safety := s, .. } =>
      let body ← printDef "def" id us t v s
      let doc ← getDocString id
      return formatPrint doc body
  | ConstantInfo.thmInfo { levelParams := us, type := t, value := _, .. } =>
      let body ← printThm "theorem" id us t
      let doc ← getDocString id
      return formatPrint doc body
  | ConstantInfo.inductInfo { levelParams := us, numParams, type := t, ctors, isUnsafe := u, .. } =>
    if isStructure env id then
      let body ← printStructure id us numParams t ctors[0]! u
      let doc ← getDocString id
      return formatPrint doc body
    else
      let body ← printInduct id us numParams t ctors u
      let doc ← getDocString id
      return formatPrint doc body
  | some _ => return "<not def, thm, struct or induct>"
  | none => return "<error>"

/-- Finds all possible name resolutions and returns the print string for each -/
def getPrintStrList (s : String) : CommandElabM <| List String := do
  let id := mkIdent s.toName
  let allNames ← liftCoreM <| realizeGlobalConstWithInfos id
  allNames.mapM (getPrintStrFromName ·)

/-- Extracts the value of key `key` from a jsonl file (currently capped at first 100 lines) -/
def extractValuesFromJsonl (key : String) (filepath : String)
    : IO <| Except String <| List String := do
  let mut names : List String := []
  if (filepath : System.FilePath).extension != "jsonl" then
    return Except.error "File extension not `.jsonl`"
  else
    let content ← IO.FS.readFile filepath
    let lines := content.splitOn "\n"
    let mut i := 0
    for line in lines do
      let trimmedLine := line.trim
      if !trimmedLine.isEmpty then
        match Json.parse trimmedLine with
        | Except.error e =>
          return Except.error s!"Failed to parse JSON on line: {trimmedLine}.\n Error: {e}"
        | Except.ok js =>
          match js.getObjValAs? String key with
          | Except.ok nameValue =>
            if i >= 100 then
              return Except.ok <| List.dedup names.reverse
            else
              names := nameValue :: names
            i := i + 1
          | Except.error e =>
            return Except.error s!"Failed to get '{key}' string key from line: {trimmedLine}. Error: {e}"
  return Except.ok <| List.dedup names.reverse

/-- Given a `jsonl` file, the `name` values are extracted and the
result of `#print <name value>` are written into the output file -/
def writeDocs (inFilePath : String) (outFilePath : String) : CommandElabM Unit := do
  -- Extract all "name" values from the jsonl file at `inFilePath`
  let namesE ← extractValuesFromJsonl "name" inFilePath
  match namesE with
  | Except.error e =>
    IO.eprintln s!"Error: {e}"
  | Except.ok names =>
    -- Get the print object for each name in names
    let printObjs ← names.flatMapM <| getPrintStrList
    let handle ← IO.FS.Handle.mk outFilePath IO.FS.Mode.write
    -- Write each object to `outFilePath`
    for obj in printObjs do
      handle.putStrLn obj
    handle.flush
    IO.println s!"Content successfully written to {outFilePath}"

