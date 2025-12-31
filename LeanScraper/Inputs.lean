import Lean

open Lean

/-
Set the modules you want to extract from
-/
def setModules : Array Import :=
  #[{module := `Lean}]

/-
Set the constants filter -
`true` if you want it, `false` otherwise.
-/
def setFilter (info : ConstantInfo) : Bool :=
  match info with
  | .axiomInfo _  => false
  | .defnInfo _   => true
  | .thmInfo _    => true
  | .opaqueInfo _ => false
  | .quotInfo _   => false
  | .inductInfo _ => true
  | .ctorInfo _   => false
  | .recInfo _    => false

/-
Set if you want proofs to be present (`true`) or omitted (`false`).
-/
def setProofs : Bool :=
  false

/-
Set the output (.jsonl) path for the data
-/
def setDataOutFilePath : String :=
  "Data/lean.jsonl"
