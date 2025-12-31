import Lean

open Lean

/-
Set the modules you want to extract constants from.
Add or remove modules in the format shown below.
-/
def setModules : Array Import :=
  #[
    {module := `Lean},
    {module := `Mathlib}
  ]

/-
Set a filter for the extracted constants -
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
Set whether you want proofs to be present (`true`) or omitted (`false`)
in the "print" key of the output Json object.
-/
def setProofs : Bool :=
  false

/-
Set the output (.jsonl) path for the data
(relative to the root of the repo)
-/
def setDataOutFilePath : String :=
  "output.jsonl"
