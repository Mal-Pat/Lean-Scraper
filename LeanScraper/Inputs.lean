import Lean

open Lean

/-
Set the modules you want to extract from
-/
def modules : Array Import :=
  #[{module := `Mathlib}]

/-
Set whatever you want to extract to `true`,
and the rest to `false`.
-/
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

/-
Set the output (.jsonl) path for the data
-/
def dataOutFilePath : String :=
  "Data/mathlib.jsonl"
