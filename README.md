# Lean-Scraper

Scrapes all the constants from any module in Lean!

## Background

You can `#print` constants in Lean 4 as follows:

```lean4
#print Nat.add_le_add

-- Output:
/-
theorem Nat.add_le_add : ∀ {a b c d : Nat}, a ≤ b → c ≤ d → a + c ≤ b + d :=
fun {a b c d} h₁ h₂ ↦ Nat.le_trans (Nat.add_le_add_right h₁ c) (Nat.add_le_add_left h₂ b)
-/
```

In Lean 4, the information associated with constant declarations is stored in the `ConstantInfo` type.

```lean4
/-- Information associated with constant declarations. -/
inductive ConstantInfo where
  | axiomInfo    (val : AxiomVal)
  | defnInfo     (val : DefinitionVal)
  | thmInfo      (val : TheoremVal)
  | opaqueInfo   (val : OpaqueVal)
  | quotInfo     (val : QuotVal)
  | inductInfo   (val : InductiveVal)
  | ctorInfo     (val : ConstructorVal)
  | recInfo      (val : RecursorVal)
  deriving Inhabited
```

This code extracts all the constants in the module, filters out what you don't want, takes the output of running `#print` on those constants and stores it all in a jsonl file, with each object in the format given below.

```json
{"name": "Nat.add_le_add", "info": "thm", "print": "theorem Nat.add_le_add : ∀ {a b c d : Nat}, a ≤ b → c ≤ d → a + c ≤ b + d :=\nfun {a b c d} h₁ h₂ ↦ Nat.le_trans (Nat.add_le_add_right h₁ c) (Nat.add_le_add_left h₂ b)"}
```

## How to Use

Clone this repo and run:

```bash
lake build
```

Go to `LeanScraper.lean` and set your inputs:

```lean4
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
```

Then run:

```bash
lake exe Scraper
```

It could take anywhere between 2 min to 15 min to run, based on your system.

The data will be extracted into the `dataOutFilePath` you set.