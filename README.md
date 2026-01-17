# Lean-Scraper

Scrapes all the constants from any module in Lean!

## Background

You can `#print` names of constants in Lean 4 as follows:

```lean4
#print Nat.add_le_add
```

Output:
```
theorem Nat.add_le_add : ∀ {a b c d : Nat}, a ≤ b → c ≤ d → a + c ≤ b + d :=
fun {a b c d} h₁ h₂ ↦ Nat.le_trans (Nat.add_le_add_right h₁ c) (Nat.add_le_add_left h₂ b)
```

The information associated with constant declarations is stored in the `ConstantInfo` type.

```lean4
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

## What Lean-Scraper does

- Extracts all the constants in the modules set by the user
- Filters out constants the user doesn't want (based on `ConstantInfo`)
- Finds the docstrings associated with the constants (if any)
- Takes the output of running `#print` on those constants as a string
- Constructs a Json object for each constant with all the above details (format of Json object given below)
- Writes all the Json objects in a `.jsonl` file

Format:
```json
{
  "docstring":"string", 
  "info":"string", 
  "name":"string", 
  "print":"string"
}
```

Example:
```json
{
  "docstring":"The set of closed points. ",
  "info":"defn",
  "name":"closedPoints",
  "print":"private theorem SimplexCategoryGenRel.simplicialInsert_length._proof_1_1 : ∀ (a : Nat),\n  Eq (SimplexCategoryGenRel.simplicialInsert a List.nil).length (instHAdd.hAdd List.nil.length 1) :=\n⋯"
}
```

(the example given above has `setProofs` set to `false`)

## How to Use

Clone this repo.

Go to `LeanScraper/Inputs.lean` and set your inputs:

- setModules (the modules you want to extract)
- setFilter (the filter on types of constants)
- setProofs (if you want proofs in the `"print"` key or not)
- setDataOutFilePath (the output `.jsonl` file path)

More details can be found in the comments above the inputs in `LeanScraper/Inputs.lean`.

(The defaults set in `LeanScraper/Inputs.lean` extract all constants from Lean and Mathlib, keep only the definitions, theorems and inductive types, and write their data into `output.jsonl`, with the proofs set to `false` in the "print" key output)

Run the following commands:

```bash
lake exe cache get
lake build
```

Then run the following command to start the scraping process:

```bash
lake exe Scraper
```

It could take anywhere between 2 min to 20 min to run, based on your system.

The data will be extracted into the output file you set.

Running `lake exe Scraper` with the same output file in `LeanScraper/Inputs.lean` will overwrite any data in that file.