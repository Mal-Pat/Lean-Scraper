/-
Authors: Malhar A. Patel, Anand Rao Tadipatri
-/

import Lean

open Lean Meta Elab Command

def modifyScopeOptions (ls : List Scope) (f : Options → Options)
    : List Scope :=
  match ls with
  | [] => panic! "unreachable"
  | h :: l => {h with opts := f h.opts} :: l

instance : MonadWithOptions CommandElabM where
  withOptions f act := do
    modify (fun σ => {σ with scopes := modifyScopeOptions σ.scopes f})
    act

def printercept (t : Ident) (proofs : Bool := true)
    : CommandElabM String :=
  withOptions (· |>.insert `pp.proofs proofs) do
  elabCommand =<< `(command | #print $t)
  return ← (← get).messages.unreported[0]!.data.toString

def printerceptName (n : Name) (proofs : Bool := true)
    : CommandElabM String :=
  printercept (mkIdent n) proofs
