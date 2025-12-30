/-
Authors: Malhar A. Patel, Anand Rao Tadipatri
-/

import Lean

open Lean Meta Elab Command

def modifyScopeOptions (ls : List Scope) (f : Options → Options) : List Scope :=
  match ls with
  | [] => panic! "unreachable"
  | h :: l => {h with opts := f h.opts} :: l

instance : MonadWithOptions CommandElabM where
  withOptions f act := do
    modify (fun σ => {σ with scopes := modifyScopeOptions σ.scopes f})
    act

def printercept (t:Ident) : CommandElabM String :=
  withOptions (· |>.insert `pp.proofs false) do
  elabCommand =<< `(command | #print $t)
  return ← (← get).messages.unreported[0]!.data.toString

def printerceptName (n : Name) : CommandElabM String :=
  withOptions (· |>.insert `pp.proofs false) do
  elabCommand =<< `(command | #print $(mkIdent n))
  return ← (← get).messages.unreported[0]!.data.toString

#eval printerceptName ``Nat.zero_le
