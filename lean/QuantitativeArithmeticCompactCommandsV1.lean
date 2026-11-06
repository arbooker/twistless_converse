module
public meta import Lean.Elab.Command

/-! Keep generated certificate families in a single module without retaining
editor information for each proof. The supplied command is elaborated normally;
all declarations still pass Lean's kernel. -/

public meta section
open Lean Elab Command

elab "compact_certificate " declaration:command : command =>
  withScope (fun scope => { scope with opts := scope.opts.setBool `Elab.async false }) <|
    withEnableInfoTree false <| elabCommand declaration
