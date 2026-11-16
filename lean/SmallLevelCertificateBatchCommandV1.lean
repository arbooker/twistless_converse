module
public meta import Lean.Elab.Command

public meta section
open Lean Elab Command

/-- Elaborate a group of ordinary certificate declarations without retaining
one frontend environment snapshot per declaration. Every declaration still
goes through Lean's usual elaborator and kernel. -/
elab "certificate_batch" "{" declarations:command* "}" : command => do
  let progress ← IO.getEnv "ASTRA_CERTIFICATE_PROGRESS"
  withEnableInfoTree false do
    for declaration in declarations do
      -- Optional build instrumentation. This does not supply proof terms or
      -- alter kernel checking; it identifies the declaration being checked.
      if let some path := progress then
        let label := (declaration.raw.reprint.getD "certificate declaration").take 180
        IO.FS.writeFile path s!"{← IO.monoMsNow}\n{label}\n"
      elabCommand declaration
      if (← get).messages.hasErrors then
        return

end
