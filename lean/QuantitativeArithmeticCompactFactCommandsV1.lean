module
public meta import Lean.Elab.Command

/-! A family of explicitly stated facts sharing one proof procedure.
Each generated theorem is elaborated and kernel-checked normally, sequentially.
This removes duplicated tactic text and editor metadata, not proof obligations.
-/
public meta section
open Lean Elab Command

declare_syntax_cat compactFact
syntax "(" ident " : " term ")" : compactFact
syntax "compact_facts " "[" compactFact,* "]" " by " tacticSeq : command

elab_rules : command
  | `(command| compact_facts [$facts:compactFact,*] by $proof:tacticSeq) => do
      for fact in facts.getElems do
        let `(compactFact| ($name:ident : $type:term)) := fact
          | throwUnsupportedSyntax
        let decl ← `(command| theorem $name : $type := by $proof)
        withScope (fun scope => { scope with opts := scope.opts.setBool `Elab.async false }) <|
          withEnableInfoTree false <| elabCommand decl
        elabCommand (← `(command| #print axioms $name))
