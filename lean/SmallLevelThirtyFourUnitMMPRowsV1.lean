module
public import SmallLevelThirtyFourUnitMMPRowsBundleV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 6000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMP
open Complex

/-- Selected original leading-row expressions for this sign case.
Their interpretation as Mellin equations is proved separately. -/
def sourceRows (X Y Z W a b : ℂ) (v : Fin 510→ℂ) (i : Fin 546) : ℂ :=
  let j : Fin 16:=⟨i.val%16,Nat.mod_lt _ (by decide)⟩
  match i.val/16 with
  | 0 => sourceRowsPart0 X Y Z W a b v j
  | 1 => sourceRowsPart1 X Y Z W a b v j
  | 2 => sourceRowsPart2 X Y Z W a b v j
  | 3 => sourceRowsPart3 X Y Z W a b v j
  | 4 => sourceRowsPart4 X Y Z W a b v j
  | 5 => sourceRowsPart5 X Y Z W a b v j
  | 6 => sourceRowsPart6 X Y Z W a b v j
  | 7 => sourceRowsPart7 X Y Z W a b v j
  | 8 => sourceRowsPart8 X Y Z W a b v j
  | 9 => sourceRowsPart9 X Y Z W a b v j
  | 10 => sourceRowsPart10 X Y Z W a b v j
  | 11 => sourceRowsPart11 X Y Z W a b v j
  | 12 => sourceRowsPart12 X Y Z W a b v j
  | 13 => sourceRowsPart13 X Y Z W a b v j
  | 14 => sourceRowsPart14 X Y Z W a b v j
  | 15 => sourceRowsPart15 X Y Z W a b v j
  | 16 => sourceRowsPart16 X Y Z W a b v j
  | 17 => sourceRowsPart17 X Y Z W a b v j
  | 18 => sourceRowsPart18 X Y Z W a b v j
  | 19 => sourceRowsPart19 X Y Z W a b v j
  | 20 => sourceRowsPart20 X Y Z W a b v j
  | 21 => sourceRowsPart21 X Y Z W a b v j
  | 22 => sourceRowsPart22 X Y Z W a b v j
  | 23 => sourceRowsPart23 X Y Z W a b v j
  | 24 => sourceRowsPart24 X Y Z W a b v j
  | 25 => sourceRowsPart25 X Y Z W a b v j
  | 26 => sourceRowsPart26 X Y Z W a b v j
  | 27 => sourceRowsPart27 X Y Z W a b v j
  | 28 => sourceRowsPart28 X Y Z W a b v j
  | 29 => sourceRowsPart29 X Y Z W a b v j
  | 30 => sourceRowsPart30 X Y Z W a b v j
  | 31 => sourceRowsPart31 X Y Z W a b v j
  | 32 => sourceRowsPart32 X Y Z W a b v j
  | 33 => sourceRowsPart33 X Y Z W a b v j
  | 34 => sourceRowsPart34 X Y Z W a b v j
  | _ => 0

end SmallLevelThirtyFourUnitMMP
