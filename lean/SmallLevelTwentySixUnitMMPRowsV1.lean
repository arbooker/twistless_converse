module
public import SmallLevelTwentySixUnitMMPRowsBundleV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 6000
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMP
open Complex

/-- Selected original leading-row expressions for this sign case.
Their interpretation as Mellin equations is proved separately. -/
def sourceRows (X Y Z W a b : ℂ) (v : Fin 780→ℂ) (i : Fin 370) : ℂ :=
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
  | _ => 0

end SmallLevelTwentySixUnitMMP
