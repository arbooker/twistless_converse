module
public import SmallLevelTwentySixUnitMMMLinearSystemV1
public import SmallLevelTwentySixGridAssemblyV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM FinitenessRamanujanSum

def groupTargetSupport : Fin 235→Fin 320 :=
  ![306,308,309,293,297,298,299,302,304,0,0,0,160,0,0,88,219,0,160,222,0,102,160,233,242,250,0,73,84,88,102,112,118,160,187,205,209,211,219,224,227,232,233,237,242,244,248,250,251,254,255,258,261,262,263,267,272,279,281,283,286,287,288,0,102,233,0,0,160,0,0,0,294,29,307,295,296,301,30,31,32,36,39,44,55,61,68,92,118,211,77,16,99,252,289,310,57,103,187,63,273,274,275,276,51,52,53,310,311,312,313,314,316,317,0,6,12,22,49,259,282,288,293,299,301,302,304,305,306,307,308,303,304,305,309,311,228,286,295,298,299,300,301,277,278,280,282,285,286,288,289,299,75,82,110,160,222,49,84,211,237,71,103,187,215,219,222,237,241,247,252,253,255,256,258,259,260,262,263,265,266,56,57,58,62,65,66,74,77,80,102,106,134,187,218,250,84,110,237,272,99,160,211,222,239,246,309,41,43,21,57,93,237,260,18,268,269,270,45,46,47,271,237,71,173,201,213,217,239,218,88,160,160,77,145]

theorem groupTargetSupport_spec (i : Fin 235) :
    support (groupTargetSupport i)=gridGroupTarget i := by
  fin_cases i <;> rfl

theorem groupTarget_restrict (v : Fin 780→ℂ) (i : Fin 235) :
    extension support (fun j => v (support j)) (gridGroupTarget i)=v (gridGroupTarget i) := by
  rw [←groupTargetSupport_spec]
  exact extend_at support support_injective (fun j => v (support j)) (groupTargetSupport i)

end SmallLevelTwentySixGrid
