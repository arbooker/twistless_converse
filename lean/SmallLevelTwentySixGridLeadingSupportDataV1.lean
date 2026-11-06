module
public import SmallLevelTwentySixGridShiftSupportV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM FinitenessRamanujanSum

def groupIndexSupport : Fin 235→Fin 320 :=
 ![0,99,160,0,71,79,88,160,219,1,2,3,4,5,6,8,9,10,12,13,15,17,19,22,23,24,28,33,34,35,38,40,42,49,54,58,59,60,63,66,67,70,71,73,77,79,84,88,89,94,97,102,110,112,116,134,160,203,209,219,233,237,248,311,312,313,314,315,316,317,318,319,258,244,229,134,218,264,110,203,229,253,260,266,277,282,285,289,290,291,292,222,305,11,14,69,20,25,26,27,84,110,237,293,99,222,258,115,134,144,149,154,157,158,160,162,163,164,165,167,168,169,170,172,174,175,177,181,187,197,209,89,110,125,146,151,171,178,192,200,203,216,237,49,71,93,103,114,118,123,124,143,179,180,182,183,184,185,186,188,189,190,191,193,194,195,196,198,199,202,206,207,208,210,211,215,218,222,229,241,272,80,84,92,106,111,113,119,121,122,126,127,128,129,130,131,132,133,135,136,137,138,139,140,141,142,155,228,250,105,147,150,152,153,232,63,99,222,28,84,211,250,48,50,103,82,104,108,120,148,156,159,161,176,244]
theorem groupIndexSupport_spec (i : Fin 235) : support (groupIndexSupport i)=gridGroupIndex i := by
  fin_cases i <;> rfl

theorem groupIndex_restrict (v : Fin 780→ℂ) (i : Fin 235) :
    extension support (fun j => v (support j)) (gridGroupIndex i)=v (gridGroupIndex i) := by
  rw [←groupIndexSupport_spec]
  exact extend_at support support_injective (fun j => v (support j)) (groupIndexSupport i)
theorem infinity_restrict_0 (v : Fin 780→ℂ) :
    extension support (fun j => v (support j)) (gridInfinityIndex 0)=v (gridInfinityIndex 0) :=
  extend_at support support_injective (fun j => v (support j)) 0
theorem infinity_restrict_1 (v : Fin 780→ℂ) :
    extension support (fun j => v (support j)) (gridInfinityIndex 1)=v (gridInfinityIndex 1) :=
  extend_at support support_injective (fun j => v (support j)) 166

end SmallLevelTwentySixGrid
