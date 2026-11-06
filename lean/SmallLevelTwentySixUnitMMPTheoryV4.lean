module
public meta import SmallLevelTriangularCertificateCommandsV4
public meta import SmallLevelLaurentSourceMatchTacticV4

public import SmallLevelTwentySixGridLaurentRowsV1
public import SmallLevelTwentySixGridLeadingLinearV1
public import SmallLevelTwentySixGridLeadingSupportV1
public import SmallLevelTwentySixGridSignScalingV1
public import SmallLevelTwentySixScaledContinuationMinorV1
public import SmallLevelTwentySixUnitMMMLinearSystemV1
public import SmallLevelTwentySixUnitMMMTheoryV4
public import SmallLevelTwentySixUnitMMPFreeKernelTheoryV4
public import SmallLevelTwentySixUnitMMPKernelV1
public import SmallLevelTwentySixUnitMMPResidualBundleV4
public import SmallLevelTwentySixUnitMMPRowsV1
public import SmallLevelTwentySixWeightZeroChartV1

set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option stderrAsMessages false

/-! Consolidated chapter: SmallLevelTwentySixUnitMMP. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixUnitMMPSourceSelectionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 7000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMP
open SmallLevelTwentySixGrid SmallLevelFourPrimeRates FinitenessRamanujanSum

def selectedSource : Fin 370→GridSource :=
  ![.word 0,.word 1,.word 2,.word 3,.word 4,.word 5,.word 6,.word 7,.word 8,.infinity 0,.word 9,.word 10,.word 11,.word 12,.word 13,.word 14,.word 15,.word 16,.word 17,.word 18,.word 19,.word 20,.word 21,.word 22,.word 23,.word 24,.word 25,.word 26,.word 27,.word 28,.word 29,.word 30,.word 31,.word 32,.word 33,.word 34,.word 35,.word 36,.word 37,.word 38,.word 39,.word 40,.word 41,.word 42,.word 43,.word 44,.word 45,.word 46,.word 47,.word 48,.word 49,.word 50,.word 51,.word 52,.word 53,.word 54,.word 55,.word 56,.word 57,.word 58,.word 59,.word 60,.word 61,.word 62,.word 63,.word 64,.word 65,.word 66,.word 67,.word 68,.word 69,.word 70,.word 71,.word 72,.word 73,.word 74,.word 75,.word 76,.word 77,.word 78,.word 79,.word 80,.word 81,.word 82,.word 83,.word 84,.word 85,.word 86,.word 87,.word 88,.word 89,.word 90,.word 91,.word 92,.word 93,.word 94,.word 95,.word 96,.word 97,.word 98,.word 99,.word 100,.word 101,.word 102,.word 103,.word 104,.word 105,.word 106,.word 107,.word 108,.word 109,.word 110,.word 111,.word 112,.word 113,.word 114,.word 115,.word 116,.word 117,.word 118,.infinity 1,.word 119,.word 120,.word 121,.word 122,.word 123,.word 124,.word 125,.word 126,.word 127,.word 128,.word 129,.word 130,.word 131,.word 132,.word 133,.word 134,.word 135,.word 136,.word 137,.word 138,.word 139,.word 140,.word 141,.word 142,.word 143,.word 144,.word 145,.word 146,.word 147,.word 148,.word 149,.word 150,.word 151,.word 152,.word 153,.word 154,.word 155,.word 156,.word 157,.word 158,.word 159,.word 160,.word 161,.word 162,.word 163,.word 164,.word 165,.word 166,.word 167,.word 168,.word 169,.word 170,.word 171,.word 172,.word 173,.word 174,.word 175,.word 176,.word 177,.word 178,.word 179,.word 180,.word 181,.word 182,.word 183,.word 184,.word 185,.word 186,.word 187,.word 188,.word 189,.word 190,.word 191,.word 192,.word 193,.word 194,.word 195,.word 196,.word 197,.word 198,.word 199,.word 200,.word 201,.word 202,.word 203,.word 204,.word 205,.word 206,.word 207,.word 208,.word 209,.word 210,.word 211,.word 212,.word 213,.word 214,.word 215,.word 216,.word 217,.word 218,.word 219,.word 220,.word 221,.word 222,.word 223,.word 224,.word 225,.word 226,.word 227,.word 228,.word 229,.word 230,.word 231,.word 232,.word 233,.word 234,.entire 0,.taylor 9,.taylor 8,.taylor 10,.taylor 7,.taylor 11,.taylor 6,.taylor 12,.taylor 5,.taylor 13,.taylor 4,.taylor 14,.taylor 3,.taylor 15,.taylor 2,.taylor 16,.taylor 1,.taylor 17,.taylor 0,.entire 1,.taylor 22,.taylor 21,.taylor 23,.taylor 20,.taylor 24,.taylor 19,.taylor 25,.taylor 18,.taylor 26,.taylor 27,.entire 2,.entire 3,.taylor 34,.taylor 33,.taylor 35,.taylor 32,.taylor 36,.taylor 31,.taylor 37,.taylor 30,.taylor 38,.taylor 29,.taylor 39,.taylor 28,.entire 4,.taylor 41,.taylor 40,.taylor 44,.taylor 43,.taylor 45,.taylor 42,.entire 5,.taylor 50,.taylor 49,.taylor 51,.taylor 48,.taylor 52,.taylor 53,.taylor 47,.taylor 54,.taylor 46,.entire 6,.entire 7,.taylor 57,.taylor 56,.taylor 58,.taylor 55,.entire 8,.entire 9,.taylor 61,.taylor 60,.taylor 62,.taylor 59,.taylor 65,.taylor 64,.taylor 66,.taylor 63,.entire 10,.taylor 68,.taylor 67,.taylor 70,.taylor 69,.hecke 0,.hecke 1,.hecke 2,.hecke 3,.hecke 4,.hecke 5,.hecke 6,.hecke 7,.hecke 8,.hecke 9,.hecke 10,.hecke 11,.hecke 12,.hecke 13,.hecke 14,.hecke 15,.hecke 16,.hecke 17,.hecke 18,.hecke 19,.hecke 20,.hecke 21,.hecke 22,.hecke 23,.hecke 24,.hecke 25,.hecke 26,.hecke 27,.hecke 28,.hecke 29,.hecke 30,.hecke 31,.hecke 32,.hecke 33,.hecke 34,.hecke 35,.hecke 36,.hecke 37,.hecke 38,.hecke 39,.hecke 40,.hecke 41,.hecke 42,.hecke 43,.hecke 44,.hecke 45,.hecke 46,.hecke 47,.hecke 48,.hecke 49,.hecke 50]

end SmallLevelTwentySixUnitMMP
end
end

/-! ## SmallLevelTwentySixUnitMMPSourceMatchBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 7000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixUnitMMP
open SmallLevelTwentySixGrid SmallLevelFourPrimeRates FinitenessRamanujanSum

compact_elimination_proof theorem source_match_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 0=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 0) := by
  match_laurent_source sourceRowsPart0 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 0=(0:Fin 780) from rfl,
    show gridGroupTarget 0=(765:Fin 780) from rfl,
    show gridGroupSource 0=(23:Fin 27) from rfl,
    show sourceWord 23=[(3,false),(0,false),(0,false)] from rfl,
    show groupPowers 0=(3, 0, 1, 0) from rfl]

compact_elimination_proof theorem source_match_1 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 1=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 1) := by
  match_laurent_source sourceRowsPart0 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 1=(240:Fin 780) from rfl,
    show gridGroupTarget 1=(767:Fin 780) from rfl,
    show gridGroupSource 1=(23:Fin 27) from rfl,
    show sourceWord 23=[(3,false),(0,false),(0,false)] from rfl,
    show groupPowers 1=(3, 2, -1, 2) from rfl]

compact_elimination_proof theorem source_match_2 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 2=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 2) := by
  match_laurent_source sourceRowsPart0 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 2=(390:Fin 780) from rfl,
    show gridGroupTarget 2=(768:Fin 780) from rfl,
    show gridGroupSource 2=(23:Fin 27) from rfl,
    show sourceWord 23=[(3,false),(0,false),(0,false)] from rfl,
    show groupPowers 2=(-1, 0, 1, 2) from rfl]

compact_elimination_proof theorem source_match_3 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 3=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 3) := by
  match_laurent_source sourceRowsPart0 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 3=(0:Fin 780) from rfl,
    show gridGroupTarget 3=(750:Fin 780) from rfl,
    show gridGroupSource 3=(22:Fin 27) from rfl,
    show sourceWord 22=[(3,false),(0,false)] from rfl,
    show groupPowers 3=(1, 0, 1, 0) from rfl]

compact_elimination_proof theorem source_match_4 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 4=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 4) := by
  match_laurent_source sourceRowsPart0 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 4=(120:Fin 780) from rfl,
    show gridGroupTarget 4=(754:Fin 780) from rfl,
    show gridGroupSource 4=(22:Fin 27) from rfl,
    show sourceWord 22=[(3,false),(0,false)] from rfl,
    show groupPowers 4=(1, 2, -1, 2) from rfl]

compact_elimination_proof theorem source_match_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 5=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 5) := by
  match_laurent_source sourceRowsPart0 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 5=(156:Fin 780) from rfl,
    show gridGroupTarget 5=(755:Fin 780) from rfl,
    show gridGroupSource 5=(22:Fin 27) from rfl,
    show sourceWord 22=[(3,false),(0,false)] from rfl,
    show groupPowers 5=(3, 2, 1, -2) from rfl]

compact_elimination_proof theorem source_match_6 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 6=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 6) := by
  match_laurent_source sourceRowsPart0 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 6=(195:Fin 780) from rfl,
    show gridGroupTarget 6=(756:Fin 780) from rfl,
    show gridGroupSource 6=(22:Fin 27) from rfl,
    show sourceWord 22=[(3,false),(0,false)] from rfl,
    show groupPowers 6=(-3, 0, 1, 2) from rfl]

compact_elimination_proof theorem source_match_7 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 7=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 7) := by
  match_laurent_source sourceRowsPart0 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 7=(390:Fin 780) from rfl,
    show gridGroupTarget 7=(760:Fin 780) from rfl,
    show gridGroupSource 7=(22:Fin 27) from rfl,
    show sourceWord 22=[(3,false),(0,false)] from rfl,
    show groupPowers 7=(-1, 2, 1, 0) from rfl]

compact_elimination_proof theorem source_match_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 8=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 8) := by
  match_laurent_source sourceRowsPart0 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 8=(520:Fin 780) from rfl,
    show gridGroupTarget 8=(762:Fin 780) from rfl,
    show gridGroupSource 8=(22:Fin 27) from rfl,
    show sourceWord 22=[(3,false),(0,false)] from rfl,
    show groupPowers 8=(1, -2, 1, 2) from rfl]

compact_elimination_proof theorem source_match_9 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 9=laurentRows X Y Z W (-1) (-1) (1) a b v (.infinity 0) := by
  match_laurent_source sourceRowsPart0 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridInfinityIndex 0=(0:Fin 780) from rfl]

compact_elimination_proof theorem source_match_10 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 10=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 9) := by
  match_laurent_source sourceRowsPart0 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 9=(1:Fin 780) from rfl,
    show gridGroupTarget 9=(0:Fin 780) from rfl,
    show gridGroupSource 9=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 9=(-3, -2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_11 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 11=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 10) := by
  match_laurent_source sourceRowsPart0 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 10=(2:Fin 780) from rfl,
    show gridGroupTarget 10=(0:Fin 780) from rfl,
    show gridGroupSource 10=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 10=(-1, -2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_12 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 12=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 11) := by
  match_laurent_source sourceRowsPart0 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 11=(3:Fin 780) from rfl,
    show gridGroupTarget 11=(0:Fin 780) from rfl,
    show gridGroupSource 11=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 11=(-3, 0, -1, -2) from rfl]

compact_elimination_proof theorem source_match_13 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 13=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 12) := by
  match_laurent_source sourceRowsPart0 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 12=(4:Fin 780) from rfl,
    show gridGroupTarget 12=(390:Fin 780) from rfl,
    show gridGroupSource 12=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 12=(1, -2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_14 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 14=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 13) := by
  match_laurent_source sourceRowsPart0 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 13=(5:Fin 780) from rfl,
    show gridGroupTarget 13=(0:Fin 780) from rfl,
    show gridGroupSource 13=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 13=(-3, -2, -1, 0) from rfl]

compact_elimination_proof theorem source_match_15 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 15=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 14) := by
  match_laurent_source sourceRowsPart0 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 14=(6:Fin 780) from rfl,
    show gridGroupTarget 14=(0:Fin 780) from rfl,
    show gridGroupSource 14=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 14=(-1, 0, -1, -2) from rfl]

compact_elimination_proof theorem source_match_16 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 16=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 15) := by
  match_laurent_source sourceRowsPart1 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 15=(8:Fin 780) from rfl,
    show gridGroupTarget 15=(195:Fin 780) from rfl,
    show gridGroupSource 15=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 15=(3, -2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_17 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 17=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 16) := by
  match_laurent_source sourceRowsPart1 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 16=(9:Fin 780) from rfl,
    show gridGroupTarget 16=(520:Fin 780) from rfl,
    show gridGroupSource 16=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 16=(-3, 2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_18 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 18=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 17) := by
  match_laurent_source sourceRowsPart1 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 17=(10:Fin 780) from rfl,
    show gridGroupTarget 17=(0:Fin 780) from rfl,
    show gridGroupSource 17=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 17=(-1, -2, -1, 0) from rfl]

compact_elimination_proof theorem source_match_19 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 19=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 18) := by
  match_laurent_source sourceRowsPart1 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 18=(12:Fin 780) from rfl,
    show gridGroupTarget 18=(390:Fin 780) from rfl,
    show gridGroupSource 18=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 18=(1, 0, -1, -2) from rfl]

compact_elimination_proof theorem source_match_20 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 20=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 19) := by
  match_laurent_source sourceRowsPart1 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 19=(13:Fin 780) from rfl,
    show gridGroupTarget 19=(540:Fin 780) from rfl,
    show gridGroupSource 19=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 19=(-3, -2, 1, -2) from rfl]

compact_elimination_proof theorem source_match_21 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 21=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 20) := by
  match_laurent_source sourceRowsPart1 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 20=(15:Fin 780) from rfl,
    show gridGroupTarget 20=(0:Fin 780) from rfl,
    show gridGroupSource 20=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 20=(-3, 0, -1, 0) from rfl]

compact_elimination_proof theorem source_match_22 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 22=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 21) := by
  match_laurent_source sourceRowsPart1 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 21=(18:Fin 780) from rfl,
    show gridGroupTarget 21=(260:Fin 780) from rfl,
    show gridGroupSource 21=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 21=(-1, 2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_23 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 23=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 22) := by
  match_laurent_source sourceRowsPart1 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 22=(20:Fin 780) from rfl,
    show gridGroupTarget 22=(390:Fin 780) from rfl,
    show gridGroupSource 22=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 22=(1, -2, -1, 0) from rfl]

compact_elimination_proof theorem source_match_24 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 24=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 23) := by
  match_laurent_source sourceRowsPart1 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 23=(24:Fin 780) from rfl,
    show gridGroupTarget 23=(585:Fin 780) from rfl,
    show gridGroupSource 23=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 23=(3, 0, -1, -2) from rfl]

compact_elimination_proof theorem source_match_25 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 25=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 24) := by
  match_laurent_source sourceRowsPart1 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 24=(25:Fin 780) from rfl,
    show gridGroupTarget 24=(624:Fin 780) from rfl,
    show gridGroupSource 24=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 24=(-3, -2, -1, 2) from rfl]

compact_elimination_proof theorem source_match_26 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 26=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 25) := by
  match_laurent_source sourceRowsPart1 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 25=(26:Fin 780) from rfl,
    show gridGroupTarget 25=(660:Fin 780) from rfl,
    show gridGroupSource 25=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 25=(-1, -2, 1, -2) from rfl]

compact_elimination_proof theorem source_match_27 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 27=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 26) := by
  match_laurent_source sourceRowsPart1 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 26=(30:Fin 780) from rfl,
    show gridGroupTarget 26=(0:Fin 780) from rfl,
    show gridGroupSource 26=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 26=(-1, 0, -1, 0) from rfl]

compact_elimination_proof theorem source_match_28 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 28=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 27) := by
  match_laurent_source sourceRowsPart1 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 27=(36:Fin 780) from rfl,
    show gridGroupTarget 27=(130:Fin 780) from rfl,
    show gridGroupSource 27=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 27=(1, 2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_29 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 29=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 28) := by
  match_laurent_source sourceRowsPart1 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 28=(39:Fin 780) from rfl,
    show gridGroupTarget 28=(180:Fin 780) from rfl,
    show gridGroupSource 28=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 28=(-3, 0, 1, -2) from rfl]

compact_elimination_proof theorem source_match_30 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 30=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 29) := by
  match_laurent_source sourceRowsPart1 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 29=(40:Fin 780) from rfl,
    show gridGroupTarget 29=(195:Fin 780) from rfl,
    show gridGroupSource 29=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 29=(3, -2, -1, 0) from rfl]

compact_elimination_proof theorem source_match_31 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 31=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 30) := by
  match_laurent_source sourceRowsPart1 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 30=(45:Fin 780) from rfl,
    show gridGroupTarget 30=(260:Fin 780) from rfl,
    show gridGroupSource 30=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 30=(-3, 2, -1, 0) from rfl]

compact_elimination_proof theorem source_match_32 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 32=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 31) := by
  match_laurent_source sourceRowsPart2 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 31=(50:Fin 780) from rfl,
    show gridGroupTarget 31=(312:Fin 780) from rfl,
    show gridGroupSource 31=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 31=(-1, -2, -1, 2) from rfl]

compact_elimination_proof theorem source_match_33 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 33=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 32) := by
  match_laurent_source sourceRowsPart2 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 32=(52:Fin 780) from rfl,
    show gridGroupTarget 32=(330:Fin 780) from rfl,
    show gridGroupSource 32=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 32=(1, -2, 1, -2) from rfl]

compact_elimination_proof theorem source_match_34 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 34=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 33) := by
  match_laurent_source sourceRowsPart2 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 33=(60:Fin 780) from rfl,
    show gridGroupTarget 33=(390:Fin 780) from rfl,
    show gridGroupSource 33=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 33=(1, 0, -1, 0) from rfl]

compact_elimination_proof theorem source_match_35 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 35=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 34) := by
  match_laurent_source sourceRowsPart2 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 34=(65:Fin 780) from rfl,
    show gridGroupTarget 34=(420:Fin 780) from rfl,
    show gridGroupSource 34=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 34=(-3, -2, 1, 0) from rfl]

compact_elimination_proof theorem source_match_36 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 36=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 35) := by
  match_laurent_source sourceRowsPart2 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 35=(72:Fin 780) from rfl,
    show gridGroupTarget 35=(455:Fin 780) from rfl,
    show gridGroupSource 35=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 35=(3, 2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_37 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 37=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 36) := by
  match_laurent_source sourceRowsPart2 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 36=(75:Fin 780) from rfl,
    show gridGroupTarget 36=(468:Fin 780) from rfl,
    show gridGroupSource 36=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 36=(-3, 0, -1, 2) from rfl]

compact_elimination_proof theorem source_match_38 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 38=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 37) := by
  match_laurent_source sourceRowsPart2 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 37=(78:Fin 780) from rfl,
    show gridGroupTarget 37=(480:Fin 780) from rfl,
    show gridGroupSource 37=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 37=(-1, 0, 1, -2) from rfl]

compact_elimination_proof theorem source_match_39 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 39=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 38) := by
  match_laurent_source sourceRowsPart2 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 38=(90:Fin 780) from rfl,
    show gridGroupTarget 38=(520:Fin 780) from rfl,
    show gridGroupSource 38=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 38=(-1, 2, -1, 0) from rfl]

compact_elimination_proof theorem source_match_40 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 40=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 39) := by
  match_laurent_source sourceRowsPart2 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 39=(100:Fin 780) from rfl,
    show gridGroupTarget 39=(546:Fin 780) from rfl,
    show gridGroupSource 39=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 39=(1, -2, -1, 2) from rfl]

compact_elimination_proof theorem source_match_41 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 41=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 40) := by
  match_laurent_source sourceRowsPart2 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 40=(104:Fin 780) from rfl,
    show gridGroupTarget 40=(555:Fin 780) from rfl,
    show gridGroupSource 40=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 40=(3, -2, 1, -2) from rfl]

compact_elimination_proof theorem source_match_42 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 42=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 41) := by
  match_laurent_source sourceRowsPart2 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 41=(117:Fin 780) from rfl,
    show gridGroupTarget 41=(580:Fin 780) from rfl,
    show gridGroupSource 41=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 41=(-3, 2, 1, -2) from rfl]

compact_elimination_proof theorem source_match_43 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 43=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 42) := by
  match_laurent_source sourceRowsPart2 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 42=(120:Fin 780) from rfl,
    show gridGroupTarget 42=(585:Fin 780) from rfl,
    show gridGroupSource 42=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 42=(3, 0, -1, 0) from rfl]

compact_elimination_proof theorem source_match_44 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 44=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 43) := by
  match_laurent_source sourceRowsPart2 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 43=(130:Fin 780) from rfl,
    show gridGroupTarget 43=(600:Fin 780) from rfl,
    show gridGroupSource 43=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 43=(-1, -2, 1, 0) from rfl]

compact_elimination_proof theorem source_match_45 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 45=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 44) := by
  match_laurent_source sourceRowsPart2 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 44=(150:Fin 780) from rfl,
    show gridGroupTarget 44=(624:Fin 780) from rfl,
    show gridGroupSource 44=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 44=(-1, 0, -1, 2) from rfl]

compact_elimination_proof theorem source_match_46 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 46=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 45) := by
  match_laurent_source sourceRowsPart2 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 45=(156:Fin 780) from rfl,
    show gridGroupTarget 45=(630:Fin 780) from rfl,
    show gridGroupSource 45=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 45=(1, 0, 1, -2) from rfl]

compact_elimination_proof theorem source_match_47 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 47=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 46) := by
  match_laurent_source sourceRowsPart2 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 46=(180:Fin 780) from rfl,
    show gridGroupTarget 46=(650:Fin 780) from rfl,
    show gridGroupSource 46=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 46=(1, 2, -1, 0) from rfl]

compact_elimination_proof theorem source_match_48 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 48=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 47) := by
  match_laurent_source sourceRowsPart3 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 47=(195:Fin 780) from rfl,
    show gridGroupTarget 47=(660:Fin 780) from rfl,
    show gridGroupSource 47=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 47=(-3, 0, 1, 0) from rfl]

compact_elimination_proof theorem source_match_49 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 49=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 48) := by
  match_laurent_source sourceRowsPart3 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 48=(200:Fin 780) from rfl,
    show gridGroupTarget 48=(663:Fin 780) from rfl,
    show gridGroupSource 48=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 48=(3, -2, -1, 2) from rfl]

compact_elimination_proof theorem source_match_50 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 50=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 49) := by
  match_laurent_source sourceRowsPart3 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 49=(225:Fin 780) from rfl,
    show gridGroupTarget 49=(676:Fin 780) from rfl,
    show gridGroupSource 49=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 49=(-3, 2, -1, 2) from rfl]

compact_elimination_proof theorem source_match_51 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 51=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 50) := by
  match_laurent_source sourceRowsPart3 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 50=(234:Fin 780) from rfl,
    show gridGroupTarget 50=(680:Fin 780) from rfl,
    show gridGroupSource 50=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 50=(-1, 2, 1, -2) from rfl]

compact_elimination_proof theorem source_match_52 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 52=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 51) := by
  match_laurent_source sourceRowsPart3 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 51=(260:Fin 780) from rfl,
    show gridGroupTarget 51=(690:Fin 780) from rfl,
    show gridGroupSource 51=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 51=(1, -2, 1, 0) from rfl]

compact_elimination_proof theorem source_match_53 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 53=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 52) := by
  match_laurent_source sourceRowsPart3 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 52=(300:Fin 780) from rfl,
    show gridGroupTarget 52=(702:Fin 780) from rfl,
    show gridGroupSource 52=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 52=(1, 0, -1, 2) from rfl]

compact_elimination_proof theorem source_match_54 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 54=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 53) := by
  match_laurent_source sourceRowsPart3 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 53=(312:Fin 780) from rfl,
    show gridGroupTarget 53=(705:Fin 780) from rfl,
    show gridGroupSource 53=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 53=(3, 0, 1, -2) from rfl]

compact_elimination_proof theorem source_match_55 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 55=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 54) := by
  match_laurent_source sourceRowsPart3 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 54=(325:Fin 780) from rfl,
    show gridGroupTarget 54=(708:Fin 780) from rfl,
    show gridGroupSource 54=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 54=(-3, -2, 1, 2) from rfl]

compact_elimination_proof theorem source_match_56 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 56=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 55) := by
  match_laurent_source sourceRowsPart3 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 55=(360:Fin 780) from rfl,
    show gridGroupTarget 55=(715:Fin 780) from rfl,
    show gridGroupSource 55=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 55=(3, 2, -1, 0) from rfl]

compact_elimination_proof theorem source_match_57 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 57=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 56) := by
  match_laurent_source sourceRowsPart3 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 56=(390:Fin 780) from rfl,
    show gridGroupTarget 56=(720:Fin 780) from rfl,
    show gridGroupSource 56=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 56=(-1, 0, 1, 0) from rfl]

compact_elimination_proof theorem source_match_58 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 58=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 57) := by
  match_laurent_source sourceRowsPart3 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 57=(450:Fin 780) from rfl,
    show gridGroupTarget 57=(728:Fin 780) from rfl,
    show gridGroupSource 57=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 57=(-1, 2, -1, 2) from rfl]

compact_elimination_proof theorem source_match_59 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 59=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 58) := by
  match_laurent_source sourceRowsPart3 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 58=(468:Fin 780) from rfl,
    show gridGroupTarget 58=(730:Fin 780) from rfl,
    show gridGroupSource 58=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 58=(1, 2, 1, -2) from rfl]

compact_elimination_proof theorem source_match_60 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 60=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 59) := by
  match_laurent_source sourceRowsPart3 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 59=(520:Fin 780) from rfl,
    show gridGroupTarget 59=(735:Fin 780) from rfl,
    show gridGroupSource 59=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 59=(3, -2, 1, 0) from rfl]

compact_elimination_proof theorem source_match_61 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 61=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 60) := by
  match_laurent_source sourceRowsPart3 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 60=(585:Fin 780) from rfl,
    show gridGroupTarget 60=(740:Fin 780) from rfl,
    show gridGroupSource 60=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 60=(-3, 2, 1, 0) from rfl]

compact_elimination_proof theorem source_match_62 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 62=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 61) := by
  match_laurent_source sourceRowsPart3 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 61=(600:Fin 780) from rfl,
    show gridGroupTarget 61=(741:Fin 780) from rfl,
    show gridGroupSource 61=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 61=(3, 0, -1, 2) from rfl]

compact_elimination_proof theorem source_match_63 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 63=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 62) := by
  match_laurent_source sourceRowsPart3 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 62=(650:Fin 780) from rfl,
    show gridGroupTarget 62=(744:Fin 780) from rfl,
    show gridGroupSource 62=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,
    show groupPowers 62=(-1, -2, 1, 2) from rfl]

compact_elimination_proof theorem source_match_64 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 64=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 63) := by
  match_laurent_source sourceRowsPart4 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 63=(770:Fin 780) from rfl,
    show gridGroupTarget 63=(0:Fin 780) from rfl,
    show gridGroupSource 63=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,
    show groupPowers 63=(-1, -2, -1, 0) from rfl]

compact_elimination_proof theorem source_match_65 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 65=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 64) := by
  match_laurent_source sourceRowsPart4 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 64=(771:Fin 780) from rfl,
    show gridGroupTarget 64=(260:Fin 780) from rfl,
    show gridGroupSource 64=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,
    show groupPowers 64=(-3, 2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_66 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 66=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 65) := by
  match_laurent_source sourceRowsPart4 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 65=(772:Fin 780) from rfl,
    show gridGroupTarget 65=(585:Fin 780) from rfl,
    show gridGroupSource 65=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,
    show groupPowers 65=(3, -2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_67 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 67=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 66) := by
  match_laurent_source sourceRowsPart4 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 66=(774:Fin 780) from rfl,
    show gridGroupTarget 66=(0:Fin 780) from rfl,
    show gridGroupSource 66=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,
    show groupPowers 66=(-1, 0, -1, -2) from rfl]

compact_elimination_proof theorem source_match_68 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 68=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 67) := by
  match_laurent_source sourceRowsPart4 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 67=(775:Fin 780) from rfl,
    show gridGroupTarget 67=(0:Fin 780) from rfl,
    show gridGroupSource 67=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,
    show groupPowers 67=(-3, -2, -1, 0) from rfl]

compact_elimination_proof theorem source_match_69 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 69=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 68) := by
  match_laurent_source sourceRowsPart4 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 68=(776:Fin 780) from rfl,
    show gridGroupTarget 68=(390:Fin 780) from rfl,
    show gridGroupSource 68=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,
    show groupPowers 68=(1, -2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_70 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 70=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 69) := by
  match_laurent_source sourceRowsPart4 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 69=(777:Fin 780) from rfl,
    show gridGroupTarget 69=(0:Fin 780) from rfl,
    show gridGroupSource 69=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,
    show groupPowers 69=(-3, 0, -1, -2) from rfl]

compact_elimination_proof theorem source_match_71 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 71=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 70) := by
  match_laurent_source sourceRowsPart4 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 70=(778:Fin 780) from rfl,
    show gridGroupTarget 70=(0:Fin 780) from rfl,
    show gridGroupSource 70=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,
    show groupPowers 70=(-1, -2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_72 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 72=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 71) := by
  match_laurent_source sourceRowsPart4 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 71=(779:Fin 780) from rfl,
    show gridGroupTarget 71=(0:Fin 780) from rfl,
    show gridGroupSource 71=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,
    show groupPowers 71=(-3, -2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_73 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 73=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 72) := by
  match_laurent_source sourceRowsPart4 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 72=(690:Fin 780) from rfl,
    show gridGroupTarget 72=(751:Fin 780) from rfl,
    show gridGroupSource 72=(9:Fin 27) from rfl,
    show sourceWord 9=[(1,true),(0,true),(0,true)] from rfl,
    show groupPowers 72=(2, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_74 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 74=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 73) := by
  match_laurent_source sourceRowsPart4 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 73=(630:Fin 780) from rfl,
    show gridGroupTarget 73=(31:Fin 780) from rfl,
    show gridGroupSource 73=(1:Fin 27) from rfl,
    show sourceWord 1=[(1,false),(0,true),(0,true)] from rfl,
    show groupPowers 73=(2, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_75 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 75=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 74) := by
  match_laurent_source sourceRowsPart4 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 74=(570:Fin 780) from rfl,
    show gridGroupTarget 74=(766:Fin 780) from rfl,
    show gridGroupSource 74=(10:Fin 27) from rfl,
    show sourceWord 10=[(1,true),(1,true),(0,true)] from rfl,
    show groupPowers 74=(0, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_76 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 76=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 75) := by
  match_laurent_source sourceRowsPart4 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 75=(360:Fin 780) from rfl,
    show gridGroupTarget 75=(752:Fin 780) from rfl,
    show gridGroupSource 75=(8:Fin 27) from rfl,
    show sourceWord 8=[(1,true),(0,true)] from rfl,
    show groupPowers 75=(0, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_77 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 77=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 76) := by
  match_laurent_source sourceRowsPart4 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 76=(510:Fin 780) from rfl,
    show gridGroupTarget 76=(753:Fin 780) from rfl,
    show gridGroupSource 76=(8:Fin 27) from rfl,
    show sourceWord 8=[(1,true),(0,true)] from rfl,
    show groupPowers 76=(2, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_78 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 78=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 77) := by
  match_laurent_source sourceRowsPart4 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 77=(710:Fin 780) from rfl,
    show gridGroupTarget 77=(759:Fin 780) from rfl,
    show gridGroupSource 77=(8:Fin 27) from rfl,
    show sourceWord 8=[(1,true),(0,true)] from rfl,
    show groupPowers 77=(2, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_79 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 79=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 78) := by
  match_laurent_source sourceRowsPart4 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 78=(300:Fin 780) from rfl,
    show gridGroupTarget 78=(32:Fin 780) from rfl,
    show gridGroupSource 78=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,
    show groupPowers 78=(0, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_80 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 80=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 79) := by
  match_laurent_source sourceRowsPart5 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 79=(450:Fin 780) from rfl,
    show gridGroupTarget 79=(33:Fin 780) from rfl,
    show gridGroupSource 79=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,
    show groupPowers 79=(2, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_81 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 81=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 80) := by
  match_laurent_source sourceRowsPart5 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 80=(570:Fin 780) from rfl,
    show gridGroupTarget 80=(35:Fin 780) from rfl,
    show gridGroupSource 80=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,
    show groupPowers 80=(2, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_82 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 82=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 81) := by
  match_laurent_source sourceRowsPart5 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 81=(675:Fin 780) from rfl,
    show gridGroupTarget 81=(42:Fin 780) from rfl,
    show gridGroupSource 81=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,
    show groupPowers 81=(-2, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_83 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 83=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 82) := by
  match_laurent_source sourceRowsPart5 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 82=(700:Fin 780) from rfl,
    show gridGroupTarget 82=(48:Fin 780) from rfl,
    show gridGroupSource 82=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,
    show groupPowers 82=(0, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_84 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 84=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 83) := by
  match_laurent_source sourceRowsPart5 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 83=(714:Fin 780) from rfl,
    show gridGroupTarget 83=(55:Fin 780) from rfl,
    show gridGroupSource 83=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,
    show groupPowers 83=(2, 2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_85 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 85=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 84) := by
  match_laurent_source sourceRowsPart5 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 84=(725:Fin 780) from rfl,
    show gridGroupTarget 84=(66:Fin 780) from rfl,
    show gridGroupSource 84=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,
    show groupPowers 84=(-2, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_86 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 86=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 85) := by
  match_laurent_source sourceRowsPart5 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 85=(732:Fin 780) from rfl,
    show gridGroupTarget 85=(80:Fin 780) from rfl,
    show gridGroupSource 85=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,
    show groupPowers 85=(0, 2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_87 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 87=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 86) := by
  match_laurent_source sourceRowsPart5 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 86=(738:Fin 780) from rfl,
    show gridGroupTarget 86=(105:Fin 780) from rfl,
    show gridGroupSource 86=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,
    show groupPowers 86=(2, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_88 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 88=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 87) := by
  match_laurent_source sourceRowsPart5 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 87=(745:Fin 780) from rfl,
    show gridGroupTarget 87=(210:Fin 780) from rfl,
    show gridGroupSource 87=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,
    show groupPowers 87=(-2, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_89 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 89=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 88) := by
  match_laurent_source sourceRowsPart5 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 88=(747:Fin 780) from rfl,
    show gridGroupTarget 88=(330:Fin 780) from rfl,
    show gridGroupSource 88=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,
    show groupPowers 88=(-2, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_90 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 90=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 89) := by
  match_laurent_source sourceRowsPart5 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 89=(748:Fin 780) from rfl,
    show gridGroupTarget 89=(480:Fin 780) from rfl,
    show gridGroupSource 89=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,
    show groupPowers 89=(0, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_91 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 91=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 90) := by
  match_laurent_source sourceRowsPart5 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 90=(749:Fin 780) from rfl,
    show gridGroupTarget 90=(150:Fin 780) from rfl,
    show gridGroupSource 90=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,
    show groupPowers 90=(-2, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_92 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 92=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 91) := by
  match_laurent_source sourceRowsPart5 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 91=(540:Fin 780) from rfl,
    show gridGroupTarget 91=(16:Fin 780) from rfl,
    show gridGroupSource 91=(2:Fin 27) from rfl,
    show sourceWord 2=[(1,false),(1,false),(0,true)] from rfl,
    show groupPowers 91=(0, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_93 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 93=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 92) := by
  match_laurent_source sourceRowsPart5 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 92=(764:Fin 780) from rfl,
    show gridGroupTarget 92=(240:Fin 780) from rfl,
    show gridGroupSource 92=(2:Fin 27) from rfl,
    show sourceWord 2=[(1,false),(1,false),(0,true)] from rfl,
    show groupPowers 92=(0, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_94 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 94=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 93) := by
  match_laurent_source sourceRowsPart5 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 93=(11:Fin 780) from rfl,
    show gridGroupTarget 93=(670:Fin 780) from rfl,
    show gridGroupSource 93=(11:Fin 27) from rfl,
    show sourceWord 11=[(1,true),(1,true),(1,true)] from rfl,
    show groupPowers 93=(-2, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_95 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 95=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 94) := by
  match_laurent_source sourceRowsPart5 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 94=(14:Fin 780) from rfl,
    show gridGroupTarget 94=(745:Fin 780) from rfl,
    show gridGroupSource 94=(11:Fin 27) from rfl,
    show sourceWord 11=[(1,true),(1,true),(1,true)] from rfl,
    show groupPowers 94=(2, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_96 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 96=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 95) := by
  match_laurent_source sourceRowsPart6 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 95=(110:Fin 780) from rfl,
    show gridGroupTarget 95=(769:Fin 780) from rfl,
    show gridGroupSource 95=(11:Fin 27) from rfl,
    show sourceWord 11=[(1,true),(1,true),(1,true)] from rfl,
    show groupPowers 95=(2, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_97 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 97=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 96) := by
  match_laurent_source sourceRowsPart6 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 96=(21:Fin 780) from rfl,
    show gridGroupTarget 96=(70:Fin 780) from rfl,
    show gridGroupSource 96=(7:Fin 27) from rfl,
    show sourceWord 7=[(1,true)] from rfl,
    show groupPowers 96=(-2, 2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_98 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 98=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 97) := by
  match_laurent_source sourceRowsPart6 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 97=(27:Fin 780) from rfl,
    show gridGroupTarget 97=(270:Fin 780) from rfl,
    show gridGroupSource 97=(7:Fin 27) from rfl,
    show sourceWord 7=[(1,true)] from rfl,
    show groupPowers 97=(-2, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_99 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 99=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 98) := by
  match_laurent_source sourceRowsPart6 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 98=(28:Fin 780) from rfl,
    show gridGroupTarget 98=(420:Fin 780) from rfl,
    show gridGroupSource 98=(7:Fin 27) from rfl,
    show sourceWord 7=[(1,true)] from rfl,
    show groupPowers 98=(0, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_100 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 100=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 99) := by
  match_laurent_source sourceRowsPart6 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 99=(29:Fin 780) from rfl,
    show gridGroupTarget 99=(90:Fin 780) from rfl,
    show gridGroupSource 99=(7:Fin 27) from rfl,
    show sourceWord 7=[(1,true)] from rfl,
    show groupPowers 99=(-2, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_101 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 101=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 100) := by
  match_laurent_source sourceRowsPart6 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 100=(180:Fin 780) from rfl,
    show gridGroupTarget 100=(721:Fin 780) from rfl,
    show gridGroupSource 100=(18:Fin 27) from rfl,
    show sourceWord 18=[(2,false),(0,true),(0,true)] from rfl,
    show groupPowers 100=(3, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_102 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 102=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 101) := by
  match_laurent_source sourceRowsPart6 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 101=(300:Fin 780) from rfl,
    show gridGroupTarget 101=(722:Fin 780) from rfl,
    show gridGroupSource 101=(17:Fin 27) from rfl,
    show sourceWord 17=[(2,false),(0,true)] from rfl,
    show groupPowers 101=(1, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_103 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 103=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 102) := by
  match_laurent_source sourceRowsPart6 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 102=(600:Fin 780) from rfl,
    show gridGroupTarget 102=(723:Fin 780) from rfl,
    show gridGroupSource 102=(17:Fin 27) from rfl,
    show sourceWord 17=[(2,false),(0,true)] from rfl,
    show groupPowers 102=(3, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_104 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 104=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 103) := by
  match_laurent_source sourceRowsPart6 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 103=(750:Fin 780) from rfl,
    show gridGroupTarget 103=(724:Fin 780) from rfl,
    show gridGroupSource 103=(17:Fin 27) from rfl,
    show sourceWord 17=[(2,false),(0,true)] from rfl,
    show groupPowers 103=(-1, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_105 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 105=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 104) := by
  match_laurent_source sourceRowsPart6 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 104=(240:Fin 780) from rfl,
    show gridGroupTarget 104=(62:Fin 780) from rfl,
    show gridGroupSource 104=(6:Fin 27) from rfl,
    show sourceWord 6=[(1,false),(2,false),(0,true)] from rfl,
    show groupPowers 104=(1, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_106 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 106=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 105) := by
  match_laurent_source sourceRowsPart6 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 105=(540:Fin 780) from rfl,
    show gridGroupTarget 105=(63:Fin 780) from rfl,
    show gridGroupSource 105=(6:Fin 27) from rfl,
    show sourceWord 6=[(1,false),(2,false),(0,true)] from rfl,
    show groupPowers 105=(3, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_107 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 107=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 106) := by
  match_laurent_source sourceRowsPart6 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 106=(690:Fin 780) from rfl,
    show gridGroupTarget 106=(64:Fin 780) from rfl,
    show gridGroupSource 106=(6:Fin 27) from rfl,
    show sourceWord 6=[(1,false),(2,false),(0,true)] from rfl,
    show groupPowers 106=(-1, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_108 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 108=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 107) := by
  match_laurent_source sourceRowsPart6 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 107=(324:Fin 780) from rfl,
    show gridGroupTarget 107=(769:Fin 780) from rfl,
    show gridGroupSource 107=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 107=(3, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_109 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 109=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 108) := by
  match_laurent_source sourceRowsPart6 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 108=(360:Fin 780) from rfl,
    show gridGroupTarget 108=(770:Fin 780) from rfl,
    show gridGroupSource 108=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 108=(1, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_110 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 110=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 109) := by
  match_laurent_source sourceRowsPart6 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 109=(372:Fin 780) from rfl,
    show gridGroupTarget 109=(771:Fin 780) from rfl,
    show gridGroupSource 109=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 109=(3, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_111 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 111=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 110) := by
  match_laurent_source sourceRowsPart6 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 110=(378:Fin 780) from rfl,
    show gridGroupTarget 110=(772:Fin 780) from rfl,
    show gridGroupSource 110=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 110=(-1, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_112 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 112=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 111) := by
  match_laurent_source sourceRowsPart7 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 111=(384:Fin 780) from rfl,
    show gridGroupTarget 111=(774:Fin 780) from rfl,
    show gridGroupSource 111=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 111=(1, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_113 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 113=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 112) := by
  match_laurent_source sourceRowsPart7 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 112=(387:Fin 780) from rfl,
    show gridGroupTarget 112=(776:Fin 780) from rfl,
    show gridGroupSource 112=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 112=(-3, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_114 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 114=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 113) := by
  match_laurent_source sourceRowsPart7 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 113=(388:Fin 780) from rfl,
    show gridGroupTarget 113=(777:Fin 780) from rfl,
    show gridGroupSource 113=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 113=(3, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_115 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 115=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 114) := by
  match_laurent_source sourceRowsPart7 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 114=(390:Fin 780) from rfl,
    show gridGroupTarget 114=(0:Fin 780) from rfl,
    show gridGroupSource 114=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 114=(-1, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_116 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 116=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 115) := by
  match_laurent_source sourceRowsPart7 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 115=(392:Fin 780) from rfl,
    show gridGroupTarget 115=(6:Fin 780) from rfl,
    show gridGroupSource 115=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 115=(1, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_117 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 117=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 116) := by
  match_laurent_source sourceRowsPart7 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 116=(393:Fin 780) from rfl,
    show gridGroupTarget 116=(12:Fin 780) from rfl,
    show gridGroupSource 116=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 116=(-3, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_118 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 118=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 117) := by
  match_laurent_source sourceRowsPart7 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 117=(394:Fin 780) from rfl,
    show gridGroupTarget 117=(24:Fin 780) from rfl,
    show gridGroupSource 117=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 117=(-1, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_119 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 119=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 118) := by
  match_laurent_source sourceRowsPart7 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 118=(395:Fin 780) from rfl,
    show gridGroupTarget 118=(60:Fin 780) from rfl,
    show gridGroupSource 118=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 118=(-3, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_120 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 120=laurentRows X Y Z W (-1) (-1) (1) a b v (.infinity 1) := by
  match_laurent_source sourceRowsPart7 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridInfinityIndex 1=(396:Fin 780) from rfl]

compact_elimination_proof theorem source_match_121 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 121=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 119) := by
  match_laurent_source sourceRowsPart7 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 119=(397:Fin 780) from rfl,
    show gridGroupTarget 119=(696:Fin 780) from rfl,
    show gridGroupSource 119=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 119=(-3, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_122 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 122=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 120) := by
  match_laurent_source sourceRowsPart7 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 120=(398:Fin 780) from rfl,
    show gridGroupTarget 120=(732:Fin 780) from rfl,
    show gridGroupSource 120=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 120=(-1, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_123 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 123=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 121) := by
  match_laurent_source sourceRowsPart7 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 121=(399:Fin 780) from rfl,
    show gridGroupTarget 121=(744:Fin 780) from rfl,
    show gridGroupSource 121=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 121=(-3, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_124 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 124=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 122) := by
  match_laurent_source sourceRowsPart7 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 122=(400:Fin 780) from rfl,
    show gridGroupTarget 122=(750:Fin 780) from rfl,
    show gridGroupSource 122=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 122=(1, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_125 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 125=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 123) := by
  match_laurent_source sourceRowsPart7 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 123=(402:Fin 780) from rfl,
    show gridGroupTarget 123=(756:Fin 780) from rfl,
    show gridGroupSource 123=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 123=(-1, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_126 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 126=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 124) := by
  match_laurent_source sourceRowsPart7 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 124=(404:Fin 780) from rfl,
    show gridGroupTarget 124=(759:Fin 780) from rfl,
    show gridGroupSource 124=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 124=(3, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_127 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 127=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 125) := by
  match_laurent_source sourceRowsPart7 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 125=(405:Fin 780) from rfl,
    show gridGroupTarget 125=(760:Fin 780) from rfl,
    show gridGroupSource 125=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 125=(-3, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_128 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 128=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 126) := by
  match_laurent_source sourceRowsPart8 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 126=(408:Fin 780) from rfl,
    show gridGroupTarget 126=(762:Fin 780) from rfl,
    show gridGroupSource 126=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 126=(1, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_129 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 129=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 127) := by
  match_laurent_source sourceRowsPart8 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 127=(414:Fin 780) from rfl,
    show gridGroupTarget 127=(764:Fin 780) from rfl,
    show gridGroupSource 127=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 127=(-1, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_130 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 130=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 128) := by
  match_laurent_source sourceRowsPart8 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 128=(420:Fin 780) from rfl,
    show gridGroupTarget 128=(765:Fin 780) from rfl,
    show gridGroupSource 128=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 128=(3, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_131 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 131=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 129) := by
  match_laurent_source sourceRowsPart8 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 129=(432:Fin 780) from rfl,
    show gridGroupTarget 129=(766:Fin 780) from rfl,
    show gridGroupSource 129=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 129=(1, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_132 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 132=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 130) := by
  match_laurent_source sourceRowsPart8 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 130=(468:Fin 780) from rfl,
    show gridGroupTarget 130=(767:Fin 780) from rfl,
    show gridGroupSource 130=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 130=(3, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_133 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 133=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 131) := by
  match_laurent_source sourceRowsPart8 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 131=(200:Fin 780) from rfl,
    show gridGroupTarget 131=(761:Fin 780) from rfl,
    show gridGroupSource 131=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,
    show groupPowers 131=(3, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_134 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 134=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 132) := by
  match_laurent_source sourceRowsPart8 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 132=(300:Fin 780) from rfl,
    show gridGroupTarget 132=(762:Fin 780) from rfl,
    show gridGroupSource 132=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,
    show groupPowers 132=(1, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_135 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 135=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 133) := by
  match_laurent_source sourceRowsPart8 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 133=(350:Fin 780) from rfl,
    show gridGroupTarget 133=(764:Fin 780) from rfl,
    show gridGroupSource 133=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,
    show groupPowers 133=(-1, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_136 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 136=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 134) := by
  match_laurent_source sourceRowsPart8 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 134=(375:Fin 780) from rfl,
    show gridGroupTarget 134=(768:Fin 780) from rfl,
    show gridGroupSource 134=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,
    show groupPowers 134=(-3, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_137 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 137=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 135) := by
  match_laurent_source sourceRowsPart8 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 135=(380:Fin 780) from rfl,
    show gridGroupTarget 135=(770:Fin 780) from rfl,
    show gridGroupSource 135=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,
    show groupPowers 135=(1, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_138 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 138=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 136) := by
  match_laurent_source sourceRowsPart8 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 136=(401:Fin 780) from rfl,
    show gridGroupTarget 136=(560:Fin 780) from rfl,
    show gridGroupSource 136=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,
    show groupPowers 136=(-3, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_139 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 139=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 137) := by
  match_laurent_source sourceRowsPart8 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 137=(410:Fin 780) from rfl,
    show gridGroupTarget 137=(740:Fin 780) from rfl,
    show gridGroupSource 137=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,
    show groupPowers 137=(-1, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_140 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 140=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 138) := by
  match_laurent_source sourceRowsPart8 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 138=(425:Fin 780) from rfl,
    show gridGroupTarget 138=(752:Fin 780) from rfl,
    show gridGroupSource 138=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,
    show groupPowers 138=(-3, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_141 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 141=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 139) := by
  match_laurent_source sourceRowsPart8 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 139=(440:Fin 780) from rfl,
    show gridGroupTarget 139=(755:Fin 780) from rfl,
    show gridGroupSource 139=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,
    show groupPowers 139=(3, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_142 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 142=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 140) := by
  match_laurent_source sourceRowsPart8 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 140=(450:Fin 780) from rfl,
    show gridGroupTarget 140=(756:Fin 780) from rfl,
    show gridGroupSource 140=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,
    show groupPowers 140=(-1, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_143 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 143=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 141) := by
  match_laurent_source sourceRowsPart8 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 141=(500:Fin 780) from rfl,
    show gridGroupTarget 141=(758:Fin 780) from rfl,
    show gridGroupSource 141=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,
    show groupPowers 141=(1, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_144 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 144=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 142) := by
  match_laurent_source sourceRowsPart9 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 142=(600:Fin 780) from rfl,
    show gridGroupTarget 142=(759:Fin 780) from rfl,
    show gridGroupSource 142=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,
    show groupPowers 142=(3, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_145 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 145=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 143) := by
  match_laurent_source sourceRowsPart9 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 143=(60:Fin 780) from rfl,
    show gridGroupTarget 143=(725:Fin 780) from rfl,
    show gridGroupSource 143=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 143=(3, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_146 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 146=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 144) := by
  match_laurent_source sourceRowsPart9 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 144=(120:Fin 780) from rfl,
    show gridGroupTarget 144=(726:Fin 780) from rfl,
    show gridGroupSource 144=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 144=(1, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_147 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 147=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 145) := by
  match_laurent_source sourceRowsPart9 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 145=(220:Fin 780) from rfl,
    show gridGroupTarget 145=(729:Fin 780) from rfl,
    show gridGroupSource 145=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 145=(3, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_148 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 148=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 146) := by
  match_laurent_source sourceRowsPart9 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 146=(270:Fin 780) from rfl,
    show gridGroupTarget 146=(732:Fin 780) from rfl,
    show gridGroupSource 146=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 146=(-1, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_149 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 149=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 147) := by
  match_laurent_source sourceRowsPart9 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 147=(320:Fin 780) from rfl,
    show gridGroupTarget 147=(738:Fin 780) from rfl,
    show gridGroupSource 147=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 147=(1, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_150 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 150=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 148) := by
  match_laurent_source sourceRowsPart9 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 148=(330:Fin 780) from rfl,
    show gridGroupTarget 148=(740:Fin 780) from rfl,
    show gridGroupSource 148=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 148=(-1, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_151 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 151=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 149) := by
  match_laurent_source sourceRowsPart9 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 149=(345:Fin 780) from rfl,
    show gridGroupTarget 149=(744:Fin 780) from rfl,
    show gridGroupSource 149=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 149=(-3, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_152 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 152=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 150) := by
  match_laurent_source sourceRowsPart9 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 150=(348:Fin 780) from rfl,
    show gridGroupTarget 150=(745:Fin 780) from rfl,
    show gridGroupSource 150=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 150=(3, 2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_153 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 153=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 151) := by
  match_laurent_source sourceRowsPart9 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 151=(370:Fin 780) from rfl,
    show gridGroupTarget 151=(756:Fin 780) from rfl,
    show gridGroupSource 151=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 151=(-1, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_154 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 154=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 152) := by
  match_laurent_source sourceRowsPart9 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 152=(411:Fin 780) from rfl,
    show gridGroupTarget 152=(140:Fin 780) from rfl,
    show gridGroupSource 152=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 152=(-3, 2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_155 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 155=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 153) := by
  match_laurent_source sourceRowsPart9 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 153=(412:Fin 780) from rfl,
    show gridGroupTarget 153=(165:Fin 780) from rfl,
    show gridGroupSource 153=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 153=(3, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_156 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 156=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 154) := by
  match_laurent_source sourceRowsPart9 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 154=(415:Fin 780) from rfl,
    show gridGroupTarget 154=(300:Fin 780) from rfl,
    show gridGroupSource 154=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 154=(-3, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_157 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 157=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 155) := by
  match_laurent_source sourceRowsPart9 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 155=(416:Fin 780) from rfl,
    show gridGroupTarget 155=(390:Fin 780) from rfl,
    show gridGroupSource 155=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 155=(1, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_158 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 158=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 156) := by
  match_laurent_source sourceRowsPart9 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 156=(417:Fin 780) from rfl,
    show gridGroupTarget 156=(540:Fin 780) from rfl,
    show gridGroupSource 156=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 156=(-3, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_159 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 159=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 157) := by
  match_laurent_source sourceRowsPart9 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 157=(418:Fin 780) from rfl,
    show gridGroupTarget 157=(60:Fin 780) from rfl,
    show gridGroupSource 157=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 157=(-1, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_160 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 160=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 158) := by
  match_laurent_source sourceRowsPart10 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 158=(419:Fin 780) from rfl,
    show gridGroupTarget 158=(180:Fin 780) from rfl,
    show gridGroupSource 158=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 158=(-3, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_161 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 161=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 159) := by
  match_laurent_source sourceRowsPart10 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 159=(421:Fin 780) from rfl,
    show gridGroupTarget 159=(480:Fin 780) from rfl,
    show gridGroupSource 159=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 159=(-3, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_162 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 162=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 160) := by
  match_laurent_source sourceRowsPart10 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 160=(422:Fin 780) from rfl,
    show gridGroupTarget 160=(600:Fin 780) from rfl,
    show gridGroupSource 160=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 160=(-1, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_163 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 163=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 161) := by
  match_laurent_source sourceRowsPart10 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 161=(423:Fin 780) from rfl,
    show gridGroupTarget 161=(120:Fin 780) from rfl,
    show gridGroupSource 161=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 161=(-3, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_164 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 164=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 162) := by
  match_laurent_source sourceRowsPart10 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 162=(424:Fin 780) from rfl,
    show gridGroupTarget 162=(270:Fin 780) from rfl,
    show gridGroupSource 162=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 162=(1, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_165 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 165=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 163) := by
  match_laurent_source sourceRowsPart10 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 163=(426:Fin 780) from rfl,
    show gridGroupTarget 163=(420:Fin 780) from rfl,
    show gridGroupSource 163=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 163=(-1, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_166 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 166=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 164) := by
  match_laurent_source sourceRowsPart10 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 164=(428:Fin 780) from rfl,
    show gridGroupTarget 164=(495:Fin 780) from rfl,
    show gridGroupSource 164=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 164=(3, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_167 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 167=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 165) := by
  match_laurent_source sourceRowsPart10 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 165=(429:Fin 780) from rfl,
    show gridGroupTarget 165=(520:Fin 780) from rfl,
    show gridGroupSource 165=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 165=(-3, 2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_168 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 168=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 166) := by
  match_laurent_source sourceRowsPart10 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 166=(430:Fin 780) from rfl,
    show gridGroupTarget 166=(540:Fin 780) from rfl,
    show gridGroupSource 166=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 166=(-1, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_169 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 169=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 167) := by
  match_laurent_source sourceRowsPart10 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 167=(435:Fin 780) from rfl,
    show gridGroupTarget 167=(600:Fin 780) from rfl,
    show gridGroupSource 167=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 167=(-3, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_170 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 170=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 168) := by
  match_laurent_source sourceRowsPart10 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 168=(438:Fin 780) from rfl,
    show gridGroupTarget 168=(620:Fin 780) from rfl,
    show gridGroupSource 168=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 168=(-1, 2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_171 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 171=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 169) := by
  match_laurent_source sourceRowsPart10 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 169=(445:Fin 780) from rfl,
    show gridGroupTarget 169=(648:Fin 780) from rfl,
    show gridGroupSource 169=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 169=(-3, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_172 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 172=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 170) := by
  match_laurent_source sourceRowsPart10 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 170=(456:Fin 780) from rfl,
    show gridGroupTarget 170=(670:Fin 780) from rfl,
    show gridGroupSource 170=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 170=(1, 2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_173 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 173=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 171) := by
  match_laurent_source sourceRowsPart10 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 171=(460:Fin 780) from rfl,
    show gridGroupTarget 171=(675:Fin 780) from rfl,
    show gridGroupSource 171=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 171=(3, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_174 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 174=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 172) := by
  match_laurent_source sourceRowsPart10 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 172=(465:Fin 780) from rfl,
    show gridGroupTarget 172=(680:Fin 780) from rfl,
    show gridGroupSource 172=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 172=(-3, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_175 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 175=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 173) := by
  match_laurent_source sourceRowsPart10 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 173=(470:Fin 780) from rfl,
    show gridGroupTarget 173=(684:Fin 780) from rfl,
    show gridGroupSource 173=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 173=(-1, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_176 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 176=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 174) := by
  match_laurent_source sourceRowsPart11 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 174=(480:Fin 780) from rfl,
    show gridGroupTarget 174=(690:Fin 780) from rfl,
    show gridGroupSource 174=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 174=(1, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_177 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 177=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 175) := by
  match_laurent_source sourceRowsPart11 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 175=(495:Fin 780) from rfl,
    show gridGroupTarget 175=(696:Fin 780) from rfl,
    show gridGroupSource 175=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 175=(-3, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_178 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 178=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 176) := by
  match_laurent_source sourceRowsPart11 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 176=(510:Fin 780) from rfl,
    show gridGroupTarget 176=(700:Fin 780) from rfl,
    show gridGroupSource 176=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 176=(-1, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_179 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 179=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 177) := by
  match_laurent_source sourceRowsPart11 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 177=(540:Fin 780) from rfl,
    show gridGroupTarget 177=(705:Fin 780) from rfl,
    show gridGroupSource 177=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 177=(3, 0, 0, 0) from rfl]

compact_elimination_proof theorem source_match_180 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 180=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 178) := by
  match_laurent_source sourceRowsPart11 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 178=(570:Fin 780) from rfl,
    show gridGroupTarget 178=(708:Fin 780) from rfl,
    show gridGroupSource 178=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 178=(-1, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_181 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 181=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 179) := by
  match_laurent_source sourceRowsPart11 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 179=(620:Fin 780) from rfl,
    show gridGroupTarget 179=(711:Fin 780) from rfl,
    show gridGroupSource 179=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 179=(3, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_182 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 182=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 180) := by
  match_laurent_source sourceRowsPart11 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 180=(720:Fin 780) from rfl,
    show gridGroupTarget 180=(714:Fin 780) from rfl,
    show gridGroupSource 180=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,
    show groupPowers 180=(1, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_183 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 183=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 181) := by
  match_laurent_source sourceRowsPart11 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 181=(160:Fin 780) from rfl,
    show gridGroupTarget 181=(69:Fin 780) from rfl,
    show gridGroupSource 181=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 181=(3, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_184 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 184=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 182) := by
  match_laurent_source sourceRowsPart11 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 182=(180:Fin 780) from rfl,
    show gridGroupTarget 182=(70:Fin 780) from rfl,
    show gridGroupSource 182=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 182=(1, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_185 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 185=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 183) := by
  match_laurent_source sourceRowsPart11 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 183=(210:Fin 780) from rfl,
    show gridGroupTarget 183=(72:Fin 780) from rfl,
    show gridGroupSource 183=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 183=(-1, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_186 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 186=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 184) := by
  match_laurent_source sourceRowsPart11 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 184=(285:Fin 780) from rfl,
    show gridGroupTarget 184=(84:Fin 780) from rfl,
    show gridGroupSource 184=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 184=(-3, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_187 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 187=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 185) := by
  match_laurent_source sourceRowsPart11 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 185=(310:Fin 780) from rfl,
    show gridGroupTarget 185=(96:Fin 780) from rfl,
    show gridGroupSource 185=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 185=(-1, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_188 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 188=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 186) := by
  match_laurent_source sourceRowsPart11 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 186=(315:Fin 780) from rfl,
    show gridGroupTarget 186=(100:Fin 780) from rfl,
    show gridGroupSource 186=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 186=(-3, 2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_189 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 189=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 187) := by
  match_laurent_source sourceRowsPart11 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 187=(335:Fin 780) from rfl,
    show gridGroupTarget 187=(132:Fin 780) from rfl,
    show gridGroupSource 187=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 187=(-3, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_190 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 190=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 188) := by
  match_laurent_source sourceRowsPart11 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 188=(340:Fin 780) from rfl,
    show gridGroupTarget 188=(150:Fin 780) from rfl,
    show gridGroupSource 188=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 188=(1, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_191 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 191=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 189) := by
  match_laurent_source sourceRowsPart11 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 189=(342:Fin 780) from rfl,
    show gridGroupTarget 189=(160:Fin 780) from rfl,
    show gridGroupSource 189=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 189=(-1, 2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_192 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 192=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 190) := by
  match_laurent_source sourceRowsPart12 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 190=(351:Fin 780) from rfl,
    show gridGroupTarget 190=(260:Fin 780) from rfl,
    show gridGroupSource 190=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 190=(-3, 2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_193 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 193=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 191) := by
  match_laurent_source sourceRowsPart12 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 191=(352:Fin 780) from rfl,
    show gridGroupTarget 191=(285:Fin 780) from rfl,
    show gridGroupSource 191=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 191=(3, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_194 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 194=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 192) := by
  match_laurent_source sourceRowsPart12 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 192=(354:Fin 780) from rfl,
    show gridGroupTarget 192=(360:Fin 780) from rfl,
    show gridGroupSource 192=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 192=(-1, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_195 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 195=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 193) := by
  match_laurent_source sourceRowsPart12 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 193=(355:Fin 780) from rfl,
    show gridGroupTarget 193=(420:Fin 780) from rfl,
    show gridGroupSource 193=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 193=(-3, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_196 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 196=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 194) := by
  match_laurent_source sourceRowsPart12 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 194=(356:Fin 780) from rfl,
    show gridGroupTarget 194=(510:Fin 780) from rfl,
    show gridGroupSource 194=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 194=(1, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_197 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 197=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 195) := by
  match_laurent_source sourceRowsPart12 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 195=(357:Fin 780) from rfl,
    show gridGroupTarget 195=(660:Fin 780) from rfl,
    show gridGroupSource 195=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 195=(-3, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_198 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 198=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 196) := by
  match_laurent_source sourceRowsPart12 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 196=(358:Fin 780) from rfl,
    show gridGroupTarget 196=(180:Fin 780) from rfl,
    show gridGroupSource 196=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 196=(-1, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_199 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 199=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 197) := by
  match_laurent_source sourceRowsPart12 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 197=(359:Fin 780) from rfl,
    show gridGroupTarget 197=(300:Fin 780) from rfl,
    show gridGroupSource 197=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 197=(-3, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_200 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 200=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 198) := by
  match_laurent_source sourceRowsPart12 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 198=(361:Fin 780) from rfl,
    show gridGroupTarget 198=(600:Fin 780) from rfl,
    show gridGroupSource 198=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 198=(-3, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_201 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 201=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 199) := by
  match_laurent_source sourceRowsPart12 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 199=(362:Fin 780) from rfl,
    show gridGroupTarget 199=(720:Fin 780) from rfl,
    show gridGroupSource 199=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 199=(-1, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_202 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 202=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 200) := by
  match_laurent_source sourceRowsPart12 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 200=(363:Fin 780) from rfl,
    show gridGroupTarget 200=(240:Fin 780) from rfl,
    show gridGroupSource 200=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 200=(-3, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_203 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 203=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 201) := by
  match_laurent_source sourceRowsPart12 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 201=(364:Fin 780) from rfl,
    show gridGroupTarget 201=(390:Fin 780) from rfl,
    show gridGroupSource 201=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 201=(1, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_204 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 204=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 202) := by
  match_laurent_source sourceRowsPart12 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 202=(365:Fin 780) from rfl,
    show gridGroupTarget 202=(480:Fin 780) from rfl,
    show gridGroupSource 202=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 202=(-3, -2, 0, 0) from rfl]

compact_elimination_proof theorem source_match_205 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 205=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 203) := by
  match_laurent_source sourceRowsPart12 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 203=(366:Fin 780) from rfl,
    show gridGroupTarget 203=(540:Fin 780) from rfl,
    show gridGroupSource 203=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 203=(-1, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_206 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 206=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 204) := by
  match_laurent_source sourceRowsPart12 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 204=(368:Fin 780) from rfl,
    show gridGroupTarget 204=(615:Fin 780) from rfl,
    show gridGroupSource 204=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 204=(3, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_207 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 207=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 205) := by
  match_laurent_source sourceRowsPart12 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 205=(369:Fin 780) from rfl,
    show gridGroupTarget 205=(640:Fin 780) from rfl,
    show gridGroupSource 205=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 205=(-3, 2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_208 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 208=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 206) := by
  match_laurent_source sourceRowsPart13 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 206=(385:Fin 780) from rfl,
    show gridGroupTarget 206=(768:Fin 780) from rfl,
    show gridGroupSource 206=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 206=(-3, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_209 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 209=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 207) := by
  match_laurent_source sourceRowsPart13 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 207=(560:Fin 780) from rfl,
    show gridGroupTarget 207=(51:Fin 780) from rfl,
    show gridGroupSource 207=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 207=(3, -2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_210 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 210=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 208) := by
  match_laurent_source sourceRowsPart13 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 208=(660:Fin 780) from rfl,
    show gridGroupTarget 208=(54:Fin 780) from rfl,
    show gridGroupSource 208=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,
    show groupPowers 208=(1, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_211 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 211=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 209) := by
  match_laurent_source sourceRowsPart13 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 209=(280:Fin 780) from rfl,
    show gridGroupTarget 209=(22:Fin 780) from rfl,
    show gridGroupSource 209=(3:Fin 27) from rfl,
    show sourceWord 3=[(1,false),(1,false),(2,false)] from rfl,
    show groupPowers 209=(1, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_212 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 212=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 210) := by
  match_laurent_source sourceRowsPart13 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 210=(376:Fin 780) from rfl,
    show gridGroupTarget 210=(70:Fin 780) from rfl,
    show gridGroupSource 210=(3:Fin 27) from rfl,
    show sourceWord 3=[(1,false),(1,false),(2,false)] from rfl,
    show groupPowers 210=(1, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_213 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 213=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 211) := by
  match_laurent_source sourceRowsPart13 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 211=(379:Fin 780) from rfl,
    show gridGroupTarget 211=(220:Fin 780) from rfl,
    show gridGroupSource 211=(3:Fin 27) from rfl,
    show sourceWord 3=[(1,false),(1,false),(2,false)] from rfl,
    show groupPowers 211=(-3, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_214 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 214=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 212) := by
  match_laurent_source sourceRowsPart13 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 212=(381:Fin 780) from rfl,
    show gridGroupTarget 212=(600:Fin 780) from rfl,
    show gridGroupSource 212=(3:Fin 27) from rfl,
    show sourceWord 3=[(1,false),(1,false),(2,false)] from rfl,
    show groupPowers 212=(-3, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_215 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 215=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 213) := by
  match_laurent_source sourceRowsPart13 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 213=(382:Fin 780) from rfl,
    show gridGroupTarget 213=(700:Fin 780) from rfl,
    show gridGroupSource 213=(3:Fin 27) from rfl,
    show sourceWord 3=[(1,false),(1,false),(2,false)] from rfl,
    show groupPowers 213=(-1, 0, 0, -2) from rfl]

compact_elimination_proof theorem source_match_216 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 216=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 214) := by
  match_laurent_source sourceRowsPart13 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 214=(580:Fin 780) from rfl,
    show gridGroupTarget 214=(19:Fin 780) from rfl,
    show gridGroupSource 214=(3:Fin 27) from rfl,
    show sourceWord 3=[(1,false),(1,false),(2,false)] from rfl,
    show groupPowers 214=(3, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_217 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 217=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 215) := by
  match_laurent_source sourceRowsPart13 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 215=(90:Fin 780) from rfl,
    show gridGroupTarget 215=(716:Fin 780) from rfl,
    show gridGroupSource 215=(15:Fin 27) from rfl,
    show sourceWord 15=[(2,false),(0,false)] from rfl,
    show groupPowers 215=(-1, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_218 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 218=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 216) := by
  match_laurent_source sourceRowsPart13 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 216=(240:Fin 780) from rfl,
    show gridGroupTarget 216=(717:Fin 780) from rfl,
    show gridGroupSource 216=(15:Fin 27) from rfl,
    show sourceWord 15=[(2,false),(0,false)] from rfl,
    show groupPowers 216=(3, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_219 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 219=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 217) := by
  match_laurent_source sourceRowsPart13 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 217=(540:Fin 780) from rfl,
    show gridGroupTarget 217=(718:Fin 780) from rfl,
    show gridGroupSource 217=(15:Fin 27) from rfl,
    show sourceWord 15=[(2,false),(0,false)] from rfl,
    show groupPowers 217=(1, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_220 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 220=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 218) := by
  match_laurent_source sourceRowsPart13 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 218=(30:Fin 780) from rfl,
    show gridGroupTarget 218=(56:Fin 780) from rfl,
    show gridGroupSource 218=(5:Fin 27) from rfl,
    show sourceWord 5=[(1,false),(2,false),(0,false)] from rfl,
    show groupPowers 218=(-1, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_221 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 221=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 219) := by
  match_laurent_source sourceRowsPart13 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 219=(180:Fin 780) from rfl,
    show gridGroupTarget 219=(57:Fin 780) from rfl,
    show gridGroupSource 219=(5:Fin 27) from rfl,
    show sourceWord 5=[(1,false),(2,false),(0,false)] from rfl,
    show groupPowers 219=(3, 0, 0, 2) from rfl]

compact_elimination_proof theorem source_match_222 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 222=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 220) := by
  match_laurent_source sourceRowsPart13 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 220=(480:Fin 780) from rfl,
    show gridGroupTarget 220=(58:Fin 780) from rfl,
    show gridGroupSource 220=(5:Fin 27) from rfl,
    show sourceWord 5=[(1,false),(2,false),(0,false)] from rfl,
    show groupPowers 220=(1, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_223 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 223=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 221) := by
  match_laurent_source sourceRowsPart13 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 221=(660:Fin 780) from rfl,
    show gridGroupTarget 221=(719:Fin 780) from rfl,
    show gridGroupSource 221=(16:Fin 27) from rfl,
    show sourceWord 16=[(2,false),(0,false),(0,false)] from rfl,
    show groupPowers 221=(3, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_224 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 224=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 222) := by
  match_laurent_source sourceRowsPart14 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 222=(59:Fin 780) from rfl,
    show gridGroupTarget 222=(600:Fin 780) from rfl,
    show gridGroupSource 222=(19:Fin 27) from rfl,
    show sourceWord 19=[(2,true),(1,true)] from rfl,
    show groupPowers 222=(-3, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_225 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 225=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 223) := by
  match_laurent_source sourceRowsPart14 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 223=(61:Fin 780) from rfl,
    show gridGroupTarget 223=(120:Fin 780) from rfl,
    show gridGroupSource 223=(19:Fin 27) from rfl,
    show sourceWord 19=[(2,true),(1,true)] from rfl,
    show groupPowers 223=(-3, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_226 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 226=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 224) := by
  match_laurent_source sourceRowsPart14 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 224=(270:Fin 780) from rfl,
    show gridGroupTarget 224=(403:Fin 780) from rfl,
    show gridGroupSource 224=(26:Fin 27) from rfl,
    show sourceWord 26=[(3,false),(2,false),(0,true)] from rfl,
    show groupPowers 224=(2, 2, -1, 2) from rfl]

compact_elimination_proof theorem source_match_227 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 227=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 225) := by
  match_laurent_source sourceRowsPart14 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 225=(165:Fin 780) from rfl,
    show gridGroupTarget 225=(442:Fin 780) from rfl,
    show gridGroupSource 225=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,
    show groupPowers 225=(-2, 2, -1, 2) from rfl]

compact_elimination_proof theorem source_match_228 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 228=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 226) := by
  match_laurent_source sourceRowsPart14 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 226=(273:Fin 780) from rfl,
    show gridGroupTarget 226=(490:Fin 780) from rfl,
    show gridGroupSource 226=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,
    show groupPowers 226=(-2, 2, 1, -2) from rfl]

compact_elimination_proof theorem source_match_229 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 229=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 227) := by
  match_laurent_source sourceRowsPart14 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 227=(290:Fin 780) from rfl,
    show gridGroupTarget 227=(507:Fin 780) from rfl,
    show gridGroupSource 227=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,
    show groupPowers 227=(2, -2, -1, 2) from rfl]

compact_elimination_proof theorem source_match_230 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 230=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 228) := by
  match_laurent_source sourceRowsPart14 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 228=(338:Fin 780) from rfl,
    show gridGroupTarget 228=(615:Fin 780) from rfl,
    show gridGroupSource 228=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,
    show groupPowers 228=(2, -2, 1, -2) from rfl]

compact_elimination_proof theorem source_match_231 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 231=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 229) := by
  match_laurent_source sourceRowsPart14 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 229=(377:Fin 780) from rfl,
    show gridGroupTarget 229=(510:Fin 780) from rfl,
    show gridGroupSource 229=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,
    show groupPowers 229=(-2, -2, 1, -2) from rfl]

compact_elimination_proof theorem source_match_232 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 232=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 230) := by
  match_laurent_source sourceRowsPart14 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 230=(386:Fin 780) from rfl,
    show gridGroupTarget 230=(195:Fin 780) from rfl,
    show gridGroupSource 230=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,
    show groupPowers 230=(2, -2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_233 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 233=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 231) := by
  match_laurent_source sourceRowsPart14 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 231=(389:Fin 780) from rfl,
    show gridGroupTarget 231=(390:Fin 780) from rfl,
    show gridGroupSource 231=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,
    show groupPowers 231=(-2, -2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_234 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 234=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 232) := by
  match_laurent_source sourceRowsPart14 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 232=(391:Fin 780) from rfl,
    show gridGroupTarget 232=(390:Fin 780) from rfl,
    show gridGroupSource 232=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,
    show groupPowers 232=(-2, -2, -1, -2) from rfl]

compact_elimination_proof theorem source_match_235 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 235=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 233) := by
  match_laurent_source sourceRowsPart14 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 233=(406:Fin 780) from rfl,
    show gridGroupTarget 233=(150:Fin 780) from rfl,
    show gridGroupSource 233=(20:Fin 27) from rfl,
    show sourceWord 20=[(2,true),(1,true),(2,false)] from rfl,
    show groupPowers 233=(0, -2, 0, -2) from rfl]

compact_elimination_proof theorem source_match_236 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 236=laurentRows X Y Z W (-1) (-1) (1) a b v (.word 234) := by
  match_laurent_source sourceRowsPart14 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridGroupIndex 234=(630:Fin 780) from rfl,
    show gridGroupTarget 234=(374:Fin 780) from rfl,
    show gridGroupSource 234=(20:Fin 27) from rfl,
    show sourceWord 20=[(2,true),(1,true),(2,false)] from rfl,
    show groupPowers 234=(0, 2, 0, 2) from rfl]

compact_elimination_proof theorem source_match_237 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 237=laurentRows X Y Z W (-1) (-1) (1) a b v (.entire 0) := by
  match_laurent_source sourceRowsPart14 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridEntireQ 0=3 from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_238 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 238=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 9) := by
  match_laurent_source sourceRowsPart14 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 9=3 from rfl,
    show gridTaylorT 9=(10:ℤ) from rfl,
    show gridTaylorPartner 9=(-260:ℤ) from rfl,
    show taylorPowers 9=(-1, 0, -1, 0) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_239 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 239=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 8) := by
  match_laurent_source sourceRowsPart14 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 8=3 from rfl,
    show gridTaylorT 8=(-10:ℤ) from rfl,
    show gridTaylorPartner 8=(260:ℤ) from rfl,
    show taylorPowers 8=(-1, 0, -1, 0) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_240 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 240=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 10) := by
  match_laurent_source sourceRowsPart15 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 10=3 from rfl,
    show gridTaylorT 10=(13:ℤ) from rfl,
    show gridTaylorPartner 10=(-200:ℤ) from rfl,
    show taylorPowers 10=(-3, 0, 1, -2) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_241 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 241=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 7) := by
  match_laurent_source sourceRowsPart15 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 7=3 from rfl,
    show gridTaylorT 7=(-13:ℤ) from rfl,
    show gridTaylorPartner 7=(200:ℤ) from rfl,
    show taylorPowers 7=(-3, 0, 1, -2) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_242 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 242=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 11) := by
  match_laurent_source sourceRowsPart15 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 11=3 from rfl,
    show gridTaylorT 11=(20:ℤ) from rfl,
    show gridTaylorPartner 11=(-130:ℤ) from rfl,
    show taylorPowers 11=(1, 0, -1, 0) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_243 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 243=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 6) := by
  match_laurent_source sourceRowsPart15 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 6=3 from rfl,
    show gridTaylorT 6=(-20:ℤ) from rfl,
    show gridTaylorPartner 6=(130:ℤ) from rfl,
    show taylorPowers 6=(1, 0, -1, 0) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_244 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 244=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 12) := by
  match_laurent_source sourceRowsPart15 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 12=3 from rfl,
    show gridTaylorT 12=(25:ℤ) from rfl,
    show gridTaylorPartner 12=(-104:ℤ) from rfl,
    show taylorPowers 12=(-3, 0, -1, 2) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_245 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 245=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 5) := by
  match_laurent_source sourceRowsPart15 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 5=3 from rfl,
    show gridTaylorT 5=(-25:ℤ) from rfl,
    show gridTaylorPartner 5=(104:ℤ) from rfl,
    show taylorPowers 5=(-3, 0, -1, 2) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_246 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 246=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 13) := by
  match_laurent_source sourceRowsPart15 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 13=3 from rfl,
    show gridTaylorT 13=(26:ℤ) from rfl,
    show gridTaylorPartner 13=(-100:ℤ) from rfl,
    show taylorPowers 13=(-1, 0, 1, -2) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_247 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 247=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 4) := by
  match_laurent_source sourceRowsPart15 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 4=3 from rfl,
    show gridTaylorT 4=(-26:ℤ) from rfl,
    show gridTaylorPartner 4=(100:ℤ) from rfl,
    show taylorPowers 4=(-1, 0, 1, -2) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_248 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 248=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 14) := by
  match_laurent_source sourceRowsPart15 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 14=3 from rfl,
    show gridTaylorT 14=(40:ℤ) from rfl,
    show gridTaylorPartner 14=(-65:ℤ) from rfl,
    show taylorPowers 14=(3, 0, -1, 0) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_249 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 249=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 3) := by
  match_laurent_source sourceRowsPart15 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 3=3 from rfl,
    show gridTaylorT 3=(-40:ℤ) from rfl,
    show gridTaylorPartner 3=(65:ℤ) from rfl,
    show taylorPowers 3=(3, 0, -1, 0) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_250 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 250=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 15) := by
  match_laurent_source sourceRowsPart15 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 15=3 from rfl,
    show gridTaylorT 15=(50:ℤ) from rfl,
    show gridTaylorPartner 15=(-52:ℤ) from rfl,
    show taylorPowers 15=(-1, 0, -1, 2) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_251 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 251=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 2) := by
  match_laurent_source sourceRowsPart15 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 2=3 from rfl,
    show gridTaylorT 2=(-50:ℤ) from rfl,
    show gridTaylorPartner 2=(52:ℤ) from rfl,
    show taylorPowers 2=(-1, 0, -1, 2) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_252 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 252=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 16) := by
  match_laurent_source sourceRowsPart15 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 16=3 from rfl,
    show gridTaylorT 16=(65:ℤ) from rfl,
    show gridTaylorPartner 16=(-40:ℤ) from rfl,
    show taylorPowers 16=(-3, 0, 1, 0) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_253 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 253=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 1) := by
  match_laurent_source sourceRowsPart15 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 1=3 from rfl,
    show gridTaylorT 1=(-65:ℤ) from rfl,
    show gridTaylorPartner 1=(40:ℤ) from rfl,
    show taylorPowers 1=(-3, 0, 1, 0) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_254 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 254=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 17) := by
  match_laurent_source sourceRowsPart15 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 17=3 from rfl,
    show gridTaylorT 17=(130:ℤ) from rfl,
    show gridTaylorPartner 17=(-20:ℤ) from rfl,
    show taylorPowers 17=(-1, 0, 1, 0) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_255 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 255=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 0) := by
  match_laurent_source sourceRowsPart15 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 0=3 from rfl,
    show gridTaylorT 0=(-130:ℤ) from rfl,
    show gridTaylorPartner 0=(20:ℤ) from rfl,
    show taylorPowers 0=(-1, 0, 1, 0) from rfl,
    show residues 3=({1,2}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_256 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 256=laurentRows X Y Z W (-1) (-1) (1) a b v (.entire 1) := by
  match_laurent_source sourceRowsPart16 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridEntireQ 1=4 from rfl,
    show residues 4=({1,3}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_257 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 257=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 22) := by
  match_laurent_source sourceRowsPart16 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 22=4 from rfl,
    show gridTaylorT 22=(5:ℤ) from rfl,
    show gridTaylorPartner 22=(-585:ℤ) from rfl,
    show taylorPowers 22=(0, -2, -1, 0) from rfl,
    show residues 4=({1,3}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_258 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 258=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 21) := by
  match_laurent_source sourceRowsPart16 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 21=4 from rfl,
    show gridTaylorT 21=(-5:ℤ) from rfl,
    show gridTaylorPartner 21=(585:ℤ) from rfl,
    show taylorPowers 21=(0, -2, -1, 0) from rfl,
    show residues 4=({1,3}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_259 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 259=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 23) := by
  match_laurent_source sourceRowsPart16 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 23=4 from rfl,
    show gridTaylorT 23=(13:ℤ) from rfl,
    show gridTaylorPartner 23=(-225:ℤ) from rfl,
    show taylorPowers 23=(0, -2, 1, -2) from rfl,
    show residues 4=({1,3}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_260 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 260=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 20) := by
  match_laurent_source sourceRowsPart16 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 20=4 from rfl,
    show gridTaylorT 20=(-13:ℤ) from rfl,
    show gridTaylorPartner 20=(225:ℤ) from rfl,
    show taylorPowers 20=(0, -2, 1, -2) from rfl,
    show residues 4=({1,3}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_261 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 261=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 24) := by
  match_laurent_source sourceRowsPart16 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 24=4 from rfl,
    show gridTaylorT 24=(15:ℤ) from rfl,
    show gridTaylorPartner 24=(-195:ℤ) from rfl,
    show taylorPowers 24=(0, 0, -1, 0) from rfl,
    show residues 4=({1,3}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_262 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 262=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 19) := by
  match_laurent_source sourceRowsPart16 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 19=4 from rfl,
    show gridTaylorT 19=(-15:ℤ) from rfl,
    show gridTaylorPartner 19=(195:ℤ) from rfl,
    show taylorPowers 19=(0, 0, -1, 0) from rfl,
    show residues 4=({1,3}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_263 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 263=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 25) := by
  match_laurent_source sourceRowsPart16 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 25=4 from rfl,
    show gridTaylorT 25=(25:ℤ) from rfl,
    show gridTaylorPartner 25=(-117:ℤ) from rfl,
    show taylorPowers 25=(0, -2, -1, 2) from rfl,
    show residues 4=({1,3}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_264 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 264=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 18) := by
  match_laurent_source sourceRowsPart16 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 18=4 from rfl,
    show gridTaylorT 18=(-25:ℤ) from rfl,
    show gridTaylorPartner 18=(117:ℤ) from rfl,
    show taylorPowers 18=(0, -2, -1, 2) from rfl,
    show residues 4=({1,3}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_265 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 265=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 26) := by
  match_laurent_source sourceRowsPart16 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 26=4 from rfl,
    show gridTaylorT 26=(39:ℤ) from rfl,
    show gridTaylorPartner 26=(-75:ℤ) from rfl,
    show taylorPowers 26=(0, 0, 1, -2) from rfl,
    show residues 4=({1,3}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_266 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 266=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 27) := by
  match_laurent_source sourceRowsPart16 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 27=4 from rfl,
    show gridTaylorT 27=(45:ℤ) from rfl,
    show gridTaylorPartner 27=(-65:ℤ) from rfl,
    show taylorPowers 27=(0, 2, -1, 0) from rfl,
    show residues 4=({1,3}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_267 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 267=laurentRows X Y Z W (-1) (-1) (1) a b v (.entire 2) := by
  match_laurent_source sourceRowsPart16 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridEntireQ 2=5 from rfl,
    show residues 5=({1,2,3,4}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_268 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 268=laurentRows X Y Z W (-1) (-1) (1) a b v (.entire 3) := by
  match_laurent_source sourceRowsPart16 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridEntireQ 3=6 from rfl,
    show residues 6=({1,5}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_269 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 269=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 34) := by
  match_laurent_source sourceRowsPart16 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 34=6 from rfl,
    show gridTaylorT 34=(2:ℤ) from rfl,
    show gridTaylorPartner 34=(-650:ℤ) from rfl,
    show taylorPowers 34=(0, 0, -1, -2) from rfl,
    show residues 6=({1,5}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_270 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 270=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 33) := by
  match_laurent_source sourceRowsPart16 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 33=6 from rfl,
    show gridTaylorT 33=(-2:ℤ) from rfl,
    show gridTaylorPartner 33=(650:ℤ) from rfl,
    show taylorPowers 33=(0, 0, -1, -2) from rfl,
    show residues 6=({1,5}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_271 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 271=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 35) := by
  match_laurent_source sourceRowsPart16 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 35=6 from rfl,
    show gridTaylorT 35=(10:ℤ) from rfl,
    show gridTaylorPartner 35=(-130:ℤ) from rfl,
    show taylorPowers 35=(0, 0, -1, 0) from rfl,
    show residues 6=({1,5}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_272 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 272=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 32) := by
  match_laurent_source sourceRowsPart17 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 32=6 from rfl,
    show gridTaylorT 32=(-10:ℤ) from rfl,
    show gridTaylorPartner 32=(130:ℤ) from rfl,
    show taylorPowers 32=(0, 0, -1, 0) from rfl,
    show residues 6=({1,5}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_273 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 273=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 36) := by
  match_laurent_source sourceRowsPart17 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 36=6 from rfl,
    show gridTaylorT 36=(13:ℤ) from rfl,
    show gridTaylorPartner 36=(-100:ℤ) from rfl,
    show taylorPowers 36=(-2, 0, 1, -2) from rfl,
    show residues 6=({1,5}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_274 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 274=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 31) := by
  match_laurent_source sourceRowsPart17 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 31=6 from rfl,
    show gridTaylorT 31=(-13:ℤ) from rfl,
    show gridTaylorPartner 31=(100:ℤ) from rfl,
    show taylorPowers 31=(-2, 0, 1, -2) from rfl,
    show residues 6=({1,5}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_275 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 275=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 37) := by
  match_laurent_source sourceRowsPart17 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 37=6 from rfl,
    show gridTaylorT 37=(20:ℤ) from rfl,
    show gridTaylorPartner 37=(-65:ℤ) from rfl,
    show taylorPowers 37=(2, 0, -1, 0) from rfl,
    show residues 6=({1,5}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_276 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 276=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 30) := by
  match_laurent_source sourceRowsPart17 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 30=6 from rfl,
    show gridTaylorT 30=(-20:ℤ) from rfl,
    show gridTaylorPartner 30=(65:ℤ) from rfl,
    show taylorPowers 30=(2, 0, -1, 0) from rfl,
    show residues 6=({1,5}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_277 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 277=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 38) := by
  match_laurent_source sourceRowsPart17 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 38=6 from rfl,
    show gridTaylorT 38=(25:ℤ) from rfl,
    show gridTaylorPartner 38=(-52:ℤ) from rfl,
    show taylorPowers 38=(-2, 0, -1, 2) from rfl,
    show residues 6=({1,5}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_278 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 278=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 29) := by
  match_laurent_source sourceRowsPart17 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 29=6 from rfl,
    show gridTaylorT 29=(-25:ℤ) from rfl,
    show gridTaylorPartner 29=(52:ℤ) from rfl,
    show taylorPowers 29=(-2, 0, -1, 2) from rfl,
    show residues 6=({1,5}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_279 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 279=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 39) := by
  match_laurent_source sourceRowsPart17 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 39=6 from rfl,
    show gridTaylorT 39=(26:ℤ) from rfl,
    show gridTaylorPartner 39=(-50:ℤ) from rfl,
    show taylorPowers 39=(0, 0, 1, -2) from rfl,
    show residues 6=({1,5}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_280 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 280=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 28) := by
  match_laurent_source sourceRowsPart17 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 28=6 from rfl,
    show gridTaylorT 28=(-26:ℤ) from rfl,
    show gridTaylorPartner 28=(50:ℤ) from rfl,
    show taylorPowers 28=(0, 0, 1, -2) from rfl,
    show residues 6=({1,5}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_281 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 281=laurentRows X Y Z W (-1) (-1) (1) a b v (.entire 4) := by
  match_laurent_source sourceRowsPart17 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridEntireQ 4=10 from rfl,
    show residues 10=({1,3,7,9}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_282 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 282=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 41) := by
  match_laurent_source sourceRowsPart17 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 41=10 from rfl,
    show gridTaylorT 41=(6:ℤ) from rfl,
    show gridTaylorPartner 41=(-78:ℤ) from rfl,
    show taylorPowers 41=(0, 0, -1, 0) from rfl,
    show residues 10=({1,3,7,9}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_283 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 283=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 40) := by
  match_laurent_source sourceRowsPart17 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 40=10 from rfl,
    show gridTaylorT 40=(-6:ℤ) from rfl,
    show gridTaylorPartner 40=(78:ℤ) from rfl,
    show taylorPowers 40=(0, 0, -1, 0) from rfl,
    show residues 10=({1,3,7,9}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_284 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 284=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 44) := by
  match_laurent_source sourceRowsPart17 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 44=12 from rfl,
    show gridTaylorT 44=(1:ℤ) from rfl,
    show gridTaylorPartner 44=(-325:ℤ) from rfl,
    show taylorPowers 44=(0, 0, -1, -2) from rfl,
    show residues 12=({1,5,7,11}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_285 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 285=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 43) := by
  match_laurent_source sourceRowsPart17 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 43=12 from rfl,
    show gridTaylorT 43=(-1:ℤ) from rfl,
    show gridTaylorPartner 43=(325:ℤ) from rfl,
    show taylorPowers 43=(0, 0, -1, -2) from rfl,
    show residues 12=({1,5,7,11}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_286 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 286=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 45) := by
  match_laurent_source sourceRowsPart17 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 45=12 from rfl,
    show gridTaylorT 45=(5:ℤ) from rfl,
    show gridTaylorPartner 45=(-65:ℤ) from rfl,
    show taylorPowers 45=(0, 0, -1, 0) from rfl,
    show residues 12=({1,5,7,11}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_287 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 287=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 42) := by
  match_laurent_source sourceRowsPart17 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 42=12 from rfl,
    show gridTaylorT 42=(-5:ℤ) from rfl,
    show gridTaylorPartner 42=(65:ℤ) from rfl,
    show taylorPowers 42=(0, 0, -1, 0) from rfl,
    show residues 12=({1,5,7,11}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_288 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 288=laurentRows X Y Z W (-1) (-1) (1) a b v (.entire 5) := by
  match_laurent_source sourceRowsPart18 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridEntireQ 5=13 from rfl,
    show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_289 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 289=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 50) := by
  match_laurent_source sourceRowsPart18 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 50=13 from rfl,
    show gridTaylorT 50=(10:ℤ) from rfl,
    show gridTaylorPartner 50=(-180:ℤ) from rfl,
    show taylorPowers 50=(-1, -2, 0, 0) from rfl,
    show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_290 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 290=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 49) := by
  match_laurent_source sourceRowsPart18 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 49=13 from rfl,
    show gridTaylorT 49=(-10:ℤ) from rfl,
    show gridTaylorPartner 49=(180:ℤ) from rfl,
    show taylorPowers 49=(-1, -2, 0, 0) from rfl,
    show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_291 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 291=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 51) := by
  match_laurent_source sourceRowsPart18 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 51=13 from rfl,
    show gridTaylorT 51=(20:ℤ) from rfl,
    show gridTaylorPartner 51=(-90:ℤ) from rfl,
    show taylorPowers 51=(1, -2, 0, 0) from rfl,
    show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_292 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 292=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 48) := by
  match_laurent_source sourceRowsPart18 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 48=13 from rfl,
    show gridTaylorT 48=(-20:ℤ) from rfl,
    show gridTaylorPartner 48=(90:ℤ) from rfl,
    show taylorPowers 48=(1, -2, 0, 0) from rfl,
    show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_293 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 293=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 52) := by
  match_laurent_source sourceRowsPart18 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 52=13 from rfl,
    show gridTaylorT 52=(30:ℤ) from rfl,
    show gridTaylorPartner 52=(-60:ℤ) from rfl,
    show taylorPowers 52=(-1, 0, 0, 0) from rfl,
    show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_294 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 294=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 53) := by
  match_laurent_source sourceRowsPart18 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 53=13 from rfl,
    show gridTaylorT 53=(90:ℤ) from rfl,
    show gridTaylorPartner 53=(-20:ℤ) from rfl,
    show taylorPowers 53=(-1, 2, 0, 0) from rfl,
    show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_295 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 295=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 47) := by
  match_laurent_source sourceRowsPart18 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 47=13 from rfl,
    show gridTaylorT 47=(-90:ℤ) from rfl,
    show gridTaylorPartner 47=(20:ℤ) from rfl,
    show taylorPowers 47=(-1, 2, 0, 0) from rfl,
    show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_296 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 296=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 54) := by
  match_laurent_source sourceRowsPart18 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 54=13 from rfl,
    show gridTaylorT 54=(180:ℤ) from rfl,
    show gridTaylorPartner 54=(-10:ℤ) from rfl,
    show taylorPowers 54=(1, 2, 0, 0) from rfl,
    show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_297 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 297=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 46) := by
  match_laurent_source sourceRowsPart18 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 46=13 from rfl,
    show gridTaylorT 46=(-180:ℤ) from rfl,
    show gridTaylorPartner 46=(10:ℤ) from rfl,
    show taylorPowers 46=(1, 2, 0, 0) from rfl,
    show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_298 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 298=laurentRows X Y Z W (-1) (-1) (1) a b v (.entire 6) := by
  match_laurent_source sourceRowsPart18 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridEntireQ 6=15 from rfl,
    show residues 15=({1,2,4,7,8,11,13,14}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_299 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 299=laurentRows X Y Z W (-1) (-1) (1) a b v (.entire 7) := by
  match_laurent_source sourceRowsPart18 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridEntireQ 7=20 from rfl,
    show residues 20=({1,3,7,9,11,13,17,19}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_300 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 300=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 57) := by
  match_laurent_source sourceRowsPart18 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 57=26 from rfl,
    show gridTaylorT 57=(10:ℤ) from rfl,
    show gridTaylorPartner 57=(-90:ℤ) from rfl,
    show taylorPowers 57=(0, -2, 0, 0) from rfl,
    show residues 26=({1,3,5,7,9,11,15,17,19,21,23,25}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_301 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 301=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 56) := by
  match_laurent_source sourceRowsPart18 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 56=26 from rfl,
    show gridTaylorT 56=(-10:ℤ) from rfl,
    show gridTaylorPartner 56=(90:ℤ) from rfl,
    show taylorPowers 56=(0, -2, 0, 0) from rfl,
    show residues 26=({1,3,5,7,9,11,15,17,19,21,23,25}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_302 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 302=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 58) := by
  match_laurent_source sourceRowsPart18 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 58=26 from rfl,
    show gridTaylorT 58=(90:ℤ) from rfl,
    show gridTaylorPartner 58=(-10:ℤ) from rfl,
    show taylorPowers 58=(0, 2, 0, 0) from rfl,
    show residues 26=({1,3,5,7,9,11,15,17,19,21,23,25}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_303 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 303=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 55) := by
  match_laurent_source sourceRowsPart18 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 55=26 from rfl,
    show gridTaylorT 55=(-90:ℤ) from rfl,
    show gridTaylorPartner 55=(10:ℤ) from rfl,
    show taylorPowers 55=(0, 2, 0, 0) from rfl,
    show residues 26=({1,3,5,7,9,11,15,17,19,21,23,25}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_304 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 304=laurentRows X Y Z W (-1) (-1) (1) a b v (.entire 8) := by
  match_laurent_source sourceRowsPart19 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridEntireQ 8=30 from rfl,
    show residues 30=({1,7,11,13,17,19,23,29}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_305 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 305=laurentRows X Y Z W (-1) (-1) (1) a b v (.entire 9) := by
  match_laurent_source sourceRowsPart19 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridEntireQ 9=39 from rfl,
    show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_306 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 306=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 61) := by
  match_laurent_source sourceRowsPart19 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 61=39 from rfl,
    show gridTaylorT 61=(10:ℤ) from rfl,
    show gridTaylorPartner 61=(-20:ℤ) from rfl,
    show taylorPowers 61=(-1, 0, 0, 0) from rfl,
    show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_307 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 307=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 60) := by
  match_laurent_source sourceRowsPart19 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 60=39 from rfl,
    show gridTaylorT 60=(-10:ℤ) from rfl,
    show gridTaylorPartner 60=(20:ℤ) from rfl,
    show taylorPowers 60=(-1, 0, 0, 0) from rfl,
    show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_308 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 308=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 62) := by
  match_laurent_source sourceRowsPart19 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 62=39 from rfl,
    show gridTaylorT 62=(20:ℤ) from rfl,
    show gridTaylorPartner 62=(-10:ℤ) from rfl,
    show taylorPowers 62=(1, 0, 0, 0) from rfl,
    show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_309 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 309=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 59) := by
  match_laurent_source sourceRowsPart19 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 59=39 from rfl,
    show gridTaylorT 59=(-20:ℤ) from rfl,
    show gridTaylorPartner 59=(10:ℤ) from rfl,
    show taylorPowers 59=(1, 0, 0, 0) from rfl,
    show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_310 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 310=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 65) := by
  match_laurent_source sourceRowsPart19 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 65=52 from rfl,
    show gridTaylorT 65=(5:ℤ) from rfl,
    show gridTaylorPartner 65=(-45:ℤ) from rfl,
    show taylorPowers 65=(0, -2, 0, 0) from rfl,
    show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_311 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 311=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 64) := by
  match_laurent_source sourceRowsPart19 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 64=52 from rfl,
    show gridTaylorT 64=(-5:ℤ) from rfl,
    show gridTaylorPartner 64=(45:ℤ) from rfl,
    show taylorPowers 64=(0, -2, 0, 0) from rfl,
    show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_312 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 312=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 66) := by
  match_laurent_source sourceRowsPart19 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 66=52 from rfl,
    show gridTaylorT 66=(45:ℤ) from rfl,
    show gridTaylorPartner 66=(-5:ℤ) from rfl,
    show taylorPowers 66=(0, 2, 0, 0) from rfl,
    show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_313 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 313=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 63) := by
  match_laurent_source sourceRowsPart19 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 63=52 from rfl,
    show gridTaylorT 63=(-45:ℤ) from rfl,
    show gridTaylorPartner 63=(5:ℤ) from rfl,
    show taylorPowers 63=(0, 2, 0, 0) from rfl,
    show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_314 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 314=laurentRows X Y Z W (-1) (-1) (1) a b v (.entire 10) := by
  match_laurent_source sourceRowsPart19 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridEntireQ 10=78 from rfl,
    show residues 78=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_315 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 315=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 68) := by
  match_laurent_source sourceRowsPart19 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 68=78 from rfl,
    show gridTaylorT 68=(10:ℤ) from rfl,
    show gridTaylorPartner 68=(-10:ℤ) from rfl,
    show taylorPowers 68=(0, 0, 0, 0) from rfl,
    show residues 78=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_316 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 316=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 67) := by
  match_laurent_source sourceRowsPart19 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 67=78 from rfl,
    show gridTaylorT 67=(-10:ℤ) from rfl,
    show gridTaylorPartner 67=(10:ℤ) from rfl,
    show taylorPowers 67=(0, 0, 0, 0) from rfl,
    show residues 78=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_317 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 317=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 70) := by
  match_laurent_source sourceRowsPart19 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 70=156 from rfl,
    show gridTaylorT 70=(5:ℤ) from rfl,
    show gridTaylorPartner 70=(-5:ℤ) from rfl,
    show taylorPowers 70=(0, 0, 0, 0) from rfl,
    show residues 156=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77,79,83,85,89,95,97,101,103,107,109,113,115,119,121,125,127,131,133,137,139,145,149,151,155}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_318 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 318=laurentRows X Y Z W (-1) (-1) (1) a b v (.taylor 69) := by
  match_laurent_source sourceRowsPart19 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridTaylorQ 69=156 from rfl,
    show gridTaylorT 69=(-5:ℤ) from rfl,
    show gridTaylorPartner 69=(5:ℤ) from rfl,
    show taylorPowers 69=(0, 0, 0, 0) from rfl,
    show residues 156=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77,79,83,85,89,95,97,101,103,107,109,113,115,119,121,125,127,131,133,137,139,145,149,151,155}:Finset ℕ) from by decide]

compact_elimination_proof theorem source_match_319 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 319=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 0) := by
  match_laurent_source sourceRowsPart19 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 0=2 from rfl,
    show gridHeckeT 0=(7:ℤ) from rfl]

compact_elimination_proof theorem source_match_320 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 320=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 1) := by
  match_laurent_source sourceRowsPart20 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 1=2 from rfl,
    show gridHeckeT 1=(8:ℤ) from rfl]

compact_elimination_proof theorem source_match_321 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 321=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 2) := by
  match_laurent_source sourceRowsPart20 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 2=2 from rfl,
    show gridHeckeT 2=(9:ℤ) from rfl]

compact_elimination_proof theorem source_match_322 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 322=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 3) := by
  match_laurent_source sourceRowsPart20 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 3=2 from rfl,
    show gridHeckeT 3=(11:ℤ) from rfl]

compact_elimination_proof theorem source_match_323 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 323=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 4) := by
  match_laurent_source sourceRowsPart20 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 4=2 from rfl,
    show gridHeckeT 4=(22:ℤ) from rfl]

compact_elimination_proof theorem source_match_324 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 324=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 5) := by
  match_laurent_source sourceRowsPart20 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 5=2 from rfl,
    show gridHeckeT 5=(42:ℤ) from rfl]

compact_elimination_proof theorem source_match_325 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 325=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 6) := by
  match_laurent_source sourceRowsPart20 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 6=2 from rfl,
    show gridHeckeT 6=(52:ℤ) from rfl]

compact_elimination_proof theorem source_match_326 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 326=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 7) := by
  match_laurent_source sourceRowsPart20 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 7=2 from rfl,
    show gridHeckeT 7=(55:ℤ) from rfl]

compact_elimination_proof theorem source_match_327 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 327=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 8) := by
  match_laurent_source sourceRowsPart20 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 8=2 from rfl,
    show gridHeckeT 8=(66:ℤ) from rfl]

compact_elimination_proof theorem source_match_328 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 328=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 9) := by
  match_laurent_source sourceRowsPart20 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 9=2 from rfl,
    show gridHeckeT 9=(95:ℤ) from rfl]

compact_elimination_proof theorem source_match_329 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 329=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 10) := by
  match_laurent_source sourceRowsPart20 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 10=2 from rfl,
    show gridHeckeT 10=(100:ℤ) from rfl]

compact_elimination_proof theorem source_match_330 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 330=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 11) := by
  match_laurent_source sourceRowsPart20 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 11=2 from rfl,
    show gridHeckeT 11=(104:ℤ) from rfl]

compact_elimination_proof theorem source_match_331 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 331=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 12) := by
  match_laurent_source sourceRowsPart20 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 12=2 from rfl,
    show gridHeckeT 12=(105:ℤ) from rfl]

compact_elimination_proof theorem source_match_332 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 332=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 13) := by
  match_laurent_source sourceRowsPart20 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 13=2 from rfl,
    show gridHeckeT 13=(110:ℤ) from rfl]

compact_elimination_proof theorem source_match_333 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 333=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 14) := by
  match_laurent_source sourceRowsPart20 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 14=2 from rfl,
    show gridHeckeT 14=(140:ℤ) from rfl]

compact_elimination_proof theorem source_match_334 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 334=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 15) := by
  match_laurent_source sourceRowsPart20 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 15=2 from rfl,
    show gridHeckeT 15=(143:ℤ) from rfl]

compact_elimination_proof theorem source_match_335 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 335=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 16) := by
  match_laurent_source sourceRowsPart20 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 16=2 from rfl,
    show gridHeckeT 16=(162:ℤ) from rfl]

compact_elimination_proof theorem source_match_336 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 336=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 17) := by
  match_laurent_source sourceRowsPart21 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 17=2 from rfl,
    show gridHeckeT 17=(185:ℤ) from rfl]

compact_elimination_proof theorem source_match_337 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 337=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 18) := by
  match_laurent_source sourceRowsPart21 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 18=2 from rfl,
    show gridHeckeT 18=(205:ℤ) from rfl]

compact_elimination_proof theorem source_match_338 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 338=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 19) := by
  match_laurent_source sourceRowsPart21 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 19=2 from rfl,
    show gridHeckeT 19=(225:ℤ) from rfl]

compact_elimination_proof theorem source_match_339 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 339=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 20) := by
  match_laurent_source sourceRowsPart21 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 20=2 from rfl,
    show gridHeckeT 20=(228:ℤ) from rfl]

compact_elimination_proof theorem source_match_340 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 340=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 21) := by
  match_laurent_source sourceRowsPart21 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 21=2 from rfl,
    show gridHeckeT 21=(250:ℤ) from rfl]

compact_elimination_proof theorem source_match_341 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 341=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 22) := by
  match_laurent_source sourceRowsPart21 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 22=2 from rfl,
    show gridHeckeT 22=(295:ℤ) from rfl]

compact_elimination_proof theorem source_match_342 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 342=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 23) := by
  match_laurent_source sourceRowsPart21 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 23=2 from rfl,
    show gridHeckeT 23=(368:ℤ) from rfl]

compact_elimination_proof theorem source_match_343 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 343=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 24) := by
  match_laurent_source sourceRowsPart21 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 24=3 from rfl,
    show gridHeckeT 24=(13:ℤ) from rfl]

compact_elimination_proof theorem source_match_344 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 344=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 25) := by
  match_laurent_source sourceRowsPart21 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 25=3 from rfl,
    show gridHeckeT 25=(20:ℤ) from rfl]

compact_elimination_proof theorem source_match_345 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 345=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 26) := by
  match_laurent_source sourceRowsPart21 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 26=3 from rfl,
    show gridHeckeT 26=(25:ℤ) from rfl]

compact_elimination_proof theorem source_match_346 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 346=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 27) := by
  match_laurent_source sourceRowsPart21 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 27=3 from rfl,
    show gridHeckeT 27=(26:ℤ) from rfl]

compact_elimination_proof theorem source_match_347 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 347=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 28) := by
  match_laurent_source sourceRowsPart21 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 28=3 from rfl,
    show gridHeckeT 28=(35:ℤ) from rfl]

compact_elimination_proof theorem source_match_348 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 348=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 29) := by
  match_laurent_source sourceRowsPart21 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 29=3 from rfl,
    show gridHeckeT 29=(40:ℤ) from rfl]

compact_elimination_proof theorem source_match_349 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 349=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 30) := by
  match_laurent_source sourceRowsPart21 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 30=3 from rfl,
    show gridHeckeT 30=(55:ℤ) from rfl]

compact_elimination_proof theorem source_match_350 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 350=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 31) := by
  match_laurent_source sourceRowsPart21 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 31=3 from rfl,
    show gridHeckeT 31=(65:ℤ) from rfl]

compact_elimination_proof theorem source_match_351 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 351=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 32) := by
  match_laurent_source sourceRowsPart21 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 32=3 from rfl,
    show gridHeckeT 32=(75:ℤ) from rfl]

compact_elimination_proof theorem source_match_352 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 352=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 33) := by
  match_laurent_source sourceRowsPart22 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 33=3 from rfl,
    show gridHeckeT 33=(95:ℤ) from rfl]

compact_elimination_proof theorem source_match_353 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 353=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 34) := by
  match_laurent_source sourceRowsPart22 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 34=3 from rfl,
    show gridHeckeT 34=(110:ℤ) from rfl]

compact_elimination_proof theorem source_match_354 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 354=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 35) := by
  match_laurent_source sourceRowsPart22 at 2 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 35=3 from rfl,
    show gridHeckeT 35=(150:ℤ) from rfl]

compact_elimination_proof theorem source_match_355 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 355=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 36) := by
  match_laurent_source sourceRowsPart22 at 3 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 36=3 from rfl,
    show gridHeckeT 36=(185:ℤ) from rfl]

compact_elimination_proof theorem source_match_356 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 356=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 37) := by
  match_laurent_source sourceRowsPart22 at 4 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 37=3 from rfl,
    show gridHeckeT 37=(195:ℤ) from rfl]

compact_elimination_proof theorem source_match_357 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 357=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 38) := by
  match_laurent_source sourceRowsPart22 at 5 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 38=3 from rfl,
    show gridHeckeT 38=(205:ℤ) from rfl]

compact_elimination_proof theorem source_match_358 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 358=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 39) := by
  match_laurent_source sourceRowsPart22 at 6 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 39=3 from rfl,
    show gridHeckeT 39=(220:ℤ) from rfl]

compact_elimination_proof theorem source_match_359 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 359=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 40) := by
  match_laurent_source sourceRowsPart22 at 7 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 40=3 from rfl,
    show gridHeckeT 40=(240:ℤ) from rfl]

compact_elimination_proof theorem source_match_360 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 360=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 41) := by
  match_laurent_source sourceRowsPart22 at 8 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 41=5 from rfl,
    show gridHeckeT 41=(26:ℤ) from rfl]

compact_elimination_proof theorem source_match_361 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 361=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 42) := by
  match_laurent_source sourceRowsPart22 at 9 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 42=5 from rfl,
    show gridHeckeT 42=(39:ℤ) from rfl]

compact_elimination_proof theorem source_match_362 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 362=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 43) := by
  match_laurent_source sourceRowsPart22 at 10 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 43=5 from rfl,
    show gridHeckeT 43=(52:ℤ) from rfl]

compact_elimination_proof theorem source_match_363 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 363=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 44) := by
  match_laurent_source sourceRowsPart22 at 11 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 44=5 from rfl,
    show gridHeckeT 44=(104:ℤ) from rfl]

compact_elimination_proof theorem source_match_364 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 364=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 45) := by
  match_laurent_source sourceRowsPart22 at 12 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 45=5 from rfl,
    show gridHeckeT 45=(117:ℤ) from rfl]

compact_elimination_proof theorem source_match_365 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 365=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 46) := by
  match_laurent_source sourceRowsPart22 at 13 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 46=5 from rfl,
    show gridHeckeT 46=(130:ℤ) from rfl]

compact_elimination_proof theorem source_match_366 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 366=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 47) := by
  match_laurent_source sourceRowsPart22 at 14 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 47=13 from rfl,
    show gridHeckeT 47=(10:ℤ) from rfl]

compact_elimination_proof theorem source_match_367 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 367=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 48) := by
  match_laurent_source sourceRowsPart22 at 15 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 48=13 from rfl,
    show gridHeckeT 48=(20:ℤ) from rfl]

compact_elimination_proof theorem source_match_368 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 368=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 49) := by
  match_laurent_source sourceRowsPart23 at 0 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 49=13 from rfl,
    show gridHeckeT 49=(40:ℤ) from rfl]

compact_elimination_proof theorem source_match_369 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 780→ℂ) :
    sourceRows X Y Z W a b v 369=laurentRows X Y Z W (-1) (-1) (1) a b v (.hecke 50) := by
  match_laurent_source sourceRowsPart23 at 1 policy level26Optional using [laurentRows,laurentHecke,gridSample,
    show gridHeckeP 50=13 from rfl,
    show gridHeckeT 50=(50:ℤ) from rfl]

end SmallLevelTwentySixUnitMMP
end
end

/-! ## SmallLevelTwentySixUnitMMPTheoryV4 -/
section
/-! Consolidated chapter: SmallLevelTwentySixUnitMMP. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixUnitMMPSourceMatchV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 7000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMP
open SmallLevelTwentySixGrid SmallLevelFourPrimeRates FinitenessRamanujanSum

compact_elimination_proof theorem sourceRows_match (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (i : Fin 370) :
    sourceRows X Y Z W a b v i=laurentRows X Y Z W (-1) (-1) (1) a b v (selectedSource i) := by
  fin_cases i
  · exact source_match_0 X Y Z W a b hX hY hZ hW v
  · exact source_match_1 X Y Z W a b hX hY hZ hW v
  · exact source_match_2 X Y Z W a b hX hY hZ hW v
  · exact source_match_3 X Y Z W a b hX hY hZ hW v
  · exact source_match_4 X Y Z W a b hX hY hZ hW v
  · exact source_match_5 X Y Z W a b hX hY hZ hW v
  · exact source_match_6 X Y Z W a b hX hY hZ hW v
  · exact source_match_7 X Y Z W a b hX hY hZ hW v
  · exact source_match_8 X Y Z W a b hX hY hZ hW v
  · exact source_match_9 X Y Z W a b hX hY hZ hW v
  · exact source_match_10 X Y Z W a b hX hY hZ hW v
  · exact source_match_11 X Y Z W a b hX hY hZ hW v
  · exact source_match_12 X Y Z W a b hX hY hZ hW v
  · exact source_match_13 X Y Z W a b hX hY hZ hW v
  · exact source_match_14 X Y Z W a b hX hY hZ hW v
  · exact source_match_15 X Y Z W a b hX hY hZ hW v
  · exact source_match_16 X Y Z W a b hX hY hZ hW v
  · exact source_match_17 X Y Z W a b hX hY hZ hW v
  · exact source_match_18 X Y Z W a b hX hY hZ hW v
  · exact source_match_19 X Y Z W a b hX hY hZ hW v
  · exact source_match_20 X Y Z W a b hX hY hZ hW v
  · exact source_match_21 X Y Z W a b hX hY hZ hW v
  · exact source_match_22 X Y Z W a b hX hY hZ hW v
  · exact source_match_23 X Y Z W a b hX hY hZ hW v
  · exact source_match_24 X Y Z W a b hX hY hZ hW v
  · exact source_match_25 X Y Z W a b hX hY hZ hW v
  · exact source_match_26 X Y Z W a b hX hY hZ hW v
  · exact source_match_27 X Y Z W a b hX hY hZ hW v
  · exact source_match_28 X Y Z W a b hX hY hZ hW v
  · exact source_match_29 X Y Z W a b hX hY hZ hW v
  · exact source_match_30 X Y Z W a b hX hY hZ hW v
  · exact source_match_31 X Y Z W a b hX hY hZ hW v
  · exact source_match_32 X Y Z W a b hX hY hZ hW v
  · exact source_match_33 X Y Z W a b hX hY hZ hW v
  · exact source_match_34 X Y Z W a b hX hY hZ hW v
  · exact source_match_35 X Y Z W a b hX hY hZ hW v
  · exact source_match_36 X Y Z W a b hX hY hZ hW v
  · exact source_match_37 X Y Z W a b hX hY hZ hW v
  · exact source_match_38 X Y Z W a b hX hY hZ hW v
  · exact source_match_39 X Y Z W a b hX hY hZ hW v
  · exact source_match_40 X Y Z W a b hX hY hZ hW v
  · exact source_match_41 X Y Z W a b hX hY hZ hW v
  · exact source_match_42 X Y Z W a b hX hY hZ hW v
  · exact source_match_43 X Y Z W a b hX hY hZ hW v
  · exact source_match_44 X Y Z W a b hX hY hZ hW v
  · exact source_match_45 X Y Z W a b hX hY hZ hW v
  · exact source_match_46 X Y Z W a b hX hY hZ hW v
  · exact source_match_47 X Y Z W a b hX hY hZ hW v
  · exact source_match_48 X Y Z W a b hX hY hZ hW v
  · exact source_match_49 X Y Z W a b hX hY hZ hW v
  · exact source_match_50 X Y Z W a b hX hY hZ hW v
  · exact source_match_51 X Y Z W a b hX hY hZ hW v
  · exact source_match_52 X Y Z W a b hX hY hZ hW v
  · exact source_match_53 X Y Z W a b hX hY hZ hW v
  · exact source_match_54 X Y Z W a b hX hY hZ hW v
  · exact source_match_55 X Y Z W a b hX hY hZ hW v
  · exact source_match_56 X Y Z W a b hX hY hZ hW v
  · exact source_match_57 X Y Z W a b hX hY hZ hW v
  · exact source_match_58 X Y Z W a b hX hY hZ hW v
  · exact source_match_59 X Y Z W a b hX hY hZ hW v
  · exact source_match_60 X Y Z W a b hX hY hZ hW v
  · exact source_match_61 X Y Z W a b hX hY hZ hW v
  · exact source_match_62 X Y Z W a b hX hY hZ hW v
  · exact source_match_63 X Y Z W a b hX hY hZ hW v
  · exact source_match_64 X Y Z W a b hX hY hZ hW v
  · exact source_match_65 X Y Z W a b hX hY hZ hW v
  · exact source_match_66 X Y Z W a b hX hY hZ hW v
  · exact source_match_67 X Y Z W a b hX hY hZ hW v
  · exact source_match_68 X Y Z W a b hX hY hZ hW v
  · exact source_match_69 X Y Z W a b hX hY hZ hW v
  · exact source_match_70 X Y Z W a b hX hY hZ hW v
  · exact source_match_71 X Y Z W a b hX hY hZ hW v
  · exact source_match_72 X Y Z W a b hX hY hZ hW v
  · exact source_match_73 X Y Z W a b hX hY hZ hW v
  · exact source_match_74 X Y Z W a b hX hY hZ hW v
  · exact source_match_75 X Y Z W a b hX hY hZ hW v
  · exact source_match_76 X Y Z W a b hX hY hZ hW v
  · exact source_match_77 X Y Z W a b hX hY hZ hW v
  · exact source_match_78 X Y Z W a b hX hY hZ hW v
  · exact source_match_79 X Y Z W a b hX hY hZ hW v
  · exact source_match_80 X Y Z W a b hX hY hZ hW v
  · exact source_match_81 X Y Z W a b hX hY hZ hW v
  · exact source_match_82 X Y Z W a b hX hY hZ hW v
  · exact source_match_83 X Y Z W a b hX hY hZ hW v
  · exact source_match_84 X Y Z W a b hX hY hZ hW v
  · exact source_match_85 X Y Z W a b hX hY hZ hW v
  · exact source_match_86 X Y Z W a b hX hY hZ hW v
  · exact source_match_87 X Y Z W a b hX hY hZ hW v
  · exact source_match_88 X Y Z W a b hX hY hZ hW v
  · exact source_match_89 X Y Z W a b hX hY hZ hW v
  · exact source_match_90 X Y Z W a b hX hY hZ hW v
  · exact source_match_91 X Y Z W a b hX hY hZ hW v
  · exact source_match_92 X Y Z W a b hX hY hZ hW v
  · exact source_match_93 X Y Z W a b hX hY hZ hW v
  · exact source_match_94 X Y Z W a b hX hY hZ hW v
  · exact source_match_95 X Y Z W a b hX hY hZ hW v
  · exact source_match_96 X Y Z W a b hX hY hZ hW v
  · exact source_match_97 X Y Z W a b hX hY hZ hW v
  · exact source_match_98 X Y Z W a b hX hY hZ hW v
  · exact source_match_99 X Y Z W a b hX hY hZ hW v
  · exact source_match_100 X Y Z W a b hX hY hZ hW v
  · exact source_match_101 X Y Z W a b hX hY hZ hW v
  · exact source_match_102 X Y Z W a b hX hY hZ hW v
  · exact source_match_103 X Y Z W a b hX hY hZ hW v
  · exact source_match_104 X Y Z W a b hX hY hZ hW v
  · exact source_match_105 X Y Z W a b hX hY hZ hW v
  · exact source_match_106 X Y Z W a b hX hY hZ hW v
  · exact source_match_107 X Y Z W a b hX hY hZ hW v
  · exact source_match_108 X Y Z W a b hX hY hZ hW v
  · exact source_match_109 X Y Z W a b hX hY hZ hW v
  · exact source_match_110 X Y Z W a b hX hY hZ hW v
  · exact source_match_111 X Y Z W a b hX hY hZ hW v
  · exact source_match_112 X Y Z W a b hX hY hZ hW v
  · exact source_match_113 X Y Z W a b hX hY hZ hW v
  · exact source_match_114 X Y Z W a b hX hY hZ hW v
  · exact source_match_115 X Y Z W a b hX hY hZ hW v
  · exact source_match_116 X Y Z W a b hX hY hZ hW v
  · exact source_match_117 X Y Z W a b hX hY hZ hW v
  · exact source_match_118 X Y Z W a b hX hY hZ hW v
  · exact source_match_119 X Y Z W a b hX hY hZ hW v
  · exact source_match_120 X Y Z W a b hX hY hZ hW v
  · exact source_match_121 X Y Z W a b hX hY hZ hW v
  · exact source_match_122 X Y Z W a b hX hY hZ hW v
  · exact source_match_123 X Y Z W a b hX hY hZ hW v
  · exact source_match_124 X Y Z W a b hX hY hZ hW v
  · exact source_match_125 X Y Z W a b hX hY hZ hW v
  · exact source_match_126 X Y Z W a b hX hY hZ hW v
  · exact source_match_127 X Y Z W a b hX hY hZ hW v
  · exact source_match_128 X Y Z W a b hX hY hZ hW v
  · exact source_match_129 X Y Z W a b hX hY hZ hW v
  · exact source_match_130 X Y Z W a b hX hY hZ hW v
  · exact source_match_131 X Y Z W a b hX hY hZ hW v
  · exact source_match_132 X Y Z W a b hX hY hZ hW v
  · exact source_match_133 X Y Z W a b hX hY hZ hW v
  · exact source_match_134 X Y Z W a b hX hY hZ hW v
  · exact source_match_135 X Y Z W a b hX hY hZ hW v
  · exact source_match_136 X Y Z W a b hX hY hZ hW v
  · exact source_match_137 X Y Z W a b hX hY hZ hW v
  · exact source_match_138 X Y Z W a b hX hY hZ hW v
  · exact source_match_139 X Y Z W a b hX hY hZ hW v
  · exact source_match_140 X Y Z W a b hX hY hZ hW v
  · exact source_match_141 X Y Z W a b hX hY hZ hW v
  · exact source_match_142 X Y Z W a b hX hY hZ hW v
  · exact source_match_143 X Y Z W a b hX hY hZ hW v
  · exact source_match_144 X Y Z W a b hX hY hZ hW v
  · exact source_match_145 X Y Z W a b hX hY hZ hW v
  · exact source_match_146 X Y Z W a b hX hY hZ hW v
  · exact source_match_147 X Y Z W a b hX hY hZ hW v
  · exact source_match_148 X Y Z W a b hX hY hZ hW v
  · exact source_match_149 X Y Z W a b hX hY hZ hW v
  · exact source_match_150 X Y Z W a b hX hY hZ hW v
  · exact source_match_151 X Y Z W a b hX hY hZ hW v
  · exact source_match_152 X Y Z W a b hX hY hZ hW v
  · exact source_match_153 X Y Z W a b hX hY hZ hW v
  · exact source_match_154 X Y Z W a b hX hY hZ hW v
  · exact source_match_155 X Y Z W a b hX hY hZ hW v
  · exact source_match_156 X Y Z W a b hX hY hZ hW v
  · exact source_match_157 X Y Z W a b hX hY hZ hW v
  · exact source_match_158 X Y Z W a b hX hY hZ hW v
  · exact source_match_159 X Y Z W a b hX hY hZ hW v
  · exact source_match_160 X Y Z W a b hX hY hZ hW v
  · exact source_match_161 X Y Z W a b hX hY hZ hW v
  · exact source_match_162 X Y Z W a b hX hY hZ hW v
  · exact source_match_163 X Y Z W a b hX hY hZ hW v
  · exact source_match_164 X Y Z W a b hX hY hZ hW v
  · exact source_match_165 X Y Z W a b hX hY hZ hW v
  · exact source_match_166 X Y Z W a b hX hY hZ hW v
  · exact source_match_167 X Y Z W a b hX hY hZ hW v
  · exact source_match_168 X Y Z W a b hX hY hZ hW v
  · exact source_match_169 X Y Z W a b hX hY hZ hW v
  · exact source_match_170 X Y Z W a b hX hY hZ hW v
  · exact source_match_171 X Y Z W a b hX hY hZ hW v
  · exact source_match_172 X Y Z W a b hX hY hZ hW v
  · exact source_match_173 X Y Z W a b hX hY hZ hW v
  · exact source_match_174 X Y Z W a b hX hY hZ hW v
  · exact source_match_175 X Y Z W a b hX hY hZ hW v
  · exact source_match_176 X Y Z W a b hX hY hZ hW v
  · exact source_match_177 X Y Z W a b hX hY hZ hW v
  · exact source_match_178 X Y Z W a b hX hY hZ hW v
  · exact source_match_179 X Y Z W a b hX hY hZ hW v
  · exact source_match_180 X Y Z W a b hX hY hZ hW v
  · exact source_match_181 X Y Z W a b hX hY hZ hW v
  · exact source_match_182 X Y Z W a b hX hY hZ hW v
  · exact source_match_183 X Y Z W a b hX hY hZ hW v
  · exact source_match_184 X Y Z W a b hX hY hZ hW v
  · exact source_match_185 X Y Z W a b hX hY hZ hW v
  · exact source_match_186 X Y Z W a b hX hY hZ hW v
  · exact source_match_187 X Y Z W a b hX hY hZ hW v
  · exact source_match_188 X Y Z W a b hX hY hZ hW v
  · exact source_match_189 X Y Z W a b hX hY hZ hW v
  · exact source_match_190 X Y Z W a b hX hY hZ hW v
  · exact source_match_191 X Y Z W a b hX hY hZ hW v
  · exact source_match_192 X Y Z W a b hX hY hZ hW v
  · exact source_match_193 X Y Z W a b hX hY hZ hW v
  · exact source_match_194 X Y Z W a b hX hY hZ hW v
  · exact source_match_195 X Y Z W a b hX hY hZ hW v
  · exact source_match_196 X Y Z W a b hX hY hZ hW v
  · exact source_match_197 X Y Z W a b hX hY hZ hW v
  · exact source_match_198 X Y Z W a b hX hY hZ hW v
  · exact source_match_199 X Y Z W a b hX hY hZ hW v
  · exact source_match_200 X Y Z W a b hX hY hZ hW v
  · exact source_match_201 X Y Z W a b hX hY hZ hW v
  · exact source_match_202 X Y Z W a b hX hY hZ hW v
  · exact source_match_203 X Y Z W a b hX hY hZ hW v
  · exact source_match_204 X Y Z W a b hX hY hZ hW v
  · exact source_match_205 X Y Z W a b hX hY hZ hW v
  · exact source_match_206 X Y Z W a b hX hY hZ hW v
  · exact source_match_207 X Y Z W a b hX hY hZ hW v
  · exact source_match_208 X Y Z W a b hX hY hZ hW v
  · exact source_match_209 X Y Z W a b hX hY hZ hW v
  · exact source_match_210 X Y Z W a b hX hY hZ hW v
  · exact source_match_211 X Y Z W a b hX hY hZ hW v
  · exact source_match_212 X Y Z W a b hX hY hZ hW v
  · exact source_match_213 X Y Z W a b hX hY hZ hW v
  · exact source_match_214 X Y Z W a b hX hY hZ hW v
  · exact source_match_215 X Y Z W a b hX hY hZ hW v
  · exact source_match_216 X Y Z W a b hX hY hZ hW v
  · exact source_match_217 X Y Z W a b hX hY hZ hW v
  · exact source_match_218 X Y Z W a b hX hY hZ hW v
  · exact source_match_219 X Y Z W a b hX hY hZ hW v
  · exact source_match_220 X Y Z W a b hX hY hZ hW v
  · exact source_match_221 X Y Z W a b hX hY hZ hW v
  · exact source_match_222 X Y Z W a b hX hY hZ hW v
  · exact source_match_223 X Y Z W a b hX hY hZ hW v
  · exact source_match_224 X Y Z W a b hX hY hZ hW v
  · exact source_match_225 X Y Z W a b hX hY hZ hW v
  · exact source_match_226 X Y Z W a b hX hY hZ hW v
  · exact source_match_227 X Y Z W a b hX hY hZ hW v
  · exact source_match_228 X Y Z W a b hX hY hZ hW v
  · exact source_match_229 X Y Z W a b hX hY hZ hW v
  · exact source_match_230 X Y Z W a b hX hY hZ hW v
  · exact source_match_231 X Y Z W a b hX hY hZ hW v
  · exact source_match_232 X Y Z W a b hX hY hZ hW v
  · exact source_match_233 X Y Z W a b hX hY hZ hW v
  · exact source_match_234 X Y Z W a b hX hY hZ hW v
  · exact source_match_235 X Y Z W a b hX hY hZ hW v
  · exact source_match_236 X Y Z W a b hX hY hZ hW v
  · exact source_match_237 X Y Z W a b hX hY hZ hW v
  · exact source_match_238 X Y Z W a b hX hY hZ hW v
  · exact source_match_239 X Y Z W a b hX hY hZ hW v
  · exact source_match_240 X Y Z W a b hX hY hZ hW v
  · exact source_match_241 X Y Z W a b hX hY hZ hW v
  · exact source_match_242 X Y Z W a b hX hY hZ hW v
  · exact source_match_243 X Y Z W a b hX hY hZ hW v
  · exact source_match_244 X Y Z W a b hX hY hZ hW v
  · exact source_match_245 X Y Z W a b hX hY hZ hW v
  · exact source_match_246 X Y Z W a b hX hY hZ hW v
  · exact source_match_247 X Y Z W a b hX hY hZ hW v
  · exact source_match_248 X Y Z W a b hX hY hZ hW v
  · exact source_match_249 X Y Z W a b hX hY hZ hW v
  · exact source_match_250 X Y Z W a b hX hY hZ hW v
  · exact source_match_251 X Y Z W a b hX hY hZ hW v
  · exact source_match_252 X Y Z W a b hX hY hZ hW v
  · exact source_match_253 X Y Z W a b hX hY hZ hW v
  · exact source_match_254 X Y Z W a b hX hY hZ hW v
  · exact source_match_255 X Y Z W a b hX hY hZ hW v
  · exact source_match_256 X Y Z W a b hX hY hZ hW v
  · exact source_match_257 X Y Z W a b hX hY hZ hW v
  · exact source_match_258 X Y Z W a b hX hY hZ hW v
  · exact source_match_259 X Y Z W a b hX hY hZ hW v
  · exact source_match_260 X Y Z W a b hX hY hZ hW v
  · exact source_match_261 X Y Z W a b hX hY hZ hW v
  · exact source_match_262 X Y Z W a b hX hY hZ hW v
  · exact source_match_263 X Y Z W a b hX hY hZ hW v
  · exact source_match_264 X Y Z W a b hX hY hZ hW v
  · exact source_match_265 X Y Z W a b hX hY hZ hW v
  · exact source_match_266 X Y Z W a b hX hY hZ hW v
  · exact source_match_267 X Y Z W a b hX hY hZ hW v
  · exact source_match_268 X Y Z W a b hX hY hZ hW v
  · exact source_match_269 X Y Z W a b hX hY hZ hW v
  · exact source_match_270 X Y Z W a b hX hY hZ hW v
  · exact source_match_271 X Y Z W a b hX hY hZ hW v
  · exact source_match_272 X Y Z W a b hX hY hZ hW v
  · exact source_match_273 X Y Z W a b hX hY hZ hW v
  · exact source_match_274 X Y Z W a b hX hY hZ hW v
  · exact source_match_275 X Y Z W a b hX hY hZ hW v
  · exact source_match_276 X Y Z W a b hX hY hZ hW v
  · exact source_match_277 X Y Z W a b hX hY hZ hW v
  · exact source_match_278 X Y Z W a b hX hY hZ hW v
  · exact source_match_279 X Y Z W a b hX hY hZ hW v
  · exact source_match_280 X Y Z W a b hX hY hZ hW v
  · exact source_match_281 X Y Z W a b hX hY hZ hW v
  · exact source_match_282 X Y Z W a b hX hY hZ hW v
  · exact source_match_283 X Y Z W a b hX hY hZ hW v
  · exact source_match_284 X Y Z W a b hX hY hZ hW v
  · exact source_match_285 X Y Z W a b hX hY hZ hW v
  · exact source_match_286 X Y Z W a b hX hY hZ hW v
  · exact source_match_287 X Y Z W a b hX hY hZ hW v
  · exact source_match_288 X Y Z W a b hX hY hZ hW v
  · exact source_match_289 X Y Z W a b hX hY hZ hW v
  · exact source_match_290 X Y Z W a b hX hY hZ hW v
  · exact source_match_291 X Y Z W a b hX hY hZ hW v
  · exact source_match_292 X Y Z W a b hX hY hZ hW v
  · exact source_match_293 X Y Z W a b hX hY hZ hW v
  · exact source_match_294 X Y Z W a b hX hY hZ hW v
  · exact source_match_295 X Y Z W a b hX hY hZ hW v
  · exact source_match_296 X Y Z W a b hX hY hZ hW v
  · exact source_match_297 X Y Z W a b hX hY hZ hW v
  · exact source_match_298 X Y Z W a b hX hY hZ hW v
  · exact source_match_299 X Y Z W a b hX hY hZ hW v
  · exact source_match_300 X Y Z W a b hX hY hZ hW v
  · exact source_match_301 X Y Z W a b hX hY hZ hW v
  · exact source_match_302 X Y Z W a b hX hY hZ hW v
  · exact source_match_303 X Y Z W a b hX hY hZ hW v
  · exact source_match_304 X Y Z W a b hX hY hZ hW v
  · exact source_match_305 X Y Z W a b hX hY hZ hW v
  · exact source_match_306 X Y Z W a b hX hY hZ hW v
  · exact source_match_307 X Y Z W a b hX hY hZ hW v
  · exact source_match_308 X Y Z W a b hX hY hZ hW v
  · exact source_match_309 X Y Z W a b hX hY hZ hW v
  · exact source_match_310 X Y Z W a b hX hY hZ hW v
  · exact source_match_311 X Y Z W a b hX hY hZ hW v
  · exact source_match_312 X Y Z W a b hX hY hZ hW v
  · exact source_match_313 X Y Z W a b hX hY hZ hW v
  · exact source_match_314 X Y Z W a b hX hY hZ hW v
  · exact source_match_315 X Y Z W a b hX hY hZ hW v
  · exact source_match_316 X Y Z W a b hX hY hZ hW v
  · exact source_match_317 X Y Z W a b hX hY hZ hW v
  · exact source_match_318 X Y Z W a b hX hY hZ hW v
  · exact source_match_319 X Y Z W a b hX hY hZ hW v
  · exact source_match_320 X Y Z W a b hX hY hZ hW v
  · exact source_match_321 X Y Z W a b hX hY hZ hW v
  · exact source_match_322 X Y Z W a b hX hY hZ hW v
  · exact source_match_323 X Y Z W a b hX hY hZ hW v
  · exact source_match_324 X Y Z W a b hX hY hZ hW v
  · exact source_match_325 X Y Z W a b hX hY hZ hW v
  · exact source_match_326 X Y Z W a b hX hY hZ hW v
  · exact source_match_327 X Y Z W a b hX hY hZ hW v
  · exact source_match_328 X Y Z W a b hX hY hZ hW v
  · exact source_match_329 X Y Z W a b hX hY hZ hW v
  · exact source_match_330 X Y Z W a b hX hY hZ hW v
  · exact source_match_331 X Y Z W a b hX hY hZ hW v
  · exact source_match_332 X Y Z W a b hX hY hZ hW v
  · exact source_match_333 X Y Z W a b hX hY hZ hW v
  · exact source_match_334 X Y Z W a b hX hY hZ hW v
  · exact source_match_335 X Y Z W a b hX hY hZ hW v
  · exact source_match_336 X Y Z W a b hX hY hZ hW v
  · exact source_match_337 X Y Z W a b hX hY hZ hW v
  · exact source_match_338 X Y Z W a b hX hY hZ hW v
  · exact source_match_339 X Y Z W a b hX hY hZ hW v
  · exact source_match_340 X Y Z W a b hX hY hZ hW v
  · exact source_match_341 X Y Z W a b hX hY hZ hW v
  · exact source_match_342 X Y Z W a b hX hY hZ hW v
  · exact source_match_343 X Y Z W a b hX hY hZ hW v
  · exact source_match_344 X Y Z W a b hX hY hZ hW v
  · exact source_match_345 X Y Z W a b hX hY hZ hW v
  · exact source_match_346 X Y Z W a b hX hY hZ hW v
  · exact source_match_347 X Y Z W a b hX hY hZ hW v
  · exact source_match_348 X Y Z W a b hX hY hZ hW v
  · exact source_match_349 X Y Z W a b hX hY hZ hW v
  · exact source_match_350 X Y Z W a b hX hY hZ hW v
  · exact source_match_351 X Y Z W a b hX hY hZ hW v
  · exact source_match_352 X Y Z W a b hX hY hZ hW v
  · exact source_match_353 X Y Z W a b hX hY hZ hW v
  · exact source_match_354 X Y Z W a b hX hY hZ hW v
  · exact source_match_355 X Y Z W a b hX hY hZ hW v
  · exact source_match_356 X Y Z W a b hX hY hZ hW v
  · exact source_match_357 X Y Z W a b hX hY hZ hW v
  · exact source_match_358 X Y Z W a b hX hY hZ hW v
  · exact source_match_359 X Y Z W a b hX hY hZ hW v
  · exact source_match_360 X Y Z W a b hX hY hZ hW v
  · exact source_match_361 X Y Z W a b hX hY hZ hW v
  · exact source_match_362 X Y Z W a b hX hY hZ hW v
  · exact source_match_363 X Y Z W a b hX hY hZ hW v
  · exact source_match_364 X Y Z W a b hX hY hZ hW v
  · exact source_match_365 X Y Z W a b hX hY hZ hW v
  · exact source_match_366 X Y Z W a b hX hY hZ hW v
  · exact source_match_367 X Y Z W a b hX hY hZ hW v
  · exact source_match_368 X Y Z W a b hX hY hZ hW v
  · exact source_match_369 X Y Z W a b hX hY hZ hW v

#print axioms sourceRows_match

end SmallLevelTwentySixUnitMMP
end
end

/-! ## SmallLevelTwentySixUnitMMPSupportV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMP

compact_elimination_proof theorem support_eq_mmm : support=SmallLevelTwentySixUnitMMM.support := rfl

compact_elimination_proof theorem support_injective : Function.Injective support := by
  rw [support_eq_mmm]
  exact SmallLevelTwentySixUnitMMM.support_injective

#print axioms support_injective
end SmallLevelTwentySixUnitMMP
end
end

/-! ## SmallLevelTwentySixUnitMMPScaledContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMP
open SmallLevelTwentySixUnitMMM (actualGrid)
open Complex Matrix SmallLevelTwentySixGrid SmallLevelPrimeRates SmallLevelFiniteGridSupport

compact_elimination_proof
/-- Exact identification for all four sign patterns obtained from the MMP base. -/
theorem scaled_sourceRows_actual (m : ℕ) (f : ℕ→ℂ) (ε u v s : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₃ : badParameter f 13= v) (w : Fin 780→ℂ) (i : Fin 370) :
    sourceRows (u*parameter 2 m s) (parameter 3 m s) (v*parameter 13 m s)
      (parameter 5 m s) (badParameter f 3) (badParameter f 5) w i=
      gridLeadingRows m f ε s w (selectedSource i) := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  rw [sourceRows_match _ _ _ _ _ _
    (mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) s))
    (parameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) s))
    (parameter_ne_zero 5 m (by decide) s)]
  rw [laurentRows_sign_scale _ _ _ _ _ _ _ u v hu hv]
  rw [leadingRows_laurent,hη,h₂,h₁₃]
  simp only [one_mul]

compact_elimination_proof theorem scaled_leading_kernel_exists (m : ℕ) (f : ℕ→ℂ) (ε u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₃ : badParameter f 13= v) :
    ∃ s : ℂ,∀ w : Fin 320→ℂ,
      restrictedLeadingMatrix selectedSource support m f ε s *ᵥ w=0 → w=0 := by
  obtain ⟨s,hs⟩:=SmallLevelTwentySixScaledContinuationMinor.mmp_nonzero_on_scaled_curve
    (badParameter f 3) u v (by rcases hu with rfl|rfl <;> norm_num) m
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  refine ⟨s,?_⟩
  apply matrix_kernel_of_support support support_injective
    (selectedLeadingLinearMap selectedSource m f ε s)
  intro w hw
  apply source_kernel_zero _ _ _ _ (badParameter f 3) (badParameter f 5)
    (mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) s))
    (parameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) s))
    (parameter_ne_zero 5 m (by decide) s) w _ hs
  intro i
  rw [scaled_sourceRows_actual m f ε u v s hu hv hη h₂ h₁₃]
  exact congrFun hw i

compact_elimination_proof
/-- Original additive meromorphic continuation in four of the eight sign cases. -/
theorem original_grid_continuation_scaled (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    {ε : ℂ} (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε)
    (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u) (h₁₃ : badParameter f 13= v) :
    ∃ B : ℝ,∃ G : ℂ→Fin 320→ℂ,
      (∀ i x,MeromorphicNFAt (fun z => G z i) x) ∧
      ∀ z,B<z.re → G z=actualGrid m f z := by
  obtain ⟨B,E,hF,hE,hrow⟩:=initial_system_of_laws m hm hf hε hlaw
  have hrestrict (s : ℂ) (w : Fin 780→ℂ) (i : Fin 370) :
      gridLeadingRows m f ε s (extension support (fun j => w (support j))) (selectedSource i)=
        gridLeadingRows m f ε s w (selectedSource i) := by
    exact leadingRows_restrict m f ε s w (selectedSource i)
  refine ⟨B,?_⟩
  apply QuantitativeArithmeticRectangularContinuation.meromorphic_continuation
    B (actualGrid m f) (restrictedLeadingMatrix selectedSource support m f ε)
    (restrictedShiftMatrix selectedSource support m f ε)
    (fun n s i => E (selectedSource i) n s)
    (fun i z hz => hF (support i) z hz)
    (fun x i j => restrictedLeadingMatrix_analytic selectedSource support m f ε i j x)
    (scaled_leading_kernel_exists m f ε u v hu hv hη h₂ h₁₃)
    (fun n x i j => restrictedShiftMatrix_analytic selectedSource support m f ε n i j x)
    (fun n i z hz => (hE n (selectedSource i) z hz).meromorphicAt)
  intro n s hs
  funext i
  simp only [Pi.add_apply,Finset.sum_apply]
  change (restrictedLeadingMatrix selectedSource support m f ε s *ᵥ
    (fun j => gridVector (2*m) f s (support j))) i =
    E (selectedSource i) n s + ∑ c ∈ Finset.range n,
      (restrictedShiftMatrix selectedSource support m f ε c s *ᵥ
        (fun j => gridVector (2*m) f (s+((c:ℂ)+1)) (support j))) i
  rw [restrictedLeadingMatrix_mulVec,hrestrict]
  simp_rw [restrictedShiftMatrix_mulVec,support_eq_mmm,shiftRows_restrict]
  exact hrow n s hs (selectedSource i)

#print axioms original_grid_continuation_scaled
end SmallLevelTwentySixUnitMMP
end
end

/-! ## SmallLevelTwentySixUnitMMPWeightRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMP
open Complex
compact_elimination_proof theorem weight_row0 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((-2)*Y^2) + (2*Y^4) + ((-2)*X*Y^4) + ((-3)*X^2) + ((-1)*X^2*Z) + ((-2)*X^2*Y*a) + (2*X^2*Y^2) + ((-2)*X^3) + (1*X^3*Y*a) + ((-1)*X^3*Y^2) + ((-1)*X^4))*v 300 + (((-2)*Y^2) + (2*Y^3*a) + ((-2)*X*Y^2) + ((-3)*X^2) + (1*X^2*Y*a) + ((-1)*X^2*Y^2) + ((-2)*X^3) + ((-2)*X^4))*v 540=0 := by
  have hr0:=residual_0 X Y Z W a b hX hY hZ hW v hv
  have hr1:=residual_24 X Y Z W a b hX hY hZ hW v hv
  have hp:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (((-1)*X^3*Y^2))*hr0 + (((-1)*X^3*Y^2))*hr1 + (((-2)*Y^2) + (2*Y^4) + ((-2)*X*Y^4) + ((-3)*X^2) + ((-1)*X^2*Z) + ((-2)*X^2*Y*a) + (2*X^2*Y^2) + ((-2)*X^3) + (1*X^3*Y*a) + ((-1)*X^3*Y^2) + ((-1)*X^4))*hp

compact_elimination_proof theorem weight_row1 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((-1)) + ((-1)*Y*a) + (1*Y^3*a) + (1*Y^4) + ((-1)*X*Y^2) + ((-1)*X*Y^3*a) + ((-1)*X*Y^4) + ((-1)*X^2) + (1*X^3))*v 300 + (((-1)) + ((-1)*Y^2) + (1*Y^2*a^2) + (1*Y^3*a) + ((-1)*X) + ((-1)*X*Y*a) + ((-1)*X*Y^2))*v 540=0 := by
  have hr0:=residual_0 X Y Z W a b hX hY hZ hW v hv
  have hp:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) ((1*X^2*Y^2))*hr0 + (((-1)) + ((-1)*Y*a) + (1*Y^3*a) + (1*Y^4) + ((-1)*X*Y^2) + ((-1)*X*Y^3*a) + ((-1)*X*Y^4) + ((-1)*X^2) + (1*X^3))*hp

compact_elimination_proof theorem weight_row2 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((2*Y^2) + ((-2)*Y^4) + (2*X) + ((-4)*X*Y^2) + (4*X*Y^4) + (3*X^2) + (1*X^2*W*b) + (1*X^2*W^2) + (1*X^2*Z) + (1*X^2*Y*a) + (1*X^2*Y^2) + ((-2)*X^2*Y^4) + ((-3)*X^3) + ((-1)*X^3*W*b) + ((-1)*X^3*W^2) + ((-1)*X^3*Z) + ((-2)*X^3*Y*a) + (2*X^3*Y^2) + ((-1)*X^4) + (1*X^4*Y*a) + ((-1)*X^4*Y^2) + ((-1)*X^5))*v 300 + ((2*Y^2) + ((-2)*Y^3*a) + (2*X) + ((-2)*X*Y*a) + (2*X*Y^3*a) + (2*X^2) + ((-1)*X^3) + (1*X^3*Y*a) + ((-3)*X^3*Y^2) + ((-1)*X^4) + (1*X^4*Y*a) + (1*X^4*Y^2) + ((-2)*X^5))*v 540=0 := by
  have hr0:=residual_0 X Y Z W a b hX hY hZ hW v hv
  have hr1:=residual_8 X Y Z W a b hX hY hZ hW v hv
  have hr2:=residual_42 X Y Z W a b hX hY hZ hW v hv
  have hp:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (((-1)*X^4*Y^2))*hr0 + (((-1)*X^3*Y^2))*hr1 + (((1*X^3*Y^2*W^2)/(Z)))*hr2 + ((2*Y^2) + ((-2)*Y^4) + (2*X) + ((-4)*X*Y^2) + (4*X*Y^4) + (3*X^2) + (1*X^2*W*b) + (1*X^2*W^2) + (1*X^2*Z) + (1*X^2*Y*a) + (1*X^2*Y^2) + ((-2)*X^2*Y^4) + ((-3)*X^3) + ((-1)*X^3*W*b) + ((-1)*X^3*W^2) + ((-1)*X^3*Z) + ((-2)*X^3*Y*a) + (2*X^3*Y^2) + ((-1)*X^4) + (1*X^4*Y*a) + ((-1)*X^4*Y^2) + ((-1)*X^5))*hp

compact_elimination_proof theorem weight_row3 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((-2)*Y^2) + (2*Y^4) + (1*X) + ((-1)*X*W*b) + (1*X*W^2) + ((-1)*X*Y^2) + (1*X*Y^2*W*b) + ((-1)*X*Y^2*W^2) + ((-2)*X*Y^4) + ((-2)*X^2*Y*a) + (1*X^2*Y^2) + ((-1)*X^2*Y^2*W*b) + (1*X^2*Y^2*W^2) + ((-1)*X^3) + (2*X^3*Y*a) + (1*X^4))*v 300 + (((-2)*Y^2) + (2*Y^3*a) + (1*X) + ((-1)*X*W*b) + (1*X*W^2) + ((-1)*X*Y*a) + (1*X*Y*W*a*b) + ((-1)*X*Y*W^2*a) + ((-2)*X*Y^2) + ((-1)*X^2) + ((-1)*X^2*W*b) + (1*X^2*W^2) + (1*X^3) + (1*X^5))*v 540=0 := by
  have hr0:=residual_43 X Y Z W a b hX hY hZ hW v hv
  have hp:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (((1*X^5*W^2)/(Z)))*hr0 + (((-2)*Y^2) + (2*Y^4) + (1*X) + ((-1)*X*W*b) + (1*X*W^2) + ((-1)*X*Y^2) + (1*X*Y^2*W*b) + ((-1)*X*Y^2*W^2) + ((-2)*X*Y^4) + ((-2)*X^2*Y*a) + (1*X^2*Y^2) + ((-1)*X^2*Y^2*W*b) + (1*X^2*Y^2*W^2) + ((-1)*X^3) + (2*X^3*Y*a) + (1*X^4))*hp

compact_elimination_proof theorem weight_row4 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((-2)*Y^2) + (2*Y^4) + ((-2)*X) + (2*X*Y^2) + ((-2)*X*Y^4) + ((-5)*X^2) + ((-1)*X^2*W*b) + ((-1)*X^2*W^2) + ((-1)*X^2*Z) + ((-1)*X^2*Y*a) + (1*X^2*Y^2) + ((-2)*X^3) + (1*X^3*Y*a) + ((-1)*X^3*Y^2) + ((-1)*X^4))*v 300 + (((-2)*Y^2) + (2*Y^3*a) + ((-2)*X) + (2*X*Y*a) + ((-2)*X*Y^2) + ((-4)*X^2) + (2*X^2*Y*a) + ((-2)*X^2*Y^2) + ((-3)*X^3) + (1*X^3*Y*a) + (1*X^3*Y^2) + ((-2)*X^4))*v 540=0 := by
  have hr0:=residual_0 X Y Z W a b hX hY hZ hW v hv
  have hr1:=residual_0 X Y Z W a b hX hY hZ hW v hv
  have hr2:=residual_0 X Y Z W a b hX hY hZ hW v hv
  have hr3:=residual_0 X Y Z W a b hX hY hZ hW v hv
  have hr4:=residual_8 X Y Z W a b hX hY hZ hW v hv
  have hr5:=residual_8 X Y Z W a b hX hY hZ hW v hv
  have hr6:=residual_10 X Y Z W a b hX hY hZ hW v hv
  have hr7:=residual_42 X Y Z W a b hX hY hZ hW v hv
  have hr8:=residual_42 X Y Z W a b hX hY hZ hW v hv
  have hr9:=residual_44 X Y Z W a b hX hY hZ hW v hv
  have hp:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (((-1)*Y^2))*hr0 + (((-1)*X*Y^2))*hr1 + (((-1)*X^2*Y^2))*hr2 + (((-1)*X^3*Y^2))*hr3 + (((-1)*X*Y^2))*hr4 + (((-1)*X^2*Y^2))*hr5 + (((-1)*Y^2))*hr6 + (((1*X*Y^2*W^2)/(Z)))*hr7 + (((1*X^2*Y^2*W^2)/(Z)))*hr8 + (((1*Y^2*W^2)/(Z)))*hr9 + (((-2)*Y^2) + (2*Y^4) + ((-2)*X) + (2*X*Y^2) + ((-2)*X*Y^4) + ((-5)*X^2) + ((-1)*X^2*W*b) + ((-1)*X^2*W^2) + ((-1)*X^2*Z) + ((-1)*X^2*Y*a) + (1*X^2*Y^2) + ((-2)*X^3) + (1*X^3*Y*a) + ((-1)*X^3*Y^2) + ((-1)*X^4))*hp

#print axioms weight_row4
end SmallLevelTwentySixUnitMMP
end
end

/-! ## SmallLevelTwentySixUnitMMPSourceZeroChartV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMP
open Complex SmallLevelTwentySixWeightZeroChart

compact_elimination_proof
/-- At the physical positive-integer parameter range, the zero-first-coordinate
projective chart is excluded directly from two checked leading equations. -/
theorem source_zero_chart (x y : ℝ) (Z W a b : ℂ)
    (hx : 2≤x ∨ x≤ -2) (hy : y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows x y Z W a b v i=0)
    (h300 : v 300=0) : ∀ j : Fin 320,v (support j)=0 := by
  have hx0 : x≠0 := by intro h; rcases hx with hh|hh <;> norm_num [h] at hh
  have hX : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx0
  have hY : (y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hy
  have h540 : v 540=0 := by
    by_contra hn
    have h0:=weight_row0 x y Z W a b hX hY hZ hW v hv
    have h1:=weight_row1 x y Z W a b hX hY hZ hW v hv
    have he0 : firstCoefficient x ((y:ℂ)^2) (a*y)*v 540=0 := by
      unfold firstCoefficient
      rw [h300,mul_zero,zero_add] at h0
      linear_combination h0
    have he1 : secondCoefficient x ((y:ℂ)^2) (a*y)*v 540=0 := by
      unfold secondCoefficient
      rw [h300,mul_zero,zero_add] at h1
      linear_combination h1
    apply no_zero_chart x (y^2) hx (sq_nonneg y) (a*y)
    · simpa only [Complex.ofReal_pow] using (mul_eq_zero.mp he0).resolve_right hn
    · simpa only [Complex.ofReal_pow] using (mul_eq_zero.mp he1).resolve_right hn
  have hh:=pivot_150 x y Z W a b hX hY hZ hW v hv
  have he : ((y:ℂ)^2/Z)*v 520=0 := by simpa [h300] using hh
  have h520 := (mul_eq_zero.mp he).resolve_left (div_ne_zero (pow_ne_zero _ hY) hZ)
  exact FreeKernel.source_zero_of_free x y Z W a b hX hY hZ hW v hv h520 h540

#print axioms source_zero_chart
end SmallLevelTwentySixUnitMMP
end
end
end
