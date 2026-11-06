module

public import QuantitativeArithmeticGridCertificateConstructorsV1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridSourceRowV1
public meta import QuantitativeArithmeticCompactCommandsV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxWordDataV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData
open QuantitativeArithmeticSmallLevelTwentyFiveKnownWords QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
def auxWord0 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 0)) (.generator 0))
def auxWord1 : Word := (.mul (.mul .one (.generator 3)) (.generator 0))
def auxWord2 : Word := (.mul .one (.generator 3))
def auxWord3 : Word := (.mul (.mul .one (.generator 3)) (.inv (.generator 0)))
def auxWord4 : Word := (.mul (.mul (.mul .one (.generator 3)) (.inv (.generator 0))) (.inv (.generator 0)))
def auxWord5 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 0))) (.inv (.generator 0)))
def auxWord6 : Word := (.mul (.mul (.mul .one (.generator 1)) (.inv (.generator 0))) (.inv (.generator 0)))
def auxWord7 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 1))) (.inv (.generator 0)))
def auxWord8 : Word := (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 0)))
def auxWord9 : Word := (.mul (.mul .one (.generator 1)) (.inv (.generator 0)))
def auxWord10 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 1)) (.inv (.generator 0)))
def auxWord11 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 1))) (.inv (.generator 1)))
def auxWord12 : Word := (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 1)))
def auxWord13 : Word := (.mul .one (.inv (.generator 1)))
def auxWord14 : Word := (.mul .one (.generator 1))
def auxWord15 : Word := (.mul (.mul .one (.generator 1)) (.generator 1))
def auxWord16 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 1)) (.generator 1))
def auxWord17 : Word := (.mul (.mul .one (.inv (.generator 1))) (.generator 0))
def auxWord18 : Word := (.mul (.mul .one (.generator 1)) (.generator 0))
def auxWord19 : Word := (.mul (.mul (.mul .one (.generator 2)) (.inv (.generator 0))) (.inv (.generator 0)))
def auxWord20 : Word := (.mul (.mul .one (.generator 2)) (.inv (.generator 0)))
def auxWord21 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 2)) (.inv (.generator 0)))
def auxWord22 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 1))) (.generator 2))
def auxWord23 : Word := (.mul (.mul .one (.inv (.generator 1))) (.generator 2))
def auxWord24 : Word := (.mul .one (.generator 2))
def auxWord25 : Word := (.mul (.mul .one (.generator 1)) (.generator 2))
def auxWord26 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 1)) (.generator 2))
def auxWord27 : Word := (.mul (.mul .one (.generator 2)) (.generator 0))
def auxWord28 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 2)) (.generator 0))
def auxWord29 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 0)) (.generator 0))
def auxWord30 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 1))) (.inv (.generator 0)))
def auxWord31 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 2))) (.inv (.generator 0)))
def auxWord32 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 2))) (.inv (.generator 1)))
def auxWord33 : Word := (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 1)))
def auxWord34 : Word := (.mul (.mul (.mul .one (.generator 1)) (.inv (.generator 2))) (.inv (.generator 1)))
def auxWord35 : Word := (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 2)))
def auxWord36 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 1))) (.generator 0))
def auxWord37 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 2))) (.generator 0))
def auxWord38 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 0))) (.inv (.generator 0)))
def auxWord39 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 2))) (.inv (.generator 0)))
def auxWord40 : Word := (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 0)))
def auxWord41 : Word := (.mul (.mul (.mul .one (.generator 1)) (.inv (.generator 2))) (.inv (.generator 0)))
def auxWord42 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 2))) (.inv (.generator 1)))
def auxWord43 : Word := (.mul .one (.inv (.generator 2)))
def auxWord44 : Word := (.mul (.mul .one (.inv (.generator 2))) (.generator 0))
def auxWord45 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 0)) (.generator 2))
def auxWord46 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 1)) (.generator 2))
def auxWord47 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 2)) (.inv (.generator 0)))
def auxWord48 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 1)) (.inv (.generator 0)))
def auxWord49 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.generator 0)) (.generator 2))
def auxWord50 : Word := (.mul (.mul .one (.generator 0)) (.generator 2))
def auxWord51 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 0)) (.generator 2))
def auxWord52 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.generator 1)) (.generator 2))
def auxWord53 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 0)) (.inv (.generator 1)))
def auxWord54 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 2)) (.generator 0))
def auxWord55 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 1))) (.inv (.generator 0)))
def auxWord56 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.generator 1)) (.inv (.generator 0)))
def auxWord57 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.generator 0)) (.inv (.generator 1)))
def auxWord58 : Word := (.mul (.mul .one (.generator 0)) (.inv (.generator 1)))
def auxWord59 : Word := (.mul (.mul .one (.inv (.generator 0))) (.generator 1))
def auxWord60 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 1))) (.generator 0))
def auxWord61 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.generator 1)) (.generator 0))
def auxWord62 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 2)) (.inv (.generator 0)))
def auxWord63 : Word := (.mul (.mul (.mul .one (.generator 3)) (.inv (.generator 1))) (.inv (.generator 0)))
def auxWord64 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.generator 1)) (.generator 3))
def auxWord65 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 1)) (.generator 3))
def auxWord66 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 0)) (.generator 2))
def auxWord67 : Word := (.mul (.mul .one (.generator 3)) (.generator 2))
def auxWord68 : Word := (.mul (.mul (.mul .one (.generator 3)) (.inv (.generator 0))) (.generator 2))
def auxWord69 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 2))) (.generator 3))
def auxWord70 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 0)) (.generator 3))
def auxWord71 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 0)) (.inv (.generator 1)))
def auxWord72 : Word := (.mul (.mul .one (.generator 3)) (.inv (.generator 1)))
def auxWord73 : Word := (.mul (.mul (.mul .one (.generator 3)) (.inv (.generator 0))) (.inv (.generator 1)))
def auxWord74 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 0)) (.generator 1))
def auxWord75 : Word := (.mul (.mul .one (.generator 3)) (.generator 1))
def auxWord76 : Word := (.mul (.mul (.mul .one (.generator 3)) (.inv (.generator 0))) (.generator 1))
def auxWord77 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 0)) (.inv (.generator 2)))
def auxWord78 : Word := (.mul (.mul .one (.generator 3)) (.inv (.generator 2)))
def auxWord79 : Word := (.mul (.mul (.mul .one (.generator 3)) (.inv (.generator 0))) (.inv (.generator 2)))
def auxWord80 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 1))) (.generator 3))
def auxWord81 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 1))) (.generator 3))
def auxWord82 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 1)) (.generator 0))
def auxWord83 : Word := (.mul (.mul (.mul .one (.generator 3)) (.inv (.generator 2))) (.generator 0))
def auxWord84 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 1))) (.inv (.generator 0)))
def auxWord85 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 1)) (.inv (.generator 0)))
def auxWord86 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 0))) (.inv (.generator 1)))
def auxWord87 : Word := (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 1)))
def auxWord88 : Word := (.mul (.mul .one (.generator 0)) (.generator 1))
def auxWord89 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 1))) (.generator 0))
def auxWord90 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 1)) (.generator 0))
def auxWord91 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.generator 2)) (.inv (.generator 0)))
def auxWord92 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 0))) (.generator 2))
def auxWord93 : Word := (.mul (.mul .one (.inv (.generator 0))) (.generator 2))
def auxWord94 : Word := (.mul (.mul (.mul .one (.generator 1)) (.inv (.generator 0))) (.generator 2))
def auxWord95 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 1)) (.generator 2))
def auxWord96 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.generator 2)) (.inv (.generator 1)))
def auxWord97 : Word := (.mul (.mul .one (.generator 2)) (.inv (.generator 1)))
def auxWord98 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 2)) (.inv (.generator 1)))
def auxWord99 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.generator 2)) (.generator 0))
def auxWord100 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.generator 2)) (.generator 2))
def auxWord101 : Word := (.mul (.mul .one (.generator 2)) (.generator 2))
def auxWord102 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 2)) (.generator 2))
def auxWord103 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 2))) (.inv (.generator 1)))
def auxWord104 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 1))) (.inv (.generator 1)))
def auxWord105 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 2))) (.generator 1))
def auxWord106 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 0))) (.inv (.generator 2)))
def auxWord107 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.generator 1)) (.inv (.generator 0)))
def auxWord108 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 2))) (.inv (.generator 0)))
def auxWord109 : Word := (.mul (.mul .one (.inv (.generator 2))) (.generator 1))
def auxWord110 : Word := (.mul (.mul .one (.generator 0)) (.inv (.generator 2)))
def auxWord111 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 2))) (.generator 0))
def auxWord112 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 0)) (.generator 2))
def auxWord113 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 1))) (.generator 2))
def auxWord114 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 0)) (.inv (.generator 1)))
def auxWord115 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 1))) (.inv (.generator 1)))
def auxWord116 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.generator 1)) (.generator 1))
def auxWord117 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 0))) (.generator 1))
def auxWord118 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 0)) (.generator 3))
def auxWord119 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 0))) (.generator 3))
def auxWord120 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.generator 1)) (.generator 2))
def auxWord121 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 0))) (.inv (.generator 1)))
def auxWord122 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 1))) (.inv (.generator 1)))
def auxWord123 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 1)) (.generator 1))
def auxWord124 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 0)) (.generator 1))
def auxWord125 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 0))) (.generator 2))
def auxWord126 : Word := (.mul (.mul (.mul .one (.generator 2)) (.inv (.generator 1))) (.inv (.generator 1)))
def auxWord127 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.generator 1)) (.generator 1))
def auxWord128 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 0)) (.inv (.generator 2)))
def auxWord129 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 1))) (.generator 2))
def auxWord130 : Word := (.mul (.mul (.mul .one (.generator 3)) (.inv (.generator 1))) (.generator 2))
def auxWord131 : Word := (.mul (.mul (.mul .one (.generator 2)) (.inv (.generator 0))) (.generator 3))
def auxWord132 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 1))) (.generator 2))
def auxWord133 : Word := (.mul (.mul (.mul .one (.generator 2)) (.inv (.generator 0))) (.inv (.generator 1)))
def auxWord134 : Word := (.mul (.mul (.mul .one (.generator 2)) (.inv (.generator 0))) (.generator 2))
def auxWord135 : Word := (.mul (.mul (.mul .one (.generator 2)) (.inv (.generator 1))) (.generator 2))
def auxWord136 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 2))) (.generator 1))
def auxWord137 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 1))) (.inv (.generator 2)))
def auxWord138 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 0))) (.inv (.generator 2)))
def auxWord139 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 2))) (.inv (.generator 1)))
def auxWord140 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 2))) (.inv (.generator 0)))
def auxWord141 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 0))) (.generator 3))
def auxWord142 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 2)) (.generator 3))
def auxWord143 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 0))) (.inv (.generator 1)))
def auxWord144 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 2)) (.inv (.generator 1)))
def auxWord145 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.generator 0)) (.inv (.generator 1)))
def auxWord146 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 2)) (.generator 2))
def auxWord147 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.generator 0)) (.generator 3))
def auxWord148 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 1)) (.inv (.generator 2)))
def auxWord149 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 2)) (.generator 2))
def auxWord150 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.generator 2)) (.inv (.generator 1)))
def auxWord151 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.generator 2)) (.generator 2))
def auxWord152 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 2)) (.inv (.generator 1)))
def auxWord153 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 2)) (.generator 2))

end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxActualDataBundleV4 -/
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData
open QuantitativeArithmeticSmallLevelTwentyFiveKnownWords
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
compact_certificate def auxSource0 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-44100) (1) (44100) (44100) (-1050) ((2,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource1 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-22050) (2) (44100) (11025) (-525) ((0,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource2 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-14700) (3) (44100) (4900) (-350) ((2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource3 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-11025) (4) (44100) ((11025/4)) ((-525/2)) ((-2,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource4 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-8820) (5) (44100) (1764) (-210) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource5 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-7350) (6) (44100) (1225) (-175) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource6 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-6300) (7) (44100) (900) (-150) ((2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource7 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-4900) (9) (44100) ((4900/9)) ((-350/3)) ((2,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource8 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-4410) (10) (44100) (441) (-105) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource9 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-3675) (12) (44100) ((1225/4)) ((-175/2)) ((-2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource10 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-3150) (14) (44100) (225) (-75) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource11 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-2940) (15) (44100) (196) (-70) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource12 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-2450) (18) (44100) ((1225/9)) ((-175/3)) ((0,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource13 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-2205) (20) (44100) ((441/4)) ((-105/2)) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource14 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-2100) (21) (44100) (100) (-50) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource15 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-1764) (25) (44100) ((1764/25)) (-42) ((2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource16 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-1575) (28) (44100) ((225/4)) ((-75/2)) ((-2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource17 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-1470) (30) (44100) (49) (-35) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource18 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-1260) (35) (44100) (36) (-30) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource19 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-1225) (36) (44100) ((1225/36)) ((-175/6)) ((-2,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource20 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-1050) (42) (44100) (25) (-25) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource21 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-980) (45) (44100) ((196/9)) ((-70/3)) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource22 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-900) (49) (44100) ((900/49)) ((-150/7)) ((2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource23 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-882) (50) (44100) ((441/25)) (-21) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource24 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-735) (60) (44100) ((49/4)) ((-35/2)) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource25 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-700) (63) (44100) ((100/9)) ((-50/3)) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource26 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-630) (70) (44100) (9) (-15) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource27 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-588) (75) (44100) ((196/25)) (-14) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource28 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-525) (84) (44100) ((25/4)) ((-25/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource29 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-490) (90) (44100) ((49/9)) ((-35/3)) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource30 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-450) (98) (44100) ((225/49)) ((-75/7)) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource31 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-441) (100) (44100) ((441/100)) ((-21/2)) ((-2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource32 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-420) (105) (44100) (4) (-10) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource33 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-350) (126) (44100) ((25/9)) ((-25/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource34 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-315) (140) (44100) ((9/4)) ((-15/2)) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource35 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-300) (147) (44100) ((100/49)) ((-50/7)) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource36 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-294) (150) (44100) ((49/25)) (-7) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource37 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-252) (175) (44100) ((36/25)) (-6) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource38 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-245) (180) (44100) ((49/36)) ((-35/6)) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource39 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-225) (196) (44100) ((225/196)) ((-75/14)) ((-2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource40 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-210) (210) (44100) (1) (-5) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource41 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-196) (225) (44100) ((196/225)) ((-14/3)) ((2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource42 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-180) (245) (44100) ((36/49)) ((-30/7)) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource43 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-175) (252) (44100) ((25/36)) ((-25/6)) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource44 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-150) (294) (44100) ((25/49)) ((-25/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource45 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-147) (300) (44100) ((49/100)) ((-7/2)) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource46 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-140) (315) (44100) ((4/9)) ((-10/3)) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource47 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-126) (350) (44100) ((9/25)) (-3) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource48 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-105) (420) (44100) ((1/4)) ((-5/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource49 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-100) (441) (44100) ((100/441)) ((-50/21)) ((2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource50 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-98) (450) (44100) ((49/225)) ((-7/3)) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource51 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-90) (490) (44100) ((9/49)) ((-15/7)) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource52 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-84) (525) (44100) ((4/25)) (-2) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource53 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-75) (588) (44100) ((25/196)) ((-25/14)) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource54 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-70) (630) (44100) ((1/9)) ((-5/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource55 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-63) (700) (44100) ((9/100)) ((-3/2)) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource56 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-60) (735) (44100) ((4/49)) ((-10/7)) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource57 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-50) (882) (44100) ((25/441)) ((-25/21)) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource58 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-49) (900) (44100) ((49/900)) ((-7/6)) ((-2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource59 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-45) (980) (44100) ((9/196)) ((-15/14)) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource60 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-42) (1050) (44100) ((1/25)) (-1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource61 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-36) (1225) (44100) ((36/1225)) ((-6/7)) ((2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource62 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-35) (1260) (44100) ((1/36)) ((-5/6)) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource63 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-30) (1470) (44100) ((1/49)) ((-5/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource64 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-28) (1575) (44100) ((4/225)) ((-2/3)) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource65 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-25) (1764) (44100) ((25/1764)) ((-25/42)) ((-2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource66 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-21) (2100) (44100) ((1/100)) ((-1/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource67 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-20) (2205) (44100) ((4/441)) ((-10/21)) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource68 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-18) (2450) (44100) ((9/1225)) ((-3/7)) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource69 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-15) (2940) (44100) ((1/196)) ((-5/14)) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource70 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-14) (3150) (44100) ((1/225)) ((-1/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource71 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-12) (3675) (44100) ((4/1225)) ((-2/7)) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource72 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-10) (4410) (44100) ((1/441)) ((-5/21)) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource73 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-9) (4900) (44100) ((9/4900)) ((-3/14)) ((-2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource74 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-7) (6300) (44100) ((1/900)) ((-1/6)) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource75 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-6) (7350) (44100) ((1/1225)) ((-1/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource76 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-5) (8820) (44100) ((1/1764)) ((-5/42)) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource77 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-4) (11025) (44100) ((4/11025)) ((-2/21)) ((2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource78 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-3) (14700) (44100) ((1/4900)) ((-1/14)) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource79 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-2) (22050) (44100) ((1/11025)) ((-1/21)) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource80 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (-1) (44100) (44100) ((1/44100)) ((-1/42)) ((-2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource81 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (1) (-44100) (44100) ((1/44100)) ((1/42)) ((-2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource82 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (2) (-22050) (44100) ((1/11025)) ((1/21)) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource83 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (3) (-14700) (44100) ((1/4900)) ((1/14)) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource84 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (4) (-11025) (44100) ((4/11025)) ((2/21)) ((2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource85 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (5) (-8820) (44100) ((1/1764)) ((5/42)) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource86 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (6) (-7350) (44100) ((1/1225)) ((1/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource87 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (7) (-6300) (44100) ((1/900)) ((1/6)) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource88 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (9) (-4900) (44100) ((9/4900)) ((3/14)) ((-2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource89 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (10) (-4410) (44100) ((1/441)) ((5/21)) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource90 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (12) (-3675) (44100) ((4/1225)) ((2/7)) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource91 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (14) (-3150) (44100) ((1/225)) ((1/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource92 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (15) (-2940) (44100) ((1/196)) ((5/14)) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource93 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (18) (-2450) (44100) ((9/1225)) ((3/7)) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource94 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (20) (-2205) (44100) ((4/441)) ((10/21)) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource95 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (21) (-2100) (44100) ((1/100)) ((1/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource96 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (25) (-1764) (44100) ((25/1764)) ((25/42)) ((-2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource97 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (28) (-1575) (44100) ((4/225)) ((2/3)) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource98 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (30) (-1470) (44100) ((1/49)) ((5/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource99 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (35) (-1260) (44100) ((1/36)) ((5/6)) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource100 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (36) (-1225) (44100) ((36/1225)) ((6/7)) ((2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource101 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (42) (-1050) (44100) ((1/25)) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource102 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (45) (-980) (44100) ((9/196)) ((15/14)) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource103 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (49) (-900) (44100) ((49/900)) ((7/6)) ((-2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource104 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (50) (-882) (44100) ((25/441)) ((25/21)) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource105 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (60) (-735) (44100) ((4/49)) ((10/7)) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource106 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (63) (-700) (44100) ((9/100)) ((3/2)) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource107 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (70) (-630) (44100) ((1/9)) ((5/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource108 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (75) (-588) (44100) ((25/196)) ((25/14)) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource109 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (84) (-525) (44100) ((4/25)) (2) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource110 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (90) (-490) (44100) ((9/49)) ((15/7)) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource111 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (98) (-450) (44100) ((49/225)) ((7/3)) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource112 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (100) (-441) (44100) ((100/441)) ((50/21)) ((2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource113 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (105) (-420) (44100) ((1/4)) ((5/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource114 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (126) (-350) (44100) ((9/25)) (3) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource115 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (140) (-315) (44100) ((4/9)) ((10/3)) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource116 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (147) (-300) (44100) ((49/100)) ((7/2)) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource117 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (150) (-294) (44100) ((25/49)) ((25/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource118 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (175) (-252) (44100) ((25/36)) ((25/6)) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource119 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (180) (-245) (44100) ((36/49)) ((30/7)) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource120 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (196) (-225) (44100) ((196/225)) ((14/3)) ((2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource121 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (210) (-210) (44100) (1) (5) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource122 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (225) (-196) (44100) ((225/196)) ((75/14)) ((-2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource123 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (245) (-180) (44100) ((49/36)) ((35/6)) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource124 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (252) (-175) (44100) ((36/25)) (6) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource125 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (294) (-150) (44100) ((49/25)) (7) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource126 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (300) (-147) (44100) ((100/49)) ((50/7)) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource127 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (315) (-140) (44100) ((9/4)) ((15/2)) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource128 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (350) (-126) (44100) ((25/9)) ((25/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource129 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (420) (-105) (44100) (4) (10) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource130 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (441) (-100) (44100) ((441/100)) ((21/2)) ((-2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource131 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (450) (-98) (44100) ((225/49)) ((75/7)) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource132 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (490) (-90) (44100) ((49/9)) ((35/3)) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource133 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (525) (-84) (44100) ((25/4)) ((25/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource134 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (588) (-75) (44100) ((196/25)) (14) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource135 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (630) (-70) (44100) (9) (15) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource136 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (700) (-63) (44100) ((100/9)) ((50/3)) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource137 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (735) (-60) (44100) ((49/4)) ((35/2)) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource138 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (882) (-50) (44100) ((441/25)) (21) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource139 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (900) (-49) (44100) ((900/49)) ((150/7)) ((2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource140 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (980) (-45) (44100) ((196/9)) ((70/3)) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource141 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (1050) (-42) (44100) (25) (25) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource142 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (1225) (-36) (44100) ((1225/36)) ((175/6)) ((-2,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource143 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (1260) (-35) (44100) (36) (30) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource144 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (1470) (-30) (44100) (49) (35) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource145 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (1575) (-28) (44100) ((225/4)) ((75/2)) ((-2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource146 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (1764) (-25) (44100) ((1764/25)) (42) ((2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource147 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (2100) (-21) (44100) (100) (50) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource148 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (2205) (-20) (44100) ((441/4)) ((105/2)) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource149 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (2450) (-18) (44100) ((1225/9)) ((175/3)) ((0,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource150 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (2940) (-15) (44100) (196) (70) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource151 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (3150) (-14) (44100) (225) (75) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource152 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (3675) (-12) (44100) ((1225/4)) ((175/2)) ((-2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource153 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (4410) (-10) (44100) (441) (105) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource154 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (4900) (-9) (44100) ((4900/9)) ((350/3)) ((2,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource155 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (6300) (-7) (44100) (900) (150) ((2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource156 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (7350) (-6) (44100) (1225) (175) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource157 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (8820) (-5) (44100) (1764) (210) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource158 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (11025) (-4) (44100) ((11025/4)) ((525/2)) ((-2,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource159 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (14700) (-3) (44100) (4900) (350) ((2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource160 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (22050) (-2) (44100) (11025) (525) ((0,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource161 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1) (44100) (-1) (44100) (44100) (1050) ((2,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource162 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-11025) (1) (11025) (11025) (-1050) ((0,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource163 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-3675) (3) (11025) (1225) (-350) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource164 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-2205) (5) (11025) (441) (-210) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource165 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-1575) (7) (11025) (225) (-150) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource166 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-1225) (9) (11025) ((1225/9)) ((-350/3)) ((0,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource167 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-735) (15) (11025) (49) (-70) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource168 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-525) (21) (11025) (25) (-50) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource169 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-441) (25) (11025) ((441/25)) (-42) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource170 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-315) (35) (11025) (9) (-30) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource171 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-245) (45) (11025) ((49/9)) ((-70/3)) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource172 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-225) (49) (11025) ((225/49)) ((-150/7)) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource173 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-175) (63) (11025) ((25/9)) ((-50/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource174 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-147) (75) (11025) ((49/25)) (-14) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource175 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-105) (105) (11025) (1) (-10) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource176 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-75) (147) (11025) ((25/49)) ((-50/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource177 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-63) (175) (11025) ((9/25)) (-6) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource178 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-49) (225) (11025) ((49/225)) ((-14/3)) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource179 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-45) (245) (11025) ((9/49)) ((-30/7)) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource180 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-35) (315) (11025) ((1/9)) ((-10/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource181 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-25) (441) (11025) ((25/441)) ((-50/21)) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource182 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-21) (525) (11025) ((1/25)) (-2) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource183 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-15) (735) (11025) ((1/49)) ((-10/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource184 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-9) (1225) (11025) ((9/1225)) ((-6/7)) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource185 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-7) (1575) (11025) ((1/225)) ((-2/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource186 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-5) (2205) (11025) ((1/441)) ((-10/21)) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource187 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-3) (3675) (11025) ((1/1225)) ((-2/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource188 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (-1) (11025) (11025) ((1/11025)) ((-2/21)) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource189 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (1) (-11025) (11025) ((1/11025)) ((2/21)) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource190 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (3) (-3675) (11025) ((1/1225)) ((2/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource191 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (5) (-2205) (11025) ((1/441)) ((10/21)) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource192 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (7) (-1575) (11025) ((1/225)) ((2/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource193 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (9) (-1225) (11025) ((9/1225)) ((6/7)) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource194 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (15) (-735) (11025) ((1/49)) ((10/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource195 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (21) (-525) (11025) ((1/25)) (2) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource196 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (25) (-441) (11025) ((25/441)) ((50/21)) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource197 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (35) (-315) (11025) ((1/9)) ((10/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource198 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (45) (-245) (11025) ((9/49)) ((30/7)) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource199 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (49) (-225) (11025) ((49/225)) ((14/3)) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource200 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (63) (-175) (11025) ((9/25)) (6) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource201 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (75) (-147) (11025) ((25/49)) ((50/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource202 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (105) (-105) (11025) (1) (10) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource203 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (147) (-75) (11025) ((49/25)) (14) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource204 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (175) (-63) (11025) ((25/9)) ((50/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource205 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (225) (-49) (11025) ((225/49)) ((150/7)) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource206 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (245) (-45) (11025) ((49/9)) ((70/3)) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource207 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (315) (-35) (11025) (9) (30) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource208 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (441) (-25) (11025) ((441/25)) (42) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource209 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (525) (-21) (11025) (25) (50) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource210 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (735) (-15) (11025) (49) (70) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource211 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (1225) (-9) (11025) ((1225/9)) ((350/3)) ((0,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource212 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (1575) (-7) (11025) (225) (150) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource213 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (2205) (-5) (11025) (441) (210) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource214 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (3675) (-3) (11025) (1225) (350) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource215 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (2) (11025) (-1) (11025) (11025) (1050) ((0,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource216 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-4900) (1) (4900) (4900) (-1050) ((2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource217 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-2450) (2) (4900) (1225) (-525) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource218 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-1225) (4) (4900) ((1225/4)) ((-525/2)) ((-2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource219 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-980) (5) (4900) (196) (-210) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource220 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-700) (7) (4900) (100) (-150) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource221 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-490) (10) (4900) (49) (-105) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource222 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-350) (14) (4900) (25) (-75) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource223 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-245) (20) (4900) ((49/4)) ((-105/2)) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource224 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-196) (25) (4900) ((196/25)) (-42) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource225 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-175) (28) (4900) ((25/4)) ((-75/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource226 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-140) (35) (4900) (4) (-30) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource227 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-100) (49) (4900) ((100/49)) ((-150/7)) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource228 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-98) (50) (4900) ((49/25)) (-21) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource229 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-70) (70) (4900) (1) (-15) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource230 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-50) (98) (4900) ((25/49)) ((-75/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource231 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-49) (100) (4900) ((49/100)) ((-21/2)) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource232 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-35) (140) (4900) ((1/4)) ((-15/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource233 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-28) (175) (4900) ((4/25)) (-6) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource234 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-25) (196) (4900) ((25/196)) ((-75/14)) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource235 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-20) (245) (4900) ((4/49)) ((-30/7)) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource236 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-14) (350) (4900) ((1/25)) (-3) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource237 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-10) (490) (4900) ((1/49)) ((-15/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource238 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-7) (700) (4900) ((1/100)) ((-3/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource239 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-5) (980) (4900) ((1/196)) ((-15/14)) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource240 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-4) (1225) (4900) ((4/1225)) ((-6/7)) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource241 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-2) (2450) (4900) ((1/1225)) ((-3/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource242 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (-1) (4900) (4900) ((1/4900)) ((-3/14)) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource243 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (1) (-4900) (4900) ((1/4900)) ((3/14)) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource244 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (2) (-2450) (4900) ((1/1225)) ((3/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource245 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (4) (-1225) (4900) ((4/1225)) ((6/7)) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource246 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (5) (-980) (4900) ((1/196)) ((15/14)) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource247 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (7) (-700) (4900) ((1/100)) ((3/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource248 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (10) (-490) (4900) ((1/49)) ((15/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource249 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (14) (-350) (4900) ((1/25)) (3) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource250 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (20) (-245) (4900) ((4/49)) ((30/7)) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource251 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (25) (-196) (4900) ((25/196)) ((75/14)) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource252 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (28) (-175) (4900) ((4/25)) (6) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource253 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (35) (-140) (4900) ((1/4)) ((15/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource254 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (49) (-100) (4900) ((49/100)) ((21/2)) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource255 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (50) (-98) (4900) ((25/49)) ((75/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource256 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (70) (-70) (4900) (1) (15) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource257 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (98) (-50) (4900) ((49/25)) (21) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource258 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (100) (-49) (4900) ((100/49)) ((150/7)) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource259 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (140) (-35) (4900) (4) (30) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource260 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (175) (-28) (4900) ((25/4)) ((75/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource261 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (196) (-25) (4900) ((196/25)) (42) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource262 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (245) (-20) (4900) ((49/4)) ((105/2)) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource263 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (350) (-14) (4900) (25) (75) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource264 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (490) (-10) (4900) (49) (105) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource265 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (700) (-7) (4900) (100) (150) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource266 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (980) (-5) (4900) (196) (210) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource267 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (1225) (-4) (4900) ((1225/4)) ((525/2)) ((-2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource268 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (2450) (-2) (4900) (1225) (525) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource269 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (3) (4900) (-1) (4900) (4900) (1050) ((2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource270 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-44100) (1) (44100) (44100) (-1050) ((2,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource271 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-22050) (2) (44100) (11025) (-525) ((0,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource272 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-14700) (3) (44100) (4900) (-350) ((2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource273 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-11025) (4) (44100) ((11025/4)) ((-525/2)) ((-2,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource274 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-8820) (5) (44100) (1764) (-210) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource275 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-7350) (6) (44100) (1225) (-175) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource276 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-6300) (7) (44100) (900) (-150) ((2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource277 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-4900) (9) (44100) ((4900/9)) ((-350/3)) ((2,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource278 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-4410) (10) (44100) (441) (-105) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource279 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-3675) (12) (44100) ((1225/4)) ((-175/2)) ((-2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource280 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-3150) (14) (44100) (225) (-75) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource281 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-2940) (15) (44100) (196) (-70) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource282 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-2450) (18) (44100) ((1225/9)) ((-175/3)) ((0,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource283 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-2205) (20) (44100) ((441/4)) ((-105/2)) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource284 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-2100) (21) (44100) (100) (-50) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource285 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-1764) (25) (44100) ((1764/25)) (-42) ((2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource286 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-1575) (28) (44100) ((225/4)) ((-75/2)) ((-2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource287 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-1470) (30) (44100) (49) (-35) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource288 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-1260) (35) (44100) (36) (-30) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource289 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-1225) (36) (44100) ((1225/36)) ((-175/6)) ((-2,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource290 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-1050) (42) (44100) (25) (-25) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource291 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-980) (45) (44100) ((196/9)) ((-70/3)) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource292 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-900) (49) (44100) ((900/49)) ((-150/7)) ((2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource293 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-882) (50) (44100) ((441/25)) (-21) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource294 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-735) (60) (44100) ((49/4)) ((-35/2)) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource295 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-700) (63) (44100) ((100/9)) ((-50/3)) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource296 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-630) (70) (44100) (9) (-15) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource297 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-588) (75) (44100) ((196/25)) (-14) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource298 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-525) (84) (44100) ((25/4)) ((-25/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource299 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-490) (90) (44100) ((49/9)) ((-35/3)) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource300 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-450) (98) (44100) ((225/49)) ((-75/7)) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource301 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-441) (100) (44100) ((441/100)) ((-21/2)) ((-2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource302 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-420) (105) (44100) (4) (-10) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource303 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-350) (126) (44100) ((25/9)) ((-25/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource304 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-315) (140) (44100) ((9/4)) ((-15/2)) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource305 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-300) (147) (44100) ((100/49)) ((-50/7)) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource306 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-294) (150) (44100) ((49/25)) (-7) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource307 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-252) (175) (44100) ((36/25)) (-6) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource308 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-245) (180) (44100) ((49/36)) ((-35/6)) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource309 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-225) (196) (44100) ((225/196)) ((-75/14)) ((-2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource310 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-210) (210) (44100) (1) (-5) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource311 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-196) (225) (44100) ((196/225)) ((-14/3)) ((2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource312 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-180) (245) (44100) ((36/49)) ((-30/7)) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource313 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-175) (252) (44100) ((25/36)) ((-25/6)) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource314 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-150) (294) (44100) ((25/49)) ((-25/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource315 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-147) (300) (44100) ((49/100)) ((-7/2)) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource316 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-140) (315) (44100) ((4/9)) ((-10/3)) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource317 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-126) (350) (44100) ((9/25)) (-3) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource318 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-105) (420) (44100) ((1/4)) ((-5/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource319 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-100) (441) (44100) ((100/441)) ((-50/21)) ((2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource320 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-98) (450) (44100) ((49/225)) ((-7/3)) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource321 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-90) (490) (44100) ((9/49)) ((-15/7)) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource322 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-84) (525) (44100) ((4/25)) (-2) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource323 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-75) (588) (44100) ((25/196)) ((-25/14)) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource324 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-70) (630) (44100) ((1/9)) ((-5/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource325 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-63) (700) (44100) ((9/100)) ((-3/2)) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource326 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-60) (735) (44100) ((4/49)) ((-10/7)) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource327 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-50) (882) (44100) ((25/441)) ((-25/21)) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource328 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-49) (900) (44100) ((49/900)) ((-7/6)) ((-2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource329 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-45) (980) (44100) ((9/196)) ((-15/14)) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource330 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-42) (1050) (44100) ((1/25)) (-1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource331 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-36) (1225) (44100) ((36/1225)) ((-6/7)) ((2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource332 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-35) (1260) (44100) ((1/36)) ((-5/6)) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource333 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-30) (1470) (44100) ((1/49)) ((-5/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource334 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-28) (1575) (44100) ((4/225)) ((-2/3)) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource335 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-25) (1764) (44100) ((25/1764)) ((-25/42)) ((-2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource336 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-21) (2100) (44100) ((1/100)) ((-1/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource337 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-20) (2205) (44100) ((4/441)) ((-10/21)) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource338 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-18) (2450) (44100) ((9/1225)) ((-3/7)) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource339 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-15) (2940) (44100) ((1/196)) ((-5/14)) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource340 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-14) (3150) (44100) ((1/225)) ((-1/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource341 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-12) (3675) (44100) ((4/1225)) ((-2/7)) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource342 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-10) (4410) (44100) ((1/441)) ((-5/21)) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource343 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-9) (4900) (44100) ((9/4900)) ((-3/14)) ((-2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource344 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-7) (6300) (44100) ((1/900)) ((-1/6)) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource345 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-6) (7350) (44100) ((1/1225)) ((-1/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource346 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-5) (8820) (44100) ((1/1764)) ((-5/42)) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource347 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-4) (11025) (44100) ((4/11025)) ((-2/21)) ((2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource348 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-3) (14700) (44100) ((1/4900)) ((-1/14)) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource349 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-2) (22050) (44100) ((1/11025)) ((-1/21)) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource350 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (-1) (44100) (44100) ((1/44100)) ((-1/42)) ((-2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource351 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (1) (-44100) (44100) ((1/44100)) ((1/42)) ((-2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource352 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (2) (-22050) (44100) ((1/11025)) ((1/21)) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource353 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (3) (-14700) (44100) ((1/4900)) ((1/14)) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource354 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (4) (-11025) (44100) ((4/11025)) ((2/21)) ((2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource355 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (5) (-8820) (44100) ((1/1764)) ((5/42)) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource356 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (6) (-7350) (44100) ((1/1225)) ((1/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource357 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (7) (-6300) (44100) ((1/900)) ((1/6)) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource358 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (9) (-4900) (44100) ((9/4900)) ((3/14)) ((-2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource359 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (10) (-4410) (44100) ((1/441)) ((5/21)) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource360 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (12) (-3675) (44100) ((4/1225)) ((2/7)) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource361 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (14) (-3150) (44100) ((1/225)) ((1/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource362 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (15) (-2940) (44100) ((1/196)) ((5/14)) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource363 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (18) (-2450) (44100) ((9/1225)) ((3/7)) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource364 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (20) (-2205) (44100) ((4/441)) ((10/21)) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource365 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (21) (-2100) (44100) ((1/100)) ((1/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource366 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (25) (-1764) (44100) ((25/1764)) ((25/42)) ((-2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource367 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (28) (-1575) (44100) ((4/225)) ((2/3)) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource368 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (30) (-1470) (44100) ((1/49)) ((5/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource369 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (35) (-1260) (44100) ((1/36)) ((5/6)) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource370 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (36) (-1225) (44100) ((36/1225)) ((6/7)) ((2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource371 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (42) (-1050) (44100) ((1/25)) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource372 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (45) (-980) (44100) ((9/196)) ((15/14)) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource373 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (49) (-900) (44100) ((49/900)) ((7/6)) ((-2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource374 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (50) (-882) (44100) ((25/441)) ((25/21)) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource375 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (60) (-735) (44100) ((4/49)) ((10/7)) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource376 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (63) (-700) (44100) ((9/100)) ((3/2)) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource377 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (70) (-630) (44100) ((1/9)) ((5/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource378 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (75) (-588) (44100) ((25/196)) ((25/14)) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource379 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (84) (-525) (44100) ((4/25)) (2) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource380 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (90) (-490) (44100) ((9/49)) ((15/7)) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource381 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (98) (-450) (44100) ((49/225)) ((7/3)) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource382 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (100) (-441) (44100) ((100/441)) ((50/21)) ((2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource383 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (105) (-420) (44100) ((1/4)) ((5/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource384 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (126) (-350) (44100) ((9/25)) (3) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource385 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (140) (-315) (44100) ((4/9)) ((10/3)) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource386 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (147) (-300) (44100) ((49/100)) ((7/2)) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource387 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (150) (-294) (44100) ((25/49)) ((25/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource388 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (175) (-252) (44100) ((25/36)) ((25/6)) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource389 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (180) (-245) (44100) ((36/49)) ((30/7)) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource390 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (196) (-225) (44100) ((196/225)) ((14/3)) ((2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource391 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (210) (-210) (44100) (1) (5) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource392 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (225) (-196) (44100) ((225/196)) ((75/14)) ((-2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource393 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (245) (-180) (44100) ((49/36)) ((35/6)) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource394 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (252) (-175) (44100) ((36/25)) (6) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource395 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (294) (-150) (44100) ((49/25)) (7) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource396 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (300) (-147) (44100) ((100/49)) ((50/7)) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource397 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (315) (-140) (44100) ((9/4)) ((15/2)) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource398 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (350) (-126) (44100) ((25/9)) ((25/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource399 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (420) (-105) (44100) (4) (10) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource400 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (441) (-100) (44100) ((441/100)) ((21/2)) ((-2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource401 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (450) (-98) (44100) ((225/49)) ((75/7)) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource402 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (490) (-90) (44100) ((49/9)) ((35/3)) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource403 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (525) (-84) (44100) ((25/4)) ((25/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource404 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (588) (-75) (44100) ((196/25)) (14) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource405 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (630) (-70) (44100) (9) (15) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource406 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (700) (-63) (44100) ((100/9)) ((50/3)) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource407 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (735) (-60) (44100) ((49/4)) ((35/2)) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource408 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (882) (-50) (44100) ((441/25)) (21) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource409 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (900) (-49) (44100) ((900/49)) ((150/7)) ((2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource410 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (980) (-45) (44100) ((196/9)) ((70/3)) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource411 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (1050) (-42) (44100) (25) (25) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource412 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (1225) (-36) (44100) ((1225/36)) ((175/6)) ((-2,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource413 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (1260) (-35) (44100) (36) (30) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource414 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (1470) (-30) (44100) (49) (35) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource415 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (1575) (-28) (44100) ((225/4)) ((75/2)) ((-2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource416 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (1764) (-25) (44100) ((1764/25)) (42) ((2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource417 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (2100) (-21) (44100) (100) (50) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource418 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (2205) (-20) (44100) ((441/4)) ((105/2)) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource419 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (2450) (-18) (44100) ((1225/9)) ((175/3)) ((0,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource420 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (2940) (-15) (44100) (196) (70) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource421 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (3150) (-14) (44100) (225) (75) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource422 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (3675) (-12) (44100) ((1225/4)) ((175/2)) ((-2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource423 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (4410) (-10) (44100) (441) (105) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource424 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (4900) (-9) (44100) ((4900/9)) ((350/3)) ((2,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource425 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (6300) (-7) (44100) (900) (150) ((2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource426 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (7350) (-6) (44100) (1225) (175) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource427 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (8820) (-5) (44100) (1764) (210) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource428 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (11025) (-4) (44100) ((11025/4)) ((525/2)) ((-2,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource429 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (14700) (-3) (44100) (4900) (350) ((2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource430 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (22050) (-2) (44100) (11025) (525) ((0,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource431 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (5) (44100) (-1) (44100) (44100) (1050) ((2,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource432 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (-1225) (1) (1225) (1225) (-1050) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource433 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (-245) (5) (1225) (49) (-210) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource434 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (-175) (7) (1225) (25) (-150) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource435 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (-49) (25) (1225) ((49/25)) (-42) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource436 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (-35) (35) (1225) (1) (-30) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource437 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (-25) (49) (1225) ((25/49)) ((-150/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource438 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (-7) (175) (1225) ((1/25)) (-6) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource439 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (-5) (245) (1225) ((1/49)) ((-30/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource440 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (-1) (1225) (1225) ((1/1225)) ((-6/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource441 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (1) (-1225) (1225) ((1/1225)) ((6/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource442 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (5) (-245) (1225) ((1/49)) ((30/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource443 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (7) (-175) (1225) ((1/25)) (6) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource444 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (25) (-49) (1225) ((25/49)) ((150/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource445 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (35) (-35) (1225) (1) (30) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource446 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (49) (-25) (1225) ((49/25)) (42) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource447 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (175) (-7) (1225) (25) (150) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource448 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (245) (-5) (1225) (49) (210) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource449 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (6) (1225) (-1) (1225) (1225) (1050) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource450 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-900) (1) (900) (900) (-1050) ((2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource451 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-450) (2) (900) (225) (-525) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource452 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-300) (3) (900) (100) (-350) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource453 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-225) (4) (900) ((225/4)) ((-525/2)) ((-2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource454 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-180) (5) (900) (36) (-210) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource455 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-150) (6) (900) (25) (-175) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource456 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-100) (9) (900) ((100/9)) ((-350/3)) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource457 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-90) (10) (900) (9) (-105) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource458 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-75) (12) (900) ((25/4)) ((-175/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource459 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-60) (15) (900) (4) (-70) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource460 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-50) (18) (900) ((25/9)) ((-175/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource461 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-45) (20) (900) ((9/4)) ((-105/2)) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource462 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-36) (25) (900) ((36/25)) (-42) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource463 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-30) (30) (900) (1) (-35) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource464 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-25) (36) (900) ((25/36)) ((-175/6)) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource465 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-20) (45) (900) ((4/9)) ((-70/3)) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource466 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-18) (50) (900) ((9/25)) (-21) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource467 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-15) (60) (900) ((1/4)) ((-35/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource468 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-12) (75) (900) ((4/25)) (-14) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource469 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-10) (90) (900) ((1/9)) ((-35/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource470 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-9) (100) (900) ((9/100)) ((-21/2)) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource471 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-6) (150) (900) ((1/25)) (-7) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource472 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-5) (180) (900) ((1/36)) ((-35/6)) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource473 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-4) (225) (900) ((4/225)) ((-14/3)) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource474 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-3) (300) (900) ((1/100)) ((-7/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource475 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-2) (450) (900) ((1/225)) ((-7/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource476 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (-1) (900) (900) ((1/900)) ((-7/6)) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource477 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (1) (-900) (900) ((1/900)) ((7/6)) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource478 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (2) (-450) (900) ((1/225)) ((7/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource479 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (3) (-300) (900) ((1/100)) ((7/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource480 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (4) (-225) (900) ((4/225)) ((14/3)) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource481 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (5) (-180) (900) ((1/36)) ((35/6)) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource482 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (6) (-150) (900) ((1/25)) (7) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource483 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (9) (-100) (900) ((9/100)) ((21/2)) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource484 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (10) (-90) (900) ((1/9)) ((35/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource485 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (12) (-75) (900) ((4/25)) (14) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource486 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (15) (-60) (900) ((1/4)) ((35/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource487 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (18) (-50) (900) ((9/25)) (21) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource488 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (20) (-45) (900) ((4/9)) ((70/3)) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource489 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (25) (-36) (900) ((25/36)) ((175/6)) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource490 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (30) (-30) (900) (1) (35) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource491 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (36) (-25) (900) ((36/25)) (42) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource492 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (45) (-20) (900) ((9/4)) ((105/2)) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource493 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (50) (-18) (900) ((25/9)) ((175/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource494 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (60) (-15) (900) (4) (70) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource495 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (75) (-12) (900) ((25/4)) ((175/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource496 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (90) (-10) (900) (9) (105) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource497 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (100) (-9) (900) ((100/9)) ((350/3)) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource498 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (150) (-6) (900) (25) (175) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource499 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (180) (-5) (900) (36) (210) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource500 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (225) (-4) (900) ((225/4)) ((525/2)) ((-2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource501 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (300) (-3) (900) (100) (350) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource502 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (450) (-2) (900) (225) (525) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource503 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (7) (900) (-1) (900) (900) (1050) ((2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource504 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-11025) (1) (11025) (11025) (-1050) ((0,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource505 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-3675) (3) (11025) (1225) (-350) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource506 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-2205) (5) (11025) (441) (-210) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource507 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-1575) (7) (11025) (225) (-150) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource508 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-1225) (9) (11025) ((1225/9)) ((-350/3)) ((0,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource509 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-735) (15) (11025) (49) (-70) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource510 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-525) (21) (11025) (25) (-50) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource511 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-441) (25) (11025) ((441/25)) (-42) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource512 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-315) (35) (11025) (9) (-30) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource513 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-245) (45) (11025) ((49/9)) ((-70/3)) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource514 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-225) (49) (11025) ((225/49)) ((-150/7)) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource515 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-175) (63) (11025) ((25/9)) ((-50/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource516 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-147) (75) (11025) ((49/25)) (-14) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource517 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-105) (105) (11025) (1) (-10) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource518 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-75) (147) (11025) ((25/49)) ((-50/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource519 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-63) (175) (11025) ((9/25)) (-6) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource520 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-49) (225) (11025) ((49/225)) ((-14/3)) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource521 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-45) (245) (11025) ((9/49)) ((-30/7)) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource522 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-35) (315) (11025) ((1/9)) ((-10/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource523 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-25) (441) (11025) ((25/441)) ((-50/21)) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource524 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-21) (525) (11025) ((1/25)) (-2) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource525 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-15) (735) (11025) ((1/49)) ((-10/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource526 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-9) (1225) (11025) ((9/1225)) ((-6/7)) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource527 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-7) (1575) (11025) ((1/225)) ((-2/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource528 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-5) (2205) (11025) ((1/441)) ((-10/21)) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource529 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-3) (3675) (11025) ((1/1225)) ((-2/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource530 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (-1) (11025) (11025) ((1/11025)) ((-2/21)) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource531 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (1) (-11025) (11025) ((1/11025)) ((2/21)) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource532 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (3) (-3675) (11025) ((1/1225)) ((2/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource533 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (5) (-2205) (11025) ((1/441)) ((10/21)) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource534 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (7) (-1575) (11025) ((1/225)) ((2/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource535 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (9) (-1225) (11025) ((9/1225)) ((6/7)) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource536 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (15) (-735) (11025) ((1/49)) ((10/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource537 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (21) (-525) (11025) ((1/25)) (2) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource538 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (25) (-441) (11025) ((25/441)) ((50/21)) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource539 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (35) (-315) (11025) ((1/9)) ((10/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource540 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (45) (-245) (11025) ((9/49)) ((30/7)) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource541 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (49) (-225) (11025) ((49/225)) ((14/3)) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource542 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (63) (-175) (11025) ((9/25)) (6) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource543 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (75) (-147) (11025) ((25/49)) ((50/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource544 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (105) (-105) (11025) (1) (10) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource545 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (147) (-75) (11025) ((49/25)) (14) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource546 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (175) (-63) (11025) ((25/9)) ((50/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource547 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (225) (-49) (11025) ((225/49)) ((150/7)) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource548 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (245) (-45) (11025) ((49/9)) ((70/3)) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource549 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (315) (-35) (11025) (9) (30) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource550 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (441) (-25) (11025) ((441/25)) (42) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource551 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (525) (-21) (11025) (25) (50) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource552 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (735) (-15) (11025) (49) (70) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource553 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (1225) (-9) (11025) ((1225/9)) ((350/3)) ((0,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource554 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (1575) (-7) (11025) (225) (150) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource555 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (2205) (-5) (11025) (441) (210) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource556 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (3675) (-3) (11025) (1225) (350) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource557 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (10) (11025) (-1) (11025) (11025) (1050) ((0,2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource558 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (-225) (1) (225) (225) (-1050) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource559 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (-75) (3) (225) (25) (-350) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource560 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (-45) (5) (225) (9) (-210) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource561 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (-25) (9) (225) ((25/9)) ((-350/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource562 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (-15) (15) (225) (1) (-70) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource563 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (-9) (25) (225) ((9/25)) (-42) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource564 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (-5) (45) (225) ((1/9)) ((-70/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource565 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (-3) (75) (225) ((1/25)) (-14) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource566 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (-1) (225) (225) ((1/225)) ((-14/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource567 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (1) (-225) (225) ((1/225)) ((14/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource568 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (3) (-75) (225) ((1/25)) (14) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource569 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (5) (-45) (225) ((1/9)) ((70/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource570 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (9) (-25) (225) ((9/25)) (42) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource571 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (15) (-15) (225) (1) (70) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource572 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (25) (-9) (225) ((25/9)) ((350/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource573 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (45) (-5) (225) (9) (210) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource574 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (75) (-3) (225) (25) (350) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource575 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (14) (225) (-1) (225) (225) (1050) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource576 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-4900) (1) (4900) (4900) (-1050) ((2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource577 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-2450) (2) (4900) (1225) (-525) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource578 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-1225) (4) (4900) ((1225/4)) ((-525/2)) ((-2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource579 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-980) (5) (4900) (196) (-210) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource580 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-700) (7) (4900) (100) (-150) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource581 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-490) (10) (4900) (49) (-105) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource582 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-350) (14) (4900) (25) (-75) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource583 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-245) (20) (4900) ((49/4)) ((-105/2)) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource584 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-196) (25) (4900) ((196/25)) (-42) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource585 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-175) (28) (4900) ((25/4)) ((-75/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource586 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-140) (35) (4900) (4) (-30) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource587 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-100) (49) (4900) ((100/49)) ((-150/7)) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource588 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-98) (50) (4900) ((49/25)) (-21) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource589 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-70) (70) (4900) (1) (-15) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource590 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-50) (98) (4900) ((25/49)) ((-75/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource591 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-49) (100) (4900) ((49/100)) ((-21/2)) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource592 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-35) (140) (4900) ((1/4)) ((-15/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource593 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-28) (175) (4900) ((4/25)) (-6) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource594 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-25) (196) (4900) ((25/196)) ((-75/14)) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource595 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-20) (245) (4900) ((4/49)) ((-30/7)) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource596 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-14) (350) (4900) ((1/25)) (-3) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource597 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-10) (490) (4900) ((1/49)) ((-15/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource598 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-7) (700) (4900) ((1/100)) ((-3/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource599 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-5) (980) (4900) ((1/196)) ((-15/14)) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource600 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-4) (1225) (4900) ((4/1225)) ((-6/7)) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource601 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-2) (2450) (4900) ((1/1225)) ((-3/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource602 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (-1) (4900) (4900) ((1/4900)) ((-3/14)) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource603 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (1) (-4900) (4900) ((1/4900)) ((3/14)) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource604 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (2) (-2450) (4900) ((1/1225)) ((3/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource605 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (4) (-1225) (4900) ((4/1225)) ((6/7)) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource606 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (5) (-980) (4900) ((1/196)) ((15/14)) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource607 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (7) (-700) (4900) ((1/100)) ((3/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource608 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (10) (-490) (4900) ((1/49)) ((15/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource609 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (14) (-350) (4900) ((1/25)) (3) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource610 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (20) (-245) (4900) ((4/49)) ((30/7)) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource611 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (25) (-196) (4900) ((25/196)) ((75/14)) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource612 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (28) (-175) (4900) ((4/25)) (6) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource613 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (35) (-140) (4900) ((1/4)) ((15/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource614 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (49) (-100) (4900) ((49/100)) ((21/2)) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource615 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (50) (-98) (4900) ((25/49)) ((75/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource616 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (70) (-70) (4900) (1) (15) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource617 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (98) (-50) (4900) ((49/25)) (21) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource618 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (100) (-49) (4900) ((100/49)) ((150/7)) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource619 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (140) (-35) (4900) (4) (30) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource620 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (175) (-28) (4900) ((25/4)) ((75/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource621 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (196) (-25) (4900) ((196/25)) (42) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource622 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (245) (-20) (4900) ((49/4)) ((105/2)) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource623 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (350) (-14) (4900) (25) (75) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource624 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (490) (-10) (4900) (49) (105) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource625 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (700) (-7) (4900) (100) (150) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource626 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (980) (-5) (4900) (196) (210) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource627 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (1225) (-4) (4900) ((1225/4)) ((525/2)) ((-2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource628 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (2450) (-2) (4900) (1225) (525) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource629 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (15) (4900) (-1) (4900) (4900) (1050) ((2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource630 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (-100) (1) (100) (100) (-1050) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource631 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (-50) (2) (100) (25) (-525) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource632 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (-25) (4) (100) ((25/4)) ((-525/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource633 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (-20) (5) (100) (4) (-210) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource634 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (-10) (10) (100) (1) (-105) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource635 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (-5) (20) (100) ((1/4)) ((-105/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource636 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (-4) (25) (100) ((4/25)) (-42) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource637 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (-2) (50) (100) ((1/25)) (-21) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource638 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (-1) (100) (100) ((1/100)) ((-21/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource639 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (1) (-100) (100) ((1/100)) ((21/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource640 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (2) (-50) (100) ((1/25)) (21) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource641 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (4) (-25) (100) ((4/25)) (42) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource642 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (5) (-20) (100) ((1/4)) ((105/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource643 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (10) (-10) (100) (1) (105) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource644 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (20) (-5) (100) (4) (210) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource645 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (25) (-4) (100) ((25/4)) ((525/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource646 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (50) (-2) (100) (25) (525) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource647 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (21) (100) (-1) (100) (100) (1050) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource648 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-1764) (1) (1764) (1764) (-1050) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource649 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-882) (2) (1764) (441) (-525) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource650 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-588) (3) (1764) (196) (-350) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource651 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-441) (4) (1764) ((441/4)) ((-525/2)) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource652 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-294) (6) (1764) (49) (-175) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource653 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-252) (7) (1764) (36) (-150) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource654 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-196) (9) (1764) ((196/9)) ((-350/3)) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource655 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-147) (12) (1764) ((49/4)) ((-175/2)) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource656 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-126) (14) (1764) (9) (-75) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource657 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-98) (18) (1764) ((49/9)) ((-175/3)) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource658 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-84) (21) (1764) (4) (-50) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource659 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-63) (28) (1764) ((9/4)) ((-75/2)) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource660 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-49) (36) (1764) ((49/36)) ((-175/6)) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource661 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-42) (42) (1764) (1) (-25) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource662 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-36) (49) (1764) ((36/49)) ((-150/7)) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource663 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-28) (63) (1764) ((4/9)) ((-50/3)) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource664 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-21) (84) (1764) ((1/4)) ((-25/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource665 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-18) (98) (1764) ((9/49)) ((-75/7)) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource666 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-14) (126) (1764) ((1/9)) ((-25/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource667 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-12) (147) (1764) ((4/49)) ((-50/7)) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource668 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-9) (196) (1764) ((9/196)) ((-75/14)) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource669 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-7) (252) (1764) ((1/36)) ((-25/6)) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource670 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-6) (294) (1764) ((1/49)) ((-25/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource671 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-4) (441) (1764) ((4/441)) ((-50/21)) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource672 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-3) (588) (1764) ((1/196)) ((-25/14)) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource673 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-2) (882) (1764) ((1/441)) ((-25/21)) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource674 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (-1) (1764) (1764) ((1/1764)) ((-25/42)) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource675 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (1) (-1764) (1764) ((1/1764)) ((25/42)) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource676 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (2) (-882) (1764) ((1/441)) ((25/21)) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource677 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (3) (-588) (1764) ((1/196)) ((25/14)) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource678 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (4) (-441) (1764) ((4/441)) ((50/21)) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource679 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (6) (-294) (1764) ((1/49)) ((25/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource680 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (7) (-252) (1764) ((1/36)) ((25/6)) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource681 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (9) (-196) (1764) ((9/196)) ((75/14)) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource682 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (12) (-147) (1764) ((4/49)) ((50/7)) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource683 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (14) (-126) (1764) ((1/9)) ((25/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource684 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (18) (-98) (1764) ((9/49)) ((75/7)) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource685 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (21) (-84) (1764) ((1/4)) ((25/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource686 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (28) (-63) (1764) ((4/9)) ((50/3)) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource687 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (36) (-49) (1764) ((36/49)) ((150/7)) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource688 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (42) (-42) (1764) (1) (25) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource689 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (49) (-36) (1764) ((49/36)) ((175/6)) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource690 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (63) (-28) (1764) ((9/4)) ((75/2)) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource691 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (84) (-21) (1764) (4) (50) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource692 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (98) (-18) (1764) ((49/9)) ((175/3)) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource693 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (126) (-14) (1764) (9) (75) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource694 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (147) (-12) (1764) ((49/4)) ((175/2)) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource695 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (196) (-9) (1764) ((196/9)) ((350/3)) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource696 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (252) (-7) (1764) (36) (150) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource697 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (294) (-6) (1764) (49) (175) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource698 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (441) (-4) (1764) ((441/4)) ((525/2)) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource699 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (588) (-3) (1764) (196) (350) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource700 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (882) (-2) (1764) (441) (525) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource701 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (25) (1764) (-1) (1764) (1764) (1050) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource702 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (-1225) (1) (1225) (1225) (-1050) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource703 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (-245) (5) (1225) (49) (-210) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource704 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (-175) (7) (1225) (25) (-150) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource705 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (-49) (25) (1225) ((49/25)) (-42) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource706 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (-35) (35) (1225) (1) (-30) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource707 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (-25) (49) (1225) ((25/49)) ((-150/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource708 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (-7) (175) (1225) ((1/25)) (-6) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource709 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (-5) (245) (1225) ((1/49)) ((-30/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource710 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (-1) (1225) (1225) ((1/1225)) ((-6/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource711 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (1) (-1225) (1225) ((1/1225)) ((6/7)) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource712 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (5) (-245) (1225) ((1/49)) ((30/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource713 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (7) (-175) (1225) ((1/25)) (6) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource714 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (25) (-49) (1225) ((25/49)) ((150/7)) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource715 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (35) (-35) (1225) (1) (30) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource716 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (49) (-25) (1225) ((49/25)) (42) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource717 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (175) (-7) (1225) (25) (150) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource718 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (245) (-5) (1225) (49) (210) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource719 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (30) (1225) (-1) (1225) (1225) (1050) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource720 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-900) (1) (900) (900) (-1050) ((2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource721 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-450) (2) (900) (225) (-525) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource722 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-300) (3) (900) (100) (-350) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource723 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-225) (4) (900) ((225/4)) ((-525/2)) ((-2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource724 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-180) (5) (900) (36) (-210) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource725 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-150) (6) (900) (25) (-175) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource726 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-100) (9) (900) ((100/9)) ((-350/3)) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource727 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-90) (10) (900) (9) (-105) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource728 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-75) (12) (900) ((25/4)) ((-175/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource729 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-60) (15) (900) (4) (-70) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource730 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-50) (18) (900) ((25/9)) ((-175/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource731 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-45) (20) (900) ((9/4)) ((-105/2)) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource732 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-36) (25) (900) ((36/25)) (-42) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource733 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-30) (30) (900) (1) (-35) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource734 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-25) (36) (900) ((25/36)) ((-175/6)) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource735 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-20) (45) (900) ((4/9)) ((-70/3)) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource736 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-18) (50) (900) ((9/25)) (-21) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource737 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-15) (60) (900) ((1/4)) ((-35/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource738 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-12) (75) (900) ((4/25)) (-14) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource739 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-10) (90) (900) ((1/9)) ((-35/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource740 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-9) (100) (900) ((9/100)) ((-21/2)) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource741 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-6) (150) (900) ((1/25)) (-7) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource742 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-5) (180) (900) ((1/36)) ((-35/6)) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource743 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-4) (225) (900) ((4/225)) ((-14/3)) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource744 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-3) (300) (900) ((1/100)) ((-7/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource745 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-2) (450) (900) ((1/225)) ((-7/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource746 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (-1) (900) (900) ((1/900)) ((-7/6)) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource747 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (1) (-900) (900) ((1/900)) ((7/6)) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource748 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (2) (-450) (900) ((1/225)) ((7/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource749 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (3) (-300) (900) ((1/100)) ((7/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource750 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (4) (-225) (900) ((4/225)) ((14/3)) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource751 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (5) (-180) (900) ((1/36)) ((35/6)) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource752 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (6) (-150) (900) ((1/25)) (7) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource753 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (9) (-100) (900) ((9/100)) ((21/2)) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource754 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (10) (-90) (900) ((1/9)) ((35/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource755 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (12) (-75) (900) ((4/25)) (14) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource756 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (15) (-60) (900) ((1/4)) ((35/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource757 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (18) (-50) (900) ((9/25)) (21) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource758 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (20) (-45) (900) ((4/9)) ((70/3)) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource759 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (25) (-36) (900) ((25/36)) ((175/6)) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource760 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (30) (-30) (900) (1) (35) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource761 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (36) (-25) (900) ((36/25)) (42) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource762 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (45) (-20) (900) ((9/4)) ((105/2)) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource763 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (50) (-18) (900) ((25/9)) ((175/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource764 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (60) (-15) (900) (4) (70) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource765 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (75) (-12) (900) ((25/4)) ((175/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource766 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (90) (-10) (900) (9) (105) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource767 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (100) (-9) (900) ((100/9)) ((350/3)) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource768 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (150) (-6) (900) (25) (175) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource769 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (180) (-5) (900) (36) (210) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource770 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (225) (-4) (900) ((225/4)) ((525/2)) ((-2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource771 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (300) (-3) (900) (100) (350) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource772 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (450) (-2) (900) (225) (525) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource773 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (35) (900) (-1) (900) (900) (1050) ((2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource774 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (42) (-25) (1) (25) (25) (-1050) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource775 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (42) (-5) (5) (25) (1) (-210) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource776 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (42) (-1) (25) (25) ((1/25)) (-42) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource777 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (42) (1) (-25) (25) ((1/25)) (42) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource778 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (42) (5) (-5) (25) (1) (210) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource779 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (42) (25) (-1) (25) (25) (1050) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource780 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (-441) (1) (441) (441) (-1050) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource781 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (-147) (3) (441) (49) (-350) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource782 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (-63) (7) (441) (9) (-150) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource783 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (-49) (9) (441) ((49/9)) ((-350/3)) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource784 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (-21) (21) (441) (1) (-50) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource785 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (-9) (49) (441) ((9/49)) ((-150/7)) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource786 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (-7) (63) (441) ((1/9)) ((-50/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource787 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (-3) (147) (441) ((1/49)) ((-50/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource788 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (-1) (441) (441) ((1/441)) ((-50/21)) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource789 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (1) (-441) (441) ((1/441)) ((50/21)) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource790 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (3) (-147) (441) ((1/49)) ((50/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource791 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (7) (-63) (441) ((1/9)) ((50/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource792 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (9) (-49) (441) ((9/49)) ((150/7)) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource793 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (21) (-21) (441) (1) (50) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource794 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (49) (-9) (441) ((49/9)) ((350/3)) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource795 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (63) (-7) (441) (9) (150) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource796 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (147) (-3) (441) (49) (350) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource797 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (50) (441) (-1) (441) (441) (1050) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource798 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (-225) (1) (225) (225) (-1050) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource799 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (-75) (3) (225) (25) (-350) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource800 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (-45) (5) (225) (9) (-210) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource801 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (-25) (9) (225) ((25/9)) ((-350/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource802 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (-15) (15) (225) (1) (-70) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource803 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (-9) (25) (225) ((9/25)) (-42) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource804 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (-5) (45) (225) ((1/9)) ((-70/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource805 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (-3) (75) (225) ((1/25)) (-14) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource806 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (-1) (225) (225) ((1/225)) ((-14/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource807 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (1) (-225) (225) ((1/225)) ((14/3)) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource808 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (3) (-75) (225) ((1/25)) (14) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource809 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (5) (-45) (225) ((1/9)) ((70/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource810 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (9) (-25) (225) ((9/25)) (42) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource811 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (15) (-15) (225) (1) (70) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource812 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (25) (-9) (225) ((25/9)) ((350/3)) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource813 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (45) (-5) (225) (9) (210) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource814 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (75) (-3) (225) (25) (350) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource815 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (70) (225) (-1) (225) (225) (1050) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource816 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (-196) (1) (196) (196) (-1050) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource817 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (-98) (2) (196) (49) (-525) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource818 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (-49) (4) (196) ((49/4)) ((-525/2)) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource819 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (-28) (7) (196) (4) (-150) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource820 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (-14) (14) (196) (1) (-75) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource821 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (-7) (28) (196) ((1/4)) ((-75/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource822 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (-4) (49) (196) ((4/49)) ((-150/7)) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource823 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (-2) (98) (196) ((1/49)) ((-75/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource824 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (-1) (196) (196) ((1/196)) ((-75/14)) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource825 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (1) (-196) (196) ((1/196)) ((75/14)) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource826 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (2) (-98) (196) ((1/49)) ((75/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource827 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (4) (-49) (196) ((4/49)) ((150/7)) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource828 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (7) (-28) (196) ((1/4)) ((75/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource829 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (14) (-14) (196) (1) (75) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource830 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (28) (-7) (196) (4) (150) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource831 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (49) (-4) (196) ((49/4)) ((525/2)) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource832 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (98) (-2) (196) (49) (525) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource833 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (75) (196) (-1) (196) (196) (1050) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource834 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (-100) (1) (100) (100) (-1050) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource835 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (-50) (2) (100) (25) (-525) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource836 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (-25) (4) (100) ((25/4)) ((-525/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource837 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (-20) (5) (100) (4) (-210) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource838 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (-10) (10) (100) (1) (-105) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource839 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (-5) (20) (100) ((1/4)) ((-105/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource840 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (-4) (25) (100) ((4/25)) (-42) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource841 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (-2) (50) (100) ((1/25)) (-21) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource842 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (-1) (100) (100) ((1/100)) ((-21/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource843 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (1) (-100) (100) ((1/100)) ((21/2)) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource844 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (2) (-50) (100) ((1/25)) (21) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource845 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (4) (-25) (100) ((4/25)) (42) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource846 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (5) (-20) (100) ((1/4)) ((105/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource847 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (10) (-10) (100) (1) (105) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource848 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (20) (-5) (100) (4) (210) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource849 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (25) (-4) (100) ((25/4)) ((525/2)) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource850 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (50) (-2) (100) (25) (525) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource851 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (105) (100) (-1) (100) (100) (1050) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource852 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (150) (-49) (1) (49) (49) (-1050) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource853 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (150) (-7) (7) (49) (1) (-150) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource854 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (150) (-1) (49) (49) ((1/49)) ((-150/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource855 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (150) (1) (-49) (49) ((1/49)) ((150/7)) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource856 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (150) (7) (-7) (49) (1) (150) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource857 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (150) (49) (-1) (49) (49) (1050) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource858 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (-36) (1) (36) (36) (-1050) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource859 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (-18) (2) (36) (9) (-525) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource860 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (-12) (3) (36) (4) (-350) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource861 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (-9) (4) (36) ((9/4)) ((-525/2)) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource862 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (-6) (6) (36) (1) (-175) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource863 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (-4) (9) (36) ((4/9)) ((-350/3)) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource864 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (-3) (12) (36) ((1/4)) ((-175/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource865 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (-2) (18) (36) ((1/9)) ((-175/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource866 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (-1) (36) (36) ((1/36)) ((-175/6)) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource867 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (1) (-36) (36) ((1/36)) ((175/6)) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource868 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (2) (-18) (36) ((1/9)) ((175/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource869 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (3) (-12) (36) ((1/4)) ((175/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource870 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (4) (-9) (36) ((4/9)) ((350/3)) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource871 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (6) (-6) (36) (1) (175) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource872 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (9) (-4) (36) ((9/4)) ((525/2)) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource873 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (12) (-3) (36) (4) (350) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource874 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (18) (-2) (36) (9) (525) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource875 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (175) (36) (-1) (36) (36) (1050) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource876 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (210) (-25) (1) (25) (25) (-1050) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource877 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (210) (-5) (5) (25) (1) (-210) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource878 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (210) (-1) (25) (25) ((1/25)) (-42) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource879 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (210) (1) (-25) (25) ((1/25)) (42) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource880 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (210) (5) (-5) (25) (1) (210) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource881 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (210) (25) (-1) (25) (25) (1050) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource882 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (350) (-9) (1) (9) (9) (-1050) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource883 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (350) (-3) (3) (9) (1) (-350) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource884 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (350) (-1) (9) (9) ((1/9)) ((-350/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource885 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (350) (1) (-9) (9) ((1/9)) ((350/3)) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource886 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (350) (3) (-3) (9) (1) (350) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource887 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (350) (9) (-1) (9) (9) (1050) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource888 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (525) (-4) (1) (4) (4) (-1050) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource889 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (525) (-2) (2) (4) (1) (-525) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource890 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (525) (-1) (4) (4) ((1/4)) ((-525/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource891 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (525) (1) (-4) (4) ((1/4)) ((525/2)) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource892 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (525) (2) (-2) (4) (1) (525) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource893 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (525) (4) (-1) (4) (4) (1050) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource894 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1050) (-1) (1) (1) (1) (-1050) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource895 : SourceRow := .physical (.taylor (TaylorCertificate.ofValues (1050) (1) (-1) (1) (1) (1050) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource896 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (0))

compact_certificate def auxSource897 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (1))

compact_certificate def auxSource898 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (2))

compact_certificate def auxSource899 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (3))

compact_certificate def auxSource900 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (4))

compact_certificate def auxSource901 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (5))

compact_certificate def auxSource902 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (6))

compact_certificate def auxSource903 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (7))

compact_certificate def auxSource904 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (8))

compact_certificate def auxSource905 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (9))

compact_certificate def auxSource906 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (10))

compact_certificate def auxSource907 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (11))

compact_certificate def auxSource908 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (12))

compact_certificate def auxSource909 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (13))

compact_certificate def auxSource910 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (14))

compact_certificate def auxSource911 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (15))

compact_certificate def auxSource912 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (16))

compact_certificate def auxSource913 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (17))

compact_certificate def auxSource914 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (18))

compact_certificate def auxSource915 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (19))

compact_certificate def auxSource916 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (20))

compact_certificate def auxSource917 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (21))

compact_certificate def auxSource918 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (22))

compact_certificate def auxSource919 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (23))

compact_certificate def auxSource920 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (24))

compact_certificate def auxSource921 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (25))

compact_certificate def auxSource922 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (26))

compact_certificate def auxSource923 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (27))

compact_certificate def auxSource924 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (28))

compact_certificate def auxSource925 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (29))

compact_certificate def auxSource926 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (30))

compact_certificate def auxSource927 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (31))

compact_certificate def auxSource928 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (32))

compact_certificate def auxSource929 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (33))

compact_certificate def auxSource930 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (34))

compact_certificate def auxSource931 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (35))

compact_certificate def auxSource932 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (36))

compact_certificate def auxSource933 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (37))

compact_certificate def auxSource934 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (38))

compact_certificate def auxSource935 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (39))

compact_certificate def auxSource936 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (40))

compact_certificate def auxSource937 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (41))

compact_certificate def auxSource938 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (42))

compact_certificate def auxSource939 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (43))

compact_certificate def auxSource940 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (44))

compact_certificate def auxSource941 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (45))

compact_certificate def auxSource942 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (46))

compact_certificate def auxSource943 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (47))

compact_certificate def auxSource944 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (48))

compact_certificate def auxSource945 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (49))

compact_certificate def auxSource946 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (50))

compact_certificate def auxSource947 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (51))

compact_certificate def auxSource948 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (52))

compact_certificate def auxSource949 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (53))

compact_certificate def auxSource950 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (54))

compact_certificate def auxSource951 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (55))

compact_certificate def auxSource952 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (56))

compact_certificate def auxSource953 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (57))

compact_certificate def auxSource954 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (58))

compact_certificate def auxSource955 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (59))

compact_certificate def auxSource956 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (60))

compact_certificate def auxSource957 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (61))

compact_certificate def auxSource958 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (62))

compact_certificate def auxSource959 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (63))

compact_certificate def auxSource960 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (64))

compact_certificate def auxSource961 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (65))

compact_certificate def auxSource962 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (66))

compact_certificate def auxSource963 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (67))

compact_certificate def auxSource964 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (68))

compact_certificate def auxSource965 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (69))

compact_certificate def auxSource966 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (70))

compact_certificate def auxSource967 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (71))

compact_certificate def auxSource968 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (72))

compact_certificate def auxSource969 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (73))

compact_certificate def auxSource970 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (74))

compact_certificate def auxSource971 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (75))

compact_certificate def auxSource972 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (76))

compact_certificate def auxSource973 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (77))

compact_certificate def auxSource974 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (78))

compact_certificate def auxSource975 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (79))

compact_certificate def auxSource976 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (80))

compact_certificate def auxSource977 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (81))

compact_certificate def auxSource978 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (82))

compact_certificate def auxSource979 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (83))

compact_certificate def auxSource980 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (84))

compact_certificate def auxSource981 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (85))

compact_certificate def auxSource982 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (86))

compact_certificate def auxSource983 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (87))

compact_certificate def auxSource984 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (88))

compact_certificate def auxSource985 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (89))

compact_certificate def auxSource986 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (90))

compact_certificate def auxSource987 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (91))

compact_certificate def auxSource988 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (92))

compact_certificate def auxSource989 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (93))

compact_certificate def auxSource990 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (94))

compact_certificate def auxSource991 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (95))

compact_certificate def auxSource992 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (96))

compact_certificate def auxSource993 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (97))

compact_certificate def auxSource994 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (98))

compact_certificate def auxSource995 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (99))

compact_certificate def auxSource996 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (100))

compact_certificate def auxSource997 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (101))

compact_certificate def auxSource998 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (102))

compact_certificate def auxSource999 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (103))

compact_certificate def auxSource1000 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (104))

compact_certificate def auxSource1001 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (105))

compact_certificate def auxSource1002 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (106))

compact_certificate def auxSource1003 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (107))

compact_certificate def auxSource1004 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (108))

compact_certificate def auxSource1005 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (109))

compact_certificate def auxSource1006 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (110))

compact_certificate def auxSource1007 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (111))

compact_certificate def auxSource1008 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (112))

compact_certificate def auxSource1009 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (113))

compact_certificate def auxSource1010 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (114))

compact_certificate def auxSource1011 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (115))

compact_certificate def auxSource1012 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (116))

compact_certificate def auxSource1013 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (117))

compact_certificate def auxSource1014 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (118))

compact_certificate def auxSource1015 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (119))

compact_certificate def auxSource1016 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (120))

compact_certificate def auxSource1017 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (121))

compact_certificate def auxSource1018 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (122))

compact_certificate def auxSource1019 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (123))

compact_certificate def auxSource1020 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (124))

compact_certificate def auxSource1021 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (125))

compact_certificate def auxSource1022 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (126))

compact_certificate def auxSource1023 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (127))

compact_certificate def auxSource1024 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (128))

compact_certificate def auxSource1025 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (129))

compact_certificate def auxSource1026 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (130))

compact_certificate def auxSource1027 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (131))

compact_certificate def auxSource1028 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (132))

compact_certificate def auxSource1029 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (133))

compact_certificate def auxSource1030 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (134))

compact_certificate def auxSource1031 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (135))

compact_certificate def auxSource1032 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (136))

compact_certificate def auxSource1033 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (137))

compact_certificate def auxSource1034 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (138))

compact_certificate def auxSource1035 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (139))

compact_certificate def auxSource1036 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (140))

compact_certificate def auxSource1037 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (141))

compact_certificate def auxSource1038 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (142))

compact_certificate def auxSource1039 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (143))

compact_certificate def auxSource1040 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (144))

compact_certificate def auxSource1041 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (145))

compact_certificate def auxSource1042 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (146))

compact_certificate def auxSource1043 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (147))

compact_certificate def auxSource1044 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (148))

compact_certificate def auxSource1045 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (149))

compact_certificate def auxSource1046 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (150))

compact_certificate def auxSource1047 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (151))

compact_certificate def auxSource1048 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (152))

compact_certificate def auxSource1049 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (153))

compact_certificate def auxSource1050 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (154))

compact_certificate def auxSource1051 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (155))

compact_certificate def auxSource1052 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (156))

compact_certificate def auxSource1053 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (157))

compact_certificate def auxSource1054 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (158))

compact_certificate def auxSource1055 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (159))

compact_certificate def auxSource1056 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (160))

compact_certificate def auxSource1057 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (161))

compact_certificate def auxSource1058 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (162))

compact_certificate def auxSource1059 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (163))

compact_certificate def auxSource1060 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (164))

compact_certificate def auxSource1061 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (165))

compact_certificate def auxSource1062 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (166))

compact_certificate def auxSource1063 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (167))

compact_certificate def auxSource1064 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (168))

compact_certificate def auxSource1065 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (169))

compact_certificate def auxSource1066 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (170))

compact_certificate def auxSource1067 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (171))

compact_certificate def auxSource1068 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (172))

compact_certificate def auxSource1069 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (173))

compact_certificate def auxSource1070 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (174))

compact_certificate def auxSource1071 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (175))

compact_certificate def auxSource1072 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (176))

compact_certificate def auxSource1073 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (177))

compact_certificate def auxSource1074 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (178))

compact_certificate def auxSource1075 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (179))

compact_certificate def auxSource1076 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (180))

compact_certificate def auxSource1077 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (181))

compact_certificate def auxSource1078 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (182))

compact_certificate def auxSource1079 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (183))

compact_certificate def auxSource1080 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (184))

compact_certificate def auxSource1081 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (185))

compact_certificate def auxSource1082 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (186))

compact_certificate def auxSource1083 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (187))

compact_certificate def auxSource1084 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (188))

compact_certificate def auxSource1085 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (189))

compact_certificate def auxSource1086 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (190))

compact_certificate def auxSource1087 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (191))

compact_certificate def auxSource1088 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (192))

compact_certificate def auxSource1089 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (193))

compact_certificate def auxSource1090 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (194))

compact_certificate def auxSource1091 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (195))

compact_certificate def auxSource1092 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (196))

compact_certificate def auxSource1093 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (197))

compact_certificate def auxSource1094 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (198))

compact_certificate def auxSource1095 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (199))

compact_certificate def auxSource1096 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (200))

compact_certificate def auxSource1097 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (201))

compact_certificate def auxSource1098 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (202))

compact_certificate def auxSource1099 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (203))

compact_certificate def auxSource1100 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (204))

compact_certificate def auxSource1101 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (205))

compact_certificate def auxSource1102 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (206))

compact_certificate def auxSource1103 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (207))

compact_certificate def auxSource1104 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (208))

compact_certificate def auxSource1105 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (209))

compact_certificate def auxSource1106 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (210))

compact_certificate def auxSource1107 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (211))

compact_certificate def auxSource1108 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (212))

compact_certificate def auxSource1109 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (213))

compact_certificate def auxSource1110 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (214))

compact_certificate def auxSource1111 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (215))

compact_certificate def auxSource1112 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (216))

compact_certificate def auxSource1113 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (217))

compact_certificate def auxSource1114 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (218))

compact_certificate def auxSource1115 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (219))

compact_certificate def auxSource1116 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (220))

compact_certificate def auxSource1117 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (221))

compact_certificate def auxSource1118 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (222))

compact_certificate def auxSource1119 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (223))

compact_certificate def auxSource1120 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (224))

compact_certificate def auxSource1121 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (225))

compact_certificate def auxSource1122 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (226))

compact_certificate def auxSource1123 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (227))

compact_certificate def auxSource1124 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (228))

compact_certificate def auxSource1125 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (229))

compact_certificate def auxSource1126 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (230))

compact_certificate def auxSource1127 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (231))

compact_certificate def auxSource1128 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (232))

compact_certificate def auxSource1129 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (233))

compact_certificate def auxSource1130 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (234))

compact_certificate def auxSource1131 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (235))

compact_certificate def auxSource1132 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (236))

compact_certificate def auxSource1133 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (237))

compact_certificate def auxSource1134 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (238))

compact_certificate def auxSource1135 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (239))

compact_certificate def auxSource1136 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (240))

compact_certificate def auxSource1137 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (241))

compact_certificate def auxSource1138 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (242))

compact_certificate def auxSource1139 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (243))

compact_certificate def auxSource1140 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (244))

compact_certificate def auxSource1141 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (245))

compact_certificate def auxSource1142 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (246))

compact_certificate def auxSource1143 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (247))

compact_certificate def auxSource1144 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (248))

compact_certificate def auxSource1145 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (249))

compact_certificate def auxSource1146 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (250))

compact_certificate def auxSource1147 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (251))

compact_certificate def auxSource1148 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (252))

compact_certificate def auxSource1149 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (253))

compact_certificate def auxSource1150 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (254))

compact_certificate def auxSource1151 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (255))

compact_certificate def auxSource1152 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (256))

compact_certificate def auxSource1153 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (257))

compact_certificate def auxSource1154 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (258))

compact_certificate def auxSource1155 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (259))

compact_certificate def auxSource1156 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (260))

compact_certificate def auxSource1157 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (261))

compact_certificate def auxSource1158 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (262))

compact_certificate def auxSource1159 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (263))

compact_certificate def auxSource1160 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (264))

compact_certificate def auxSource1161 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (265))

compact_certificate def auxSource1162 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (266))

compact_certificate def auxSource1163 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (267))

compact_certificate def auxSource1164 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (268))

compact_certificate def auxSource1165 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (269))

compact_certificate def auxSource1166 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (270))

compact_certificate def auxSource1167 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (271))

compact_certificate def auxSource1168 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (272))

compact_certificate def auxSource1169 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (273))

compact_certificate def auxSource1170 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (274))

compact_certificate def auxSource1171 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (275))

compact_certificate def auxSource1172 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (276))

compact_certificate def auxSource1173 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (277))

compact_certificate def auxSource1174 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (278))

compact_certificate def auxSource1175 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (279))

compact_certificate def auxSource1176 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (280))

compact_certificate def auxSource1177 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (281))

compact_certificate def auxSource1178 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (282))

compact_certificate def auxSource1179 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (283))

compact_certificate def auxSource1180 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (284))

compact_certificate def auxSource1181 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (285))

compact_certificate def auxSource1182 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (286))

compact_certificate def auxSource1183 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (287))

compact_certificate def auxSource1184 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (288))

compact_certificate def auxSource1185 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (289))

compact_certificate def auxSource1186 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (290))

compact_certificate def auxSource1187 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (291))

compact_certificate def auxSource1188 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (292))

compact_certificate def auxSource1189 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (293))

compact_certificate def auxSource1190 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (294))

compact_certificate def auxSource1191 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (295))

compact_certificate def auxSource1192 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (296))

compact_certificate def auxSource1193 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (297))

compact_certificate def auxSource1194 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (298))

compact_certificate def auxSource1195 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (299))

compact_certificate def auxSource1196 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (300))

compact_certificate def auxSource1197 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (301))

compact_certificate def auxSource1198 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (302))

compact_certificate def auxSource1199 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (303))

compact_certificate def auxSource1200 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (304))

compact_certificate def auxSource1201 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (305))

compact_certificate def auxSource1202 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (306))

compact_certificate def auxSource1203 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (307))

compact_certificate def auxSource1204 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (308))

compact_certificate def auxSource1205 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (309))

compact_certificate def auxSource1206 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (310))

compact_certificate def auxSource1207 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (311))

compact_certificate def auxSource1208 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (312))

compact_certificate def auxSource1209 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (313))

compact_certificate def auxSource1210 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (314))

compact_certificate def auxSource1211 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (315))

compact_certificate def auxSource1212 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (316))

compact_certificate def auxSource1213 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (317))

compact_certificate def auxSource1214 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (318))

compact_certificate def auxSource1215 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (319))

compact_certificate def auxSource1216 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (320))

compact_certificate def auxSource1217 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (321))

compact_certificate def auxSource1218 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (322))

compact_certificate def auxSource1219 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (323))

compact_certificate def auxSource1220 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (324))

compact_certificate def auxSource1221 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (325))

compact_certificate def auxSource1222 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (326))

compact_certificate def auxSource1223 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (327))

compact_certificate def auxSource1224 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (328))

compact_certificate def auxSource1225 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (329))

compact_certificate def auxSource1226 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (330))

compact_certificate def auxSource1227 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (331))

compact_certificate def auxSource1228 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (332))

compact_certificate def auxSource1229 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (333))

compact_certificate def auxSource1230 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (334))

compact_certificate def auxSource1231 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (335))

compact_certificate def auxSource1232 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (336))

compact_certificate def auxSource1233 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (337))

compact_certificate def auxSource1234 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (338))

compact_certificate def auxSource1235 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (339))

compact_certificate def auxSource1236 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (340))

compact_certificate def auxSource1237 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (341))

compact_certificate def auxSource1238 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (342))

compact_certificate def auxSource1239 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (343))

compact_certificate def auxSource1240 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (344))

compact_certificate def auxSource1241 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (345))

compact_certificate def auxSource1242 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (346))

compact_certificate def auxSource1243 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (347))

compact_certificate def auxSource1244 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (348))

compact_certificate def auxSource1245 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (349))

compact_certificate def auxSource1246 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (350))

compact_certificate def auxSource1247 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (351))

compact_certificate def auxSource1248 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (352))

compact_certificate def auxSource1249 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (353))

compact_certificate def auxSource1250 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (354))

compact_certificate def auxSource1251 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (355))

compact_certificate def auxSource1252 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (356))

compact_certificate def auxSource1253 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (357))

compact_certificate def auxSource1254 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (358))

compact_certificate def auxSource1255 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (359))

compact_certificate def auxSource1256 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (360))

compact_certificate def auxSource1257 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (361))

compact_certificate def auxSource1258 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (362))

compact_certificate def auxSource1259 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (363))

compact_certificate def auxSource1260 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (364))

compact_certificate def auxSource1261 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (365))

compact_certificate def auxSource1262 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (366))

compact_certificate def auxSource1263 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (367))

compact_certificate def auxSource1264 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (368))

compact_certificate def auxSource1265 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (369))

compact_certificate def auxSource1266 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (370))

compact_certificate def auxSource1267 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (371))

compact_certificate def auxSource1268 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (372))

compact_certificate def auxSource1269 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (373))

compact_certificate def auxSource1270 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (374))

compact_certificate def auxSource1271 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (375))

compact_certificate def auxSource1272 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (376))

compact_certificate def auxSource1273 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (377))

compact_certificate def auxSource1274 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (378))

compact_certificate def auxSource1275 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (379))

compact_certificate def auxSource1276 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (380))

compact_certificate def auxSource1277 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (381))

compact_certificate def auxSource1278 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (382))

compact_certificate def auxSource1279 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (383))

compact_certificate def auxSource1280 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (384))

compact_certificate def auxSource1281 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (385))

compact_certificate def auxSource1282 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (386))

compact_certificate def auxSource1283 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (387))

compact_certificate def auxSource1284 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (388))

compact_certificate def auxSource1285 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (389))

compact_certificate def auxSource1286 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (390))

compact_certificate def auxSource1287 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (391))

compact_certificate def auxSource1288 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (392))

compact_certificate def auxSource1289 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (393))

compact_certificate def auxSource1290 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (394))

compact_certificate def auxSource1291 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (395))

compact_certificate def auxSource1292 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (396))

compact_certificate def auxSource1293 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (397))

compact_certificate def auxSource1294 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (398))

compact_certificate def auxSource1295 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (399))

compact_certificate def auxSource1296 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (400))

compact_certificate def auxSource1297 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (401))

compact_certificate def auxSource1298 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (402))

compact_certificate def auxSource1299 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (403))

compact_certificate def auxSource1300 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (404))

compact_certificate def auxSource1301 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (405))

compact_certificate def auxSource1302 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (406))

compact_certificate def auxSource1303 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (407))

compact_certificate def auxSource1304 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (408))

compact_certificate def auxSource1305 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (409))

compact_certificate def auxSource1306 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (410))

compact_certificate def auxSource1307 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (411))

compact_certificate def auxSource1308 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (412))

compact_certificate def auxSource1309 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (413))

compact_certificate def auxSource1310 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (414))

compact_certificate def auxSource1311 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (415))

compact_certificate def auxSource1312 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (416))

compact_certificate def auxSource1313 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (417))

compact_certificate def auxSource1314 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (418))

compact_certificate def auxSource1315 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (419))

compact_certificate def auxSource1316 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (420))

compact_certificate def auxSource1317 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (421))

compact_certificate def auxSource1318 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (422))

compact_certificate def auxSource1319 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (423))

compact_certificate def auxSource1320 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (424))

compact_certificate def auxSource1321 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (425))

compact_certificate def auxSource1322 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (426))

compact_certificate def auxSource1323 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (427))

compact_certificate def auxSource1324 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (428))

compact_certificate def auxSource1325 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (429))

compact_certificate def auxSource1326 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (430))

compact_certificate def auxSource1327 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (431))

compact_certificate def auxSource1328 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (432))

compact_certificate def auxSource1329 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (433))

compact_certificate def auxSource1330 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (434))

compact_certificate def auxSource1331 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (435))

compact_certificate def auxSource1332 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (436))

compact_certificate def auxSource1333 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (437))

compact_certificate def auxSource1334 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (438))

compact_certificate def auxSource1335 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (439))

compact_certificate def auxSource1336 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (440))

compact_certificate def auxSource1337 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (441))

compact_certificate def auxSource1338 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (442))

compact_certificate def auxSource1339 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (443))

compact_certificate def auxSource1340 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (444))

compact_certificate def auxSource1341 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (445))

compact_certificate def auxSource1342 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (446))

compact_certificate def auxSource1343 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (447))

compact_certificate def auxSource1344 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (448))

compact_certificate def auxSource1345 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (449))

compact_certificate def auxSource1346 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (450))

compact_certificate def auxSource1347 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (451))

compact_certificate def auxSource1348 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (452))

compact_certificate def auxSource1349 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (453))

compact_certificate def auxSource1350 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (454))

compact_certificate def auxSource1351 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (455))

compact_certificate def auxSource1352 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (456))

compact_certificate def auxSource1353 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (457))

compact_certificate def auxSource1354 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (458))

compact_certificate def auxSource1355 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (459))

compact_certificate def auxSource1356 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (460))

compact_certificate def auxSource1357 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (461))

compact_certificate def auxSource1358 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (462))

compact_certificate def auxSource1359 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (463))

compact_certificate def auxSource1360 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (464))

compact_certificate def auxSource1361 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (465))

compact_certificate def auxSource1362 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (466))

compact_certificate def auxSource1363 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (467))

compact_certificate def auxSource1364 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (468))

compact_certificate def auxSource1365 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (469))

compact_certificate def auxSource1366 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (470))

compact_certificate def auxSource1367 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (471))

compact_certificate def auxSource1368 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (472))

compact_certificate def auxSource1369 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (473))

compact_certificate def auxSource1370 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (474))

compact_certificate def auxSource1371 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (475))

compact_certificate def auxSource1372 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (476))

compact_certificate def auxSource1373 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (477))

compact_certificate def auxSource1374 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (478))

compact_certificate def auxSource1375 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (479))

compact_certificate def auxSource1376 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (480))

compact_certificate def auxSource1377 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (481))

compact_certificate def auxSource1378 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (482))

compact_certificate def auxSource1379 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (483))

compact_certificate def auxSource1380 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (484))

compact_certificate def auxSource1381 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (485))

compact_certificate def auxSource1382 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (486))

compact_certificate def auxSource1383 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (487))

compact_certificate def auxSource1384 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (488))

compact_certificate def auxSource1385 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (489))

compact_certificate def auxSource1386 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (490))

compact_certificate def auxSource1387 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (491))

compact_certificate def auxSource1388 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (492))

compact_certificate def auxSource1389 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (493))

compact_certificate def auxSource1390 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (494))

compact_certificate def auxSource1391 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (495))

compact_certificate def auxSource1392 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (496))

compact_certificate def auxSource1393 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (497))

compact_certificate def auxSource1394 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (498))

compact_certificate def auxSource1395 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (499))

compact_certificate def auxSource1396 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (500))

compact_certificate def auxSource1397 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (501))

compact_certificate def auxSource1398 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (502))

compact_certificate def auxSource1399 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (503))

compact_certificate def auxSource1400 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (504))

compact_certificate def auxSource1401 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (505))

compact_certificate def auxSource1402 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (506))

compact_certificate def auxSource1403 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (507))

compact_certificate def auxSource1404 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (508))

compact_certificate def auxSource1405 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (509))

compact_certificate def auxSource1406 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (510))

compact_certificate def auxSource1407 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (511))

compact_certificate def auxSource1408 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (512))

compact_certificate def auxSource1409 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (513))

compact_certificate def auxSource1410 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (514))

compact_certificate def auxSource1411 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (515))

compact_certificate def auxSource1412 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (516))

compact_certificate def auxSource1413 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (517))

compact_certificate def auxSource1414 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (518))

compact_certificate def auxSource1415 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (519))

compact_certificate def auxSource1416 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (520))

compact_certificate def auxSource1417 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (521))

compact_certificate def auxSource1418 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (522))

compact_certificate def auxSource1419 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (523))

compact_certificate def auxSource1420 : SourceRow := .physical (.hecke 2 (by decide +kernel) (by decide +kernel) (524))

compact_certificate def auxSource1421 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (0))

compact_certificate def auxSource1422 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (1))

compact_certificate def auxSource1423 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (2))

compact_certificate def auxSource1424 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (3))

compact_certificate def auxSource1425 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (4))

compact_certificate def auxSource1426 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (5))

compact_certificate def auxSource1427 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (6))

compact_certificate def auxSource1428 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (7))

compact_certificate def auxSource1429 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (8))

compact_certificate def auxSource1430 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (9))

compact_certificate def auxSource1431 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (10))

compact_certificate def auxSource1432 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (11))

compact_certificate def auxSource1433 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (12))

compact_certificate def auxSource1434 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (13))

compact_certificate def auxSource1435 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (14))

compact_certificate def auxSource1436 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (15))

compact_certificate def auxSource1437 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (16))

compact_certificate def auxSource1438 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (17))

compact_certificate def auxSource1439 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (18))

compact_certificate def auxSource1440 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (19))

compact_certificate def auxSource1441 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (20))

compact_certificate def auxSource1442 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (21))

compact_certificate def auxSource1443 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (22))

compact_certificate def auxSource1444 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (23))

compact_certificate def auxSource1445 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (24))

compact_certificate def auxSource1446 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (25))

compact_certificate def auxSource1447 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (26))

compact_certificate def auxSource1448 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (27))

compact_certificate def auxSource1449 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (28))

compact_certificate def auxSource1450 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (29))

compact_certificate def auxSource1451 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (30))

compact_certificate def auxSource1452 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (31))

compact_certificate def auxSource1453 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (32))

compact_certificate def auxSource1454 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (33))

compact_certificate def auxSource1455 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (34))

compact_certificate def auxSource1456 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (35))

compact_certificate def auxSource1457 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (36))

compact_certificate def auxSource1458 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (37))

compact_certificate def auxSource1459 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (38))

compact_certificate def auxSource1460 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (39))

compact_certificate def auxSource1461 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (40))

compact_certificate def auxSource1462 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (41))

compact_certificate def auxSource1463 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (42))

compact_certificate def auxSource1464 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (43))

compact_certificate def auxSource1465 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (44))

compact_certificate def auxSource1466 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (45))

compact_certificate def auxSource1467 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (46))

compact_certificate def auxSource1468 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (47))

compact_certificate def auxSource1469 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (48))

compact_certificate def auxSource1470 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (49))

compact_certificate def auxSource1471 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (50))

compact_certificate def auxSource1472 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (51))

compact_certificate def auxSource1473 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (52))

compact_certificate def auxSource1474 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (53))

compact_certificate def auxSource1475 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (54))

compact_certificate def auxSource1476 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (55))

compact_certificate def auxSource1477 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (56))

compact_certificate def auxSource1478 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (57))

compact_certificate def auxSource1479 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (58))

compact_certificate def auxSource1480 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (59))

compact_certificate def auxSource1481 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (60))

compact_certificate def auxSource1482 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (61))

compact_certificate def auxSource1483 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (62))

compact_certificate def auxSource1484 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (63))

compact_certificate def auxSource1485 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (64))

compact_certificate def auxSource1486 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (65))

compact_certificate def auxSource1487 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (66))

compact_certificate def auxSource1488 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (67))

compact_certificate def auxSource1489 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (68))

compact_certificate def auxSource1490 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (69))

compact_certificate def auxSource1491 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (70))

compact_certificate def auxSource1492 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (71))

compact_certificate def auxSource1493 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (72))

compact_certificate def auxSource1494 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (73))

compact_certificate def auxSource1495 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (74))

compact_certificate def auxSource1496 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (75))

compact_certificate def auxSource1497 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (76))

compact_certificate def auxSource1498 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (77))

compact_certificate def auxSource1499 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (78))

compact_certificate def auxSource1500 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (79))

compact_certificate def auxSource1501 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (80))

compact_certificate def auxSource1502 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (81))

compact_certificate def auxSource1503 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (82))

compact_certificate def auxSource1504 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (83))

compact_certificate def auxSource1505 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (84))

compact_certificate def auxSource1506 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (85))

compact_certificate def auxSource1507 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (86))

compact_certificate def auxSource1508 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (87))

compact_certificate def auxSource1509 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (88))

compact_certificate def auxSource1510 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (89))

compact_certificate def auxSource1511 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (90))

compact_certificate def auxSource1512 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (91))

compact_certificate def auxSource1513 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (92))

compact_certificate def auxSource1514 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (93))

compact_certificate def auxSource1515 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (94))

compact_certificate def auxSource1516 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (95))

compact_certificate def auxSource1517 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (96))

compact_certificate def auxSource1518 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (97))

compact_certificate def auxSource1519 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (98))

compact_certificate def auxSource1520 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (99))

compact_certificate def auxSource1521 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (100))

compact_certificate def auxSource1522 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (101))

compact_certificate def auxSource1523 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (102))

compact_certificate def auxSource1524 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (103))

compact_certificate def auxSource1525 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (104))

compact_certificate def auxSource1526 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (105))

compact_certificate def auxSource1527 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (106))

compact_certificate def auxSource1528 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (107))

compact_certificate def auxSource1529 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (108))

compact_certificate def auxSource1530 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (109))

compact_certificate def auxSource1531 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (110))

compact_certificate def auxSource1532 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (111))

compact_certificate def auxSource1533 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (112))

compact_certificate def auxSource1534 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (113))

compact_certificate def auxSource1535 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (114))

compact_certificate def auxSource1536 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (115))

compact_certificate def auxSource1537 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (116))

compact_certificate def auxSource1538 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (117))

compact_certificate def auxSource1539 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (118))

compact_certificate def auxSource1540 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (119))

compact_certificate def auxSource1541 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (120))

compact_certificate def auxSource1542 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (121))

compact_certificate def auxSource1543 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (122))

compact_certificate def auxSource1544 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (123))

compact_certificate def auxSource1545 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (124))

compact_certificate def auxSource1546 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (125))

compact_certificate def auxSource1547 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (126))

compact_certificate def auxSource1548 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (127))

compact_certificate def auxSource1549 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (128))

compact_certificate def auxSource1550 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (129))

compact_certificate def auxSource1551 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (130))

compact_certificate def auxSource1552 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (131))

compact_certificate def auxSource1553 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (132))

compact_certificate def auxSource1554 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (133))

compact_certificate def auxSource1555 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (134))

compact_certificate def auxSource1556 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (135))

compact_certificate def auxSource1557 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (136))

compact_certificate def auxSource1558 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (137))

compact_certificate def auxSource1559 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (138))

compact_certificate def auxSource1560 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (139))

compact_certificate def auxSource1561 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (140))

compact_certificate def auxSource1562 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (141))

compact_certificate def auxSource1563 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (142))

compact_certificate def auxSource1564 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (143))

compact_certificate def auxSource1565 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (144))

compact_certificate def auxSource1566 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (145))

compact_certificate def auxSource1567 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (146))

compact_certificate def auxSource1568 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (147))

compact_certificate def auxSource1569 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (148))

compact_certificate def auxSource1570 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (149))

compact_certificate def auxSource1571 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (150))

compact_certificate def auxSource1572 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (151))

compact_certificate def auxSource1573 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (152))

compact_certificate def auxSource1574 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (153))

compact_certificate def auxSource1575 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (154))

compact_certificate def auxSource1576 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (155))

compact_certificate def auxSource1577 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (156))

compact_certificate def auxSource1578 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (157))

compact_certificate def auxSource1579 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (158))

compact_certificate def auxSource1580 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (159))

compact_certificate def auxSource1581 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (160))

compact_certificate def auxSource1582 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (161))

compact_certificate def auxSource1583 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (162))

compact_certificate def auxSource1584 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (163))

compact_certificate def auxSource1585 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (164))

compact_certificate def auxSource1586 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (165))

compact_certificate def auxSource1587 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (166))

compact_certificate def auxSource1588 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (167))

compact_certificate def auxSource1589 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (168))

compact_certificate def auxSource1590 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (169))

compact_certificate def auxSource1591 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (170))

compact_certificate def auxSource1592 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (171))

compact_certificate def auxSource1593 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (172))

compact_certificate def auxSource1594 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (173))

compact_certificate def auxSource1595 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (174))

compact_certificate def auxSource1596 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (175))

compact_certificate def auxSource1597 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (176))

compact_certificate def auxSource1598 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (177))

compact_certificate def auxSource1599 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (178))

compact_certificate def auxSource1600 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (179))

compact_certificate def auxSource1601 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (180))

compact_certificate def auxSource1602 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (181))

compact_certificate def auxSource1603 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (182))

compact_certificate def auxSource1604 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (183))

compact_certificate def auxSource1605 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (184))

compact_certificate def auxSource1606 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (185))

compact_certificate def auxSource1607 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (186))

compact_certificate def auxSource1608 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (187))

compact_certificate def auxSource1609 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (188))

compact_certificate def auxSource1610 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (189))

compact_certificate def auxSource1611 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (190))

compact_certificate def auxSource1612 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (191))

compact_certificate def auxSource1613 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (192))

compact_certificate def auxSource1614 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (193))

compact_certificate def auxSource1615 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (194))

compact_certificate def auxSource1616 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (195))

compact_certificate def auxSource1617 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (196))

compact_certificate def auxSource1618 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (197))

compact_certificate def auxSource1619 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (198))

compact_certificate def auxSource1620 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (199))

compact_certificate def auxSource1621 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (200))

compact_certificate def auxSource1622 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (201))

compact_certificate def auxSource1623 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (202))

compact_certificate def auxSource1624 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (203))

compact_certificate def auxSource1625 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (204))

compact_certificate def auxSource1626 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (205))

compact_certificate def auxSource1627 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (206))

compact_certificate def auxSource1628 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (207))

compact_certificate def auxSource1629 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (208))

compact_certificate def auxSource1630 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (209))

compact_certificate def auxSource1631 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (210))

compact_certificate def auxSource1632 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (211))

compact_certificate def auxSource1633 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (212))

compact_certificate def auxSource1634 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (213))

compact_certificate def auxSource1635 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (214))

compact_certificate def auxSource1636 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (215))

compact_certificate def auxSource1637 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (216))

compact_certificate def auxSource1638 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (217))

compact_certificate def auxSource1639 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (218))

compact_certificate def auxSource1640 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (219))

compact_certificate def auxSource1641 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (220))

compact_certificate def auxSource1642 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (221))

compact_certificate def auxSource1643 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (222))

compact_certificate def auxSource1644 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (223))

compact_certificate def auxSource1645 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (224))

compact_certificate def auxSource1646 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (225))

compact_certificate def auxSource1647 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (226))

compact_certificate def auxSource1648 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (227))

compact_certificate def auxSource1649 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (228))

compact_certificate def auxSource1650 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (229))

compact_certificate def auxSource1651 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (230))

compact_certificate def auxSource1652 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (231))

compact_certificate def auxSource1653 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (232))

compact_certificate def auxSource1654 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (233))

compact_certificate def auxSource1655 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (234))

compact_certificate def auxSource1656 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (235))

compact_certificate def auxSource1657 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (236))

compact_certificate def auxSource1658 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (237))

compact_certificate def auxSource1659 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (238))

compact_certificate def auxSource1660 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (239))

compact_certificate def auxSource1661 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (240))

compact_certificate def auxSource1662 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (241))

compact_certificate def auxSource1663 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (242))

compact_certificate def auxSource1664 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (243))

compact_certificate def auxSource1665 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (244))

compact_certificate def auxSource1666 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (245))

compact_certificate def auxSource1667 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (246))

compact_certificate def auxSource1668 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (247))

compact_certificate def auxSource1669 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (248))

compact_certificate def auxSource1670 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (249))

compact_certificate def auxSource1671 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (250))

compact_certificate def auxSource1672 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (251))

compact_certificate def auxSource1673 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (252))

compact_certificate def auxSource1674 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (253))

compact_certificate def auxSource1675 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (254))

compact_certificate def auxSource1676 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (255))

compact_certificate def auxSource1677 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (256))

compact_certificate def auxSource1678 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (257))

compact_certificate def auxSource1679 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (258))

compact_certificate def auxSource1680 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (259))

compact_certificate def auxSource1681 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (260))

compact_certificate def auxSource1682 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (261))

compact_certificate def auxSource1683 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (262))

compact_certificate def auxSource1684 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (263))

compact_certificate def auxSource1685 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (264))

compact_certificate def auxSource1686 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (265))

compact_certificate def auxSource1687 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (266))

compact_certificate def auxSource1688 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (267))

compact_certificate def auxSource1689 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (268))

compact_certificate def auxSource1690 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (269))

compact_certificate def auxSource1691 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (270))

compact_certificate def auxSource1692 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (271))

compact_certificate def auxSource1693 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (272))

compact_certificate def auxSource1694 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (273))

compact_certificate def auxSource1695 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (274))

compact_certificate def auxSource1696 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (275))

compact_certificate def auxSource1697 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (276))

compact_certificate def auxSource1698 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (277))

compact_certificate def auxSource1699 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (278))

compact_certificate def auxSource1700 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (279))

compact_certificate def auxSource1701 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (280))

compact_certificate def auxSource1702 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (281))

compact_certificate def auxSource1703 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (282))

compact_certificate def auxSource1704 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (283))

compact_certificate def auxSource1705 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (284))

compact_certificate def auxSource1706 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (285))

compact_certificate def auxSource1707 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (286))

compact_certificate def auxSource1708 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (287))

compact_certificate def auxSource1709 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (288))

compact_certificate def auxSource1710 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (289))

compact_certificate def auxSource1711 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (290))

compact_certificate def auxSource1712 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (291))

compact_certificate def auxSource1713 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (292))

compact_certificate def auxSource1714 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (293))

compact_certificate def auxSource1715 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (294))

compact_certificate def auxSource1716 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (295))

compact_certificate def auxSource1717 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (296))

compact_certificate def auxSource1718 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (297))

compact_certificate def auxSource1719 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (298))

compact_certificate def auxSource1720 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (299))

compact_certificate def auxSource1721 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (300))

compact_certificate def auxSource1722 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (301))

compact_certificate def auxSource1723 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (302))

compact_certificate def auxSource1724 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (303))

compact_certificate def auxSource1725 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (304))

compact_certificate def auxSource1726 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (305))

compact_certificate def auxSource1727 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (306))

compact_certificate def auxSource1728 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (307))

compact_certificate def auxSource1729 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (308))

compact_certificate def auxSource1730 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (309))

compact_certificate def auxSource1731 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (310))

compact_certificate def auxSource1732 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (311))

compact_certificate def auxSource1733 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (312))

compact_certificate def auxSource1734 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (313))

compact_certificate def auxSource1735 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (314))

compact_certificate def auxSource1736 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (315))

compact_certificate def auxSource1737 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (316))

compact_certificate def auxSource1738 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (317))

compact_certificate def auxSource1739 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (318))

compact_certificate def auxSource1740 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (319))

compact_certificate def auxSource1741 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (320))

compact_certificate def auxSource1742 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (321))

compact_certificate def auxSource1743 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (322))

compact_certificate def auxSource1744 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (323))

compact_certificate def auxSource1745 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (324))

compact_certificate def auxSource1746 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (325))

compact_certificate def auxSource1747 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (326))

compact_certificate def auxSource1748 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (327))

compact_certificate def auxSource1749 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (328))

compact_certificate def auxSource1750 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (329))

compact_certificate def auxSource1751 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (330))

compact_certificate def auxSource1752 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (331))

compact_certificate def auxSource1753 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (332))

compact_certificate def auxSource1754 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (333))

compact_certificate def auxSource1755 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (334))

compact_certificate def auxSource1756 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (335))

compact_certificate def auxSource1757 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (336))

compact_certificate def auxSource1758 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (337))

compact_certificate def auxSource1759 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (338))

compact_certificate def auxSource1760 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (339))

compact_certificate def auxSource1761 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (340))

compact_certificate def auxSource1762 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (341))

compact_certificate def auxSource1763 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (342))

compact_certificate def auxSource1764 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (343))

compact_certificate def auxSource1765 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (344))

compact_certificate def auxSource1766 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (345))

compact_certificate def auxSource1767 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (346))

compact_certificate def auxSource1768 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (347))

compact_certificate def auxSource1769 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (348))

compact_certificate def auxSource1770 : SourceRow := .physical (.hecke 3 (by decide +kernel) (by decide +kernel) (349))

compact_certificate def auxSource1771 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (0))

compact_certificate def auxSource1772 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (1))

compact_certificate def auxSource1773 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (2))

compact_certificate def auxSource1774 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (3))

compact_certificate def auxSource1775 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (4))

compact_certificate def auxSource1776 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (5))

compact_certificate def auxSource1777 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (6))

compact_certificate def auxSource1778 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (7))

compact_certificate def auxSource1779 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (8))

compact_certificate def auxSource1780 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (9))

compact_certificate def auxSource1781 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (10))

compact_certificate def auxSource1782 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (11))

compact_certificate def auxSource1783 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (12))

compact_certificate def auxSource1784 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (13))

compact_certificate def auxSource1785 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (14))

compact_certificate def auxSource1786 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (15))

compact_certificate def auxSource1787 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (16))

compact_certificate def auxSource1788 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (17))

compact_certificate def auxSource1789 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (18))

compact_certificate def auxSource1790 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (19))

compact_certificate def auxSource1791 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (20))

compact_certificate def auxSource1792 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (21))

compact_certificate def auxSource1793 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (22))

compact_certificate def auxSource1794 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (23))

compact_certificate def auxSource1795 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (24))

compact_certificate def auxSource1796 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (25))

compact_certificate def auxSource1797 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (26))

compact_certificate def auxSource1798 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (27))

compact_certificate def auxSource1799 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (28))

compact_certificate def auxSource1800 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (29))

compact_certificate def auxSource1801 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (30))

compact_certificate def auxSource1802 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (31))

compact_certificate def auxSource1803 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (32))

compact_certificate def auxSource1804 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (33))

compact_certificate def auxSource1805 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (34))

compact_certificate def auxSource1806 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (35))

compact_certificate def auxSource1807 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (36))

compact_certificate def auxSource1808 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (37))

compact_certificate def auxSource1809 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (38))

compact_certificate def auxSource1810 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (39))

compact_certificate def auxSource1811 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (40))

compact_certificate def auxSource1812 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (41))

compact_certificate def auxSource1813 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (42))

compact_certificate def auxSource1814 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (43))

compact_certificate def auxSource1815 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (44))

compact_certificate def auxSource1816 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (45))

compact_certificate def auxSource1817 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (46))

compact_certificate def auxSource1818 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (47))

compact_certificate def auxSource1819 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (48))

compact_certificate def auxSource1820 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (49))

compact_certificate def auxSource1821 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (50))

compact_certificate def auxSource1822 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (51))

compact_certificate def auxSource1823 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (52))

compact_certificate def auxSource1824 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (53))

compact_certificate def auxSource1825 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (54))

compact_certificate def auxSource1826 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (55))

compact_certificate def auxSource1827 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (56))

compact_certificate def auxSource1828 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (57))

compact_certificate def auxSource1829 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (58))

compact_certificate def auxSource1830 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (59))

compact_certificate def auxSource1831 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (60))

compact_certificate def auxSource1832 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (61))

compact_certificate def auxSource1833 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (62))

compact_certificate def auxSource1834 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (63))

compact_certificate def auxSource1835 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (64))

compact_certificate def auxSource1836 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (65))

compact_certificate def auxSource1837 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (66))

compact_certificate def auxSource1838 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (67))

compact_certificate def auxSource1839 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (68))

compact_certificate def auxSource1840 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (69))

compact_certificate def auxSource1841 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (70))

compact_certificate def auxSource1842 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (71))

compact_certificate def auxSource1843 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (72))

compact_certificate def auxSource1844 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (73))

compact_certificate def auxSource1845 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (74))

compact_certificate def auxSource1846 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (75))

compact_certificate def auxSource1847 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (76))

compact_certificate def auxSource1848 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (77))

compact_certificate def auxSource1849 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (78))

compact_certificate def auxSource1850 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (79))

compact_certificate def auxSource1851 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (80))

compact_certificate def auxSource1852 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (81))

compact_certificate def auxSource1853 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (82))

compact_certificate def auxSource1854 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (83))

compact_certificate def auxSource1855 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (84))

compact_certificate def auxSource1856 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (85))

compact_certificate def auxSource1857 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (86))

compact_certificate def auxSource1858 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (87))

compact_certificate def auxSource1859 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (88))

compact_certificate def auxSource1860 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (89))

compact_certificate def auxSource1861 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (90))

compact_certificate def auxSource1862 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (91))

compact_certificate def auxSource1863 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (92))

compact_certificate def auxSource1864 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (93))

compact_certificate def auxSource1865 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (94))

compact_certificate def auxSource1866 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (95))

compact_certificate def auxSource1867 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (96))

compact_certificate def auxSource1868 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (97))

compact_certificate def auxSource1869 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (98))

compact_certificate def auxSource1870 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (99))

compact_certificate def auxSource1871 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (100))

compact_certificate def auxSource1872 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (101))

compact_certificate def auxSource1873 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (102))

compact_certificate def auxSource1874 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (103))

compact_certificate def auxSource1875 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (104))

compact_certificate def auxSource1876 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (105))

compact_certificate def auxSource1877 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (106))

compact_certificate def auxSource1878 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (107))

compact_certificate def auxSource1879 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (108))

compact_certificate def auxSource1880 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (109))

compact_certificate def auxSource1881 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (110))

compact_certificate def auxSource1882 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (111))

compact_certificate def auxSource1883 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (112))

compact_certificate def auxSource1884 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (113))

compact_certificate def auxSource1885 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (114))

compact_certificate def auxSource1886 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (115))

compact_certificate def auxSource1887 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (116))

compact_certificate def auxSource1888 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (117))

compact_certificate def auxSource1889 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (118))

compact_certificate def auxSource1890 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (119))

compact_certificate def auxSource1891 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (120))

compact_certificate def auxSource1892 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (121))

compact_certificate def auxSource1893 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (122))

compact_certificate def auxSource1894 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (123))

compact_certificate def auxSource1895 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (124))

compact_certificate def auxSource1896 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (125))

compact_certificate def auxSource1897 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (126))

compact_certificate def auxSource1898 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (127))

compact_certificate def auxSource1899 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (128))

compact_certificate def auxSource1900 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (129))

compact_certificate def auxSource1901 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (130))

compact_certificate def auxSource1902 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (131))

compact_certificate def auxSource1903 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (132))

compact_certificate def auxSource1904 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (133))

compact_certificate def auxSource1905 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (134))

compact_certificate def auxSource1906 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (135))

compact_certificate def auxSource1907 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (136))

compact_certificate def auxSource1908 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (137))

compact_certificate def auxSource1909 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (138))

compact_certificate def auxSource1910 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (139))

compact_certificate def auxSource1911 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (140))

compact_certificate def auxSource1912 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (141))

compact_certificate def auxSource1913 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (142))

compact_certificate def auxSource1914 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (143))

compact_certificate def auxSource1915 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (144))

compact_certificate def auxSource1916 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (145))

compact_certificate def auxSource1917 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (146))

compact_certificate def auxSource1918 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (147))

compact_certificate def auxSource1919 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (148))

compact_certificate def auxSource1920 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (149))

compact_certificate def auxSource1921 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (150))

compact_certificate def auxSource1922 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (151))

compact_certificate def auxSource1923 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (152))

compact_certificate def auxSource1924 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (153))

compact_certificate def auxSource1925 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (154))

compact_certificate def auxSource1926 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (155))

compact_certificate def auxSource1927 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (156))

compact_certificate def auxSource1928 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (157))

compact_certificate def auxSource1929 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (158))

compact_certificate def auxSource1930 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (159))

compact_certificate def auxSource1931 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (160))

compact_certificate def auxSource1932 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (161))

compact_certificate def auxSource1933 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (162))

compact_certificate def auxSource1934 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (163))

compact_certificate def auxSource1935 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (164))

compact_certificate def auxSource1936 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (165))

compact_certificate def auxSource1937 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (166))

compact_certificate def auxSource1938 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (167))

compact_certificate def auxSource1939 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (168))

compact_certificate def auxSource1940 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (169))

compact_certificate def auxSource1941 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (170))

compact_certificate def auxSource1942 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (171))

compact_certificate def auxSource1943 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (172))

compact_certificate def auxSource1944 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (173))

compact_certificate def auxSource1945 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (174))

compact_certificate def auxSource1946 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (175))

compact_certificate def auxSource1947 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (176))

compact_certificate def auxSource1948 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (177))

compact_certificate def auxSource1949 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (178))

compact_certificate def auxSource1950 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (179))

compact_certificate def auxSource1951 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (180))

compact_certificate def auxSource1952 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (181))

compact_certificate def auxSource1953 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (182))

compact_certificate def auxSource1954 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (183))

compact_certificate def auxSource1955 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (184))

compact_certificate def auxSource1956 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (185))

compact_certificate def auxSource1957 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (186))

compact_certificate def auxSource1958 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (187))

compact_certificate def auxSource1959 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (188))

compact_certificate def auxSource1960 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (189))

compact_certificate def auxSource1961 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (190))

compact_certificate def auxSource1962 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (191))

compact_certificate def auxSource1963 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (192))

compact_certificate def auxSource1964 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (193))

compact_certificate def auxSource1965 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (194))

compact_certificate def auxSource1966 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (195))

compact_certificate def auxSource1967 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (196))

compact_certificate def auxSource1968 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (197))

compact_certificate def auxSource1969 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (198))

compact_certificate def auxSource1970 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (199))

compact_certificate def auxSource1971 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (200))

compact_certificate def auxSource1972 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (201))

compact_certificate def auxSource1973 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (202))

compact_certificate def auxSource1974 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (203))

compact_certificate def auxSource1975 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (204))

compact_certificate def auxSource1976 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (205))

compact_certificate def auxSource1977 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (206))

compact_certificate def auxSource1978 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (207))

compact_certificate def auxSource1979 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (208))

compact_certificate def auxSource1980 : SourceRow := .physical (.hecke 5 (by decide +kernel) (by decide +kernel) (209))

compact_certificate def auxSource1981 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (0))

compact_certificate def auxSource1982 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (1))

compact_certificate def auxSource1983 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (2))

compact_certificate def auxSource1984 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (3))

compact_certificate def auxSource1985 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (4))

compact_certificate def auxSource1986 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (5))

compact_certificate def auxSource1987 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (6))

compact_certificate def auxSource1988 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (7))

compact_certificate def auxSource1989 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (8))

compact_certificate def auxSource1990 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (9))

compact_certificate def auxSource1991 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (10))

compact_certificate def auxSource1992 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (11))

compact_certificate def auxSource1993 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (12))

compact_certificate def auxSource1994 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (13))

compact_certificate def auxSource1995 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (14))

compact_certificate def auxSource1996 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (15))

compact_certificate def auxSource1997 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (16))

compact_certificate def auxSource1998 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (17))

compact_certificate def auxSource1999 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (18))

compact_certificate def auxSource2000 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (19))

compact_certificate def auxSource2001 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (20))

compact_certificate def auxSource2002 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (21))

compact_certificate def auxSource2003 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (22))

compact_certificate def auxSource2004 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (23))

compact_certificate def auxSource2005 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (24))

compact_certificate def auxSource2006 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (25))

compact_certificate def auxSource2007 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (26))

compact_certificate def auxSource2008 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (27))

compact_certificate def auxSource2009 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (28))

compact_certificate def auxSource2010 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (29))

compact_certificate def auxSource2011 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (30))

compact_certificate def auxSource2012 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (31))

compact_certificate def auxSource2013 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (32))

compact_certificate def auxSource2014 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (33))

compact_certificate def auxSource2015 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (34))

compact_certificate def auxSource2016 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (35))

compact_certificate def auxSource2017 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (36))

compact_certificate def auxSource2018 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (37))

compact_certificate def auxSource2019 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (38))

compact_certificate def auxSource2020 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (39))

compact_certificate def auxSource2021 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (40))

compact_certificate def auxSource2022 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (41))

compact_certificate def auxSource2023 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (42))

compact_certificate def auxSource2024 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (43))

compact_certificate def auxSource2025 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (44))

compact_certificate def auxSource2026 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (45))

compact_certificate def auxSource2027 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (46))

compact_certificate def auxSource2028 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (47))

compact_certificate def auxSource2029 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (48))

compact_certificate def auxSource2030 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (49))

compact_certificate def auxSource2031 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (50))

compact_certificate def auxSource2032 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (51))

compact_certificate def auxSource2033 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (52))

compact_certificate def auxSource2034 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (53))

compact_certificate def auxSource2035 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (54))

compact_certificate def auxSource2036 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (55))

compact_certificate def auxSource2037 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (56))

compact_certificate def auxSource2038 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (57))

compact_certificate def auxSource2039 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (58))

compact_certificate def auxSource2040 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (59))

compact_certificate def auxSource2041 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (60))

compact_certificate def auxSource2042 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (61))

compact_certificate def auxSource2043 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (62))

compact_certificate def auxSource2044 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (63))

compact_certificate def auxSource2045 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (64))

compact_certificate def auxSource2046 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (65))

compact_certificate def auxSource2047 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (66))

compact_certificate def auxSource2048 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (67))

compact_certificate def auxSource2049 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (68))

compact_certificate def auxSource2050 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (69))

compact_certificate def auxSource2051 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (70))

compact_certificate def auxSource2052 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (71))

compact_certificate def auxSource2053 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (72))

compact_certificate def auxSource2054 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (73))

compact_certificate def auxSource2055 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (74))

compact_certificate def auxSource2056 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (75))

compact_certificate def auxSource2057 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (76))

compact_certificate def auxSource2058 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (77))

compact_certificate def auxSource2059 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (78))

compact_certificate def auxSource2060 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (79))

compact_certificate def auxSource2061 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (80))

compact_certificate def auxSource2062 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (81))

compact_certificate def auxSource2063 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (82))

compact_certificate def auxSource2064 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (83))

compact_certificate def auxSource2065 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (84))

compact_certificate def auxSource2066 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (85))

compact_certificate def auxSource2067 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (86))

compact_certificate def auxSource2068 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (87))

compact_certificate def auxSource2069 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (88))

compact_certificate def auxSource2070 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (89))

compact_certificate def auxSource2071 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (90))

compact_certificate def auxSource2072 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (91))

compact_certificate def auxSource2073 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (92))

compact_certificate def auxSource2074 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (93))

compact_certificate def auxSource2075 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (94))

compact_certificate def auxSource2076 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (95))

compact_certificate def auxSource2077 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (96))

compact_certificate def auxSource2078 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (97))

compact_certificate def auxSource2079 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (98))

compact_certificate def auxSource2080 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (99))

compact_certificate def auxSource2081 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (100))

compact_certificate def auxSource2082 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (101))

compact_certificate def auxSource2083 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (102))

compact_certificate def auxSource2084 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (103))

compact_certificate def auxSource2085 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (104))

compact_certificate def auxSource2086 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (105))

compact_certificate def auxSource2087 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (106))

compact_certificate def auxSource2088 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (107))

compact_certificate def auxSource2089 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (108))

compact_certificate def auxSource2090 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (109))

compact_certificate def auxSource2091 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (110))

compact_certificate def auxSource2092 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (111))

compact_certificate def auxSource2093 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (112))

compact_certificate def auxSource2094 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (113))

compact_certificate def auxSource2095 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (114))

compact_certificate def auxSource2096 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (115))

compact_certificate def auxSource2097 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (116))

compact_certificate def auxSource2098 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (117))

compact_certificate def auxSource2099 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (118))

compact_certificate def auxSource2100 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (119))

compact_certificate def auxSource2101 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (120))

compact_certificate def auxSource2102 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (121))

compact_certificate def auxSource2103 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (122))

compact_certificate def auxSource2104 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (123))

compact_certificate def auxSource2105 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (124))

compact_certificate def auxSource2106 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (125))

compact_certificate def auxSource2107 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (126))

compact_certificate def auxSource2108 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (127))

compact_certificate def auxSource2109 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (128))

compact_certificate def auxSource2110 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (129))

compact_certificate def auxSource2111 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (130))

compact_certificate def auxSource2112 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (131))

compact_certificate def auxSource2113 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (132))

compact_certificate def auxSource2114 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (133))

compact_certificate def auxSource2115 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (134))

compact_certificate def auxSource2116 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (135))

compact_certificate def auxSource2117 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (136))

compact_certificate def auxSource2118 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (137))

compact_certificate def auxSource2119 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (138))

compact_certificate def auxSource2120 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (139))

compact_certificate def auxSource2121 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (140))

compact_certificate def auxSource2122 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (141))

compact_certificate def auxSource2123 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (142))

compact_certificate def auxSource2124 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (143))

compact_certificate def auxSource2125 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (144))

compact_certificate def auxSource2126 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (145))

compact_certificate def auxSource2127 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (146))

compact_certificate def auxSource2128 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (147))

compact_certificate def auxSource2129 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (148))

compact_certificate def auxSource2130 : SourceRow := .physical (.hecke 7 (by decide +kernel) (by decide +kernel) (149))

compact_certificate def auxSource2131 : SourceRow := .physical (.entire 1 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2132 : SourceRow := .physical (.entire 2 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2133 : SourceRow := .physical (.entire 3 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2134 : SourceRow := .physical (.entire 5 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2135 : SourceRow := .physical (.entire 6 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2136 : SourceRow := .physical (.entire 7 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2137 : SourceRow := .physical (.entire 10 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2138 : SourceRow := .physical (.entire 14 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2139 : SourceRow := .physical (.entire 15 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2140 : SourceRow := .physical (.entire 21 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2141 : SourceRow := .physical (.entire 25 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2142 : SourceRow := .physical (.entire 30 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2143 : SourceRow := .physical (.entire 35 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2144 : SourceRow := .physical (.entire 42 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2145 : SourceRow := .physical (.entire 50 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2146 : SourceRow := .physical (.entire 70 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2147 : SourceRow := .physical (.entire 75 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2148 : SourceRow := .physical (.entire 105 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2149 : SourceRow := .physical (.entire 150 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2150 : SourceRow := .physical (.entire 175 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2151 : SourceRow := .physical (.entire 210 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2152 : SourceRow := .physical (.entire 350 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2153 : SourceRow := .physical (.entire 525 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2154 : SourceRow := .physical (.entire 1050 (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource2155 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord0) (0) (-21) (100) (50) (1) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2156 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord0) (105) (-20) ((441/4)) ((105/2)) (1) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2157 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord0) (350) (-18) ((1225/9)) ((175/3)) (1) ((0,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource2158 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord0) (840) (-15) (196) (70) (1) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2159 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord1) (0) (-42) (25) (25) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2160 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord1) (175) (-36) ((1225/36)) ((175/6)) (1) ((-2,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource2161 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord1) (210) (-35) (36) (30) (1) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2162 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord1) (420) (-30) (49) (35) (1) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2163 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord1) (525) (-28) ((225/4)) ((75/2)) (1) ((-2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2164 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord1) (714) (-25) ((1764/25)) (42) (1) ((2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2165 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (1) (-44100) ((1/44100)) ((1/42)) (1) ((-2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2166 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (2) (-22050) ((1/11025)) ((1/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2167 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (3) (-14700) ((1/4900)) ((1/14)) (1) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2168 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (4) (-11025) ((4/11025)) ((2/21)) (1) ((2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2169 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (5) (-8820) ((1/1764)) ((5/42)) (1) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2170 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (6) (-7350) ((1/1225)) ((1/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2171 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (7) (-6300) ((1/900)) ((1/6)) (1) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2172 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (9) (-4900) ((9/4900)) ((3/14)) (1) ((-2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2173 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (10) (-4410) ((1/441)) ((5/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2174 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (12) (-3675) ((4/1225)) ((2/7)) (1) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2175 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (14) (-3150) ((1/225)) ((1/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2176 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (15) (-2940) ((1/196)) ((5/14)) (1) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2177 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (18) (-2450) ((9/1225)) ((3/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2178 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (20) (-2205) ((4/441)) ((10/21)) (1) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2179 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (21) (-2100) ((1/100)) ((1/2)) (1) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2180 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (25) (-1764) ((25/1764)) ((25/42)) (1) ((-2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2181 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (28) (-1575) ((4/225)) ((2/3)) (1) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2182 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (30) (-1470) ((1/49)) ((5/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2183 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (35) (-1260) ((1/36)) ((5/6)) (1) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2184 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (36) (-1225) ((36/1225)) ((6/7)) (1) ((2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2185 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (42) (-1050) ((1/25)) (1) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2186 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (45) (-980) ((9/196)) ((15/14)) (1) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2187 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (49) (-900) ((49/900)) ((7/6)) (1) ((-2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2188 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (50) (-882) ((25/441)) ((25/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2189 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (60) (-735) ((4/49)) ((10/7)) (1) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2190 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (63) (-700) ((9/100)) ((3/2)) (1) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2191 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (70) (-630) ((1/9)) ((5/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2192 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (75) (-588) ((25/196)) ((25/14)) (1) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2193 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (84) (-525) ((4/25)) (2) (1) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2194 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (90) (-490) ((9/49)) ((15/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2195 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (98) (-450) ((49/225)) ((7/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2196 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (100) (-441) ((100/441)) ((50/21)) (1) ((2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2197 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (105) (-420) ((1/4)) ((5/2)) (1) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2198 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (126) (-350) ((9/25)) (3) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2199 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (140) (-315) ((4/9)) ((10/3)) (1) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2200 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (147) (-300) ((49/100)) ((7/2)) (1) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2201 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (150) (-294) ((25/49)) ((25/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2202 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (175) (-252) ((25/36)) ((25/6)) (1) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2203 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (180) (-245) ((36/49)) ((30/7)) (1) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2204 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (196) (-225) ((196/225)) ((14/3)) (1) ((2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2205 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (210) (-210) (1) (5) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2206 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (225) (-196) ((225/196)) ((75/14)) (1) ((-2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2207 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (245) (-180) ((49/36)) ((35/6)) (1) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2208 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (252) (-175) ((36/25)) (6) (1) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2209 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (294) (-150) ((49/25)) (7) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2210 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (300) (-147) ((100/49)) ((50/7)) (1) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2211 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (315) (-140) ((9/4)) ((15/2)) (1) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2212 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (350) (-126) ((25/9)) ((25/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2213 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (420) (-105) (4) (10) (1) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2214 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (441) (-100) ((441/100)) ((21/2)) (1) ((-2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2215 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (450) (-98) ((225/49)) ((75/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2216 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (490) (-90) ((49/9)) ((35/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2217 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (525) (-84) ((25/4)) ((25/2)) (1) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2218 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (588) (-75) ((196/25)) (14) (1) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2219 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (630) (-70) (9) (15) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2220 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (700) (-63) ((100/9)) ((50/3)) (1) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2221 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (735) (-60) ((49/4)) ((35/2)) (1) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2222 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (882) (-50) ((441/25)) (21) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2223 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (900) (-49) ((900/49)) ((150/7)) (1) ((2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2224 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord2) (980) (-45) ((196/9)) ((70/3)) (1) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2225 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (0) (42) (25) (-25) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2226 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (70) (45) ((196/9)) ((-70/3)) (1) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2227 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (150) (49) ((900/49)) ((-150/7)) (1) ((2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2228 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (168) (50) ((441/25)) (-21) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2229 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (315) (60) ((49/4)) ((-35/2)) (1) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2230 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (350) (63) ((100/9)) ((-50/3)) (1) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2231 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (420) (70) (9) (-15) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2232 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (462) (75) ((196/25)) (-14) (1) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2233 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (525) (84) ((25/4)) ((-25/2)) (1) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2234 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (560) (90) ((49/9)) ((-35/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2235 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (600) (98) ((225/49)) ((-75/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2236 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (609) (100) ((441/100)) ((-21/2)) (1) ((-2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2237 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (630) (105) (4) (-10) (1) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2238 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (700) (126) ((25/9)) ((-25/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2239 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (735) (140) ((9/4)) ((-15/2)) (1) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2240 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (750) (147) ((100/49)) ((-50/7)) (1) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2241 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (756) (150) ((49/25)) (-7) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2242 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (798) (175) ((36/25)) (-6) (1) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2243 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (805) (180) ((49/36)) ((-35/6)) (1) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2244 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (825) (196) ((225/196)) ((-75/14)) (1) ((-2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2245 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (840) (210) (1) (-5) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2246 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (854) (225) ((196/225)) ((-14/3)) (1) ((2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2247 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (870) (245) ((36/49)) ((-30/7)) (1) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2248 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (875) (252) ((25/36)) ((-25/6)) (1) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2249 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (900) (294) ((25/49)) ((-25/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2250 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (903) (300) ((49/100)) ((-7/2)) (1) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2251 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (910) (315) ((4/9)) ((-10/3)) (1) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2252 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (924) (350) ((9/25)) (-3) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2253 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (945) (420) ((1/4)) ((-5/2)) (1) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2254 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (950) (441) ((100/441)) ((-50/21)) (1) ((2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2255 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (952) (450) ((49/225)) ((-7/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2256 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (960) (490) ((9/49)) ((-15/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2257 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (966) (525) ((4/25)) (-2) (1) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2258 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (975) (588) ((25/196)) ((-25/14)) (1) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2259 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (980) (630) ((1/9)) ((-5/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2260 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (987) (700) ((9/100)) ((-3/2)) (1) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2261 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (990) (735) ((4/49)) ((-10/7)) (1) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2262 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1000) (882) ((25/441)) ((-25/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2263 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1001) (900) ((49/900)) ((-7/6)) (1) ((-2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2264 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1005) (980) ((9/196)) ((-15/14)) (1) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2265 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1008) (1050) ((1/25)) (-1) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2266 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1014) (1225) ((36/1225)) ((-6/7)) (1) ((2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2267 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1015) (1260) ((1/36)) ((-5/6)) (1) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2268 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1020) (1470) ((1/49)) ((-5/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2269 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1022) (1575) ((4/225)) ((-2/3)) (1) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2270 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1025) (1764) ((25/1764)) ((-25/42)) (1) ((-2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2271 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1029) (2100) ((1/100)) ((-1/2)) (1) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2272 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1030) (2205) ((4/441)) ((-10/21)) (1) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2273 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1032) (2450) ((9/1225)) ((-3/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2274 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1035) (2940) ((1/196)) ((-5/14)) (1) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2275 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1036) (3150) ((1/225)) ((-1/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2276 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1038) (3675) ((4/1225)) ((-2/7)) (1) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2277 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1040) (4410) ((1/441)) ((-5/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2278 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1041) (4900) ((9/4900)) ((-3/14)) (1) ((-2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2279 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1043) (6300) ((1/900)) ((-1/6)) (1) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource2280 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1044) (7350) ((1/1225)) ((-1/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2281 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1045) (8820) ((1/1764)) ((-5/42)) (1) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2282 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1046) (11025) ((4/11025)) ((-2/21)) (1) ((2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2283 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1047) (14700) ((1/4900)) ((-1/14)) (1) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2284 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1048) (22050) ((1/11025)) ((-1/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2285 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord3) (1049) (44100) ((1/44100)) ((-1/42)) (1) ((-2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource2286 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord4) (0) (21) (100) (-50) (1) ((2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2287 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord4) (336) (25) ((1764/25)) (-42) (1) ((2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource2288 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord4) (525) (28) ((225/4)) ((-75/2)) (1) ((-2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource2289 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord4) (630) (30) (49) (-35) (1) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2290 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord4) (840) (35) (36) (-30) (1) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2291 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord4) (875) (36) ((1225/36)) ((-175/6)) (1) ((-2,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource2292 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord5) (378) (-41) (1764) (-1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2293 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord6) (294) (43) (1764) (-1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2294 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord7) (630) (-20) (441) (-1050) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2295 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord7) (924) (-18) (49) (-350) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2296 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord7) (1008) (-14) (9) (-150) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2297 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord7) (1022) (-12) ((49/9)) ((-350/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2298 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord8) (210) (-40) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2299 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord8) (504) (-39) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2300 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord8) (651) (-38) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2301 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord8) (798) (-36) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2302 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord8) (840) (-35) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2303 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord8) (896) (-33) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2304 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord8) (945) (-30) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2305 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord8) (966) (-28) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2306 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord8) (994) (-24) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2307 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord8) (1008) (-21) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2308 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord8) (1029) (-14) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2309 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord8) (1043) (-6) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2310 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (126) (44) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2311 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (420) (45) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2312 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (567) (46) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2313 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (714) (48) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2314 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (756) (49) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2315 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (812) (51) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2316 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (861) (54) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2317 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (882) (56) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2318 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (910) (60) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2319 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (924) (63) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2320 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (945) (70) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2321 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (959) (78) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2322 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (966) (84) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2323 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (972) (91) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2324 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (980) (105) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2325 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (987) (126) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2326 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (990) (140) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2327 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (994) (168) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2328 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (996) (189) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2329 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (999) (238) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2330 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1001) (294) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2331 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1002) (336) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2332 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1004) (483) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2333 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1005) (630) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2334 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1006) (924) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2335 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1007) (1806) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2336 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1009) (-1722) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2337 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1010) (-840) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2338 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1011) (-546) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2339 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1012) (-399) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2340 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1014) (-252) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2341 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1015) (-210) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2342 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1017) (-154) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2343 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1020) (-105) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2344 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1022) (-84) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2345 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1026) (-56) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2346 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1029) (-42) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2347 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1036) (-21) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2348 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord9) (1044) (-7) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2349 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord10) (588) (22) (441) (-1050) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2350 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord10) (882) (24) (49) (-350) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2351 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord10) (966) (28) (9) (-150) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2352 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord10) (980) (30) ((49/9)) ((-350/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2353 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord10) (1008) (42) (1) (-50) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2354 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord10) (1020) (70) ((9/49)) ((-150/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2355 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord10) (1022) (84) ((1/9)) ((-50/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2356 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord10) (1026) (168) ((1/49)) ((-50/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2357 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord10) (1028) (462) ((1/441)) ((-50/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2358 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord10) (1030) (-420) ((1/441)) ((50/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2359 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord10) (1032) (-126) ((1/49)) ((50/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2360 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord10) (1036) (-42) ((1/9)) ((50/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2361 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord10) (1038) (-28) ((9/49)) ((150/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2362 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord11) (7) (14) ((1/4)) ((-75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2363 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord11) (10) (35) ((4/49)) ((-150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2364 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord11) (12) (84) ((1/49)) ((-75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2365 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord11) (13) (182) ((1/196)) ((-75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2366 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord11) (15) (-210) ((1/196)) ((75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2367 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord11) (16) (-112) ((1/49)) ((75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2368 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord11) (18) (-63) ((4/49)) ((150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2369 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord11) (21) (-42) ((1/4)) ((75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2370 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord11) (28) (-28) (1) (75) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2371 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord11) (42) (-21) (4) (150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2372 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord11) (63) (-18) ((49/4)) ((525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2373 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord11) (112) (-16) (49) (525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2374 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord11) (210) (-15) (196) (1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2375 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord12) (12) (28) ((9/49)) ((-150/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2376 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord12) (14) (42) ((1/9)) ((-50/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2377 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord12) (18) (126) ((1/49)) ((-50/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2378 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord12) (20) (420) ((1/441)) ((-50/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2379 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord12) (22) (-462) ((1/441)) ((50/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2380 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord12) (24) (-168) ((1/49)) ((50/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2381 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord12) (28) (-84) ((1/9)) ((50/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2382 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord12) (30) (-70) ((9/49)) ((150/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2383 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord12) (42) (-42) (1) (50) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2384 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord12) (70) (-30) ((49/9)) ((350/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2385 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord12) (84) (-28) (9) (150) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2386 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord12) (168) (-24) (49) (350) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2387 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord12) (462) (-22) (441) (1050) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2388 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (6) (7) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2389 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (14) (21) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2390 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (21) (42) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2391 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (24) (56) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2392 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (28) (84) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2393 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (30) (105) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2394 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (33) (154) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2395 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (35) (210) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2396 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (36) (252) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2397 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (38) (399) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2398 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (39) (546) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2399 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (40) (840) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2400 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (41) (1722) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2401 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (43) (-1806) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2402 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (44) (-924) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2403 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (45) (-630) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2404 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (46) (-483) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2405 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (48) (-336) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2406 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (49) (-294) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2407 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (51) (-238) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2408 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (54) (-189) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2409 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (56) (-168) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2410 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (60) (-140) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2411 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (63) (-126) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2412 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (70) (-105) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2413 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (78) (-91) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2414 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (84) (-84) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2415 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (91) (-78) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2416 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (105) (-70) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2417 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (126) (-63) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2418 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (140) (-60) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2419 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (168) (-56) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2420 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (189) (-54) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2421 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (238) (-51) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2422 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (294) (-49) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2423 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (336) (-48) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2424 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (483) (-46) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2425 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (630) (-45) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2426 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord13) (924) (-44) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2427 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord14) (7) (6) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2428 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord14) (21) (14) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2429 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord14) (42) (21) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2430 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord14) (56) (24) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2431 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord14) (84) (28) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2432 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord14) (105) (30) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2433 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord14) (154) (33) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2434 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord14) (210) (35) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2435 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord14) (252) (36) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2436 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord14) (399) (38) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2437 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord14) (546) (39) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2438 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord14) (840) (40) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2439 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord15) (28) (12) ((49/9)) ((350/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2440 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord15) (42) (14) (9) (150) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2441 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord15) (126) (18) (49) (350) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2442 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord15) (420) (20) (441) (1050) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2443 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord16) (14) (7) (4) (150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2444 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord16) (35) (10) ((49/4)) ((525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2445 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord16) (84) (12) (49) (525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2446 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord16) (182) (13) (196) (1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2447 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord17) (756) (-43) (1764) (1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2448 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord18) (672) (41) (1764) (1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2449 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord19) (882) (-83) (1764) (-1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2450 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord20) (714) (-82) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2451 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord20) (1008) (-81) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2452 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord21) (672) (86) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2453 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord21) (966) (87) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2454 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (441) (-16) ((441/4)) ((-2625/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2455 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (490) (-15) ((196/9)) ((-1750/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2456 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (504) (-14) (9) (-375) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2457 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (522) (-7) ((36/49)) ((-750/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2458 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (525) (0) ((1/4)) ((-125/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2459 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (528) (42) ((1/49)) ((-125/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2460 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (529) (336) ((1/1764)) ((-125/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2461 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (530) (-105) ((4/441)) ((250/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2462 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (531) (-56) ((9/196)) ((375/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2463 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (532) (-42) ((1/9)) ((125/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2464 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (539) (-24) ((49/36)) ((875/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2465 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (546) (-21) (4) (250) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2466 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (588) (-18) (49) (875) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2467 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord22) (882) (-17) (1764) (5250) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2468 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (336) (-27) (196) (-1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2469 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (434) (-26) (49) (-525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2470 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (483) (-24) ((49/4)) ((-525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2471 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (504) (-21) (4) (-150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2472 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (518) (-14) (1) (-75) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2473 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (525) (0) ((1/4)) ((-75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2474 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (528) (21) ((4/49)) ((-150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2475 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (530) (70) ((1/49)) ((-75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2476 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (531) (168) ((1/196)) ((-75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2477 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (533) (-224) ((1/196)) ((75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2478 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (534) (-126) ((1/49)) ((75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2479 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (536) (-77) ((4/49)) ((150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2480 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (539) (-56) ((1/4)) ((75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2481 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (546) (-42) (1) (75) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2482 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (560) (-35) (4) (150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2483 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (581) (-32) ((49/4)) ((525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2484 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (630) (-30) (49) (525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2485 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord23) (728) (-29) (196) (1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2486 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (105) (-80) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2487 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (252) (-78) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2488 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (294) (-77) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2489 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (350) (-75) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2490 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (399) (-72) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2491 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (420) (-70) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2492 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (448) (-66) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2493 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (462) (-63) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2494 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (483) (-56) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2495 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (497) (-48) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2496 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (504) (-42) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2497 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (510) (-35) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2498 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (518) (-21) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2499 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (525) (0) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2500 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (528) (14) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2501 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (532) (42) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2502 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (534) (63) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2503 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (537) (112) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2504 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (539) (168) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2505 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (540) (210) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2506 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (542) (357) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2507 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (543) (504) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2508 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (544) (798) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2509 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (545) (1680) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2510 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (547) (-1848) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2511 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (548) (-966) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2512 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (549) (-672) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2513 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (550) (-525) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2514 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (552) (-378) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2515 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (553) (-336) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2516 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (555) (-280) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2517 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (558) (-231) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2518 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (560) (-210) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2519 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (564) (-182) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2520 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (567) (-168) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2521 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (574) (-147) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2522 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (582) (-133) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2523 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (588) (-126) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2524 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (595) (-120) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2525 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (609) (-112) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2526 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (630) (-105) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2527 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (644) (-102) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2528 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (672) (-98) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2529 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (693) (-96) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2530 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (742) (-93) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2531 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (798) (-91) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2532 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (840) (-90) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2533 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord24) (987) (-88) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2534 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (63) (88) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2535 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (210) (90) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2536 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (252) (91) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2537 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (308) (93) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2538 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (357) (96) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2539 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (378) (98) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2540 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (406) (102) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2541 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (420) (105) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2542 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (441) (112) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2543 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (455) (120) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2544 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (462) (126) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2545 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (468) (133) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2546 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (476) (147) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2547 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (483) (168) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2548 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (486) (182) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2549 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (490) (210) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2550 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (492) (231) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2551 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (495) (280) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2552 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (497) (336) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2553 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (498) (378) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2554 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (500) (525) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2555 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (501) (672) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2556 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (502) (966) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2557 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (503) (1848) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2558 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (505) (-1680) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2559 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (506) (-798) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2560 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (507) (-504) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2561 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (508) (-357) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2562 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (510) (-210) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2563 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (511) (-168) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2564 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (513) (-112) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2565 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (516) (-63) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2566 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (518) (-42) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2567 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (522) (-14) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2568 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (525) (0) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2569 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (532) (21) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2570 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (540) (35) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2571 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (546) (42) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2572 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (553) (48) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2573 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (567) (56) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2574 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (588) (63) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2575 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (602) (66) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2576 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (630) (70) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2577 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (651) (72) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2578 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (700) (75) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2579 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (756) (77) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2580 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (798) (78) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2581 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord25) (945) (80) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2582 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (322) (29) (196) (-1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2583 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (420) (30) (49) (-525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2584 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (469) (32) ((49/4)) ((-525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2585 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (490) (35) (4) (-150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2586 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (504) (42) (1) (-75) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2587 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (511) (56) ((1/4)) ((-75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2588 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (514) (77) ((4/49)) ((-150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2589 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (516) (126) ((1/49)) ((-75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2590 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (517) (224) ((1/196)) ((-75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2591 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (519) (-168) ((1/196)) ((75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2592 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (520) (-70) ((1/49)) ((75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2593 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (522) (-21) ((4/49)) ((150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2594 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (525) (0) ((1/4)) ((75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2595 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (532) (14) (1) (75) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2596 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (546) (21) (4) (150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2597 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (567) (24) ((49/4)) ((525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2598 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (616) (26) (49) (525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2599 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord26) (714) (27) (196) (1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2600 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord27) (84) (-87) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2601 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord27) (378) (-86) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2602 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord28) (42) (81) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2603 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord28) (336) (82) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2604 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord29) (210) (-85) (1764) (1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2605 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord30) (252) (506) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2606 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord30) (546) (507) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2607 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord30) (693) (508) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2608 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord30) (840) (510) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2609 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord30) (882) (511) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2610 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord30) (938) (513) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2611 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord30) (987) (516) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2612 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord30) (1008) (518) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2613 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord30) (1036) (522) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2614 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (84) (-502) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2615 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (378) (-501) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2616 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (525) (-500) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2617 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (672) (-498) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2618 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (714) (-497) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2619 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (770) (-495) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2620 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (819) (-492) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2621 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (840) (-490) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2622 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (868) (-486) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2623 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (882) (-483) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2624 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (903) (-476) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2625 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (917) (-468) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2626 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (924) (-462) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2627 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (930) (-455) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2628 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (938) (-441) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2629 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (945) (-420) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2630 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (948) (-406) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2631 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (952) (-378) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2632 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (954) (-357) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2633 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (957) (-308) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2634 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (959) (-252) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2635 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (960) (-210) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2636 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (962) (-63) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2637 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (963) (84) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2638 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (964) (378) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2639 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (965) (1260) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2640 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (967) (-2268) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2641 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (968) (-1386) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2642 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (969) (-1092) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2643 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (970) (-945) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2644 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (972) (-798) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2645 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (973) (-756) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2646 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (975) (-700) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2647 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (978) (-651) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2648 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (980) (-630) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2649 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (984) (-602) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2650 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (987) (-588) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2651 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (994) (-567) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2652 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (1002) (-553) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2653 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (1008) (-546) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2654 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (1015) (-540) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2655 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord31) (1029) (-532) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2656 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord32) (70) (-45) ((196/9)) ((-3850/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2657 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord32) (84) (-42) (1) (-275) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2658 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord32) (87) (-28) ((9/196)) ((-825/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2659 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord32) (88) (-126) ((1/441)) ((275/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2660 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord32) (168) (-46) (441) (5775) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2661 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (0) (525) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2662 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (21) (532) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2663 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (35) (540) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2664 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (42) (546) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2665 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (48) (553) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2666 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (56) (567) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2667 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (63) (588) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2668 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (66) (602) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2669 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (70) (630) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2670 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (72) (651) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2671 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (75) (700) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2672 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (77) (756) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2673 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (78) (798) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2674 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (80) (945) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2675 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (81) (1092) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2676 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (82) (1386) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2677 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (83) (2268) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2678 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (85) (-1260) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2679 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (86) (-378) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2680 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (87) (-84) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2681 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (88) (63) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2682 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (90) (210) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2683 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (91) (252) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2684 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (93) (308) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2685 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (96) (357) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2686 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (98) (378) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2687 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (102) (406) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2688 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (105) (420) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2689 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (112) (441) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2690 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (120) (455) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2691 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (126) (462) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2692 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (133) (468) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2693 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (147) (476) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2694 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (168) (483) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2695 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (182) (486) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2696 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (210) (490) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2697 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (231) (492) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2698 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (280) (495) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2699 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (336) (497) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2700 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (378) (498) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2701 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (525) (500) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2702 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (672) (501) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2703 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord33) (966) (502) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2704 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord34) (42) (39) (196) (-4550) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2705 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord34) (84) (42) (1) (-325) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2706 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord34) (87) (84) ((1/196)) ((-325/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2707 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord34) (90) (35) ((36/49)) ((1950/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2708 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord34) (91) (36) ((49/36)) ((2275/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2709 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord35) (0) (-525) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2710 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord35) (14) (-522) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2711 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord35) (42) (-518) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2712 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord35) (63) (-516) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2713 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord35) (112) (-513) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2714 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord35) (168) (-511) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2715 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord35) (210) (-510) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2716 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord35) (357) (-508) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2717 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord35) (504) (-507) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2718 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord35) (798) (-506) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2719 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord36) (798) (503) (1764) (1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2720 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord37) (630) (-505) (1764) (1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2721 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord38) (252) (547) (1764) (-1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2722 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord39) (945) (-45) (49) (-2100) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2723 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord39) (966) (-42) (1) (-300) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2724 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord39) (969) (-21) ((1/49)) ((-300/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2725 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord39) (970) (-70) ((1/49)) ((300/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2726 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord39) (973) (-49) (1) (300) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2727 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord39) (994) (-46) (49) (2100) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2728 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (84) (548) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2729 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (378) (549) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2730 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (525) (550) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2731 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (672) (552) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2732 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (714) (553) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2733 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (770) (555) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2734 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (819) (558) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2735 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (840) (560) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2736 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (868) (564) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2737 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (882) (567) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2738 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (903) (574) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2739 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (917) (582) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2740 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (924) (588) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2741 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (930) (595) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2742 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (938) (609) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2743 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (945) (630) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2744 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (948) (644) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2745 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (952) (672) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2746 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (954) (693) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2747 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (957) (742) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2748 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (959) (798) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2749 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (960) (840) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2750 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (962) (987) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2751 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (963) (1134) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2752 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (964) (1428) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2753 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (965) (2310) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2754 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (967) (-1218) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2755 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (968) (-336) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2756 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (969) (-42) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2757 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (970) (105) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2758 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (972) (252) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2759 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (973) (294) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2760 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (975) (350) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2761 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (978) (399) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2762 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (980) (420) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2763 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (984) (448) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2764 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (987) (462) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2765 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (994) (483) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2766 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (1002) (497) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2767 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (1008) (504) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2768 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (1015) (510) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2769 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord40) (1029) (518) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2770 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord41) (960) (40) (9) (-1050) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2771 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord41) (966) (42) (1) (-350) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2772 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord41) (968) (48) ((1/9)) ((-350/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2773 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord41) (970) (30) ((1/9)) ((350/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2774 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord41) (972) (36) (1) (350) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2775 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord41) (978) (38) (9) (1050) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2776 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (0) (-525) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2777 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (21) (-518) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2778 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (35) (-510) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2779 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (42) (-504) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2780 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (48) (-497) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2781 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (56) (-483) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2782 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (63) (-462) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2783 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (66) (-448) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2784 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (70) (-420) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2785 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (72) (-399) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2786 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (75) (-350) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2787 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (77) (-294) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2788 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (78) (-252) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2789 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (80) (-105) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2790 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (81) (42) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2791 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (82) (336) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2792 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (83) (1218) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2793 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (85) (-2310) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2794 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (86) (-1428) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2795 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (87) (-1134) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2796 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (88) (-987) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2797 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (90) (-840) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2798 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (91) (-798) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2799 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (93) (-742) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2800 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (96) (-693) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2801 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (98) (-672) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2802 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (102) (-644) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2803 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (105) (-630) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2804 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (112) (-609) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2805 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (120) (-595) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2806 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (126) (-588) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2807 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (133) (-582) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2808 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (147) (-574) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2809 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (168) (-567) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2810 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (182) (-564) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2811 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (210) (-560) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2812 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (231) (-558) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2813 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (280) (-555) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2814 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (336) (-553) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2815 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (378) (-552) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2816 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (525) (-550) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2817 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (672) (-549) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2818 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord42) (966) (-548) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2819 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord43) (0) (525) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2820 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord43) (14) (528) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2821 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord43) (42) (532) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2822 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord43) (63) (534) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2823 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord43) (112) (537) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2824 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord43) (168) (539) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2825 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord43) (210) (540) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2826 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord43) (357) (542) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2827 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord43) (504) (543) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2828 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord43) (798) (544) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2829 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord44) (630) (545) (1764) (1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2830 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord45) (462) (-88) (441) (-5250) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2831 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord45) (546) (-84) (1) (-250) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2832 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord45) (550) (0) ((1/441)) ((-250/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2833 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord45) (552) (-98) ((9/49)) ((750/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2834 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord45) (560) (-90) ((49/9)) ((1750/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2835 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord46) (420) (-80) (441) (-5775) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2836 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord46) (500) (0) ((1/441)) ((-275/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2837 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord46) (501) (-98) ((9/196)) ((825/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2838 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord46) (504) (-84) (1) (275) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2839 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord46) (518) (-81) ((196/9)) ((3850/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2840 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord47) (714) (968) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2841 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord47) (1008) (969) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2842 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord48) (980) (-80) (49) (-2100) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2843 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord48) (1001) (-77) (1) (-300) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2844 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord48) (1004) (-56) ((1/49)) ((-300/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2845 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord48) (1005) (-105) ((1/49)) ((300/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2846 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord48) (1008) (-84) (1) (300) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2847 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord48) (1029) (-81) (49) (2100) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2848 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord49) (546) (-42) (1) (-550) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2849 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord49) (548) (-84) ((1/441)) ((550/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2850 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord49) (588) (-44) (441) (11550) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2851 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (105) (970) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2852 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (252) (972) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2853 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (294) (973) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2854 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (350) (975) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2855 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (399) (978) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2856 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (420) (980) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2857 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (448) (984) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2858 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (462) (987) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2859 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (483) (994) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2860 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (497) (1002) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2861 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (504) (1008) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2862 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (510) (1015) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2863 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (518) (1029) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2864 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (525) (1050) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2865 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (528) (1064) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2866 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (532) (1092) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2867 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (534) (1113) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2868 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (537) (1162) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2869 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (539) (1218) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2870 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (540) (1260) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2871 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (542) (1407) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2872 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (543) (1554) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2873 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (544) (1848) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2874 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (545) (2730) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2875 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (547) (-798) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2876 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (548) (84) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2877 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (549) (378) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2878 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (550) (525) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2879 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (552) (672) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2880 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (553) (714) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2881 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (555) (770) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2882 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (558) (819) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2883 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (560) (840) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2884 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (564) (868) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2885 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (567) (882) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2886 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (574) (903) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2887 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (582) (917) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2888 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (588) (924) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2889 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (595) (930) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2890 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (609) (938) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2891 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (630) (945) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2892 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (644) (948) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2893 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (672) (952) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2894 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (693) (954) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2895 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (742) (957) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2896 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (798) (959) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2897 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (840) (960) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2898 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord50) (987) (962) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2899 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord51) (546) (42) (1) (-600) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2900 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord51) (548) (28) ((1/49)) ((600/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2901 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord51) (560) (40) (49) (4200) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2902 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (63) (-962) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2903 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (210) (-960) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2904 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (252) (-959) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2905 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (308) (-957) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2906 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (357) (-954) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2907 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (378) (-952) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2908 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (406) (-948) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2909 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (420) (-945) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2910 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (441) (-938) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2911 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (455) (-930) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2912 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (462) (-924) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2913 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (468) (-917) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2914 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (476) (-903) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2915 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (483) (-882) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2916 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (486) (-868) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2917 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (490) (-840) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2918 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (492) (-819) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2919 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (495) (-770) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2920 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (497) (-714) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2921 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (498) (-672) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2922 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (500) (-525) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2923 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (501) (-378) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2924 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (502) (-84) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2925 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (503) (798) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2926 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (505) (-2730) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2927 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (506) (-1848) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2928 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (507) (-1554) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2929 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (508) (-1407) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2930 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (510) (-1260) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2931 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (511) (-1218) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2932 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (513) (-1162) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2933 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (516) (-1113) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2934 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (518) (-1092) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2935 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (522) (-1064) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2936 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (525) (-1050) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2937 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (532) (-1029) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2938 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (540) (-1015) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2939 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (546) (-1008) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2940 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (553) (-1002) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2941 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (567) (-994) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2942 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (588) (-987) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2943 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (602) (-984) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2944 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (630) (-980) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2945 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (651) (-978) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2946 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (700) (-975) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2947 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (756) (-973) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2948 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (798) (-972) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2949 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord52) (945) (-970) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2950 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord53) (28) (-87) ((196/9)) ((-3850/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2951 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord53) (42) (-84) (1) (-275) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2952 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord53) (45) (-70) ((9/196)) ((-825/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2953 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord53) (46) (-168) ((1/441)) ((275/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2954 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord53) (126) (-88) (441) (5775) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2955 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord54) (84) (963) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2956 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord54) (378) (964) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2957 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord55) (210) (1010) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2958 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord55) (504) (1011) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2959 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord55) (651) (1012) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2960 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord55) (798) (1014) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2961 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord55) (840) (1015) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2962 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord55) (896) (1017) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2963 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord55) (945) (1020) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2964 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord55) (966) (1022) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2965 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord55) (994) (1026) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2966 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord55) (1008) (1029) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2967 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord55) (1029) (1036) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2968 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord55) (1043) (1044) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2969 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (126) (-1006) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2970 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (420) (-1005) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2971 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (567) (-1004) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2972 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (714) (-1002) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2973 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (756) (-1001) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2974 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (812) (-999) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2975 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (861) (-996) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2976 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (882) (-994) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2977 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (910) (-990) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2978 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (924) (-987) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2979 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (945) (-980) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2980 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (959) (-972) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource2981 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (966) (-966) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2982 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (972) (-959) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2983 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (980) (-945) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2984 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (987) (-924) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2985 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (990) (-910) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2986 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (994) (-882) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2987 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (996) (-861) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2988 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (999) (-812) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2989 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1001) (-756) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource2990 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1002) (-714) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2991 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1004) (-567) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2992 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1005) (-420) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2993 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1006) (-126) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2994 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1007) (756) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2995 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1009) (-2772) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2996 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1010) (-1890) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2997 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1011) (-1596) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2998 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1012) (-1449) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource2999 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1014) (-1302) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3000 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1015) (-1260) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3001 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1017) (-1204) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3002 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1020) (-1155) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3003 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1022) (-1134) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3004 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1026) (-1106) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3005 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1029) (-1092) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3006 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1036) (-1071) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3007 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord56) (1044) (-1057) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3008 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord57) (42) (-42) (1) (-575) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3009 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord57) (44) (-63) ((4/441)) ((1150/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3010 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord57) (63) (-44) ((441/4)) ((12075/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3011 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (6) (1057) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3012 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (14) (1071) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3013 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (21) (1092) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3014 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (24) (1106) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3015 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (28) (1134) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3016 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (30) (1155) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3017 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (33) (1204) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3018 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (35) (1260) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3019 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (36) (1302) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3020 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (38) (1449) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3021 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (39) (1596) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3022 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (40) (1890) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3023 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (41) (2772) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3024 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (43) (-756) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3025 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (44) (126) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3026 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (45) (420) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3027 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (46) (567) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3028 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (48) (714) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3029 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (49) (756) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3030 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (51) (812) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3031 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (54) (861) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3032 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (56) (882) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3033 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (60) (910) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3034 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (63) (924) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3035 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (70) (945) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3036 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (78) (959) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3037 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (84) (966) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3038 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (91) (972) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3039 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (105) (980) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3040 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (126) (987) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3041 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (140) (990) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3042 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (168) (994) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3043 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (189) (996) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3044 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (238) (999) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3045 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (294) (1001) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3046 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (336) (1002) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3047 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (483) (1004) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3048 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (630) (1005) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3049 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord58) (924) (1006) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3050 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord59) (7) (-1044) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3051 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord59) (21) (-1036) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3052 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord59) (42) (-1029) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3053 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord59) (56) (-1026) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3054 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord59) (84) (-1022) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3055 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord59) (105) (-1020) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3056 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord59) (154) (-1017) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3057 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord59) (210) (-1015) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3058 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord59) (252) (-1014) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3059 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord59) (399) (-1012) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3060 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord59) (546) (-1011) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3061 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord59) (840) (-1010) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3062 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord60) (756) (1007) (1764) (1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3063 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord61) (672) (-1009) (1764) (1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3064 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord62) (0) (532) (225) (-150) (1) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3065 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord62) (350) (534) ((1225/9)) ((-350/3)) (1) ((0,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource3066 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord62) (840) (540) (49) (-70) (1) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3067 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (0) (1092) (25) (-25) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3068 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (70) (1095) ((196/9)) ((-70/3)) (1) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3069 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (150) (1099) ((900/49)) ((-150/7)) (1) ((2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3070 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (168) (1100) ((441/25)) (-21) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3071 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (315) (1110) ((49/4)) ((-35/2)) (1) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3072 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (350) (1113) ((100/9)) ((-50/3)) (1) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3073 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (420) (1120) (9) (-15) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3074 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (462) (1125) ((196/25)) (-14) (1) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3075 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (525) (1134) ((25/4)) ((-25/2)) (1) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3076 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (560) (1140) ((49/9)) ((-35/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3077 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (600) (1148) ((225/49)) ((-75/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3078 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (609) (1150) ((441/100)) ((-21/2)) (1) ((-2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3079 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (630) (1155) (4) (-10) (1) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3080 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (700) (1176) ((25/9)) ((-25/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3081 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (735) (1190) ((9/4)) ((-15/2)) (1) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3082 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (750) (1197) ((100/49)) ((-50/7)) (1) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3083 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (756) (1200) ((49/25)) (-7) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3084 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (798) (1225) ((36/25)) (-6) (1) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3085 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (805) (1230) ((49/36)) ((-35/6)) (1) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3086 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (825) (1246) ((225/196)) ((-75/14)) (1) ((-2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3087 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (840) (1260) (1) (-5) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3088 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (854) (1275) ((196/225)) ((-14/3)) (1) ((2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3089 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (870) (1295) ((36/49)) ((-30/7)) (1) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3090 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (875) (1302) ((25/36)) ((-25/6)) (1) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3091 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (900) (1344) ((25/49)) ((-25/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3092 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (903) (1350) ((49/100)) ((-7/2)) (1) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3093 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (910) (1365) ((4/9)) ((-10/3)) (1) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3094 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (924) (1400) ((9/25)) (-3) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3095 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (945) (1470) ((1/4)) ((-5/2)) (1) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3096 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (950) (1491) ((100/441)) ((-50/21)) (1) ((2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3097 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (952) (1500) ((49/225)) ((-7/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3098 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (960) (1540) ((9/49)) ((-15/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3099 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (966) (1575) ((4/25)) (-2) (1) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3100 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (975) (1638) ((25/196)) ((-25/14)) (1) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3101 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (980) (1680) ((1/9)) ((-5/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3102 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (987) (1750) ((9/100)) ((-3/2)) (1) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3103 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (990) (1785) ((4/49)) ((-10/7)) (1) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3104 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1000) (1932) ((25/441)) ((-25/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3105 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1001) (1950) ((49/900)) ((-7/6)) (1) ((-2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3106 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1005) (2030) ((9/196)) ((-15/14)) (1) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3107 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1008) (2100) ((1/25)) (-1) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3108 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1014) (2275) ((36/1225)) ((-6/7)) (1) ((2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3109 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1015) (2310) ((1/36)) ((-5/6)) (1) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3110 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1020) (2520) ((1/49)) ((-5/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3111 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1022) (2625) ((4/225)) ((-2/3)) (1) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3112 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1025) (2814) ((25/1764)) ((-25/42)) (1) ((-2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3113 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1029) (3150) ((1/100)) ((-1/2)) (1) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3114 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1030) (3255) ((4/441)) ((-10/21)) (1) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3115 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1032) (3500) ((9/1225)) ((-3/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3116 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1035) (3990) ((1/196)) ((-5/14)) (1) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3117 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1036) (4200) ((1/225)) ((-1/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3118 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1038) (4725) ((4/1225)) ((-2/7)) (1) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3119 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1040) (5460) ((1/441)) ((-5/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3120 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1041) (5950) ((9/4900)) ((-3/14)) (1) ((-2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3121 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1043) (7350) ((1/900)) ((-1/6)) (1) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3122 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1044) (8400) ((1/1225)) ((-1/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3123 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1045) (9870) ((1/1764)) ((-5/42)) (1) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3124 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1046) (12075) ((4/11025)) ((-2/21)) (1) ((2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3125 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1047) (15750) ((1/4900)) ((-1/14)) (1) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3126 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1048) (23100) ((1/11025)) ((-1/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3127 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord63) (1049) (45150) ((1/44100)) ((-1/42)) (1) ((-2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3128 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (0) (-1008) (25) (-25) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3129 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (70) (-1005) ((196/9)) ((-70/3)) (1) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3130 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (150) (-1001) ((900/49)) ((-150/7)) (1) ((2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3131 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (168) (-1000) ((441/25)) (-21) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3132 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (315) (-990) ((49/4)) ((-35/2)) (1) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3133 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (350) (-987) ((100/9)) ((-50/3)) (1) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3134 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (420) (-980) (9) (-15) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3135 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (462) (-975) ((196/25)) (-14) (1) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3136 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (525) (-966) ((25/4)) ((-25/2)) (1) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3137 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (560) (-960) ((49/9)) ((-35/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3138 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (600) (-952) ((225/49)) ((-75/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3139 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (609) (-950) ((441/100)) ((-21/2)) (1) ((-2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3140 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (630) (-945) (4) (-10) (1) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3141 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (700) (-924) ((25/9)) ((-25/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3142 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (735) (-910) ((9/4)) ((-15/2)) (1) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3143 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (750) (-903) ((100/49)) ((-50/7)) (1) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3144 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (756) (-900) ((49/25)) (-7) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3145 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (798) (-875) ((36/25)) (-6) (1) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3146 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (805) (-870) ((49/36)) ((-35/6)) (1) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3147 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (825) (-854) ((225/196)) ((-75/14)) (1) ((-2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3148 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (840) (-840) (1) (-5) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3149 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (854) (-825) ((196/225)) ((-14/3)) (1) ((2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3150 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (870) (-805) ((36/49)) ((-30/7)) (1) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3151 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (875) (-798) ((25/36)) ((-25/6)) (1) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3152 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (900) (-756) ((25/49)) ((-25/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3153 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (903) (-750) ((49/100)) ((-7/2)) (1) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3154 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (910) (-735) ((4/9)) ((-10/3)) (1) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3155 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (924) (-700) ((9/25)) (-3) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3156 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (945) (-630) ((1/4)) ((-5/2)) (1) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3157 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (950) (-609) ((100/441)) ((-50/21)) (1) ((2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3158 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (952) (-600) ((49/225)) ((-7/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3159 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (960) (-560) ((9/49)) ((-15/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3160 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (966) (-525) ((4/25)) (-2) (1) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3161 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (975) (-462) ((25/196)) ((-25/14)) (1) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3162 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (980) (-420) ((1/9)) ((-5/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3163 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (987) (-350) ((9/100)) ((-3/2)) (1) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3164 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (990) (-315) ((4/49)) ((-10/7)) (1) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3165 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1000) (-168) ((25/441)) ((-25/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3166 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1001) (-150) ((49/900)) ((-7/6)) (1) ((-2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3167 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1005) (-70) ((9/196)) ((-15/14)) (1) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3168 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1008) (0) ((1/25)) (-1) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3169 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1014) (175) ((36/1225)) ((-6/7)) (1) ((2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3170 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1015) (210) ((1/36)) ((-5/6)) (1) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3171 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1020) (420) ((1/49)) ((-5/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3172 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1022) (525) ((4/225)) ((-2/3)) (1) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3173 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1025) (714) ((25/1764)) ((-25/42)) (1) ((-2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3174 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1029) (1050) ((1/100)) ((-1/2)) (1) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3175 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1030) (1155) ((4/441)) ((-10/21)) (1) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3176 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1032) (1400) ((9/1225)) ((-3/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3177 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1035) (1890) ((1/196)) ((-5/14)) (1) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3178 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1036) (2100) ((1/225)) ((-1/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3179 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1038) (2625) ((4/1225)) ((-2/7)) (1) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3180 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1040) (3360) ((1/441)) ((-5/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3181 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1041) (3850) ((9/4900)) ((-3/14)) (1) ((-2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3182 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1043) (5250) ((1/900)) ((-1/6)) (1) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3183 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1044) (6300) ((1/1225)) ((-1/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3184 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1045) (7770) ((1/1764)) ((-5/42)) (1) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3185 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1046) (9975) ((4/11025)) ((-2/21)) (1) ((2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3186 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1047) (13650) ((1/4900)) ((-1/14)) (1) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3187 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1048) (21000) ((1/11025)) ((-1/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3188 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord64) (1049) (43050) ((1/44100)) ((-1/42)) (1) ((-2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3189 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord65) (630) (-80) (441) (-1365) (1) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3190 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord65) (875) (-78) ((1225/36)) ((-2275/6)) (1) ((-2,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource3191 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord65) (900) (-77) ((900/49)) ((-1950/7)) (1) ((2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3192 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord65) (924) (-75) ((196/25)) (-182) (1) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3193 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord65) (945) (-70) ((9/4)) ((-195/2)) (1) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3194 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord65) (966) (0) ((1/25)) (-13) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3195 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord65) (969) (1050) ((1/4900)) ((-13/14)) (1) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3196 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord65) (970) (-420) ((1/441)) ((65/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3197 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord65) (972) (-175) ((36/1225)) ((78/7)) (1) ((2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3198 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord65) (973) (-150) ((49/900)) ((91/6)) (1) ((-2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3199 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord65) (975) (-126) ((25/196)) ((325/14)) (1) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3200 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord65) (980) (-105) ((4/9)) ((130/3)) (1) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3201 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord66) (420) (-45) (196) (-1610) (1) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3202 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord66) (525) (-42) ((25/4)) ((-575/2)) (1) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3203 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord66) (540) (-35) ((36/49)) ((-690/7)) (1) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3204 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord66) (546) (0) ((1/25)) (-23) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3205 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord66) (548) (-525) ((4/11025)) ((46/21)) (1) ((2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3206 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord66) (550) (-84) ((25/441)) ((575/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3207 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord66) (567) (-50) ((441/100)) ((483/2)) (1) ((-2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3208 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (0) (546) (25) (-50) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3209 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (84) (550) ((441/25)) (-42) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3210 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (210) (560) (9) (-30) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3211 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (280) (570) ((49/9)) ((-70/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3212 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (300) (574) ((225/49)) ((-150/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3213 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (350) (588) ((25/9)) ((-50/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3214 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (378) (600) ((49/25)) (-14) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3215 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (420) (630) (1) (-10) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3216 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (450) (672) ((25/49)) ((-50/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3217 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (462) (700) ((9/25)) (-6) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3218 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (476) (750) ((49/225)) ((-14/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3219 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (480) (770) ((9/49)) ((-30/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3220 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (490) (840) ((1/9)) ((-10/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3221 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (500) (966) ((25/441)) ((-50/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3222 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (504) (1050) ((1/25)) (-2) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3223 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (510) (1260) ((1/49)) ((-10/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3224 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (516) (1750) ((9/1225)) ((-6/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3225 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (518) (2100) ((1/225)) ((-2/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3226 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (520) (2730) ((1/441)) ((-10/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3227 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (522) (4200) ((1/1225)) ((-2/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3228 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (524) (11550) ((1/11025)) ((-2/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3229 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (526) (-10500) ((1/11025)) ((2/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3230 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (528) (-3150) ((1/1225)) ((2/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3231 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (530) (-1680) ((1/441)) ((10/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3232 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (532) (-1050) ((1/225)) ((2/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3233 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (534) (-700) ((9/1225)) ((6/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3234 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (540) (-210) ((1/49)) ((10/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3235 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (546) (0) ((1/25)) (2) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3236 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (550) (84) ((25/441)) ((50/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3237 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (560) (210) ((1/9)) ((10/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3238 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (570) (280) ((9/49)) ((30/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3239 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (574) (300) ((49/225)) ((14/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3240 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (588) (350) ((9/25)) (6) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3241 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (600) (378) ((25/49)) ((50/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3242 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (630) (420) (1) (10) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3243 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (672) (450) ((49/25)) (14) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3244 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (700) (462) ((25/9)) ((50/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3245 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (750) (476) ((225/49)) ((150/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3246 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (770) (480) ((49/9)) ((70/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3247 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (840) (490) (9) (30) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3248 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord67) (966) (500) ((441/25)) (42) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3249 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord68) (0) (39) (4900) (-9450) (1) ((2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource3250 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord68) (490) (40) (49) (-945) (1) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3251 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord68) (525) (42) ((25/4)) ((-675/2)) (1) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3252 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord68) (539) (50) ((49/100)) ((-189/2)) (1) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3253 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord68) (544) (175) ((4/1225)) ((-54/7)) (1) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3254 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord68) (545) (-70) ((1/196)) ((135/14)) (1) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3255 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord68) (546) (0) ((1/25)) (27) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3256 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord68) (550) (28) ((25/49)) ((675/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3257 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord68) (560) (35) (4) (270) (1) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3258 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (0) (-504) (25) (-50) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3259 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (84) (-500) ((441/25)) (-42) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3260 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (210) (-490) (9) (-30) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3261 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (280) (-480) ((49/9)) ((-70/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3262 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (300) (-476) ((225/49)) ((-150/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3263 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (350) (-462) ((25/9)) ((-50/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3264 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (378) (-450) ((49/25)) (-14) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3265 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (420) (-420) (1) (-10) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3266 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (450) (-378) ((25/49)) ((-50/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3267 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (462) (-350) ((9/25)) (-6) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3268 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (476) (-300) ((49/225)) ((-14/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3269 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (480) (-280) ((9/49)) ((-30/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3270 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (490) (-210) ((1/9)) ((-10/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3271 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (500) (-84) ((25/441)) ((-50/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3272 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (504) (0) ((1/25)) (-2) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3273 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (510) (210) ((1/49)) ((-10/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3274 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (516) (700) ((9/1225)) ((-6/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3275 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (518) (1050) ((1/225)) ((-2/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3276 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (520) (1680) ((1/441)) ((-10/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3277 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (522) (3150) ((1/1225)) ((-2/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3278 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (524) (10500) ((1/11025)) ((-2/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3279 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (526) (-11550) ((1/11025)) ((2/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3280 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (528) (-4200) ((1/1225)) ((2/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3281 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (530) (-2730) ((1/441)) ((10/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3282 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (532) (-2100) ((1/225)) ((2/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3283 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (534) (-1750) ((9/1225)) ((6/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3284 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (540) (-1260) ((1/49)) ((10/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3285 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (546) (-1050) ((1/25)) (2) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3286 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (550) (-966) ((25/441)) ((50/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3287 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (560) (-840) ((1/9)) ((10/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3288 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (570) (-770) ((9/49)) ((30/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3289 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (574) (-750) ((49/225)) ((14/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3290 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (588) (-700) ((9/25)) (6) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3291 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (600) (-672) ((25/49)) ((50/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3292 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (630) (-630) (1) (10) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3293 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (672) (-600) ((49/25)) (14) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3294 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (700) (-588) ((25/9)) ((50/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3295 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (750) (-574) ((225/49)) ((150/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3296 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (770) (-570) ((49/9)) ((70/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3297 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (840) (-560) (9) (30) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3298 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord69) (966) (-550) ((441/25)) (42) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3299 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (0) (-84) (25) (-300) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3300 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (63) (-75) ((49/25)) (-84) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3301 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (70) (-70) (1) (-60) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3302 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (75) (-63) ((25/49)) ((-300/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3303 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (84) (0) ((1/25)) (-12) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3304 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (85) (35) ((1/49)) ((-60/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3305 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (87) (525) ((1/1225)) ((-12/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3306 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (88) (-700) ((1/1225)) ((12/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3307 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (90) (-210) ((1/49)) ((60/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3308 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (91) (-175) ((1/25)) (12) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3309 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (100) (-112) ((25/49)) ((300/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3310 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (105) (-105) (1) (60) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3311 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (112) (-100) ((49/25)) (84) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3312 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (175) (-91) (25) (300) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3313 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (210) (-90) (49) (420) (1) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3314 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord70) (700) (-88) (1225) (2100) (1) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource3315 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord71) (0) (-42) (25) (-600) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3316 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord71) (35) (-35) (1) (-120) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3317 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord71) (42) (0) ((1/25)) (-24) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3318 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord71) (44) (-350) ((1/1225)) ((24/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3319 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord71) (45) (-105) ((1/49)) ((120/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3320 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord71) (50) (-56) ((25/49)) ((600/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3321 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord71) (56) (-50) ((49/25)) (168) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3322 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord71) (105) (-45) (49) (840) (1) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3323 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord71) (350) (-44) (1225) (4200) (1) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource3324 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (1) (-43050) ((1/44100)) ((1/42)) (1) ((-2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3325 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (2) (-21000) ((1/11025)) ((1/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3326 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (3) (-13650) ((1/4900)) ((1/14)) (1) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3327 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (4) (-9975) ((4/11025)) ((2/21)) (1) ((2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3328 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (5) (-7770) ((1/1764)) ((5/42)) (1) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3329 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (6) (-6300) ((1/1225)) ((1/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3330 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (7) (-5250) ((1/900)) ((1/6)) (1) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3331 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (9) (-3850) ((9/4900)) ((3/14)) (1) ((-2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3332 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (10) (-3360) ((1/441)) ((5/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3333 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (12) (-2625) ((4/1225)) ((2/7)) (1) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3334 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (14) (-2100) ((1/225)) ((1/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3335 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (15) (-1890) ((1/196)) ((5/14)) (1) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3336 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (18) (-1400) ((9/1225)) ((3/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3337 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (20) (-1155) ((4/441)) ((10/21)) (1) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3338 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (21) (-1050) ((1/100)) ((1/2)) (1) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3339 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (25) (-714) ((25/1764)) ((25/42)) (1) ((-2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3340 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (28) (-525) ((4/225)) ((2/3)) (1) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3341 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (30) (-420) ((1/49)) ((5/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3342 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (35) (-210) ((1/36)) ((5/6)) (1) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3343 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (36) (-175) ((36/1225)) ((6/7)) (1) ((2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3344 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (42) (0) ((1/25)) (1) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3345 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (45) (70) ((9/196)) ((15/14)) (1) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3346 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (49) (150) ((49/900)) ((7/6)) (1) ((-2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3347 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (50) (168) ((25/441)) ((25/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3348 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (60) (315) ((4/49)) ((10/7)) (1) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3349 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (63) (350) ((9/100)) ((3/2)) (1) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3350 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (70) (420) ((1/9)) ((5/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3351 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (75) (462) ((25/196)) ((25/14)) (1) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3352 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (84) (525) ((4/25)) (2) (1) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3353 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (90) (560) ((9/49)) ((15/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3354 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (98) (600) ((49/225)) ((7/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3355 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (100) (609) ((100/441)) ((50/21)) (1) ((2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3356 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (105) (630) ((1/4)) ((5/2)) (1) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3357 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (126) (700) ((9/25)) (3) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3358 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (140) (735) ((4/9)) ((10/3)) (1) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3359 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (147) (750) ((49/100)) ((7/2)) (1) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3360 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (150) (756) ((25/49)) ((25/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3361 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (175) (798) ((25/36)) ((25/6)) (1) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3362 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (180) (805) ((36/49)) ((30/7)) (1) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3363 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (196) (825) ((196/225)) ((14/3)) (1) ((2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3364 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (210) (840) (1) (5) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3365 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (225) (854) ((225/196)) ((75/14)) (1) ((-2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3366 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (245) (870) ((49/36)) ((35/6)) (1) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3367 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (252) (875) ((36/25)) (6) (1) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3368 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (294) (900) ((49/25)) (7) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3369 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (300) (903) ((100/49)) ((50/7)) (1) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3370 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (315) (910) ((9/4)) ((15/2)) (1) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3371 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (350) (924) ((25/9)) ((25/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3372 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (420) (945) (4) (10) (1) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3373 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (441) (950) ((441/100)) ((21/2)) (1) ((-2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3374 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (450) (952) ((225/49)) ((75/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3375 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (490) (960) ((49/9)) ((35/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3376 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (525) (966) ((25/4)) ((25/2)) (1) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3377 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (588) (975) ((196/25)) (14) (1) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3378 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (630) (980) (9) (15) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3379 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (700) (987) ((100/9)) ((50/3)) (1) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3380 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (735) (990) ((49/4)) ((35/2)) (1) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3381 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (882) (1000) ((441/25)) (21) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3382 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (900) (1001) ((900/49)) ((150/7)) (1) ((2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3383 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord72) (980) (1005) ((196/9)) ((70/3)) (1) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3384 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord73) (0) (42) (25) (-650) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3385 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord73) (40) (210) ((1/441)) ((-130/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3386 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord73) (42) (0) ((1/25)) (26) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3387 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord73) (210) (40) (441) (2730) (1) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3388 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord74) (0) (-42) (25) (650) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3389 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (1) (-45150) ((1/44100)) ((1/42)) (1) ((-2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3390 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (2) (-23100) ((1/11025)) ((1/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3391 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (3) (-15750) ((1/4900)) ((1/14)) (1) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3392 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (4) (-12075) ((4/11025)) ((2/21)) (1) ((2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3393 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (5) (-9870) ((1/1764)) ((5/42)) (1) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3394 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (6) (-8400) ((1/1225)) ((1/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3395 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (7) (-7350) ((1/900)) ((1/6)) (1) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3396 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (9) (-5950) ((9/4900)) ((3/14)) (1) ((-2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3397 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (10) (-5460) ((1/441)) ((5/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3398 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (12) (-4725) ((4/1225)) ((2/7)) (1) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3399 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (14) (-4200) ((1/225)) ((1/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3400 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (15) (-3990) ((1/196)) ((5/14)) (1) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3401 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (18) (-3500) ((9/1225)) ((3/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3402 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (20) (-3255) ((4/441)) ((10/21)) (1) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3403 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (21) (-3150) ((1/100)) ((1/2)) (1) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3404 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (25) (-2814) ((25/1764)) ((25/42)) (1) ((-2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3405 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (28) (-2625) ((4/225)) ((2/3)) (1) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3406 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (30) (-2520) ((1/49)) ((5/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3407 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (35) (-2310) ((1/36)) ((5/6)) (1) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3408 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (36) (-2275) ((36/1225)) ((6/7)) (1) ((2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3409 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (42) (-2100) ((1/25)) (1) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3410 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (45) (-2030) ((9/196)) ((15/14)) (1) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3411 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (49) (-1950) ((49/900)) ((7/6)) (1) ((-2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3412 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (50) (-1932) ((25/441)) ((25/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3413 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (60) (-1785) ((4/49)) ((10/7)) (1) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3414 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (63) (-1750) ((9/100)) ((3/2)) (1) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3415 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (70) (-1680) ((1/9)) ((5/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3416 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (75) (-1638) ((25/196)) ((25/14)) (1) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3417 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (84) (-1575) ((4/25)) (2) (1) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3418 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (90) (-1540) ((9/49)) ((15/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3419 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (98) (-1500) ((49/225)) ((7/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3420 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (100) (-1491) ((100/441)) ((50/21)) (1) ((2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3421 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (105) (-1470) ((1/4)) ((5/2)) (1) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3422 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (126) (-1400) ((9/25)) (3) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3423 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (140) (-1365) ((4/9)) ((10/3)) (1) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3424 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (147) (-1350) ((49/100)) ((7/2)) (1) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3425 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (150) (-1344) ((25/49)) ((25/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3426 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (175) (-1302) ((25/36)) ((25/6)) (1) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3427 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (180) (-1295) ((36/49)) ((30/7)) (1) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3428 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (196) (-1275) ((196/225)) ((14/3)) (1) ((2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3429 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (210) (-1260) (1) (5) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3430 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (225) (-1246) ((225/196)) ((75/14)) (1) ((-2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3431 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (245) (-1230) ((49/36)) ((35/6)) (1) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3432 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (252) (-1225) ((36/25)) (6) (1) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3433 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (294) (-1200) ((49/25)) (7) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3434 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (300) (-1197) ((100/49)) ((50/7)) (1) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3435 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (315) (-1190) ((9/4)) ((15/2)) (1) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3436 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (350) (-1176) ((25/9)) ((25/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3437 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (420) (-1155) (4) (10) (1) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3438 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (441) (-1150) ((441/100)) ((21/2)) (1) ((-2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3439 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (450) (-1148) ((225/49)) ((75/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3440 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (490) (-1140) ((49/9)) ((35/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3441 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (525) (-1134) ((25/4)) ((25/2)) (1) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3442 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (588) (-1125) ((196/25)) (14) (1) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3443 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (630) (-1120) (9) (15) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3444 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (700) (-1113) ((100/9)) ((50/3)) (1) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3445 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (735) (-1110) ((49/4)) ((35/2)) (1) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3446 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (882) (-1100) ((441/25)) (21) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3447 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (900) (-1099) ((900/49)) ((150/7)) (1) ((2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3448 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord75) (980) (-1095) ((196/9)) ((70/3)) (1) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3449 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord76) (0) (42) (25) (600) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3450 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord77) (0) (-28) (225) (2850) (1) ((0,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3451 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord78) (0) (-84) (25) (325) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3452 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord79) (0) (84) (25) (300) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3453 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord79) (35) (85) (49) (420) (1) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3454 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord79) (525) (87) (1225) (2100) (1) ((0,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource3455 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord80) (0) (504) (25) (50) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3456 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord80) (210) (510) (49) (70) (1) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3457 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord80) (700) (516) ((1225/9)) ((350/3)) (1) ((0,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource3458 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord81) (0) (1008) (25) (25) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3459 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord81) (175) (1014) ((1225/36)) ((175/6)) (1) ((-2,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource3460 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord81) (210) (1015) (36) (30) (1) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3461 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord81) (420) (1020) (49) (35) (1) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3462 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord81) (525) (1022) ((225/4)) ((75/2)) (1) ((-2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3463 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord81) (714) (1025) ((1764/25)) (42) (1) ((2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3464 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord82) (0) (-1092) (25) (25) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3465 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord82) (175) (-1086) ((1225/36)) ((175/6)) (1) ((-2,-2,2,2))
    (by decide +kernel)))

compact_certificate def auxSource3466 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord82) (210) (-1085) (36) (30) (1) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3467 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord82) (420) (-1080) (49) (35) (1) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3468 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord82) (525) (-1078) ((225/4)) ((75/2)) (1) ((-2,2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource3469 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord82) (714) (-1075) ((1764/25)) (42) (1) ((2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource3470 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord83) (0) (-81) (4900) (4550) (1) ((2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource3471 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord84) (210) (-1090) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3472 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord84) (504) (-1089) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3473 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord84) (651) (-1088) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3474 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord84) (798) (-1086) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3475 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord84) (840) (-1085) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3476 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord84) (896) (-1083) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3477 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord84) (945) (-1080) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3478 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord84) (966) (-1078) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3479 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord84) (994) (-1074) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3480 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord84) (1008) (-1071) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3481 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord84) (1029) (-1064) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3482 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord84) (1043) (-1056) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3483 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (126) (1094) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3484 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (420) (1095) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3485 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (567) (1096) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3486 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (714) (1098) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3487 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (756) (1099) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3488 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (812) (1101) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3489 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (861) (1104) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3490 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (882) (1106) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3491 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (910) (1110) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3492 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (924) (1113) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3493 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (945) (1120) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3494 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (959) (1128) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3495 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (966) (1134) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3496 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (972) (1141) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3497 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (980) (1155) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3498 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (987) (1176) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3499 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (990) (1190) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3500 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (994) (1218) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3501 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (996) (1239) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3502 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (999) (1288) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3503 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1001) (1344) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3504 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1002) (1386) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3505 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1004) (1533) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3506 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1005) (1680) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3507 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1006) (1974) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3508 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1007) (2856) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3509 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1009) (-672) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3510 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1010) (210) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3511 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1011) (504) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3512 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1012) (651) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3513 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1014) (798) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3514 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1015) (840) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3515 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1017) (896) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3516 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1020) (945) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3517 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1022) (966) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3518 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1026) (994) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3519 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1029) (1008) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3520 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1036) (1029) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3521 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord85) (1044) (1043) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3522 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord86) (35) (-40) ((49/4)) ((-4725/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3523 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord86) (40) (-35) ((4/49)) ((-1350/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3524 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord86) (42) (-42) (1) (675) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3525 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (6) (-1043) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3526 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (14) (-1029) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3527 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (21) (-1008) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3528 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (24) (-994) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3529 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (28) (-966) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3530 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (30) (-945) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3531 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (33) (-896) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3532 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (35) (-840) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3533 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (36) (-798) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3534 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (38) (-651) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3535 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (39) (-504) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3536 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (40) (-210) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3537 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (41) (672) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3538 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (43) (-2856) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3539 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (44) (-1974) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3540 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (45) (-1680) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3541 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (46) (-1533) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3542 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (48) (-1386) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3543 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (49) (-1344) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3544 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (51) (-1288) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3545 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (54) (-1239) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3546 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (56) (-1218) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3547 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (60) (-1190) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3548 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (63) (-1176) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3549 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (70) (-1155) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3550 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (78) (-1141) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3551 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (84) (-1134) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3552 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (91) (-1128) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3553 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (105) (-1120) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3554 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (126) (-1113) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3555 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (140) (-1110) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3556 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (168) (-1106) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3557 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (189) (-1104) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3558 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (238) (-1101) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3559 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (294) (-1099) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3560 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (336) (-1098) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3561 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (483) (-1096) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3562 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (630) (-1095) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3563 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord87) (924) (-1094) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3564 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord88) (7) (1056) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3565 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord88) (21) (1064) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3566 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord88) (42) (1071) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3567 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord88) (56) (1074) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3568 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord88) (84) (1078) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3569 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord88) (105) (1080) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3570 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord88) (154) (1083) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3571 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord88) (210) (1085) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3572 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord88) (252) (1086) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3573 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord88) (399) (1088) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3574 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord88) (546) (1089) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3575 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord88) (840) (1090) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3576 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord89) (756) (-1093) (1764) (1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3577 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord90) (672) (1091) (1764) (1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3578 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord91) (714) (-1132) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3579 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord91) (1008) (-1131) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3580 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord92) (540) (-40) (9) (-2100) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3581 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord92) (543) (-39) (1) (-700) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3582 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord92) (544) (-36) ((1/9)) ((-700/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3583 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord92) (545) (-45) ((1/9)) ((700/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3584 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord92) (546) (-42) (1) (700) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3585 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord92) (549) (-41) (9) (2100) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3586 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (105) (-1130) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3587 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (252) (-1128) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3588 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (294) (-1127) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3589 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (350) (-1125) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3590 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (399) (-1122) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3591 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (420) (-1120) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3592 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (448) (-1116) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3593 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (462) (-1113) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3594 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (483) (-1106) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3595 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (497) (-1098) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3596 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (504) (-1092) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3597 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (510) (-1085) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3598 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (518) (-1071) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3599 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (525) (-1050) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3600 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (528) (-1036) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3601 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (532) (-1008) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3602 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (534) (-987) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3603 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (537) (-938) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3604 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (539) (-882) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3605 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (540) (-840) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3606 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (542) (-693) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3607 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (543) (-546) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3608 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (544) (-252) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3609 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (545) (630) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3610 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (547) (-2898) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3611 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (548) (-2016) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3612 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (549) (-1722) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3613 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (550) (-1575) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3614 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (552) (-1428) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3615 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (553) (-1386) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3616 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (555) (-1330) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3617 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (558) (-1281) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3618 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (560) (-1260) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3619 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (564) (-1232) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3620 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (567) (-1218) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3621 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (574) (-1197) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3622 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (582) (-1183) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3623 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (588) (-1176) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3624 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (595) (-1170) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3625 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (609) (-1162) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3626 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (630) (-1155) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3627 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (644) (-1152) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3628 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (672) (-1148) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3629 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (693) (-1146) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3630 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (742) (-1143) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3631 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (798) (-1141) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3632 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (840) (-1140) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3633 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord93) (987) (-1138) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3634 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord94) (546) (42) (1) (650) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3635 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (63) (1138) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3636 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (210) (1140) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3637 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (252) (1141) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3638 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (308) (1143) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3639 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (357) (1146) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3640 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (378) (1148) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3641 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (406) (1152) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3642 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (420) (1155) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3643 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (441) (1162) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3644 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (455) (1170) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3645 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (462) (1176) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3646 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (468) (1183) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3647 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (476) (1197) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3648 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (483) (1218) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3649 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (486) (1232) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3650 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (490) (1260) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3651 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (492) (1281) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3652 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (495) (1330) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3653 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (497) (1386) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3654 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (498) (1428) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3655 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (500) (1575) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3656 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (501) (1722) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3657 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (502) (2016) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3658 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (503) (2898) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3659 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (505) (-630) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3660 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (506) (252) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3661 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (507) (546) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3662 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (508) (693) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3663 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (510) (840) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3664 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (511) (882) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3665 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (513) (938) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3666 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (516) (987) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3667 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (518) (1008) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3668 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (522) (1036) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3669 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (525) (1050) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3670 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (532) (1071) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3671 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (540) (1085) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3672 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (546) (1092) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3673 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (553) (1098) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3674 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (567) (1106) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3675 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (588) (1113) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3676 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (602) (1116) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3677 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (630) (1120) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3678 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (651) (1122) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3679 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (700) (1125) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3680 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (756) (1127) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3681 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (798) (1128) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3682 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord95) (945) (1130) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3683 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord96) (39) (-42) ((1/196)) ((1025/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3684 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord96) (42) (-28) (9) (3075) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3685 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord97) (30) (-80) (9) (-1050) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3686 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord97) (36) (-78) (1) (-350) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3687 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord97) (38) (-72) ((1/9)) ((-350/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3688 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord97) (40) (-90) ((1/9)) ((350/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3689 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord97) (42) (-84) (1) (350) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3690 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord97) (48) (-82) (9) (1050) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3691 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord98) (35) (90) ((49/36)) ((-2275/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3692 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord98) (36) (91) ((36/49)) ((-1950/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3693 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord98) (39) (42) ((1/196)) ((325/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3694 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord98) (42) (84) (1) (325) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3695 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord98) (84) (87) (196) (4550) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3696 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord99) (84) (-1137) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3697 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord99) (378) (-1136) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3698 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord100) (543) (-21) ((1/49)) ((-1100/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3699 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord100) (546) (-28) (9) (3300) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3700 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord101) (504) (-81) (196) (-5250) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3701 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord101) (543) (-42) ((1/196)) ((-375/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3702 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord101) (544) (-91) ((4/49)) ((750/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3703 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord101) (546) (-84) (1) (375) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3704 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord101) (553) (-82) ((49/4)) ((2625/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3705 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord102) (534) (88) (9) (-1050) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3706 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord102) (540) (90) (1) (-350) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3707 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord102) (542) (96) ((1/9)) ((-350/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3708 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord102) (544) (78) ((1/9)) ((350/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3709 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord102) (546) (84) (1) (350) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3710 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord102) (552) (86) (9) (1050) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3711 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (0) (1575) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3712 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (21) (1582) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3713 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (35) (1590) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3714 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (42) (1596) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3715 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (48) (1603) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3716 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (56) (1617) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3717 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (63) (1638) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3718 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (66) (1652) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3719 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (70) (1680) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3720 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (72) (1701) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3721 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (75) (1750) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3722 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (77) (1806) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3723 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (78) (1848) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3724 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (80) (1995) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3725 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (81) (2142) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3726 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (82) (2436) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3727 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (83) (3318) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3728 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (85) (-210) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3729 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (86) (672) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3730 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (87) (966) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3731 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (88) (1113) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3732 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (90) (1260) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3733 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (91) (1302) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3734 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (93) (1358) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3735 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (96) (1407) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3736 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (98) (1428) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3737 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (102) (1456) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3738 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (105) (1470) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3739 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (112) (1491) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3740 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (120) (1505) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3741 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (126) (1512) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3742 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (133) (1518) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3743 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (147) (1526) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3744 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (168) (1533) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3745 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (182) (1536) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3746 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (210) (1540) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3747 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (231) (1542) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3748 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (280) (1545) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3749 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (336) (1547) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3750 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (378) (1548) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3751 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (525) (1550) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3752 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (672) (1551) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3753 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord103) (966) (1552) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3754 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (0) (525) (4) (-150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3755 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (14) (532) (1) (-75) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3756 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (21) (546) ((1/4)) ((-75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3757 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (24) (567) ((4/49)) ((-150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3758 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (26) (616) ((1/49)) ((-75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3759 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (27) (714) ((1/196)) ((-75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3760 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (29) (322) ((1/196)) ((75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3761 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (30) (420) ((1/49)) ((75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3762 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (32) (469) ((4/49)) ((150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3763 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (35) (490) ((1/4)) ((75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3764 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (42) (504) (1) (75) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3765 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (56) (511) (4) (150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3766 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (77) (514) ((49/4)) ((525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3767 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (126) (516) (49) (525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3768 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord104) (224) (517) (196) (1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3769 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord105) (0) (-525) (4) (150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3770 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord105) (21) (-522) ((49/4)) ((525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3771 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord105) (70) (-520) (49) (525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3772 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord105) (168) (-519) (196) (1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3773 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord106) (0) (-1575) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3774 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord106) (14) (-1572) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3775 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord106) (42) (-1568) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3776 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord106) (63) (-1566) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3777 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord106) (112) (-1563) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3778 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord106) (168) (-1561) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3779 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord106) (210) (-1560) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3780 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord106) (357) (-1558) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3781 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord106) (504) (-1557) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3782 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord106) (798) (-1556) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3783 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (826) (533) (196) (-1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3784 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (924) (534) (49) (-525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3785 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (973) (536) ((49/4)) ((-525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3786 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (994) (539) (4) (-150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3787 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (1008) (546) (1) (-75) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3788 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (1015) (560) ((1/4)) ((-75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3789 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (1018) (581) ((4/49)) ((-150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3790 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (1020) (630) ((1/49)) ((-75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3791 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (1021) (728) ((1/196)) ((-75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3792 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (1023) (336) ((1/196)) ((75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3793 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (1024) (434) ((1/49)) ((75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3794 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (1026) (483) ((4/49)) ((150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3795 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (1029) (504) ((1/4)) ((75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3796 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord107) (1036) (518) (1) (75) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3797 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (84) (1598) (441) (-525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3798 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (378) (1599) (196) (-350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3799 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (525) (1600) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3800 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (672) (1602) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3801 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (714) (1603) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3802 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (770) (1605) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3803 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (819) (1608) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3804 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (840) (1610) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3805 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (868) (1614) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3806 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (882) (1617) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3807 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (903) (1624) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3808 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (917) (1632) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3809 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (924) (1638) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3810 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (930) (1645) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3811 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (938) (1659) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3812 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (945) (1680) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3813 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (948) (1694) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3814 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (952) (1722) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3815 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (954) (1743) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3816 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (957) (1792) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3817 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (959) (1848) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3818 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (960) (1890) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3819 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (962) (2037) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3820 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (963) (2184) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3821 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (964) (2478) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3822 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (965) (3360) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3823 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (967) (-168) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3824 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (968) (714) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3825 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (969) (1008) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3826 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (970) (1155) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3827 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (972) (1302) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3828 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (973) (1344) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3829 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (975) (1400) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3830 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (978) (1449) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3831 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (980) (1470) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3832 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (984) (1498) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3833 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (987) (1512) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3834 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (994) (1533) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3835 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (1002) (1547) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3836 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (1008) (1554) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3837 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (1015) (1560) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3838 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord108) (1029) (1568) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3839 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord109) (0) (525) (4) (150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3840 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord109) (21) (528) ((49/4)) ((525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3841 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord109) (70) (530) (49) (525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3842 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord109) (168) (531) (196) (1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3843 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord110) (0) (1575) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3844 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord110) (14) (1578) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3845 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord110) (42) (1582) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3846 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord110) (63) (1584) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3847 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord110) (112) (1587) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3848 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord110) (168) (1589) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3849 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord110) (210) (1590) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3850 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord110) (357) (1592) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3851 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord110) (504) (1593) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3852 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord110) (798) (1594) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3853 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord111) (630) (1595) (1764) (1050) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3854 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (105) (2020) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3855 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (252) (2022) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3856 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (294) (2023) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3857 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (350) (2025) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3858 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (399) (2028) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3859 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (420) (2030) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3860 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (448) (2034) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3861 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (462) (2037) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3862 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (483) (2044) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3863 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (497) (2052) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3864 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (504) (2058) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3865 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (510) (2065) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3866 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (518) (2079) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3867 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (525) (2100) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3868 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (528) (2114) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3869 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (532) (2142) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3870 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (534) (2163) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3871 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (537) (2212) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3872 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (539) (2268) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3873 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (540) (2310) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3874 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (542) (2457) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3875 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (543) (2604) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3876 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (544) (2898) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3877 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (545) (3780) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3878 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (547) (252) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3879 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (548) (1134) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3880 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (549) (1428) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3881 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (550) (1575) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3882 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (552) (1722) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3883 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (553) (1764) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3884 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (555) (1820) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3885 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (558) (1869) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3886 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (560) (1890) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3887 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (564) (1918) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3888 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (567) (1932) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3889 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (574) (1953) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3890 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (582) (1967) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3891 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (588) (1974) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3892 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (595) (1980) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3893 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (609) (1988) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3894 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (630) (1995) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3895 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (644) (1998) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3896 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (672) (2002) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3897 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (693) (2004) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3898 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (742) (2007) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3899 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (798) (2009) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3900 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (840) (2010) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3901 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord112) (987) (2012) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3902 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (315) (515) (441) (-2100) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3903 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (462) (516) (49) (-700) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3904 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (504) (518) (9) (-300) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3905 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (511) (519) ((49/9)) ((-700/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3906 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (531) (539) ((9/49)) ((-300/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3907 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (532) (546) ((1/9)) ((-100/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3908 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (534) (588) ((1/49)) ((-100/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3909 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (535) (735) ((1/441)) ((-100/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3910 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (536) (294) ((1/441)) ((100/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3911 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (537) (441) ((1/49)) ((100/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3912 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (539) (483) ((1/9)) ((100/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3913 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (540) (490) ((9/49)) ((300/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3914 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (546) (504) (1) (100) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3915 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (560) (510) ((49/9)) ((700/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3916 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (567) (511) (9) (300) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3917 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (609) (513) (49) (700) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3918 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord113) (756) (514) (441) (2100) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3919 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (6) (2107) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3920 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (14) (2121) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3921 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (21) (2142) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3922 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (24) (2156) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3923 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (28) (2184) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3924 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (30) (2205) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3925 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (33) (2254) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3926 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (35) (2310) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3927 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (36) (2352) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3928 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (38) (2499) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3929 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (39) (2646) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3930 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (40) (2940) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3931 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (41) (3822) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3932 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (43) (294) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3933 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (44) (1176) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3934 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (45) (1470) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3935 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (46) (1617) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3936 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (48) (1764) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3937 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (49) (1806) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3938 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (51) (1862) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3939 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (54) (1911) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3940 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (56) (1932) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3941 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (60) (1960) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3942 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (63) (1974) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3943 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (70) (1995) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3944 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (78) (2009) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3945 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (84) (2016) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3946 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (91) (2022) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3947 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (105) (2030) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3948 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (126) (2037) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3949 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (140) (2040) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3950 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (168) (2044) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3951 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (189) (2046) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3952 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (238) (2049) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3953 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (294) (2051) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3954 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (336) (2052) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3955 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (483) (2054) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3956 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (630) (2055) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3957 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord114) (924) (2056) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3958 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord115) (12) (1078) ((9/49)) ((-150/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3959 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord115) (14) (1092) ((1/9)) ((-50/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3960 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord115) (18) (1176) ((1/49)) ((-50/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3961 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord115) (20) (1470) ((1/441)) ((-50/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3962 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord115) (22) (588) ((1/441)) ((50/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3963 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord115) (24) (882) ((1/49)) ((50/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3964 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord115) (28) (966) ((1/9)) ((50/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3965 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord115) (30) (980) ((9/49)) ((150/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3966 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord115) (42) (1008) (1) (50) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3967 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord115) (70) (1020) ((49/9)) ((350/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3968 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord115) (84) (1022) (9) (150) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3969 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord115) (168) (1026) (49) (350) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3970 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord115) (462) (1028) (441) (1050) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3971 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord116) (28) (-1038) ((49/9)) ((350/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3972 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord116) (42) (-1036) (9) (150) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3973 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord116) (126) (-1032) (49) (350) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3974 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord116) (420) (-1030) (441) (1050) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3975 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord117) (7) (-2094) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3976 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord117) (21) (-2086) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3977 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord117) (42) (-2079) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3978 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord117) (56) (-2076) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3979 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord117) (84) (-2072) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3980 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord117) (105) (-2070) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3981 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord117) (154) (-2067) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3982 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord117) (210) (-2065) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource3983 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord117) (252) (-2064) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3984 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord117) (399) (-2062) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3985 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord117) (546) (-2061) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3986 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord117) (840) (-2060) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource3987 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (1) (-42000) ((1/44100)) ((1/42)) (1) ((-2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3988 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (2) (-19950) ((1/11025)) ((1/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3989 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (3) (-12600) ((1/4900)) ((1/14)) (1) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3990 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (4) (-8925) ((4/11025)) ((2/21)) (1) ((2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3991 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (5) (-6720) ((1/1764)) ((5/42)) (1) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3992 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (6) (-5250) ((1/1225)) ((1/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3993 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (7) (-4200) ((1/900)) ((1/6)) (1) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3994 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (9) (-2800) ((9/4900)) ((3/14)) (1) ((-2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3995 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (10) (-2310) ((1/441)) ((5/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3996 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (12) (-1575) ((4/1225)) ((2/7)) (1) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource3997 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (14) (-1050) ((1/225)) ((1/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource3998 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (15) (-840) ((1/196)) ((5/14)) (1) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource3999 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (18) (-350) ((9/1225)) ((3/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4000 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (20) (-105) ((4/441)) ((10/21)) (1) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4001 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (21) (0) ((1/100)) ((1/2)) (1) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4002 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (25) (336) ((25/1764)) ((25/42)) (1) ((-2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4003 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (28) (525) ((4/225)) ((2/3)) (1) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4004 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (30) (630) ((1/49)) ((5/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4005 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (35) (840) ((1/36)) ((5/6)) (1) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4006 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (36) (875) ((36/1225)) ((6/7)) (1) ((2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4007 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (42) (1050) ((1/25)) (1) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4008 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (45) (1120) ((9/196)) ((15/14)) (1) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4009 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (49) (1200) ((49/900)) ((7/6)) (1) ((-2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4010 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (50) (1218) ((25/441)) ((25/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4011 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (60) (1365) ((4/49)) ((10/7)) (1) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4012 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (63) (1400) ((9/100)) ((3/2)) (1) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4013 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (70) (1470) ((1/9)) ((5/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4014 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (75) (1512) ((25/196)) ((25/14)) (1) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4015 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (84) (1575) ((4/25)) (2) (1) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4016 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (90) (1610) ((9/49)) ((15/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4017 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (98) (1650) ((49/225)) ((7/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4018 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (100) (1659) ((100/441)) ((50/21)) (1) ((2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4019 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (105) (1680) ((1/4)) ((5/2)) (1) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4020 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (126) (1750) ((9/25)) (3) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4021 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (140) (1785) ((4/9)) ((10/3)) (1) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4022 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (147) (1800) ((49/100)) ((7/2)) (1) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4023 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (150) (1806) ((25/49)) ((25/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4024 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (175) (1848) ((25/36)) ((25/6)) (1) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4025 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (180) (1855) ((36/49)) ((30/7)) (1) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4026 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (196) (1875) ((196/225)) ((14/3)) (1) ((2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4027 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (210) (1890) (1) (5) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4028 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (225) (1904) ((225/196)) ((75/14)) (1) ((-2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4029 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (245) (1920) ((49/36)) ((35/6)) (1) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4030 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (252) (1925) ((36/25)) (6) (1) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4031 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (294) (1950) ((49/25)) (7) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4032 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (300) (1953) ((100/49)) ((50/7)) (1) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4033 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (315) (1960) ((9/4)) ((15/2)) (1) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4034 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (350) (1974) ((25/9)) ((25/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4035 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (420) (1995) (4) (10) (1) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4036 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (441) (2000) ((441/100)) ((21/2)) (1) ((-2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4037 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (450) (2002) ((225/49)) ((75/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4038 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (490) (2010) ((49/9)) ((35/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4039 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (525) (2016) ((25/4)) ((25/2)) (1) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4040 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (588) (2025) ((196/25)) (14) (1) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4041 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (630) (2030) (9) (15) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4042 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (700) (2037) ((100/9)) ((50/3)) (1) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4043 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (735) (2040) ((49/4)) ((35/2)) (1) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4044 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (882) (2050) ((441/25)) (21) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4045 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (900) (2051) ((900/49)) ((150/7)) (1) ((2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4046 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord118) (980) (2055) ((196/9)) ((70/3)) (1) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4047 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (1) (-46200) ((1/44100)) ((1/42)) (1) ((-2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4048 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (2) (-24150) ((1/11025)) ((1/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4049 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (3) (-16800) ((1/4900)) ((1/14)) (1) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4050 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (4) (-13125) ((4/11025)) ((2/21)) (1) ((2,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4051 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (5) (-10920) ((1/1764)) ((5/42)) (1) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4052 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (6) (-9450) ((1/1225)) ((1/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4053 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (7) (-8400) ((1/900)) ((1/6)) (1) ((-2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4054 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (9) (-7000) ((9/4900)) ((3/14)) (1) ((-2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4055 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (10) (-6510) ((1/441)) ((5/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4056 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (12) (-5775) ((4/1225)) ((2/7)) (1) ((2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4057 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (14) (-5250) ((1/225)) ((1/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4058 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (15) (-5040) ((1/196)) ((5/14)) (1) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4059 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (18) (-4550) ((9/1225)) ((3/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4060 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (20) (-4305) ((4/441)) ((10/21)) (1) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4061 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (21) (-4200) ((1/100)) ((1/2)) (1) ((-2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4062 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (25) (-3864) ((25/1764)) ((25/42)) (1) ((-2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4063 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (28) (-3675) ((4/225)) ((2/3)) (1) ((2,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4064 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (30) (-3570) ((1/49)) ((5/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4065 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (35) (-3360) ((1/36)) ((5/6)) (1) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4066 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (36) (-3325) ((36/1225)) ((6/7)) (1) ((2,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4067 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (42) (-3150) ((1/25)) (1) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4068 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (45) (-3080) ((9/196)) ((15/14)) (1) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4069 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (49) (-3000) ((49/900)) ((7/6)) (1) ((-2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4070 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (50) (-2982) ((25/441)) ((25/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4071 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (60) (-2835) ((4/49)) ((10/7)) (1) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4072 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (63) (-2800) ((9/100)) ((3/2)) (1) ((-2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4073 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (70) (-2730) ((1/9)) ((5/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4074 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (75) (-2688) ((25/196)) ((25/14)) (1) ((-2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4075 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (84) (-2625) ((4/25)) (2) (1) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4076 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (90) (-2590) ((9/49)) ((15/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4077 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (98) (-2550) ((49/225)) ((7/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4078 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (100) (-2541) ((100/441)) ((50/21)) (1) ((2,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4079 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (105) (-2520) ((1/4)) ((5/2)) (1) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4080 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (126) (-2450) ((9/25)) (3) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4081 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (140) (-2415) ((4/9)) ((10/3)) (1) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4082 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (147) (-2400) ((49/100)) ((7/2)) (1) ((-2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4083 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (150) (-2394) ((25/49)) ((25/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4084 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (175) (-2352) ((25/36)) ((25/6)) (1) ((-2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4085 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (180) (-2345) ((36/49)) ((30/7)) (1) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4086 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (196) (-2325) ((196/225)) ((14/3)) (1) ((2,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4087 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (210) (-2310) (1) (5) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4088 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (225) (-2296) ((225/196)) ((75/14)) (1) ((-2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4089 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (245) (-2280) ((49/36)) ((35/6)) (1) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4090 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (252) (-2275) ((36/25)) (6) (1) ((2,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4091 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (294) (-2250) ((49/25)) (7) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4092 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (300) (-2247) ((100/49)) ((50/7)) (1) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4093 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (315) (-2240) ((9/4)) ((15/2)) (1) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4094 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (350) (-2226) ((25/9)) ((25/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4095 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (420) (-2205) (4) (10) (1) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4096 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (441) (-2200) ((441/100)) ((21/2)) (1) ((-2,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4097 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (450) (-2198) ((225/49)) ((75/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4098 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (490) (-2190) ((49/9)) ((35/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4099 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (525) (-2184) ((25/4)) ((25/2)) (1) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4100 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (588) (-2175) ((196/25)) (14) (1) ((2,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4101 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (630) (-2170) (9) (15) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4102 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (700) (-2163) ((100/9)) ((50/3)) (1) ((2,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4103 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (735) (-2160) ((49/4)) ((35/2)) (1) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4104 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (882) (-2150) ((441/25)) (21) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4105 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (900) (-2149) ((900/49)) ((150/7)) (1) ((2,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4106 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord119) (980) (-2145) ((196/9)) ((70/3)) (1) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4107 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (294) (536) (441) (-2100) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4108 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (441) (537) (49) (-700) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4109 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (483) (539) (9) (-300) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4110 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (490) (540) ((49/9)) ((-700/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4111 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (504) (546) (1) (-100) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4112 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (510) (560) ((9/49)) ((-300/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4113 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (511) (567) ((1/9)) ((-100/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4114 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (513) (609) ((1/49)) ((-100/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4115 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (514) (756) ((1/441)) ((-100/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4116 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (515) (315) ((1/441)) ((100/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4117 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (516) (462) ((1/49)) ((100/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4118 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (518) (504) ((1/9)) ((100/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4119 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (519) (511) ((9/49)) ((300/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4120 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (539) (531) ((49/9)) ((700/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4121 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (546) (532) (9) (300) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4122 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (588) (534) (49) (700) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4123 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord120) (735) (535) (441) (2100) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4124 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (6) (-2093) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4125 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (14) (-2079) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4126 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (21) (-2058) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4127 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (24) (-2044) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4128 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (28) (-2016) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4129 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (30) (-1995) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4130 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (33) (-1946) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4131 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (35) (-1890) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4132 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (36) (-1848) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4133 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (38) (-1701) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4134 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (39) (-1554) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4135 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (40) (-1260) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4136 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (41) (-378) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4137 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (43) (-3906) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4138 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (44) (-3024) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4139 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (45) (-2730) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4140 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (46) (-2583) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4141 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (48) (-2436) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4142 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (49) (-2394) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4143 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (51) (-2338) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4144 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (54) (-2289) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4145 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (56) (-2268) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4146 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (60) (-2240) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4147 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (63) (-2226) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4148 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (70) (-2205) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4149 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (78) (-2191) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4150 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (84) (-2184) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4151 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (91) (-2178) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4152 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (105) (-2170) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4153 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (126) (-2163) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4154 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (140) (-2160) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4155 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (168) (-2156) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4156 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (189) (-2154) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4157 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (238) (-2151) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4158 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (294) (-2149) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4159 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (336) (-2148) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4160 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (483) (-2146) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4161 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (630) (-2145) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4162 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord121) (924) (-2144) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4163 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord122) (12) (-1022) ((9/49)) ((-150/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4164 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord122) (14) (-1008) ((1/9)) ((-50/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4165 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord122) (18) (-924) ((1/49)) ((-50/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4166 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord122) (20) (-630) ((1/441)) ((-50/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4167 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord122) (22) (-1512) ((1/441)) ((50/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4168 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord122) (24) (-1218) ((1/49)) ((50/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4169 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord122) (28) (-1134) ((1/9)) ((50/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4170 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord122) (30) (-1120) ((9/49)) ((150/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4171 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord122) (42) (-1092) (1) (50) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4172 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord122) (70) (-1080) ((49/9)) ((350/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4173 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord122) (84) (-1078) (9) (150) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4174 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord122) (168) (-1074) (49) (350) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4175 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord122) (462) (-1072) (441) (1050) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4176 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord123) (28) (1062) ((49/9)) ((350/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4177 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord123) (42) (1064) (9) (150) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4178 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord123) (126) (1068) (49) (350) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4179 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord123) (420) (1070) (441) (1050) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4180 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord124) (7) (2106) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4181 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord124) (21) (2114) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4182 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord124) (42) (2121) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4183 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord124) (56) (2124) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4184 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord124) (84) (2128) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4185 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord124) (105) (2130) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4186 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord124) (154) (2133) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4187 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord124) (210) (2135) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4188 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord124) (252) (2136) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4189 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord124) (399) (2138) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4190 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord124) (546) (2139) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4191 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord124) (840) (2140) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4192 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (105) (-2180) ((441/4)) ((-525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4193 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (252) (-2178) (49) (-175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4194 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (294) (-2177) (36) (-150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4195 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (350) (-2175) ((196/9)) ((-350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4196 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (399) (-2172) ((49/4)) ((-175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4197 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (420) (-2170) (9) (-75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4198 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (448) (-2166) ((49/9)) ((-175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4199 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (462) (-2163) (4) (-50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4200 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (483) (-2156) ((9/4)) ((-75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4201 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (497) (-2148) ((49/36)) ((-175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4202 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (504) (-2142) (1) (-25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4203 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (510) (-2135) ((36/49)) ((-150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4204 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (518) (-2121) ((4/9)) ((-50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4205 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (525) (-2100) ((1/4)) ((-25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4206 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (528) (-2086) ((9/49)) ((-75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4207 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (532) (-2058) ((1/9)) ((-25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4208 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (534) (-2037) ((4/49)) ((-50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4209 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (537) (-1988) ((9/196)) ((-75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4210 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (539) (-1932) ((1/36)) ((-25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4211 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (540) (-1890) ((1/49)) ((-25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4212 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (542) (-1743) ((4/441)) ((-50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4213 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (543) (-1596) ((1/196)) ((-25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4214 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (544) (-1302) ((1/441)) ((-25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4215 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (545) (-420) ((1/1764)) ((-25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4216 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (547) (-3948) ((1/1764)) ((25/42)) (0) ((-2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4217 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (548) (-3066) ((1/441)) ((25/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4218 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (549) (-2772) ((1/196)) ((25/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4219 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (550) (-2625) ((4/441)) ((50/21)) (0) ((2,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4220 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (552) (-2478) ((1/49)) ((25/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4221 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (553) (-2436) ((1/36)) ((25/6)) (0) ((-2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4222 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (555) (-2380) ((9/196)) ((75/14)) (0) ((-2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4223 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (558) (-2331) ((4/49)) ((50/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4224 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (560) (-2310) ((1/9)) ((25/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4225 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (564) (-2282) ((9/49)) ((75/7)) (0) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4226 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (567) (-2268) ((1/4)) ((25/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4227 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (574) (-2247) ((4/9)) ((50/3)) (0) ((2,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4228 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (582) (-2233) ((36/49)) ((150/7)) (0) ((2,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4229 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (588) (-2226) (1) (25) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4230 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (595) (-2220) ((49/36)) ((175/6)) (0) ((-2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4231 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (609) (-2212) ((9/4)) ((75/2)) (0) ((-2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4232 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (630) (-2205) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4233 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (644) (-2202) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4234 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (672) (-2198) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4235 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (693) (-2196) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4236 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (742) (-2193) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4237 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (798) (-2191) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4238 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (840) (-2190) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4239 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord125) (987) (-2188) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4240 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord126) (20) (-70) ((1/49)) ((-675/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4241 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord126) (21) (-84) ((1/4)) ((675/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4242 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord126) (42) (-81) (196) (9450) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4243 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord127) (0) (525) (4) (250) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4244 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord127) (42) (528) (49) (875) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4245 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord127) (336) (529) (1764) (5250) (0) ((2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4246 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord128) (0) (2625) (4) (50) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4247 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord128) (14) (2628) ((49/9)) ((175/3)) (0) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4248 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord128) (42) (2632) (9) (75) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4249 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord128) (63) (2634) ((49/4)) ((175/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4250 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord128) (112) (2637) ((196/9)) ((350/3)) (0) ((2,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4251 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord128) (168) (2639) (36) (150) (0) ((2,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4252 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord128) (210) (2640) (49) (175) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4253 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord128) (357) (2642) ((441/4)) ((525/2)) (0) ((-2,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4254 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord128) (504) (2643) (196) (350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4255 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord128) (798) (2644) (441) (525) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4256 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (336) (1023) (196) (-1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4257 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (434) (1024) (49) (-525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4258 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (483) (1026) ((49/4)) ((-525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4259 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (504) (1029) (4) (-150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4260 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (518) (1036) (1) (-75) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4261 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (525) (1050) ((1/4)) ((-75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4262 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (528) (1071) ((4/49)) ((-150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4263 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (530) (1120) ((1/49)) ((-75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4264 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (531) (1218) ((1/196)) ((-75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4265 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (533) (826) ((1/196)) ((75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4266 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (534) (924) ((1/49)) ((75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4267 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (536) (973) ((4/49)) ((150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4268 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (539) (994) ((1/4)) ((75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4269 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (546) (1008) (1) (75) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4270 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (560) (1015) (4) (150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4271 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (581) (1018) ((49/4)) ((525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4272 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (630) (1020) (49) (525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4273 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord129) (728) (1021) (196) (1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4274 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (0) (1596) (25) (-50) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4275 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (84) (1600) ((441/25)) (-42) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4276 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (210) (1610) (9) (-30) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4277 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (280) (1620) ((49/9)) ((-70/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4278 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (300) (1624) ((225/49)) ((-150/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4279 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (350) (1638) ((25/9)) ((-50/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4280 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (378) (1650) ((49/25)) (-14) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4281 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (420) (1680) (1) (-10) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4282 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (450) (1722) ((25/49)) ((-50/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4283 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (462) (1750) ((9/25)) (-6) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4284 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (476) (1800) ((49/225)) ((-14/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4285 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (480) (1820) ((9/49)) ((-30/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4286 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (490) (1890) ((1/9)) ((-10/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4287 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (500) (2016) ((25/441)) ((-50/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4288 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (504) (2100) ((1/25)) (-2) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4289 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (510) (2310) ((1/49)) ((-10/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4290 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (516) (2800) ((9/1225)) ((-6/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4291 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (518) (3150) ((1/225)) ((-2/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4292 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (520) (3780) ((1/441)) ((-10/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4293 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (522) (5250) ((1/1225)) ((-2/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4294 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (524) (12600) ((1/11025)) ((-2/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4295 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (526) (-9450) ((1/11025)) ((2/21)) (1) ((0,-2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4296 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (528) (-2100) ((1/1225)) ((2/7)) (1) ((0,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4297 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (530) (-630) ((1/441)) ((10/21)) (1) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4298 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (532) (0) ((1/225)) ((2/3)) (1) ((0,-2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4299 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (534) (350) ((9/1225)) ((6/7)) (1) ((0,2,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4300 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (540) (840) ((1/49)) ((10/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4301 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (546) (1050) ((1/25)) (2) (1) ((0,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4302 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (550) (1134) ((25/441)) ((50/21)) (1) ((0,-2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4303 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (560) (1260) ((1/9)) ((10/3)) (1) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4304 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (570) (1330) ((9/49)) ((30/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4305 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (574) (1350) ((49/225)) ((14/3)) (1) ((0,-2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4306 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (588) (1400) ((9/25)) (6) (1) ((0,2,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4307 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (600) (1428) ((25/49)) ((50/7)) (1) ((0,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4308 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (630) (1470) (1) (10) (1) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4309 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (672) (1500) ((49/25)) (14) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4310 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (700) (1512) ((25/9)) ((50/3)) (1) ((0,-2,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4311 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (750) (1526) ((225/49)) ((150/7)) (1) ((0,2,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4312 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (770) (1530) ((49/9)) ((70/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4313 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (840) (1540) (9) (30) (1) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4314 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord130) (966) (1550) ((441/25)) (42) (1) ((0,2,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4315 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord131) (0) (-84) (25) (950) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4316 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (336) (-1077) (196) (-1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4317 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (434) (-1076) (49) (-525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4318 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (483) (-1074) ((49/4)) ((-525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4319 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (504) (-1071) (4) (-150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4320 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (518) (-1064) (1) (-75) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4321 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (525) (-1050) ((1/4)) ((-75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4322 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (528) (-1029) ((4/49)) ((-150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4323 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (530) (-980) ((1/49)) ((-75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4324 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (531) (-882) ((1/196)) ((-75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4325 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (533) (-1274) ((1/196)) ((75/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4326 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (534) (-1176) ((1/49)) ((75/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4327 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (536) (-1127) ((4/49)) ((150/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4328 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (539) (-1106) ((1/4)) ((75/2)) (0) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4329 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (546) (-1092) (1) (75) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4330 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (560) (-1085) (4) (150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4331 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (581) (-1082) ((49/4)) ((525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4332 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (630) (-1080) (49) (525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4333 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord132) (728) (-1079) (196) (1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4334 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord133) (41) (-98) ((1/196)) ((975/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4335 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord133) (42) (-84) (1) (975) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4336 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord133) (56) (-83) (196) (13650) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4337 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord134) (545) (-105) ((1/441)) ((1000/21)) (0) ((0,-2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4338 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord134) (546) (-84) (1) (1000) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4339 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord134) (567) (-83) (441) (21000) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4340 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord135) (532) (-84) ((1/9)) ((1025/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4341 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord135) (546) (-81) (196) (14350) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4342 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord136) (0) (1575) (4) (150) (0) ((2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4343 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord136) (21) (1578) ((49/4)) ((525/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4344 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord136) (70) (1580) (49) (525) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4345 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord136) (168) (1581) (196) (1050) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4346 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord137) (0) (500) (441) (5775) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4347 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord138) (0) (550) (441) (5250) (0) ((0,2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4348 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord139) (78) (544) (9) (-1050) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4349 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord139) (84) (546) (1) (-350) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4350 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord139) (86) (552) ((1/9)) ((-350/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4351 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord139) (88) (534) ((1/9)) ((350/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4352 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord139) (90) (540) (1) (350) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4353 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord139) (96) (542) (9) (1050) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4354 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord140) (959) (544) ((49/4)) ((-2625/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4355 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord140) (966) (546) (1) (-375) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4356 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord140) (968) (553) ((4/49)) ((-750/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4357 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord140) (969) (504) ((1/196)) ((375/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4358 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord140) (1008) (543) (196) (5250) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4359 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord141) (0) (546) (25) (575) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4360 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord142) (0) (966) (25) (325) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4361 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord143) (28) (548) (49) (-4200) (0) ((0,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4362 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord143) (40) (560) ((1/49)) ((-600/7)) (0) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4363 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord143) (42) (546) (1) (600) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4364 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord144) (30) (970) (9) (-1050) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4365 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord144) (36) (972) (1) (-350) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4366 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord144) (38) (978) ((1/9)) ((-350/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4367 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord144) (40) (960) ((1/9)) ((350/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4368 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord144) (42) (966) (1) (350) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4369 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord144) (48) (968) (9) (1050) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4370 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord145) (42) (546) (1) (-650) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4371 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord146) (504) (969) (196) (-5250) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4372 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord146) (543) (1008) ((1/196)) ((-375/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4373 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord146) (544) (959) ((4/49)) ((750/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4374 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord146) (546) (966) (1) (375) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4375 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord146) (553) (968) ((49/4)) ((2625/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4376 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord147) (0) (546) (25) (-675) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4377 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord147) (28) (550) ((49/25)) (-189) (1) ((0,0,-2,2))
    (by decide +kernel)))

compact_certificate def auxSource4378 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord147) (35) (560) ((1/4)) ((-135/2)) (1) ((-2,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4379 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord147) (39) (0) ((1/4900)) ((27/14)) (1) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4380 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord147) (40) (490) ((1/49)) ((135/7)) (1) ((0,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4381 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord147) (42) (525) ((4/25)) (54) (1) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4382 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord147) (50) (539) ((100/49)) ((1350/7)) (1) ((2,0,2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4383 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord147) (175) (544) ((1225/4)) ((4725/2)) (1) ((-2,0,2,2))
    (by decide +kernel)))

compact_certificate def auxSource4384 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord148) (0) (-1134) (25) (325) (1) ((0,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4385 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord149) (525) (546) ((25/4)) ((-725/2)) (1) ((-2,0,2,0))
    (by decide +kernel)))

compact_certificate def auxSource4386 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord149) (540) (560) ((9/49)) ((-435/7)) (1) ((0,2,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4387 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord149) (543) (1050) ((1/4900)) ((-29/14)) (1) ((-2,0,-2,-2))
    (by decide +kernel)))

compact_certificate def auxSource4388 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord149) (546) (525) ((4/25)) (58) (1) ((2,0,-2,0))
    (by decide +kernel)))

compact_certificate def auxSource4389 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord149) (560) (540) ((49/9)) ((1015/3)) (1) ((0,-2,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4390 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord150) (30) (-1130) (9) (-1050) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4391 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord150) (36) (-1128) (1) (-350) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4392 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord150) (38) (-1122) ((1/9)) ((-350/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4393 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord150) (40) (-1140) ((1/9)) ((350/3)) (0) ((0,-2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4394 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord150) (42) (-1134) (1) (350) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4395 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord150) (48) (-1132) (9) (1050) (0) ((0,2,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4396 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord151) (504) (-1131) (196) (-5250) (0) ((2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4397 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord151) (543) (-1092) ((1/196)) ((-375/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4398 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord151) (544) (-1141) ((4/49)) ((750/7)) (0) ((2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4399 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord151) (546) (-1134) (1) (375) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4400 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord151) (553) (-1132) ((49/4)) ((2625/2)) (0) ((-2,0,0,2))
    (by decide +kernel)))

compact_certificate def auxSource4401 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord152) (39) (-84) ((1/196)) ((5225/14)) (0) ((-2,0,0,-2))
    (by decide +kernel)))

compact_certificate def auxSource4402 : SourceRow := .physical (.word (WordCertificate.ofValues 1050 (auxWord153) (543) (-81) (1) (-5600) (0) ((0,0,0,0))
    (by decide +kernel)))

compact_certificate def auxSource4403 : SourceRow := .physical (.infinity auxWord2 (0) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4404 : SourceRow := .physical (.infinity auxWord9 (1008) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4405 : SourceRow := .physical (.infinity auxWord10 (1029) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4406 : SourceRow := .physical (.infinity auxWord11 (14) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4407 : SourceRow := .physical (.infinity auxWord12 (21) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4408 : SourceRow := .physical (.infinity auxWord13 (42) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4409 : SourceRow := .physical (.infinity auxWord23 (532) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4410 : SourceRow := .physical (.infinity auxWord24 (546) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4411 : SourceRow := .physical (.infinity auxWord25 (504) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4412 : SourceRow := .physical (.infinity auxWord26 (518) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4413 : SourceRow := .physical (.infinity auxWord31 (966) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4414 : SourceRow := .physical (.infinity auxWord33 (84) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4415 : SourceRow := .physical (.infinity auxWord40 (966) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4416 : SourceRow := .physical (.infinity auxWord41 (969) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4417 : SourceRow := .physical (.infinity auxWord42 (84) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4418 : SourceRow := .physical (.infinity auxWord50 (546) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4419 : SourceRow := .physical (.infinity auxWord52 (504) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4420 : SourceRow := .physical (.infinity auxWord56 (1008) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4421 : SourceRow := .physical (.infinity auxWord58 (42) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4422 : SourceRow := .physical (.infinity auxWord67 (525) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4423 : SourceRow := .physical (.infinity auxWord69 (525) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4424 : SourceRow := .physical (.infinity auxWord72 (0) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4425 : SourceRow := .physical (.infinity auxWord75 (0) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4426 : SourceRow := .physical (.infinity auxWord85 (1008) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4427 : SourceRow := .physical (.infinity auxWord87 (42) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4428 : SourceRow := .physical (.infinity auxWord93 (546) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4429 : SourceRow := .physical (.infinity auxWord95 (504) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4430 : SourceRow := .physical (.infinity auxWord97 (39) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4431 : SourceRow := .physical (.infinity auxWord102 (543) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4432 : SourceRow := .physical (.infinity auxWord103 (84) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4433 : SourceRow := .physical (.infinity auxWord104 (28) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4434 : SourceRow := .physical (.infinity auxWord107 (1022) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4435 : SourceRow := .physical (.infinity auxWord108 (966) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4436 : SourceRow := .physical (.infinity auxWord112 (546) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4437 : SourceRow := .physical (.infinity auxWord114 (42) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4438 : SourceRow := .physical (.infinity auxWord115 (21) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4439 : SourceRow := .physical (.infinity auxWord118 (0) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4440 : SourceRow := .physical (.infinity auxWord119 (0) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4441 : SourceRow := .physical (.infinity auxWord121 (42) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4442 : SourceRow := .physical (.infinity auxWord122 (21) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4443 : SourceRow := .physical (.infinity auxWord125 (546) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4444 : SourceRow := .physical (.infinity auxWord129 (532) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4445 : SourceRow := .physical (.infinity auxWord130 (525) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4446 : SourceRow := .physical (.infinity auxWord132 (532) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4447 : SourceRow := .physical (.infinity auxWord139 (87) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4448 : SourceRow := .physical (.infinity auxWord144 (39) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4449 : SourceRow := .physical (.infinity auxWord150 (39) (by decide +kernel) (by decide +kernel))

compact_certificate def auxSource4450 : SourceRow := .old 0

compact_certificate def auxSource4451 : SourceRow := .old 1

compact_certificate def auxSource4452 : SourceRow := .old 2

compact_certificate def auxSource4453 : SourceRow := .old 3

compact_certificate def auxSource4454 : SourceRow := .old 4

compact_certificate def auxSource4455 : SourceRow := .old 5

compact_certificate def auxSource4456 : SourceRow := .old 6

compact_certificate def auxSource4457 : SourceRow := .old 7

compact_certificate def auxSource4458 : SourceRow := .old 8

compact_certificate def auxSource4459 : SourceRow := .old 9

compact_certificate def auxSource4460 : SourceRow := .old 10

compact_certificate def auxSource4461 : SourceRow := .old 11

compact_certificate def auxSource4462 : SourceRow := .old 12

compact_certificate def auxSource4463 : SourceRow := .old 13

compact_certificate def auxSource4464 : SourceRow := .old 14

compact_certificate def auxSource4465 : SourceRow := .old 15

compact_certificate def auxSource4466 : SourceRow := .old 16

compact_certificate def auxSource4467 : SourceRow := .old 17

compact_certificate def auxSource4468 : SourceRow := .old 18

compact_certificate def auxSource4469 : SourceRow := .old 19

compact_certificate def auxSource4470 : SourceRow := .old 20

compact_certificate def auxSource4471 : SourceRow := .old 21

compact_certificate def auxSource4472 : SourceRow := .old 22

compact_certificate def auxSource4473 : SourceRow := .old 23

compact_certificate def auxSource4474 : SourceRow := .old 24

compact_certificate def auxSource4475 : SourceRow := .old 25

compact_certificate def auxSource4476 : SourceRow := .old 26

compact_certificate def auxSource4477 : SourceRow := .old 27

compact_certificate def auxSource4478 : SourceRow := .old 28

compact_certificate def auxSource4479 : SourceRow := .old 29

compact_certificate def auxSource4480 : SourceRow := .old 30

compact_certificate def auxSource4481 : SourceRow := .old 31

compact_certificate def auxSource4482 : SourceRow := .old 32

compact_certificate def auxSource4483 : SourceRow := .old 33

compact_certificate def auxSource4484 : SourceRow := .old 34

compact_certificate def auxSource4485 : SourceRow := .old 35

compact_certificate def auxSource4486 : SourceRow := .old 36

compact_certificate def auxSource4487 : SourceRow := .old 37

compact_certificate def auxSource4488 : SourceRow := .old 38

compact_certificate def auxSource4489 : SourceRow := .old 39

compact_certificate def auxSource4490 : SourceRow := .old 40

compact_certificate def auxSource4491 : SourceRow := .old 41

compact_certificate def auxSource4492 : SourceRow := .old 42

compact_certificate def auxSource4493 : SourceRow := .old 43

compact_certificate def auxSource4494 : SourceRow := .old 44

compact_certificate def auxSource4495 : SourceRow := .old 45

compact_certificate def auxSource4496 : SourceRow := .old 46

compact_certificate def auxSource4497 : SourceRow := .old 47

compact_certificate def auxSource4498 : SourceRow := .old 48

compact_certificate def auxSource4499 : SourceRow := .old 49

compact_certificate def auxSource4500 : SourceRow := .old 50

compact_certificate def auxSource4501 : SourceRow := .old 51

compact_certificate def auxSource4502 : SourceRow := .old 52

compact_certificate def auxSource4503 : SourceRow := .old 53

compact_certificate def auxSource4504 : SourceRow := .old 54

compact_certificate def auxSource4505 : SourceRow := .old 55

compact_certificate def auxSource4506 : SourceRow := .old 56

compact_certificate def auxSource4507 : SourceRow := .old 57

compact_certificate def auxSource4508 : SourceRow := .old 58

compact_certificate def auxSource4509 : SourceRow := .old 59

compact_certificate def auxSource4510 : SourceRow := .old 60

compact_certificate def auxSource4511 : SourceRow := .old 61

compact_certificate def auxSource4512 : SourceRow := .old 62

compact_certificate def auxSource4513 : SourceRow := .old 63

compact_certificate def auxSource4514 : SourceRow := .old 64

compact_certificate def auxSource4515 : SourceRow := .old 65

compact_certificate def auxSource4516 : SourceRow := .old 66

compact_certificate def auxSource4517 : SourceRow := .old 67

compact_certificate def auxSource4518 : SourceRow := .old 68

compact_certificate def auxSource4519 : SourceRow := .old 69

compact_certificate def auxSource4520 : SourceRow := .old 70

compact_certificate def auxSource4521 : SourceRow := .old 71

compact_certificate def auxSource4522 : SourceRow := .old 72

compact_certificate def auxSource4523 : SourceRow := .old 73

compact_certificate def auxSource4524 : SourceRow := .old 74

compact_certificate def auxSource4525 : SourceRow := .old 75

compact_certificate def auxSource4526 : SourceRow := .old 76

compact_certificate def auxSource4527 : SourceRow := .old 77

compact_certificate def auxSource4528 : SourceRow := .old 78

compact_certificate def auxSource4529 : SourceRow := .old 79

compact_certificate def auxSource4530 : SourceRow := .old 80

compact_certificate def auxSource4531 : SourceRow := .old 81

compact_certificate def auxSource4532 : SourceRow := .old 82

compact_certificate def auxSource4533 : SourceRow := .old 83

compact_certificate def auxSource4534 : SourceRow := .old 84

compact_certificate def auxSource4535 : SourceRow := .old 85

compact_certificate def auxSource4536 : SourceRow := .old 86

compact_certificate def auxSource4537 : SourceRow := .old 87

compact_certificate def auxSource4538 : SourceRow := .old 88

compact_certificate def auxSource4539 : SourceRow := .old 89

compact_certificate def auxSource4540 : SourceRow := .old 90

compact_certificate def auxSource4541 : SourceRow := .old 91

compact_certificate def auxSource4542 : SourceRow := .old 92

compact_certificate def auxSource4543 : SourceRow := .old 93

compact_certificate def auxSource4544 : SourceRow := .old 94

compact_certificate def auxSource4545 : SourceRow := .old 95

compact_certificate def auxSource4546 : SourceRow := .old 96

compact_certificate def auxSource4547 : SourceRow := .old 97

compact_certificate def auxSource4548 : SourceRow := .old 98

compact_certificate def auxSource4549 : SourceRow := .old 99

compact_certificate def auxSource4550 : SourceRow := .old 100

compact_certificate def auxSource4551 : SourceRow := .old 101

compact_certificate def auxSource4552 : SourceRow := .old 102

compact_certificate def auxSource4553 : SourceRow := .old 103

compact_certificate def auxSource4554 : SourceRow := .old 104

compact_certificate def auxSource4555 : SourceRow := .old 105

compact_certificate def auxSource4556 : SourceRow := .old 106

compact_certificate def auxSource4557 : SourceRow := .old 107

compact_certificate def auxSource4558 : SourceRow := .old 108

compact_certificate def auxSource4559 : SourceRow := .old 109

compact_certificate def auxSource4560 : SourceRow := .old 110

compact_certificate def auxSource4561 : SourceRow := .old 111

compact_certificate def auxSource4562 : SourceRow := .old 112

compact_certificate def auxSource4563 : SourceRow := .old 113

compact_certificate def auxSource4564 : SourceRow := .old 114

compact_certificate def auxSource4565 : SourceRow := .old 115

compact_certificate def auxSource4566 : SourceRow := .old 116

compact_certificate def auxSource4567 : SourceRow := .old 117

compact_certificate def auxSource4568 : SourceRow := .old 118

compact_certificate def auxSource4569 : SourceRow := .old 119

compact_certificate def auxSource4570 : SourceRow := .old 120

compact_certificate def auxSource4571 : SourceRow := .old 121

compact_certificate def auxSource4572 : SourceRow := .old 122

compact_certificate def auxSource4573 : SourceRow := .old 123

compact_certificate def auxSource4574 : SourceRow := .old 124

compact_certificate def auxSource4575 : SourceRow := .old 125

compact_certificate def auxSource4576 : SourceRow := .old 126

compact_certificate def auxSource4577 : SourceRow := .old 127

compact_certificate def auxSource4578 : SourceRow := .old 128

compact_certificate def auxSource4579 : SourceRow := .old 129

compact_certificate def auxSource4580 : SourceRow := .old 130

compact_certificate def auxSource4581 : SourceRow := .old 131

compact_certificate def auxSource4582 : SourceRow := .old 132

compact_certificate def auxSource4583 : SourceRow := .old 133

compact_certificate def auxSource4584 : SourceRow := .old 134

compact_certificate def auxSource4585 : SourceRow := .old 135

compact_certificate def auxSource4586 : SourceRow := .old 136

compact_certificate def auxSource4587 : SourceRow := .old 137

compact_certificate def auxSource4588 : SourceRow := .old 138

compact_certificate def auxSource4589 : SourceRow := .old 139

compact_certificate def auxSource4590 : SourceRow := .old 140

compact_certificate def auxSource4591 : SourceRow := .old 141

compact_certificate def auxSource4592 : SourceRow := .old 142

compact_certificate def auxSource4593 : SourceRow := .old 143

compact_certificate def auxSource4594 : SourceRow := .old 144

compact_certificate def auxSource4595 : SourceRow := .old 145

compact_certificate def auxSource4596 : SourceRow := .old 146

compact_certificate def auxSource4597 : SourceRow := .old 147

compact_certificate def auxSource4598 : SourceRow := .old 148

compact_certificate def auxSource4599 : SourceRow := .old 149

#print axioms auxSource0
#print axioms auxSource895
#print axioms auxSource896
#print axioms auxSource2500
#print axioms auxSource4599
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData
end
end
