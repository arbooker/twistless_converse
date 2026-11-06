module
public import QuantitativeArithmeticSmallLevelThirtyFiveFullGridCaseIndexDataSeriesV4
public import QuantitativeArithmeticSparseEliminationV1
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace QuantitativeArithmeticCompact35Case0
open QuantitativeArithmeticSparseElimination
open QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

abbrev inputsRow000 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),209),((X^2*Z*W),208)]
abbrev inputsRow001 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),209),((Z*W),207)]
abbrev inputsRow002 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),104),(((X^2*Y^2*W)/(Z)),187)]
abbrev inputsRow003 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),199),(((Y^2*Z*W)/(X^2)),198)]
abbrev inputsRow004 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),209)]
abbrev inputsRow005 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Y^2*Z*W)),209),(((1)),206)]
abbrev inputsRow006 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*Z*W)),209),(((1)),205)]
abbrev inputsRow007 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Z*W)),209),(((1)),204)]
abbrev inputsRow008 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),197),(((X^2)/(Y^2*Z*W)),199)]
abbrev inputsRow009 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),186),(((Z)/(X^2*Y^2*W)),176)]
abbrev inputsRow010 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Z*W)),209),(((1)),203)]
abbrev inputsRow011 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),185),(((W)/(X^2*Y^2*Z)),143)]
abbrev inputsRow012 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),184),(((Y^2)/(X^2*Z*W)),128)]
abbrev inputsRow013 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),183),(((Z)/(Y^2*W)),109)]
abbrev inputsRow014 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),196),(((X^2)/(Z*W)),199)]
abbrev inputsRow015 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),182),(((W)/(Y^2*Z)),152)]
abbrev inputsRow016 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),181),(((Z)/(X^2*W)),101)]
abbrev inputsRow017 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),180),(((Y^2)/(Z*W)),127)]
abbrev inputsRow018 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),179),(((X^2*Z)/(Y^2*W)),107)]
abbrev inputsRow019 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),178),(((W)/(X^2*Z)),103)]
abbrev inputsRow020 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),177),(((X^2*W)/(Y^2*Z)),102)]
abbrev inputsRow021 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),143),(((Z)/(W)),176)]
abbrev inputsRow022 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),190),(((Z*W)/(X^2*Y^2)),191)]
abbrev inputsRow023 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),188),(((X^2*Y^2)/(Z*W)),189)]
abbrev inputsRow024 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),104),(((W)/(Z)),175)]
abbrev inputsRow025 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),97),(((Y^2*Z)/(X^2*W)),174)]
abbrev inputsRow026 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),108),(((X^2*Z)/(W)),173)]
abbrev inputsRow027 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),172),(((Y^2*W)/(X^2*Z)),105)]
abbrev inputsRow028 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),128),(((Z*W)/(Y^2)),171)]
abbrev inputsRow029 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),109),(((X^2*W)/(Z)),170)]
abbrev inputsRow030 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),160),(((Y^2*Z)/(W)),169)]
abbrev inputsRow031 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),199),(((Z*W)/(X^2)),195)]
abbrev inputsRow032 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),101),(((Y^2*W)/(Z)),168)]
abbrev inputsRow033 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),127),(((X^2*Z*W)/(Y^2)),167)]
abbrev inputsRow034 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),175),(((X^2*Y^2*Z)/(W)),166)]
abbrev inputsRow035 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*Z*W)),209),(((1)),202)]
abbrev inputsRow036 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Y^2*Z*W)),209),(((1)),201)]
abbrev inputsRow037 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*Y^2),165),(((1)),120)]
abbrev inputsRow038 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2)),66),(((1)),164)]
abbrev inputsRow039 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),200),(((-1)*Y^2),202)]
abbrev inputsRow040 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2)),209),(((1)),199)]
abbrev inputsRow041 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),194),((((-1))/(Y^2)),207)]
abbrev inputsRow042 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),193),(((-1)*X^2),208)]
abbrev inputsRow043 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),192),(((-1)),202)]
abbrev inputsRow044 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),163),((((-1))/(X^2)),164)]
abbrev inputsRow045 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),162),(((-1)*X^2),187)]
abbrev inputsRow046 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),72),(((-1)*X^2*Y^2),161)]
abbrev inputsRow047 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),160),(((-1)*Y^2),168)]
abbrev inputsRow048 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),159),(((-1)*X^2),167)]
abbrev inputsRow049 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),158),((((-1)*Y^2)/(X^2)),164)]
abbrev inputsRow050 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),157),((((-1))/(X^2*Y^2)),65)]
abbrev inputsRow051 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),156),((((-1))/(X^2)),120)]
abbrev inputsRow052 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),155),((((-1)*X^2)/(Y^2)),173)]
abbrev inputsRow053 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),154),(((-1)),171)]
abbrev inputsRow054 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),153),((((-1)*Y^2)/(X^2)),68)]
abbrev inputsRow055 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),152),(((-1)*X^2),170)]
abbrev inputsRow056 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),70),(((-1)*X^2*Y^2),151)]
abbrev inputsRow057 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*X^2*Y^2),150),(((1)),71)]
abbrev inputsRow058 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Y^2)/(X^2)),106),(((1)),149)]
abbrev inputsRow059 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^2)/(Y^2)),178),(((1)),148)]
abbrev inputsRow060 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2)),143),(((1)),147)]
abbrev inputsRow061 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),62),(((1)),146)]
abbrev inputsRow062 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),145),((((-1))/(X^2*Y^2)),120)]
abbrev inputsRow063 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*X^2*Y^2),144),(((1)),73)]
abbrev inputsRow064 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),176),(((-1)*X^2*Y^2),166)]
abbrev inputsRow065 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),191),(((-1)),207)]
abbrev inputsRow066 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),209),(((1)),189)]
abbrev inputsRow067 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),142),((((-1)*X^2)/(Y^2)),167)]
abbrev inputsRow068 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),141),((((-1)*Y^2)/(X^2)),164)]
abbrev inputsRow069 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*X^2*Y^2),140),(((1)),73)]
abbrev inputsRow070 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*Y^2),139),(((1)),67)]
abbrev inputsRow071 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*X^2),138),(((1)),65)]
abbrev inputsRow072 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Y^2)/(X^2)),137),(((1)),102)]
abbrev inputsRow073 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^2)/(Y^2)),97),(((1)),136)]
abbrev inputsRow074 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2)),62),(((1)),135)]
abbrev inputsRow075 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2)),69),(((1)),134)]
abbrev inputsRow076 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),72),(((1)),133)]
abbrev inputsRow077 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^2)/(Y^2)),63),(((1)),132)]
abbrev inputsRow078 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Y^2)/(X^2)),60),(((1)),131)]
abbrev inputsRow079 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*X^2),130),(((1)),120)]
abbrev inputsRow080 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*Y^2),129),(((1)),171)]
abbrev inputsRow081 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),128),(((1)),127)]
abbrev inputsRow082 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Z*W)),209),(((1)),126),((((1))/(X^2*Z*W)),127),(((1)),58)]
abbrev inputsRow083 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Z*W)),209),(((1)),59),((((1))/(X^2*Z*W)),128),(((1)),125)]
abbrev inputsRow084 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Z*W)),209),((((1))/(Z*W)),128),(((1)),72),(((1)),124)]
abbrev inputsRow085 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Z*W)),209),(((1)),123),(((1)),73),((((1))/(Z*W)),127)]
abbrev inputsRow086 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2)/(Z*W)),190),(((1)),122),(((X^2)/(Z*W)),199),(((1)),70)]
abbrev inputsRow087 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),71),(((X^2)/(Z*W)),199),(((1)),121),(((X^2)/(Z*W)),189)]
abbrev inputsRow088 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(X^2*W)),104),(((1)),96),(((Z)/(X^2*W)),155),(((1)),95)]
abbrev inputsRow089 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),98),(((Z)/(X^2*W)),148),(((1)),99),(((Z)/(X^2*W)),176)]
abbrev inputsRow090 (X Y Z W a b : ℂ) : Row ℂ := [(((W)/(X^2*Z)),92),(((1)),93),(((W)/(X^2*Z)),152),(((1)),107)]
abbrev inputsRow091 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),172),(((W)/(X^2*Z)),160),(((1)),85),(((W)/(X^2*Z)),86)]
abbrev inputsRow092 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(W)),89),(((1)),90),(((Z)/(W)),101),(((1)),103)]
abbrev inputsRow093 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),108),(((Z)/(W)),109),(((1)),87),(((Z)/(W)),88)]
abbrev inputsRow094 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),104),(((1)),109),(((1)),101),(((1)),176)]
abbrev inputsRow095 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Y^2*W)),209),((((1))/(X^2*Y^2*W)),104),(((1)),48),((((1))/(X^2*Y^2*W)),109),(((1)),76),((((1))/(X^2*Y^2*W)),101),(((1)),43),(((1)),44)]
abbrev inputsRow096 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Y^2*W)),209),(((1)),45),(((1)),50),((((1))/(X^2*Y^2*W)),109),(((1)),83),((((1))/(X^2*Y^2*W)),101),(((1)),46),((((1))/(X^2*Y^2*W)),176)]
abbrev inputsRow097 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*W)),209),((((1))/(Y^2*W)),104),(((1)),39),(((1)),49),((((1))/(Y^2*W)),101),(((1)),4),((((1))/(Y^2*W)),176),(((1)),136)]
abbrev inputsRow098 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*W)),209),(((1)),137),((((1))/(Y^2*W)),104),(((1)),111),((((1))/(Y^2*W)),109),(((1)),41),(((1)),38),((((1))/(Y^2*W)),176)]
abbrev inputsRow099 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*W)),209),((((1))/(X^2*W)),104),(((1)),97),((((1))/(X^2*W)),109),(((1)),112),(((1)),61),((((1))/(X^2*W)),176),(((1)),135)]
abbrev inputsRow100 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*W)),209),(((1)),138),((((1))/(X^2*W)),104),(((1)),64),(((1)),119),((((1))/(X^2*W)),101),(((1)),102),((((1))/(X^2*W)),176)]
abbrev inputsRow101 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2)/(Y^2*W)),178),(((1)),37),(((X^2)/(Y^2*W)),172),(((1)),14),(((X^2)/(Y^2*W)),199),(((1)),87),(((1)),134),(((X^2)/(Y^2*W)),173)]
abbrev inputsRow102 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2)/(Y^2*W)),178),(((1)),139),(((1)),90),(((X^2)/(Y^2*W)),199),(((1)),36),(((X^2)/(Y^2*W)),107),(((1)),5),(((X^2)/(Y^2*W)),173)]
abbrev inputsRow103 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(W)),209),((((1))/(W)),104),(((1)),62),((((1))/(W)),109),(((1)),160),((((1))/(W)),101),(((1)),75),(((1)),191)]
abbrev inputsRow104 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(W)),209),(((1)),188),(((1)),74),((((1))/(W)),109),(((1)),152),((((1))/(W)),101),(((1)),65),((((1))/(W)),176)]
abbrev inputsRow105 (X Y Z W a b : ℂ) : Row ℂ := [(((Y^2)/(X^2*W)),182),(((1)),117),(((Y^2)/(X^2*W)),89),(((1)),149),(((Y^2)/(X^2*W)),148),(((1)),99),(((Y^2)/(X^2*W)),127),(((1)),141)]
abbrev inputsRow106 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),130),(((Y^2)/(X^2*W)),128),(((1)),96),(((Y^2)/(X^2*W)),155),(((1)),153),(((Y^2)/(X^2*W)),88),(((1)),114),(((Y^2)/(X^2*W)),169)]
abbrev inputsRow107 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2)/(W)),178),(((1)),69),(((X^2)/(W)),172),(((1)),159),(((X^2)/(W)),199),(((1)),73),(((X^2)/(W)),107),(((1)),175)]
abbrev inputsRow108 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),143),(((X^2)/(W)),172),(((1)),72),(((X^2)/(W)),199),(((1)),154),(((X^2)/(W)),107),(((1)),67),(((X^2)/(W)),173)]
abbrev inputsRow109 (X Y Z W a b : ℂ) : Row ℂ := [(((W)/(Y^2)),66),(((1)),89),(((W)/(Y^2)),71),(((1)),148),(((W)/(Y^2)),193),(((1)),127),(((W)/(Y^2)),103),(((1)),174)]
abbrev inputsRow110 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),177),(((W)/(Y^2)),108),(((1)),128),(((W)/(Y^2)),200),(((1)),155),(((W)/(Y^2)),70),(((1)),88),(((W)/(Y^2)),120)]
abbrev inputsRow111 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),143),(((1)),108),(((1)),160),(((1)),152),(((1)),103),(((1)),175)]
abbrev inputsRow112 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Y^2*Z)),209),(((1)),42),((((1))/(X^2*Y^2*Z)),108),(((1)),35),((((1))/(X^2*Y^2*Z)),160),(((1)),78),((((1))/(X^2*Y^2*Z)),152),(((1)),23),((((1))/(X^2*Y^2*Z)),103),(((1)),51),((((1))/(X^2*Y^2*Z)),175),(((1)),52)]
abbrev inputsRow113 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Y^2*Z)),209),(((1)),56),((((1))/(X^2*Y^2*Z)),143),(((1)),40),((((1))/(X^2*Y^2*Z)),108),(((1)),34),((((1))/(X^2*Y^2*Z)),160),(((1)),84),((((1))/(X^2*Y^2*Z)),152),(((1)),18),((((1))/(X^2*Y^2*Z)),103),(((1)),47)]
abbrev inputsRow114 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*Z)),209),((((1))/(Y^2*Z)),143),(((1)),60),((((1))/(Y^2*Z)),108),(((1)),54),((((1))/(Y^2*Z)),160),(((1)),25),(((1)),36),((((1))/(Y^2*Z)),103),(((1)),6),((((1))/(Y^2*Z)),175),(((1)),174)]
abbrev inputsRow115 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*Z)),209),(((1)),177),((((1))/(Y^2*Z)),143),(((1)),110),((((1))/(Y^2*Z)),108),(((1)),14),(((1)),1),((((1))/(Y^2*Z)),152),(((1)),55),((((1))/(Y^2*Z)),103),(((1)),132),((((1))/(Y^2*Z)),175)]
abbrev inputsRow116 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Z)),209),((((1))/(X^2*Z)),143),(((1)),130),((((1))/(X^2*Z)),108),(((1)),172),((((1))/(X^2*Z)),160),(((1)),149),((((1))/(X^2*Z)),152),(((1)),119),(((1)),118),((((1))/(X^2*Z)),175),(((1)),131)]
abbrev inputsRow117 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Z)),209),(((1)),63),((((1))/(X^2*Z)),143),(((1)),113),(((1)),112),((((1))/(X^2*Z)),160),(((1)),153),((((1))/(X^2*Z)),152),(((1)),107),((((1))/(X^2*Z)),103),(((1)),141),((((1))/(X^2*Z)),175)]
abbrev inputsRow118 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2)/(Y^2*Z)),181),(((1)),129),(((X^2)/(Y^2*Z)),97),(((1)),13),(((X^2)/(Y^2*Z)),96),(((1)),28),(((X^2)/(Y^2*Z)),199),(((1)),41),(((X^2)/(Y^2*Z)),99),(((1)),88),(((1)),31),(((X^2)/(Y^2*Z)),170)]
abbrev inputsRow119 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(X^2*Y^2)),66),(((1)),190),(((Z)/(X^2*Y^2)),69),(((1)),98),(((Z)/(X^2*Y^2)),109),(((1)),94),(((Z)/(X^2*Y^2)),154),(((1)),83),(((Z)/(X^2*Y^2)),70),(((1)),91),(((1)),77),(((Z)/(X^2*Y^2)),207)]
abbrev inputsRow120 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(X^2*Y^2)),203),(((1)),82),(((1)),80),(((Z)/(X^2*Y^2)),71),(((1)),76),(((Z)/(X^2*Y^2)),159),(((1)),100),(((Z)/(X^2*Y^2)),101),(((1)),95),(((Z)/(X^2*Y^2)),67),(((1)),189),(((Z)/(X^2*Y^2)),120)]
abbrev inputsRow121 (X Y Z W a b : ℂ) : Row ℂ := [(((Y^2)/(X^2*Z)),183),(((1)),138),(((Y^2)/(X^2*Z)),137),(((1)),59),(((Y^2)/(X^2*Z)),128),(((1)),158),(((Y^2)/(X^2*Z)),147),(((1)),61),(((Y^2)/(X^2*Z)),87),(((1)),114),(((Y^2)/(X^2*Z)),86),(((1)),173)]
abbrev inputsRow122 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),178),(((Y^2)/(X^2*Z)),92),(((1)),117),(((Y^2)/(X^2*Z)),90),(((1)),64),(((Y^2)/(X^2*Z)),162),(((1)),156),(((Y^2)/(X^2*Z)),127),(((1)),58),(((Y^2)/(X^2*Z)),136),(((1)),135),(((Y^2)/(X^2*Z)),168)]
abbrev inputsRow123 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(Y^2)),196),(((1)),137),(((Z)/(Y^2)),104),(((1)),128),(((Z)/(Y^2)),72),(((1)),147),(((Z)/(Y^2)),200),(((1)),87),(((Z)/(Y^2)),75),(((1)),86),(((Z)/(Y^2)),65),(((1)),105)]
abbrev inputsRow124 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),178),(((1)),172),(((1)),107),(((1)),173)]
abbrev inputsRow125 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*W)),209),(((1)),33),(((1)),13),((((1))/(Y^2*W)),109),((((1))/(Y^2*W)),101),(((1)),55),((((1))/(Y^2*W)),176),(((1)),105)]
abbrev inputsRow126 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*W)),209),(((1)),179),((((1))/(Y^2*W)),104),(((1)),54),((((1))/(Y^2*W)),109),((((1))/(Y^2*W)),101),(((1)),32),(((1)),16)]
abbrev inputsRow127 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),181),(((1)),97),(((1)),96),(((1)),99),(((1)),102),(((1)),170)]
abbrev inputsRow128 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),182),(((1)),177),(((1)),89),(((1)),148),(((1)),155),(((1)),88),(((1)),174),(((1)),169)]
abbrev inputsRow129 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*W)),209),(((1)),181),((((1))/(X^2*W)),177),(((1)),56),(((1)),113),((((1))/(X^2*W)),128),((((1))/(X^2*W)),109),(((1)),158),(((1)),57),((((1))/(X^2*W)),101),((((1))/(X^2*W)),88),(((1)),91),((((1))/(X^2*W)),176),(((1)),131),((((1))/(X^2*W)),169),(((1)),151)]
abbrev inputsRow130 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*W)),209),(((1)),150),((((1))/(X^2*W)),182),(((1)),63),((((1))/(X^2*W)),104),(((1)),80),((((1))/(X^2*W)),89),((((1))/(X^2*W)),109),(((1)),53),(((1)),156),((((1))/(X^2*W)),101),((((1))/(X^2*W)),127),(((1)),118),(((1)),52),((((1))/(X^2*W)),174),(((1)),170)]
abbrev inputsRow131 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(W)),209),((((1))/(W)),182),(((1)),106),(((1)),143),((((1))/(W)),104),(((1)),110),((((1))/(W)),109),((((1))/(W)),148),(((1)),147),(((1)),154),((((1))/(W)),127),(((1)),67),((((1))/(W)),176),((((1))/(W)),174),(((1)),31),(((1)),195)]
abbrev inputsRow132 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(W)),209),(((1)),196),(((1)),30),((((1))/(W)),177),((((1))/(W)),104),(((1)),69),((((1))/(W)),128),(((1)),159),(((1)),162),((((1))/(W)),155),((((1))/(W)),101),(((1)),6),((((1))/(W)),176),(((1)),175),(((1)),68),((((1))/(W)),169)]
abbrev inputsRow133 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2)/(W)),185),(((1)),180),(((X^2)/(W)),178),(((1)),60),(((X^2)/(W)),81),(((1)),108),(((X^2)/(W)),78),(((1)),200),(((X^2)/(W)),199),(((1)),29),(((X^2)/(W)),107),(((1)),3),(((X^2)/(W)),189),(((1)),120),(((X^2)/(W)),173),(((1)),168)]
abbrev inputsRow134 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),183),(((X^2)/(W)),178),(((1)),66),(((X^2)/(W)),190),(((1)),15),(((X^2)/(W)),172),(((1)),28),(((X^2)/(W)),199),(((1)),193),(((X^2)/(W)),84),(((1)),103),(((X^2)/(W)),79),(((1)),132),(((X^2)/(W)),173),(((1)),171),(((X^2)/(W)),166)]
abbrev inputsRow135 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),183),(((1)),179),(((1)),137),(((1)),92),(((1)),90),(((1)),147),(((1)),162),(((1)),87),(((1)),86),(((1)),136),(((1)),105),(((1)),168)]
abbrev inputsRow136 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Z)),209),(((1)),144),((((1))/(X^2*Z)),179),(((1)),178),((((1))/(X^2*Z)),143),(((1)),45),(((1)),117),((((1))/(X^2*Z)),108),((((1))/(X^2*Z)),90),(((1)),64),((((1))/(X^2*Z)),160),(((1)),146),((((1))/(X^2*Z)),162),(((1)),156),(((1)),27),((((1))/(X^2*Z)),127),((((1))/(X^2*Z)),103),(((1)),79),((((1))/(X^2*Z)),136),(((1)),135),((((1))/(X^2*Z)),175),(((1)),20),((((1))/(X^2*Z)),168),(((1)),167)]
abbrev inputsRow137 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Z)),209),(((1)),184),((((1))/(X^2*Z)),183),(((1)),26),((((1))/(X^2*Z)),143),(((1)),138),((((1))/(X^2*Z)),137),(((1)),81),((((1))/(X^2*Z)),108),((((1))/(X^2*Z)),128),(((1)),21),(((1)),158),((((1))/(X^2*Z)),147),(((1)),157),((((1))/(X^2*Z)),152),(((1)),61),((((1))/(X^2*Z)),87),((((1))/(X^2*Z)),103),(((1)),114),(((1)),44),((((1))/(X^2*Z)),175),(((1)),173),((((1))/(X^2*Z)),105),(((1)),161)]
abbrev inputsRow138 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),185),(((1)),81),(((1)),93),(((1)),78),(((1)),84),(((1)),85),(((1)),79),(((1)),166)]
abbrev inputsRow139 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(W)),209),(((1)),165),((((1))/(W)),104),(((1)),92),((((1))/(W)),128),(((1)),74),((((1))/(W)),109),(((1)),25),((((1))/(W)),155),(((1)),152),((((1))/(W)),101),(((1)),2),((((1))/(W)),88),(((1)),65),((((1))/(W)),169),(((1)),207)]
abbrev inputsRow140 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(W)),209),(((1)),203),((((1))/(W)),182),(((1)),62),((((1))/(W)),89),(((1)),24),((((1))/(W)),109),(((1)),160),((((1))/(W)),148),(((1)),1),((((1))/(W)),101),(((1)),75),((((1))/(W)),127),(((1)),86),((((1))/(W)),176),(((1)),164)]
abbrev inputsRow141 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Y^2)),209),(((1)),185),((((1))/(X^2*Y^2)),196),(((1)),150),((((1))/(X^2*Y^2)),180),(((1)),26),(((1)),82),((((1))/(X^2*Y^2)),143),((((1))/(X^2*Y^2)),188),(((1)),140),((((1))/(X^2*Y^2)),104),(((1)),81),(((1)),80),((((1))/(X^2*Y^2)),108),((((1))/(X^2*Y^2)),71),(((1)),10),((((1))/(X^2*Y^2)),72),(((1)),17),((((1))/(X^2*Y^2)),74),(((1)),21),((((1))/(X^2*Y^2)),159),(((1)),53),((((1))/(X^2*Y^2)),200),(((1)),145),((((1))/(X^2*Y^2)),193),(((1)),157),(((1)),100),((((1))/(X^2*Y^2)),152),((((1))/(X^2*Y^2)),101),(((1)),85),((((1))/(X^2*Y^2)),73),(((1)),125),(((1)),95),((((1))/(X^2*Y^2)),103),((((1))/(X^2*Y^2)),67),(((1)),116),((((1))/(X^2*Y^2)),65),(((1)),7),((((1))/(X^2*Y^2)),176),(((1)),189),((((1))/(X^2*Y^2)),175),((((1))/(X^2*Y^2)),120),(((1)),0),((((1))/(X^2*Y^2)),171),(((1)),19),((((1))/(X^2*Y^2)),195),(((1)),161),(((1)),187)]
abbrev inputsRow142 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),186),(((1)),82),(((1)),80),(((1)),98),(((1)),76),(((1)),94),(((1)),100),(((1)),83),(((1)),95),(((1)),91),(((1)),77),(((1)),187)]
abbrev inputsRow143 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),206),(((1)),144),(((1)),150),(((1)),22),(((1)),26),(((1)),12),(((1)),56),(((1)),42),(((1)),140),(((1)),45),(((1)),48),(((1)),11),(((1)),115),(((1)),40),(((1)),35),(((1)),10),(((1)),126),(((1)),17),(((1)),21),(((1)),50),(((1)),34),(((1)),53),(((1)),146),(((1)),145),(((1)),163),(((1)),157),(((1)),57),(((1)),23),(((1)),43),(((1)),27),(((1)),9),(((1)),125),(((1)),8),(((1)),18),(((1)),51),(((1)),116),(((1)),7),(((1)),46),(((1)),44),(((1)),133),(((1)),47),(((1)),52),(((1)),0),(((1)),20),(((1)),19),(((1)),151),(((1)),161),(((1)),201)]
abbrev inputsRow144 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),205),((((-1)*a)/(X)),197),((((1))/(X^2)),165),(((1)),163)]
abbrev inputsRow145 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),197),((((-1)*a)/(X)),165),((((1))/(X^2)),106),(((1)),157)]
abbrev inputsRow146 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),186),((((-1)*a)/(X)),183),((((1))/(X^2)),179),(((1)),162)]
abbrev inputsRow147 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),185),((((-1)*a)/(X)),182),((((1))/(X^2)),177),(((1)),155)]
abbrev inputsRow148 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),165),((((-1)*a)/(X)),106),((((1))/(X^2)),60),(((1)),57)]
abbrev inputsRow149 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),184),((((-1)*a)/(X)),180),((((1))/(X^2)),188),(((1)),154)]
abbrev inputsRow150 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),183),((((-1)*a)/(X)),179),((((1))/(X^2)),137),(((1)),100)]
abbrev inputsRow151 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),144),((((-1)*a)/(X)),33),((((1))/(X^2)),39),(((1)),29)]
abbrev inputsRow152 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),182),((((-1)*a)/(X)),177),((((1))/(X^2)),89),(((1)),84)]
abbrev inputsRow153 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),181),((((-1)*a)/(X)),143),((((1))/(X^2)),108),(((1)),152)]
abbrev inputsRow154 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),106),((((-1)*a)/(X)),60),((((1))/(X^2)),13),(((1)),23)]
abbrev inputsRow155 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),22),((((-1)*a)/(X)),129),((((1))/(X^2)),123),(((1)),36)]
abbrev inputsRow156 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),180),((((-1)*a)/(X)),188),((((1))/(X^2)),72),(((1)),119)]
abbrev inputsRow157 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),26),((((-1)*a)/(X)),139),((((1))/(X^2)),24),(((1)),41)]
abbrev inputsRow158 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),179),((((-1)*a)/(X)),137),((((1))/(X^2)),90),(((1)),83)]
abbrev inputsRow159 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),33),((((-1)*a)/(X)),39),((((1))/(X^2)),14),(((1)),43)]
abbrev inputsRow160 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),12),((((-1)*a)/(X)),37),((((1))/(X^2)),25),(((1)),4)]
abbrev inputsRow161 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),82),((((-1)*a)/(X)),92),((((1))/(X^2)),147),(((1)),87)]
abbrev inputsRow162 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),30),((((-1)*a)/(X)),15),((((1))/(X^2)),192),(((1)),27)]
abbrev inputsRow163 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),143),((((-1)*a)/(X)),108),((((1))/(X^2)),152),(((1)),99)]
abbrev inputsRow164 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),42),((((-1)*a)/(X)),54),((((1))/(X^2)),41),(((1)),121)]
abbrev inputsRow165 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),140),((((-1)*a)/(X)),122),(((1)),124),((((1))/(X^2)),55)]
abbrev inputsRow166 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),48),((((-1)*a)/(X)),49),(((1)),55),((((1))/(X^2)),134)]
abbrev inputsRow167 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),97),((((-1)*a)/(X)),160),(((1)),103),((((1))/(X^2)),175)]
abbrev inputsRow168 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),62),((((-1)*a)/(X)),159),(((1)),118),((((1))/(X^2)),171)]
abbrev inputsRow169 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),81),((((-1)*a)/(X)),148),(((1)),88),((((1))/(X^2)),169)]
abbrev inputsRow170 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),92),((((-1)*a)/(X)),147),(((1)),91),((((1))/(X^2)),168)]
abbrev inputsRow171 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),117),((((-1)*a)/(X)),200),(((1)),67),((((1))/(X^2)),207)]
abbrev inputsRow172 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),15),((((-1)*a)/(X)),192),(((1)),116),((((1))/(X^2)),202)]
abbrev inputsRow173 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),205),(((1)),115),((((-1)*a)/(X)),194),(((1)),3)]
abbrev inputsRow174 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),203),(((1)),69),((((-1)*a)/(X)),193),(((1)),114)]
abbrev inputsRow175 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),183),(((1)),80),((((-1)*a)/(X)),162),(((1)),86)]
abbrev inputsRow176 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),182),(((1)),89),((((-1)*a)/(X)),155),(((1)),79)]
abbrev inputsRow177 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),180),(((1)),113),((((-1)*a)/(X)),154),(((1)),65)]
abbrev inputsRow178 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),104),(((1)),172),((((-1)*a)/(X)),101),(((1)),176)]
abbrev inputsRow179 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),54),(((1)),123),((((-1)*a)/(X)),121),(((1)),133)]
abbrev inputsRow180 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),122),((((1))/(X^2)),49),((((-1)*a)/(X)),55),(((1)),47)]
abbrev inputsRow181 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),90),((((1))/(X^2)),162),((((-1)*a)/(X)),86),(((1)),77)]
abbrev inputsRow182 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),49),((((1))/(X^2)),2),((((-1)*a)/(X)),134),(((1)),20)]
abbrev inputsRow183 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),112),((((1))/(X^2)),73),((((-1)*a)/(X)),191),(((1)),171)]
abbrev inputsRow184 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),14),((((1))/(X^2)),124),((((-1)*a)/(X)),142),(((1)),19)]
abbrev inputsRow185 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),34),((((1))/(X^2)),32),((((-1)*a)/(X)),132),(((1)),68)]
abbrev inputsRow186 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),94),((((1))/(X^2)),136),((((-1)*a)/(X)),105),(((1)),168)]
abbrev inputsRow187 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),53),((((1))/(X^2)),132),((((-1)*a)/(X)),68),(((1)),164)]
abbrev inputsRow188 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),204),((((-1)*b)/(Y)),184),((((1))/(Y^2)),63),(((1)),17),(((1)),8)]
abbrev inputsRow189 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),203),((((-1)*b)/(Y)),180),((((1))/(Y^2)),69),(((1)),24),(((1)),32)]
abbrev inputsRow190 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),185),((((-1)*b)/(Y)),178),((((1))/(Y^2)),172),(((1)),93),(((1)),107)]
abbrev inputsRow191 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),183),((((-1)*b)/(Y)),143),(((1)),90),((((1))/(Y^2)),160),(((1)),103)]
abbrev inputsRow192 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),144),((((-1)*b)/(Y)),130),(((1)),64),((((1))/(Y^2)),158),(((1)),51)]
abbrev inputsRow193 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),196),((((-1)*b)/(Y)),188),(((1)),111),((((1))/(Y^2)),193),(((1)),6)]
abbrev inputsRow194 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),150),((((-1)*b)/(Y)),138),(((1)),50),((((1))/(Y^2)),153),(((1)),118)]
abbrev inputsRow195 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),106),((((-1)*b)/(Y)),62),(((1)),49),((((1))/(Y^2)),70),(((1)),67)]
abbrev inputsRow196 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),22),((((-1)*b)/(Y)),117),(((1)),112),((((1))/(Y^2)),118),(((1)),116)]
abbrev inputsRow197 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),180),((((-1)*b)/(Y)),69),(((1)),14),(((1)),3),((((1))/(Y^2)),65)]
abbrev inputsRow198 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),33),((((-1)*b)/(Y)),71),(((1)),25),(((1)),65),((((1))/(Y^2)),195)]
abbrev inputsRow199 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),12),((((-1)*b)/(Y)),59),(((1)),149),(((1)),7),((((1))/(Y^2)),208)]
abbrev inputsRow200 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),63),((((1))/(Y^2)),130),((((-1)*b)/(Y)),64),(((1)),53),(((1)),46)]
abbrev inputsRow201 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),177),((((1))/(Y^2)),104),((((-1)*b)/(Y)),109),(((1)),148),(((1)),176)]
abbrev inputsRow202 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),56),((((1))/(Y^2)),117),((((-1)*b)/(Y)),112),(((1)),158),(((1)),44)]
abbrev inputsRow203 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),42),((((1))/(Y^2)),59),((((-1)*b)/(Y)),149),(((1)),146),(((1)),135)]
abbrev inputsRow204 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),130),((((1))/(Y^2)),112),((((-1)*b)/(Y)),158),(((1)),145),(((1)),133)]
abbrev inputsRow205 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2)),204),(((1)),11),(((1)),153),((((-1)*b)/(Y)),58),(((1)),0)]
abbrev inputsRow206 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),110),((((1))/(Y^2)),200),(((1)),4),((((-1)*b)/(Y)),191),(((1)),195)]
abbrev inputsRow207 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),40),((((1))/(Y^2)),156),(((1)),61),((((-1)*b)/(Y)),141),(((1)),161)]
abbrev inputsRow208 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),144),(((1)),115),((((1))/(Z)),80),(((1)),94),(((1)),9),(((1)),47)]
abbrev inputsRow209 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),22),(((1)),40),((((1))/(Z)),76),(((1)),146),(((1)),8),(((1)),77)]
def inputsTable (X Y Z W a b : ℂ) : Array (Row ℂ) := #[
  inputsRow000 X Y Z W a b,
  inputsRow001 X Y Z W a b,
  inputsRow002 X Y Z W a b,
  inputsRow003 X Y Z W a b,
  inputsRow004 X Y Z W a b,
  inputsRow005 X Y Z W a b,
  inputsRow006 X Y Z W a b,
  inputsRow007 X Y Z W a b,
  inputsRow008 X Y Z W a b,
  inputsRow009 X Y Z W a b,
  inputsRow010 X Y Z W a b,
  inputsRow011 X Y Z W a b,
  inputsRow012 X Y Z W a b,
  inputsRow013 X Y Z W a b,
  inputsRow014 X Y Z W a b,
  inputsRow015 X Y Z W a b,
  inputsRow016 X Y Z W a b,
  inputsRow017 X Y Z W a b,
  inputsRow018 X Y Z W a b,
  inputsRow019 X Y Z W a b,
  inputsRow020 X Y Z W a b,
  inputsRow021 X Y Z W a b,
  inputsRow022 X Y Z W a b,
  inputsRow023 X Y Z W a b,
  inputsRow024 X Y Z W a b,
  inputsRow025 X Y Z W a b,
  inputsRow026 X Y Z W a b,
  inputsRow027 X Y Z W a b,
  inputsRow028 X Y Z W a b,
  inputsRow029 X Y Z W a b,
  inputsRow030 X Y Z W a b,
  inputsRow031 X Y Z W a b,
  inputsRow032 X Y Z W a b,
  inputsRow033 X Y Z W a b,
  inputsRow034 X Y Z W a b,
  inputsRow035 X Y Z W a b,
  inputsRow036 X Y Z W a b,
  inputsRow037 X Y Z W a b,
  inputsRow038 X Y Z W a b,
  inputsRow039 X Y Z W a b,
  inputsRow040 X Y Z W a b,
  inputsRow041 X Y Z W a b,
  inputsRow042 X Y Z W a b,
  inputsRow043 X Y Z W a b,
  inputsRow044 X Y Z W a b,
  inputsRow045 X Y Z W a b,
  inputsRow046 X Y Z W a b,
  inputsRow047 X Y Z W a b,
  inputsRow048 X Y Z W a b,
  inputsRow049 X Y Z W a b,
  inputsRow050 X Y Z W a b,
  inputsRow051 X Y Z W a b,
  inputsRow052 X Y Z W a b,
  inputsRow053 X Y Z W a b,
  inputsRow054 X Y Z W a b,
  inputsRow055 X Y Z W a b,
  inputsRow056 X Y Z W a b,
  inputsRow057 X Y Z W a b,
  inputsRow058 X Y Z W a b,
  inputsRow059 X Y Z W a b,
  inputsRow060 X Y Z W a b,
  inputsRow061 X Y Z W a b,
  inputsRow062 X Y Z W a b,
  inputsRow063 X Y Z W a b,
  inputsRow064 X Y Z W a b,
  inputsRow065 X Y Z W a b,
  inputsRow066 X Y Z W a b,
  inputsRow067 X Y Z W a b,
  inputsRow068 X Y Z W a b,
  inputsRow069 X Y Z W a b,
  inputsRow070 X Y Z W a b,
  inputsRow071 X Y Z W a b,
  inputsRow072 X Y Z W a b,
  inputsRow073 X Y Z W a b,
  inputsRow074 X Y Z W a b,
  inputsRow075 X Y Z W a b,
  inputsRow076 X Y Z W a b,
  inputsRow077 X Y Z W a b,
  inputsRow078 X Y Z W a b,
  inputsRow079 X Y Z W a b,
  inputsRow080 X Y Z W a b,
  inputsRow081 X Y Z W a b,
  inputsRow082 X Y Z W a b,
  inputsRow083 X Y Z W a b,
  inputsRow084 X Y Z W a b,
  inputsRow085 X Y Z W a b,
  inputsRow086 X Y Z W a b,
  inputsRow087 X Y Z W a b,
  inputsRow088 X Y Z W a b,
  inputsRow089 X Y Z W a b,
  inputsRow090 X Y Z W a b,
  inputsRow091 X Y Z W a b,
  inputsRow092 X Y Z W a b,
  inputsRow093 X Y Z W a b,
  inputsRow094 X Y Z W a b,
  inputsRow095 X Y Z W a b,
  inputsRow096 X Y Z W a b,
  inputsRow097 X Y Z W a b,
  inputsRow098 X Y Z W a b,
  inputsRow099 X Y Z W a b,
  inputsRow100 X Y Z W a b,
  inputsRow101 X Y Z W a b,
  inputsRow102 X Y Z W a b,
  inputsRow103 X Y Z W a b,
  inputsRow104 X Y Z W a b,
  inputsRow105 X Y Z W a b,
  inputsRow106 X Y Z W a b,
  inputsRow107 X Y Z W a b,
  inputsRow108 X Y Z W a b,
  inputsRow109 X Y Z W a b,
  inputsRow110 X Y Z W a b,
  inputsRow111 X Y Z W a b,
  inputsRow112 X Y Z W a b,
  inputsRow113 X Y Z W a b,
  inputsRow114 X Y Z W a b,
  inputsRow115 X Y Z W a b,
  inputsRow116 X Y Z W a b,
  inputsRow117 X Y Z W a b,
  inputsRow118 X Y Z W a b,
  inputsRow119 X Y Z W a b,
  inputsRow120 X Y Z W a b,
  inputsRow121 X Y Z W a b,
  inputsRow122 X Y Z W a b,
  inputsRow123 X Y Z W a b,
  inputsRow124 X Y Z W a b,
  inputsRow125 X Y Z W a b,
  inputsRow126 X Y Z W a b,
  inputsRow127 X Y Z W a b,
  inputsRow128 X Y Z W a b,
  inputsRow129 X Y Z W a b,
  inputsRow130 X Y Z W a b,
  inputsRow131 X Y Z W a b,
  inputsRow132 X Y Z W a b,
  inputsRow133 X Y Z W a b,
  inputsRow134 X Y Z W a b,
  inputsRow135 X Y Z W a b,
  inputsRow136 X Y Z W a b,
  inputsRow137 X Y Z W a b,
  inputsRow138 X Y Z W a b,
  inputsRow139 X Y Z W a b,
  inputsRow140 X Y Z W a b,
  inputsRow141 X Y Z W a b,
  inputsRow142 X Y Z W a b,
  inputsRow143 X Y Z W a b,
  inputsRow144 X Y Z W a b,
  inputsRow145 X Y Z W a b,
  inputsRow146 X Y Z W a b,
  inputsRow147 X Y Z W a b,
  inputsRow148 X Y Z W a b,
  inputsRow149 X Y Z W a b,
  inputsRow150 X Y Z W a b,
  inputsRow151 X Y Z W a b,
  inputsRow152 X Y Z W a b,
  inputsRow153 X Y Z W a b,
  inputsRow154 X Y Z W a b,
  inputsRow155 X Y Z W a b,
  inputsRow156 X Y Z W a b,
  inputsRow157 X Y Z W a b,
  inputsRow158 X Y Z W a b,
  inputsRow159 X Y Z W a b,
  inputsRow160 X Y Z W a b,
  inputsRow161 X Y Z W a b,
  inputsRow162 X Y Z W a b,
  inputsRow163 X Y Z W a b,
  inputsRow164 X Y Z W a b,
  inputsRow165 X Y Z W a b,
  inputsRow166 X Y Z W a b,
  inputsRow167 X Y Z W a b,
  inputsRow168 X Y Z W a b,
  inputsRow169 X Y Z W a b,
  inputsRow170 X Y Z W a b,
  inputsRow171 X Y Z W a b,
  inputsRow172 X Y Z W a b,
  inputsRow173 X Y Z W a b,
  inputsRow174 X Y Z W a b,
  inputsRow175 X Y Z W a b,
  inputsRow176 X Y Z W a b,
  inputsRow177 X Y Z W a b,
  inputsRow178 X Y Z W a b,
  inputsRow179 X Y Z W a b,
  inputsRow180 X Y Z W a b,
  inputsRow181 X Y Z W a b,
  inputsRow182 X Y Z W a b,
  inputsRow183 X Y Z W a b,
  inputsRow184 X Y Z W a b,
  inputsRow185 X Y Z W a b,
  inputsRow186 X Y Z W a b,
  inputsRow187 X Y Z W a b,
  inputsRow188 X Y Z W a b,
  inputsRow189 X Y Z W a b,
  inputsRow190 X Y Z W a b,
  inputsRow191 X Y Z W a b,
  inputsRow192 X Y Z W a b,
  inputsRow193 X Y Z W a b,
  inputsRow194 X Y Z W a b,
  inputsRow195 X Y Z W a b,
  inputsRow196 X Y Z W a b,
  inputsRow197 X Y Z W a b,
  inputsRow198 X Y Z W a b,
  inputsRow199 X Y Z W a b,
  inputsRow200 X Y Z W a b,
  inputsRow201 X Y Z W a b,
  inputsRow202 X Y Z W a b,
  inputsRow203 X Y Z W a b,
  inputsRow204 X Y Z W a b,
  inputsRow205 X Y Z W a b,
  inputsRow206 X Y Z W a b,
  inputsRow207 X Y Z W a b,
  inputsRow208 X Y Z W a b,
  inputsRow209 X Y Z W a b
]
def inputs (X Y Z W a b : ℂ) (i : ℕ) : Row ℂ := (inputsTable X Y Z W a b)[i]?.getD []

abbrev stepsRow000 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),209)]
abbrev stepsRow001 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),208)]
abbrev stepsRow002 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),207)]
abbrev stepsRow003 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),206)]
abbrev stepsRow004 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),205)]
abbrev stepsRow005 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),204)]
abbrev stepsRow006 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),203)]
abbrev stepsRow007 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),202)]
abbrev stepsRow008 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),201)]
abbrev stepsRow009 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),200)]
abbrev stepsRow010 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),199)]
abbrev stepsRow011 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),198)]
abbrev stepsRow012 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),197)]
abbrev stepsRow013 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),196)]
abbrev stepsRow014 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),195)]
abbrev stepsRow015 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),194)]
abbrev stepsRow016 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),193)]
abbrev stepsRow017 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),192)]
abbrev stepsRow018 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),191)]
abbrev stepsRow019 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),190)]
abbrev stepsRow020 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),189)]
abbrev stepsRow021 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),188)]
abbrev stepsRow022 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(X^2*Y^2*W)),104),(((1)),187)]
abbrev stepsRow023 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),186),(((Z)/(X^2*Y^2*W)),176)]
abbrev stepsRow024 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),185),(((W)/(X^2*Y^2*Z)),143)]
abbrev stepsRow025 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),184),(((Y^2)/(X^2*Z*W)),128)]
abbrev stepsRow026 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),183),(((Z)/(Y^2*W)),109)]
abbrev stepsRow027 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),182),(((W)/(Y^2*Z)),152)]
abbrev stepsRow028 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),181),(((Z)/(X^2*W)),101)]
abbrev stepsRow029 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),180),(((Y^2)/(Z*W)),127)]
abbrev stepsRow030 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),179),(((X^2*Z)/(Y^2*W)),107)]
abbrev stepsRow031 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),178),(((W)/(X^2*Z)),103)]
abbrev stepsRow032 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),177),(((X^2*W)/(Y^2*Z)),102)]
abbrev stepsRow033 (X Y Z W a b : ℂ) : Row ℂ := [(((W)/(Z)),143),(((1)),176)]
abbrev stepsRow034 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(W)),104),(((1)),175)]
abbrev stepsRow035 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2*W)/(Y^2*Z)),97),(((1)),174)]
abbrev stepsRow036 (X Y Z W a b : ℂ) : Row ℂ := [(((W)/(X^2*Z)),108),(((1)),173)]
abbrev stepsRow037 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),172),(((Y^2*W)/(X^2*Z)),105)]
abbrev stepsRow038 (X Y Z W a b : ℂ) : Row ℂ := [(((Y^2)/(Z*W)),128),(((1)),171)]
abbrev stepsRow039 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(X^2*W)),109),(((1)),170)]
abbrev stepsRow040 (X Y Z W a b : ℂ) : Row ℂ := [(((W)/(Y^2*Z)),160),(((1)),169)]
abbrev stepsRow041 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(Y^2*W)),101),(((1)),168)]
abbrev stepsRow042 (X Y Z W a b : ℂ) : Row ℂ := [(((Y^2)/(X^2*Z*W)),127),(((1)),167)]
abbrev stepsRow043 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),104),(((1)),166)]
abbrev stepsRow044 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),165),((((-1))/(Y^2)),120)]
abbrev stepsRow045 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2)),66),(((1)),164)]
abbrev stepsRow046 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),66),(((1)),163)]
abbrev stepsRow047 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(Y^2*W)),104),(((1)),162)]
abbrev stepsRow048 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),72),(((1)),161)]
abbrev stepsRow049 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),160),(((Z)/(W)),101)]
abbrev stepsRow050 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),159),(((Y^2)/(Z*W)),127)]
abbrev stepsRow051 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2)),66),(((1)),158)]
abbrev stepsRow052 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),157),((((-1))/(X^2*Y^2)),65)]
abbrev stepsRow053 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),156),((((-1))/(X^2)),120)]
abbrev stepsRow054 (X Y Z W a b : ℂ) : Row ℂ := [(((W)/(Y^2*Z)),108),(((1)),155)]
abbrev stepsRow055 (X Y Z W a b : ℂ) : Row ℂ := [(((Y^2)/(Z*W)),128),(((1)),154)]
abbrev stepsRow056 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),153),((((-1)*Y^2)/(X^2)),68)]
abbrev stepsRow057 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(W)),109),(((1)),152)]
abbrev stepsRow058 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),70),(((1)),151)]
abbrev stepsRow059 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),150),((((-1))/(X^2*Y^2)),71)]
abbrev stepsRow060 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Y^2)/(X^2)),106),(((1)),149)]
abbrev stepsRow061 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),148),(((W)/(Y^2*Z)),103)]
abbrev stepsRow062 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2)),143),(((1)),147)]
abbrev stepsRow063 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),62),(((1)),146)]
abbrev stepsRow064 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),145),((((-1))/(X^2*Y^2)),120)]
abbrev stepsRow065 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),144),((((-1))/(X^2*Y^2)),73)]
abbrev stepsRow066 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),143),(((Z)/(W)),104)]
abbrev stepsRow067 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Z*W)),127),(((1)),142)]
abbrev stepsRow068 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2)),66),(((1)),141)]
abbrev stepsRow069 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),140),((((-1))/(X^2*Y^2)),73)]
abbrev stepsRow070 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),139),((((-1))/(Y^2)),67)]
abbrev stepsRow071 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),138),((((-1))/(X^2)),65)]
abbrev stepsRow072 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),137),((((-1)*X^2)/(Y^2)),102)]
abbrev stepsRow073 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^2)/(Y^2)),97),(((1)),136)]
abbrev stepsRow074 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2)),62),(((1)),135)]
abbrev stepsRow075 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2)),69),(((1)),134)]
abbrev stepsRow076 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),72),(((1)),133)]
abbrev stepsRow077 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^2)/(Y^2)),63),(((1)),132)]
abbrev stepsRow078 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Y^2)/(X^2)),60),(((1)),131)]
abbrev stepsRow079 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),130),((((-1))/(X^2)),120)]
abbrev stepsRow080 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),129),((((1))/(Z*W)),128)]
abbrev stepsRow081 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),128),(((1)),127)]
abbrev stepsRow082 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),127)]
abbrev stepsRow083 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),126),(((1)),58)]
abbrev stepsRow084 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),59),(((1)),125)]
abbrev stepsRow085 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),72),(((1)),124)]
abbrev stepsRow086 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),123),(((1)),73)]
abbrev stepsRow087 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),122),(((1)),70)]
abbrev stepsRow088 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),71),(((1)),121)]
abbrev stepsRow089 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),66),(((1)),120)]
abbrev stepsRow090 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),72),(((1)),119)]
abbrev stepsRow091 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),62),(((1)),118)]
abbrev stepsRow092 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),117),(((1)),67)]
abbrev stepsRow093 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),15),(((1)),116)]
abbrev stepsRow094 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),115),(((1)),3)]
abbrev stepsRow095 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),69),(((1)),114)]
abbrev stepsRow096 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),113),(((1)),65)]
abbrev stepsRow097 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),112),((((1))/(X^2)),73)]
abbrev stepsRow098 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),111),(((1)),6)]
abbrev stepsRow099 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),110),(((1)),4)]
abbrev stepsRow100 (X Y Z W a b : ℂ) : Row ℂ := [(((2)),104),(((1)),109),(((1)),101)]
abbrev stepsRow101 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),108),(((1)),103)]
abbrev stepsRow102 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),107),((((-1)*Y^2*W)/(X^2*Z)),105)]
abbrev stepsRow103 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),106),(((X*a)/(Y^2)),66),((((1))/(Y^2)),65)]
abbrev stepsRow104 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2*Z + (2)*X*Z*a + Z)/(Y^2*W)),104),(((X*Z*a)/(Y^2*W)),101),(((1)),105)]
abbrev stepsRow105 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),104)]
abbrev stepsRow106 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^2*Z + Z)/(W)),101),(((1)),103)]
abbrev stepsRow107 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^3*Z + X*Z + (-1)*Z*a)/(X*W)),101),(((1)),102)]
abbrev stepsRow108 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),101)]
abbrev stepsRow109 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),100)]
abbrev stepsRow110 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),99)]
abbrev stepsRow111 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),98)]
abbrev stepsRow112 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),97)]
abbrev stepsRow113 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),96)]
abbrev stepsRow114 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),95)]
abbrev stepsRow115 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),94)]
abbrev stepsRow116 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),93)]
abbrev stepsRow117 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),92)]
abbrev stepsRow118 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),91)]
abbrev stepsRow119 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),90)]
abbrev stepsRow120 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),89)]
abbrev stepsRow121 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),88)]
abbrev stepsRow122 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),87)]
abbrev stepsRow123 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),86)]
abbrev stepsRow124 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),85)]
abbrev stepsRow125 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),84)]
abbrev stepsRow126 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),83)]
abbrev stepsRow127 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),82)]
abbrev stepsRow128 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),81)]
abbrev stepsRow129 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),80)]
abbrev stepsRow130 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),79)]
abbrev stepsRow131 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),78)]
abbrev stepsRow132 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),77)]
abbrev stepsRow133 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),76)]
abbrev stepsRow134 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),62),(((1)),75)]
abbrev stepsRow135 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),74),(((1)),65)]
abbrev stepsRow136 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),69),(((1)),73)]
abbrev stepsRow137 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),72),(((1)),67)]
abbrev stepsRow138 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),66),(((1)),71)]
abbrev stepsRow139 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)),66),(((1)),70)]
abbrev stepsRow140 (X Y Z W a b : ℂ) : Row ℂ := [(((2)),66),(((1)),69)]
abbrev stepsRow141 (X Y Z W a b : ℂ) : Row ℂ := [((((2)*X^2 + (-1))/(Y^2)),66),(((1)),68)]
abbrev stepsRow142 (X Y Z W a b : ℂ) : Row ℂ := [(((-2)),66),(((1)),67)]
abbrev stepsRow143 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),66)]
abbrev stepsRow144 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),65)]
abbrev stepsRow145 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),64)]
abbrev stepsRow146 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),63)]
abbrev stepsRow147 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),62)]
abbrev stepsRow148 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),61)]
abbrev stepsRow149 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),60)]
abbrev stepsRow150 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),59)]
abbrev stepsRow151 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),58)]
abbrev stepsRow152 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),57)]
abbrev stepsRow153 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),56)]
abbrev stepsRow154 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),55)]
abbrev stepsRow155 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),54)]
abbrev stepsRow156 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),53)]
abbrev stepsRow157 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),52)]
abbrev stepsRow158 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),51)]
abbrev stepsRow159 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),50)]
abbrev stepsRow160 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),49)]
abbrev stepsRow161 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),48)]
abbrev stepsRow162 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),47)]
abbrev stepsRow163 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),46)]
abbrev stepsRow164 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),45)]
abbrev stepsRow165 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),44)]
abbrev stepsRow166 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),43)]
abbrev stepsRow167 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),42)]
abbrev stepsRow168 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),41)]
abbrev stepsRow169 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),40)]
abbrev stepsRow170 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),39),(((1)),4)]
abbrev stepsRow171 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)),6),(((1)),38)]
abbrev stepsRow172 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),37),(((1)),14)]
abbrev stepsRow173 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),36),(((1)),5)]
abbrev stepsRow174 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),35),(((1)),23)]
abbrev stepsRow175 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),34),(((1)),18)]
abbrev stepsRow176 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),33),(((1)),13)]
abbrev stepsRow177 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),32),(((1)),16)]
abbrev stepsRow178 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)),4),(((1)),31)]
abbrev stepsRow179 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),30),(((1)),6)]
abbrev stepsRow180 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),29),(((1)),3)]
abbrev stepsRow181 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),15),(((1)),28)]
abbrev stepsRow182 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),27),(((1)),20)]
abbrev stepsRow183 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),26),(((1)),21)]
abbrev stepsRow184 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),25),(((1)),2)]
abbrev stepsRow185 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),24),(((1)),1)]
abbrev stepsRow186 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),13),(((1)),23)]
abbrev stepsRow187 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),22),(((-1)),5)]
abbrev stepsRow188 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),21),((((1))/(X^2)),1)]
abbrev stepsRow189 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),2),(((1)),20)]
abbrev stepsRow190 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),14),(((1)),19)]
abbrev stepsRow191 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),18),((((1))/(X^2)),16)]
abbrev stepsRow192 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),17),(((1)),8)]
abbrev stepsRow193 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),1),(((1)),16)]
abbrev stepsRow194 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),15),(((-1)),5)]
abbrev stepsRow195 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),14),(((1)),3)]
abbrev stepsRow196 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),13),(((1)),2)]
abbrev stepsRow197 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),12),(((1)),7)]
abbrev stepsRow198 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),11),(((1)),0)]
abbrev stepsRow199 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),10),(((1)),9)]
abbrev stepsRow200 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),9),(((-1)),3)]
abbrev stepsRow201 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),8),(((1)),5)]
abbrev stepsRow202 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),7),(((1)),0)]
abbrev stepsRow203 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)),2),(((1)),6),(((-1)),5)]
abbrev stepsRow204 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2 + (-1))/(X^2 + X*a)),2),(((1)),5)]
abbrev stepsRow205 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),4),((((-1)*X*a + (-1))/(X^2 + X*a)),2)]
abbrev stepsRow206 (X Y Z W a b : ℂ) : Row ℂ := [(((X^3*a + X^2*a^2 + X*a + (1))/(X^4 + X^3*a)),2),(((1)),3)]
abbrev stepsRow207 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),2)]
abbrev stepsRow208 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),1)]
abbrev stepsRow209 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),0)]
def stepsTable (X Y Z W a b : ℂ) : Array (Row ℂ) := #[
  stepsRow000 X Y Z W a b,
  stepsRow001 X Y Z W a b,
  stepsRow002 X Y Z W a b,
  stepsRow003 X Y Z W a b,
  stepsRow004 X Y Z W a b,
  stepsRow005 X Y Z W a b,
  stepsRow006 X Y Z W a b,
  stepsRow007 X Y Z W a b,
  stepsRow008 X Y Z W a b,
  stepsRow009 X Y Z W a b,
  stepsRow010 X Y Z W a b,
  stepsRow011 X Y Z W a b,
  stepsRow012 X Y Z W a b,
  stepsRow013 X Y Z W a b,
  stepsRow014 X Y Z W a b,
  stepsRow015 X Y Z W a b,
  stepsRow016 X Y Z W a b,
  stepsRow017 X Y Z W a b,
  stepsRow018 X Y Z W a b,
  stepsRow019 X Y Z W a b,
  stepsRow020 X Y Z W a b,
  stepsRow021 X Y Z W a b,
  stepsRow022 X Y Z W a b,
  stepsRow023 X Y Z W a b,
  stepsRow024 X Y Z W a b,
  stepsRow025 X Y Z W a b,
  stepsRow026 X Y Z W a b,
  stepsRow027 X Y Z W a b,
  stepsRow028 X Y Z W a b,
  stepsRow029 X Y Z W a b,
  stepsRow030 X Y Z W a b,
  stepsRow031 X Y Z W a b,
  stepsRow032 X Y Z W a b,
  stepsRow033 X Y Z W a b,
  stepsRow034 X Y Z W a b,
  stepsRow035 X Y Z W a b,
  stepsRow036 X Y Z W a b,
  stepsRow037 X Y Z W a b,
  stepsRow038 X Y Z W a b,
  stepsRow039 X Y Z W a b,
  stepsRow040 X Y Z W a b,
  stepsRow041 X Y Z W a b,
  stepsRow042 X Y Z W a b,
  stepsRow043 X Y Z W a b,
  stepsRow044 X Y Z W a b,
  stepsRow045 X Y Z W a b,
  stepsRow046 X Y Z W a b,
  stepsRow047 X Y Z W a b,
  stepsRow048 X Y Z W a b,
  stepsRow049 X Y Z W a b,
  stepsRow050 X Y Z W a b,
  stepsRow051 X Y Z W a b,
  stepsRow052 X Y Z W a b,
  stepsRow053 X Y Z W a b,
  stepsRow054 X Y Z W a b,
  stepsRow055 X Y Z W a b,
  stepsRow056 X Y Z W a b,
  stepsRow057 X Y Z W a b,
  stepsRow058 X Y Z W a b,
  stepsRow059 X Y Z W a b,
  stepsRow060 X Y Z W a b,
  stepsRow061 X Y Z W a b,
  stepsRow062 X Y Z W a b,
  stepsRow063 X Y Z W a b,
  stepsRow064 X Y Z W a b,
  stepsRow065 X Y Z W a b,
  stepsRow066 X Y Z W a b,
  stepsRow067 X Y Z W a b,
  stepsRow068 X Y Z W a b,
  stepsRow069 X Y Z W a b,
  stepsRow070 X Y Z W a b,
  stepsRow071 X Y Z W a b,
  stepsRow072 X Y Z W a b,
  stepsRow073 X Y Z W a b,
  stepsRow074 X Y Z W a b,
  stepsRow075 X Y Z W a b,
  stepsRow076 X Y Z W a b,
  stepsRow077 X Y Z W a b,
  stepsRow078 X Y Z W a b,
  stepsRow079 X Y Z W a b,
  stepsRow080 X Y Z W a b,
  stepsRow081 X Y Z W a b,
  stepsRow082 X Y Z W a b,
  stepsRow083 X Y Z W a b,
  stepsRow084 X Y Z W a b,
  stepsRow085 X Y Z W a b,
  stepsRow086 X Y Z W a b,
  stepsRow087 X Y Z W a b,
  stepsRow088 X Y Z W a b,
  stepsRow089 X Y Z W a b,
  stepsRow090 X Y Z W a b,
  stepsRow091 X Y Z W a b,
  stepsRow092 X Y Z W a b,
  stepsRow093 X Y Z W a b,
  stepsRow094 X Y Z W a b,
  stepsRow095 X Y Z W a b,
  stepsRow096 X Y Z W a b,
  stepsRow097 X Y Z W a b,
  stepsRow098 X Y Z W a b,
  stepsRow099 X Y Z W a b,
  stepsRow100 X Y Z W a b,
  stepsRow101 X Y Z W a b,
  stepsRow102 X Y Z W a b,
  stepsRow103 X Y Z W a b,
  stepsRow104 X Y Z W a b,
  stepsRow105 X Y Z W a b,
  stepsRow106 X Y Z W a b,
  stepsRow107 X Y Z W a b,
  stepsRow108 X Y Z W a b,
  stepsRow109 X Y Z W a b,
  stepsRow110 X Y Z W a b,
  stepsRow111 X Y Z W a b,
  stepsRow112 X Y Z W a b,
  stepsRow113 X Y Z W a b,
  stepsRow114 X Y Z W a b,
  stepsRow115 X Y Z W a b,
  stepsRow116 X Y Z W a b,
  stepsRow117 X Y Z W a b,
  stepsRow118 X Y Z W a b,
  stepsRow119 X Y Z W a b,
  stepsRow120 X Y Z W a b,
  stepsRow121 X Y Z W a b,
  stepsRow122 X Y Z W a b,
  stepsRow123 X Y Z W a b,
  stepsRow124 X Y Z W a b,
  stepsRow125 X Y Z W a b,
  stepsRow126 X Y Z W a b,
  stepsRow127 X Y Z W a b,
  stepsRow128 X Y Z W a b,
  stepsRow129 X Y Z W a b,
  stepsRow130 X Y Z W a b,
  stepsRow131 X Y Z W a b,
  stepsRow132 X Y Z W a b,
  stepsRow133 X Y Z W a b,
  stepsRow134 X Y Z W a b,
  stepsRow135 X Y Z W a b,
  stepsRow136 X Y Z W a b,
  stepsRow137 X Y Z W a b,
  stepsRow138 X Y Z W a b,
  stepsRow139 X Y Z W a b,
  stepsRow140 X Y Z W a b,
  stepsRow141 X Y Z W a b,
  stepsRow142 X Y Z W a b,
  stepsRow143 X Y Z W a b,
  stepsRow144 X Y Z W a b,
  stepsRow145 X Y Z W a b,
  stepsRow146 X Y Z W a b,
  stepsRow147 X Y Z W a b,
  stepsRow148 X Y Z W a b,
  stepsRow149 X Y Z W a b,
  stepsRow150 X Y Z W a b,
  stepsRow151 X Y Z W a b,
  stepsRow152 X Y Z W a b,
  stepsRow153 X Y Z W a b,
  stepsRow154 X Y Z W a b,
  stepsRow155 X Y Z W a b,
  stepsRow156 X Y Z W a b,
  stepsRow157 X Y Z W a b,
  stepsRow158 X Y Z W a b,
  stepsRow159 X Y Z W a b,
  stepsRow160 X Y Z W a b,
  stepsRow161 X Y Z W a b,
  stepsRow162 X Y Z W a b,
  stepsRow163 X Y Z W a b,
  stepsRow164 X Y Z W a b,
  stepsRow165 X Y Z W a b,
  stepsRow166 X Y Z W a b,
  stepsRow167 X Y Z W a b,
  stepsRow168 X Y Z W a b,
  stepsRow169 X Y Z W a b,
  stepsRow170 X Y Z W a b,
  stepsRow171 X Y Z W a b,
  stepsRow172 X Y Z W a b,
  stepsRow173 X Y Z W a b,
  stepsRow174 X Y Z W a b,
  stepsRow175 X Y Z W a b,
  stepsRow176 X Y Z W a b,
  stepsRow177 X Y Z W a b,
  stepsRow178 X Y Z W a b,
  stepsRow179 X Y Z W a b,
  stepsRow180 X Y Z W a b,
  stepsRow181 X Y Z W a b,
  stepsRow182 X Y Z W a b,
  stepsRow183 X Y Z W a b,
  stepsRow184 X Y Z W a b,
  stepsRow185 X Y Z W a b,
  stepsRow186 X Y Z W a b,
  stepsRow187 X Y Z W a b,
  stepsRow188 X Y Z W a b,
  stepsRow189 X Y Z W a b,
  stepsRow190 X Y Z W a b,
  stepsRow191 X Y Z W a b,
  stepsRow192 X Y Z W a b,
  stepsRow193 X Y Z W a b,
  stepsRow194 X Y Z W a b,
  stepsRow195 X Y Z W a b,
  stepsRow196 X Y Z W a b,
  stepsRow197 X Y Z W a b,
  stepsRow198 X Y Z W a b,
  stepsRow199 X Y Z W a b,
  stepsRow200 X Y Z W a b,
  stepsRow201 X Y Z W a b,
  stepsRow202 X Y Z W a b,
  stepsRow203 X Y Z W a b,
  stepsRow204 X Y Z W a b,
  stepsRow205 X Y Z W a b,
  stepsRow206 X Y Z W a b,
  stepsRow207 X Y Z W a b,
  stepsRow208 X Y Z W a b,
  stepsRow209 X Y Z W a b
]
def steps (X Y Z W a b : ℂ) (i : ℕ) : Row ℂ := (stepsTable X Y Z W a b)[i]?.getD []

abbrev instructionsRow000 (X Y Z W a b : ℂ) : Row ℂ := [(1,4)]
abbrev instructionsRow001 (X Y Z W a b : ℂ) : Row ℂ := [(1 / (X ^ 2 * Z * W),0),((1 / (X ^ 2 * Z * W))*(-(1)),210)]
abbrev instructionsRow002 (X Y Z W a b : ℂ) : Row ℂ := [(1 / (Z * W),1),((1 / (Z * W))*(-(1)),210)]
abbrev instructionsRow003 (X Y Z W a b : ℂ) : Row ℂ := [(1,5),(-(1 / (X ^ 2 * Y ^ 2 * Z * W)),210)]
abbrev instructionsRow004 (X Y Z W a b : ℂ) : Row ℂ := [(1,6),(-(1 / (Y ^ 2 * Z * W)),210)]
abbrev instructionsRow005 (X Y Z W a b : ℂ) : Row ℂ := [(1,7),(-(1 / (X ^ 2 * Z * W)),210)]
abbrev instructionsRow006 (X Y Z W a b : ℂ) : Row ℂ := [(1,10),(-(1 / (Z * W)),210)]
abbrev instructionsRow007 (X Y Z W a b : ℂ) : Row ℂ := [(1,35),(-(1 / (Y ^ 2 * Z * W)),210)]
abbrev instructionsRow008 (X Y Z W a b : ℂ) : Row ℂ := [(1,36),(-(1 / (X ^ 2 * Y ^ 2 * Z * W)),210)]
abbrev instructionsRow009 (X Y Z W a b : ℂ) : Row ℂ := [(1,39),(-(-1 * Y ^ 2),217)]
abbrev instructionsRow010 (X Y Z W a b : ℂ) : Row ℂ := [(1,40),(-(-1 / X ^ 2),210)]
abbrev instructionsRow011 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 / (Y ^ 2 * Z * W),3),((X ^ 2 / (Y ^ 2 * Z * W))*(-(1)),220)]
abbrev instructionsRow012 (X Y Z W a b : ℂ) : Row ℂ := [(1,8),(-(X ^ 2 / (Y ^ 2 * Z * W)),220)]
abbrev instructionsRow013 (X Y Z W a b : ℂ) : Row ℂ := [(1,14),(-(X ^ 2 / (Z * W)),220)]
abbrev instructionsRow014 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 / (Z * W),31),((X ^ 2 / (Z * W))*(-(1)),220)]
abbrev instructionsRow015 (X Y Z W a b : ℂ) : Row ℂ := [(1,41),(-(-1 / Y ^ 2),212)]
abbrev instructionsRow016 (X Y Z W a b : ℂ) : Row ℂ := [(1,42),(-(-1 * X ^ 2),211)]
abbrev instructionsRow017 (X Y Z W a b : ℂ) : Row ℂ := [(1,43),(-(-1),217)]
abbrev instructionsRow018 (X Y Z W a b : ℂ) : Row ℂ := [(1,65),(-(-1),212)]
abbrev instructionsRow019 (X Y Z W a b : ℂ) : Row ℂ := [(1,22),(-(Z * W / (X ^ 2 * Y ^ 2)),228)]
abbrev instructionsRow020 (X Y Z W a b : ℂ) : Row ℂ := [(1,66),(-(-1 / (X ^ 2 * Y ^ 2)),210)]
abbrev instructionsRow021 (X Y Z W a b : ℂ) : Row ℂ := [(1,23),(-(X ^ 2 * Y ^ 2 / (Z * W)),230)]
abbrev instructionsRow022 (X Y Z W a b : ℂ) : Row ℂ := [(Z / (X ^ 2 * Y ^ 2 * W),2)]
abbrev instructionsRow023 (X Y Z W a b : ℂ) : Row ℂ := [(1,9)]
abbrev instructionsRow024 (X Y Z W a b : ℂ) : Row ℂ := [(1,11)]
abbrev instructionsRow025 (X Y Z W a b : ℂ) : Row ℂ := [(1,12)]
abbrev instructionsRow026 (X Y Z W a b : ℂ) : Row ℂ := [(1,13)]
abbrev instructionsRow027 (X Y Z W a b : ℂ) : Row ℂ := [(1,15)]
abbrev instructionsRow028 (X Y Z W a b : ℂ) : Row ℂ := [(1,16)]
abbrev instructionsRow029 (X Y Z W a b : ℂ) : Row ℂ := [(1,17)]
abbrev instructionsRow030 (X Y Z W a b : ℂ) : Row ℂ := [(1,18)]
abbrev instructionsRow031 (X Y Z W a b : ℂ) : Row ℂ := [(1,19)]
abbrev instructionsRow032 (X Y Z W a b : ℂ) : Row ℂ := [(1,20)]
abbrev instructionsRow033 (X Y Z W a b : ℂ) : Row ℂ := [(W / Z,21)]
abbrev instructionsRow034 (X Y Z W a b : ℂ) : Row ℂ := [(Z / W,24)]
abbrev instructionsRow035 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 * W / (Y ^ 2 * Z),25)]
abbrev instructionsRow036 (X Y Z W a b : ℂ) : Row ℂ := [(W / (X ^ 2 * Z),26)]
abbrev instructionsRow037 (X Y Z W a b : ℂ) : Row ℂ := [(1,27)]
abbrev instructionsRow038 (X Y Z W a b : ℂ) : Row ℂ := [(Y ^ 2 / (Z * W),28)]
abbrev instructionsRow039 (X Y Z W a b : ℂ) : Row ℂ := [(Z / (X ^ 2 * W),29)]
abbrev instructionsRow040 (X Y Z W a b : ℂ) : Row ℂ := [(W / (Y ^ 2 * Z),30)]
abbrev instructionsRow041 (X Y Z W a b : ℂ) : Row ℂ := [(Z / (Y ^ 2 * W),32)]
abbrev instructionsRow042 (X Y Z W a b : ℂ) : Row ℂ := [(Y ^ 2 / (X ^ 2 * Z * W),33)]
abbrev instructionsRow043 (X Y Z W a b : ℂ) : Row ℂ := [(W / (X ^ 2 * Y ^ 2 * Z),34),((W / (X ^ 2 * Y ^ 2 * Z))*(-(1)),244)]
abbrev instructionsRow044 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / Y ^ 2,37)]
abbrev instructionsRow045 (X Y Z W a b : ℂ) : Row ℂ := [(1,38)]
abbrev instructionsRow046 (X Y Z W a b : ℂ) : Row ℂ := [(1,44),(-(-1 / X ^ 2),255)]
abbrev instructionsRow047 (X Y Z W a b : ℂ) : Row ℂ := [(1,45),(-(-1 * X ^ 2),232)]
abbrev instructionsRow048 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / (X ^ 2 * Y ^ 2),46)]
abbrev instructionsRow049 (X Y Z W a b : ℂ) : Row ℂ := [(1,47),(-(-1 * Y ^ 2),251)]
abbrev instructionsRow050 (X Y Z W a b : ℂ) : Row ℂ := [(1,48),(-(-1 * X ^ 2),252)]
abbrev instructionsRow051 (X Y Z W a b : ℂ) : Row ℂ := [(1,49),(-(-1 * Y ^ 2 / X ^ 2),255)]
abbrev instructionsRow052 (X Y Z W a b : ℂ) : Row ℂ := [(1,50)]
abbrev instructionsRow053 (X Y Z W a b : ℂ) : Row ℂ := [(1,51)]
abbrev instructionsRow054 (X Y Z W a b : ℂ) : Row ℂ := [(1,52),(-(-1 * X ^ 2 / Y ^ 2),246)]
abbrev instructionsRow055 (X Y Z W a b : ℂ) : Row ℂ := [(1,53),(-(-1),248)]
abbrev instructionsRow056 (X Y Z W a b : ℂ) : Row ℂ := [(1,54)]
abbrev instructionsRow057 (X Y Z W a b : ℂ) : Row ℂ := [(1,55),(-(-1 * X ^ 2),249)]
abbrev instructionsRow058 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / (X ^ 2 * Y ^ 2),56)]
abbrev instructionsRow059 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / (X ^ 2 * Y ^ 2),57)]
abbrev instructionsRow060 (X Y Z W a b : ℂ) : Row ℂ := [(1,58)]
abbrev instructionsRow061 (X Y Z W a b : ℂ) : Row ℂ := [(1,59),(-(-1 * X ^ 2 / Y ^ 2),241)]
abbrev instructionsRow062 (X Y Z W a b : ℂ) : Row ℂ := [(1,60)]
abbrev instructionsRow063 (X Y Z W a b : ℂ) : Row ℂ := [(1,61)]
abbrev instructionsRow064 (X Y Z W a b : ℂ) : Row ℂ := [(1,62)]
abbrev instructionsRow065 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / (X ^ 2 * Y ^ 2),63)]
abbrev instructionsRow066 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * Z / W,64),((-1 * Z / W)*(-(-1 * X ^ 2 * Y ^ 2)),253),((-1 * Z / W)*(-(1)),243)]
abbrev instructionsRow067 (X Y Z W a b : ℂ) : Row ℂ := [(1,67),(-(-1 * X ^ 2 / Y ^ 2),252)]
abbrev instructionsRow068 (X Y Z W a b : ℂ) : Row ℂ := [(1,68),(-(-1 * Y ^ 2 / X ^ 2),255)]
abbrev instructionsRow069 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / (X ^ 2 * Y ^ 2),69)]
abbrev instructionsRow070 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / Y ^ 2,70)]
abbrev instructionsRow071 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / X ^ 2,71)]
abbrev instructionsRow072 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X ^ 2 / Y ^ 2,72)]
abbrev instructionsRow073 (X Y Z W a b : ℂ) : Row ℂ := [(1,73)]
abbrev instructionsRow074 (X Y Z W a b : ℂ) : Row ℂ := [(1,74)]
abbrev instructionsRow075 (X Y Z W a b : ℂ) : Row ℂ := [(1,75)]
abbrev instructionsRow076 (X Y Z W a b : ℂ) : Row ℂ := [(1,76)]
abbrev instructionsRow077 (X Y Z W a b : ℂ) : Row ℂ := [(1,77)]
abbrev instructionsRow078 (X Y Z W a b : ℂ) : Row ℂ := [(1,78)]
abbrev instructionsRow079 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / X ^ 2,79)]
abbrev instructionsRow080 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / Y ^ 2,80),((-1 / Y ^ 2)*(-(1)),248)]
abbrev instructionsRow081 (X Y Z W a b : ℂ) : Row ℂ := [(1,81)]
abbrev instructionsRow082 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2),149),((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-((-1 * X ^ 2 * Y ^ 2 + -1 * Y ^ 2) / (X ^ 2 * Z * W))),291),((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-(1)),265),((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-(-1 * a / X)),239),((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-(1)),235),((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-(1 / X ^ 2)),231)]
abbrev instructionsRow083 (X Y Z W a b : ℂ) : Row ℂ := [(1,82),(-(1 / (X ^ 2 * Z * W)),292),(-(1 / (X ^ 2 * Z * W)),210)]
abbrev instructionsRow084 (X Y Z W a b : ℂ) : Row ℂ := [(1,83),(-(-1 / (X ^ 2 * Z * W)),292),(-(1 / (X ^ 2 * Z * W)),291),(-(1 / (X ^ 2 * Z * W)),210)]
abbrev instructionsRow085 (X Y Z W a b : ℂ) : Row ℂ := [(1,84),(-(-1 / (Z * W)),292),(-(1 / (Z * W)),291),(-(1 / (Z * W)),210)]
abbrev instructionsRow086 (X Y Z W a b : ℂ) : Row ℂ := [(1,85),(-(1 / (Z * W)),292),(-(1 / (Z * W)),210)]
abbrev instructionsRow087 (X Y Z W a b : ℂ) : Row ℂ := [(1,86),(-(X ^ 2 / (Z * W)),229),(-(X ^ 2 / (Z * W)),220)]
abbrev instructionsRow088 (X Y Z W a b : ℂ) : Row ℂ := [(1,87),(-(X ^ 2 / (Z * W)),230),(-(X ^ 2 / (Z * W)),220)]
abbrev instructionsRow089 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 * Y ^ 2,144),((X ^ 2 * Y ^ 2)*(-(1)),256),((X ^ 2 * Y ^ 2)*(-(1 / X ^ 2)),254),((X ^ 2 * Y ^ 2)*(-(-1 * a / X)),222),((X ^ 2 * Y ^ 2)*(-(1)),214)]
abbrev instructionsRow090 (X Y Z W a b : ℂ) : Row ℂ := [(1,156),(-(-1 * Y ^ 2 / (Z * W)),292),(-(1),239),(-(-1 * a / X),231)]
abbrev instructionsRow091 (X Y Z W a b : ℂ) : Row ℂ := [(1,168),(-((X * Y ^ 2 * a + Y ^ 2) / (X ^ 2 * Z * W)),292),(-(-1 * Y ^ 2 / (X ^ 2 * Z * W)),291),(-(-1 * a / X),260),(-(1 / X ^ 2),248)]
abbrev instructionsRow092 (X Y Z W a b : ℂ) : Row ℂ := [(1,171),(-(-1 * a / X),219),(-(1 / X ^ 2),212)]
abbrev instructionsRow093 (X Y Z W a b : ℂ) : Row ℂ := [(1,172),(-(-1 * a / X),227),(-(1 / X ^ 2),217)]
abbrev instructionsRow094 (X Y Z W a b : ℂ) : Row ℂ := [(1,173),(-(-1 * a / X),225),(-(1 / X ^ 2),214)]
abbrev instructionsRow095 (X Y Z W a b : ℂ) : Row ℂ := [(1,174),(-(-1 * a / X),226),(-(1 / X ^ 2),216)]
abbrev instructionsRow096 (X Y Z W a b : ℂ) : Row ℂ := [(1,177),(-((-1 * X * Y ^ 2 * a + -1 * Y ^ 2) / (X ^ 2 * Z * W)),292),(-(Y ^ 2 * a / (X * Z * W)),291),(-(-1 * a / X),265),(-(1 / X ^ 2),239)]
abbrev instructionsRow097 (X Y Z W a b : ℂ) : Row ℂ := [(1,183),(-(Y ^ 2 / (Z * W)),292),(-(-1 * Y ^ 2 / (Z * W)),291),(-(1),248),(-(-1 * a / X),228)]
abbrev instructionsRow098 (X Y Z W a b : ℂ) : Row ℂ := [(1,193),(-(-1 * b / Y),231),(-(1 / Y ^ 2),226),(-(1),223)]
abbrev instructionsRow099 (X Y Z W a b : ℂ) : Row ℂ := [(1,206),(-(-1 * b / Y),228),(-(1),224),(-(1 / Y ^ 2),219)]
abbrev instructionsRow100 (X Y Z W a b : ℂ) : Row ℂ := [(1,94),(-(-1 * W / Z),276),(-(1),243)]
abbrev instructionsRow101 (X Y Z W a b : ℂ) : Row ℂ := [(1,111),(-(-1 * Z / W),310),(-(1),276),(-(1),267),(-(1),259),(-(1),244)]
abbrev instructionsRow102 (X Y Z W a b : ℂ) : Row ℂ := [(1,124),(-(-1 * W / (X ^ 2 * Z)),311),(-(1),247),(-(1),246),(-(1),241)]
abbrev instructionsRow103 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2,145),((X ^ 2)*(-(-1 * a / (X * Y ^ 2))),299),((X ^ 2)*(-(1)),262),((X ^ 2)*(-(-1 * a / X)),254),((X ^ 2)*(-(1)),222)]
abbrev instructionsRow104 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X ^ 2,146),((-1 * X ^ 2)*(-(-1 * Z / (Y ^ 2 * W))),312),((-1 * X ^ 2)*(-(Z * a / (X * Y ^ 2 * W))),310),((-1 * X ^ 2)*(-(1 / (X ^ 2 * Y ^ 2))),276),((-1 * X ^ 2)*(-(1)),257),((-1 * X ^ 2)*(-(-1 * Z / (X ^ 2 * Y ^ 2 * W))),243),((-1 * X ^ 2)*(-(1 / X ^ 2)),240),((-1 * X ^ 2)*(-(-1 * a / X)),236),((-1 * X ^ 2)*(-(1)),233)]
abbrev instructionsRow105 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2),178),((X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2))*(-(-1 * Y ^ 2 * W / (X ^ 2 * Z))),314),((X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2))*(-(-1 * W / Z)),276),((X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2))*(-(1)),247),((X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2))*(-(1)),243)]
abbrev instructionsRow106 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X ^ 2,153),((-1 * X ^ 2)*(-((2 * X * Z + Z * a) / (X * W))),315),((-1 * X ^ 2)*(-(1 / X ^ 2)),311),((-1 * X ^ 2)*(-(-1 * Z / W)),310),((-1 * X ^ 2)*(-(-1 * a / X)),276),((-1 * X ^ 2)*(-(1)),267),((-1 * X ^ 2)*(-(1)),238)]
abbrev instructionsRow107 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * Y ^ 2 * Z / W,147),((-1 * Y ^ 2 * Z / W)*(-(W / (Y ^ 2 * Z))),316),((-1 * Y ^ 2 * Z / W)*(-((2 * X * a + 1) / (X ^ 2 * Y ^ 2))),315),((-1 * Y ^ 2 * Z / W)*(-(-1 * W / (Y ^ 2 * Z))),311),((-1 * Y ^ 2 * Z / W)*(-(-1 * a / (X * Y ^ 2))),310),((-1 * Y ^ 2 * Z / W)*(-(-1 * W / (X ^ 2 * Y ^ 2 * Z))),276),((-1 * Y ^ 2 * Z / W)*(-(W * a / (X * Y ^ 2 * Z))),267),((-1 * Y ^ 2 * Z / W)*(-(1)),264),((-1 * Y ^ 2 * Z / W)*(-(1 / X ^ 2)),242),((-1 * Y ^ 2 * Z / W)*(-(-1 * a / X)),237),((-1 * Y ^ 2 * Z / W)*(-(1)),234)]
abbrev instructionsRow108 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1),201),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(-1 * X ^ 2 * W / (Y ^ 2 * Z))),317),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(-1 * W / (Y ^ 2 * Z))),316),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-((Y ^ 2 + 2 * Y * b + 1) / Y ^ 2)),315),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(-1 * b / Y)),310),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(-1 * W / Z)),276),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(1)),271),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(1)),243),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(1)),242)]
abbrev instructionsRow109 (X Y Z W a b : ℂ) : Row ℂ := [(1,150),(-((X ^ 3 * Z + -1 * X * Z * a ^ 2 + Z * a) / (X * Y ^ 2 * W)),318),(-(1 / Y ^ 2),317),(-((-1 * X ^ 2 * Z * a + -2 * X * Z * a ^ 2 + 2 * X * Z + -1 * Z * a) / (X * Y ^ 2 * W)),315),(-(a / X),314),(-(X * Z * a / (Y ^ 2 * W)),312),(-(-1 * Z / (Y ^ 2 * W)),310),(-(1 / X ^ 2),282),(-(-1 * a / X),240),(-(1),236)]
abbrev instructionsRow110 (X Y Z W a b : ℂ) : Row ℂ := [(1,163),(-((X ^ 3 * Z * a + -1 * X * Z * a + Z) / (X ^ 2 * W)),318),(-(a / X),316),(-((-1 * X ^ 2 * Z + 2 * Z) / (X ^ 2 * W)),315),(-(-1 * a / X),311),(-(-1 * Z / (X ^ 2 * W)),310),(-(1),276),(-(1 / X ^ 2),267)]
abbrev instructionsRow111 (X Y Z W a b : ℂ) : Row ℂ := [(1,89),(-(1),320),(-((-1 * X ^ 2 * Z + Z) / (X ^ 2 * Y ^ 2 * W)),318),(-(-1 / (X ^ 2 * Y ^ 2)),316),(-(Z / (X ^ 2 * W)),315),(-(-1 / X ^ 2),276),(-(Z / (X ^ 2 * W)),271),(-(Z / (X ^ 2 * W)),243)]
abbrev instructionsRow112 (X Y Z W a b : ℂ) : Row ℂ := [(1,167),(-((X ^ 3 * Z + -1 * X * Z + Z * a) / (X * W)),318),(-(1),316),(-(-1 * Z / (X ^ 2 * W)),315),(-(-1 * a / X),259),(-(1 / X ^ 2),244)]
abbrev instructionsRow113 (X Y Z W a b : ℂ) : Row ℂ := [(1,127),(-(1),322),(-(1),320),(-((X ^ 3 * Z + -1 * X * Z + Z * a) / (X * W)),318),(-(1),317),(-(2 * Z / (X ^ 2 * W)),315),(-(-1 * Z / (X ^ 2 * W)),310),(-(1),249),(-(1),238)]
abbrev instructionsRow114 (X Y Z W a b : ℂ) : Row ℂ := [(1,88),(-(1),323),(-((X ^ 2 * Z + -1 * Z) / (X ^ 2 * Y ^ 2 * W)),318),(-(1 / (X ^ 2 * Y ^ 2)),316),(-(Z / (X ^ 2 * W)),315),(-(-1 / (X ^ 2 * Y ^ 2)),311),(-(Z / (X ^ 2 * W)),264)]
abbrev instructionsRow115 (X Y Z W a b : ℂ) : Row ℂ := [(1,186),(-(1 / Y ^ 2),322),(-((Z * a ^ 2 + -1 * Z) / (Y ^ 2 * W)),318),(-((X ^ 2 * Z * a + 2 * X * Z * a ^ 2 + Z * a) / (X * Y ^ 2 * W)),315),(-(-1 * a / X),314),(-(1 / X ^ 2),283),(-(1),251)]
abbrev instructionsRow116 (X Y Z W a b : ℂ) : Row ℂ := [(1,190),(-((X ^ 2 * Y * b + -1 * X * Y ^ 2 * a + X * a + -1 * Y * b) / (X ^ 2 * Y ^ 2)),318),(-(W * b / (X ^ 2 * Y * Z)),316),(-((-1 * X ^ 2 * Y ^ 2 + X ^ 2 + -2 * X * Y ^ 2 * a + 2 * X * a + -1 * Y ^ 2 + 2) / (X ^ 2 * Y ^ 2)),315),(-((Y ^ 2 * W + -1 * W) / (X ^ 2 * Z)),314),(-(1),312),(-(-1 * W / (X ^ 2 * Y ^ 2 * Z)),276),(-(1 / Y ^ 2),247),(-(-1 * b / Y),241),(-(1),234)]
abbrev instructionsRow117 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 * Z / W,90),((X ^ 2 * Z / W)*(-(1)),326),((X ^ 2 * Z / W)*(-((-1 * X * a + 1) / X ^ 2)),318),((X ^ 2 * Z / W)*(-((-1 * X ^ 2 + -2 * X * a + 1) / X ^ 2)),315),((X ^ 2 * Z / W)*(-(Y ^ 2 * W / (X ^ 2 * Z))),314),((X ^ 2 * Z / W)*(-(1)),312),((X ^ 2 * Z / W)*(-(-1 / X ^ 2)),310),((X ^ 2 * Z / W)*(-(W / (X ^ 2 * Z))),267)]
abbrev instructionsRow118 (X Y Z W a b : ℂ) : Row ℂ := [(1,170),(-(1),327),(-(-1 * Z / (X ^ 2 * Y ^ 2 * W)),318),(-(Z * a / (X * Y ^ 2 * W)),315),(-(-1 * a / (X * Y ^ 2)),276),(-(-1 * a / X),272),(-(1 / X ^ 2),251)]
abbrev instructionsRow119 (X Y Z W a b : ℂ) : Row ℂ := [(1,191),(-((X ^ 2 * Z + -1 * Z) / W),318),(-(1),316),(-((Y * Z * b + 2 * Z) / (Y ^ 2 * W)),315),(-(-1 * Z / (Y ^ 2 * W)),310),(-(-1 * b / Y),276),(-(1 / Y ^ 2),259),(-(1),236)]
abbrev instructionsRow120 (X Y Z W a b : ℂ) : Row ℂ := [(W / Z,92),((W / Z)*(-(1)),329),((W / Z)*(-(X ^ 2 * Z / W)),318),((W / Z)*(-(1)),316)]
abbrev instructionsRow121 (X Y Z W a b : ℂ) : Row ℂ := [(1,128),(-(1),330),(-(-1 * X ^ 2 * W / (Y ^ 2 * Z)),322),(-((-1 * X ^ 4 + X ^ 2 + -1 * X * a) / Y ^ 2),318),(-(-1 * X ^ 2 * W / (Y ^ 2 * Z)),317),(-(-2 / Y ^ 2),315),(-(-1 * W / (Y ^ 2 * Z)),311),(-(1 / Y ^ 2),310),(-(1),271),(-(-1 * W / (Y ^ 2 * Z)),267),(-(1),264),(-(-1 * W / (Y ^ 2 * Z)),259),(-(1),250),(-(1),245),(-(1),242),(-(1),237)]
abbrev instructionsRow122 (X Y Z W a b : ℂ) : Row ℂ := [(1,93),(-(Z / W),331),(-(-1 * X ^ 2 * Z / W),318),(-(-1),316),(-(-2 * Z / W),315),(-(1),311),(-(Z / W),310)]
abbrev instructionsRow123 (X Y Z W a b : ℂ) : Row ℂ := [(1,135),(-(1),332),(-(1),329),(-(1),327),(-(X ^ 2 / Y ^ 2),322),(-((X ^ 4 * Z + -1 * X ^ 2 * Z + X * Z * a) / (Y ^ 2 * W)),318),(-(X ^ 2 / Y ^ 2),317),(-(-1 * X ^ 2 * Z / (Y ^ 2 * W)),312),(-(-1 * Z / (Y ^ 2 * W)),310),(-(1),283),(-(1),282),(-(1 / Y ^ 2),276),(-(1),272),(-(1),257),(-(1),251),(-(1),240),(-(1),236)]
abbrev instructionsRow124 (X Y Z W a b : ℂ) : Row ℂ := [(1,91),(-(W / (X ^ 2 * Z)),333),(-((X * a + -1) / X ^ 2),318),(-((X ^ 2 + 2 * X * a + 1) / X ^ 2),315),(-(-1 * Y ^ 2 * W / (X ^ 2 * Z)),314),(-(W / (X ^ 2 * Z)),259),(-(1),247)]
abbrev instructionsRow125 (X Y Z W a b : ℂ) : Row ℂ := [(1,152),(-(1 / X ^ 2),330),(-((X ^ 3 * a + -1 * X * a + a ^ 2 + -1) / Y ^ 2),318),(-(X * W * a / (Y ^ 2 * Z)),317),(-(-2 / Y ^ 2),315),(-(1 / Y ^ 2),310),(-(-1 * W / (Y ^ 2 * Z)),267),(-(-1 * a / X),242),(-(1),237)]
abbrev instructionsRow126 (X Y Z W a b : ℂ) : Row ℂ := [(1,158),(-(1 / X ^ 2),329),(-((-1 * X ^ 3 * Z * a + 2 * X * Z * a + -1 * Z * a ^ 2) / (Y ^ 2 * W)),318),(-(-1 * X * a / Y ^ 2),317),(-((X ^ 2 * Z + 2 * X * Z * a + Z) / (Y ^ 2 * W)),315),(-(-1),314),(-(-1 * X ^ 2 * Z / (Y ^ 2 * W)),312),(-(-1 * a / X),282),(-(1),240)]
abbrev instructionsRow127 (X Y Z W a b : ℂ) : Row ℂ := [(1,161),(-(1),332),(-(-1 * a / X),327),(-(-1 * Z / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / (X ^ 2 * Y ^ 2)),276),(-(1 / X ^ 2),272)]
abbrev instructionsRow128 (X Y Z W a b : ℂ) : Row ℂ := [(1,169),(-(1),331),(-((X ^ 3 * a + -1 * X * a + 1) / (X ^ 2 * Y ^ 2)),318),(-(W * a / (X * Y ^ 2 * Z)),316),(-(-1 * a / X),271),(-(-1 * W / (X ^ 2 * Y ^ 2 * Z)),259),(-(1 / X ^ 2),250)]
abbrev instructionsRow129 (X Y Z W a b : ℂ) : Row ℂ := [(1,175),(-(1),333),(-(Z / (X ^ 2 * Y ^ 2 * W)),318),(-((X * Z * a + 2 * Z) / (X ^ 2 * Y ^ 2 * W)),315),(-(-1 * Z / (X ^ 2 * Y ^ 2 * W)),310),(-(-1 * a / X),257),(-(1 / X ^ 2),236)]
abbrev instructionsRow130 (X Y Z W a b : ℂ) : Row ℂ := [(1,176),(-(1),330),(-((-1 * X ^ 3 * a + X * a + -1) / (X ^ 2 * Y ^ 2)),318),(-(-1 * W * a / (X * Y ^ 2 * Z)),316),(-(-2 / (X ^ 2 * Y ^ 2)),315),(-(W * a / (X * Y ^ 2 * Z)),311),(-(1 / (X ^ 2 * Y ^ 2)),310),(-(-1 * W / (X ^ 2 * Y ^ 2 * Z)),267),(-(-1 * a / X),264),(-(1 / X ^ 2),237)]
abbrev instructionsRow131 (X Y Z W a b : ℂ) : Row ℂ := [(1,138),(-(1),340),(-(1),338),(-(1),335),(-(1),334),(-(1),326),(-(2 / (X ^ 2 * Y ^ 2)),315),(-(-1 * W / (X ^ 2 * Y ^ 2 * Z)),276),(-(1),253),(-(1),234)]
abbrev instructionsRow132 (X Y Z W a b : ℂ) : Row ℂ := [(1,181),(-(-1 * a / X),333),(-(1),329),(-(-1 * Z / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / X ^ 2),257)]
abbrev instructionsRow133 (X Y Z W a b : ℂ) : Row ℂ := [(1,142),(-(1),342),(-(1),339),(-(1),337),(-(1),336),(-(1),328),(-(1),325),(-(1),324),(-(1),321),(-(1),319),(-(-2 * Z / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / (X ^ 2 * Y ^ 2)),276),(-(-1 * Z / (X ^ 2 * Y ^ 2 * W)),243),(-(1),233),(-(1),232)]
abbrev instructionsRow134 (X Y Z W a b : ℂ) : Row ℂ := [(1,103),(-(-1 * Z / W),318),(-(-1 / W),315),(-(1 / W),310),(-(1),259),(-(1),228),(-(1 / W),210)]
abbrev instructionsRow135 (X Y Z W a b : ℂ) : Row ℂ := [(1,104),(-(Z / W),318),(-((2 * Z + -1) / W),315),(-((-1 * Z + 1) / W),310),(-(-1 / Z),276),(-(1),267),(-(1 / W),243),(-(1),231),(-(1 / W),210)]
abbrev instructionsRow136 (X Y Z W a b : ℂ) : Row ℂ := [(1,107),(-((-1 * X ^ 2 + 1) / W),318),(-(-1 / Z),316),(-(-1 * Z / W),315),(-(X ^ 2 / W),312),(-(-1 * Y ^ 2 / (Z * W)),292),(-(1),260),(-(X ^ 2 / W),247),(-(1),244),(-(X ^ 2 / W),241),(-(X ^ 2 / W),220)]
abbrev instructionsRow137 (X Y Z W a b : ℂ) : Row ℂ := [(1,108),(-((X ^ 2 + -1) / W),318),(-(1 / Z),316),(-(-1 * Z / W),315),(-(X ^ 2 / W),312),(-(-1 / Z),311),(-(Y ^ 2 / (Z * W)),292),(-(-1 * Y ^ 2 / (Z * W)),291),(-(1),276),(-(1),265),(-(X ^ 2 / W),247),(-(X ^ 2 / W),246),(-(X ^ 2 / W),220)]
abbrev instructionsRow138 (X Y Z W a b : ℂ) : Row ℂ := [(Y ^ 2 / W,109),((Y ^ 2 / W)*(-(1)),330),((Y ^ 2 / W)*(-(-1 * X ^ 2 * W / (Y ^ 2 * Z))),322),((Y ^ 2 / W)*(-((X ^ 2 * Z + -1 * X ^ 2 + -1 * Z + 1) / Y ^ 2)),318),((Y ^ 2 / W)*(-((Z * W + -1 * W) / (Y ^ 2 * Z))),316),((Y ^ 2 / W)*(-(1)),292),((Y ^ 2 / W)*(-(1)),271),((Y ^ 2 / W)*(-(1)),245),((Y ^ 2 / W)*(-(W / Y ^ 2)),226)]
abbrev instructionsRow139 (X Y Z W a b : ℂ) : Row ℂ := [(Y ^ 2 / W,110),((Y ^ 2 / W)*(-(1)),331),((Y ^ 2 / W)*(-((-1 * X ^ 4 + -1 * X ^ 2 * Z + 2 * X ^ 2 + -1 * X * a + Z + -1) / Y ^ 2)),318),((Y ^ 2 / W)*(-(-1 * X ^ 2 * W / (Y ^ 2 * Z))),317),((Y ^ 2 / W)*(-((-1 * Z * W + W) / (Y ^ 2 * Z))),316),((Y ^ 2 / W)*(-((Z * W + -1 * W) / (Y ^ 2 * Z))),311),((Y ^ 2 / W)*(-(W / Y ^ 2)),299),((Y ^ 2 / W)*(-(-1)),292),((Y ^ 2 / W)*(-(1)),291),((Y ^ 2 / W)*(-(1)),264),((Y ^ 2 / W)*(-(1)),242),((Y ^ 2 / W)*(-(W / Y ^ 2)),219)]
abbrev instructionsRow140 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 * Y ^ 2 / Z,119),((X ^ 2 * Y ^ 2 / Z)*(-(Z / (X ^ 2 * Y ^ 2))),349),((X ^ 2 * Y ^ 2 / Z)*(-(1)),342),((X ^ 2 * Y ^ 2 / Z)*(-(1)),336),((X ^ 2 * Y ^ 2 / Z)*(-(1)),328),((X ^ 2 * Y ^ 2 / Z)*(-(1)),325),((X ^ 2 * Y ^ 2 / Z)*(-(1)),321),((X ^ 2 * Y ^ 2 / Z)*(-(-1 * Z / (X ^ 2 * Y ^ 2))),318),((X ^ 2 * Y ^ 2 / Z)*(-(-2 * Z / (X ^ 2 * Y ^ 2))),315),((X ^ 2 * Y ^ 2 / Z)*(-(Z / (X ^ 2 * Y ^ 2))),310),((X ^ 2 * Y ^ 2 / Z)*(-(1 / (X ^ 2 * W))),292),((X ^ 2 * Y ^ 2 / Z)*(-(-1 / (X ^ 2 * W))),291),((X ^ 2 * Y ^ 2 / Z)*(-(Z / (X ^ 2 * Y ^ 2))),265),((X ^ 2 * Y ^ 2 / Z)*(-(1)),229),((X ^ 2 * Y ^ 2 / Z)*(-(Z / (X ^ 2 * Y ^ 2))),212)]
abbrev instructionsRow141 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 / Y ^ 2,106),((X ^ 2 / Y ^ 2)*(-(-1)),350),((X ^ 2 / Y ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),331),((X ^ 2 / Y ^ 2)*(-(1)),323),((X ^ 2 / Y ^ 2)*(-(1 / W)),318),((X ^ 2 / Y ^ 2)*(-(1 / (X ^ 2 * Z))),316),((X ^ 2 / Y ^ 2)*(-(-1 / (X ^ 2 * Z))),311),((X ^ 2 / Y ^ 2)*(-(1)),305),((X ^ 2 / Y ^ 2)*(-(1 / X ^ 2)),299),((X ^ 2 / Y ^ 2)*(-(-1 * Y ^ 2 / (X ^ 2 * W))),292),((X ^ 2 / Y ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),291),((X ^ 2 / Y ^ 2)*(-(1)),289),((X ^ 2 / Y ^ 2)*(-(1)),266),((X ^ 2 / Y ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),264),((X ^ 2 / Y ^ 2)*(-(-1 / (X ^ 2 * Z))),259),((X ^ 2 / Y ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),250)]
abbrev instructionsRow142 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 * Y ^ 2 / Z,120),((X ^ 2 * Y ^ 2 / Z)*(-(Z / (X ^ 2 * Y ^ 2))),348),((X ^ 2 * Y ^ 2 / Z)*(-(1)),343),((X ^ 2 * Y ^ 2 / Z)*(-(1)),339),((X ^ 2 * Y ^ 2 / Z)*(-(1)),337),((X ^ 2 * Y ^ 2 / Z)*(-(1)),324),((X ^ 2 * Y ^ 2 / Z)*(-(1)),319),((X ^ 2 * Y ^ 2 / Z)*(-(Z / (X ^ 2 * Y ^ 2))),318),((X ^ 2 * Y ^ 2 / Z)*(-(Z / (X ^ 2 * Y ^ 2))),299),((X ^ 2 * Y ^ 2 / Z)*(-(-1 / (X ^ 2 * W))),292),((X ^ 2 * Y ^ 2 / Z)*(-(Z / (X ^ 2 * Y ^ 2))),260),((X ^ 2 * Y ^ 2 / Z)*(-(1)),230),((X ^ 2 * Y ^ 2 / Z)*(-(Z / (X ^ 2 * Y ^ 2))),216)]
abbrev instructionsRow143 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5),204),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(-1 / (X ^ 2 * Y ^ 2))),352),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1 / (X ^ 2 * Y ^ 2))),350),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1 / (X ^ 2 * Y ^ 2))),347),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(-1 / (X ^ 2 * Y ^ 2))),346),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1 / Y ^ 2)),307),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-((Y ^ 2 + 1) / (X ^ 2 * Y ^ 2))),299),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1)),289),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1)),286),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1)),274),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(-1 * b / Y)),261)]
abbrev instructionsRow144 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X ^ 2,105),((-1 * X ^ 2)*(-((-2 * X ^ 2 + -1 * X * a + 1) / X ^ 2)),353),((-1 * X ^ 2)*(-(-1)),352),((-1 * X ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),330),((-1 * X ^ 2)*(-(1)),320),((-1 * X ^ 2)*(-(-1 / W)),318),((-1 * X ^ 2)*(-(-1 / (X ^ 2 * Z))),316),((-1 * X ^ 2)*(-(-2 / (X ^ 2 * W))),315),((-1 * X ^ 2)*(-(Y ^ 2 / X ^ 2)),313),((-1 * X ^ 2)*(-(1 / (X ^ 2 * W))),310),((-1 * X ^ 2)*(-(1)),302),((-1 * X ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),292),((-1 * X ^ 2)*(-(1)),278),((-1 * X ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),271),((-1 * X ^ 2)*(-(1)),270),((-1 * X ^ 2)*(-(-1 / (X ^ 2 * Z))),267),((-1 * X ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),237)]
abbrev instructionsRow145 (X Y Z W a b : ℂ) : Row ℂ := [(1,100),(-(1 / X ^ 2),354),(-(2 / X ^ 2),353),(-(1 / X ^ 2),352),(-(-1 / X ^ 2),347),(-((X ^ 4 * Z + -1 * X ^ 2 * Z + X * Z * a + 1) / (X ^ 2 * W)),318),(-(1),317),(-(2 / (X ^ 2 * W)),315),(-(1),300),(-(1),281),(-(-1 / (X ^ 2 * Z)),276),(-(1 / (X ^ 2 * W)),243),(-(1 / (X ^ 2 * W)),210)]
abbrev instructionsRow146 (X Y Z W a b : ℂ) : Row ℂ := [(1,117),(-(-1),354),(-(-2),353),(-(Y ^ 2 / X ^ 2),351),(-(1 / X ^ 2),350),(-(-1 / X ^ 2),346),(-((X ^ 2 + -1 * X * W * a + -1) / (X ^ 2 * W)),318),(-(1 / (X ^ 2 * Z)),316),(-((-1 * X ^ 2 + -2 * X * a + -1) / X ^ 2),315),(-(Y ^ 2 * W / (X ^ 2 * Z)),314),(-(1),312),(-(-1 / (X ^ 2 * W)),310),(-(1),307),(-(1),306),(-(1),278),(-(1 / (X ^ 2 * Z)),276),(-(1 / (X ^ 2 * Z)),267),(-(1),266),(-(1 / (X ^ 2 * Z)),259),(-(1 / (X ^ 2 * Z)),244),(-(1 / (X ^ 2 * Z)),210)]
abbrev instructionsRow147 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * Y ^ 2 / Z,123),((-1 * Y ^ 2 / Z)*(-(Z / Y ^ 2)),354),((-1 * Y ^ 2 / Z)*(-(-2 * Z / Y ^ 2)),353),((-1 * Y ^ 2 / Z)*(-(-1 * Z / Y ^ 2)),352),((-1 * Y ^ 2 / Z)*(-(Z / Y ^ 2)),347),((-1 * Y ^ 2 / Z)*(-(Z / Y ^ 2)),344),((-1 * Y ^ 2 / Z)*(-(1)),333),((-1 * Y ^ 2 / Z)*(-(1)),332),((-1 * Y ^ 2 / Z)*(-((X ^ 4 * Z + -1 * X ^ 2 * Z) / (Y ^ 2 * W))),318),((-1 * Y ^ 2 / Z)*(-(X ^ 2 / Y ^ 2)),317),((-1 * Y ^ 2 / Z)*(-((-1 * X ^ 2 * Z + -2 * X * Z * a + Z * W + -2 * Z) / (Y ^ 2 * W))),315),((-1 * Y ^ 2 / Z)*(-(1)),314),((-1 * Y ^ 2 / Z)*(-(-1)),292),((-1 * Y ^ 2 / Z)*(-(1)),291),((-1 * Y ^ 2 / Z)*(-(1)),282),((-1 * Y ^ 2 / Z)*(-(1 / Y ^ 2)),276),((-1 * Y ^ 2 / Z)*(-(1)),272),((-1 * Y ^ 2 / Z)*(-(Z / Y ^ 2)),223),((-1 * Y ^ 2 / Z)*(-(Z / Y ^ 2)),219)]
abbrev instructionsRow148 (X Y Z W a b : ℂ) : Row ℂ := [(1,99),(-(1 / X ^ 2),357),(-(-2 / X ^ 2),353),(-(1 / X ^ 2),350),(-(-1 / X ^ 2),346),(-(1),322),(-(-1 / (X ^ 2 * W)),318),(-(1 / (X ^ 2 * W)),310),(-(1),307),(-(1),284),(-(-1 / (X ^ 2 * Z)),276),(-(1 / (X ^ 2 * W)),243),(-(1 / (X ^ 2 * W)),210)]
abbrev instructionsRow149 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 / Y ^ 2,116),((X ^ 2 / Y ^ 2)*(-(-1)),357),((X ^ 2 / Y ^ 2)*(-(-1 / X ^ 2)),354),((X ^ 2 / Y ^ 2)*(-((-1 * X * a + 1) / X ^ 2)),353),((X ^ 2 / Y ^ 2)*(-(1 / X ^ 2)),352),((X ^ 2 / Y ^ 2)*(-(-1 / X ^ 2)),347),((X ^ 2 / Y ^ 2)*(-((-1 * X ^ 2 + X * W * a + 1) / (X ^ 2 * W))),318),((X ^ 2 / Y ^ 2)*(-(-1 / (X ^ 2 * Z))),316),((X ^ 2 / Y ^ 2)*(-((X ^ 2 + 2 * X * a + 1) / X ^ 2)),315),((X ^ 2 / Y ^ 2)*(-(-1 * Y ^ 2 * W / (X ^ 2 * Z))),314),((X ^ 2 / Y ^ 2)*(-(Y ^ 2 / X ^ 2)),313),((X ^ 2 / Y ^ 2)*(-(1 / (X ^ 2 * Z))),311),((X ^ 2 / Y ^ 2)*(-(-1 / (X ^ 2 * W))),310),((X ^ 2 / Y ^ 2)*(-(1)),301),((X ^ 2 / Y ^ 2)*(-(1)),300),((X ^ 2 / Y ^ 2)*(-(1 / X ^ 2)),299),((X ^ 2 / Y ^ 2)*(-(1)),289),((X ^ 2 / Y ^ 2)*(-(1)),288),((X ^ 2 / Y ^ 2)*(-(1 / (X ^ 2 * Z))),276),((X ^ 2 / Y ^ 2)*(-(1)),270),((X ^ 2 / Y ^ 2)*(-(1 / (X ^ 2 * Z))),267),((X ^ 2 / Y ^ 2)*(-(1 / (X ^ 2 * Z))),259),((X ^ 2 / Y ^ 2)*(-(1)),247),((X ^ 2 / Y ^ 2)*(-(1 / (X ^ 2 * Z))),244),((X ^ 2 / Y ^ 2)*(-(1 / (X ^ 2 * Z))),210)]
abbrev instructionsRow150 (X Y Z W a b : ℂ) : Row ℂ := [(1,121),(-(1),358),(-(1 / X ^ 2),354),(-((2 * X ^ 2 + 1) / X ^ 2),353),(-(-1),350),(-(Y ^ 2 / (X ^ 2 * Z)),333),(-(Y ^ 2 / (X ^ 2 * Z)),332),(-((X ^ 4 + X ^ 2 * W + -1 * X ^ 2 + X * a + -1 * W + 1) / (X ^ 2 * W)),318),(-(1 / Z),317),(-(W / (X ^ 2 * Z)),316),(-(1 / (X ^ 2 * W)),315),(-(-1 * W / (X ^ 2 * Z)),311),(-(-1 / (X ^ 2 * W)),310),(-(1),305),(-(-1 * Y ^ 2 / (X ^ 2 * Z)),292),(-(Y ^ 2 / (X ^ 2 * Z)),291),(-(Y ^ 2 / (X ^ 2 * Z)),282),(-(1),281),(-(1 / (X ^ 2 * Z)),276),(-(Y ^ 2 / (X ^ 2 * Z)),272),(-(1),261),(-(1),246),(-(Y ^ 2 / (X ^ 2 * Z)),236)]
abbrev instructionsRow151 (X Y Z W a b : ℂ) : Row ℂ := [(1,122),(-(1 / X ^ 2),357),(-(1),355),(-((-2 * X ^ 2 + -1) / X ^ 2),353),(-(-1),352),(-(Y ^ 2 / (X ^ 2 * Z)),329),(-(Y ^ 2 / (X ^ 2 * Z)),327),(-(1 / Z),322),(-((-1 * X ^ 2 * W + W + -1) / (X ^ 2 * W)),318),(-(-1 * W / (X ^ 2 * Z)),316),(-(-1 / (X ^ 2 * W)),315),(-(1),302),(-(1 / X ^ 2),299),(-(Y ^ 2 / (X ^ 2 * Z)),292),(-(1),284),(-(Y ^ 2 / (X ^ 2 * Z)),283),(-(1),263),(-(Y ^ 2 / (X ^ 2 * Z)),257),(-(Y ^ 2 / (X ^ 2 * Z)),251),(-(1),241)]
abbrev instructionsRow152 (X Y Z W a b : ℂ) : Row ℂ := [(1,148),(-(1 / X ^ 2),359),(-(a / (X * Y ^ 2)),354),(-((a ^ 2 + -1) / Y ^ 2),353),(-(-1 * a / X),313),(-(1 / Y ^ 2),299),(-(1),254)]
abbrev instructionsRow153 (X Y Z W a b : ℂ) : Row ℂ := [(1,129),(-(1),362),(-(Y ^ 2 / X ^ 2),359),(-(-1),354),(-((Y ^ 2 + 1) / (X ^ 2 * Y ^ 2)),353),(-(1 / (X ^ 2 * Y ^ 2)),349),(-(1 / (X ^ 2 * W)),331),(-(1),328),(-((-1 * X ^ 4 + X ^ 2 + -1 * X * a + -1 * Y ^ 2 * Z + 1) / (X ^ 2 * Y ^ 2 * W)),318),(-(-1 / (Y ^ 2 * Z)),317),(-(-1 / (X ^ 2 * W)),315),(-(1 / (X ^ 2 * W)),310),(-(1),306),(-(-1 / (X ^ 2 * W)),292),(-(1 / (X ^ 2 * W)),291),(-(1),288),(-(-1 / (X ^ 2 * Z)),276),(-(1),268),(-(1),261),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),259),(-(1 / (X ^ 2 * W)),250),(-(1 / (X ^ 2 * W)),243),(-(1 / (X ^ 2 * W)),242),(-(1),238),(-(1 / (X ^ 2 * W)),210)]
abbrev instructionsRow154 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2,165),((X ^ 2)*(-((2 * X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + 2) / (X ^ 2 * Y ^ 2))),353),((X ^ 2)*(-(1)),352),((X ^ 2)*(-(-1 / (X ^ 2 * Y ^ 2))),350),((X ^ 2)*(-(a / X)),349),((X ^ 2)*(-(-1)),347),((X ^ 2)*(-(1 / (X ^ 2 * Y ^ 2))),346),((X ^ 2)*(-(-1 * a / X)),297),((X ^ 2)*(-(1)),295),((X ^ 2)*(-(1)),279)]
abbrev instructionsRow155 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2,179),((X ^ 2)*(-((-2 * X ^ 2 * Y ^ 2 + -1 * X * Y ^ 2 * a + -2) / (X ^ 2 * Y ^ 2))),353),((X ^ 2)*(-(-1 / (X ^ 2 * Y ^ 2))),352),((X ^ 2)*(-(1)),350),((X ^ 2)*(-(a / X)),348),((X ^ 2)*(-(1 / (X ^ 2 * Y ^ 2))),347),((X ^ 2)*(-(-1)),346),((X ^ 2)*(-(-1 * a / X)),298),((X ^ 2)*(-(1)),296),((X ^ 2)*(-(1)),286)]
abbrev instructionsRow156 (X Y Z W a b : ℂ) : Row ℂ := [(1,187),(-(1 / Y ^ 2),356),(-((2 * X ^ 2 * a + X + -1 * a) / (X * Y ^ 2)),353),(-(-1 * a / X),351),(-(1 / X ^ 2),287),(-(1),255)]
abbrev instructionsRow157 (X Y Z W a b : ℂ) : Row ℂ := [(1,130),(-(1),366),(-(-1),357),(-(1),356),(-((-1 * Y ^ 2 + -1) / (X ^ 2 * Y ^ 2)),353),(-(1 / (X ^ 2 * Y ^ 2)),348),(-(1),339),(-(1 / (X ^ 2 * W)),330),(-(-1 / (Y ^ 2 * Z)),322),(-((Y ^ 2 * Z + -1) / (X ^ 2 * Y ^ 2 * W)),318),(-((2 * Y ^ 2 * Z + -1 * Y ^ 2 + -2) / (X ^ 2 * Y ^ 2 * W)),315),(-((-1 * Y ^ 2 * Z + Y ^ 2 + 1) / (X ^ 2 * Y ^ 2 * W)),310),(-(1),301),(-(1 / X ^ 2),299),(-(1 / (X ^ 2 * W)),292),(-(1),269),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),267),(-(1),263),(-(1),249),(-(1 / (X ^ 2 * W)),245),(-(1 / (X ^ 2 * W)),237),(-(1 / (X ^ 2 * W)),210)]
abbrev instructionsRow158 (X Y Z W a b : ℂ) : Row ℂ := [(1,192),(-(1),355),(-((Y * b + 3) / (X ^ 2 * Y ^ 2)),353),(-(-1 / (X ^ 2 * Y ^ 2)),350),(-(1 / (X ^ 2 * Y ^ 2)),346),(-(-1 * b / (X ^ 2 * Y)),299),(-(-1 * b / Y),289),(-(1),275),(-(1 / Y ^ 2),261)]
abbrev instructionsRow159 (X Y Z W a b : ℂ) : Row ℂ := [(1,194),(-(-1),357),(-(-1 * b / (X ^ 2 * Y)),354),(-(-2 / Y ^ 2),353),(-(1 / X ^ 2),351),(-(1 / (X ^ 2 * Y ^ 2)),348),(-(1),301),(-(-1 * b / Y),281),(-(1),269),(-(1 / Y ^ 2),266)]
abbrev instructionsRow160 (X Y Z W a b : ℂ) : Row ℂ := [(1,195),(-(-1 * b / Y),357),(-(-1 / Y ^ 2),354),(-((-1 * X * a + 2 * Y ^ 2 + 1) / Y ^ 2),353),(-(1),352),(-(1 / Y ^ 2),349),(-(1),313)]
abbrev instructionsRow161 (X Y Z W a b : ℂ) : Row ℂ := [(1,166),(-(-1 * a / X),370),(-(1),364),(-(-2 / (X ^ 2 * Y ^ 2)),353),(-(1 / (X ^ 2 * Y ^ 2)),350),(-(1 / X ^ 2),285)]
abbrev instructionsRow162 (X Y Z W a b : ℂ) : Row ℂ := [(1,180),(-(1 / X ^ 2),370),(-(-1 * a / X),364),(-(-1),353),(-(-1),349),(-(1),297)]
abbrev instructionsRow163 (X Y Z W a b : ℂ) : Row ℂ := [(1,200),(-(1),366),(-(1),356),(-(-1 * b / Y),355),(-(-1 / (X ^ 2 * Y ^ 2)),353),(-(1 / (X ^ 2 * Y ^ 2)),299),(-(1 / Y ^ 2),289)]
abbrev instructionsRow164 (X Y Z W a b : ℂ) : Row ℂ := [(1,96),(-(1),373),(-(1),369),(-(1),336),(-(-1 / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / (X ^ 2 * Y ^ 2 * W)),310),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),276),(-(1 / (X ^ 2 * Y ^ 2 * W)),243),(-(1 / (X ^ 2 * Y ^ 2 * W)),210)]
abbrev instructionsRow165 (X Y Z W a b : ℂ) : Row ℂ := [(1,202),(-(1),363),(-((-2 * X ^ 2 + Y ^ 2 + 2 * Y * b) / (X ^ 2 * Y ^ 2)),353),(-(-1 / Y ^ 2),352),(-(-1 * b / (X ^ 2 * Y)),350),(-(b / (X ^ 2 * Y)),346),(-(-1 * b / Y),307),(-(1 / Y ^ 2),302),(-(1),261)]
abbrev instructionsRow166 (X Y Z W a b : ℂ) : Row ℂ := [(1,95),(-(1),375),(-(1),371),(-(1),343),(-(-1 / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / (X ^ 2 * Y ^ 2 * W)),310),(-(1 / (X ^ 2 * Y ^ 2 * W)),210)]
abbrev instructionsRow167 (X Y Z W a b : ℂ) : Row ℂ := [(1,203),(-(1 / Y ^ 2),360),(-((Y ^ 2 + 1) / (X ^ 2 * Y ^ 2)),357),(-(b / (X ^ 2 * Y)),354),(-(a * b / (X * Y)),353),(-(-1 * Y * b / X ^ 2),313),(-(1),284),(-(1),273),(-(-1 * b / Y),270)]
abbrev instructionsRow168 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2,164),((X ^ 2)*(-(1)),377),((X ^ 2)*(-(-1 * a / X)),365),((X ^ 2)*(-(1)),353),((X ^ 2)*(-(-1)),348),((X ^ 2)*(-(1)),298)]
abbrev instructionsRow169 (X Y Z W a b : ℂ) : Row ℂ := [(1,207),(-(1),358),(-((-1 * Y * b + -3) / (X ^ 2 * Y ^ 2)),353),(-(-1 / (X ^ 2 * Y ^ 2)),352),(-(1 / (X ^ 2 * Y ^ 2)),347),(-(1 / (X ^ 2 * Y ^ 2)),299),(-(-1 * b / Y),278),(-(1 / Y ^ 2),263),(-(1),258)]
abbrev instructionsRow170 (X Y Z W a b : ℂ) : Row ℂ := [(1,97),(-(1),370),(-(X ^ 2 / Y ^ 2),322),(-(1 / (Y ^ 2 * W)),318),(-(2 / (Y ^ 2 * W)),315),(-(1),283),(-(-1 / (Y ^ 2 * Z)),276),(-(1 / (Y ^ 2 * W)),243),(-(1 / (Y ^ 2 * W)),210)]
abbrev instructionsRow171 (X Y Z W a b : ℂ) : Row ℂ := [(1,98),(-(1),378),(-((X ^ 4 * Z + -1 * X ^ 2 * Z + X * Z * a + -1) / (Y ^ 2 * W)),318),(-(X ^ 2 / Y ^ 2),317),(-(1 / (Y ^ 2 * W)),310),(-(1),308),(-(1),282),(-(-1 / (Y ^ 2 * Z)),276),(-(1 / (Y ^ 2 * W)),243),(-(1 / (Y ^ 2 * W)),210)]
abbrev instructionsRow172 (X Y Z W a b : ℂ) : Row ℂ := [(1,101),(-(-2 / Y ^ 2),353),(-(1 / Y ^ 2),350),(-(1),332),(-(X * a / (Y ^ 2 * W)),318),(-((X ^ 2 + 2 * X * a + 1) / (Y ^ 2 * W)),315),(-(-1 / Z),314),(-(-1 / (Y ^ 2 * Z)),311),(-(1),285),(-(X ^ 2 / (Y ^ 2 * W)),247),(-(X ^ 2 / (Y ^ 2 * W)),246),(-(X ^ 2 / (Y ^ 2 * W)),241),(-(X ^ 2 / (Y ^ 2 * W)),220)]
abbrev instructionsRow173 (X Y Z W a b : ℂ) : Row ℂ := [(1,102),(-(2 / Y ^ 2),353),(-(1 / Y ^ 2),352),(-(1),329),(-(-1 * X * a / (Y ^ 2 * W)),318),(-((-1 * X ^ 2 + -2 * X * a + -1) / (Y ^ 2 * W)),315),(-(1 / Z),314),(-(X ^ 2 / (Y ^ 2 * W)),312),(-(-1 / (Y ^ 2 * Z)),311),(-(1),280),(-(X ^ 2 / (Y ^ 2 * W)),246),(-(X ^ 2 / (Y ^ 2 * W)),241),(-(X ^ 2 / (Y ^ 2 * W)),220)]
abbrev instructionsRow174 (X Y Z W a b : ℂ) : Row ℂ := [(1,112),(-(1),377),(-(1),368),(-(1),367),(-(1),341),(-(1 / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / (X ^ 2 * Y ^ 2 * Z)),311),(-(-1 / (X ^ 2 * Y ^ 2 * W)),310),(-(1 / (X ^ 2 * Y ^ 2 * Z)),267),(-(1 / (X ^ 2 * Y ^ 2 * Z)),259),(-(1 / (X ^ 2 * Y ^ 2 * Z)),244),(-(1 / (X ^ 2 * Y ^ 2 * Z)),210)]
abbrev instructionsRow175 (X Y Z W a b : ℂ) : Row ℂ := [(1,113),(-(1),379),(-(1),372),(-(1),363),(-(1),335),(-(1 / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / (X ^ 2 * Y ^ 2 * Z)),311),(-(-1 / (X ^ 2 * Y ^ 2 * W)),310),(-(1 / (X ^ 2 * Y ^ 2 * Z)),276),(-(1 / (X ^ 2 * Y ^ 2 * Z)),267),(-(1 / (X ^ 2 * Y ^ 2 * Z)),259),(-(1 / (X ^ 2 * Y ^ 2 * Z)),210)]
abbrev instructionsRow176 (X Y Z W a b : ℂ) : Row ℂ := [(1,125),(-(1),364),(-(-1 * X * Z * a / (Y ^ 2 * W)),318),(-((-1 * X ^ 2 * Z + -2 * X * Z * a + -1 * Z + -1) / (Y ^ 2 * W)),315),(-(1),314),(-(1 / (Y ^ 2 * W)),310),(-(-1 / (Y ^ 2 * Z)),276),(-(1 / (Y ^ 2 * W)),243),(-(1 / (Y ^ 2 * W)),210)]
abbrev instructionsRow177 (X Y Z W a b : ℂ) : Row ℂ := [(1,126),(-(1),365),(-(X * Z * a / (Y ^ 2 * W)),318),(-((X ^ 2 * Z + 2 * X * Z * a + Z + -1) / (Y ^ 2 * W)),315),(-(-1),314),(-(-1 * X ^ 2 * Z / (Y ^ 2 * W)),312),(-(1 / (Y ^ 2 * W)),310),(-(1),240),(-(1 / (Y ^ 2 * W)),210)]
abbrev instructionsRow178 (X Y Z W a b : ℂ) : Row ℂ := [(1,131),(-(-1 / Y ^ 2),354),(-((-1 * X * a + 2 * Y ^ 2) / Y ^ 2),353),(-(1),352),(-(-1 * X ^ 2 / (Y ^ 2 * Z)),322),(-((-1 * X ^ 2 + -1 * Y ^ 2) / (Y ^ 2 * W)),318),(-(-1 / (Y ^ 2 * Z)),316),(-((-1 * Y ^ 2 * Z + -1 * Z + -2) / (Y ^ 2 * W)),315),(-(1),313),(-((Y ^ 2 + 1) / (Y ^ 2 * W)),310),(-(1),309),(-((Y ^ 2 + Z) / (Z * W)),292),(-(-1 * Y ^ 2 / (Z * W)),291),(-((Y ^ 2 * Z + -1 * Y ^ 2 + Z) / (Y ^ 2 * Z)),276),(-(1),272),(-(1 / W),271),(-(-1 / (Y ^ 2 * Z)),267),(-(1),265),(-(1 / W),245),(-(1 / W),243),(-(1 / W),237),(-(1),224),(-(1 / W),210)]
abbrev instructionsRow179 (X Y Z W a b : ℂ) : Row ℂ := [(1,132),(-((-2 * X ^ 2 + -2 * Y ^ 2 + 1) / Y ^ 2),353),(-(1),351),(-(1),350),(-((-1 * X ^ 4 + 2 * X ^ 2 + -1 * X * a + Y ^ 2) / (Y ^ 2 * W)),318),(-(-1 * X ^ 2 / (Y ^ 2 * Z)),317),(-(1 / (Y ^ 2 * Z)),316),(-((-1 * Y ^ 2 * Z + 2 * Y ^ 2 + -1 * Z) / (Y ^ 2 * W)),315),(-(-1 / (Y ^ 2 * Z)),311),(-((-1 * Y ^ 2 + -1 * Z) / (Z * W)),292),(-(1 / W),291),(-(-1 / Z),276),(-(1 / W),264),(-(1),260),(-(-1 / (Y ^ 2 * Z)),259),(-(1),257),(-(1 / W),250),(-(1),244),(-(1 / W),243),(-(1 / W),242),(-(1),223),(-(1 / W),210)]
abbrev instructionsRow180 (X Y Z W a b : ℂ) : Row ℂ := [(1,133),(-(1),359),(-(-1),353),(-(X ^ 2 / W),341),(-(X ^ 2 / W),338),(-((-1 * X ^ 2 * Y ^ 2 * Z + -1 * X * Y ^ 2 * a + Y ^ 2 * Z + -1 * Z) / (Y ^ 2 * W)),318),(-(-1),316),(-((-1 * X ^ 2 * Y ^ 2 + -2 * X * Y ^ 2 * a + -1 * Y ^ 2 + 1) / (Y ^ 2 * W)),315),(-(Y ^ 2 / Z),314),(-(X ^ 2 / W),312),(-((Z + -1) / Z),311),(-(1),299),(-(-1 * Y ^ 2 / (Z * W)),292),(-(-1 / (Y ^ 2 * Z)),276),(-(1),251),(-(X ^ 2 / W),246),(-(X ^ 2 / W),241),(-(1),239),(-(X ^ 2 / W),234),(-(X ^ 2 / W),230),(-(X ^ 2 / W),220),(-(1),219)]
abbrev instructionsRow181 (X Y Z W a b : ℂ) : Row ℂ := [(1,134),(-(X ^ 2 / Y ^ 2),356),(-(1),353),(-(X ^ 2 / W),340),(-(X ^ 2 / W),335),(-((X ^ 2 * Y ^ 2 * Z + X * Y ^ 2 * a + -1 * Y ^ 2 * Z + Z) / (Y ^ 2 * W)),318),(-(1),316),(-((X ^ 2 * Y ^ 2 + 2 * X * Y ^ 2 * a + Y ^ 2 + 2 * Z + 1) / (Y ^ 2 * W)),315),(-(-1 * Y ^ 2 / Z),314),(-(-1 / Z),311),(-(-1 * Z / (Y ^ 2 * W)),310),(-(Y ^ 2 / (Z * W)),292),(-(-1 * Y ^ 2 / (Z * W)),291),(-(1),287),(-(X ^ 2 / W),253),(-(1),248),(-(X ^ 2 / W),247),(-(X ^ 2 / W),246),(-(X ^ 2 / W),241),(-(1),236),(-(X ^ 2 / W),229),(-(1),226),(-(X ^ 2 / W),220)]
abbrev instructionsRow182 (X Y Z W a b : ℂ) : Row ℂ := [(1,136),(-(1),374),(-((Y ^ 2 + 1) / (X ^ 2 * Y ^ 2)),357),(-(1),355),(-((-2 * X ^ 2 * Y ^ 2 + -1 * Y ^ 2 + 2) / (X ^ 2 * Y ^ 2)),353),(-(-1),352),(-(-1 / (X ^ 2 * Y ^ 2)),350),(-(1 / (X ^ 2 * Y ^ 2)),346),(-(1),340),(-(1 / (X ^ 2 * Z)),329),(-(1 / (Y ^ 2 * Z)),322),(-((-1 * X ^ 2 * Y ^ 2 * W + X * a + Y ^ 2 * W + -1 * Y ^ 2 + -1) / (X ^ 2 * Y ^ 2 * W)),318),(-(-1 * W / (X ^ 2 * Z)),316),(-((X ^ 2 + 2 * X * a + -2 * Y ^ 2) / (X ^ 2 * Y ^ 2 * W)),315),(-(-1 / (X ^ 2 * Z)),314),(-(-1 / (Y ^ 2 * W)),312),(-(1 / (X ^ 2 * Z)),311),(-(1),302),(-(1 / X ^ 2),299),(-((-1 * Y ^ 2 + W) / (X ^ 2 * Z * W)),292),(-(1),284),(-(1 / (X ^ 2 * Z)),283),(-(1 / (X ^ 2 * Z)),276),(-(1),275),(-(1),273),(-(1),263),(-(1 / (X ^ 2 * Z)),259),(-(1 / (X ^ 2 * Z)),257),(-(1),252),(-(1 / (X ^ 2 * Z)),251),(-(1 / (X ^ 2 * Z)),244),(-(1),241),(-(1 / (X ^ 2 * Z)),240),(-(1 / (X ^ 2 * Z)),210)]
abbrev instructionsRow183 (X Y Z W a b : ℂ) : Row ℂ := [(1,137),(-(1),375),(-(1),358),(-((Y ^ 2 + 1) / (X ^ 2 * Y ^ 2)),354),(-((2 * X ^ 2 * Y ^ 2 + Y ^ 2 + -2) / (X ^ 2 * Y ^ 2)),353),(-(-1 / (X ^ 2 * Y ^ 2)),352),(-(-1),350),(-(1 / (X ^ 2 * Y ^ 2)),347),(-(1),338),(-(1 / (X ^ 2 * Z)),332),(-((X ^ 4 + X ^ 2 * Y ^ 2 * W + -1 * X ^ 2 + -1 * Y ^ 2 * W + Y ^ 2 + 1) / (X ^ 2 * Y ^ 2 * W)),318),(-(1 / (Y ^ 2 * Z)),317),(-(W / (X ^ 2 * Z)),316),(-((-1 * X + -2 * a) / (X * Y ^ 2 * W)),315),(-(1 / (X ^ 2 * Z)),314),(-((-1 * W + 1) / (X ^ 2 * Z)),311),(-((-1 * Y ^ 2 + -1) / (X ^ 2 * Y ^ 2 * W)),310),(-(1),305),(-((Y ^ 2 + -1 * W) / (X ^ 2 * Z * W)),292),(-((-1 * Y ^ 2 + W) / (X ^ 2 * Z * W)),291),(-(1 / (X ^ 2 * Z)),282),(-(1),281),(-((Y ^ 2 + 1) / (X ^ 2 * Y ^ 2 * Z)),276),(-(1 / (X ^ 2 * Z)),272),(-(1 / (X ^ 2 * Z)),267),(-(1),262),(-(1),261),(-(1),258),(-(1),246),(-(1 / (X ^ 2 * Z)),244),(-(1 / (X ^ 2 * Z)),236),(-(1),235),(-(1 / (X ^ 2 * Z)),210)]
abbrev instructionsRow184 (X Y Z W a b : ℂ) : Row ℂ := [(1,139),(-(-1 / Y ^ 2),353),(-(1),345),(-(1 / W),331),(-(1),327),(-((X ^ 2 + Y ^ 2 * Z) / (Y ^ 2 * W)),318),(-(1 / (Y ^ 2 * Z)),316),(-((2 * Z + -1) / W),315),(-(-1 / (Y ^ 2 * Z)),311),(-((-1 * Z + 1) / W),310),(-(1 / Y ^ 2),299),(-(-1 / W),292),(-(1 / W),291),(-(1),267),(-(1 / W),264),(-(-1 / (Y ^ 2 * Z)),259),(-(1),254),(-(1 / W),250),(-(1),212),(-(1 / W),210)]
abbrev instructionsRow185 (X Y Z W a b : ℂ) : Row ℂ := [(1,140),(-(1 / Y ^ 2),353),(-(1),344),(-(1),333),(-(1 / W),330),(-((-1 * X ^ 2 + -1 * Y ^ 2 * Z) / (Y ^ 2 * W)),318),(-(-1 / (Y ^ 2 * Z)),316),(-((-1 * Y ^ 2 + -2) / (Y ^ 2 * W)),315),(-((Y ^ 2 + 1) / (Y ^ 2 * W)),310),(-(1 / W),292),(-(-1 / Z),276),(-(1 / W),271),(-(-1 / (Y ^ 2 * Z)),267),(-(1),259),(-(1),255),(-(1 / W),243),(-(1 / W),237),(-(1),216),(-(1 / W),210)]
abbrev instructionsRow186 (X Y Z W a b : ℂ) : Row ℂ := [(1,154),(-(-1 * a / X),359),(-(-1 / Y ^ 2),354),(-(-1 * X * a / Y ^ 2),353),(-(1),313)]
abbrev instructionsRow187 (X Y Z W a b : ℂ) : Row ℂ := [(1,155),(-(1),383),(-(-2 / X ^ 2),353),(-(1 / X ^ 2),350),(-(-1 / X ^ 2),346),(-(1 / X ^ 2),296),(-(-1 * a / (X * Z * W)),292),(-(a / (X * Z * W)),291),(-(-1 * a / X),290)]
abbrev instructionsRow188 (X Y Z W a b : ℂ) : Row ℂ := [(-1,157),((-1)*(-(1 / X ^ 2)),395),((-1)*(-(1)),393),((-1)*(-(1)),378),((-1)*(-(-2 * a / (X * Y ^ 2))),353),((-1)*(-(-1 * a / (X * Y ^ 2))),352),((-1)*(-(-1 * a / X)),280)]
abbrev instructionsRow189 (X Y Z W a b : ℂ) : Row ℂ := [(1,182),(-(1),370),(-(2 * a / (X * Y ^ 2)),353),(-(-1 * a / (X * Y ^ 2)),350),(-(-1 * a / X),285)]
abbrev instructionsRow190 (X Y Z W a b : ℂ) : Row ℂ := [(1,184),(-(2 / X ^ 2),353),(-(1 / X ^ 2),352),(-(-1 / X ^ 2),347),(-(1 / X ^ 2),295),(-(a / (X * Z * W)),292),(-(-1 * a / X),277)]
abbrev instructionsRow191 (X Y Z W a b : ℂ) : Row ℂ := [(-1,185),((-1)*(-(1 / X ^ 2)),387),((-1)*(-(1)),385),((-1)*(-(-1 * X * a / Y ^ 2)),356),((-1)*(-((-2 * X ^ 2 + 1) / Y ^ 2)),353),((-1)*(-(1)),351),((-1)*(-(-1 * a / X)),287)]
abbrev instructionsRow192 (X Y Z W a b : ℂ) : Row ℂ := [(1,188),(-(1 / Y ^ 2),356),(-(-1 * Y * b / (X ^ 2 * Z * W)),292),(-(Y * b / (X ^ 2 * Z * W)),291),(-(-1 * b / Y),235),(-(1),215)]
abbrev instructionsRow193 (X Y Z W a b : ℂ) : Row ℂ := [(-1,189),((-1)*(-(1)),395),((-1)*(-(1)),387),((-1)*(-(-2 / Y ^ 2)),353),((-1)*(-(1 / Y ^ 2)),350),((-1)*(-(Y * b / (Z * W))),292),((-1)*(-(-1 * b / Y)),239),((-1)*(-(1)),216)]
abbrev instructionsRow194 (X Y Z W a b : ℂ) : Row ℂ := [(-1,196),((-1)*(-(1)),397),((-1)*(-(-1 / Y ^ 2)),357),((-1)*(-((2 * X ^ 2 * b + -2 * Y) / (X ^ 2 * Y))),353),((-1)*(-(b / Y)),352),((-1)*(-(1 / X ^ 2)),350),((-1)*(-(-1 / X ^ 2)),346),((-1)*(-(1)),307),((-1)*(-(1)),303),((-1)*(-(-1 * b / Y)),302),((-1)*(-(1 / Y ^ 2)),301)]
abbrev instructionsRow195 (X Y Z W a b : ℂ) : Row ℂ := [(1,197),(-(1 / Y ^ 2),354),(-(2 * b / Y),353),(-(-1 * b / Y),350),(-(-1 * Y ^ 2 / (Z * W)),292),(-(1),239)]
abbrev instructionsRow196 (X Y Z W a b : ℂ) : Row ℂ := [(-1,198),((-1)*(-(1)),394),((-1)*(-(1)),386),((-1)*(-(1)),354),((-1)*(-(b / Y)),353),((-1)*(-(-1 * b / Y)),348),((-1)*(-(1 / Y ^ 2)),224)]
abbrev instructionsRow197 (X Y Z W a b : ℂ) : Row ℂ := [(1,199),(-(-1 * b / Y),360),(-(-1 / X ^ 2),354),(-(-1 * a / X),353),(-(Y ^ 2 / X ^ 2),313),(-(1),270),(-(1 / Y ^ 2),211)]
abbrev instructionsRow198 (X Y Z W a b : ℂ) : Row ℂ := [(1,205),(-(-1 * b / Y),361),(-((-2 * X ^ 2 + 1) / X ^ 2),353),(-(Y ^ 2 / X ^ 2),351),(-(1),266),(-(1 / Y ^ 2),215)]
abbrev instructionsRow199 (X Y Z W a b : ℂ) : Row ℂ := [(1,143),(-(1),408),(-(1),407),(-(-1),405),(-(-1),404),(-(1),402),(-(1),400),(-(1),397),(-(1),393),(-(1),392),(-(1),385),(-(1),384),(-(1),379),(-(1),377),(-(1),376),(-(1),375),(-(1),374),(-(1),373),(-(1),372),(-(1),371),(-(1),369),(-(1),368),(-(1),367),(-(1),366),(-(1),363),(-(1),362),(-(-1),361),(-(-1),360),(-(1 / (X ^ 2 * Y ^ 2)),357),(-(1 / (X ^ 2 * Y ^ 2)),354),(-(-2 / (X ^ 2 * Y ^ 2)),352),(-(-2 / (X ^ 2 * Y ^ 2)),350),(-(1 / (X ^ 2 * Y ^ 2)),349),(-(1 / (X ^ 2 * Y ^ 2)),348),(-(2 / (X ^ 2 * Y ^ 2)),347),(-(2 / (X ^ 2 * Y ^ 2)),346),(-(1),304),(-(1),303),(-(1 / (X ^ 2 * Y ^ 2)),299),(-(1),294),(-(1),293),(-(1),286),(-(1),279),(-(1),275),(-(1),274),(-(1),273),(-(1),269),(-(1),268),(-(1),262),(-(1),258),(-(1),256),(-(1),218),(-(1),213)]
abbrev instructionsRow200 (X Y Z W a b : ℂ) : Row ℂ := [(1,208),(-(1),372),(-(2 / (X ^ 2 * Y ^ 2)),353),(-(-1 / (X ^ 2 * Y ^ 2)),350),(-(1 / (X ^ 2 * Y ^ 2)),346),(-(1 / Z),339),(-(1),325),(-(1),304),(-(1),275)]
abbrev instructionsRow201 (X Y Z W a b : ℂ) : Row ℂ := [(1,209),(-(1),397),(-(1),379),(-(1 / (X ^ 2 * Y ^ 2)),357),(-(1 / Z),343),(-(1),342),(-(1),273)]
abbrev instructionsRow202 (X Y Z W a b : ℂ) : Row ℂ := [(1,141),(-(-1),411),(-(-1),410),(-(1),409),(-(-1),405),(-(-1),404),(-(1),402),(-(1),400),(-(1),393),(-(1),366),(-(-1),360),(-(1 / (X ^ 2 * Y ^ 2)),354),(-(-2 / (X ^ 2 * Y ^ 2)),353),(-(-1 / (X ^ 2 * Y ^ 2)),352),(-(-2 / (X ^ 2 * Y ^ 2)),350),(-(2 / (X ^ 2 * Y ^ 2)),348),(-(2 / (X ^ 2 * Y ^ 2)),347),(-(2 / (X ^ 2 * Y ^ 2)),346),(-(1 / (X ^ 2 * Y ^ 2)),345),(-(1),339),(-(1),338),(-(1),337),(-(1),334),(-(1),324),(-(1),319),(-((Z + W) / (X ^ 2 * Y ^ 2 * W)),318),(-((-1 * Z + 3 * W) / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / (X ^ 2 * Y ^ 2)),311),(-(-1 * Z / (X ^ 2 * Y ^ 2 * W)),310),(-(1),303),(-(2 / (X ^ 2 * Y ^ 2)),299),(-(1),294),(-(-1 / (X ^ 2 * Z * W)),292),(-(-1 / (X ^ 2 * Z * W)),291),(-(1),279),(-((Z + -2 * W) / (X ^ 2 * Y ^ 2 * Z)),276),(-(1),274),(-(1),269),(-(1 / (X ^ 2 * Y ^ 2)),267),(-(1),262),(-(1 / (X ^ 2 * Y ^ 2)),260),(-(1),258),(-(1 / (X ^ 2 * Y ^ 2)),248),(-(1 / (X ^ 2 * Y ^ 2)),244),(-(1 / (X ^ 2 * Y ^ 2)),243),(-(1 / (X ^ 2 * Y ^ 2)),239),(-(1),234),(-(1),232),(-(1 / (X ^ 2 * Y ^ 2)),231),(-(1),230),(-(1 / (X ^ 2 * Y ^ 2)),226),(-(1 / (X ^ 2 * Y ^ 2)),224),(-(1 / (X ^ 2 * Y ^ 2)),223),(-(1 / (X ^ 2 * Y ^ 2)),219),(-(1 / (X ^ 2 * Y ^ 2)),210)]
abbrev instructionsRow203 (X Y Z W a b : ℂ) : Row ℂ := [(1,114),(-(1),394),(-(1),383),(-(1),365),(-(1),359),(-(-1 * X ^ 2 * W / (Y ^ 2 * Z)),322),(-(-1 / (Y ^ 2 * W)),318),(-(-2 / (Y ^ 2 * W)),315),(-(1 / (Y ^ 2 * Z)),311),(-(1 / (Y ^ 2 * Z)),276),(-(1 / (Y ^ 2 * Z)),259),(-(1),245),(-(1 / (Y ^ 2 * Z)),244),(-(1 / (Y ^ 2 * Z)),210)]
abbrev instructionsRow204 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X / (X + a),162),((-1 * X / (X + a))*(-(-1)),413),((-1 * X / (X + a))*(-(-1 * a / X)),404),((-1 * X / (X + a))*(-(-1)),399),((-1 * X / (X + a))*(-(1)),392),((-1 * X / (X + a))*(-(1)),389),((-1 * X / (X + a))*(-(1 / X ^ 2)),227)]
abbrev instructionsRow205 (X Y Z W a b : ℂ) : Row ℂ := [(1,118),(-(-1),414),(-(1),406),(-(-1),404),(-(1),391),(-(1),388),(-(1),378),(-(1),331),(-(X ^ 2 / (Y ^ 2 * Z)),323),(-(X ^ 2 / (Y ^ 2 * Z)),322),(-(X ^ 2 / (Y ^ 2 * Z)),320),(-(2 / (Y ^ 2 * W)),315),(-(-1 / (Y ^ 2 * W)),310),(-(1 / (Z * W)),292),(-(-1 / (Z * W)),291),(-(1),290),(-(X ^ 2 / (Y ^ 2 * Z)),249),(-(X ^ 2 / (Y ^ 2 * Z)),238),(-(X ^ 2 / (Y ^ 2 * Z)),220)]
abbrev instructionsRow206 (X Y Z W a b : ℂ) : Row ℂ := [(-1,151),((-1)*(-(-1 / X ^ 2)),415),((-1)*(-(a / X)),406),((-1)*(-(1)),390),((-1)*(-(-1 * a / X)),386),((-1)*(-(1 / X ^ 2)),380),((-1)*(-(2 / (X ^ 2 * Y ^ 2))),353),((-1)*(-(-1 / (X ^ 2 * Y ^ 2))),350),((-1)*(-(1 / (X ^ 2 * Y ^ 2))),346),((-1)*(-(1)),275)]
abbrev instructionsRow207 (X Y Z W a b : ℂ) : Row ℂ := [((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1),159),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(-1 / X ^ 2)),416),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(a / X)),415),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(-1)),406),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(1 / X ^ 2)),405),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(1)),386),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(-1 * a / X)),380),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(1)),376)]
abbrev instructionsRow208 (X Y Z W a b : ℂ) : Row ℂ := [(1,115),(-((X ^ 2 * a ^ 2 + -1 * X ^ 2 + X * a + 1) / (X ^ 4 + X ^ 3 * a)),417),(-(-1),416),(-(-1),415),(-(1),405),(-(1),364),(-(X ^ 2 / Y ^ 2),356),(-((-1 * X ^ 4 * W + X ^ 2 * W + -1 * X * W * a + 1) / (Y ^ 2 * W)),318),(-(-1 * X ^ 2 * W / (Y ^ 2 * Z)),317),(-(1 / (Y ^ 2 * Z)),311),(-(-1 / (Y ^ 2 * W)),310),(-(1),309),(-(1),287),(-(1 / (Y ^ 2 * Z)),276),(-(1 / (Y ^ 2 * Z)),267),(-(1 / (Y ^ 2 * Z)),244),(-(1),242),(-(1 / (Y ^ 2 * Z)),210)]
abbrev instructionsRow209 (X Y Z W a b : ℂ) : Row ℂ := [(1,160),(-((X ^ 4 * a + X ^ 3 * a ^ 2 + X ^ 2 * a ^ 3 + -1 * X ^ 2 * a + X * a ^ 2 + a) / (X ^ 5 + X ^ 4 * a)),417),(-(-1 * a / X),416),(-(1),415),(-(-1),412),(-(1),407),(-(a / X),405),(-(1 / X ^ 2),394),(-(-1 * a / X),382)]
def instructionsTable (X Y Z W a b : ℂ) : Array (Row ℂ) := #[
  instructionsRow000 X Y Z W a b,
  instructionsRow001 X Y Z W a b,
  instructionsRow002 X Y Z W a b,
  instructionsRow003 X Y Z W a b,
  instructionsRow004 X Y Z W a b,
  instructionsRow005 X Y Z W a b,
  instructionsRow006 X Y Z W a b,
  instructionsRow007 X Y Z W a b,
  instructionsRow008 X Y Z W a b,
  instructionsRow009 X Y Z W a b,
  instructionsRow010 X Y Z W a b,
  instructionsRow011 X Y Z W a b,
  instructionsRow012 X Y Z W a b,
  instructionsRow013 X Y Z W a b,
  instructionsRow014 X Y Z W a b,
  instructionsRow015 X Y Z W a b,
  instructionsRow016 X Y Z W a b,
  instructionsRow017 X Y Z W a b,
  instructionsRow018 X Y Z W a b,
  instructionsRow019 X Y Z W a b,
  instructionsRow020 X Y Z W a b,
  instructionsRow021 X Y Z W a b,
  instructionsRow022 X Y Z W a b,
  instructionsRow023 X Y Z W a b,
  instructionsRow024 X Y Z W a b,
  instructionsRow025 X Y Z W a b,
  instructionsRow026 X Y Z W a b,
  instructionsRow027 X Y Z W a b,
  instructionsRow028 X Y Z W a b,
  instructionsRow029 X Y Z W a b,
  instructionsRow030 X Y Z W a b,
  instructionsRow031 X Y Z W a b,
  instructionsRow032 X Y Z W a b,
  instructionsRow033 X Y Z W a b,
  instructionsRow034 X Y Z W a b,
  instructionsRow035 X Y Z W a b,
  instructionsRow036 X Y Z W a b,
  instructionsRow037 X Y Z W a b,
  instructionsRow038 X Y Z W a b,
  instructionsRow039 X Y Z W a b,
  instructionsRow040 X Y Z W a b,
  instructionsRow041 X Y Z W a b,
  instructionsRow042 X Y Z W a b,
  instructionsRow043 X Y Z W a b,
  instructionsRow044 X Y Z W a b,
  instructionsRow045 X Y Z W a b,
  instructionsRow046 X Y Z W a b,
  instructionsRow047 X Y Z W a b,
  instructionsRow048 X Y Z W a b,
  instructionsRow049 X Y Z W a b,
  instructionsRow050 X Y Z W a b,
  instructionsRow051 X Y Z W a b,
  instructionsRow052 X Y Z W a b,
  instructionsRow053 X Y Z W a b,
  instructionsRow054 X Y Z W a b,
  instructionsRow055 X Y Z W a b,
  instructionsRow056 X Y Z W a b,
  instructionsRow057 X Y Z W a b,
  instructionsRow058 X Y Z W a b,
  instructionsRow059 X Y Z W a b,
  instructionsRow060 X Y Z W a b,
  instructionsRow061 X Y Z W a b,
  instructionsRow062 X Y Z W a b,
  instructionsRow063 X Y Z W a b,
  instructionsRow064 X Y Z W a b,
  instructionsRow065 X Y Z W a b,
  instructionsRow066 X Y Z W a b,
  instructionsRow067 X Y Z W a b,
  instructionsRow068 X Y Z W a b,
  instructionsRow069 X Y Z W a b,
  instructionsRow070 X Y Z W a b,
  instructionsRow071 X Y Z W a b,
  instructionsRow072 X Y Z W a b,
  instructionsRow073 X Y Z W a b,
  instructionsRow074 X Y Z W a b,
  instructionsRow075 X Y Z W a b,
  instructionsRow076 X Y Z W a b,
  instructionsRow077 X Y Z W a b,
  instructionsRow078 X Y Z W a b,
  instructionsRow079 X Y Z W a b,
  instructionsRow080 X Y Z W a b,
  instructionsRow081 X Y Z W a b,
  instructionsRow082 X Y Z W a b,
  instructionsRow083 X Y Z W a b,
  instructionsRow084 X Y Z W a b,
  instructionsRow085 X Y Z W a b,
  instructionsRow086 X Y Z W a b,
  instructionsRow087 X Y Z W a b,
  instructionsRow088 X Y Z W a b,
  instructionsRow089 X Y Z W a b,
  instructionsRow090 X Y Z W a b,
  instructionsRow091 X Y Z W a b,
  instructionsRow092 X Y Z W a b,
  instructionsRow093 X Y Z W a b,
  instructionsRow094 X Y Z W a b,
  instructionsRow095 X Y Z W a b,
  instructionsRow096 X Y Z W a b,
  instructionsRow097 X Y Z W a b,
  instructionsRow098 X Y Z W a b,
  instructionsRow099 X Y Z W a b,
  instructionsRow100 X Y Z W a b,
  instructionsRow101 X Y Z W a b,
  instructionsRow102 X Y Z W a b,
  instructionsRow103 X Y Z W a b,
  instructionsRow104 X Y Z W a b,
  instructionsRow105 X Y Z W a b,
  instructionsRow106 X Y Z W a b,
  instructionsRow107 X Y Z W a b,
  instructionsRow108 X Y Z W a b,
  instructionsRow109 X Y Z W a b,
  instructionsRow110 X Y Z W a b,
  instructionsRow111 X Y Z W a b,
  instructionsRow112 X Y Z W a b,
  instructionsRow113 X Y Z W a b,
  instructionsRow114 X Y Z W a b,
  instructionsRow115 X Y Z W a b,
  instructionsRow116 X Y Z W a b,
  instructionsRow117 X Y Z W a b,
  instructionsRow118 X Y Z W a b,
  instructionsRow119 X Y Z W a b,
  instructionsRow120 X Y Z W a b,
  instructionsRow121 X Y Z W a b,
  instructionsRow122 X Y Z W a b,
  instructionsRow123 X Y Z W a b,
  instructionsRow124 X Y Z W a b,
  instructionsRow125 X Y Z W a b,
  instructionsRow126 X Y Z W a b,
  instructionsRow127 X Y Z W a b,
  instructionsRow128 X Y Z W a b,
  instructionsRow129 X Y Z W a b,
  instructionsRow130 X Y Z W a b,
  instructionsRow131 X Y Z W a b,
  instructionsRow132 X Y Z W a b,
  instructionsRow133 X Y Z W a b,
  instructionsRow134 X Y Z W a b,
  instructionsRow135 X Y Z W a b,
  instructionsRow136 X Y Z W a b,
  instructionsRow137 X Y Z W a b,
  instructionsRow138 X Y Z W a b,
  instructionsRow139 X Y Z W a b,
  instructionsRow140 X Y Z W a b,
  instructionsRow141 X Y Z W a b,
  instructionsRow142 X Y Z W a b,
  instructionsRow143 X Y Z W a b,
  instructionsRow144 X Y Z W a b,
  instructionsRow145 X Y Z W a b,
  instructionsRow146 X Y Z W a b,
  instructionsRow147 X Y Z W a b,
  instructionsRow148 X Y Z W a b,
  instructionsRow149 X Y Z W a b,
  instructionsRow150 X Y Z W a b,
  instructionsRow151 X Y Z W a b,
  instructionsRow152 X Y Z W a b,
  instructionsRow153 X Y Z W a b,
  instructionsRow154 X Y Z W a b,
  instructionsRow155 X Y Z W a b,
  instructionsRow156 X Y Z W a b,
  instructionsRow157 X Y Z W a b,
  instructionsRow158 X Y Z W a b,
  instructionsRow159 X Y Z W a b,
  instructionsRow160 X Y Z W a b,
  instructionsRow161 X Y Z W a b,
  instructionsRow162 X Y Z W a b,
  instructionsRow163 X Y Z W a b,
  instructionsRow164 X Y Z W a b,
  instructionsRow165 X Y Z W a b,
  instructionsRow166 X Y Z W a b,
  instructionsRow167 X Y Z W a b,
  instructionsRow168 X Y Z W a b,
  instructionsRow169 X Y Z W a b,
  instructionsRow170 X Y Z W a b,
  instructionsRow171 X Y Z W a b,
  instructionsRow172 X Y Z W a b,
  instructionsRow173 X Y Z W a b,
  instructionsRow174 X Y Z W a b,
  instructionsRow175 X Y Z W a b,
  instructionsRow176 X Y Z W a b,
  instructionsRow177 X Y Z W a b,
  instructionsRow178 X Y Z W a b,
  instructionsRow179 X Y Z W a b,
  instructionsRow180 X Y Z W a b,
  instructionsRow181 X Y Z W a b,
  instructionsRow182 X Y Z W a b,
  instructionsRow183 X Y Z W a b,
  instructionsRow184 X Y Z W a b,
  instructionsRow185 X Y Z W a b,
  instructionsRow186 X Y Z W a b,
  instructionsRow187 X Y Z W a b,
  instructionsRow188 X Y Z W a b,
  instructionsRow189 X Y Z W a b,
  instructionsRow190 X Y Z W a b,
  instructionsRow191 X Y Z W a b,
  instructionsRow192 X Y Z W a b,
  instructionsRow193 X Y Z W a b,
  instructionsRow194 X Y Z W a b,
  instructionsRow195 X Y Z W a b,
  instructionsRow196 X Y Z W a b,
  instructionsRow197 X Y Z W a b,
  instructionsRow198 X Y Z W a b,
  instructionsRow199 X Y Z W a b,
  instructionsRow200 X Y Z W a b,
  instructionsRow201 X Y Z W a b,
  instructionsRow202 X Y Z W a b,
  instructionsRow203 X Y Z W a b,
  instructionsRow204 X Y Z W a b,
  instructionsRow205 X Y Z W a b,
  instructionsRow206 X Y Z W a b,
  instructionsRow207 X Y Z W a b,
  instructionsRow208 X Y Z W a b,
  instructionsRow209 X Y Z W a b
]
def instructions (X Y Z W a b : ℂ) (i : ℕ) : Row ℂ := (instructionsTable X Y Z W a b)[i]?.getD []

def orderTable : Array ℕ := #[187, 118, 134, 158, 128, 164, 152, 163, 143, 137, 67, 47, 23, 64, 88, 52, 188, 73, 149, 193, 191, 79, 17, 121, 76, 92, 19, 131, 94, 116, 26, 184, 146, 22, 89, 61, 122, 46, 166, 44, 59, 124, 31, 127, 169, 41, 167, 179, 43, 86, 83, 151, 181, 97, 62, 148, 29, 113, 141, 69, 32, 129, 48, 27, 81, 162, 24, 156, 194, 54, 144, 66, 72, 138, 78, 132, 85, 185, 91, 161, 55, 49, 25, 125, 119, 133, 160, 130, 154, 56, 80, 155, 50, 77, 95, 145, 75, 45, 65, 135, 115, 126, 165, 150, 42, 190, 16, 147, 60, 84, 58, 82, 87, 57, 159, 53, 157, 51, 153, 123, 186, 136, 74, 68, 142, 139, 71, 140, 70, 34, 33, 183, 178, 173, 172, 171, 170, 40, 39, 38, 37, 177, 176, 30, 11, 103, 101, 100, 98, 93, 13, 197, 120, 117, 114, 112, 111, 109, 99, 96, 90, 199, 110, 107, 202, 8, 203, 201, 200, 196, 195, 192, 63, 189, 182, 180, 168, 28, 21, 20, 18, 15, 14, 10, 9, 7, 5, 205, 36, 175, 35, 174, 104, 108, 106, 198, 12, 4, 206, 105, 102, 209, 208, 6, 3, 2, 1, 204, 207, 0]
def order (i : ℕ) : ℕ := orderTable[i]?.getD 0

def rankTable : Array ℕ := #[209, 206, 205, 204, 197, 186, 203, 185, 165, 184, 183, 144, 196, 150, 182, 181, 106, 22, 180, 26, 179, 178, 33, 12, 66, 82, 30, 63, 177, 56, 143, 42, 60, 130, 129, 190, 188, 140, 139, 138, 137, 45, 104, 48, 39, 97, 37, 11, 62, 81, 92, 117, 15, 115, 69, 80, 89, 113, 110, 40, 108, 35, 54, 172, 13, 98, 71, 10, 123, 59, 128, 126, 72, 17, 122, 96, 24, 93, 74, 21, 90, 64, 111, 50, 109, 76, 49, 112, 14, 34, 160, 78, 25, 149, 28, 94, 159, 53, 148, 158, 147, 146, 200, 145, 192, 199, 194, 163, 193, 157, 162, 156, 155, 57, 154, 100, 29, 153, 1, 84, 152, 23, 36, 119, 41, 83, 101, 43, 4, 61, 87, 27, 75, 85, 2, 99, 121, 9, 73, 125, 127, 58, 124, 8, 70, 95, 32, 107, 55, 18, 103, 51, 6, 118, 88, 91, 67, 116, 3, 114, 86, 79, 65, 7, 5, 102, 38, 46, 176, 44, 136, 135, 134, 133, 191, 189, 142, 141, 132, 47, 175, 52, 174, 131, 31, 77, 120, 0, 16, 173, 105, 20, 171, 19, 68, 170, 169, 151, 195, 161, 168, 167, 164, 166, 207, 187, 198, 208, 202, 201]
def rank (i : ℕ) : ℕ := rankTable[i]?.getD 0

def outputTable : Array ℕ := #[209, 208, 207, 206, 205, 204, 203, 202, 201, 200, 199, 198, 197, 196, 195, 194, 193, 192, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176, 175, 174, 173, 172, 171, 170, 169, 168, 167, 166, 165, 164, 163, 162, 161, 160, 159, 158, 157, 156, 155, 154, 153, 152, 151, 150, 149, 148, 147, 146, 145, 144, 143, 142, 141, 140, 139, 138, 137, 136, 135, 134, 133, 132, 131, 130, 129, 128, 127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def output (i : ℕ) : ℕ := outputTable[i]?.getD 0

theorem order_rank : ∀ i : Fin 210, order (rank i.val)=i.val := by decide +kernel
theorem rank_lt : ∀ i : Fin 210, rank i.val<210 := by decide +kernel
theorem output_lt : ∀ i : Fin 210, output i.val<210 := by decide +kernel
end QuantitativeArithmeticCompact35Case0
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace QuantitativeArithmeticCompact35Case1
open QuantitativeArithmeticSparseElimination
open QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

abbrev inputsRow000 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),209),((X^2*Z*W),208)]
abbrev inputsRow001 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),209),((Z*W),207)]
abbrev inputsRow002 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),104),(((X^2*Y^2*W)/(Z)),187)]
abbrev inputsRow003 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),199),(((Y^2*Z*W)/(X^2)),198)]
abbrev inputsRow004 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),209)]
abbrev inputsRow005 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Y^2*Z*W)),209),(((1)),206)]
abbrev inputsRow006 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*Z*W)),209),(((1)),205)]
abbrev inputsRow007 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Z*W)),209),(((1)),204)]
abbrev inputsRow008 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),197),(((X^2)/(Y^2*Z*W)),199)]
abbrev inputsRow009 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),186),(((Z)/(X^2*Y^2*W)),176)]
abbrev inputsRow010 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Z*W)),209),(((1)),203)]
abbrev inputsRow011 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),185),(((W)/(X^2*Y^2*Z)),143)]
abbrev inputsRow012 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),184),(((Y^2)/(X^2*Z*W)),128)]
abbrev inputsRow013 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),183),(((Z)/(Y^2*W)),109)]
abbrev inputsRow014 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),196),(((X^2)/(Z*W)),199)]
abbrev inputsRow015 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),182),(((W)/(Y^2*Z)),152)]
abbrev inputsRow016 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),181),(((Z)/(X^2*W)),101)]
abbrev inputsRow017 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),180),(((Y^2)/(Z*W)),127)]
abbrev inputsRow018 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),179),(((X^2*Z)/(Y^2*W)),107)]
abbrev inputsRow019 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),178),(((W)/(X^2*Z)),103)]
abbrev inputsRow020 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),177),(((X^2*W)/(Y^2*Z)),102)]
abbrev inputsRow021 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),143),(((Z)/(W)),176)]
abbrev inputsRow022 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),190),(((Z*W)/(X^2*Y^2)),191)]
abbrev inputsRow023 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),188),(((X^2*Y^2)/(Z*W)),189)]
abbrev inputsRow024 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),104),(((W)/(Z)),175)]
abbrev inputsRow025 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),97),(((Y^2*Z)/(X^2*W)),174)]
abbrev inputsRow026 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),108),(((X^2*Z)/(W)),173)]
abbrev inputsRow027 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),172),(((Y^2*W)/(X^2*Z)),105)]
abbrev inputsRow028 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),128),(((Z*W)/(Y^2)),171)]
abbrev inputsRow029 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),109),(((X^2*W)/(Z)),170)]
abbrev inputsRow030 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),160),(((Y^2*Z)/(W)),169)]
abbrev inputsRow031 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),199),(((Z*W)/(X^2)),195)]
abbrev inputsRow032 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),101),(((Y^2*W)/(Z)),168)]
abbrev inputsRow033 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),127),(((X^2*Z*W)/(Y^2)),167)]
abbrev inputsRow034 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),175),(((X^2*Y^2*Z)/(W)),166)]
abbrev inputsRow035 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*Z*W)),209),(((1)),202)]
abbrev inputsRow036 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Y^2*Z*W)),209),(((1)),201)]
abbrev inputsRow037 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*Y^2),165),(((1)),120)]
abbrev inputsRow038 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2)),66),(((1)),164)]
abbrev inputsRow039 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),200),(((-1)*Y^2),202)]
abbrev inputsRow040 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2)),209),(((1)),199)]
abbrev inputsRow041 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),194),((((-1))/(Y^2)),207)]
abbrev inputsRow042 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),193),(((-1)*X^2),208)]
abbrev inputsRow043 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),192),(((-1)),202)]
abbrev inputsRow044 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),163),((((-1))/(X^2)),164)]
abbrev inputsRow045 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),162),(((-1)*X^2),187)]
abbrev inputsRow046 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),72),(((-1)*X^2*Y^2),161)]
abbrev inputsRow047 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),160),(((-1)*Y^2),168)]
abbrev inputsRow048 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),159),(((-1)*X^2),167)]
abbrev inputsRow049 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),158),((((-1)*Y^2)/(X^2)),164)]
abbrev inputsRow050 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),157),((((-1))/(X^2*Y^2)),65)]
abbrev inputsRow051 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),156),((((-1))/(X^2)),120)]
abbrev inputsRow052 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),155),((((-1)*X^2)/(Y^2)),173)]
abbrev inputsRow053 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),154),(((-1)),171)]
abbrev inputsRow054 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),153),((((-1)*Y^2)/(X^2)),68)]
abbrev inputsRow055 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),152),(((-1)*X^2),170)]
abbrev inputsRow056 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),70),(((-1)*X^2*Y^2),151)]
abbrev inputsRow057 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*X^2*Y^2),150),(((1)),71)]
abbrev inputsRow058 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Y^2)/(X^2)),106),(((1)),149)]
abbrev inputsRow059 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^2)/(Y^2)),178),(((1)),148)]
abbrev inputsRow060 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2)),143),(((1)),147)]
abbrev inputsRow061 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),62),(((1)),146)]
abbrev inputsRow062 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),145),((((-1))/(X^2*Y^2)),120)]
abbrev inputsRow063 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*X^2*Y^2),144),(((1)),73)]
abbrev inputsRow064 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),176),(((-1)*X^2*Y^2),166)]
abbrev inputsRow065 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),191),(((-1)),207)]
abbrev inputsRow066 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),209),(((1)),189)]
abbrev inputsRow067 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),142),((((-1)*X^2)/(Y^2)),167)]
abbrev inputsRow068 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),141),((((-1)*Y^2)/(X^2)),164)]
abbrev inputsRow069 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*X^2*Y^2),140),(((1)),73)]
abbrev inputsRow070 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*Y^2),139),(((1)),67)]
abbrev inputsRow071 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*X^2),138),(((1)),65)]
abbrev inputsRow072 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Y^2)/(X^2)),137),(((1)),102)]
abbrev inputsRow073 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^2)/(Y^2)),97),(((1)),136)]
abbrev inputsRow074 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2)),62),(((1)),135)]
abbrev inputsRow075 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2)),69),(((1)),134)]
abbrev inputsRow076 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),72),(((1)),133)]
abbrev inputsRow077 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^2)/(Y^2)),63),(((1)),132)]
abbrev inputsRow078 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Y^2)/(X^2)),60),(((1)),131)]
abbrev inputsRow079 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*X^2),130),(((1)),120)]
abbrev inputsRow080 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)*Y^2),129),(((1)),171)]
abbrev inputsRow081 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),128),(((1)),127)]
abbrev inputsRow082 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Z*W)),209),(((1)),126),((((1))/(X^2*Z*W)),127),(((1)),58)]
abbrev inputsRow083 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Z*W)),209),(((1)),59),((((1))/(X^2*Z*W)),128),(((1)),125)]
abbrev inputsRow084 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Z*W)),209),((((1))/(Z*W)),128),(((1)),72),(((1)),124)]
abbrev inputsRow085 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Z*W)),209),(((1)),123),(((1)),73),((((1))/(Z*W)),127)]
abbrev inputsRow086 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2)/(Z*W)),190),(((1)),122),(((X^2)/(Z*W)),199),(((1)),70)]
abbrev inputsRow087 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),71),(((X^2)/(Z*W)),199),(((1)),121),(((X^2)/(Z*W)),189)]
abbrev inputsRow088 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(X^2*W)),104),(((1)),96),(((Z)/(X^2*W)),155),(((1)),95)]
abbrev inputsRow089 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),98),(((Z)/(X^2*W)),148),(((1)),99),(((Z)/(X^2*W)),176)]
abbrev inputsRow090 (X Y Z W a b : ℂ) : Row ℂ := [(((W)/(X^2*Z)),92),(((1)),93),(((W)/(X^2*Z)),152),(((1)),107)]
abbrev inputsRow091 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),172),(((W)/(X^2*Z)),160),(((1)),85),(((W)/(X^2*Z)),86)]
abbrev inputsRow092 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(W)),89),(((1)),90),(((Z)/(W)),101),(((1)),103)]
abbrev inputsRow093 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),108),(((Z)/(W)),109),(((1)),87),(((Z)/(W)),88)]
abbrev inputsRow094 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),104),(((1)),109),(((1)),101),(((1)),176)]
abbrev inputsRow095 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Y^2*W)),209),((((1))/(X^2*Y^2*W)),104),(((1)),48),((((1))/(X^2*Y^2*W)),109),(((1)),76),((((1))/(X^2*Y^2*W)),101),(((1)),43),(((1)),44)]
abbrev inputsRow096 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*Y^2*W)),209),(((1)),45),(((1)),50),((((1))/(X^2*Y^2*W)),109),(((1)),83),((((1))/(X^2*Y^2*W)),101),(((1)),46),((((1))/(X^2*Y^2*W)),176)]
abbrev inputsRow097 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*W)),209),((((1))/(Y^2*W)),104),(((1)),39),(((1)),49),((((1))/(Y^2*W)),101),(((1)),4),((((1))/(Y^2*W)),176),(((1)),136)]
abbrev inputsRow098 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*W)),209),(((1)),137),((((1))/(Y^2*W)),104),(((1)),111),((((1))/(Y^2*W)),109),(((1)),41),(((1)),38),((((1))/(Y^2*W)),176)]
abbrev inputsRow099 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*W)),209),((((1))/(X^2*W)),104),(((1)),97),((((1))/(X^2*W)),109),(((1)),112),(((1)),61),((((1))/(X^2*W)),176),(((1)),135)]
abbrev inputsRow100 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*W)),209),(((1)),138),((((1))/(X^2*W)),104),(((1)),64),(((1)),119),((((1))/(X^2*W)),101),(((1)),102),((((1))/(X^2*W)),176)]
abbrev inputsRow101 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2)/(Y^2*W)),178),(((1)),37),(((X^2)/(Y^2*W)),172),(((1)),14),(((X^2)/(Y^2*W)),199),(((1)),87),(((1)),134),(((X^2)/(Y^2*W)),173)]
abbrev inputsRow102 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2)/(Y^2*W)),178),(((1)),139),(((1)),90),(((X^2)/(Y^2*W)),199),(((1)),36),(((X^2)/(Y^2*W)),107),(((1)),5),(((X^2)/(Y^2*W)),173)]
abbrev inputsRow103 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(W)),209),((((1))/(W)),104),(((1)),62),((((1))/(W)),109),(((1)),160),((((1))/(W)),101),(((1)),75),(((1)),191)]
abbrev inputsRow104 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(W)),209),(((1)),188),(((1)),74),((((1))/(W)),109),(((1)),152),((((1))/(W)),101),(((1)),65),((((1))/(W)),176)]
abbrev inputsRow105 (X Y Z W a b : ℂ) : Row ℂ := [(((Y^2)/(X^2*W)),182),(((1)),117),(((Y^2)/(X^2*W)),89),(((1)),149),(((Y^2)/(X^2*W)),148),(((1)),99),(((Y^2)/(X^2*W)),127),(((1)),141)]
abbrev inputsRow106 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),130),(((Y^2)/(X^2*W)),128),(((1)),96),(((Y^2)/(X^2*W)),155),(((1)),153),(((Y^2)/(X^2*W)),88),(((1)),114),(((Y^2)/(X^2*W)),169)]
abbrev inputsRow107 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2)/(W)),178),(((1)),69),(((X^2)/(W)),172),(((1)),159),(((X^2)/(W)),199),(((1)),73),(((X^2)/(W)),107),(((1)),175)]
abbrev inputsRow108 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),143),(((X^2)/(W)),172),(((1)),72),(((X^2)/(W)),199),(((1)),154),(((X^2)/(W)),107),(((1)),67),(((X^2)/(W)),173)]
abbrev inputsRow109 (X Y Z W a b : ℂ) : Row ℂ := [(((W)/(Y^2)),66),(((1)),89),(((W)/(Y^2)),71),(((1)),148),(((W)/(Y^2)),193),(((1)),127),(((W)/(Y^2)),103),(((1)),174)]
abbrev inputsRow110 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),177),(((W)/(Y^2)),108),(((1)),128),(((W)/(Y^2)),200),(((1)),155),(((W)/(Y^2)),70),(((1)),88),(((W)/(Y^2)),120)]
abbrev inputsRow111 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),143),(((1)),108),(((1)),160),(((1)),152),(((1)),103),(((1)),175)]
abbrev inputsRow112 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2*Z)),209),(((1)),42),((((-1))/(X^2*Y^2*Z)),108),(((1)),35),((((-1))/(X^2*Y^2*Z)),160),(((1)),78),((((-1))/(X^2*Y^2*Z)),152),(((1)),23),((((-1))/(X^2*Y^2*Z)),103),(((1)),51),((((-1))/(X^2*Y^2*Z)),175),(((1)),52)]
abbrev inputsRow113 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2*Z)),209),(((1)),56),((((-1))/(X^2*Y^2*Z)),143),(((1)),40),((((-1))/(X^2*Y^2*Z)),108),(((1)),34),((((-1))/(X^2*Y^2*Z)),160),(((1)),84),((((-1))/(X^2*Y^2*Z)),152),(((1)),18),((((-1))/(X^2*Y^2*Z)),103),(((1)),47)]
abbrev inputsRow114 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2*Z)),209),((((-1))/(Y^2*Z)),143),(((1)),60),((((-1))/(Y^2*Z)),108),(((1)),54),((((-1))/(Y^2*Z)),160),(((1)),25),(((1)),36),((((-1))/(Y^2*Z)),103),(((1)),6),((((-1))/(Y^2*Z)),175),(((1)),174)]
abbrev inputsRow115 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2*Z)),209),(((1)),177),((((-1))/(Y^2*Z)),143),(((1)),110),((((-1))/(Y^2*Z)),108),(((1)),14),(((1)),1),((((-1))/(Y^2*Z)),152),(((1)),55),((((-1))/(Y^2*Z)),103),(((1)),132),((((-1))/(Y^2*Z)),175)]
abbrev inputsRow116 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Z)),209),((((-1))/(X^2*Z)),143),(((1)),130),((((-1))/(X^2*Z)),108),(((1)),172),((((-1))/(X^2*Z)),160),(((1)),149),((((-1))/(X^2*Z)),152),(((1)),119),(((1)),118),((((-1))/(X^2*Z)),175),(((1)),131)]
abbrev inputsRow117 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Z)),209),(((1)),63),((((-1))/(X^2*Z)),143),(((1)),113),(((1)),112),((((-1))/(X^2*Z)),160),(((1)),153),((((-1))/(X^2*Z)),152),(((1)),107),((((-1))/(X^2*Z)),103),(((1)),141),((((-1))/(X^2*Z)),175)]
abbrev inputsRow118 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^2)/(Y^2*Z)),181),(((1)),129),((((-1)*X^2)/(Y^2*Z)),97),(((1)),13),((((-1)*X^2)/(Y^2*Z)),96),(((1)),28),((((-1)*X^2)/(Y^2*Z)),199),(((1)),41),((((-1)*X^2)/(Y^2*Z)),99),(((1)),88),(((1)),31),((((-1)*X^2)/(Y^2*Z)),170)]
abbrev inputsRow119 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Z)/(X^2*Y^2)),66),(((1)),190),((((-1)*Z)/(X^2*Y^2)),69),(((1)),98),((((-1)*Z)/(X^2*Y^2)),109),(((1)),94),((((-1)*Z)/(X^2*Y^2)),154),(((1)),83),((((-1)*Z)/(X^2*Y^2)),70),(((1)),91),(((1)),77),((((-1)*Z)/(X^2*Y^2)),207)]
abbrev inputsRow120 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Z)/(X^2*Y^2)),203),(((1)),82),(((1)),80),((((-1)*Z)/(X^2*Y^2)),71),(((1)),76),((((-1)*Z)/(X^2*Y^2)),159),(((1)),100),((((-1)*Z)/(X^2*Y^2)),101),(((1)),95),((((-1)*Z)/(X^2*Y^2)),67),(((1)),189),((((-1)*Z)/(X^2*Y^2)),120)]
abbrev inputsRow121 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Y^2)/(X^2*Z)),183),(((1)),138),((((-1)*Y^2)/(X^2*Z)),137),(((1)),59),((((-1)*Y^2)/(X^2*Z)),128),(((1)),158),((((-1)*Y^2)/(X^2*Z)),147),(((1)),61),((((-1)*Y^2)/(X^2*Z)),87),(((1)),114),((((-1)*Y^2)/(X^2*Z)),86),(((1)),173)]
abbrev inputsRow122 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),178),((((-1)*Y^2)/(X^2*Z)),92),(((1)),117),((((-1)*Y^2)/(X^2*Z)),90),(((1)),64),((((-1)*Y^2)/(X^2*Z)),162),(((1)),156),((((-1)*Y^2)/(X^2*Z)),127),(((1)),58),((((-1)*Y^2)/(X^2*Z)),136),(((1)),135),((((-1)*Y^2)/(X^2*Z)),168)]
abbrev inputsRow123 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Z)/(Y^2)),196),(((1)),137),((((-1)*Z)/(Y^2)),104),(((1)),128),((((-1)*Z)/(Y^2)),72),(((1)),147),((((-1)*Z)/(Y^2)),200),(((1)),87),((((-1)*Z)/(Y^2)),75),(((1)),86),((((-1)*Z)/(Y^2)),65),(((1)),105)]
abbrev inputsRow124 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),178),(((1)),172),(((1)),107),(((1)),173)]
abbrev inputsRow125 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*W)),209),(((1)),33),(((1)),13),((((1))/(Y^2*W)),109),((((1))/(Y^2*W)),101),(((1)),55),((((1))/(Y^2*W)),176),(((1)),105)]
abbrev inputsRow126 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2*W)),209),(((1)),179),((((1))/(Y^2*W)),104),(((1)),54),((((1))/(Y^2*W)),109),((((1))/(Y^2*W)),101),(((1)),32),(((1)),16)]
abbrev inputsRow127 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),181),(((1)),97),(((1)),96),(((1)),99),(((1)),102),(((1)),170)]
abbrev inputsRow128 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),182),(((1)),177),(((1)),89),(((1)),148),(((1)),155),(((1)),88),(((1)),174),(((1)),169)]
abbrev inputsRow129 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*W)),209),(((1)),181),((((1))/(X^2*W)),177),(((1)),56),(((1)),113),((((1))/(X^2*W)),128),((((1))/(X^2*W)),109),(((1)),158),(((1)),57),((((1))/(X^2*W)),101),((((1))/(X^2*W)),88),(((1)),91),((((1))/(X^2*W)),176),(((1)),131),((((1))/(X^2*W)),169),(((1)),151)]
abbrev inputsRow130 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2*W)),209),(((1)),150),((((1))/(X^2*W)),182),(((1)),63),((((1))/(X^2*W)),104),(((1)),80),((((1))/(X^2*W)),89),((((1))/(X^2*W)),109),(((1)),53),(((1)),156),((((1))/(X^2*W)),101),((((1))/(X^2*W)),127),(((1)),118),(((1)),52),((((1))/(X^2*W)),174),(((1)),170)]
abbrev inputsRow131 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(W)),209),((((1))/(W)),182),(((1)),106),(((1)),143),((((1))/(W)),104),(((1)),110),((((1))/(W)),109),((((1))/(W)),148),(((1)),147),(((1)),154),((((1))/(W)),127),(((1)),67),((((1))/(W)),176),((((1))/(W)),174),(((1)),31),(((1)),195)]
abbrev inputsRow132 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(W)),209),(((1)),196),(((1)),30),((((1))/(W)),177),((((1))/(W)),104),(((1)),69),((((1))/(W)),128),(((1)),159),(((1)),162),((((1))/(W)),155),((((1))/(W)),101),(((1)),6),((((1))/(W)),176),(((1)),175),(((1)),68),((((1))/(W)),169)]
abbrev inputsRow133 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2)/(W)),185),(((1)),180),(((X^2)/(W)),178),(((1)),60),(((X^2)/(W)),81),(((1)),108),(((X^2)/(W)),78),(((1)),200),(((X^2)/(W)),199),(((1)),29),(((X^2)/(W)),107),(((1)),3),(((X^2)/(W)),189),(((1)),120),(((X^2)/(W)),173),(((1)),168)]
abbrev inputsRow134 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),183),(((X^2)/(W)),178),(((1)),66),(((X^2)/(W)),190),(((1)),15),(((X^2)/(W)),172),(((1)),28),(((X^2)/(W)),199),(((1)),193),(((X^2)/(W)),84),(((1)),103),(((X^2)/(W)),79),(((1)),132),(((X^2)/(W)),173),(((1)),171),(((X^2)/(W)),166)]
abbrev inputsRow135 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),183),(((1)),179),(((1)),137),(((1)),92),(((1)),90),(((1)),147),(((1)),162),(((1)),87),(((1)),86),(((1)),136),(((1)),105),(((1)),168)]
abbrev inputsRow136 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Z)),209),(((1)),144),((((-1))/(X^2*Z)),179),(((1)),178),((((-1))/(X^2*Z)),143),(((1)),45),(((1)),117),((((-1))/(X^2*Z)),108),((((-1))/(X^2*Z)),90),(((1)),64),((((-1))/(X^2*Z)),160),(((1)),146),((((-1))/(X^2*Z)),162),(((1)),156),(((1)),27),((((-1))/(X^2*Z)),127),((((-1))/(X^2*Z)),103),(((1)),79),((((-1))/(X^2*Z)),136),(((1)),135),((((-1))/(X^2*Z)),175),(((1)),20),((((-1))/(X^2*Z)),168),(((1)),167)]
abbrev inputsRow137 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Z)),209),(((1)),184),((((-1))/(X^2*Z)),183),(((1)),26),((((-1))/(X^2*Z)),143),(((1)),138),((((-1))/(X^2*Z)),137),(((1)),81),((((-1))/(X^2*Z)),108),((((-1))/(X^2*Z)),128),(((1)),21),(((1)),158),((((-1))/(X^2*Z)),147),(((1)),157),((((-1))/(X^2*Z)),152),(((1)),61),((((-1))/(X^2*Z)),87),((((-1))/(X^2*Z)),103),(((1)),114),(((1)),44),((((-1))/(X^2*Z)),175),(((1)),173),((((-1))/(X^2*Z)),105),(((1)),161)]
abbrev inputsRow138 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),185),(((1)),81),(((1)),93),(((1)),78),(((1)),84),(((1)),85),(((1)),79),(((1)),166)]
abbrev inputsRow139 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(W)),209),(((1)),165),((((1))/(W)),104),(((1)),92),((((1))/(W)),128),(((1)),74),((((1))/(W)),109),(((1)),25),((((1))/(W)),155),(((1)),152),((((1))/(W)),101),(((1)),2),((((1))/(W)),88),(((1)),65),((((1))/(W)),169),(((1)),207)]
abbrev inputsRow140 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(W)),209),(((1)),203),((((1))/(W)),182),(((1)),62),((((1))/(W)),89),(((1)),24),((((1))/(W)),109),(((1)),160),((((1))/(W)),148),(((1)),1),((((1))/(W)),101),(((1)),75),((((1))/(W)),127),(((1)),86),((((1))/(W)),176),(((1)),164)]
abbrev inputsRow141 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),209),(((1)),185),((((-1))/(X^2*Y^2)),196),(((1)),150),((((-1))/(X^2*Y^2)),180),(((1)),26),(((1)),82),((((-1))/(X^2*Y^2)),143),((((-1))/(X^2*Y^2)),188),(((1)),140),((((-1))/(X^2*Y^2)),104),(((1)),81),(((1)),80),((((-1))/(X^2*Y^2)),108),((((-1))/(X^2*Y^2)),71),(((1)),10),((((-1))/(X^2*Y^2)),72),(((1)),17),((((-1))/(X^2*Y^2)),74),(((1)),21),((((-1))/(X^2*Y^2)),159),(((1)),53),((((-1))/(X^2*Y^2)),200),(((1)),145),((((-1))/(X^2*Y^2)),193),(((1)),157),(((1)),100),((((-1))/(X^2*Y^2)),152),((((-1))/(X^2*Y^2)),101),(((1)),85),((((-1))/(X^2*Y^2)),73),(((1)),125),(((1)),95),((((-1))/(X^2*Y^2)),103),((((-1))/(X^2*Y^2)),67),(((1)),116),((((-1))/(X^2*Y^2)),65),(((1)),7),((((-1))/(X^2*Y^2)),176),(((1)),189),((((-1))/(X^2*Y^2)),175),((((-1))/(X^2*Y^2)),120),(((1)),0),((((-1))/(X^2*Y^2)),171),(((1)),19),((((-1))/(X^2*Y^2)),195),(((1)),161),(((1)),187)]
abbrev inputsRow142 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),186),(((1)),82),(((1)),80),(((1)),98),(((1)),76),(((1)),94),(((1)),100),(((1)),83),(((1)),95),(((1)),91),(((1)),77),(((1)),187)]
abbrev inputsRow143 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),206),(((1)),144),(((1)),150),(((1)),22),(((1)),26),(((1)),12),(((1)),56),(((1)),42),(((1)),140),(((1)),45),(((1)),48),(((1)),11),(((1)),115),(((1)),40),(((1)),35),(((1)),10),(((1)),126),(((1)),17),(((1)),21),(((1)),50),(((1)),34),(((1)),53),(((1)),146),(((1)),145),(((1)),163),(((1)),157),(((1)),57),(((1)),23),(((1)),43),(((1)),27),(((1)),9),(((1)),125),(((1)),8),(((1)),18),(((1)),51),(((1)),116),(((1)),7),(((1)),46),(((1)),44),(((1)),133),(((1)),47),(((1)),52),(((1)),0),(((1)),20),(((1)),19),(((1)),151),(((1)),161),(((1)),201)]
abbrev inputsRow144 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),205),((((-1)*a)/(X)),197),((((1))/(X^2)),165),(((1)),163)]
abbrev inputsRow145 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),197),((((-1)*a)/(X)),165),((((1))/(X^2)),106),(((1)),157)]
abbrev inputsRow146 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),186),((((-1)*a)/(X)),183),((((1))/(X^2)),179),(((1)),162)]
abbrev inputsRow147 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),185),((((-1)*a)/(X)),182),((((1))/(X^2)),177),(((1)),155)]
abbrev inputsRow148 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),165),((((-1)*a)/(X)),106),((((1))/(X^2)),60),(((1)),57)]
abbrev inputsRow149 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),184),((((-1)*a)/(X)),180),((((1))/(X^2)),188),(((1)),154)]
abbrev inputsRow150 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),183),((((-1)*a)/(X)),179),((((1))/(X^2)),137),(((1)),100)]
abbrev inputsRow151 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),144),((((-1)*a)/(X)),33),((((1))/(X^2)),39),(((1)),29)]
abbrev inputsRow152 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),182),((((-1)*a)/(X)),177),((((1))/(X^2)),89),(((1)),84)]
abbrev inputsRow153 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),181),((((-1)*a)/(X)),143),((((1))/(X^2)),108),(((1)),152)]
abbrev inputsRow154 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),106),((((-1)*a)/(X)),60),((((1))/(X^2)),13),(((1)),23)]
abbrev inputsRow155 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),22),((((-1)*a)/(X)),129),((((1))/(X^2)),123),(((1)),36)]
abbrev inputsRow156 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),180),((((-1)*a)/(X)),188),((((1))/(X^2)),72),(((1)),119)]
abbrev inputsRow157 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),26),((((-1)*a)/(X)),139),((((1))/(X^2)),24),(((1)),41)]
abbrev inputsRow158 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),179),((((-1)*a)/(X)),137),((((1))/(X^2)),90),(((1)),83)]
abbrev inputsRow159 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),33),((((-1)*a)/(X)),39),((((1))/(X^2)),14),(((1)),43)]
abbrev inputsRow160 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),12),((((-1)*a)/(X)),37),((((1))/(X^2)),25),(((1)),4)]
abbrev inputsRow161 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),82),((((-1)*a)/(X)),92),((((1))/(X^2)),147),(((1)),87)]
abbrev inputsRow162 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),30),((((-1)*a)/(X)),15),((((1))/(X^2)),192),(((1)),27)]
abbrev inputsRow163 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),143),((((-1)*a)/(X)),108),((((1))/(X^2)),152),(((1)),99)]
abbrev inputsRow164 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),42),((((-1)*a)/(X)),54),((((1))/(X^2)),41),(((1)),121)]
abbrev inputsRow165 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),140),((((-1)*a)/(X)),122),(((1)),124),((((1))/(X^2)),55)]
abbrev inputsRow166 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),48),((((-1)*a)/(X)),49),(((1)),55),((((1))/(X^2)),134)]
abbrev inputsRow167 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),97),((((-1)*a)/(X)),160),(((1)),103),((((1))/(X^2)),175)]
abbrev inputsRow168 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),62),((((-1)*a)/(X)),159),(((1)),118),((((1))/(X^2)),171)]
abbrev inputsRow169 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),81),((((-1)*a)/(X)),148),(((1)),88),((((1))/(X^2)),169)]
abbrev inputsRow170 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),92),((((-1)*a)/(X)),147),(((1)),91),((((1))/(X^2)),168)]
abbrev inputsRow171 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),117),((((-1)*a)/(X)),200),(((1)),67),((((1))/(X^2)),207)]
abbrev inputsRow172 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),15),((((-1)*a)/(X)),192),(((1)),116),((((1))/(X^2)),202)]
abbrev inputsRow173 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),205),(((1)),115),((((-1)*a)/(X)),194),(((1)),3)]
abbrev inputsRow174 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),203),(((1)),69),((((-1)*a)/(X)),193),(((1)),114)]
abbrev inputsRow175 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),183),(((1)),80),((((-1)*a)/(X)),162),(((1)),86)]
abbrev inputsRow176 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),182),(((1)),89),((((-1)*a)/(X)),155),(((1)),79)]
abbrev inputsRow177 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),180),(((1)),113),((((-1)*a)/(X)),154),(((1)),65)]
abbrev inputsRow178 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),104),(((1)),172),((((-1)*a)/(X)),101),(((1)),176)]
abbrev inputsRow179 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),54),(((1)),123),((((-1)*a)/(X)),121),(((1)),133)]
abbrev inputsRow180 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),122),((((1))/(X^2)),49),((((-1)*a)/(X)),55),(((1)),47)]
abbrev inputsRow181 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),90),((((1))/(X^2)),162),((((-1)*a)/(X)),86),(((1)),77)]
abbrev inputsRow182 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),49),((((1))/(X^2)),2),((((-1)*a)/(X)),134),(((1)),20)]
abbrev inputsRow183 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),112),((((1))/(X^2)),73),((((-1)*a)/(X)),191),(((1)),171)]
abbrev inputsRow184 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),14),((((1))/(X^2)),124),((((-1)*a)/(X)),142),(((1)),19)]
abbrev inputsRow185 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),34),((((1))/(X^2)),32),((((-1)*a)/(X)),132),(((1)),68)]
abbrev inputsRow186 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),94),((((1))/(X^2)),136),((((-1)*a)/(X)),105),(((1)),168)]
abbrev inputsRow187 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),53),((((1))/(X^2)),132),((((-1)*a)/(X)),68),(((1)),164)]
abbrev inputsRow188 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),204),((((-1)*b)/(Y)),184),((((1))/(Y^2)),63),(((1)),17),(((1)),8)]
abbrev inputsRow189 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),203),((((-1)*b)/(Y)),180),((((1))/(Y^2)),69),(((1)),24),(((1)),32)]
abbrev inputsRow190 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),185),((((-1)*b)/(Y)),178),((((1))/(Y^2)),172),(((1)),93),(((1)),107)]
abbrev inputsRow191 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),183),((((-1)*b)/(Y)),143),(((1)),90),((((1))/(Y^2)),160),(((1)),103)]
abbrev inputsRow192 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),144),((((-1)*b)/(Y)),130),(((1)),64),((((1))/(Y^2)),158),(((1)),51)]
abbrev inputsRow193 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),196),((((-1)*b)/(Y)),188),(((1)),111),((((1))/(Y^2)),193),(((1)),6)]
abbrev inputsRow194 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),150),((((-1)*b)/(Y)),138),(((1)),50),((((1))/(Y^2)),153),(((1)),118)]
abbrev inputsRow195 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),106),((((-1)*b)/(Y)),62),(((1)),49),((((1))/(Y^2)),70),(((1)),67)]
abbrev inputsRow196 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),22),((((-1)*b)/(Y)),117),(((1)),112),((((1))/(Y^2)),118),(((1)),116)]
abbrev inputsRow197 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),180),((((-1)*b)/(Y)),69),(((1)),14),(((1)),3),((((1))/(Y^2)),65)]
abbrev inputsRow198 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),33),((((-1)*b)/(Y)),71),(((1)),25),(((1)),65),((((1))/(Y^2)),195)]
abbrev inputsRow199 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),12),((((-1)*b)/(Y)),59),(((1)),149),(((1)),7),((((1))/(Y^2)),208)]
abbrev inputsRow200 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),63),((((1))/(Y^2)),130),((((-1)*b)/(Y)),64),(((1)),53),(((1)),46)]
abbrev inputsRow201 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),177),((((1))/(Y^2)),104),((((-1)*b)/(Y)),109),(((1)),148),(((1)),176)]
abbrev inputsRow202 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),56),((((1))/(Y^2)),117),((((-1)*b)/(Y)),112),(((1)),158),(((1)),44)]
abbrev inputsRow203 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),42),((((1))/(Y^2)),59),((((-1)*b)/(Y)),149),(((1)),146),(((1)),135)]
abbrev inputsRow204 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),130),((((1))/(Y^2)),112),((((-1)*b)/(Y)),158),(((1)),145),(((1)),133)]
abbrev inputsRow205 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Y^2)),204),(((1)),11),(((1)),153),((((-1)*b)/(Y)),58),(((1)),0)]
abbrev inputsRow206 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),110),((((1))/(Y^2)),200),(((1)),4),((((-1)*b)/(Y)),191),(((1)),195)]
abbrev inputsRow207 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),40),((((1))/(Y^2)),156),(((1)),61),((((-1)*b)/(Y)),141),(((1)),161)]
abbrev inputsRow208 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),144),(((1)),115),((((1))/(Z)),80),(((1)),94),(((1)),9),(((1)),47)]
abbrev inputsRow209 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),22),(((1)),40),((((1))/(Z)),76),(((1)),146),(((1)),8),(((1)),77)]
def inputsTable (X Y Z W a b : ℂ) : Array (Row ℂ) := #[
  inputsRow000 X Y Z W a b,
  inputsRow001 X Y Z W a b,
  inputsRow002 X Y Z W a b,
  inputsRow003 X Y Z W a b,
  inputsRow004 X Y Z W a b,
  inputsRow005 X Y Z W a b,
  inputsRow006 X Y Z W a b,
  inputsRow007 X Y Z W a b,
  inputsRow008 X Y Z W a b,
  inputsRow009 X Y Z W a b,
  inputsRow010 X Y Z W a b,
  inputsRow011 X Y Z W a b,
  inputsRow012 X Y Z W a b,
  inputsRow013 X Y Z W a b,
  inputsRow014 X Y Z W a b,
  inputsRow015 X Y Z W a b,
  inputsRow016 X Y Z W a b,
  inputsRow017 X Y Z W a b,
  inputsRow018 X Y Z W a b,
  inputsRow019 X Y Z W a b,
  inputsRow020 X Y Z W a b,
  inputsRow021 X Y Z W a b,
  inputsRow022 X Y Z W a b,
  inputsRow023 X Y Z W a b,
  inputsRow024 X Y Z W a b,
  inputsRow025 X Y Z W a b,
  inputsRow026 X Y Z W a b,
  inputsRow027 X Y Z W a b,
  inputsRow028 X Y Z W a b,
  inputsRow029 X Y Z W a b,
  inputsRow030 X Y Z W a b,
  inputsRow031 X Y Z W a b,
  inputsRow032 X Y Z W a b,
  inputsRow033 X Y Z W a b,
  inputsRow034 X Y Z W a b,
  inputsRow035 X Y Z W a b,
  inputsRow036 X Y Z W a b,
  inputsRow037 X Y Z W a b,
  inputsRow038 X Y Z W a b,
  inputsRow039 X Y Z W a b,
  inputsRow040 X Y Z W a b,
  inputsRow041 X Y Z W a b,
  inputsRow042 X Y Z W a b,
  inputsRow043 X Y Z W a b,
  inputsRow044 X Y Z W a b,
  inputsRow045 X Y Z W a b,
  inputsRow046 X Y Z W a b,
  inputsRow047 X Y Z W a b,
  inputsRow048 X Y Z W a b,
  inputsRow049 X Y Z W a b,
  inputsRow050 X Y Z W a b,
  inputsRow051 X Y Z W a b,
  inputsRow052 X Y Z W a b,
  inputsRow053 X Y Z W a b,
  inputsRow054 X Y Z W a b,
  inputsRow055 X Y Z W a b,
  inputsRow056 X Y Z W a b,
  inputsRow057 X Y Z W a b,
  inputsRow058 X Y Z W a b,
  inputsRow059 X Y Z W a b,
  inputsRow060 X Y Z W a b,
  inputsRow061 X Y Z W a b,
  inputsRow062 X Y Z W a b,
  inputsRow063 X Y Z W a b,
  inputsRow064 X Y Z W a b,
  inputsRow065 X Y Z W a b,
  inputsRow066 X Y Z W a b,
  inputsRow067 X Y Z W a b,
  inputsRow068 X Y Z W a b,
  inputsRow069 X Y Z W a b,
  inputsRow070 X Y Z W a b,
  inputsRow071 X Y Z W a b,
  inputsRow072 X Y Z W a b,
  inputsRow073 X Y Z W a b,
  inputsRow074 X Y Z W a b,
  inputsRow075 X Y Z W a b,
  inputsRow076 X Y Z W a b,
  inputsRow077 X Y Z W a b,
  inputsRow078 X Y Z W a b,
  inputsRow079 X Y Z W a b,
  inputsRow080 X Y Z W a b,
  inputsRow081 X Y Z W a b,
  inputsRow082 X Y Z W a b,
  inputsRow083 X Y Z W a b,
  inputsRow084 X Y Z W a b,
  inputsRow085 X Y Z W a b,
  inputsRow086 X Y Z W a b,
  inputsRow087 X Y Z W a b,
  inputsRow088 X Y Z W a b,
  inputsRow089 X Y Z W a b,
  inputsRow090 X Y Z W a b,
  inputsRow091 X Y Z W a b,
  inputsRow092 X Y Z W a b,
  inputsRow093 X Y Z W a b,
  inputsRow094 X Y Z W a b,
  inputsRow095 X Y Z W a b,
  inputsRow096 X Y Z W a b,
  inputsRow097 X Y Z W a b,
  inputsRow098 X Y Z W a b,
  inputsRow099 X Y Z W a b,
  inputsRow100 X Y Z W a b,
  inputsRow101 X Y Z W a b,
  inputsRow102 X Y Z W a b,
  inputsRow103 X Y Z W a b,
  inputsRow104 X Y Z W a b,
  inputsRow105 X Y Z W a b,
  inputsRow106 X Y Z W a b,
  inputsRow107 X Y Z W a b,
  inputsRow108 X Y Z W a b,
  inputsRow109 X Y Z W a b,
  inputsRow110 X Y Z W a b,
  inputsRow111 X Y Z W a b,
  inputsRow112 X Y Z W a b,
  inputsRow113 X Y Z W a b,
  inputsRow114 X Y Z W a b,
  inputsRow115 X Y Z W a b,
  inputsRow116 X Y Z W a b,
  inputsRow117 X Y Z W a b,
  inputsRow118 X Y Z W a b,
  inputsRow119 X Y Z W a b,
  inputsRow120 X Y Z W a b,
  inputsRow121 X Y Z W a b,
  inputsRow122 X Y Z W a b,
  inputsRow123 X Y Z W a b,
  inputsRow124 X Y Z W a b,
  inputsRow125 X Y Z W a b,
  inputsRow126 X Y Z W a b,
  inputsRow127 X Y Z W a b,
  inputsRow128 X Y Z W a b,
  inputsRow129 X Y Z W a b,
  inputsRow130 X Y Z W a b,
  inputsRow131 X Y Z W a b,
  inputsRow132 X Y Z W a b,
  inputsRow133 X Y Z W a b,
  inputsRow134 X Y Z W a b,
  inputsRow135 X Y Z W a b,
  inputsRow136 X Y Z W a b,
  inputsRow137 X Y Z W a b,
  inputsRow138 X Y Z W a b,
  inputsRow139 X Y Z W a b,
  inputsRow140 X Y Z W a b,
  inputsRow141 X Y Z W a b,
  inputsRow142 X Y Z W a b,
  inputsRow143 X Y Z W a b,
  inputsRow144 X Y Z W a b,
  inputsRow145 X Y Z W a b,
  inputsRow146 X Y Z W a b,
  inputsRow147 X Y Z W a b,
  inputsRow148 X Y Z W a b,
  inputsRow149 X Y Z W a b,
  inputsRow150 X Y Z W a b,
  inputsRow151 X Y Z W a b,
  inputsRow152 X Y Z W a b,
  inputsRow153 X Y Z W a b,
  inputsRow154 X Y Z W a b,
  inputsRow155 X Y Z W a b,
  inputsRow156 X Y Z W a b,
  inputsRow157 X Y Z W a b,
  inputsRow158 X Y Z W a b,
  inputsRow159 X Y Z W a b,
  inputsRow160 X Y Z W a b,
  inputsRow161 X Y Z W a b,
  inputsRow162 X Y Z W a b,
  inputsRow163 X Y Z W a b,
  inputsRow164 X Y Z W a b,
  inputsRow165 X Y Z W a b,
  inputsRow166 X Y Z W a b,
  inputsRow167 X Y Z W a b,
  inputsRow168 X Y Z W a b,
  inputsRow169 X Y Z W a b,
  inputsRow170 X Y Z W a b,
  inputsRow171 X Y Z W a b,
  inputsRow172 X Y Z W a b,
  inputsRow173 X Y Z W a b,
  inputsRow174 X Y Z W a b,
  inputsRow175 X Y Z W a b,
  inputsRow176 X Y Z W a b,
  inputsRow177 X Y Z W a b,
  inputsRow178 X Y Z W a b,
  inputsRow179 X Y Z W a b,
  inputsRow180 X Y Z W a b,
  inputsRow181 X Y Z W a b,
  inputsRow182 X Y Z W a b,
  inputsRow183 X Y Z W a b,
  inputsRow184 X Y Z W a b,
  inputsRow185 X Y Z W a b,
  inputsRow186 X Y Z W a b,
  inputsRow187 X Y Z W a b,
  inputsRow188 X Y Z W a b,
  inputsRow189 X Y Z W a b,
  inputsRow190 X Y Z W a b,
  inputsRow191 X Y Z W a b,
  inputsRow192 X Y Z W a b,
  inputsRow193 X Y Z W a b,
  inputsRow194 X Y Z W a b,
  inputsRow195 X Y Z W a b,
  inputsRow196 X Y Z W a b,
  inputsRow197 X Y Z W a b,
  inputsRow198 X Y Z W a b,
  inputsRow199 X Y Z W a b,
  inputsRow200 X Y Z W a b,
  inputsRow201 X Y Z W a b,
  inputsRow202 X Y Z W a b,
  inputsRow203 X Y Z W a b,
  inputsRow204 X Y Z W a b,
  inputsRow205 X Y Z W a b,
  inputsRow206 X Y Z W a b,
  inputsRow207 X Y Z W a b,
  inputsRow208 X Y Z W a b,
  inputsRow209 X Y Z W a b
]
def inputs (X Y Z W a b : ℂ) (i : ℕ) : Row ℂ := (inputsTable X Y Z W a b)[i]?.getD []

abbrev stepsRow000 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),209)]
abbrev stepsRow001 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),208)]
abbrev stepsRow002 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),207)]
abbrev stepsRow003 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),206)]
abbrev stepsRow004 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),205)]
abbrev stepsRow005 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),204)]
abbrev stepsRow006 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),203)]
abbrev stepsRow007 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),202)]
abbrev stepsRow008 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),201)]
abbrev stepsRow009 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),200)]
abbrev stepsRow010 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),199)]
abbrev stepsRow011 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),198)]
abbrev stepsRow012 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),197)]
abbrev stepsRow013 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),196)]
abbrev stepsRow014 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),195)]
abbrev stepsRow015 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),194)]
abbrev stepsRow016 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),193)]
abbrev stepsRow017 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),192)]
abbrev stepsRow018 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),191)]
abbrev stepsRow019 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),190)]
abbrev stepsRow020 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),189)]
abbrev stepsRow021 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),188)]
abbrev stepsRow022 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(X^2*Y^2*W)),104),(((1)),187)]
abbrev stepsRow023 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),186),(((Z)/(X^2*Y^2*W)),176)]
abbrev stepsRow024 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),185),(((W)/(X^2*Y^2*Z)),143)]
abbrev stepsRow025 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),184),(((Y^2)/(X^2*Z*W)),128)]
abbrev stepsRow026 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),183),(((Z)/(Y^2*W)),109)]
abbrev stepsRow027 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),182),(((W)/(Y^2*Z)),152)]
abbrev stepsRow028 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),181),(((Z)/(X^2*W)),101)]
abbrev stepsRow029 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),180),(((Y^2)/(Z*W)),127)]
abbrev stepsRow030 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),179),(((X^2*Z)/(Y^2*W)),107)]
abbrev stepsRow031 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),178),(((W)/(X^2*Z)),103)]
abbrev stepsRow032 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),177),(((X^2*W)/(Y^2*Z)),102)]
abbrev stepsRow033 (X Y Z W a b : ℂ) : Row ℂ := [(((W)/(Z)),143),(((1)),176)]
abbrev stepsRow034 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(W)),104),(((1)),175)]
abbrev stepsRow035 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2*W)/(Y^2*Z)),97),(((1)),174)]
abbrev stepsRow036 (X Y Z W a b : ℂ) : Row ℂ := [(((W)/(X^2*Z)),108),(((1)),173)]
abbrev stepsRow037 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),172),(((Y^2*W)/(X^2*Z)),105)]
abbrev stepsRow038 (X Y Z W a b : ℂ) : Row ℂ := [(((Y^2)/(Z*W)),128),(((1)),171)]
abbrev stepsRow039 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(X^2*W)),109),(((1)),170)]
abbrev stepsRow040 (X Y Z W a b : ℂ) : Row ℂ := [(((W)/(Y^2*Z)),160),(((1)),169)]
abbrev stepsRow041 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(Y^2*W)),101),(((1)),168)]
abbrev stepsRow042 (X Y Z W a b : ℂ) : Row ℂ := [(((Y^2)/(X^2*Z*W)),127),(((1)),167)]
abbrev stepsRow043 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),104),(((1)),166)]
abbrev stepsRow044 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),165),((((-1))/(Y^2)),120)]
abbrev stepsRow045 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2)),66),(((1)),164)]
abbrev stepsRow046 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),66),(((1)),163)]
abbrev stepsRow047 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(Y^2*W)),104),(((1)),162)]
abbrev stepsRow048 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),72),(((1)),161)]
abbrev stepsRow049 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),160),(((Z)/(W)),101)]
abbrev stepsRow050 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),159),(((Y^2)/(Z*W)),127)]
abbrev stepsRow051 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2)),66),(((1)),158)]
abbrev stepsRow052 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),157),((((-1))/(X^2*Y^2)),65)]
abbrev stepsRow053 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),156),((((-1))/(X^2)),120)]
abbrev stepsRow054 (X Y Z W a b : ℂ) : Row ℂ := [(((W)/(Y^2*Z)),108),(((1)),155)]
abbrev stepsRow055 (X Y Z W a b : ℂ) : Row ℂ := [(((Y^2)/(Z*W)),128),(((1)),154)]
abbrev stepsRow056 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),153),((((-1)*Y^2)/(X^2)),68)]
abbrev stepsRow057 (X Y Z W a b : ℂ) : Row ℂ := [(((Z)/(W)),109),(((1)),152)]
abbrev stepsRow058 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),70),(((1)),151)]
abbrev stepsRow059 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),150),((((-1))/(X^2*Y^2)),71)]
abbrev stepsRow060 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Y^2)/(X^2)),106),(((1)),149)]
abbrev stepsRow061 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),148),(((W)/(Y^2*Z)),103)]
abbrev stepsRow062 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2)),143),(((1)),147)]
abbrev stepsRow063 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),62),(((1)),146)]
abbrev stepsRow064 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),145),((((-1))/(X^2*Y^2)),120)]
abbrev stepsRow065 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),144),((((-1))/(X^2*Y^2)),73)]
abbrev stepsRow066 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),143),(((Z)/(W)),104)]
abbrev stepsRow067 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(Z*W)),127),(((1)),142)]
abbrev stepsRow068 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2)),66),(((1)),141)]
abbrev stepsRow069 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),140),((((-1))/(X^2*Y^2)),73)]
abbrev stepsRow070 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),139),((((-1))/(Y^2)),67)]
abbrev stepsRow071 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),138),((((-1))/(X^2)),65)]
abbrev stepsRow072 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),137),((((-1)*X^2)/(Y^2)),102)]
abbrev stepsRow073 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^2)/(Y^2)),97),(((1)),136)]
abbrev stepsRow074 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2)),62),(((1)),135)]
abbrev stepsRow075 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(Y^2)),69),(((1)),134)]
abbrev stepsRow076 (X Y Z W a b : ℂ) : Row ℂ := [((((-1))/(X^2*Y^2)),72),(((1)),133)]
abbrev stepsRow077 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^2)/(Y^2)),63),(((1)),132)]
abbrev stepsRow078 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*Y^2)/(X^2)),60),(((1)),131)]
abbrev stepsRow079 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),130),((((-1))/(X^2)),120)]
abbrev stepsRow080 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),129),((((1))/(Z*W)),128)]
abbrev stepsRow081 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),128),(((1)),127)]
abbrev stepsRow082 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),127)]
abbrev stepsRow083 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),126),(((1)),58)]
abbrev stepsRow084 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),59),(((1)),125)]
abbrev stepsRow085 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),72),(((1)),124)]
abbrev stepsRow086 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),123),(((1)),73)]
abbrev stepsRow087 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),122),(((1)),70)]
abbrev stepsRow088 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),71),(((1)),121)]
abbrev stepsRow089 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),66),(((1)),120)]
abbrev stepsRow090 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),72),(((1)),119)]
abbrev stepsRow091 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),62),(((1)),118)]
abbrev stepsRow092 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),117),(((1)),67)]
abbrev stepsRow093 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),15),(((1)),116)]
abbrev stepsRow094 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),115),(((1)),3)]
abbrev stepsRow095 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),69),(((1)),114)]
abbrev stepsRow096 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),113),(((1)),65)]
abbrev stepsRow097 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),112),((((1))/(X^2)),73)]
abbrev stepsRow098 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),111),(((1)),6)]
abbrev stepsRow099 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),110),(((1)),4)]
abbrev stepsRow100 (X Y Z W a b : ℂ) : Row ℂ := [(((2)),104),(((1)),109),(((1)),101)]
abbrev stepsRow101 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),108),(((1)),103)]
abbrev stepsRow102 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),107),((((-1)*Y^2*W)/(X^2*Z)),105)]
abbrev stepsRow103 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),106),(((X*a)/(Y^2)),66),((((1))/(Y^2)),65)]
abbrev stepsRow104 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2*Z + (2)*X*Z*a + Z)/(Y^2*W)),104),(((X*Z*a)/(Y^2*W)),101),(((1)),105)]
abbrev stepsRow105 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),104)]
abbrev stepsRow106 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^2*Z + Z)/(W)),101),(((1)),103)]
abbrev stepsRow107 (X Y Z W a b : ℂ) : Row ℂ := [((((-1)*X^3*Z + X*Z + (-1)*Z*a)/(X*W)),101),(((1)),102)]
abbrev stepsRow108 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),101)]
abbrev stepsRow109 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),100)]
abbrev stepsRow110 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),99)]
abbrev stepsRow111 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),98)]
abbrev stepsRow112 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),97)]
abbrev stepsRow113 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),96)]
abbrev stepsRow114 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),95)]
abbrev stepsRow115 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),94)]
abbrev stepsRow116 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),93)]
abbrev stepsRow117 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),92)]
abbrev stepsRow118 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),91)]
abbrev stepsRow119 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),90)]
abbrev stepsRow120 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),89)]
abbrev stepsRow121 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),88)]
abbrev stepsRow122 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),87)]
abbrev stepsRow123 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),86)]
abbrev stepsRow124 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),85)]
abbrev stepsRow125 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),84)]
abbrev stepsRow126 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),83)]
abbrev stepsRow127 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),82)]
abbrev stepsRow128 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),81)]
abbrev stepsRow129 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),80)]
abbrev stepsRow130 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),79)]
abbrev stepsRow131 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),78)]
abbrev stepsRow132 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),77)]
abbrev stepsRow133 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),76)]
abbrev stepsRow134 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),62),(((1)),75)]
abbrev stepsRow135 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),74),(((1)),65)]
abbrev stepsRow136 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),69),(((1)),73)]
abbrev stepsRow137 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),72),(((1)),67)]
abbrev stepsRow138 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),66),(((1)),71)]
abbrev stepsRow139 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)),66),(((1)),70)]
abbrev stepsRow140 (X Y Z W a b : ℂ) : Row ℂ := [(((2)),66),(((1)),69)]
abbrev stepsRow141 (X Y Z W a b : ℂ) : Row ℂ := [((((2)*X^2 + (-1))/(Y^2)),66),(((1)),68)]
abbrev stepsRow142 (X Y Z W a b : ℂ) : Row ℂ := [(((-2)),66),(((1)),67)]
abbrev stepsRow143 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),66)]
abbrev stepsRow144 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),65)]
abbrev stepsRow145 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),64)]
abbrev stepsRow146 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),63)]
abbrev stepsRow147 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),62)]
abbrev stepsRow148 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),61)]
abbrev stepsRow149 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),60)]
abbrev stepsRow150 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),59)]
abbrev stepsRow151 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),58)]
abbrev stepsRow152 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),57)]
abbrev stepsRow153 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),56)]
abbrev stepsRow154 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),55)]
abbrev stepsRow155 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),54)]
abbrev stepsRow156 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),53)]
abbrev stepsRow157 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),52)]
abbrev stepsRow158 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),51)]
abbrev stepsRow159 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),50)]
abbrev stepsRow160 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),49)]
abbrev stepsRow161 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),48)]
abbrev stepsRow162 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),47)]
abbrev stepsRow163 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),46)]
abbrev stepsRow164 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),45)]
abbrev stepsRow165 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),44)]
abbrev stepsRow166 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),43)]
abbrev stepsRow167 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),42)]
abbrev stepsRow168 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),41)]
abbrev stepsRow169 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),40)]
abbrev stepsRow170 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),39),(((1)),4)]
abbrev stepsRow171 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)),6),(((1)),38)]
abbrev stepsRow172 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),37),(((1)),14)]
abbrev stepsRow173 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),36),(((1)),5)]
abbrev stepsRow174 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),35),(((1)),23)]
abbrev stepsRow175 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),34),(((1)),18)]
abbrev stepsRow176 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),33),(((1)),13)]
abbrev stepsRow177 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),32),(((1)),16)]
abbrev stepsRow178 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)),4),(((1)),31)]
abbrev stepsRow179 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),30),(((1)),6)]
abbrev stepsRow180 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),29),(((1)),3)]
abbrev stepsRow181 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),15),(((1)),28)]
abbrev stepsRow182 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),27),(((1)),20)]
abbrev stepsRow183 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),26),(((1)),21)]
abbrev stepsRow184 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),25),(((1)),2)]
abbrev stepsRow185 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),24),(((1)),1)]
abbrev stepsRow186 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),13),(((1)),23)]
abbrev stepsRow187 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),22),(((-1)),5)]
abbrev stepsRow188 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),21),((((1))/(X^2)),1)]
abbrev stepsRow189 (X Y Z W a b : ℂ) : Row ℂ := [((((1))/(X^2)),2),(((1)),20)]
abbrev stepsRow190 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),14),(((1)),19)]
abbrev stepsRow191 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),18),((((1))/(X^2)),16)]
abbrev stepsRow192 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),17),(((1)),8)]
abbrev stepsRow193 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),1),(((1)),16)]
abbrev stepsRow194 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),15),(((-1)),5)]
abbrev stepsRow195 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),14),(((1)),3)]
abbrev stepsRow196 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),13),(((1)),2)]
abbrev stepsRow197 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),12),(((1)),7)]
abbrev stepsRow198 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),11),(((1)),0)]
abbrev stepsRow199 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),10),(((1)),9)]
abbrev stepsRow200 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),9),(((-1)),3)]
abbrev stepsRow201 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),8),(((1)),5)]
abbrev stepsRow202 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),7),(((1)),0)]
abbrev stepsRow203 (X Y Z W a b : ℂ) : Row ℂ := [(((-1)),2),(((1)),6),(((-1)),5)]
abbrev stepsRow204 (X Y Z W a b : ℂ) : Row ℂ := [(((X^2 + (-1))/(X^2 + X*a)),2),(((1)),5)]
abbrev stepsRow205 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),4),((((-1)*X*a + (-1))/(X^2 + X*a)),2)]
abbrev stepsRow206 (X Y Z W a b : ℂ) : Row ℂ := [(((X^3*a + X^2*a^2 + X*a + (1))/(X^4 + X^3*a)),2),(((1)),3)]
abbrev stepsRow207 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),2)]
abbrev stepsRow208 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),1)]
abbrev stepsRow209 (X Y Z W a b : ℂ) : Row ℂ := [(((1)),0)]
def stepsTable (X Y Z W a b : ℂ) : Array (Row ℂ) := #[
  stepsRow000 X Y Z W a b,
  stepsRow001 X Y Z W a b,
  stepsRow002 X Y Z W a b,
  stepsRow003 X Y Z W a b,
  stepsRow004 X Y Z W a b,
  stepsRow005 X Y Z W a b,
  stepsRow006 X Y Z W a b,
  stepsRow007 X Y Z W a b,
  stepsRow008 X Y Z W a b,
  stepsRow009 X Y Z W a b,
  stepsRow010 X Y Z W a b,
  stepsRow011 X Y Z W a b,
  stepsRow012 X Y Z W a b,
  stepsRow013 X Y Z W a b,
  stepsRow014 X Y Z W a b,
  stepsRow015 X Y Z W a b,
  stepsRow016 X Y Z W a b,
  stepsRow017 X Y Z W a b,
  stepsRow018 X Y Z W a b,
  stepsRow019 X Y Z W a b,
  stepsRow020 X Y Z W a b,
  stepsRow021 X Y Z W a b,
  stepsRow022 X Y Z W a b,
  stepsRow023 X Y Z W a b,
  stepsRow024 X Y Z W a b,
  stepsRow025 X Y Z W a b,
  stepsRow026 X Y Z W a b,
  stepsRow027 X Y Z W a b,
  stepsRow028 X Y Z W a b,
  stepsRow029 X Y Z W a b,
  stepsRow030 X Y Z W a b,
  stepsRow031 X Y Z W a b,
  stepsRow032 X Y Z W a b,
  stepsRow033 X Y Z W a b,
  stepsRow034 X Y Z W a b,
  stepsRow035 X Y Z W a b,
  stepsRow036 X Y Z W a b,
  stepsRow037 X Y Z W a b,
  stepsRow038 X Y Z W a b,
  stepsRow039 X Y Z W a b,
  stepsRow040 X Y Z W a b,
  stepsRow041 X Y Z W a b,
  stepsRow042 X Y Z W a b,
  stepsRow043 X Y Z W a b,
  stepsRow044 X Y Z W a b,
  stepsRow045 X Y Z W a b,
  stepsRow046 X Y Z W a b,
  stepsRow047 X Y Z W a b,
  stepsRow048 X Y Z W a b,
  stepsRow049 X Y Z W a b,
  stepsRow050 X Y Z W a b,
  stepsRow051 X Y Z W a b,
  stepsRow052 X Y Z W a b,
  stepsRow053 X Y Z W a b,
  stepsRow054 X Y Z W a b,
  stepsRow055 X Y Z W a b,
  stepsRow056 X Y Z W a b,
  stepsRow057 X Y Z W a b,
  stepsRow058 X Y Z W a b,
  stepsRow059 X Y Z W a b,
  stepsRow060 X Y Z W a b,
  stepsRow061 X Y Z W a b,
  stepsRow062 X Y Z W a b,
  stepsRow063 X Y Z W a b,
  stepsRow064 X Y Z W a b,
  stepsRow065 X Y Z W a b,
  stepsRow066 X Y Z W a b,
  stepsRow067 X Y Z W a b,
  stepsRow068 X Y Z W a b,
  stepsRow069 X Y Z W a b,
  stepsRow070 X Y Z W a b,
  stepsRow071 X Y Z W a b,
  stepsRow072 X Y Z W a b,
  stepsRow073 X Y Z W a b,
  stepsRow074 X Y Z W a b,
  stepsRow075 X Y Z W a b,
  stepsRow076 X Y Z W a b,
  stepsRow077 X Y Z W a b,
  stepsRow078 X Y Z W a b,
  stepsRow079 X Y Z W a b,
  stepsRow080 X Y Z W a b,
  stepsRow081 X Y Z W a b,
  stepsRow082 X Y Z W a b,
  stepsRow083 X Y Z W a b,
  stepsRow084 X Y Z W a b,
  stepsRow085 X Y Z W a b,
  stepsRow086 X Y Z W a b,
  stepsRow087 X Y Z W a b,
  stepsRow088 X Y Z W a b,
  stepsRow089 X Y Z W a b,
  stepsRow090 X Y Z W a b,
  stepsRow091 X Y Z W a b,
  stepsRow092 X Y Z W a b,
  stepsRow093 X Y Z W a b,
  stepsRow094 X Y Z W a b,
  stepsRow095 X Y Z W a b,
  stepsRow096 X Y Z W a b,
  stepsRow097 X Y Z W a b,
  stepsRow098 X Y Z W a b,
  stepsRow099 X Y Z W a b,
  stepsRow100 X Y Z W a b,
  stepsRow101 X Y Z W a b,
  stepsRow102 X Y Z W a b,
  stepsRow103 X Y Z W a b,
  stepsRow104 X Y Z W a b,
  stepsRow105 X Y Z W a b,
  stepsRow106 X Y Z W a b,
  stepsRow107 X Y Z W a b,
  stepsRow108 X Y Z W a b,
  stepsRow109 X Y Z W a b,
  stepsRow110 X Y Z W a b,
  stepsRow111 X Y Z W a b,
  stepsRow112 X Y Z W a b,
  stepsRow113 X Y Z W a b,
  stepsRow114 X Y Z W a b,
  stepsRow115 X Y Z W a b,
  stepsRow116 X Y Z W a b,
  stepsRow117 X Y Z W a b,
  stepsRow118 X Y Z W a b,
  stepsRow119 X Y Z W a b,
  stepsRow120 X Y Z W a b,
  stepsRow121 X Y Z W a b,
  stepsRow122 X Y Z W a b,
  stepsRow123 X Y Z W a b,
  stepsRow124 X Y Z W a b,
  stepsRow125 X Y Z W a b,
  stepsRow126 X Y Z W a b,
  stepsRow127 X Y Z W a b,
  stepsRow128 X Y Z W a b,
  stepsRow129 X Y Z W a b,
  stepsRow130 X Y Z W a b,
  stepsRow131 X Y Z W a b,
  stepsRow132 X Y Z W a b,
  stepsRow133 X Y Z W a b,
  stepsRow134 X Y Z W a b,
  stepsRow135 X Y Z W a b,
  stepsRow136 X Y Z W a b,
  stepsRow137 X Y Z W a b,
  stepsRow138 X Y Z W a b,
  stepsRow139 X Y Z W a b,
  stepsRow140 X Y Z W a b,
  stepsRow141 X Y Z W a b,
  stepsRow142 X Y Z W a b,
  stepsRow143 X Y Z W a b,
  stepsRow144 X Y Z W a b,
  stepsRow145 X Y Z W a b,
  stepsRow146 X Y Z W a b,
  stepsRow147 X Y Z W a b,
  stepsRow148 X Y Z W a b,
  stepsRow149 X Y Z W a b,
  stepsRow150 X Y Z W a b,
  stepsRow151 X Y Z W a b,
  stepsRow152 X Y Z W a b,
  stepsRow153 X Y Z W a b,
  stepsRow154 X Y Z W a b,
  stepsRow155 X Y Z W a b,
  stepsRow156 X Y Z W a b,
  stepsRow157 X Y Z W a b,
  stepsRow158 X Y Z W a b,
  stepsRow159 X Y Z W a b,
  stepsRow160 X Y Z W a b,
  stepsRow161 X Y Z W a b,
  stepsRow162 X Y Z W a b,
  stepsRow163 X Y Z W a b,
  stepsRow164 X Y Z W a b,
  stepsRow165 X Y Z W a b,
  stepsRow166 X Y Z W a b,
  stepsRow167 X Y Z W a b,
  stepsRow168 X Y Z W a b,
  stepsRow169 X Y Z W a b,
  stepsRow170 X Y Z W a b,
  stepsRow171 X Y Z W a b,
  stepsRow172 X Y Z W a b,
  stepsRow173 X Y Z W a b,
  stepsRow174 X Y Z W a b,
  stepsRow175 X Y Z W a b,
  stepsRow176 X Y Z W a b,
  stepsRow177 X Y Z W a b,
  stepsRow178 X Y Z W a b,
  stepsRow179 X Y Z W a b,
  stepsRow180 X Y Z W a b,
  stepsRow181 X Y Z W a b,
  stepsRow182 X Y Z W a b,
  stepsRow183 X Y Z W a b,
  stepsRow184 X Y Z W a b,
  stepsRow185 X Y Z W a b,
  stepsRow186 X Y Z W a b,
  stepsRow187 X Y Z W a b,
  stepsRow188 X Y Z W a b,
  stepsRow189 X Y Z W a b,
  stepsRow190 X Y Z W a b,
  stepsRow191 X Y Z W a b,
  stepsRow192 X Y Z W a b,
  stepsRow193 X Y Z W a b,
  stepsRow194 X Y Z W a b,
  stepsRow195 X Y Z W a b,
  stepsRow196 X Y Z W a b,
  stepsRow197 X Y Z W a b,
  stepsRow198 X Y Z W a b,
  stepsRow199 X Y Z W a b,
  stepsRow200 X Y Z W a b,
  stepsRow201 X Y Z W a b,
  stepsRow202 X Y Z W a b,
  stepsRow203 X Y Z W a b,
  stepsRow204 X Y Z W a b,
  stepsRow205 X Y Z W a b,
  stepsRow206 X Y Z W a b,
  stepsRow207 X Y Z W a b,
  stepsRow208 X Y Z W a b,
  stepsRow209 X Y Z W a b
]
def steps (X Y Z W a b : ℂ) (i : ℕ) : Row ℂ := (stepsTable X Y Z W a b)[i]?.getD []

abbrev instructionsRow000 (X Y Z W a b : ℂ) : Row ℂ := [(1,4)]
abbrev instructionsRow001 (X Y Z W a b : ℂ) : Row ℂ := [(1 / (X ^ 2 * Z * W),0),((1 / (X ^ 2 * Z * W))*(-(1)),210)]
abbrev instructionsRow002 (X Y Z W a b : ℂ) : Row ℂ := [(1 / (Z * W),1),((1 / (Z * W))*(-(1)),210)]
abbrev instructionsRow003 (X Y Z W a b : ℂ) : Row ℂ := [(1,5),(-(1 / (X ^ 2 * Y ^ 2 * Z * W)),210)]
abbrev instructionsRow004 (X Y Z W a b : ℂ) : Row ℂ := [(1,6),(-(1 / (Y ^ 2 * Z * W)),210)]
abbrev instructionsRow005 (X Y Z W a b : ℂ) : Row ℂ := [(1,7),(-(1 / (X ^ 2 * Z * W)),210)]
abbrev instructionsRow006 (X Y Z W a b : ℂ) : Row ℂ := [(1,10),(-(1 / (Z * W)),210)]
abbrev instructionsRow007 (X Y Z W a b : ℂ) : Row ℂ := [(1,35),(-(1 / (Y ^ 2 * Z * W)),210)]
abbrev instructionsRow008 (X Y Z W a b : ℂ) : Row ℂ := [(1,36),(-(1 / (X ^ 2 * Y ^ 2 * Z * W)),210)]
abbrev instructionsRow009 (X Y Z W a b : ℂ) : Row ℂ := [(1,39),(-(-1 * Y ^ 2),217)]
abbrev instructionsRow010 (X Y Z W a b : ℂ) : Row ℂ := [(1,40),(-(-1 / X ^ 2),210)]
abbrev instructionsRow011 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 / (Y ^ 2 * Z * W),3),((X ^ 2 / (Y ^ 2 * Z * W))*(-(1)),220)]
abbrev instructionsRow012 (X Y Z W a b : ℂ) : Row ℂ := [(1,8),(-(X ^ 2 / (Y ^ 2 * Z * W)),220)]
abbrev instructionsRow013 (X Y Z W a b : ℂ) : Row ℂ := [(1,14),(-(X ^ 2 / (Z * W)),220)]
abbrev instructionsRow014 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 / (Z * W),31),((X ^ 2 / (Z * W))*(-(1)),220)]
abbrev instructionsRow015 (X Y Z W a b : ℂ) : Row ℂ := [(1,41),(-(-1 / Y ^ 2),212)]
abbrev instructionsRow016 (X Y Z W a b : ℂ) : Row ℂ := [(1,42),(-(-1 * X ^ 2),211)]
abbrev instructionsRow017 (X Y Z W a b : ℂ) : Row ℂ := [(1,43),(-(-1),217)]
abbrev instructionsRow018 (X Y Z W a b : ℂ) : Row ℂ := [(1,65),(-(-1),212)]
abbrev instructionsRow019 (X Y Z W a b : ℂ) : Row ℂ := [(1,22),(-(Z * W / (X ^ 2 * Y ^ 2)),228)]
abbrev instructionsRow020 (X Y Z W a b : ℂ) : Row ℂ := [(1,66),(-(-1 / (X ^ 2 * Y ^ 2)),210)]
abbrev instructionsRow021 (X Y Z W a b : ℂ) : Row ℂ := [(1,23),(-(X ^ 2 * Y ^ 2 / (Z * W)),230)]
abbrev instructionsRow022 (X Y Z W a b : ℂ) : Row ℂ := [(Z / (X ^ 2 * Y ^ 2 * W),2)]
abbrev instructionsRow023 (X Y Z W a b : ℂ) : Row ℂ := [(1,9)]
abbrev instructionsRow024 (X Y Z W a b : ℂ) : Row ℂ := [(1,11)]
abbrev instructionsRow025 (X Y Z W a b : ℂ) : Row ℂ := [(1,12)]
abbrev instructionsRow026 (X Y Z W a b : ℂ) : Row ℂ := [(1,13)]
abbrev instructionsRow027 (X Y Z W a b : ℂ) : Row ℂ := [(1,15)]
abbrev instructionsRow028 (X Y Z W a b : ℂ) : Row ℂ := [(1,16)]
abbrev instructionsRow029 (X Y Z W a b : ℂ) : Row ℂ := [(1,17)]
abbrev instructionsRow030 (X Y Z W a b : ℂ) : Row ℂ := [(1,18)]
abbrev instructionsRow031 (X Y Z W a b : ℂ) : Row ℂ := [(1,19)]
abbrev instructionsRow032 (X Y Z W a b : ℂ) : Row ℂ := [(1,20)]
abbrev instructionsRow033 (X Y Z W a b : ℂ) : Row ℂ := [(W / Z,21)]
abbrev instructionsRow034 (X Y Z W a b : ℂ) : Row ℂ := [(Z / W,24)]
abbrev instructionsRow035 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 * W / (Y ^ 2 * Z),25)]
abbrev instructionsRow036 (X Y Z W a b : ℂ) : Row ℂ := [(W / (X ^ 2 * Z),26)]
abbrev instructionsRow037 (X Y Z W a b : ℂ) : Row ℂ := [(1,27)]
abbrev instructionsRow038 (X Y Z W a b : ℂ) : Row ℂ := [(Y ^ 2 / (Z * W),28)]
abbrev instructionsRow039 (X Y Z W a b : ℂ) : Row ℂ := [(Z / (X ^ 2 * W),29)]
abbrev instructionsRow040 (X Y Z W a b : ℂ) : Row ℂ := [(W / (Y ^ 2 * Z),30)]
abbrev instructionsRow041 (X Y Z W a b : ℂ) : Row ℂ := [(Z / (Y ^ 2 * W),32)]
abbrev instructionsRow042 (X Y Z W a b : ℂ) : Row ℂ := [(Y ^ 2 / (X ^ 2 * Z * W),33)]
abbrev instructionsRow043 (X Y Z W a b : ℂ) : Row ℂ := [(W / (X ^ 2 * Y ^ 2 * Z),34),((W / (X ^ 2 * Y ^ 2 * Z))*(-(1)),244)]
abbrev instructionsRow044 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / Y ^ 2,37)]
abbrev instructionsRow045 (X Y Z W a b : ℂ) : Row ℂ := [(1,38)]
abbrev instructionsRow046 (X Y Z W a b : ℂ) : Row ℂ := [(1,44),(-(-1 / X ^ 2),255)]
abbrev instructionsRow047 (X Y Z W a b : ℂ) : Row ℂ := [(1,45),(-(-1 * X ^ 2),232)]
abbrev instructionsRow048 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / (X ^ 2 * Y ^ 2),46)]
abbrev instructionsRow049 (X Y Z W a b : ℂ) : Row ℂ := [(1,47),(-(-1 * Y ^ 2),251)]
abbrev instructionsRow050 (X Y Z W a b : ℂ) : Row ℂ := [(1,48),(-(-1 * X ^ 2),252)]
abbrev instructionsRow051 (X Y Z W a b : ℂ) : Row ℂ := [(1,49),(-(-1 * Y ^ 2 / X ^ 2),255)]
abbrev instructionsRow052 (X Y Z W a b : ℂ) : Row ℂ := [(1,50)]
abbrev instructionsRow053 (X Y Z W a b : ℂ) : Row ℂ := [(1,51)]
abbrev instructionsRow054 (X Y Z W a b : ℂ) : Row ℂ := [(1,52),(-(-1 * X ^ 2 / Y ^ 2),246)]
abbrev instructionsRow055 (X Y Z W a b : ℂ) : Row ℂ := [(1,53),(-(-1),248)]
abbrev instructionsRow056 (X Y Z W a b : ℂ) : Row ℂ := [(1,54)]
abbrev instructionsRow057 (X Y Z W a b : ℂ) : Row ℂ := [(1,55),(-(-1 * X ^ 2),249)]
abbrev instructionsRow058 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / (X ^ 2 * Y ^ 2),56)]
abbrev instructionsRow059 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / (X ^ 2 * Y ^ 2),57)]
abbrev instructionsRow060 (X Y Z W a b : ℂ) : Row ℂ := [(1,58)]
abbrev instructionsRow061 (X Y Z W a b : ℂ) : Row ℂ := [(1,59),(-(-1 * X ^ 2 / Y ^ 2),241)]
abbrev instructionsRow062 (X Y Z W a b : ℂ) : Row ℂ := [(1,60)]
abbrev instructionsRow063 (X Y Z W a b : ℂ) : Row ℂ := [(1,61)]
abbrev instructionsRow064 (X Y Z W a b : ℂ) : Row ℂ := [(1,62)]
abbrev instructionsRow065 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / (X ^ 2 * Y ^ 2),63)]
abbrev instructionsRow066 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * Z / W,64),((-1 * Z / W)*(-(-1 * X ^ 2 * Y ^ 2)),253),((-1 * Z / W)*(-(1)),243)]
abbrev instructionsRow067 (X Y Z W a b : ℂ) : Row ℂ := [(1,67),(-(-1 * X ^ 2 / Y ^ 2),252)]
abbrev instructionsRow068 (X Y Z W a b : ℂ) : Row ℂ := [(1,68),(-(-1 * Y ^ 2 / X ^ 2),255)]
abbrev instructionsRow069 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / (X ^ 2 * Y ^ 2),69)]
abbrev instructionsRow070 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / Y ^ 2,70)]
abbrev instructionsRow071 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / X ^ 2,71)]
abbrev instructionsRow072 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X ^ 2 / Y ^ 2,72)]
abbrev instructionsRow073 (X Y Z W a b : ℂ) : Row ℂ := [(1,73)]
abbrev instructionsRow074 (X Y Z W a b : ℂ) : Row ℂ := [(1,74)]
abbrev instructionsRow075 (X Y Z W a b : ℂ) : Row ℂ := [(1,75)]
abbrev instructionsRow076 (X Y Z W a b : ℂ) : Row ℂ := [(1,76)]
abbrev instructionsRow077 (X Y Z W a b : ℂ) : Row ℂ := [(1,77)]
abbrev instructionsRow078 (X Y Z W a b : ℂ) : Row ℂ := [(1,78)]
abbrev instructionsRow079 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / X ^ 2,79)]
abbrev instructionsRow080 (X Y Z W a b : ℂ) : Row ℂ := [(-1 / Y ^ 2,80),((-1 / Y ^ 2)*(-(1)),248)]
abbrev instructionsRow081 (X Y Z W a b : ℂ) : Row ℂ := [(1,81)]
abbrev instructionsRow082 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2),149),((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-((-1 * X ^ 2 * Y ^ 2 + -1 * Y ^ 2) / (X ^ 2 * Z * W))),291),((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-(1)),265),((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-(-1 * a / X)),239),((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-(1)),235),((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-(1 / X ^ 2)),231)]
abbrev instructionsRow083 (X Y Z W a b : ℂ) : Row ℂ := [(1,82),(-(1 / (X ^ 2 * Z * W)),292),(-(1 / (X ^ 2 * Z * W)),210)]
abbrev instructionsRow084 (X Y Z W a b : ℂ) : Row ℂ := [(1,83),(-(-1 / (X ^ 2 * Z * W)),292),(-(1 / (X ^ 2 * Z * W)),291),(-(1 / (X ^ 2 * Z * W)),210)]
abbrev instructionsRow085 (X Y Z W a b : ℂ) : Row ℂ := [(1,84),(-(-1 / (Z * W)),292),(-(1 / (Z * W)),291),(-(1 / (Z * W)),210)]
abbrev instructionsRow086 (X Y Z W a b : ℂ) : Row ℂ := [(1,85),(-(1 / (Z * W)),292),(-(1 / (Z * W)),210)]
abbrev instructionsRow087 (X Y Z W a b : ℂ) : Row ℂ := [(1,86),(-(X ^ 2 / (Z * W)),229),(-(X ^ 2 / (Z * W)),220)]
abbrev instructionsRow088 (X Y Z W a b : ℂ) : Row ℂ := [(1,87),(-(X ^ 2 / (Z * W)),230),(-(X ^ 2 / (Z * W)),220)]
abbrev instructionsRow089 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 * Y ^ 2,144),((X ^ 2 * Y ^ 2)*(-(1)),256),((X ^ 2 * Y ^ 2)*(-(1 / X ^ 2)),254),((X ^ 2 * Y ^ 2)*(-(-1 * a / X)),222),((X ^ 2 * Y ^ 2)*(-(1)),214)]
abbrev instructionsRow090 (X Y Z W a b : ℂ) : Row ℂ := [(1,156),(-(-1 * Y ^ 2 / (Z * W)),292),(-(1),239),(-(-1 * a / X),231)]
abbrev instructionsRow091 (X Y Z W a b : ℂ) : Row ℂ := [(1,168),(-((X * Y ^ 2 * a + Y ^ 2) / (X ^ 2 * Z * W)),292),(-(-1 * Y ^ 2 / (X ^ 2 * Z * W)),291),(-(-1 * a / X),260),(-(1 / X ^ 2),248)]
abbrev instructionsRow092 (X Y Z W a b : ℂ) : Row ℂ := [(1,171),(-(-1 * a / X),219),(-(1 / X ^ 2),212)]
abbrev instructionsRow093 (X Y Z W a b : ℂ) : Row ℂ := [(1,172),(-(-1 * a / X),227),(-(1 / X ^ 2),217)]
abbrev instructionsRow094 (X Y Z W a b : ℂ) : Row ℂ := [(1,173),(-(-1 * a / X),225),(-(1 / X ^ 2),214)]
abbrev instructionsRow095 (X Y Z W a b : ℂ) : Row ℂ := [(1,174),(-(-1 * a / X),226),(-(1 / X ^ 2),216)]
abbrev instructionsRow096 (X Y Z W a b : ℂ) : Row ℂ := [(1,177),(-((-1 * X * Y ^ 2 * a + -1 * Y ^ 2) / (X ^ 2 * Z * W)),292),(-(Y ^ 2 * a / (X * Z * W)),291),(-(-1 * a / X),265),(-(1 / X ^ 2),239)]
abbrev instructionsRow097 (X Y Z W a b : ℂ) : Row ℂ := [(1,183),(-(Y ^ 2 / (Z * W)),292),(-(-1 * Y ^ 2 / (Z * W)),291),(-(1),248),(-(-1 * a / X),228)]
abbrev instructionsRow098 (X Y Z W a b : ℂ) : Row ℂ := [(1,193),(-(-1 * b / Y),231),(-(1 / Y ^ 2),226),(-(1),223)]
abbrev instructionsRow099 (X Y Z W a b : ℂ) : Row ℂ := [(1,206),(-(-1 * b / Y),228),(-(1),224),(-(1 / Y ^ 2),219)]
abbrev instructionsRow100 (X Y Z W a b : ℂ) : Row ℂ := [(1,94),(-(-1 * W / Z),276),(-(1),243)]
abbrev instructionsRow101 (X Y Z W a b : ℂ) : Row ℂ := [(1,111),(-(-1 * Z / W),310),(-(1),276),(-(1),267),(-(1),259),(-(1),244)]
abbrev instructionsRow102 (X Y Z W a b : ℂ) : Row ℂ := [(1,124),(-(-1 * W / (X ^ 2 * Z)),311),(-(1),247),(-(1),246),(-(1),241)]
abbrev instructionsRow103 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2,145),((X ^ 2)*(-(-1 * a / (X * Y ^ 2))),299),((X ^ 2)*(-(1)),262),((X ^ 2)*(-(-1 * a / X)),254),((X ^ 2)*(-(1)),222)]
abbrev instructionsRow104 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X ^ 2,146),((-1 * X ^ 2)*(-(-1 * Z / (Y ^ 2 * W))),312),((-1 * X ^ 2)*(-(Z * a / (X * Y ^ 2 * W))),310),((-1 * X ^ 2)*(-(1 / (X ^ 2 * Y ^ 2))),276),((-1 * X ^ 2)*(-(1)),257),((-1 * X ^ 2)*(-(-1 * Z / (X ^ 2 * Y ^ 2 * W))),243),((-1 * X ^ 2)*(-(1 / X ^ 2)),240),((-1 * X ^ 2)*(-(-1 * a / X)),236),((-1 * X ^ 2)*(-(1)),233)]
abbrev instructionsRow105 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2),178),((X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2))*(-(-1 * Y ^ 2 * W / (X ^ 2 * Z))),314),((X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2))*(-(-1 * W / Z)),276),((X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2))*(-(1)),247),((X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2))*(-(1)),243)]
abbrev instructionsRow106 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X ^ 2,153),((-1 * X ^ 2)*(-((2 * X * Z + Z * a) / (X * W))),315),((-1 * X ^ 2)*(-(1 / X ^ 2)),311),((-1 * X ^ 2)*(-(-1 * Z / W)),310),((-1 * X ^ 2)*(-(-1 * a / X)),276),((-1 * X ^ 2)*(-(1)),267),((-1 * X ^ 2)*(-(1)),238)]
abbrev instructionsRow107 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * Y ^ 2 * Z / W,147),((-1 * Y ^ 2 * Z / W)*(-(W / (Y ^ 2 * Z))),316),((-1 * Y ^ 2 * Z / W)*(-((2 * X * a + 1) / (X ^ 2 * Y ^ 2))),315),((-1 * Y ^ 2 * Z / W)*(-(-1 * W / (Y ^ 2 * Z))),311),((-1 * Y ^ 2 * Z / W)*(-(-1 * a / (X * Y ^ 2))),310),((-1 * Y ^ 2 * Z / W)*(-(-1 * W / (X ^ 2 * Y ^ 2 * Z))),276),((-1 * Y ^ 2 * Z / W)*(-(W * a / (X * Y ^ 2 * Z))),267),((-1 * Y ^ 2 * Z / W)*(-(1)),264),((-1 * Y ^ 2 * Z / W)*(-(1 / X ^ 2)),242),((-1 * Y ^ 2 * Z / W)*(-(-1 * a / X)),237),((-1 * Y ^ 2 * Z / W)*(-(1)),234)]
abbrev instructionsRow108 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1),201),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(-1 * X ^ 2 * W / (Y ^ 2 * Z))),317),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(-1 * W / (Y ^ 2 * Z))),316),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-((Y ^ 2 + 2 * Y * b + 1) / Y ^ 2)),315),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(-1 * b / Y)),310),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(-1 * W / Z)),276),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(1)),271),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(1)),243),((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(1)),242)]
abbrev instructionsRow109 (X Y Z W a b : ℂ) : Row ℂ := [(1,150),(-((X ^ 3 * Z + -1 * X * Z * a ^ 2 + Z * a) / (X * Y ^ 2 * W)),318),(-(1 / Y ^ 2),317),(-((-1 * X ^ 2 * Z * a + -2 * X * Z * a ^ 2 + 2 * X * Z + -1 * Z * a) / (X * Y ^ 2 * W)),315),(-(a / X),314),(-(X * Z * a / (Y ^ 2 * W)),312),(-(-1 * Z / (Y ^ 2 * W)),310),(-(1 / X ^ 2),282),(-(-1 * a / X),240),(-(1),236)]
abbrev instructionsRow110 (X Y Z W a b : ℂ) : Row ℂ := [(1,163),(-((X ^ 3 * Z * a + -1 * X * Z * a + Z) / (X ^ 2 * W)),318),(-(a / X),316),(-((-1 * X ^ 2 * Z + 2 * Z) / (X ^ 2 * W)),315),(-(-1 * a / X),311),(-(-1 * Z / (X ^ 2 * W)),310),(-(1),276),(-(1 / X ^ 2),267)]
abbrev instructionsRow111 (X Y Z W a b : ℂ) : Row ℂ := [(1,89),(-(1),320),(-((-1 * X ^ 2 * Z + Z) / (X ^ 2 * Y ^ 2 * W)),318),(-(-1 / (X ^ 2 * Y ^ 2)),316),(-(Z / (X ^ 2 * W)),315),(-(-1 / X ^ 2),276),(-(Z / (X ^ 2 * W)),271),(-(Z / (X ^ 2 * W)),243)]
abbrev instructionsRow112 (X Y Z W a b : ℂ) : Row ℂ := [(1,167),(-((X ^ 3 * Z + -1 * X * Z + Z * a) / (X * W)),318),(-(1),316),(-(-1 * Z / (X ^ 2 * W)),315),(-(-1 * a / X),259),(-(1 / X ^ 2),244)]
abbrev instructionsRow113 (X Y Z W a b : ℂ) : Row ℂ := [(1,127),(-(1),322),(-(1),320),(-((X ^ 3 * Z + -1 * X * Z + Z * a) / (X * W)),318),(-(1),317),(-(2 * Z / (X ^ 2 * W)),315),(-(-1 * Z / (X ^ 2 * W)),310),(-(1),249),(-(1),238)]
abbrev instructionsRow114 (X Y Z W a b : ℂ) : Row ℂ := [(1,88),(-(1),323),(-((X ^ 2 * Z + -1 * Z) / (X ^ 2 * Y ^ 2 * W)),318),(-(1 / (X ^ 2 * Y ^ 2)),316),(-(Z / (X ^ 2 * W)),315),(-(-1 / (X ^ 2 * Y ^ 2)),311),(-(Z / (X ^ 2 * W)),264)]
abbrev instructionsRow115 (X Y Z W a b : ℂ) : Row ℂ := [(1,186),(-(1 / Y ^ 2),322),(-((Z * a ^ 2 + -1 * Z) / (Y ^ 2 * W)),318),(-((X ^ 2 * Z * a + 2 * X * Z * a ^ 2 + Z * a) / (X * Y ^ 2 * W)),315),(-(-1 * a / X),314),(-(1 / X ^ 2),283),(-(1),251)]
abbrev instructionsRow116 (X Y Z W a b : ℂ) : Row ℂ := [(1,190),(-((X ^ 2 * Y * b + -1 * X * Y ^ 2 * a + X * a + -1 * Y * b) / (X ^ 2 * Y ^ 2)),318),(-(W * b / (X ^ 2 * Y * Z)),316),(-((-1 * X ^ 2 * Y ^ 2 + X ^ 2 + -2 * X * Y ^ 2 * a + 2 * X * a + -1 * Y ^ 2 + 2) / (X ^ 2 * Y ^ 2)),315),(-((Y ^ 2 * W + -1 * W) / (X ^ 2 * Z)),314),(-(1),312),(-(-1 * W / (X ^ 2 * Y ^ 2 * Z)),276),(-(1 / Y ^ 2),247),(-(-1 * b / Y),241),(-(1),234)]
abbrev instructionsRow117 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 * Z / W,90),((X ^ 2 * Z / W)*(-(1)),326),((X ^ 2 * Z / W)*(-((-1 * X * a + 1) / X ^ 2)),318),((X ^ 2 * Z / W)*(-((-1 * X ^ 2 + -2 * X * a + 1) / X ^ 2)),315),((X ^ 2 * Z / W)*(-(Y ^ 2 * W / (X ^ 2 * Z))),314),((X ^ 2 * Z / W)*(-(1)),312),((X ^ 2 * Z / W)*(-(-1 / X ^ 2)),310),((X ^ 2 * Z / W)*(-(W / (X ^ 2 * Z))),267)]
abbrev instructionsRow118 (X Y Z W a b : ℂ) : Row ℂ := [(1,170),(-(1),327),(-(-1 * Z / (X ^ 2 * Y ^ 2 * W)),318),(-(Z * a / (X * Y ^ 2 * W)),315),(-(-1 * a / (X * Y ^ 2)),276),(-(-1 * a / X),272),(-(1 / X ^ 2),251)]
abbrev instructionsRow119 (X Y Z W a b : ℂ) : Row ℂ := [(1,191),(-((X ^ 2 * Z + -1 * Z) / W),318),(-(1),316),(-((Y * Z * b + 2 * Z) / (Y ^ 2 * W)),315),(-(-1 * Z / (Y ^ 2 * W)),310),(-(-1 * b / Y),276),(-(1 / Y ^ 2),259),(-(1),236)]
abbrev instructionsRow120 (X Y Z W a b : ℂ) : Row ℂ := [(W / Z,92),((W / Z)*(-(1)),329),((W / Z)*(-(X ^ 2 * Z / W)),318),((W / Z)*(-(1)),316)]
abbrev instructionsRow121 (X Y Z W a b : ℂ) : Row ℂ := [(1,128),(-(1),330),(-(-1 * X ^ 2 * W / (Y ^ 2 * Z)),322),(-((-1 * X ^ 4 + X ^ 2 + -1 * X * a) / Y ^ 2),318),(-(-1 * X ^ 2 * W / (Y ^ 2 * Z)),317),(-(-2 / Y ^ 2),315),(-(-1 * W / (Y ^ 2 * Z)),311),(-(1 / Y ^ 2),310),(-(1),271),(-(-1 * W / (Y ^ 2 * Z)),267),(-(1),264),(-(-1 * W / (Y ^ 2 * Z)),259),(-(1),250),(-(1),245),(-(1),242),(-(1),237)]
abbrev instructionsRow122 (X Y Z W a b : ℂ) : Row ℂ := [(1,93),(-(Z / W),331),(-(-1 * X ^ 2 * Z / W),318),(-(-1),316),(-(-2 * Z / W),315),(-(1),311),(-(Z / W),310)]
abbrev instructionsRow123 (X Y Z W a b : ℂ) : Row ℂ := [(1,135),(-(1),332),(-(1),329),(-(1),327),(-(X ^ 2 / Y ^ 2),322),(-((X ^ 4 * Z + -1 * X ^ 2 * Z + X * Z * a) / (Y ^ 2 * W)),318),(-(X ^ 2 / Y ^ 2),317),(-(-1 * X ^ 2 * Z / (Y ^ 2 * W)),312),(-(-1 * Z / (Y ^ 2 * W)),310),(-(1),283),(-(1),282),(-(1 / Y ^ 2),276),(-(1),272),(-(1),257),(-(1),251),(-(1),240),(-(1),236)]
abbrev instructionsRow124 (X Y Z W a b : ℂ) : Row ℂ := [(1,91),(-(W / (X ^ 2 * Z)),333),(-((X * a + -1) / X ^ 2),318),(-((X ^ 2 + 2 * X * a + 1) / X ^ 2),315),(-(-1 * Y ^ 2 * W / (X ^ 2 * Z)),314),(-(W / (X ^ 2 * Z)),259),(-(1),247)]
abbrev instructionsRow125 (X Y Z W a b : ℂ) : Row ℂ := [(1,152),(-(1 / X ^ 2),330),(-((X ^ 3 * a + -1 * X * a + a ^ 2 + -1) / Y ^ 2),318),(-(X * W * a / (Y ^ 2 * Z)),317),(-(-2 / Y ^ 2),315),(-(1 / Y ^ 2),310),(-(-1 * W / (Y ^ 2 * Z)),267),(-(-1 * a / X),242),(-(1),237)]
abbrev instructionsRow126 (X Y Z W a b : ℂ) : Row ℂ := [(1,158),(-(1 / X ^ 2),329),(-((-1 * X ^ 3 * Z * a + 2 * X * Z * a + -1 * Z * a ^ 2) / (Y ^ 2 * W)),318),(-(-1 * X * a / Y ^ 2),317),(-((X ^ 2 * Z + 2 * X * Z * a + Z) / (Y ^ 2 * W)),315),(-(-1),314),(-(-1 * X ^ 2 * Z / (Y ^ 2 * W)),312),(-(-1 * a / X),282),(-(1),240)]
abbrev instructionsRow127 (X Y Z W a b : ℂ) : Row ℂ := [(1,161),(-(1),332),(-(-1 * a / X),327),(-(-1 * Z / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / (X ^ 2 * Y ^ 2)),276),(-(1 / X ^ 2),272)]
abbrev instructionsRow128 (X Y Z W a b : ℂ) : Row ℂ := [(1,169),(-(1),331),(-((X ^ 3 * a + -1 * X * a + 1) / (X ^ 2 * Y ^ 2)),318),(-(W * a / (X * Y ^ 2 * Z)),316),(-(-1 * a / X),271),(-(-1 * W / (X ^ 2 * Y ^ 2 * Z)),259),(-(1 / X ^ 2),250)]
abbrev instructionsRow129 (X Y Z W a b : ℂ) : Row ℂ := [(1,175),(-(1),333),(-(Z / (X ^ 2 * Y ^ 2 * W)),318),(-((X * Z * a + 2 * Z) / (X ^ 2 * Y ^ 2 * W)),315),(-(-1 * Z / (X ^ 2 * Y ^ 2 * W)),310),(-(-1 * a / X),257),(-(1 / X ^ 2),236)]
abbrev instructionsRow130 (X Y Z W a b : ℂ) : Row ℂ := [(1,176),(-(1),330),(-((-1 * X ^ 3 * a + X * a + -1) / (X ^ 2 * Y ^ 2)),318),(-(-1 * W * a / (X * Y ^ 2 * Z)),316),(-(-2 / (X ^ 2 * Y ^ 2)),315),(-(W * a / (X * Y ^ 2 * Z)),311),(-(1 / (X ^ 2 * Y ^ 2)),310),(-(-1 * W / (X ^ 2 * Y ^ 2 * Z)),267),(-(-1 * a / X),264),(-(1 / X ^ 2),237)]
abbrev instructionsRow131 (X Y Z W a b : ℂ) : Row ℂ := [(1,138),(-(1),340),(-(1),338),(-(1),335),(-(1),334),(-(1),326),(-(2 / (X ^ 2 * Y ^ 2)),315),(-(-1 * W / (X ^ 2 * Y ^ 2 * Z)),276),(-(1),253),(-(1),234)]
abbrev instructionsRow132 (X Y Z W a b : ℂ) : Row ℂ := [(1,181),(-(-1 * a / X),333),(-(1),329),(-(-1 * Z / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / X ^ 2),257)]
abbrev instructionsRow133 (X Y Z W a b : ℂ) : Row ℂ := [(1,142),(-(1),342),(-(1),339),(-(1),337),(-(1),336),(-(1),328),(-(1),325),(-(1),324),(-(1),321),(-(1),319),(-(-2 * Z / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / (X ^ 2 * Y ^ 2)),276),(-(-1 * Z / (X ^ 2 * Y ^ 2 * W)),243),(-(1),233),(-(1),232)]
abbrev instructionsRow134 (X Y Z W a b : ℂ) : Row ℂ := [(1,103),(-(-1 * Z / W),318),(-(-1 / W),315),(-(1 / W),310),(-(1),259),(-(1),228),(-(1 / W),210)]
abbrev instructionsRow135 (X Y Z W a b : ℂ) : Row ℂ := [(1,104),(-(Z / W),318),(-((2 * Z + -1) / W),315),(-((-1 * Z + 1) / W),310),(-(-1 / Z),276),(-(1),267),(-(1 / W),243),(-(1),231),(-(1 / W),210)]
abbrev instructionsRow136 (X Y Z W a b : ℂ) : Row ℂ := [(1,107),(-((-1 * X ^ 2 + 1) / W),318),(-(-1 / Z),316),(-(-1 * Z / W),315),(-(X ^ 2 / W),312),(-(-1 * Y ^ 2 / (Z * W)),292),(-(1),260),(-(X ^ 2 / W),247),(-(1),244),(-(X ^ 2 / W),241),(-(X ^ 2 / W),220)]
abbrev instructionsRow137 (X Y Z W a b : ℂ) : Row ℂ := [(1,108),(-((X ^ 2 + -1) / W),318),(-(1 / Z),316),(-(-1 * Z / W),315),(-(X ^ 2 / W),312),(-(-1 / Z),311),(-(Y ^ 2 / (Z * W)),292),(-(-1 * Y ^ 2 / (Z * W)),291),(-(1),276),(-(1),265),(-(X ^ 2 / W),247),(-(X ^ 2 / W),246),(-(X ^ 2 / W),220)]
abbrev instructionsRow138 (X Y Z W a b : ℂ) : Row ℂ := [(Y ^ 2 / W,109),((Y ^ 2 / W)*(-(1)),330),((Y ^ 2 / W)*(-(-1 * X ^ 2 * W / (Y ^ 2 * Z))),322),((Y ^ 2 / W)*(-((X ^ 2 * Z + -1 * X ^ 2 + -1 * Z + 1) / Y ^ 2)),318),((Y ^ 2 / W)*(-((Z * W + -1 * W) / (Y ^ 2 * Z))),316),((Y ^ 2 / W)*(-(1)),292),((Y ^ 2 / W)*(-(1)),271),((Y ^ 2 / W)*(-(1)),245),((Y ^ 2 / W)*(-(W / Y ^ 2)),226)]
abbrev instructionsRow139 (X Y Z W a b : ℂ) : Row ℂ := [(Y ^ 2 / W,110),((Y ^ 2 / W)*(-(1)),331),((Y ^ 2 / W)*(-((-1 * X ^ 4 + -1 * X ^ 2 * Z + 2 * X ^ 2 + -1 * X * a + Z + -1) / Y ^ 2)),318),((Y ^ 2 / W)*(-(-1 * X ^ 2 * W / (Y ^ 2 * Z))),317),((Y ^ 2 / W)*(-((-1 * Z * W + W) / (Y ^ 2 * Z))),316),((Y ^ 2 / W)*(-((Z * W + -1 * W) / (Y ^ 2 * Z))),311),((Y ^ 2 / W)*(-(W / Y ^ 2)),299),((Y ^ 2 / W)*(-(-1)),292),((Y ^ 2 / W)*(-(1)),291),((Y ^ 2 / W)*(-(1)),264),((Y ^ 2 / W)*(-(1)),242),((Y ^ 2 / W)*(-(W / Y ^ 2)),219)]
abbrev instructionsRow140 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X ^ 2 * Y ^ 2 / Z,119),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(-1 * Z / (X ^ 2 * Y ^ 2))),349),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1)),342),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1)),336),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1)),328),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1)),325),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1)),321),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(Z / (X ^ 2 * Y ^ 2))),318),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(2 * Z / (X ^ 2 * Y ^ 2))),315),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(-1 * Z / (X ^ 2 * Y ^ 2))),310),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(-1 / (X ^ 2 * W))),292),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1 / (X ^ 2 * W))),291),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(-1 * Z / (X ^ 2 * Y ^ 2))),265),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1)),229),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(-1 * Z / (X ^ 2 * Y ^ 2))),212)]
abbrev instructionsRow141 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 / Y ^ 2,106),((X ^ 2 / Y ^ 2)*(-(-1)),350),((X ^ 2 / Y ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),331),((X ^ 2 / Y ^ 2)*(-(1)),323),((X ^ 2 / Y ^ 2)*(-(1 / W)),318),((X ^ 2 / Y ^ 2)*(-(1 / (X ^ 2 * Z))),316),((X ^ 2 / Y ^ 2)*(-(-1 / (X ^ 2 * Z))),311),((X ^ 2 / Y ^ 2)*(-(1)),305),((X ^ 2 / Y ^ 2)*(-(1 / X ^ 2)),299),((X ^ 2 / Y ^ 2)*(-(-1 * Y ^ 2 / (X ^ 2 * W))),292),((X ^ 2 / Y ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),291),((X ^ 2 / Y ^ 2)*(-(1)),289),((X ^ 2 / Y ^ 2)*(-(1)),266),((X ^ 2 / Y ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),264),((X ^ 2 / Y ^ 2)*(-(-1 / (X ^ 2 * Z))),259),((X ^ 2 / Y ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),250)]
abbrev instructionsRow142 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X ^ 2 * Y ^ 2 / Z,120),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(-1 * Z / (X ^ 2 * Y ^ 2))),348),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1)),343),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1)),339),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1)),337),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1)),324),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1)),319),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(-1 * Z / (X ^ 2 * Y ^ 2))),318),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(-1 * Z / (X ^ 2 * Y ^ 2))),299),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1 / (X ^ 2 * W))),292),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(-1 * Z / (X ^ 2 * Y ^ 2))),260),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(1)),230),((-1 * X ^ 2 * Y ^ 2 / Z)*(-(-1 * Z / (X ^ 2 * Y ^ 2))),216)]
abbrev instructionsRow143 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5),204),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(-1 / (X ^ 2 * Y ^ 2))),352),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1 / (X ^ 2 * Y ^ 2))),350),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1 / (X ^ 2 * Y ^ 2))),347),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(-1 / (X ^ 2 * Y ^ 2))),346),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1 / Y ^ 2)),307),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-((Y ^ 2 + 1) / (X ^ 2 * Y ^ 2))),299),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1)),289),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1)),286),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1)),274),((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(-1 * b / Y)),261)]
abbrev instructionsRow144 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X ^ 2,105),((-1 * X ^ 2)*(-((-2 * X ^ 2 + -1 * X * a + 1) / X ^ 2)),353),((-1 * X ^ 2)*(-(-1)),352),((-1 * X ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),330),((-1 * X ^ 2)*(-(1)),320),((-1 * X ^ 2)*(-(-1 / W)),318),((-1 * X ^ 2)*(-(-1 / (X ^ 2 * Z))),316),((-1 * X ^ 2)*(-(-2 / (X ^ 2 * W))),315),((-1 * X ^ 2)*(-(Y ^ 2 / X ^ 2)),313),((-1 * X ^ 2)*(-(1 / (X ^ 2 * W))),310),((-1 * X ^ 2)*(-(1)),302),((-1 * X ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),292),((-1 * X ^ 2)*(-(1)),278),((-1 * X ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),271),((-1 * X ^ 2)*(-(1)),270),((-1 * X ^ 2)*(-(-1 / (X ^ 2 * Z))),267),((-1 * X ^ 2)*(-(Y ^ 2 / (X ^ 2 * W))),237)]
abbrev instructionsRow145 (X Y Z W a b : ℂ) : Row ℂ := [(1,100),(-(1 / X ^ 2),354),(-(2 / X ^ 2),353),(-(1 / X ^ 2),352),(-(-1 / X ^ 2),347),(-((X ^ 4 * Z + -1 * X ^ 2 * Z + X * Z * a + 1) / (X ^ 2 * W)),318),(-(1),317),(-(2 / (X ^ 2 * W)),315),(-(1),300),(-(1),281),(-(-1 / (X ^ 2 * Z)),276),(-(1 / (X ^ 2 * W)),243),(-(1 / (X ^ 2 * W)),210)]
abbrev instructionsRow146 (X Y Z W a b : ℂ) : Row ℂ := [(1,117),(-(-1),354),(-(-2),353),(-(Y ^ 2 / X ^ 2),351),(-(1 / X ^ 2),350),(-(-1 / X ^ 2),346),(-((-1 * X ^ 2 + -1 * X * W * a + 1) / (X ^ 2 * W)),318),(-(-1 / (X ^ 2 * Z)),316),(-((-1 * X ^ 2 + -2 * X * a + -1) / X ^ 2),315),(-(Y ^ 2 * W / (X ^ 2 * Z)),314),(-(1),312),(-(1 / (X ^ 2 * W)),310),(-(1),307),(-(1),306),(-(1),278),(-(-1 / (X ^ 2 * Z)),276),(-(-1 / (X ^ 2 * Z)),267),(-(1),266),(-(-1 / (X ^ 2 * Z)),259),(-(-1 / (X ^ 2 * Z)),244),(-(-1 / (X ^ 2 * Z)),210)]
abbrev instructionsRow147 (X Y Z W a b : ℂ) : Row ℂ := [(Y ^ 2 / Z,123),((Y ^ 2 / Z)*(-(-1 * Z / Y ^ 2)),354),((Y ^ 2 / Z)*(-(2 * Z / Y ^ 2)),353),((Y ^ 2 / Z)*(-(Z / Y ^ 2)),352),((Y ^ 2 / Z)*(-(-1 * Z / Y ^ 2)),347),((Y ^ 2 / Z)*(-(-1 * Z / Y ^ 2)),344),((Y ^ 2 / Z)*(-(1)),333),((Y ^ 2 / Z)*(-(1)),332),((Y ^ 2 / Z)*(-((X ^ 4 * Z + -1 * X ^ 2 * Z) / (Y ^ 2 * W))),318),((Y ^ 2 / Z)*(-(X ^ 2 / Y ^ 2)),317),((Y ^ 2 / Z)*(-((-1 * X ^ 2 * Z + -2 * X * Z * a + -1 * Z * W + -2 * Z) / (Y ^ 2 * W))),315),((Y ^ 2 / Z)*(-(1)),314),((Y ^ 2 / Z)*(-(-1)),292),((Y ^ 2 / Z)*(-(1)),291),((Y ^ 2 / Z)*(-(1)),282),((Y ^ 2 / Z)*(-(1 / Y ^ 2)),276),((Y ^ 2 / Z)*(-(1)),272),((Y ^ 2 / Z)*(-(-1 * Z / Y ^ 2)),223),((Y ^ 2 / Z)*(-(-1 * Z / Y ^ 2)),219)]
abbrev instructionsRow148 (X Y Z W a b : ℂ) : Row ℂ := [(1,99),(-(1 / X ^ 2),357),(-(-2 / X ^ 2),353),(-(1 / X ^ 2),350),(-(-1 / X ^ 2),346),(-(1),322),(-(-1 / (X ^ 2 * W)),318),(-(1 / (X ^ 2 * W)),310),(-(1),307),(-(1),284),(-(-1 / (X ^ 2 * Z)),276),(-(1 / (X ^ 2 * W)),243),(-(1 / (X ^ 2 * W)),210)]
abbrev instructionsRow149 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2 / Y ^ 2,116),((X ^ 2 / Y ^ 2)*(-(-1)),357),((X ^ 2 / Y ^ 2)*(-(-1 / X ^ 2)),354),((X ^ 2 / Y ^ 2)*(-((-1 * X * a + 1) / X ^ 2)),353),((X ^ 2 / Y ^ 2)*(-(1 / X ^ 2)),352),((X ^ 2 / Y ^ 2)*(-(-1 / X ^ 2)),347),((X ^ 2 / Y ^ 2)*(-((X ^ 2 + X * W * a + -1) / (X ^ 2 * W))),318),((X ^ 2 / Y ^ 2)*(-(1 / (X ^ 2 * Z))),316),((X ^ 2 / Y ^ 2)*(-((X ^ 2 + 2 * X * a + 1) / X ^ 2)),315),((X ^ 2 / Y ^ 2)*(-(-1 * Y ^ 2 * W / (X ^ 2 * Z))),314),((X ^ 2 / Y ^ 2)*(-(Y ^ 2 / X ^ 2)),313),((X ^ 2 / Y ^ 2)*(-(-1 / (X ^ 2 * Z))),311),((X ^ 2 / Y ^ 2)*(-(1 / (X ^ 2 * W))),310),((X ^ 2 / Y ^ 2)*(-(1)),301),((X ^ 2 / Y ^ 2)*(-(1)),300),((X ^ 2 / Y ^ 2)*(-(1 / X ^ 2)),299),((X ^ 2 / Y ^ 2)*(-(1)),289),((X ^ 2 / Y ^ 2)*(-(1)),288),((X ^ 2 / Y ^ 2)*(-(-1 / (X ^ 2 * Z))),276),((X ^ 2 / Y ^ 2)*(-(1)),270),((X ^ 2 / Y ^ 2)*(-(-1 / (X ^ 2 * Z))),267),((X ^ 2 / Y ^ 2)*(-(-1 / (X ^ 2 * Z))),259),((X ^ 2 / Y ^ 2)*(-(1)),247),((X ^ 2 / Y ^ 2)*(-(-1 / (X ^ 2 * Z))),244),((X ^ 2 / Y ^ 2)*(-(-1 / (X ^ 2 * Z))),210)]
abbrev instructionsRow150 (X Y Z W a b : ℂ) : Row ℂ := [(1,121),(-(1),358),(-(1 / X ^ 2),354),(-((2 * X ^ 2 + 1) / X ^ 2),353),(-(-1),350),(-(-1 * Y ^ 2 / (X ^ 2 * Z)),333),(-(-1 * Y ^ 2 / (X ^ 2 * Z)),332),(-((-1 * X ^ 4 + X ^ 2 * W + X ^ 2 + -1 * X * a + -1 * W + -1) / (X ^ 2 * W)),318),(-(-1 / Z),317),(-(W / (X ^ 2 * Z)),316),(-(-1 / (X ^ 2 * W)),315),(-(-1 * W / (X ^ 2 * Z)),311),(-(1 / (X ^ 2 * W)),310),(-(1),305),(-(Y ^ 2 / (X ^ 2 * Z)),292),(-(-1 * Y ^ 2 / (X ^ 2 * Z)),291),(-(-1 * Y ^ 2 / (X ^ 2 * Z)),282),(-(1),281),(-(-1 / (X ^ 2 * Z)),276),(-(-1 * Y ^ 2 / (X ^ 2 * Z)),272),(-(1),261),(-(1),246),(-(-1 * Y ^ 2 / (X ^ 2 * Z)),236)]
abbrev instructionsRow151 (X Y Z W a b : ℂ) : Row ℂ := [(1,122),(-(1 / X ^ 2),357),(-(1),355),(-((-2 * X ^ 2 + -1) / X ^ 2),353),(-(-1),352),(-(-1 * Y ^ 2 / (X ^ 2 * Z)),329),(-(-1 * Y ^ 2 / (X ^ 2 * Z)),327),(-(-1 / Z),322),(-((-1 * X ^ 2 * W + W + 1) / (X ^ 2 * W)),318),(-(-1 * W / (X ^ 2 * Z)),316),(-(1 / (X ^ 2 * W)),315),(-(1),302),(-(1 / X ^ 2),299),(-(-1 * Y ^ 2 / (X ^ 2 * Z)),292),(-(1),284),(-(-1 * Y ^ 2 / (X ^ 2 * Z)),283),(-(1),263),(-(-1 * Y ^ 2 / (X ^ 2 * Z)),257),(-(-1 * Y ^ 2 / (X ^ 2 * Z)),251),(-(1),241)]
abbrev instructionsRow152 (X Y Z W a b : ℂ) : Row ℂ := [(1,148),(-(1 / X ^ 2),359),(-(a / (X * Y ^ 2)),354),(-((a ^ 2 + -1) / Y ^ 2),353),(-(-1 * a / X),313),(-(1 / Y ^ 2),299),(-(1),254)]
abbrev instructionsRow153 (X Y Z W a b : ℂ) : Row ℂ := [(1,129),(-(1),362),(-(Y ^ 2 / X ^ 2),359),(-(-1),354),(-((Y ^ 2 + 1) / (X ^ 2 * Y ^ 2)),353),(-(1 / (X ^ 2 * Y ^ 2)),349),(-(1 / (X ^ 2 * W)),331),(-(1),328),(-((-1 * X ^ 4 + X ^ 2 + -1 * X * a + -1 * Y ^ 2 * Z + 1) / (X ^ 2 * Y ^ 2 * W)),318),(-(-1 / (Y ^ 2 * Z)),317),(-(-1 / (X ^ 2 * W)),315),(-(1 / (X ^ 2 * W)),310),(-(1),306),(-(-1 / (X ^ 2 * W)),292),(-(1 / (X ^ 2 * W)),291),(-(1),288),(-(-1 / (X ^ 2 * Z)),276),(-(1),268),(-(1),261),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),259),(-(1 / (X ^ 2 * W)),250),(-(1 / (X ^ 2 * W)),243),(-(1 / (X ^ 2 * W)),242),(-(1),238),(-(1 / (X ^ 2 * W)),210)]
abbrev instructionsRow154 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2,165),((X ^ 2)*(-((2 * X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + 2) / (X ^ 2 * Y ^ 2))),353),((X ^ 2)*(-(1)),352),((X ^ 2)*(-(-1 / (X ^ 2 * Y ^ 2))),350),((X ^ 2)*(-(a / X)),349),((X ^ 2)*(-(-1)),347),((X ^ 2)*(-(1 / (X ^ 2 * Y ^ 2))),346),((X ^ 2)*(-(-1 * a / X)),297),((X ^ 2)*(-(1)),295),((X ^ 2)*(-(1)),279)]
abbrev instructionsRow155 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2,179),((X ^ 2)*(-((-2 * X ^ 2 * Y ^ 2 + -1 * X * Y ^ 2 * a + -2) / (X ^ 2 * Y ^ 2))),353),((X ^ 2)*(-(-1 / (X ^ 2 * Y ^ 2))),352),((X ^ 2)*(-(1)),350),((X ^ 2)*(-(a / X)),348),((X ^ 2)*(-(1 / (X ^ 2 * Y ^ 2))),347),((X ^ 2)*(-(-1)),346),((X ^ 2)*(-(-1 * a / X)),298),((X ^ 2)*(-(1)),296),((X ^ 2)*(-(1)),286)]
abbrev instructionsRow156 (X Y Z W a b : ℂ) : Row ℂ := [(1,187),(-(1 / Y ^ 2),356),(-((2 * X ^ 2 * a + X + -1 * a) / (X * Y ^ 2)),353),(-(-1 * a / X),351),(-(1 / X ^ 2),287),(-(1),255)]
abbrev instructionsRow157 (X Y Z W a b : ℂ) : Row ℂ := [(1,130),(-(1),366),(-(-1),357),(-(1),356),(-((-1 * Y ^ 2 + -1) / (X ^ 2 * Y ^ 2)),353),(-(1 / (X ^ 2 * Y ^ 2)),348),(-(1),339),(-(1 / (X ^ 2 * W)),330),(-(-1 / (Y ^ 2 * Z)),322),(-((Y ^ 2 * Z + -1) / (X ^ 2 * Y ^ 2 * W)),318),(-((2 * Y ^ 2 * Z + -1 * Y ^ 2 + -2) / (X ^ 2 * Y ^ 2 * W)),315),(-((-1 * Y ^ 2 * Z + Y ^ 2 + 1) / (X ^ 2 * Y ^ 2 * W)),310),(-(1),301),(-(1 / X ^ 2),299),(-(1 / (X ^ 2 * W)),292),(-(1),269),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),267),(-(1),263),(-(1),249),(-(1 / (X ^ 2 * W)),245),(-(1 / (X ^ 2 * W)),237),(-(1 / (X ^ 2 * W)),210)]
abbrev instructionsRow158 (X Y Z W a b : ℂ) : Row ℂ := [(1,192),(-(1),355),(-((Y * b + 3) / (X ^ 2 * Y ^ 2)),353),(-(-1 / (X ^ 2 * Y ^ 2)),350),(-(1 / (X ^ 2 * Y ^ 2)),346),(-(-1 * b / (X ^ 2 * Y)),299),(-(-1 * b / Y),289),(-(1),275),(-(1 / Y ^ 2),261)]
abbrev instructionsRow159 (X Y Z W a b : ℂ) : Row ℂ := [(1,194),(-(-1),357),(-(-1 * b / (X ^ 2 * Y)),354),(-(-2 / Y ^ 2),353),(-(1 / X ^ 2),351),(-(1 / (X ^ 2 * Y ^ 2)),348),(-(1),301),(-(-1 * b / Y),281),(-(1),269),(-(1 / Y ^ 2),266)]
abbrev instructionsRow160 (X Y Z W a b : ℂ) : Row ℂ := [(1,195),(-(-1 * b / Y),357),(-(-1 / Y ^ 2),354),(-((-1 * X * a + 2 * Y ^ 2 + 1) / Y ^ 2),353),(-(1),352),(-(1 / Y ^ 2),349),(-(1),313)]
abbrev instructionsRow161 (X Y Z W a b : ℂ) : Row ℂ := [(1,166),(-(-1 * a / X),370),(-(1),364),(-(-2 / (X ^ 2 * Y ^ 2)),353),(-(1 / (X ^ 2 * Y ^ 2)),350),(-(1 / X ^ 2),285)]
abbrev instructionsRow162 (X Y Z W a b : ℂ) : Row ℂ := [(1,180),(-(1 / X ^ 2),370),(-(-1 * a / X),364),(-(-1),353),(-(-1),349),(-(1),297)]
abbrev instructionsRow163 (X Y Z W a b : ℂ) : Row ℂ := [(1,200),(-(1),366),(-(1),356),(-(-1 * b / Y),355),(-(-1 / (X ^ 2 * Y ^ 2)),353),(-(1 / (X ^ 2 * Y ^ 2)),299),(-(1 / Y ^ 2),289)]
abbrev instructionsRow164 (X Y Z W a b : ℂ) : Row ℂ := [(1,96),(-(1),373),(-(1),369),(-(1),336),(-(-1 / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / (X ^ 2 * Y ^ 2 * W)),310),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),276),(-(1 / (X ^ 2 * Y ^ 2 * W)),243),(-(1 / (X ^ 2 * Y ^ 2 * W)),210)]
abbrev instructionsRow165 (X Y Z W a b : ℂ) : Row ℂ := [(1,202),(-(1),363),(-((-2 * X ^ 2 + Y ^ 2 + 2 * Y * b) / (X ^ 2 * Y ^ 2)),353),(-(-1 / Y ^ 2),352),(-(-1 * b / (X ^ 2 * Y)),350),(-(b / (X ^ 2 * Y)),346),(-(-1 * b / Y),307),(-(1 / Y ^ 2),302),(-(1),261)]
abbrev instructionsRow166 (X Y Z W a b : ℂ) : Row ℂ := [(1,95),(-(1),375),(-(1),371),(-(1),343),(-(-1 / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / (X ^ 2 * Y ^ 2 * W)),310),(-(1 / (X ^ 2 * Y ^ 2 * W)),210)]
abbrev instructionsRow167 (X Y Z W a b : ℂ) : Row ℂ := [(1,203),(-(1 / Y ^ 2),360),(-((Y ^ 2 + 1) / (X ^ 2 * Y ^ 2)),357),(-(b / (X ^ 2 * Y)),354),(-(a * b / (X * Y)),353),(-(-1 * Y * b / X ^ 2),313),(-(1),284),(-(1),273),(-(-1 * b / Y),270)]
abbrev instructionsRow168 (X Y Z W a b : ℂ) : Row ℂ := [(X ^ 2,164),((X ^ 2)*(-(1)),377),((X ^ 2)*(-(-1 * a / X)),365),((X ^ 2)*(-(1)),353),((X ^ 2)*(-(-1)),348),((X ^ 2)*(-(1)),298)]
abbrev instructionsRow169 (X Y Z W a b : ℂ) : Row ℂ := [(1,207),(-(1),358),(-((-1 * Y * b + -3) / (X ^ 2 * Y ^ 2)),353),(-(-1 / (X ^ 2 * Y ^ 2)),352),(-(1 / (X ^ 2 * Y ^ 2)),347),(-(1 / (X ^ 2 * Y ^ 2)),299),(-(-1 * b / Y),278),(-(1 / Y ^ 2),263),(-(1),258)]
abbrev instructionsRow170 (X Y Z W a b : ℂ) : Row ℂ := [(1,97),(-(1),370),(-(X ^ 2 / Y ^ 2),322),(-(1 / (Y ^ 2 * W)),318),(-(2 / (Y ^ 2 * W)),315),(-(1),283),(-(-1 / (Y ^ 2 * Z)),276),(-(1 / (Y ^ 2 * W)),243),(-(1 / (Y ^ 2 * W)),210)]
abbrev instructionsRow171 (X Y Z W a b : ℂ) : Row ℂ := [(1,98),(-(1),378),(-((X ^ 4 * Z + -1 * X ^ 2 * Z + X * Z * a + -1) / (Y ^ 2 * W)),318),(-(X ^ 2 / Y ^ 2),317),(-(1 / (Y ^ 2 * W)),310),(-(1),308),(-(1),282),(-(-1 / (Y ^ 2 * Z)),276),(-(1 / (Y ^ 2 * W)),243),(-(1 / (Y ^ 2 * W)),210)]
abbrev instructionsRow172 (X Y Z W a b : ℂ) : Row ℂ := [(1,101),(-(-2 / Y ^ 2),353),(-(1 / Y ^ 2),350),(-(1),332),(-(X * a / (Y ^ 2 * W)),318),(-((X ^ 2 + 2 * X * a + 1) / (Y ^ 2 * W)),315),(-(-1 / Z),314),(-(-1 / (Y ^ 2 * Z)),311),(-(1),285),(-(X ^ 2 / (Y ^ 2 * W)),247),(-(X ^ 2 / (Y ^ 2 * W)),246),(-(X ^ 2 / (Y ^ 2 * W)),241),(-(X ^ 2 / (Y ^ 2 * W)),220)]
abbrev instructionsRow173 (X Y Z W a b : ℂ) : Row ℂ := [(1,102),(-(2 / Y ^ 2),353),(-(1 / Y ^ 2),352),(-(1),329),(-(-1 * X * a / (Y ^ 2 * W)),318),(-((-1 * X ^ 2 + -2 * X * a + -1) / (Y ^ 2 * W)),315),(-(1 / Z),314),(-(X ^ 2 / (Y ^ 2 * W)),312),(-(-1 / (Y ^ 2 * Z)),311),(-(1),280),(-(X ^ 2 / (Y ^ 2 * W)),246),(-(X ^ 2 / (Y ^ 2 * W)),241),(-(X ^ 2 / (Y ^ 2 * W)),220)]
abbrev instructionsRow174 (X Y Z W a b : ℂ) : Row ℂ := [(1,112),(-(1),377),(-(1),368),(-(1),367),(-(1),341),(-(-1 / (X ^ 2 * Y ^ 2 * W)),315),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),311),(-(1 / (X ^ 2 * Y ^ 2 * W)),310),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),267),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),259),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),244),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),210)]
abbrev instructionsRow175 (X Y Z W a b : ℂ) : Row ℂ := [(1,113),(-(1),379),(-(1),372),(-(1),363),(-(1),335),(-(-1 / (X ^ 2 * Y ^ 2 * W)),315),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),311),(-(1 / (X ^ 2 * Y ^ 2 * W)),310),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),276),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),267),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),259),(-(-1 / (X ^ 2 * Y ^ 2 * Z)),210)]
abbrev instructionsRow176 (X Y Z W a b : ℂ) : Row ℂ := [(1,125),(-(1),364),(-(-1 * X * Z * a / (Y ^ 2 * W)),318),(-((-1 * X ^ 2 * Z + -2 * X * Z * a + -1 * Z + -1) / (Y ^ 2 * W)),315),(-(1),314),(-(1 / (Y ^ 2 * W)),310),(-(-1 / (Y ^ 2 * Z)),276),(-(1 / (Y ^ 2 * W)),243),(-(1 / (Y ^ 2 * W)),210)]
abbrev instructionsRow177 (X Y Z W a b : ℂ) : Row ℂ := [(1,126),(-(1),365),(-(X * Z * a / (Y ^ 2 * W)),318),(-((X ^ 2 * Z + 2 * X * Z * a + Z + -1) / (Y ^ 2 * W)),315),(-(-1),314),(-(-1 * X ^ 2 * Z / (Y ^ 2 * W)),312),(-(1 / (Y ^ 2 * W)),310),(-(1),240),(-(1 / (Y ^ 2 * W)),210)]
abbrev instructionsRow178 (X Y Z W a b : ℂ) : Row ℂ := [(1,131),(-(-1 / Y ^ 2),354),(-((-1 * X * a + 2 * Y ^ 2) / Y ^ 2),353),(-(1),352),(-(-1 * X ^ 2 / (Y ^ 2 * Z)),322),(-((-1 * X ^ 2 + -1 * Y ^ 2) / (Y ^ 2 * W)),318),(-(-1 / (Y ^ 2 * Z)),316),(-((-1 * Y ^ 2 * Z + -1 * Z + -2) / (Y ^ 2 * W)),315),(-(1),313),(-((Y ^ 2 + 1) / (Y ^ 2 * W)),310),(-(1),309),(-((Y ^ 2 + Z) / (Z * W)),292),(-(-1 * Y ^ 2 / (Z * W)),291),(-((Y ^ 2 * Z + -1 * Y ^ 2 + Z) / (Y ^ 2 * Z)),276),(-(1),272),(-(1 / W),271),(-(-1 / (Y ^ 2 * Z)),267),(-(1),265),(-(1 / W),245),(-(1 / W),243),(-(1 / W),237),(-(1),224),(-(1 / W),210)]
abbrev instructionsRow179 (X Y Z W a b : ℂ) : Row ℂ := [(1,132),(-((-2 * X ^ 2 + -2 * Y ^ 2 + 1) / Y ^ 2),353),(-(1),351),(-(1),350),(-((-1 * X ^ 4 + 2 * X ^ 2 + -1 * X * a + Y ^ 2) / (Y ^ 2 * W)),318),(-(-1 * X ^ 2 / (Y ^ 2 * Z)),317),(-(1 / (Y ^ 2 * Z)),316),(-((-1 * Y ^ 2 * Z + 2 * Y ^ 2 + -1 * Z) / (Y ^ 2 * W)),315),(-(-1 / (Y ^ 2 * Z)),311),(-((-1 * Y ^ 2 + -1 * Z) / (Z * W)),292),(-(1 / W),291),(-(-1 / Z),276),(-(1 / W),264),(-(1),260),(-(-1 / (Y ^ 2 * Z)),259),(-(1),257),(-(1 / W),250),(-(1),244),(-(1 / W),243),(-(1 / W),242),(-(1),223),(-(1 / W),210)]
abbrev instructionsRow180 (X Y Z W a b : ℂ) : Row ℂ := [(1,133),(-(1),359),(-(-1),353),(-(X ^ 2 / W),341),(-(X ^ 2 / W),338),(-((-1 * X ^ 2 * Y ^ 2 * Z + -1 * X * Y ^ 2 * a + Y ^ 2 * Z + -1 * Z) / (Y ^ 2 * W)),318),(-(-1),316),(-((-1 * X ^ 2 * Y ^ 2 + -2 * X * Y ^ 2 * a + -1 * Y ^ 2 + 1) / (Y ^ 2 * W)),315),(-(Y ^ 2 / Z),314),(-(X ^ 2 / W),312),(-((Z + -1) / Z),311),(-(1),299),(-(-1 * Y ^ 2 / (Z * W)),292),(-(-1 / (Y ^ 2 * Z)),276),(-(1),251),(-(X ^ 2 / W),246),(-(X ^ 2 / W),241),(-(1),239),(-(X ^ 2 / W),234),(-(X ^ 2 / W),230),(-(X ^ 2 / W),220),(-(1),219)]
abbrev instructionsRow181 (X Y Z W a b : ℂ) : Row ℂ := [(1,134),(-(X ^ 2 / Y ^ 2),356),(-(1),353),(-(X ^ 2 / W),340),(-(X ^ 2 / W),335),(-((X ^ 2 * Y ^ 2 * Z + X * Y ^ 2 * a + -1 * Y ^ 2 * Z + Z) / (Y ^ 2 * W)),318),(-(1),316),(-((X ^ 2 * Y ^ 2 + 2 * X * Y ^ 2 * a + Y ^ 2 + 2 * Z + 1) / (Y ^ 2 * W)),315),(-(-1 * Y ^ 2 / Z),314),(-(-1 / Z),311),(-(-1 * Z / (Y ^ 2 * W)),310),(-(Y ^ 2 / (Z * W)),292),(-(-1 * Y ^ 2 / (Z * W)),291),(-(1),287),(-(X ^ 2 / W),253),(-(1),248),(-(X ^ 2 / W),247),(-(X ^ 2 / W),246),(-(X ^ 2 / W),241),(-(1),236),(-(X ^ 2 / W),229),(-(1),226),(-(X ^ 2 / W),220)]
abbrev instructionsRow182 (X Y Z W a b : ℂ) : Row ℂ := [(1,136),(-(1),374),(-((Y ^ 2 + 1) / (X ^ 2 * Y ^ 2)),357),(-(1),355),(-((-2 * X ^ 2 * Y ^ 2 + -1 * Y ^ 2 + 2) / (X ^ 2 * Y ^ 2)),353),(-(-1),352),(-(-1 / (X ^ 2 * Y ^ 2)),350),(-(1 / (X ^ 2 * Y ^ 2)),346),(-(1),340),(-(-1 / (X ^ 2 * Z)),329),(-(-1 / (Y ^ 2 * Z)),322),(-((-1 * X ^ 2 * Y ^ 2 * W + -1 * X * a + Y ^ 2 * W + Y ^ 2 + 1) / (X ^ 2 * Y ^ 2 * W)),318),(-(-1 * W / (X ^ 2 * Z)),316),(-((-1 * X ^ 2 + -2 * X * a + 2 * Y ^ 2) / (X ^ 2 * Y ^ 2 * W)),315),(-(1 / (X ^ 2 * Z)),314),(-(1 / (Y ^ 2 * W)),312),(-(-1 / (X ^ 2 * Z)),311),(-(1),302),(-(1 / X ^ 2),299),(-((-1 * Y ^ 2 + -1 * W) / (X ^ 2 * Z * W)),292),(-(1),284),(-(-1 / (X ^ 2 * Z)),283),(-(-1 / (X ^ 2 * Z)),276),(-(1),275),(-(1),273),(-(1),263),(-(-1 / (X ^ 2 * Z)),259),(-(-1 / (X ^ 2 * Z)),257),(-(1),252),(-(-1 / (X ^ 2 * Z)),251),(-(-1 / (X ^ 2 * Z)),244),(-(1),241),(-(-1 / (X ^ 2 * Z)),240),(-(-1 / (X ^ 2 * Z)),210)]
abbrev instructionsRow183 (X Y Z W a b : ℂ) : Row ℂ := [(1,137),(-(1),375),(-(1),358),(-((Y ^ 2 + 1) / (X ^ 2 * Y ^ 2)),354),(-((2 * X ^ 2 * Y ^ 2 + Y ^ 2 + -2) / (X ^ 2 * Y ^ 2)),353),(-(-1 / (X ^ 2 * Y ^ 2)),352),(-(-1),350),(-(1 / (X ^ 2 * Y ^ 2)),347),(-(1),338),(-(-1 / (X ^ 2 * Z)),332),(-((-1 * X ^ 4 + X ^ 2 * Y ^ 2 * W + X ^ 2 + -1 * Y ^ 2 * W + -1 * Y ^ 2 + -1) / (X ^ 2 * Y ^ 2 * W)),318),(-(-1 / (Y ^ 2 * Z)),317),(-(W / (X ^ 2 * Z)),316),(-((X + 2 * a) / (X * Y ^ 2 * W)),315),(-(-1 / (X ^ 2 * Z)),314),(-((-1 * W + -1) / (X ^ 2 * Z)),311),(-((Y ^ 2 + 1) / (X ^ 2 * Y ^ 2 * W)),310),(-(1),305),(-((Y ^ 2 + W) / (X ^ 2 * Z * W)),292),(-((-1 * Y ^ 2 + -1 * W) / (X ^ 2 * Z * W)),291),(-(-1 / (X ^ 2 * Z)),282),(-(1),281),(-((-1 * Y ^ 2 + -1) / (X ^ 2 * Y ^ 2 * Z)),276),(-(-1 / (X ^ 2 * Z)),272),(-(-1 / (X ^ 2 * Z)),267),(-(1),262),(-(1),261),(-(1),258),(-(1),246),(-(-1 / (X ^ 2 * Z)),244),(-(-1 / (X ^ 2 * Z)),236),(-(1),235),(-(-1 / (X ^ 2 * Z)),210)]
abbrev instructionsRow184 (X Y Z W a b : ℂ) : Row ℂ := [(1,139),(-(-1 / Y ^ 2),353),(-(1),345),(-(1 / W),331),(-(1),327),(-((X ^ 2 + Y ^ 2 * Z) / (Y ^ 2 * W)),318),(-(1 / (Y ^ 2 * Z)),316),(-((2 * Z + -1) / W),315),(-(-1 / (Y ^ 2 * Z)),311),(-((-1 * Z + 1) / W),310),(-(1 / Y ^ 2),299),(-(-1 / W),292),(-(1 / W),291),(-(1),267),(-(1 / W),264),(-(-1 / (Y ^ 2 * Z)),259),(-(1),254),(-(1 / W),250),(-(1),212),(-(1 / W),210)]
abbrev instructionsRow185 (X Y Z W a b : ℂ) : Row ℂ := [(1,140),(-(1 / Y ^ 2),353),(-(1),344),(-(1),333),(-(1 / W),330),(-((-1 * X ^ 2 + -1 * Y ^ 2 * Z) / (Y ^ 2 * W)),318),(-(-1 / (Y ^ 2 * Z)),316),(-((-1 * Y ^ 2 + -2) / (Y ^ 2 * W)),315),(-((Y ^ 2 + 1) / (Y ^ 2 * W)),310),(-(1 / W),292),(-(-1 / Z),276),(-(1 / W),271),(-(-1 / (Y ^ 2 * Z)),267),(-(1),259),(-(1),255),(-(1 / W),243),(-(1 / W),237),(-(1),216),(-(1 / W),210)]
abbrev instructionsRow186 (X Y Z W a b : ℂ) : Row ℂ := [(1,154),(-(-1 * a / X),359),(-(-1 / Y ^ 2),354),(-(-1 * X * a / Y ^ 2),353),(-(1),313)]
abbrev instructionsRow187 (X Y Z W a b : ℂ) : Row ℂ := [(1,155),(-(1),383),(-(-2 / X ^ 2),353),(-(1 / X ^ 2),350),(-(-1 / X ^ 2),346),(-(1 / X ^ 2),296),(-(-1 * a / (X * Z * W)),292),(-(a / (X * Z * W)),291),(-(-1 * a / X),290)]
abbrev instructionsRow188 (X Y Z W a b : ℂ) : Row ℂ := [(-1,157),((-1)*(-(1 / X ^ 2)),395),((-1)*(-(1)),393),((-1)*(-(1)),378),((-1)*(-(-2 * a / (X * Y ^ 2))),353),((-1)*(-(-1 * a / (X * Y ^ 2))),352),((-1)*(-(-1 * a / X)),280)]
abbrev instructionsRow189 (X Y Z W a b : ℂ) : Row ℂ := [(1,182),(-(1),370),(-(2 * a / (X * Y ^ 2)),353),(-(-1 * a / (X * Y ^ 2)),350),(-(-1 * a / X),285)]
abbrev instructionsRow190 (X Y Z W a b : ℂ) : Row ℂ := [(1,184),(-(2 / X ^ 2),353),(-(1 / X ^ 2),352),(-(-1 / X ^ 2),347),(-(1 / X ^ 2),295),(-(a / (X * Z * W)),292),(-(-1 * a / X),277)]
abbrev instructionsRow191 (X Y Z W a b : ℂ) : Row ℂ := [(-1,185),((-1)*(-(1 / X ^ 2)),387),((-1)*(-(1)),385),((-1)*(-(-1 * X * a / Y ^ 2)),356),((-1)*(-((-2 * X ^ 2 + 1) / Y ^ 2)),353),((-1)*(-(1)),351),((-1)*(-(-1 * a / X)),287)]
abbrev instructionsRow192 (X Y Z W a b : ℂ) : Row ℂ := [(1,188),(-(1 / Y ^ 2),356),(-(-1 * Y * b / (X ^ 2 * Z * W)),292),(-(Y * b / (X ^ 2 * Z * W)),291),(-(-1 * b / Y),235),(-(1),215)]
abbrev instructionsRow193 (X Y Z W a b : ℂ) : Row ℂ := [(-1,189),((-1)*(-(1)),395),((-1)*(-(1)),387),((-1)*(-(-2 / Y ^ 2)),353),((-1)*(-(1 / Y ^ 2)),350),((-1)*(-(Y * b / (Z * W))),292),((-1)*(-(-1 * b / Y)),239),((-1)*(-(1)),216)]
abbrev instructionsRow194 (X Y Z W a b : ℂ) : Row ℂ := [(-1,196),((-1)*(-(1)),397),((-1)*(-(-1 / Y ^ 2)),357),((-1)*(-((2 * X ^ 2 * b + -2 * Y) / (X ^ 2 * Y))),353),((-1)*(-(b / Y)),352),((-1)*(-(1 / X ^ 2)),350),((-1)*(-(-1 / X ^ 2)),346),((-1)*(-(1)),307),((-1)*(-(1)),303),((-1)*(-(-1 * b / Y)),302),((-1)*(-(1 / Y ^ 2)),301)]
abbrev instructionsRow195 (X Y Z W a b : ℂ) : Row ℂ := [(1,197),(-(1 / Y ^ 2),354),(-(2 * b / Y),353),(-(-1 * b / Y),350),(-(-1 * Y ^ 2 / (Z * W)),292),(-(1),239)]
abbrev instructionsRow196 (X Y Z W a b : ℂ) : Row ℂ := [(-1,198),((-1)*(-(1)),394),((-1)*(-(1)),386),((-1)*(-(1)),354),((-1)*(-(b / Y)),353),((-1)*(-(-1 * b / Y)),348),((-1)*(-(1 / Y ^ 2)),224)]
abbrev instructionsRow197 (X Y Z W a b : ℂ) : Row ℂ := [(1,199),(-(-1 * b / Y),360),(-(-1 / X ^ 2),354),(-(-1 * a / X),353),(-(Y ^ 2 / X ^ 2),313),(-(1),270),(-(1 / Y ^ 2),211)]
abbrev instructionsRow198 (X Y Z W a b : ℂ) : Row ℂ := [(1,205),(-(-1 * b / Y),361),(-((-2 * X ^ 2 + 1) / X ^ 2),353),(-(Y ^ 2 / X ^ 2),351),(-(1),266),(-(1 / Y ^ 2),215)]
abbrev instructionsRow199 (X Y Z W a b : ℂ) : Row ℂ := [(1,143),(-(1),408),(-(1),407),(-(-1),405),(-(-1),404),(-(1),402),(-(1),400),(-(1),397),(-(1),393),(-(1),392),(-(1),385),(-(1),384),(-(1),379),(-(1),377),(-(1),376),(-(1),375),(-(1),374),(-(1),373),(-(1),372),(-(1),371),(-(1),369),(-(1),368),(-(1),367),(-(1),366),(-(1),363),(-(1),362),(-(-1),361),(-(-1),360),(-(1 / (X ^ 2 * Y ^ 2)),357),(-(1 / (X ^ 2 * Y ^ 2)),354),(-(-2 / (X ^ 2 * Y ^ 2)),352),(-(-2 / (X ^ 2 * Y ^ 2)),350),(-(1 / (X ^ 2 * Y ^ 2)),349),(-(1 / (X ^ 2 * Y ^ 2)),348),(-(2 / (X ^ 2 * Y ^ 2)),347),(-(2 / (X ^ 2 * Y ^ 2)),346),(-(1),304),(-(1),303),(-(1 / (X ^ 2 * Y ^ 2)),299),(-(1),294),(-(1),293),(-(1),286),(-(1),279),(-(1),275),(-(1),274),(-(1),273),(-(1),269),(-(1),268),(-(1),262),(-(1),258),(-(1),256),(-(1),218),(-(1),213)]
abbrev instructionsRow200 (X Y Z W a b : ℂ) : Row ℂ := [(1,208),(-(1),372),(-(2 / (X ^ 2 * Y ^ 2)),353),(-(-1 / (X ^ 2 * Y ^ 2)),350),(-(1 / (X ^ 2 * Y ^ 2)),346),(-(1 / Z),339),(-(1),325),(-(1),304),(-(1),275)]
abbrev instructionsRow201 (X Y Z W a b : ℂ) : Row ℂ := [(1,209),(-(1),397),(-(1),379),(-(1 / (X ^ 2 * Y ^ 2)),357),(-(1 / Z),343),(-(1),342),(-(1),273)]
abbrev instructionsRow202 (X Y Z W a b : ℂ) : Row ℂ := [(1,141),(-(-1),411),(-(-1),410),(-(1),409),(-(-1),405),(-(-1),404),(-(1),402),(-(1),400),(-(1),393),(-(1),366),(-(-1),360),(-(1 / (X ^ 2 * Y ^ 2)),354),(-(-2 / (X ^ 2 * Y ^ 2)),353),(-(-1 / (X ^ 2 * Y ^ 2)),352),(-(-1 / (X ^ 2 * Y ^ 2)),345),(-(1),339),(-(1),338),(-(1),337),(-(1),334),(-(1),324),(-(1),319),(-((-1 * Z + -1 * W) / (X ^ 2 * Y ^ 2 * W)),318),(-((-1 * Z + -1 * W) / (X ^ 2 * Y ^ 2 * W)),315),(-(-1 / (X ^ 2 * Y ^ 2)),311),(-(Z / (X ^ 2 * Y ^ 2 * W)),310),(-(1),303),(-(1),294),(-(1 / (X ^ 2 * Z * W)),292),(-(1 / (X ^ 2 * Z * W)),291),(-(1),279),(-(-1 / (X ^ 2 * Y ^ 2)),276),(-(1),274),(-(1),269),(-(-1 / (X ^ 2 * Y ^ 2)),267),(-(1),262),(-(-1 / (X ^ 2 * Y ^ 2)),260),(-(1),258),(-(-1 / (X ^ 2 * Y ^ 2)),248),(-(-1 / (X ^ 2 * Y ^ 2)),244),(-(-1 / (X ^ 2 * Y ^ 2)),243),(-(-1 / (X ^ 2 * Y ^ 2)),239),(-(1),234),(-(1),232),(-(-1 / (X ^ 2 * Y ^ 2)),231),(-(1),230),(-(-1 / (X ^ 2 * Y ^ 2)),226),(-(-1 / (X ^ 2 * Y ^ 2)),224),(-(-1 / (X ^ 2 * Y ^ 2)),223),(-(-1 / (X ^ 2 * Y ^ 2)),219),(-(-1 / (X ^ 2 * Y ^ 2)),210)]
abbrev instructionsRow203 (X Y Z W a b : ℂ) : Row ℂ := [(1,114),(-(1),394),(-(1),383),(-(1),365),(-(1),359),(-(-1 * X ^ 2 * W / (Y ^ 2 * Z)),322),(-(1 / (Y ^ 2 * W)),318),(-(2 / (Y ^ 2 * W)),315),(-(-1 / (Y ^ 2 * Z)),311),(-(-1 / (Y ^ 2 * Z)),276),(-(-1 / (Y ^ 2 * Z)),259),(-(1),245),(-(-1 / (Y ^ 2 * Z)),244),(-(-1 / (Y ^ 2 * Z)),210)]
abbrev instructionsRow204 (X Y Z W a b : ℂ) : Row ℂ := [(-1 * X / (X + a),162),((-1 * X / (X + a))*(-(-1)),413),((-1 * X / (X + a))*(-(-1 * a / X)),404),((-1 * X / (X + a))*(-(-1)),399),((-1 * X / (X + a))*(-(1)),392),((-1 * X / (X + a))*(-(1)),389),((-1 * X / (X + a))*(-(1 / X ^ 2)),227)]
abbrev instructionsRow205 (X Y Z W a b : ℂ) : Row ℂ := [(1,118),(-(-1),414),(-(1),406),(-(-1),404),(-(1),391),(-(1),388),(-(1),378),(-(1),331),(-(-1 * X ^ 2 / (Y ^ 2 * Z)),323),(-(-1 * X ^ 2 / (Y ^ 2 * Z)),322),(-(-1 * X ^ 2 / (Y ^ 2 * Z)),320),(-(-2 / (Y ^ 2 * W)),315),(-(1 / (Y ^ 2 * W)),310),(-(1 / (Z * W)),292),(-(-1 / (Z * W)),291),(-(1),290),(-(-1 * X ^ 2 / (Y ^ 2 * Z)),249),(-(-1 * X ^ 2 / (Y ^ 2 * Z)),238),(-(-1 * X ^ 2 / (Y ^ 2 * Z)),220)]
abbrev instructionsRow206 (X Y Z W a b : ℂ) : Row ℂ := [(-1,151),((-1)*(-(-1 / X ^ 2)),415),((-1)*(-(a / X)),406),((-1)*(-(1)),390),((-1)*(-(-1 * a / X)),386),((-1)*(-(1 / X ^ 2)),380),((-1)*(-(2 / (X ^ 2 * Y ^ 2))),353),((-1)*(-(-1 / (X ^ 2 * Y ^ 2))),350),((-1)*(-(1 / (X ^ 2 * Y ^ 2))),346),((-1)*(-(1)),275)]
abbrev instructionsRow207 (X Y Z W a b : ℂ) : Row ℂ := [((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1),159),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(-1 / X ^ 2)),416),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(a / X)),415),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(-1)),406),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(1 / X ^ 2)),405),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(1)),386),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(-1 * a / X)),380),(((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(1)),376)]
abbrev instructionsRow208 (X Y Z W a b : ℂ) : Row ℂ := [(1,115),(-((X ^ 2 * a ^ 2 + -1 * X ^ 2 + X * a + 1) / (X ^ 4 + X ^ 3 * a)),417),(-(-1),416),(-(-1),415),(-(1),405),(-(1),364),(-(X ^ 2 / Y ^ 2),356),(-((-1 * X ^ 4 * W + X ^ 2 * W + -1 * X * W * a + -1) / (Y ^ 2 * W)),318),(-(-1 * X ^ 2 * W / (Y ^ 2 * Z)),317),(-(-1 / (Y ^ 2 * Z)),311),(-(1 / (Y ^ 2 * W)),310),(-(1),309),(-(1),287),(-(-1 / (Y ^ 2 * Z)),276),(-(-1 / (Y ^ 2 * Z)),267),(-(-1 / (Y ^ 2 * Z)),244),(-(1),242),(-(-1 / (Y ^ 2 * Z)),210)]
abbrev instructionsRow209 (X Y Z W a b : ℂ) : Row ℂ := [(1,160),(-((X ^ 4 * a + X ^ 3 * a ^ 2 + X ^ 2 * a ^ 3 + -1 * X ^ 2 * a + X * a ^ 2 + a) / (X ^ 5 + X ^ 4 * a)),417),(-(-1 * a / X),416),(-(1),415),(-(-1),412),(-(1),407),(-(a / X),405),(-(1 / X ^ 2),394),(-(-1 * a / X),382)]
def instructionsTable (X Y Z W a b : ℂ) : Array (Row ℂ) := #[
  instructionsRow000 X Y Z W a b,
  instructionsRow001 X Y Z W a b,
  instructionsRow002 X Y Z W a b,
  instructionsRow003 X Y Z W a b,
  instructionsRow004 X Y Z W a b,
  instructionsRow005 X Y Z W a b,
  instructionsRow006 X Y Z W a b,
  instructionsRow007 X Y Z W a b,
  instructionsRow008 X Y Z W a b,
  instructionsRow009 X Y Z W a b,
  instructionsRow010 X Y Z W a b,
  instructionsRow011 X Y Z W a b,
  instructionsRow012 X Y Z W a b,
  instructionsRow013 X Y Z W a b,
  instructionsRow014 X Y Z W a b,
  instructionsRow015 X Y Z W a b,
  instructionsRow016 X Y Z W a b,
  instructionsRow017 X Y Z W a b,
  instructionsRow018 X Y Z W a b,
  instructionsRow019 X Y Z W a b,
  instructionsRow020 X Y Z W a b,
  instructionsRow021 X Y Z W a b,
  instructionsRow022 X Y Z W a b,
  instructionsRow023 X Y Z W a b,
  instructionsRow024 X Y Z W a b,
  instructionsRow025 X Y Z W a b,
  instructionsRow026 X Y Z W a b,
  instructionsRow027 X Y Z W a b,
  instructionsRow028 X Y Z W a b,
  instructionsRow029 X Y Z W a b,
  instructionsRow030 X Y Z W a b,
  instructionsRow031 X Y Z W a b,
  instructionsRow032 X Y Z W a b,
  instructionsRow033 X Y Z W a b,
  instructionsRow034 X Y Z W a b,
  instructionsRow035 X Y Z W a b,
  instructionsRow036 X Y Z W a b,
  instructionsRow037 X Y Z W a b,
  instructionsRow038 X Y Z W a b,
  instructionsRow039 X Y Z W a b,
  instructionsRow040 X Y Z W a b,
  instructionsRow041 X Y Z W a b,
  instructionsRow042 X Y Z W a b,
  instructionsRow043 X Y Z W a b,
  instructionsRow044 X Y Z W a b,
  instructionsRow045 X Y Z W a b,
  instructionsRow046 X Y Z W a b,
  instructionsRow047 X Y Z W a b,
  instructionsRow048 X Y Z W a b,
  instructionsRow049 X Y Z W a b,
  instructionsRow050 X Y Z W a b,
  instructionsRow051 X Y Z W a b,
  instructionsRow052 X Y Z W a b,
  instructionsRow053 X Y Z W a b,
  instructionsRow054 X Y Z W a b,
  instructionsRow055 X Y Z W a b,
  instructionsRow056 X Y Z W a b,
  instructionsRow057 X Y Z W a b,
  instructionsRow058 X Y Z W a b,
  instructionsRow059 X Y Z W a b,
  instructionsRow060 X Y Z W a b,
  instructionsRow061 X Y Z W a b,
  instructionsRow062 X Y Z W a b,
  instructionsRow063 X Y Z W a b,
  instructionsRow064 X Y Z W a b,
  instructionsRow065 X Y Z W a b,
  instructionsRow066 X Y Z W a b,
  instructionsRow067 X Y Z W a b,
  instructionsRow068 X Y Z W a b,
  instructionsRow069 X Y Z W a b,
  instructionsRow070 X Y Z W a b,
  instructionsRow071 X Y Z W a b,
  instructionsRow072 X Y Z W a b,
  instructionsRow073 X Y Z W a b,
  instructionsRow074 X Y Z W a b,
  instructionsRow075 X Y Z W a b,
  instructionsRow076 X Y Z W a b,
  instructionsRow077 X Y Z W a b,
  instructionsRow078 X Y Z W a b,
  instructionsRow079 X Y Z W a b,
  instructionsRow080 X Y Z W a b,
  instructionsRow081 X Y Z W a b,
  instructionsRow082 X Y Z W a b,
  instructionsRow083 X Y Z W a b,
  instructionsRow084 X Y Z W a b,
  instructionsRow085 X Y Z W a b,
  instructionsRow086 X Y Z W a b,
  instructionsRow087 X Y Z W a b,
  instructionsRow088 X Y Z W a b,
  instructionsRow089 X Y Z W a b,
  instructionsRow090 X Y Z W a b,
  instructionsRow091 X Y Z W a b,
  instructionsRow092 X Y Z W a b,
  instructionsRow093 X Y Z W a b,
  instructionsRow094 X Y Z W a b,
  instructionsRow095 X Y Z W a b,
  instructionsRow096 X Y Z W a b,
  instructionsRow097 X Y Z W a b,
  instructionsRow098 X Y Z W a b,
  instructionsRow099 X Y Z W a b,
  instructionsRow100 X Y Z W a b,
  instructionsRow101 X Y Z W a b,
  instructionsRow102 X Y Z W a b,
  instructionsRow103 X Y Z W a b,
  instructionsRow104 X Y Z W a b,
  instructionsRow105 X Y Z W a b,
  instructionsRow106 X Y Z W a b,
  instructionsRow107 X Y Z W a b,
  instructionsRow108 X Y Z W a b,
  instructionsRow109 X Y Z W a b,
  instructionsRow110 X Y Z W a b,
  instructionsRow111 X Y Z W a b,
  instructionsRow112 X Y Z W a b,
  instructionsRow113 X Y Z W a b,
  instructionsRow114 X Y Z W a b,
  instructionsRow115 X Y Z W a b,
  instructionsRow116 X Y Z W a b,
  instructionsRow117 X Y Z W a b,
  instructionsRow118 X Y Z W a b,
  instructionsRow119 X Y Z W a b,
  instructionsRow120 X Y Z W a b,
  instructionsRow121 X Y Z W a b,
  instructionsRow122 X Y Z W a b,
  instructionsRow123 X Y Z W a b,
  instructionsRow124 X Y Z W a b,
  instructionsRow125 X Y Z W a b,
  instructionsRow126 X Y Z W a b,
  instructionsRow127 X Y Z W a b,
  instructionsRow128 X Y Z W a b,
  instructionsRow129 X Y Z W a b,
  instructionsRow130 X Y Z W a b,
  instructionsRow131 X Y Z W a b,
  instructionsRow132 X Y Z W a b,
  instructionsRow133 X Y Z W a b,
  instructionsRow134 X Y Z W a b,
  instructionsRow135 X Y Z W a b,
  instructionsRow136 X Y Z W a b,
  instructionsRow137 X Y Z W a b,
  instructionsRow138 X Y Z W a b,
  instructionsRow139 X Y Z W a b,
  instructionsRow140 X Y Z W a b,
  instructionsRow141 X Y Z W a b,
  instructionsRow142 X Y Z W a b,
  instructionsRow143 X Y Z W a b,
  instructionsRow144 X Y Z W a b,
  instructionsRow145 X Y Z W a b,
  instructionsRow146 X Y Z W a b,
  instructionsRow147 X Y Z W a b,
  instructionsRow148 X Y Z W a b,
  instructionsRow149 X Y Z W a b,
  instructionsRow150 X Y Z W a b,
  instructionsRow151 X Y Z W a b,
  instructionsRow152 X Y Z W a b,
  instructionsRow153 X Y Z W a b,
  instructionsRow154 X Y Z W a b,
  instructionsRow155 X Y Z W a b,
  instructionsRow156 X Y Z W a b,
  instructionsRow157 X Y Z W a b,
  instructionsRow158 X Y Z W a b,
  instructionsRow159 X Y Z W a b,
  instructionsRow160 X Y Z W a b,
  instructionsRow161 X Y Z W a b,
  instructionsRow162 X Y Z W a b,
  instructionsRow163 X Y Z W a b,
  instructionsRow164 X Y Z W a b,
  instructionsRow165 X Y Z W a b,
  instructionsRow166 X Y Z W a b,
  instructionsRow167 X Y Z W a b,
  instructionsRow168 X Y Z W a b,
  instructionsRow169 X Y Z W a b,
  instructionsRow170 X Y Z W a b,
  instructionsRow171 X Y Z W a b,
  instructionsRow172 X Y Z W a b,
  instructionsRow173 X Y Z W a b,
  instructionsRow174 X Y Z W a b,
  instructionsRow175 X Y Z W a b,
  instructionsRow176 X Y Z W a b,
  instructionsRow177 X Y Z W a b,
  instructionsRow178 X Y Z W a b,
  instructionsRow179 X Y Z W a b,
  instructionsRow180 X Y Z W a b,
  instructionsRow181 X Y Z W a b,
  instructionsRow182 X Y Z W a b,
  instructionsRow183 X Y Z W a b,
  instructionsRow184 X Y Z W a b,
  instructionsRow185 X Y Z W a b,
  instructionsRow186 X Y Z W a b,
  instructionsRow187 X Y Z W a b,
  instructionsRow188 X Y Z W a b,
  instructionsRow189 X Y Z W a b,
  instructionsRow190 X Y Z W a b,
  instructionsRow191 X Y Z W a b,
  instructionsRow192 X Y Z W a b,
  instructionsRow193 X Y Z W a b,
  instructionsRow194 X Y Z W a b,
  instructionsRow195 X Y Z W a b,
  instructionsRow196 X Y Z W a b,
  instructionsRow197 X Y Z W a b,
  instructionsRow198 X Y Z W a b,
  instructionsRow199 X Y Z W a b,
  instructionsRow200 X Y Z W a b,
  instructionsRow201 X Y Z W a b,
  instructionsRow202 X Y Z W a b,
  instructionsRow203 X Y Z W a b,
  instructionsRow204 X Y Z W a b,
  instructionsRow205 X Y Z W a b,
  instructionsRow206 X Y Z W a b,
  instructionsRow207 X Y Z W a b,
  instructionsRow208 X Y Z W a b,
  instructionsRow209 X Y Z W a b
]
def instructions (X Y Z W a b : ℂ) (i : ℕ) : Row ℂ := (instructionsTable X Y Z W a b)[i]?.getD []

def orderTable : Array ℕ := #[187, 118, 134, 158, 128, 164, 152, 163, 143, 137, 67, 47, 23, 64, 88, 52, 188, 73, 149, 193, 191, 79, 17, 121, 76, 92, 19, 131, 94, 116, 26, 184, 146, 22, 89, 61, 122, 46, 166, 44, 59, 124, 31, 127, 169, 41, 167, 179, 43, 86, 83, 151, 181, 97, 62, 148, 29, 113, 141, 69, 32, 129, 48, 27, 81, 162, 24, 156, 194, 54, 144, 66, 72, 138, 78, 132, 85, 185, 91, 161, 55, 49, 25, 125, 119, 133, 160, 130, 154, 56, 80, 155, 50, 77, 95, 145, 75, 45, 65, 135, 115, 126, 165, 150, 42, 190, 16, 147, 60, 84, 58, 82, 87, 57, 159, 53, 157, 51, 153, 123, 186, 136, 74, 68, 142, 139, 71, 140, 70, 34, 33, 183, 178, 173, 172, 171, 170, 40, 39, 38, 37, 177, 176, 30, 11, 103, 101, 100, 98, 93, 13, 197, 120, 117, 114, 112, 111, 109, 99, 96, 90, 199, 110, 107, 202, 8, 203, 201, 200, 196, 195, 192, 63, 189, 182, 180, 168, 28, 21, 20, 18, 15, 14, 10, 9, 7, 5, 205, 36, 175, 35, 174, 104, 108, 106, 198, 12, 4, 206, 105, 102, 209, 208, 6, 3, 2, 1, 204, 207, 0]
def order (i : ℕ) : ℕ := orderTable[i]?.getD 0

def rankTable : Array ℕ := #[209, 206, 205, 204, 197, 186, 203, 185, 165, 184, 183, 144, 196, 150, 182, 181, 106, 22, 180, 26, 179, 178, 33, 12, 66, 82, 30, 63, 177, 56, 143, 42, 60, 130, 129, 190, 188, 140, 139, 138, 137, 45, 104, 48, 39, 97, 37, 11, 62, 81, 92, 117, 15, 115, 69, 80, 89, 113, 110, 40, 108, 35, 54, 172, 13, 98, 71, 10, 123, 59, 128, 126, 72, 17, 122, 96, 24, 93, 74, 21, 90, 64, 111, 50, 109, 76, 49, 112, 14, 34, 160, 78, 25, 149, 28, 94, 159, 53, 148, 158, 147, 146, 200, 145, 192, 199, 194, 163, 193, 157, 162, 156, 155, 57, 154, 100, 29, 153, 1, 84, 152, 23, 36, 119, 41, 83, 101, 43, 4, 61, 87, 27, 75, 85, 2, 99, 121, 9, 73, 125, 127, 58, 124, 8, 70, 95, 32, 107, 55, 18, 103, 51, 6, 118, 88, 91, 67, 116, 3, 114, 86, 79, 65, 7, 5, 102, 38, 46, 176, 44, 136, 135, 134, 133, 191, 189, 142, 141, 132, 47, 175, 52, 174, 131, 31, 77, 120, 0, 16, 173, 105, 20, 171, 19, 68, 170, 169, 151, 195, 161, 168, 167, 164, 166, 207, 187, 198, 208, 202, 201]
def rank (i : ℕ) : ℕ := rankTable[i]?.getD 0

def outputTable : Array ℕ := #[209, 208, 207, 206, 205, 204, 203, 202, 201, 200, 199, 198, 197, 196, 195, 194, 193, 192, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176, 175, 174, 173, 172, 171, 170, 169, 168, 167, 166, 165, 164, 163, 162, 161, 160, 159, 158, 157, 156, 155, 154, 153, 152, 151, 150, 149, 148, 147, 146, 145, 144, 143, 142, 141, 140, 139, 138, 137, 136, 135, 134, 133, 132, 131, 130, 129, 128, 127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def output (i : ℕ) : ℕ := outputTable[i]?.getD 0

theorem order_rank : ∀ i : Fin 210, order (rank i.val)=i.val := by decide +kernel
theorem rank_lt : ∀ i : Fin 210, rank i.val<210 := by decide +kernel
theorem output_lt : ∀ i : Fin 210, output i.val<210 := by decide +kernel
end QuantitativeArithmeticCompact35Case1
end
