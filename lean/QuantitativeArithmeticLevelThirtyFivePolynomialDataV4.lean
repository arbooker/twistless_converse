module
public import SmallLevelGoodHeckeTwoV1
public import QuantitativeArithmeticPrimitiveResiduePairV4

public import FinitenessAllLevelHeckePowerV1
public import FinitenessFiniteOrderClosureV1
public import FinitenessOriginalTwistLocalV1
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import QuantitativeArithmeticAnalyticGermTheoryV4
public import QuantitativeArithmeticClosedEntireV1
public import QuantitativeArithmeticCompact35AnalyticWeightsV1
public import QuantitativeArithmeticCompact35ColumnsSynchronousV1
public import QuantitativeArithmeticCompact35JetRowsPositiveTheoryV4
public import QuantitativeArithmeticComplexOuterNonzeroV1
public import QuantitativeArithmeticEntireQuotientV1
public import QuantitativeArithmeticTwoSequenceTaylorTheoryV4
public import QuantitativeArithmeticMellinScaleV1
public import QuantitativeArithmeticNormalizedIndividualFrickeTheoryV4
public import QuantitativeArithmeticOuterRootNormTheoryV4
public import QuantitativeArithmeticPolynomialRootCoverTheoryV4
public import QuantitativeArithmeticPolynomialVariationV1
public import QuantitativeArithmeticPrimePowerTorsionV1
public import QuantitativeArithmeticQuadraticTwistInversionTheoryV4
public import QuantitativeArithmeticQuadraticTwistReflectionTheoryV4
public import QuantitativeArithmeticRealQuadraticOrderV1
public import QuantitativeArithmeticCoherentTaylorTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenPoleOrderV1
public import QuantitativeArithmeticSmallLevelThirtyFiveKnownWordsTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRowsTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveCentersV1
public import QuantitativeArithmeticSmallLevelThirtyFiveChiFourTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujanTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRowsTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveJetCertificateTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFivePoleFullRowsV1
public import QuantitativeArithmeticSmallLevelThirtyFivePositiveAnalyticShortRowsTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveShiftedDominanceV1
public import QuantitativeArithmeticSmallLevelThirtyFiveSignedReducedRowsV1
public import QuantitativeArithmeticSmallLevelThirtyFiveSixRowDataV1
public import QuantitativeArithmeticSmallLevelThirtyFiveWordLaurentV1
public import QuantitativeArithmeticSmallLevelThirtyFiveWordWitnessFamilyV4
public import QuantitativeArithmeticUniversalPoleNormalizationV1
public import SmallLevelAdditiveTheoryV4
public import SmallLevelTaylorTheoryV4
public import SmallLevelContinuationTheoryV4
public import SmallLevelMellinUnscaleV1
public import SmallLevelModularCriterionV1
public import SmallLevelOddFrickeV1
public import SmallLevelPoleGridTheoryV4
public import SmallLevelQuadraticExponentialTheoryV4
public import SmallLevelSixRootsV1
public import SmallLevelThirtyPairsV1
public import SmallLevelThreePairV1
public import SmallLevelTransversalV1

set_option Elab.async false

/-! Consolidated converse argument. Large exact certificates remain
in their own modules; declarations and proof bodies are preserved. -/

/-! ## ThirtyFiveGenericPolynomialData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 60000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate

def genericInput0 (x y z : ℂ) : ℂ := (-4)*z^(2:ℕ)*x^(4:ℕ) + (-4)*z^(2:ℕ)*y*x^(2:ℕ) + (4)*z^(2:ℕ)*x^(3:ℕ) + (10)*z*x^(4:ℕ) + (-4)*x^(5:ℕ) + (-6)*z^(2:ℕ)*x^(2:ℕ) + (10)*z*y*x^(2:ℕ) + (-10)*z*x^(3:ℕ) + (16)*x^(4:ℕ) + (6)*z^(2:ℕ)*y + (-2)*z^(2:ℕ)*x + (4)*y^(2:ℕ)*x + (12)*z*x^(2:ℕ) + (-30)*x^(3:ℕ) + (6)*z^(2:ℕ) + (-10)*z*y + (-4)*y^(2:ℕ) + (26)*z*x + (2)*y*x + (-10)*x^(2:ℕ) + (-6)*z + (24)*y + (58)*x + (24)

def genericInput1 (x y z : ℂ) : ℂ := (-1)*z^(2:ℕ)*x^(5:ℕ) + (-1)*z^(2:ℕ)*y*x^(3:ℕ) + (1)*z^(2:ℕ)*x^(4:ℕ) + (3)*z*x^(5:ℕ) + (-2)*x^(6:ℕ) + (-3)*z^(2:ℕ)*x^(3:ℕ) + (3)*z*y*x^(3:ℕ) + (-3)*z*x^(4:ℕ) + (7)*x^(5:ℕ) + (2)*y^(2:ℕ)*x^(2:ℕ) + (6)*z*x^(3:ℕ) + (1)*y*x^(3:ℕ) + (-8)*x^(4:ℕ) + (-2)*z^(2:ℕ)*y + (1)*z*y*x + (3)*z*x^(2:ℕ) + (3)*y*x^(2:ℕ) + (1)*x^(3:ℕ) + (-2)*z^(2:ℕ) + (4)*z*y + (2)*y^(2:ℕ) + (-5)*z*x + (7)*y*x + (12)*x^(2:ℕ) + (4)*z + (-6)*y + (-11)*x + (-8)

def genericInput2 (x y z : ℂ) : ℂ := (2)*z^(2:ℕ)*x^(5:ℕ) + (2)*z^(2:ℕ)*y*x^(3:ℕ) + (-2)*z^(2:ℕ)*x^(4:ℕ) + (-6)*z*x^(5:ℕ) + (3)*x^(6:ℕ) + (5)*z^(2:ℕ)*x^(3:ℕ) + (-6)*z*y*x^(3:ℕ) + (7)*z*x^(4:ℕ) + (-10)*x^(5:ℕ) + (-1)*z^(2:ℕ)*y*x + (2)*z^(2:ℕ)*x^(2:ℕ) + (1)*z*y*x^(2:ℕ) + (-3)*y^(2:ℕ)*x^(2:ℕ) + (-14)*z*x^(3:ℕ) + (15)*x^(4:ℕ) + (5)*z^(2:ℕ)*y + (-4)*z^(2:ℕ)*x + (-3)*z*y*x + (-6)*z*x^(2:ℕ) + (-3)*y*x^(2:ℕ) + (-15)*x^(3:ℕ) + (-1)*z^(2:ℕ) + (-12)*z*y + (-9)*y^(2:ℕ) + (27)*z*x + (-18)*y*x + (-10)*x^(2:ℕ) + (-4)*z + (19)*y + (45)*x + (26)

def genericP17 (x : ℂ) : ℂ := x^(17:ℕ) - 6*x^(16:ℕ) + 39*x^(15:ℕ)/2 - 52*x^(14:ℕ) + 151*x^(13:ℕ)/2 + 24*x^(12:ℕ) - 378*x^(11:ℕ) + 710*x^(10:ℕ) - 860*x^(9:ℕ) - 588*x^(8:ℕ) + 8695*x^(7:ℕ)/2 - 648*x^(6:ℕ) - 9453*x^(5:ℕ)/2 + 1162*x^(4:ℕ) + 1555*x^(3:ℕ) - 2162*x^(2:ℕ) - 1906*x - 408

def genericQ16 (x : ℂ) : ℂ := 195826164175*x^(16:ℕ)/3869672976512 - 1331712766807*x^(15:ℕ)/3869672976512 + 9766337397939*x^(14:ℕ)/7739345953024 - 28151649759489*x^(13:ℕ)/7739345953024 + 12991206956547*x^(12:ℕ)/1934836488256 - 7945628598725*x^(11:ℕ)/1934836488256 - 7720257215425*x^(10:ℕ)/483709122064 + 94457421656905*x^(9:ℕ)/1934836488256 - 159417394701997*x^(8:ℕ)/1934836488256 + 68182583057261*x^(7:ℕ)/1934836488256 + 213782121645371*x^(6:ℕ)/1105620850432 - 1462417769249463*x^(5:ℕ)/7739345953024 - 50011916162609*x^(4:ℕ)/552810425216 + 76815327428381*x^(3:ℕ)/552810425216 - 29781701667141*x^(2:ℕ)/967418244128 - 173830418165241*x/1934836488256 - 11422668371311/483709122064

end QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate
end
end

/-! ## ThirtyFivePositiveGenericData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 60000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

def positiveGenericInput0 (X Y Z : ℂ) : ℂ := (-5:ℂ)*Z^(2:ℕ)*X^(3:ℕ) + (2:ℂ)*Z^(2:ℕ)*X^(2:ℕ) + (-3:ℂ)*Z^(2:ℕ)*X + (-6:ℂ)*Z^(2:ℕ) + (1:ℂ)*Z*X^(4:ℕ) + (10:ℂ)*Z*X^(3:ℕ) + (-7:ℂ)*Z*X^(2:ℕ) + (4:ℂ)*Z*X + (4:ℂ)*Z + (1:ℂ)*Y*X^(4:ℕ) + (-1:ℂ)*Y*X^(3:ℕ) + (5:ℂ)*Y*X^(2:ℕ) + (5:ℂ)*Y*X + (-2:ℂ)*Y + (-1:ℂ)*X^(6:ℕ) + (4:ℂ)*X^(5:ℕ) + (-8:ℂ)*X^(4:ℕ) + (4:ℂ)*X^(3:ℕ) + (27:ℂ)*X^(2:ℕ) + (-2:ℂ)*X

def positiveGenericInput1 (X Y Z : ℂ) : ℂ := (1:ℂ)*Z^(2:ℕ)*Y*X + (-1:ℂ)*Z^(2:ℕ)*Y + (-4:ℂ)*Z^(2:ℕ)*X^(3:ℕ) + (1:ℂ)*Z^(2:ℕ)*X + (-1:ℂ)*Z^(2:ℕ) + (-1:ℂ)*Z*Y*X^(2:ℕ) + (1:ℂ)*Z*Y*X + (2:ℂ)*Z*Y + (12:ℂ)*Z*X^(3:ℕ) + (-9:ℂ)*Z*X^(2:ℕ) + (-11:ℂ)*Z*X + (10:ℂ)*Z + (-1:ℂ)*Y^(2:ℕ)*X^(2:ℕ) + (5:ℂ)*Y^(2:ℕ) + (1:ℂ)*Y*X^(4:ℕ) + (-3:ℂ)*Y*X^(3:ℕ) + (2:ℂ)*Y*X^(2:ℕ) + (9:ℂ)*Y*X + (-7:ℂ)*Y + (-7:ℂ)*X^(4:ℕ) + (17:ℂ)*X^(3:ℕ) + (15:ℂ)*X^(2:ℕ) + (-27:ℂ)*X + (-20:ℂ)

def positiveGenericInput2 (X Y Z : ℂ) : ℂ := (1:ℂ)*Z^(2:ℕ)*Y*X^(2:ℕ) + (-1:ℂ)*Z^(2:ℕ)*Y*X + (1:ℂ)*Z^(2:ℕ)*X^(4:ℕ) + (-2:ℂ)*Z^(2:ℕ)*X^(3:ℕ) + (-14:ℂ)*Z^(2:ℕ)*X^(2:ℕ) + (13:ℂ)*Z^(2:ℕ)*X + (18:ℂ)*Z^(2:ℕ) + (-1:ℂ)*Z*Y*X^(3:ℕ) + (1:ℂ)*Z*Y*X^(2:ℕ) + (2:ℂ)*Z*Y*X + (-1:ℂ)*Z*X^(5:ℕ) + (2:ℂ)*Z*X^(4:ℕ) + (17:ℂ)*Z*X^(2:ℕ) + (-24:ℂ)*Z*X + (-28:ℂ)*Z + (-1:ℂ)*Y^(2:ℕ)*X^(3:ℕ) + (5:ℂ)*Y^(2:ℕ)*X + (-2:ℂ)*Y*X^(4:ℕ) + (-1:ℂ)*Y*X^(3:ℕ) + (-2:ℂ)*Y*X^(2:ℕ) + (1:ℂ)*Y*X + (14:ℂ)*Y + (1:ℂ)*X^(7:ℕ) + (-4:ℂ)*X^(6:ℕ) + (-1:ℂ)*X^(5:ℕ) + (25:ℂ)*X^(4:ℕ) + (-36:ℂ)*X^(3:ℕ) + (-41:ℂ)*X^(2:ℕ) + (50:ℂ)*X + (24:ℂ)

def positiveGenericInput3 (X Y Z : ℂ) : ℂ := (-1:ℂ)*Z^(2:ℕ)*Y*X^(2:ℕ) + (1:ℂ)*Z^(2:ℕ)*Y + (4:ℂ)*Z^(2:ℕ)*X^(4:ℕ) + (4:ℂ)*Z^(2:ℕ)*X^(3:ℕ) + (9:ℂ)*Z^(2:ℕ)*X^(2:ℕ) + (4:ℂ)*Z^(2:ℕ)*X + (-5:ℂ)*Z^(2:ℕ) + (1:ℂ)*Z*Y*X^(3:ℕ) + (-3:ℂ)*Z*Y*X + (-2:ℂ)*Z*Y + (-12:ℂ)*Z*X^(4:ℕ) + (-5:ℂ)*Z*X^(3:ℕ) + (3:ℂ)*Z*X + (10:ℂ)*Z + (1:ℂ)*Y^(2:ℕ)*X^(3:ℕ) + (1:ℂ)*Y^(2:ℕ)*X^(2:ℕ) + (-5:ℂ)*Y^(2:ℕ)*X + (-5:ℂ)*Y^(2:ℕ) + (-1:ℂ)*Y*X^(5:ℕ) + (2:ℂ)*Y*X^(4:ℕ) + (-1:ℂ)*Y*X^(3:ℕ) + (-9:ℂ)*Y*X^(2:ℕ) + (-8:ℂ)*Y*X + (-3:ℂ)*Y + (9:ℂ)*X^(5:ℕ) + (-18:ℂ)*X^(4:ℕ) + (-20:ℂ)*X^(3:ℕ) + (16:ℂ)*X^(2:ℕ) + (5:ℂ)*X + (-4:ℂ)

def positiveGenericP15 (X : ℂ) : ℂ := X^(15:ℕ) - 8*X^(14:ℕ) + 69*X^(13:ℕ)/2 - 116*X^(12:ℕ) + 296*X^(11:ℕ) - 528*X^(10:ℕ) + 666*X^(9:ℕ) - 558*X^(8:ℕ) + 16*X^(7:ℕ) + 336*X^(6:ℕ) + 2115*X^(5:ℕ)/2 - 1076*X^(4:ℕ) - 2751*X^(3:ℕ) + 1362*X^(2:ℕ) + 1044*X + 1944

def positiveGenericQ14 (X : ℂ) : ℂ := 123036821*X^(14:ℕ)/49054637088 - 380927327*X^(13:ℕ)/24527318544 + 1964894683*X^(12:ℕ)/32703091392 - 9430320979*X^(11:ℕ)/49054637088 + 10540873589*X^(10:ℕ)/24527318544 - 2648100685*X^(9:ℕ)/4087886424 + 1842541657*X^(8:ℕ)/2725257616 - 730493689*X^(7:ℕ)/2725257616 - 9560063335*X^(6:ℕ)/12263659272 + 1257846913*X^(5:ℕ)/2043943212 + 19206594615*X^(4:ℕ)/10901030464 + 65211308555*X^(3:ℕ)/49054637088 - 35350530967*X^(2:ℕ)/16351545696 - 1641152923*X/1021971606 - 1397885791/1362628808

def positiveGenericR14 (X : ℂ) : ℂ := -32572219*X^(14:ℕ)/5942485728 + 99431857*X^(13:ℕ)/2971242864 - 487608805*X^(12:ℕ)/3961657152 + 2284959461*X^(11:ℕ)/5942485728 - 2436659869*X^(10:ℕ)/2971242864 + 7534065*X^(9:ℕ)/6877877 - 324830869*X^(8:ℕ)/330138096 + 64609633*X^(7:ℕ)/330138096 + 573323819*X^(6:ℕ)/371405358 + 13918735*X^(5:ℕ)/495207144 - 7530220529*X^(4:ℕ)/1320552384 - 29823770401*X^(3:ℕ)/5942485728 + 16892195905*X^(2:ℕ)/1980828576 + 132115181*X/14564916 + 408584927/55023016

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

