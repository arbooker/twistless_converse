module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusRowCertificatesV1

public import QuantitativeArithmeticFiniteRangeCertificatesV1
public import QuantitativeArithmeticListBoundsV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridDataTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModelTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxSymbolicRowsV1
public meta import QuantitativeArithmeticCompactCommandsV1
public meta import QuantitativeArithmeticCompactFactCommandsV1
public meta import QuantitativeArithmeticFiniteRangeCommandsV4
public meta import SmallLevelLaurentPolynomialLiteralV1
public meta import SmallLevelCertificateBatchCommandV1
set_option Elab.async false

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
certificate_batch {
/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentCheckFamilyV4 -/
section
-- Editor-info-based tactic linting is unavailable inside compact certificates.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-! Explicit certificate statements sharing their proof procedures. -/
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 0
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_facts [
  (source_zero_0 : ∀ i : Fin 32, substitute basis (source (i.val+0))=[]),
  (tail_zero_0 : ∀ i : Fin 32, substitute basis (tail (i.val+0))=[])
] by
  decide +kernel

compact_facts [
  (source_zero_1 : ∀ i : Fin 32, substitute basis (source (i.val+32))=[]),
  (tail_zero_1 : ∀ i : Fin 32, substitute basis (tail (i.val+32))=[]),
  (source_zero_2 : ∀ i : Fin 32, substitute basis (source (i.val+64))=[]),
  (tail_zero_2 : ∀ i : Fin 32, substitute basis (tail (i.val+64))=[]),
  (source_zero_3 : ∀ i : Fin 32, substitute basis (source (i.val+96))=[]),
  (tail_zero_3 : ∀ i : Fin 32, substitute basis (tail (i.val+96))=[]),
  (source_zero_4 : ∀ i : Fin 32, substitute basis (source (i.val+128))=[]),
  (tail_zero_4 : ∀ i : Fin 32, substitute basis (tail (i.val+128))=[]),
  (source_zero_5 : ∀ i : Fin 32, substitute basis (source (i.val+160))=[]),
  (tail_zero_5 : ∀ i : Fin 32, substitute basis (tail (i.val+160))=[]),
  (source_zero_6 : ∀ i : Fin 32, substitute basis (source (i.val+192))=[]),
  (tail_zero_6 : ∀ i : Fin 32, substitute basis (tail (i.val+192))=[]),
  (source_zero_7 : ∀ i : Fin 32, substitute basis (source (i.val+224))=[]),
  (tail_zero_7 : ∀ i : Fin 32, substitute basis (tail (i.val+224))=[]),
  (source_zero_8 : ∀ i : Fin 32, substitute basis (source (i.val+256))=[]),
  (tail_zero_8 : ∀ i : Fin 32, substitute basis (tail (i.val+256))=[]),
  (source_zero_9 : ∀ i : Fin 32, substitute basis (source (i.val+288))=[]),
  (tail_zero_9 : ∀ i : Fin 32, substitute basis (tail (i.val+288))=[]),
  (source_zero_10 : ∀ i : Fin 32, substitute basis (source (i.val+320))=[]),
  (tail_zero_10 : ∀ i : Fin 32, substitute basis (tail (i.val+320))=[]),
  (source_zero_11 : ∀ i : Fin 32, substitute basis (source (i.val+352))=[]),
  (tail_zero_11 : ∀ i : Fin 32, substitute basis (tail (i.val+352))=[]),
  (source_zero_12 : ∀ i : Fin 32, substitute basis (source (i.val+384))=[]),
  (tail_zero_12 : ∀ i : Fin 32, substitute basis (tail (i.val+384))=[]),
  (source_zero_13 : ∀ i : Fin 32, substitute basis (source (i.val+416))=[]),
  (tail_zero_13 : ∀ i : Fin 32, substitute basis (tail (i.val+416))=[]),
  (source_zero_14 : ∀ i : Fin 32, substitute basis (source (i.val+448))=[]),
  (tail_zero_14 : ∀ i : Fin 32, substitute basis (tail (i.val+448))=[]),
  (source_zero_15 : ∀ i : Fin 32, substitute basis (source (i.val+480))=[]),
  (tail_zero_15 : ∀ i : Fin 32, substitute basis (tail (i.val+480))=[]),
  (source_zero_16 : ∀ i : Fin 32, substitute basis (source (i.val+512))=[]),
  (tail_zero_16 : ∀ i : Fin 32, substitute basis (tail (i.val+512))=[]),
  (source_zero_17 : ∀ i : Fin 32, substitute basis (source (i.val+544))=[]),
  (tail_zero_17 : ∀ i : Fin 32, substitute basis (tail (i.val+544))=[]),
  (source_zero_18 : ∀ i : Fin 32, substitute basis (source (i.val+576))=[]),
  (tail_zero_18 : ∀ i : Fin 32, substitute basis (tail (i.val+576))=[]),
  (source_zero_19 : ∀ i : Fin 32, substitute basis (source (i.val+608))=[]),
  (tail_zero_19 : ∀ i : Fin 32, substitute basis (tail (i.val+608))=[]),
  (source_zero_20 : ∀ i : Fin 32, substitute basis (source (i.val+640))=[]),
  (tail_zero_20 : ∀ i : Fin 32, substitute basis (tail (i.val+640))=[]),
  (source_zero_21 : ∀ i : Fin 32, substitute basis (source (i.val+672))=[]),
  (tail_zero_21 : ∀ i : Fin 32, substitute basis (tail (i.val+672))=[]),
  (source_zero_22 : ∀ i : Fin 32, substitute basis (source (i.val+704))=[]),
  (tail_zero_22 : ∀ i : Fin 32, substitute basis (tail (i.val+704))=[]),
  (source_zero_23 : ∀ i : Fin 32, substitute basis (source (i.val+736))=[]),
  (tail_zero_23 : ∀ i : Fin 32, substitute basis (tail (i.val+736))=[]),
  (source_zero_24 : ∀ i : Fin 32, substitute basis (source (i.val+768))=[]),
  (tail_zero_24 : ∀ i : Fin 32, substitute basis (tail (i.val+768))=[]),
  (source_zero_25 : ∀ i : Fin 32, substitute basis (source (i.val+800))=[]),
  (tail_zero_25 : ∀ i : Fin 32, substitute basis (tail (i.val+800))=[]),
  (source_zero_26 : ∀ i : Fin 32, substitute basis (source (i.val+832))=[]),
  (tail_zero_26 : ∀ i : Fin 32, substitute basis (tail (i.val+832))=[]),
  (source_zero_27 : ∀ i : Fin 32, substitute basis (source (i.val+864))=[]),
  (tail_zero_27 : ∀ i : Fin 32, substitute basis (tail (i.val+864))=[]),
  (source_zero_28 : ∀ i : Fin 32, substitute basis (source (i.val+896))=[]),
  (tail_zero_28 : ∀ i : Fin 32, substitute basis (tail (i.val+896))=[]),
  (source_zero_29 : ∀ i : Fin 32, substitute basis (source (i.val+928))=[]),
  (tail_zero_29 : ∀ i : Fin 32, substitute basis (tail (i.val+928))=[]),
  (source_zero_30 : ∀ i : Fin 32, substitute basis (source (i.val+960))=[]),
  (tail_zero_30 : ∀ i : Fin 32, substitute basis (tail (i.val+960))=[]),
  (source_zero_31 : ∀ i : Fin 32, substitute basis (source (i.val+992))=[]),
  (tail_zero_31 : ∀ i : Fin 32, substitute basis (tail (i.val+992))=[]),
  (source_zero_32 : ∀ i : Fin 32, substitute basis (source (i.val+1024))=[]),
  (tail_zero_32 : ∀ i : Fin 32, substitute basis (tail (i.val+1024))=[]),
  (source_zero_33 : ∀ i : Fin 32, substitute basis (source (i.val+1056))=[]),
  (tail_zero_33 : ∀ i : Fin 32, substitute basis (tail (i.val+1056))=[]),
  (source_zero_34 : ∀ i : Fin 32, substitute basis (source (i.val+1088))=[]),
  (tail_zero_34 : ∀ i : Fin 32, substitute basis (tail (i.val+1088))=[]),
  (source_zero_35 : ∀ i : Fin 32, substitute basis (source (i.val+1120))=[]),
  (tail_zero_35 : ∀ i : Fin 32, substitute basis (tail (i.val+1120))=[]),
  (source_zero_36 : ∀ i : Fin 32, substitute basis (source (i.val+1152))=[]),
  (tail_zero_36 : ∀ i : Fin 32, substitute basis (tail (i.val+1152))=[]),
  (source_zero_37 : ∀ i : Fin 32, substitute basis (source (i.val+1184))=[]),
  (tail_zero_37 : ∀ i : Fin 32, substitute basis (tail (i.val+1184))=[]),
  (source_zero_38 : ∀ i : Fin 32, substitute basis (source (i.val+1216))=[]),
  (tail_zero_38 : ∀ i : Fin 32, substitute basis (tail (i.val+1216))=[]),
  (source_zero_39 : ∀ i : Fin 32, substitute basis (source (i.val+1248))=[]),
  (tail_zero_39 : ∀ i : Fin 32, substitute basis (tail (i.val+1248))=[]),
  (source_zero_40 : ∀ i : Fin 32, substitute basis (source (i.val+1280))=[]),
  (tail_zero_40 : ∀ i : Fin 32, substitute basis (tail (i.val+1280))=[]),
  (source_zero_41 : ∀ i : Fin 32, substitute basis (source (i.val+1312))=[]),
  (tail_zero_41 : ∀ i : Fin 32, substitute basis (tail (i.val+1312))=[]),
  (source_zero_42 : ∀ i : Fin 32, substitute basis (source (i.val+1344))=[]),
  (tail_zero_42 : ∀ i : Fin 32, substitute basis (tail (i.val+1344))=[]),
  (source_zero_43 : ∀ i : Fin 32, substitute basis (source (i.val+1376))=[]),
  (tail_zero_43 : ∀ i : Fin 32, substitute basis (tail (i.val+1376))=[]),
  (source_zero_44 : ∀ i : Fin 32, substitute basis (source (i.val+1408))=[]),
  (tail_zero_44 : ∀ i : Fin 32, substitute basis (tail (i.val+1408))=[]),
  (source_zero_45 : ∀ i : Fin 32, substitute basis (source (i.val+1440))=[]),
  (tail_zero_45 : ∀ i : Fin 32, substitute basis (tail (i.val+1440))=[]),
  (source_zero_46 : ∀ i : Fin 32, substitute basis (source (i.val+1472))=[]),
  (tail_zero_46 : ∀ i : Fin 32, substitute basis (tail (i.val+1472))=[]),
  (source_zero_47 : ∀ i : Fin 32, substitute basis (source (i.val+1504))=[]),
  (tail_zero_47 : ∀ i : Fin 32, substitute basis (tail (i.val+1504))=[]),
  (source_zero_48 : ∀ i : Fin 32, substitute basis (source (i.val+1536))=[]),
  (tail_zero_48 : ∀ i : Fin 32, substitute basis (tail (i.val+1536))=[]),
  (source_zero_49 : ∀ i : Fin 32, substitute basis (source (i.val+1568))=[]),
  (tail_zero_49 : ∀ i : Fin 32, substitute basis (tail (i.val+1568))=[]),
  (source_zero_50 : ∀ i : Fin 32, substitute basis (source (i.val+1600))=[]),
  (tail_zero_50 : ∀ i : Fin 32, substitute basis (tail (i.val+1600))=[]),
  (source_zero_51 : ∀ i : Fin 32, substitute basis (source (i.val+1632))=[]),
  (tail_zero_51 : ∀ i : Fin 32, substitute basis (tail (i.val+1632))=[]),
  (source_zero_52 : ∀ i : Fin 32, substitute basis (source (i.val+1664))=[]),
  (tail_zero_52 : ∀ i : Fin 32, substitute basis (tail (i.val+1664))=[]),
  (source_zero_53 : ∀ i : Fin 32, substitute basis (source (i.val+1696))=[]),
  (tail_zero_53 : ∀ i : Fin 32, substitute basis (tail (i.val+1696))=[]),
  (source_zero_54 : ∀ i : Fin 32, substitute basis (source (i.val+1728))=[]),
  (tail_zero_54 : ∀ i : Fin 32, substitute basis (tail (i.val+1728))=[]),
  (source_zero_55 : ∀ i : Fin 32, substitute basis (source (i.val+1760))=[]),
  (tail_zero_55 : ∀ i : Fin 32, substitute basis (tail (i.val+1760))=[]),
  (source_zero_56 : ∀ i : Fin 32, substitute basis (source (i.val+1792))=[]),
  (tail_zero_56 : ∀ i : Fin 32, substitute basis (tail (i.val+1792))=[]),
  (source_zero_57 : ∀ i : Fin 32, substitute basis (source (i.val+1824))=[]),
  (tail_zero_57 : ∀ i : Fin 32, substitute basis (tail (i.val+1824))=[]),
  (source_zero_58 : ∀ i : Fin 32, substitute basis (source (i.val+1856))=[]),
  (tail_zero_58 : ∀ i : Fin 32, substitute basis (tail (i.val+1856))=[]),
  (source_zero_59 : ∀ i : Fin 32, substitute basis (source (i.val+1888))=[]),
  (tail_zero_59 : ∀ i : Fin 32, substitute basis (tail (i.val+1888))=[]),
  (source_zero_60 : ∀ i : Fin 32, substitute basis (source (i.val+1920))=[]),
  (tail_zero_60 : ∀ i : Fin 32, substitute basis (tail (i.val+1920))=[]),
  (source_zero_61 : ∀ i : Fin 32, substitute basis (source (i.val+1952))=[]),
  (tail_zero_61 : ∀ i : Fin 32, substitute basis (tail (i.val+1952))=[]),
  (source_zero_62 : ∀ i : Fin 32, substitute basis (source (i.val+1984))=[]),
  (tail_zero_62 : ∀ i : Fin 32, substitute basis (tail (i.val+1984))=[]),
  (source_zero_63 : ∀ i : Fin 32, substitute basis (source (i.val+2016))=[]),
  (tail_zero_63 : ∀ i : Fin 32, substitute basis (tail (i.val+2016))=[]),
  (source_zero_64 : ∀ i : Fin 32, substitute basis (source (i.val+2048))=[]),
  (tail_zero_64 : ∀ i : Fin 32, substitute basis (tail (i.val+2048))=[]),
  (source_zero_65 : ∀ i : Fin 32, substitute basis (source (i.val+2080))=[]),
  (tail_zero_65 : ∀ i : Fin 32, substitute basis (tail (i.val+2080))=[]),
  (source_zero_66 : ∀ i : Fin 32, substitute basis (source (i.val+2112))=[]),
  (tail_zero_66 : ∀ i : Fin 32, substitute basis (tail (i.val+2112))=[]),
  (source_zero_67 : ∀ i : Fin 32, substitute basis (source (i.val+2144))=[]),
  (tail_zero_67 : ∀ i : Fin 32, substitute basis (tail (i.val+2144))=[]),
  (source_zero_68 : ∀ i : Fin 32, substitute basis (source (i.val+2176))=[]),
  (tail_zero_68 : ∀ i : Fin 32, substitute basis (tail (i.val+2176))=[]),
  (source_zero_69 : ∀ i : Fin 32, substitute basis (source (i.val+2208))=[]),
  (tail_zero_69 : ∀ i : Fin 32, substitute basis (tail (i.val+2208))=[]),
  (source_zero_70 : ∀ i : Fin 32, substitute basis (source (i.val+2240))=[]),
  (tail_zero_70 : ∀ i : Fin 32, substitute basis (tail (i.val+2240))=[]),
  (source_zero_71 : ∀ i : Fin 32, substitute basis (source (i.val+2272))=[]),
  (tail_zero_71 : ∀ i : Fin 32, substitute basis (tail (i.val+2272))=[]),
  (source_zero_72 : ∀ i : Fin 32, substitute basis (source (i.val+2304))=[]),
  (tail_zero_72 : ∀ i : Fin 32, substitute basis (tail (i.val+2304))=[]),
  (source_zero_73 : ∀ i : Fin 32, substitute basis (source (i.val+2336))=[]),
  (tail_zero_73 : ∀ i : Fin 32, substitute basis (tail (i.val+2336))=[]),
  (source_zero_74 : ∀ i : Fin 32, substitute basis (source (i.val+2368))=[]),
  (tail_zero_74 : ∀ i : Fin 32, substitute basis (tail (i.val+2368))=[]),
  (source_zero_75 : ∀ i : Fin 32, substitute basis (source (i.val+2400))=[]),
  (tail_zero_75 : ∀ i : Fin 32, substitute basis (tail (i.val+2400))=[]),
  (source_zero_76 : ∀ i : Fin 32, substitute basis (source (i.val+2432))=[]),
  (tail_zero_76 : ∀ i : Fin 32, substitute basis (tail (i.val+2432))=[]),
  (source_zero_77 : ∀ i : Fin 32, substitute basis (source (i.val+2464))=[]),
  (tail_zero_77 : ∀ i : Fin 32, substitute basis (tail (i.val+2464))=[]),
  (source_zero_78 : ∀ i : Fin 32, substitute basis (source (i.val+2496))=[]),
  (tail_zero_78 : ∀ i : Fin 32, substitute basis (tail (i.val+2496))=[]),
  (source_zero_79 : ∀ i : Fin 32, substitute basis (source (i.val+2528))=[]),
  (tail_zero_79 : ∀ i : Fin 32, substitute basis (tail (i.val+2528))=[]),
  (source_zero_80 : ∀ i : Fin 32, substitute basis (source (i.val+2560))=[]),
  (tail_zero_80 : ∀ i : Fin 32, substitute basis (tail (i.val+2560))=[]),
  (source_zero_81 : ∀ i : Fin 32, substitute basis (source (i.val+2592))=[]),
  (tail_zero_81 : ∀ i : Fin 32, substitute basis (tail (i.val+2592))=[]),
  (source_zero_82 : ∀ i : Fin 32, substitute basis (source (i.val+2624))=[]),
  (tail_zero_82 : ∀ i : Fin 32, substitute basis (tail (i.val+2624))=[]),
  (source_zero_83 : ∀ i : Fin 32, substitute basis (source (i.val+2656))=[]),
  (tail_zero_83 : ∀ i : Fin 32, substitute basis (tail (i.val+2656))=[]),
  (source_zero_84 : ∀ i : Fin 32, substitute basis (source (i.val+2688))=[]),
  (tail_zero_84 : ∀ i : Fin 32, substitute basis (tail (i.val+2688))=[]),
  (source_zero_85 : ∀ i : Fin 32, substitute basis (source (i.val+2720))=[]),
  (tail_zero_85 : ∀ i : Fin 32, substitute basis (tail (i.val+2720))=[]),
  (source_zero_86 : ∀ i : Fin 32, substitute basis (source (i.val+2752))=[]),
  (tail_zero_86 : ∀ i : Fin 32, substitute basis (tail (i.val+2752))=[]),
  (source_zero_87 : ∀ i : Fin 32, substitute basis (source (i.val+2784))=[]),
  (tail_zero_87 : ∀ i : Fin 32, substitute basis (tail (i.val+2784))=[]),
  (source_zero_88 : ∀ i : Fin 32, substitute basis (source (i.val+2816))=[]),
  (tail_zero_88 : ∀ i : Fin 32, substitute basis (tail (i.val+2816))=[]),
  (source_zero_89 : ∀ i : Fin 32, substitute basis (source (i.val+2848))=[]),
  (tail_zero_89 : ∀ i : Fin 32, substitute basis (tail (i.val+2848))=[]),
  (source_zero_90 : ∀ i : Fin 32, substitute basis (source (i.val+2880))=[]),
  (tail_zero_90 : ∀ i : Fin 32, substitute basis (tail (i.val+2880))=[]),
  (source_zero_91 : ∀ i : Fin 32, substitute basis (source (i.val+2912))=[]),
  (tail_zero_91 : ∀ i : Fin 32, substitute basis (tail (i.val+2912))=[]),
  (source_zero_92_part0 : ∀ i : Fin 8, substitute basis (source (i.val+2944))=[]),
  (tail_zero_92_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+2944))=[]),
  (source_zero_92_part1 : ∀ i : Fin 8, substitute basis (source (i.val+2952))=[]),
  (tail_zero_92_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+2952))=[]),
  (source_zero_92_part2 : ∀ i : Fin 8, substitute basis (source (i.val+2960))=[]),
  (tail_zero_92_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+2960))=[]),
  (source_zero_92_part3 : ∀ i : Fin 8, substitute basis (source (i.val+2968))=[]),
  (tail_zero_92_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+2968))=[]),
  (source_zero_93_part0 : ∀ i : Fin 8, substitute basis (source (i.val+2976))=[]),
  (tail_zero_93_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+2976))=[]),
  (source_zero_93_part1 : ∀ i : Fin 8, substitute basis (source (i.val+2984))=[]),
  (tail_zero_93_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+2984))=[]),
  (source_zero_93_part2 : ∀ i : Fin 8, substitute basis (source (i.val+2992))=[]),
  (tail_zero_93_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+2992))=[]),
  (source_zero_93_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3000))=[]),
  (tail_zero_93_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3000))=[]),
  (source_zero_94_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3008))=[]),
  (tail_zero_94_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3008))=[]),
  (source_zero_94_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3016))=[]),
  (tail_zero_94_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3016))=[]),
  (source_zero_94_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3024))=[]),
  (tail_zero_94_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3024))=[]),
  (source_zero_94_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3032))=[]),
  (tail_zero_94_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3032))=[]),
  (source_zero_95_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3040))=[]),
  (tail_zero_95_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3040))=[]),
  (source_zero_95_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3048))=[]),
  (tail_zero_95_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3048))=[]),
  (source_zero_95_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3056))=[]),
  (tail_zero_95_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3056))=[]),
  (source_zero_95_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3064))=[]),
  (tail_zero_95_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3064))=[]),
  (source_zero_96_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3072))=[]),
  (tail_zero_96_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3072))=[]),
  (source_zero_96_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3080))=[]),
  (tail_zero_96_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3080))=[]),
  (source_zero_96_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3088))=[]),
  (tail_zero_96_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3088))=[]),
  (source_zero_96_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3096))=[]),
  (tail_zero_96_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3096))=[]),
  (source_zero_97_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3104))=[]),
  (tail_zero_97_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3104))=[]),
  (source_zero_97_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3112))=[]),
  (tail_zero_97_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3112))=[]),
  (source_zero_97_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3120))=[]),
  (tail_zero_97_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3120))=[]),
  (source_zero_97_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3128))=[]),
  (tail_zero_97_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3128))=[]),
  (source_zero_98_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3136))=[]),
  (tail_zero_98_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3136))=[]),
  (source_zero_98_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3144))=[]),
  (tail_zero_98_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3144))=[]),
  (source_zero_98_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3152))=[]),
  (tail_zero_98_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3152))=[]),
  (source_zero_98_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3160))=[]),
  (tail_zero_98_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3160))=[]),
  (source_zero_99_part0_single0 : substitute basis (source 3168)=[]),
  (tail_zero_99_part0_single0 : substitute basis (tail 3168)=[]),
  (source_zero_99_part0_single1 : substitute basis (source 3169)=[]),
  (tail_zero_99_part0_single1 : substitute basis (tail 3169)=[]),
  (source_zero_99_part0_single2 : substitute basis (source 3170)=[]),
  (tail_zero_99_part0_single2 : substitute basis (tail 3170)=[]),
  (source_zero_99_part0_single3 : substitute basis (source 3171)=[]),
  (tail_zero_99_part0_single3 : substitute basis (tail 3171)=[]),
  (source_zero_99_part0_single4 : substitute basis (source 3172)=[]),
  (tail_zero_99_part0_single4 : substitute basis (tail 3172)=[]),
  (source_zero_99_part0_single5 : substitute basis (source 3173)=[]),
  (tail_zero_99_part0_single5 : substitute basis (tail 3173)=[]),
  (source_zero_99_part0_single6 : substitute basis (source 3174)=[]),
  (tail_zero_99_part0_single6 : substitute basis (tail 3174)=[]),
  (source_zero_99_part0_single7 : substitute basis (source 3175)=[]),
  (tail_zero_99_part0_single7 : substitute basis (tail 3175)=[]),
  (source_zero_99_part1_single0 : substitute basis (source 3176)=[]),
  (tail_zero_99_part1_single0 : substitute basis (tail 3176)=[]),
  (source_zero_99_part1_single1 : substitute basis (source 3177)=[]),
  (tail_zero_99_part1_single1 : substitute basis (tail 3177)=[]),
  (source_zero_99_part1_single2 : substitute basis (source 3178)=[]),
  (tail_zero_99_part1_single2 : substitute basis (tail 3178)=[]),
  (source_zero_99_part1_single3 : substitute basis (source 3179)=[]),
  (tail_zero_99_part1_single3 : substitute basis (tail 3179)=[]),
  (source_zero_99_part1_single4 : substitute basis (source 3180)=[]),
  (tail_zero_99_part1_single4 : substitute basis (tail 3180)=[]),
  (source_zero_99_part1_single5 : substitute basis (source 3181)=[]),
  (tail_zero_99_part1_single5 : substitute basis (tail 3181)=[]),
  (source_zero_99_part1_single6 : substitute basis (source 3182)=[]),
  (tail_zero_99_part1_single6 : substitute basis (tail 3182)=[]),
  (source_zero_99_part1_single7 : substitute basis (source 3183)=[]),
  (tail_zero_99_part1_single7 : substitute basis (tail 3183)=[]),
  (source_zero_99_part2_single0 : substitute basis (source 3184)=[]),
  (tail_zero_99_part2_single0 : substitute basis (tail 3184)=[]),
  (source_zero_99_part2_single1 : substitute basis (source 3185)=[]),
  (tail_zero_99_part2_single1 : substitute basis (tail 3185)=[]),
  (source_zero_99_part2_single2 : substitute basis (source 3186)=[]),
  (tail_zero_99_part2_single2 : substitute basis (tail 3186)=[]),
  (source_zero_99_part2_single3 : substitute basis (source 3187)=[]),
  (tail_zero_99_part2_single3 : substitute basis (tail 3187)=[]),
  (source_zero_99_part2_single4 : substitute basis (source 3188)=[]),
  (tail_zero_99_part2_single4 : substitute basis (tail 3188)=[]),
  (source_zero_99_part2_single5 : substitute basis (source 3189)=[]),
  (tail_zero_99_part2_single5 : substitute basis (tail 3189)=[]),
  (source_zero_99_part2_single6 : substitute basis (source 3190)=[]),
  (tail_zero_99_part2_single6 : substitute basis (tail 3190)=[]),
  (source_zero_99_part2_single7 : substitute basis (source 3191)=[]),
  (tail_zero_99_part2_single7 : substitute basis (tail 3191)=[]),
  (source_zero_99_part3_single0 : substitute basis (source 3192)=[]),
  (tail_zero_99_part3_single0 : substitute basis (tail 3192)=[]),
  (source_zero_99_part3_single1 : substitute basis (source 3193)=[]),
  (tail_zero_99_part3_single1 : substitute basis (tail 3193)=[]),
  (source_zero_99_part3_single2 : substitute basis (source 3194)=[]),
  (tail_zero_99_part3_single2 : substitute basis (tail 3194)=[]),
  (source_zero_99_part3_single3 : substitute basis (source 3195)=[]),
  (tail_zero_99_part3_single3 : substitute basis (tail 3195)=[]),
  (source_zero_99_part3_single4 : substitute basis (source 3196)=[]),
  (tail_zero_99_part3_single4 : substitute basis (tail 3196)=[]),
  (source_zero_99_part3_single5 : substitute basis (source 3197)=[]),
  (tail_zero_99_part3_single5 : substitute basis (tail 3197)=[]),
  (source_zero_99_part3_single6 : substitute basis (source 3198)=[]),
  (tail_zero_99_part3_single6 : substitute basis (tail 3198)=[]),
  (source_zero_99_part3_single7 : substitute basis (source 3199)=[]),
  (tail_zero_99_part3_single7 : substitute basis (tail 3199)=[]),
  (source_zero_100_part0_single0 : substitute basis (source 3200)=[]),
  (tail_zero_100_part0_single0 : substitute basis (tail 3200)=[]),
  (source_zero_100_part0_single1 : substitute basis (source 3201)=[]),
  (tail_zero_100_part0_single1 : substitute basis (tail 3201)=[]),
  (source_zero_100_part0_single2 : substitute basis (source 3202)=[]),
  (tail_zero_100_part0_single2 : substitute basis (tail 3202)=[]),
  (source_zero_100_part0_single3 : substitute basis (source 3203)=[]),
  (tail_zero_100_part0_single3 : substitute basis (tail 3203)=[]),
  (source_zero_100_part0_single4 : substitute basis (source 3204)=[]),
  (tail_zero_100_part0_single4 : substitute basis (tail 3204)=[]),
  (source_zero_100_part0_single5 : substitute basis (source 3205)=[]),
  (tail_zero_100_part0_single5 : substitute basis (tail 3205)=[]),
  (source_zero_100_part1_single0 : substitute basis (source 3208)=[]),
  (tail_zero_100_part1_single0 : substitute basis (tail 3208)=[]),
  (source_zero_100_part1_single1 : substitute basis (source 3209)=[]),
  (tail_zero_100_part1_single1 : substitute basis (tail 3209)=[]),
  (source_zero_100_part1_single5 : substitute basis (source 3213)=[]),
  (tail_zero_100_part1_single5 : substitute basis (tail 3213)=[]),
  (source_zero_100_part1_single6 : substitute basis (source 3214)=[]),
  (tail_zero_100_part1_single6 : substitute basis (tail 3214)=[]),
  (source_zero_100_part1_single7 : substitute basis (source 3215)=[]),
  (tail_zero_100_part1_single7 : substitute basis (tail 3215)=[]),
  (source_zero_100_part2_single0 : substitute basis (source 3216)=[]),
  (tail_zero_100_part2_single0 : substitute basis (tail 3216)=[]),
  (source_zero_100_part2_single1 : substitute basis (source 3217)=[]),
  (tail_zero_100_part2_single1 : substitute basis (tail 3217)=[]),
  (source_zero_100_part2_single2 : substitute basis (source 3218)=[]),
  (tail_zero_100_part2_single2 : substitute basis (tail 3218)=[]),
  (source_zero_100_part2_single3 : substitute basis (source 3219)=[]),
  (tail_zero_100_part2_single3 : substitute basis (tail 3219)=[]),
  (source_zero_100_part2_single4 : substitute basis (source 3220)=[]),
  (tail_zero_100_part2_single4 : substitute basis (tail 3220)=[]),
  (source_zero_100_part2_single5 : substitute basis (source 3221)=[]),
  (tail_zero_100_part2_single5 : substitute basis (tail 3221)=[]),
  (source_zero_100_part2_single6 : substitute basis (source 3222)=[]),
  (tail_zero_100_part2_single6 : substitute basis (tail 3222)=[]),
  (source_zero_100_part2_single7 : substitute basis (source 3223)=[]),
  (tail_zero_100_part2_single7 : substitute basis (tail 3223)=[]),
  (source_zero_100_part3_single0 : substitute basis (source 3224)=[]),
  (tail_zero_100_part3_single0 : substitute basis (tail 3224)=[]),
  (source_zero_100_part3_single1 : substitute basis (source 3225)=[]),
  (tail_zero_100_part3_single1 : substitute basis (tail 3225)=[]),
  (source_zero_100_part3_single2 : substitute basis (source 3226)=[]),
  (tail_zero_100_part3_single2 : substitute basis (tail 3226)=[]),
  (source_zero_100_part3_single3 : substitute basis (source 3227)=[]),
  (tail_zero_100_part3_single3 : substitute basis (tail 3227)=[]),
  (source_zero_100_part3_single4 : substitute basis (source 3228)=[]),
  (tail_zero_100_part3_single4 : substitute basis (tail 3228)=[]),
  (source_zero_100_part3_single5 : substitute basis (source 3229)=[]),
  (tail_zero_100_part3_single5 : substitute basis (tail 3229)=[]),
  (source_zero_100_part3_single6 : substitute basis (source 3230)=[]),
  (tail_zero_100_part3_single6 : substitute basis (tail 3230)=[]),
  (source_zero_100_part3_single7 : substitute basis (source 3231)=[]),
  (tail_zero_100_part3_single7 : substitute basis (tail 3231)=[]),
  (source_zero_101_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3232))=[]),
  (tail_zero_101_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3232))=[]),
  (source_zero_101_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3240))=[]),
  (tail_zero_101_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3240))=[]),
  (source_zero_101_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3248))=[]),
  (tail_zero_101_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3248))=[]),
  (source_zero_101_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3256))=[]),
  (tail_zero_101_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3256))=[]),
  (source_zero_102_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3264))=[]),
  (tail_zero_102_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3264))=[]),
  (source_zero_102_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3272))=[]),
  (tail_zero_102_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3272))=[]),
  (source_zero_102_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3280))=[]),
  (tail_zero_102_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3280))=[]),
  (source_zero_102_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3288))=[]),
  (tail_zero_102_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3288))=[]),
  (source_zero_103_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3296))=[]),
  (tail_zero_103_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3296))=[]),
  (source_zero_103_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3304))=[]),
  (tail_zero_103_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3304))=[]),
  (source_zero_103_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3312))=[]),
  (tail_zero_103_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3312))=[]),
  (source_zero_103_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3320))=[]),
  (tail_zero_103_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3320))=[]),
  (source_zero_104_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3328))=[]),
  (tail_zero_104_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3328))=[]),
  (source_zero_104_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3336))=[]),
  (tail_zero_104_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3336))=[]),
  (source_zero_104_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3344))=[]),
  (tail_zero_104_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3344))=[]),
  (source_zero_104_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3352))=[]),
  (tail_zero_104_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3352))=[]),
  (source_zero_105_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3360))=[]),
  (tail_zero_105_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3360))=[]),
  (source_zero_105_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3368))=[]),
  (tail_zero_105_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3368))=[]),
  (source_zero_105_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3376))=[]),
  (tail_zero_105_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3376))=[]),
  (source_zero_105_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3384))=[]),
  (tail_zero_105_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3384))=[]),
  (source_zero_106_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3392))=[]),
  (tail_zero_106_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3392))=[]),
  (source_zero_106_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3400))=[]),
  (tail_zero_106_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3400))=[]),
  (source_zero_106_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3408))=[]),
  (tail_zero_106_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3408))=[]),
  (source_zero_106_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3416))=[]),
  (tail_zero_106_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3416))=[]),
  (source_zero_107_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3424))=[]),
  (tail_zero_107_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3424))=[]),
  (source_zero_107_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3432))=[]),
  (tail_zero_107_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3432))=[]),
  (source_zero_107_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3440))=[]),
  (tail_zero_107_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3440))=[]),
  (source_zero_107_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3448))=[]),
  (tail_zero_107_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3448))=[]),
  (source_zero_108_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3456))=[]),
  (tail_zero_108_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3456))=[]),
  (source_zero_108_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3464))=[]),
  (tail_zero_108_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3464))=[]),
  (source_zero_108_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3472))=[]),
  (tail_zero_108_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3472))=[]),
  (source_zero_108_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3480))=[]),
  (tail_zero_108_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3480))=[]),
  (source_zero_109_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3488))=[]),
  (tail_zero_109_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3488))=[]),
  (source_zero_109_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3496))=[]),
  (tail_zero_109_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3496))=[]),
  (source_zero_109_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3504))=[]),
  (tail_zero_109_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3504))=[]),
  (source_zero_109_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3512))=[]),
  (tail_zero_109_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3512))=[]),
  (source_zero_110_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3520))=[]),
  (tail_zero_110_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3520))=[]),
  (source_zero_110_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3528))=[]),
  (tail_zero_110_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3528))=[]),
  (source_zero_110_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3536))=[]),
  (tail_zero_110_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3536))=[]),
  (source_zero_110_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3544))=[]),
  (tail_zero_110_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3544))=[]),
  (source_zero_111_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3552))=[]),
  (tail_zero_111_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3552))=[]),
  (source_zero_111_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3560))=[]),
  (tail_zero_111_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3560))=[]),
  (source_zero_111_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3568))=[]),
  (tail_zero_111_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3568))=[]),
  (source_zero_111_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3576))=[]),
  (tail_zero_111_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3576))=[]),
  (source_zero_112_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3584))=[]),
  (tail_zero_112_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3584))=[]),
  (source_zero_112_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3592))=[]),
  (tail_zero_112_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3592))=[]),
  (source_zero_112_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3600))=[]),
  (tail_zero_112_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3600))=[]),
  (source_zero_112_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3608))=[]),
  (tail_zero_112_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3608))=[]),
  (source_zero_113_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3616))=[]),
  (tail_zero_113_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3616))=[]),
  (source_zero_113_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3624))=[]),
  (tail_zero_113_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3624))=[]),
  (source_zero_113_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3632))=[]),
  (tail_zero_113_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3632))=[]),
  (source_zero_113_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3640))=[]),
  (tail_zero_113_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3640))=[]),
  (source_zero_114_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3648))=[]),
  (tail_zero_114_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3648))=[]),
  (source_zero_114_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3656))=[]),
  (tail_zero_114_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3656))=[]),
  (source_zero_114_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3664))=[]),
  (tail_zero_114_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3664))=[]),
  (source_zero_114_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3672))=[]),
  (tail_zero_114_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3672))=[]),
  (source_zero_115_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3680))=[]),
  (tail_zero_115_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3680))=[]),
  (source_zero_115_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3688))=[]),
  (tail_zero_115_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3688))=[]),
  (source_zero_115_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3696))=[]),
  (tail_zero_115_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3696))=[]),
  (source_zero_115_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3704))=[]),
  (tail_zero_115_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3704))=[]),
  (source_zero_116_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3712))=[]),
  (tail_zero_116_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3712))=[]),
  (source_zero_116_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3720))=[]),
  (tail_zero_116_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3720))=[]),
  (source_zero_116_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3728))=[]),
  (tail_zero_116_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3728))=[]),
  (source_zero_116_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3736))=[]),
  (tail_zero_116_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3736))=[]),
  (source_zero_117_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3744))=[]),
  (tail_zero_117_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3744))=[]),
  (source_zero_117_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3752))=[]),
  (tail_zero_117_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3752))=[]),
  (source_zero_117_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3760))=[]),
  (tail_zero_117_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3760))=[]),
  (source_zero_117_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3768))=[]),
  (tail_zero_117_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3768))=[]),
  (source_zero_118_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3776))=[]),
  (tail_zero_118_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3776))=[]),
  (source_zero_118_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3784))=[]),
  (tail_zero_118_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3784))=[]),
  (source_zero_118_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3792))=[]),
  (tail_zero_118_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3792))=[]),
  (source_zero_118_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3800))=[]),
  (tail_zero_118_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3800))=[]),
  (source_zero_119_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3808))=[]),
  (tail_zero_119_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3808))=[]),
  (source_zero_119_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3816))=[]),
  (tail_zero_119_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3816))=[]),
  (source_zero_119_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3824))=[]),
  (tail_zero_119_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3824))=[]),
  (source_zero_119_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3832))=[]),
  (tail_zero_119_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3832))=[]),
  (source_zero_120_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3840))=[]),
  (tail_zero_120_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3840))=[]),
  (source_zero_120_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3848))=[]),
  (tail_zero_120_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3848))=[]),
  (source_zero_120_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3856))=[]),
  (tail_zero_120_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3856))=[]),
  (source_zero_120_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3864))=[]),
  (tail_zero_120_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3864))=[]),
  (source_zero_121_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3872))=[]),
  (tail_zero_121_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3872))=[]),
  (source_zero_121_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3880))=[]),
  (tail_zero_121_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3880))=[]),
  (source_zero_121_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3888))=[]),
  (tail_zero_121_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3888))=[]),
  (source_zero_121_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3896))=[]),
  (tail_zero_121_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3896))=[]),
  (source_zero_122_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3904))=[]),
  (tail_zero_122_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3904))=[]),
  (source_zero_122_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3912))=[]),
  (tail_zero_122_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3912))=[]),
  (source_zero_122_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3920))=[]),
  (tail_zero_122_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3920))=[]),
  (source_zero_122_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3928))=[]),
  (tail_zero_122_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3928))=[]),
  (source_zero_123_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3936))=[]),
  (tail_zero_123_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3936))=[]),
  (source_zero_123_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3944))=[]),
  (tail_zero_123_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3944))=[]),
  (source_zero_123_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3952))=[]),
  (tail_zero_123_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3952))=[]),
  (source_zero_123_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3960))=[]),
  (tail_zero_123_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3960))=[]),
  (source_zero_124_part0 : ∀ i : Fin 8, substitute basis (source (i.val+3968))=[]),
  (tail_zero_124_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+3968))=[]),
  (source_zero_124_part1 : ∀ i : Fin 8, substitute basis (source (i.val+3976))=[]),
  (tail_zero_124_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+3976))=[]),
  (source_zero_124_part2 : ∀ i : Fin 8, substitute basis (source (i.val+3984))=[]),
  (tail_zero_124_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+3984))=[]),
  (source_zero_124_part3 : ∀ i : Fin 8, substitute basis (source (i.val+3992))=[]),
  (tail_zero_124_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+3992))=[]),
  (source_zero_125_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4000))=[]),
  (tail_zero_125_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4000))=[]),
  (source_zero_125_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4008))=[]),
  (tail_zero_125_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4008))=[]),
  (source_zero_125_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4016))=[]),
  (tail_zero_125_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4016))=[]),
  (source_zero_125_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4024))=[]),
  (tail_zero_125_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4024))=[]),
  (source_zero_126_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4032))=[]),
  (tail_zero_126_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4032))=[]),
  (source_zero_126_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4040))=[]),
  (tail_zero_126_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4040))=[]),
  (source_zero_126_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4048))=[]),
  (tail_zero_126_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4048))=[]),
  (source_zero_126_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4056))=[]),
  (tail_zero_126_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4056))=[]),
  (source_zero_127_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4064))=[]),
  (tail_zero_127_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4064))=[]),
  (source_zero_127_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4072))=[]),
  (tail_zero_127_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4072))=[]),
  (source_zero_127_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4080))=[]),
  (tail_zero_127_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4080))=[]),
  (source_zero_127_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4088))=[]),
  (tail_zero_127_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4088))=[]),
  (source_zero_128_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4096))=[]),
  (tail_zero_128_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4096))=[]),
  (source_zero_128_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4104))=[]),
  (tail_zero_128_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4104))=[]),
  (source_zero_128_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4112))=[]),
  (tail_zero_128_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4112))=[]),
  (source_zero_128_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4120))=[]),
  (tail_zero_128_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4120))=[]),
  (source_zero_129_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4128))=[]),
  (tail_zero_129_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4128))=[]),
  (source_zero_129_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4136))=[]),
  (tail_zero_129_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4136))=[]),
  (source_zero_129_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4144))=[]),
  (tail_zero_129_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4144))=[]),
  (source_zero_129_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4152))=[]),
  (tail_zero_129_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4152))=[]),
  (source_zero_130_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4160))=[]),
  (tail_zero_130_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4160))=[]),
  (source_zero_130_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4168))=[]),
  (tail_zero_130_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4168))=[]),
  (source_zero_130_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4176))=[]),
  (tail_zero_130_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4176))=[]),
  (source_zero_130_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4184))=[]),
  (tail_zero_130_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4184))=[]),
  (source_zero_131_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4192))=[]),
  (tail_zero_131_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4192))=[]),
  (source_zero_131_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4200))=[]),
  (tail_zero_131_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4200))=[]),
  (source_zero_131_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4208))=[]),
  (tail_zero_131_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4208))=[]),
  (source_zero_131_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4216))=[]),
  (tail_zero_131_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4216))=[]),
  (source_zero_132_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4224))=[]),
  (tail_zero_132_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4224))=[]),
  (source_zero_132_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4232))=[]),
  (tail_zero_132_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4232))=[]),
  (source_zero_132_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4240))=[]),
  (tail_zero_132_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4240))=[]),
  (source_zero_132_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4248))=[]),
  (tail_zero_132_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4248))=[]),
  (source_zero_133_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4256))=[]),
  (tail_zero_133_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4256))=[]),
  (source_zero_133_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4264))=[]),
  (tail_zero_133_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4264))=[]),
  (source_zero_133_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4272))=[]),
  (tail_zero_133_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4272))=[]),
  (source_zero_133_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4280))=[]),
  (tail_zero_133_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4280))=[]),
  (source_zero_134_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4288))=[]),
  (tail_zero_134_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4288))=[]),
  (source_zero_134_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4296))=[]),
  (tail_zero_134_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4296))=[]),
  (source_zero_134_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4304))=[]),
  (tail_zero_134_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4304))=[]),
  (source_zero_134_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4312))=[]),
  (tail_zero_134_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4312))=[]),
  (source_zero_135_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4320))=[]),
  (tail_zero_135_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4320))=[]),
  (source_zero_135_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4328))=[]),
  (tail_zero_135_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4328))=[]),
  (source_zero_135_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4336))=[]),
  (tail_zero_135_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4336))=[]),
  (source_zero_135_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4344))=[]),
  (tail_zero_135_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4344))=[]),
  (source_zero_136_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4352))=[]),
  (tail_zero_136_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4352))=[]),
  (source_zero_136_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4360))=[]),
  (tail_zero_136_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4360))=[]),
  (source_zero_136_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4368))=[]),
  (tail_zero_136_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4368))=[]),
  (source_zero_136_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4376))=[]),
  (tail_zero_136_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4376))=[]),
  (source_zero_137_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4384))=[]),
  (tail_zero_137_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4384))=[]),
  (source_zero_137_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4392))=[]),
  (tail_zero_137_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4392))=[]),
  (source_zero_137_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4400))=[]),
  (tail_zero_137_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4400))=[]),
  (source_zero_137_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4408))=[]),
  (tail_zero_137_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4408))=[]),
  (source_zero_138_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4416))=[]),
  (tail_zero_138_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4416))=[]),
  (source_zero_138_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4424))=[]),
  (tail_zero_138_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4424))=[]),
  (source_zero_138_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4432))=[]),
  (tail_zero_138_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4432))=[]),
  (source_zero_138_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4440))=[]),
  (tail_zero_138_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4440))=[]),
  (source_zero_139_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4448))=[]),
  (tail_zero_139_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4448))=[]),
  (source_zero_139_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4456))=[]),
  (tail_zero_139_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4456))=[]),
  (source_zero_139_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4464))=[]),
  (tail_zero_139_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4464))=[]),
  (source_zero_139_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4472))=[]),
  (tail_zero_139_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4472))=[]),
  (source_zero_140_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4480))=[]),
  (tail_zero_140_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4480))=[]),
  (source_zero_140_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4488))=[]),
  (tail_zero_140_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4488))=[]),
  (source_zero_140_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4496))=[]),
  (tail_zero_140_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4496))=[]),
  (source_zero_140_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4504))=[]),
  (tail_zero_140_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4504))=[]),
  (source_zero_141_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4512))=[]),
  (tail_zero_141_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4512))=[]),
  (source_zero_141_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4520))=[]),
  (tail_zero_141_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4520))=[]),
  (source_zero_141_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4528))=[]),
  (tail_zero_141_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4528))=[]),
  (source_zero_141_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4536))=[]),
  (tail_zero_141_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4536))=[]),
  (source_zero_142_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4544))=[]),
  (tail_zero_142_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4544))=[]),
  (source_zero_142_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4552))=[]),
  (tail_zero_142_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4552))=[]),
  (source_zero_142_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4560))=[]),
  (tail_zero_142_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4560))=[]),
  (source_zero_142_part3 : ∀ i : Fin 8, substitute basis (source (i.val+4568))=[]),
  (tail_zero_142_part3 : ∀ i : Fin 8, substitute basis (tail (i.val+4568))=[]),
  (source_zero_143_part0 : ∀ i : Fin 8, substitute basis (source (i.val+4576))=[]),
  (tail_zero_143_part0 : ∀ i : Fin 8, substitute basis (tail (i.val+4576))=[]),
  (source_zero_143_part1 : ∀ i : Fin 8, substitute basis (source (i.val+4584))=[]),
  (tail_zero_143_part1 : ∀ i : Fin 8, substitute basis (tail (i.val+4584))=[]),
  (source_zero_143_part2 : ∀ i : Fin 8, substitute basis (source (i.val+4592))=[]),
  (tail_zero_143_part2 : ∀ i : Fin 8, substitute basis (tail (i.val+4592))=[])
] by
  simp only [← substituteCompute_eq]
  decide +kernel

compact_certificate theorem source_zero_92 : ∀ i : Fin 32,
    substitute basis (source (i.val+2944))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+2944) :=
    (finite_range% P 2944 [
    8 => (fun i hi => source_zero_92_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_92_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_92_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_92_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_92

compact_certificate theorem tail_zero_92 : ∀ i : Fin 32,
    substitute basis (tail (i.val+2944))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+2944) :=
    (finite_range% P 2944 [
    8 => (fun i hi => tail_zero_92_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_92_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_92_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_92_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_92

compact_certificate theorem source_zero_93 : ∀ i : Fin 32,
    substitute basis (source (i.val+2976))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+2976) :=
    (finite_range% P 2976 [
    8 => (fun i hi => source_zero_93_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_93_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_93_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_93_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_93

compact_certificate theorem tail_zero_93 : ∀ i : Fin 32,
    substitute basis (tail (i.val+2976))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+2976) :=
    (finite_range% P 2976 [
    8 => (fun i hi => tail_zero_93_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_93_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_93_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_93_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_93

compact_certificate theorem source_zero_94 : ∀ i : Fin 32,
    substitute basis (source (i.val+3008))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3008) :=
    (finite_range% P 3008 [
    8 => (fun i hi => source_zero_94_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_94_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_94_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_94_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_94

compact_certificate theorem tail_zero_94 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3008))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3008) :=
    (finite_range% P 3008 [
    8 => (fun i hi => tail_zero_94_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_94_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_94_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_94_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_94

compact_certificate theorem source_zero_95 : ∀ i : Fin 32,
    substitute basis (source (i.val+3040))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3040) :=
    (finite_range% P 3040 [
    8 => (fun i hi => source_zero_95_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_95_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_95_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_95_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_95

compact_certificate theorem tail_zero_95 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3040))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3040) :=
    (finite_range% P 3040 [
    8 => (fun i hi => tail_zero_95_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_95_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_95_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_95_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_95

compact_certificate theorem source_zero_96 : ∀ i : Fin 32,
    substitute basis (source (i.val+3072))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3072) :=
    (finite_range% P 3072 [
    8 => (fun i hi => source_zero_96_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_96_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_96_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_96_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_96

compact_certificate theorem tail_zero_96 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3072))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3072) :=
    (finite_range% P 3072 [
    8 => (fun i hi => tail_zero_96_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_96_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_96_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_96_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_96

compact_certificate theorem source_zero_97 : ∀ i : Fin 32,
    substitute basis (source (i.val+3104))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3104) :=
    (finite_range% P 3104 [
    8 => (fun i hi => source_zero_97_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_97_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_97_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_97_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_97

compact_certificate theorem tail_zero_97 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3104))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3104) :=
    (finite_range% P 3104 [
    8 => (fun i hi => tail_zero_97_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_97_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_97_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_97_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_97

compact_certificate theorem source_zero_98 : ∀ i : Fin 32,
    substitute basis (source (i.val+3136))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3136) :=
    (finite_range% P 3136 [
    8 => (fun i hi => source_zero_98_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_98_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_98_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_98_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_98

compact_certificate theorem tail_zero_98 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3136))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3136) :=
    (finite_range% P 3136 [
    8 => (fun i hi => tail_zero_98_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_98_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_98_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_98_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_98

compact_certificate theorem source_zero_99_part0 : ∀ i : Fin 8,
    substitute basis (source (i.val+3168))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<8, P (i+3168) :=
    (finite_range% P 3168 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part0_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part0_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part0_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part0_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part0_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part0_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part0_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part0_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_99_part0


}
certificate_batch {
compact_certificate theorem tail_zero_99_part0 : ∀ i : Fin 8,
    substitute basis (tail (i.val+3168))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<8, P (i+3168) :=
    (finite_range% P 3168 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part0_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part0_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part0_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part0_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part0_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part0_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part0_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part0_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_99_part0

compact_certificate theorem source_zero_99_part1 : ∀ i : Fin 8,
    substitute basis (source (i.val+3176))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<8, P (i+3176) :=
    (finite_range% P 3176 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part1_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part1_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part1_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part1_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part1_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part1_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part1_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part1_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_99_part1

compact_certificate theorem tail_zero_99_part1 : ∀ i : Fin 8,
    substitute basis (tail (i.val+3176))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<8, P (i+3176) :=
    (finite_range% P 3176 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part1_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part1_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part1_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part1_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part1_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part1_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part1_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part1_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_99_part1

compact_certificate theorem source_zero_99_part2 : ∀ i : Fin 8,
    substitute basis (source (i.val+3184))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<8, P (i+3184) :=
    (finite_range% P 3184 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part2_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part2_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part2_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part2_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part2_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part2_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part2_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part2_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_99_part2

compact_certificate theorem tail_zero_99_part2 : ∀ i : Fin 8,
    substitute basis (tail (i.val+3184))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<8, P (i+3184) :=
    (finite_range% P 3184 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part2_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part2_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part2_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part2_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part2_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part2_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part2_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part2_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_99_part2

compact_certificate theorem source_zero_99_part3 : ∀ i : Fin 8,
    substitute basis (source (i.val+3192))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<8, P (i+3192) :=
    (finite_range% P 3192 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part3_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part3_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part3_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part3_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part3_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part3_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part3_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_99_part3_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_99_part3

compact_certificate theorem tail_zero_99_part3 : ∀ i : Fin 8,
    substitute basis (tail (i.val+3192))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<8, P (i+3192) :=
    (finite_range% P 3192 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part3_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part3_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part3_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part3_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part3_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part3_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part3_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_99_part3_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_99_part3

compact_certificate theorem source_zero_99 : ∀ i : Fin 32,
    substitute basis (source (i.val+3168))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3168) :=
    (finite_range% P 3168 [
    8 => (fun i hi => source_zero_99_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_99_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_99_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_99_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_99

compact_certificate theorem tail_zero_99 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3168))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3168) :=
    (finite_range% P 3168 [
    8 => (fun i hi => tail_zero_99_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_99_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_99_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_99_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_99

compact_certificate theorem source_zero_100_part0_single6 :
    substitute basis (source 3206)=[] := by
  rw [← substituteCompute_eq]
  simpa only [List.drop_zero, source3206Result0] using source3206_suffix0
#print axioms source_zero_100_part0_single6

compact_certificate theorem tail_zero_100_part0_single6 :
    substitute basis (tail 3206)=[] := by
  rw [← substituteCompute_eq]
  simpa only [List.drop_zero, tail3206Result0] using tail3206_suffix0
#print axioms tail_zero_100_part0_single6

compact_certificate theorem source_zero_100_part0_single7 :
    substitute basis (source 3207)=[] := by
  rw [← substituteCompute_eq]
  simpa only [List.drop_zero, source3207Result0] using source3207_suffix0
#print axioms source_zero_100_part0_single7

compact_certificate theorem tail_zero_100_part0_single7 :
    substitute basis (tail 3207)=[] := by
  rw [← substituteCompute_eq]
  simpa only [List.drop_zero, tail3207Result0] using tail3207_suffix0
#print axioms tail_zero_100_part0_single7

compact_certificate theorem source_zero_100_part0 : ∀ i : Fin 8,
    substitute basis (source (i.val+3200))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<8, P (i+3200) :=
    (finite_range% P 3200 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part0_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part0_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part0_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part0_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part0_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part0_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part0_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part0_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_100_part0

compact_certificate theorem tail_zero_100_part0 : ∀ i : Fin 8,
    substitute basis (tail (i.val+3200))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<8, P (i+3200) :=
    (finite_range% P 3200 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part0_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part0_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part0_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part0_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part0_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part0_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part0_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part0_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_100_part0

compact_certificate theorem source_zero_100_part1_single2 :
    substitute basis (source 3210)=[] := by
  rw [← substituteCompute_eq]
  simpa only [List.drop_zero, source3210Result0] using source3210_suffix0
#print axioms source_zero_100_part1_single2

compact_certificate theorem tail_zero_100_part1_single2 :
    substitute basis (tail 3210)=[] := by
  rw [← substituteCompute_eq]
  simpa only [List.drop_zero, tail3210Result0] using tail3210_suffix0
#print axioms tail_zero_100_part1_single2

compact_certificate theorem source_zero_100_part1_single3 :
    substitute basis (source 3211)=[] := by
  rw [← substituteCompute_eq]
  simpa only [List.drop_zero, source3211Result0] using source3211_suffix0
#print axioms source_zero_100_part1_single3

compact_certificate theorem tail_zero_100_part1_single3 :
    substitute basis (tail 3211)=[] := by
  rw [← substituteCompute_eq]
  simpa only [List.drop_zero, tail3211Result0] using tail3211_suffix0
#print axioms tail_zero_100_part1_single3

compact_certificate theorem source_zero_100_part1_single4 :
    substitute basis (source 3212)=[] := by
  rw [← substituteCompute_eq]
  simpa only [List.drop_zero, source3212Result0] using source3212_suffix0
#print axioms source_zero_100_part1_single4

compact_certificate theorem tail_zero_100_part1_single4 :
    substitute basis (tail 3212)=[] := by
  rw [← substituteCompute_eq]
  simpa only [List.drop_zero, tail3212Result0] using tail3212_suffix0
#print axioms tail_zero_100_part1_single4

compact_certificate theorem source_zero_100_part1 : ∀ i : Fin 8,
    substitute basis (source (i.val+3208))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<8, P (i+3208) :=
    (finite_range% P 3208 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part1_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part1_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part1_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part1_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part1_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part1_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part1_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part1_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_100_part1

compact_certificate theorem tail_zero_100_part1 : ∀ i : Fin 8,
    substitute basis (tail (i.val+3208))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<8, P (i+3208) :=
    (finite_range% P 3208 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part1_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part1_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part1_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part1_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part1_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part1_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part1_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part1_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_100_part1

compact_certificate theorem source_zero_100_part2 : ∀ i : Fin 8,
    substitute basis (source (i.val+3216))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<8, P (i+3216) :=
    (finite_range% P 3216 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part2_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part2_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part2_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part2_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part2_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part2_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part2_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part2_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_100_part2

compact_certificate theorem tail_zero_100_part2 : ∀ i : Fin 8,
    substitute basis (tail (i.val+3216))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<8, P (i+3216) :=
    (finite_range% P 3216 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part2_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part2_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part2_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part2_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part2_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part2_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part2_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part2_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_100_part2

compact_certificate theorem source_zero_100_part3 : ∀ i : Fin 8,
    substitute basis (source (i.val+3224))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<8, P (i+3224) :=
    (finite_range% P 3224 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part3_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part3_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part3_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part3_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part3_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part3_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part3_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton source_zero_100_part3_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_100_part3

compact_certificate theorem tail_zero_100_part3 : ∀ i : Fin 8,
    substitute basis (tail (i.val+3224))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<8, P (i+3224) :=
    (finite_range% P 3224 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part3_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part3_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part3_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part3_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part3_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part3_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part3_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton tail_zero_100_part3_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_100_part3

compact_certificate theorem source_zero_100 : ∀ i : Fin 32,
    substitute basis (source (i.val+3200))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3200) :=
    (finite_range% P 3200 [
    8 => (fun i hi => source_zero_100_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_100_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_100_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_100_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_100

compact_certificate theorem tail_zero_100 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3200))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3200) :=
    (finite_range% P 3200 [
    8 => (fun i hi => tail_zero_100_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_100_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_100_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_100_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_100

compact_certificate theorem source_zero_101 : ∀ i : Fin 32,
    substitute basis (source (i.val+3232))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3232) :=
    (finite_range% P 3232 [
    8 => (fun i hi => source_zero_101_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_101_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_101_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_101_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_101

compact_certificate theorem tail_zero_101 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3232))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3232) :=
    (finite_range% P 3232 [
    8 => (fun i hi => tail_zero_101_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_101_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_101_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_101_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_101

compact_certificate theorem source_zero_102 : ∀ i : Fin 32,
    substitute basis (source (i.val+3264))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3264) :=
    (finite_range% P 3264 [
    8 => (fun i hi => source_zero_102_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_102_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_102_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_102_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_102

compact_certificate theorem tail_zero_102 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3264))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3264) :=
    (finite_range% P 3264 [
    8 => (fun i hi => tail_zero_102_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_102_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_102_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_102_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_102

compact_certificate theorem source_zero_103 : ∀ i : Fin 32,
    substitute basis (source (i.val+3296))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3296) :=
    (finite_range% P 3296 [
    8 => (fun i hi => source_zero_103_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_103_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_103_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_103_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_103

compact_certificate theorem tail_zero_103 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3296))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3296) :=
    (finite_range% P 3296 [
    8 => (fun i hi => tail_zero_103_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_103_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_103_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_103_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_103

compact_certificate theorem source_zero_104 : ∀ i : Fin 32,
    substitute basis (source (i.val+3328))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3328) :=
    (finite_range% P 3328 [
    8 => (fun i hi => source_zero_104_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_104_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_104_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_104_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_104

compact_certificate theorem tail_zero_104 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3328))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3328) :=
    (finite_range% P 3328 [
    8 => (fun i hi => tail_zero_104_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_104_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_104_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_104_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_104

compact_certificate theorem source_zero_105 : ∀ i : Fin 32,
    substitute basis (source (i.val+3360))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3360) :=
    (finite_range% P 3360 [
    8 => (fun i hi => source_zero_105_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_105_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_105_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_105_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_105

compact_certificate theorem tail_zero_105 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3360))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3360) :=
    (finite_range% P 3360 [
    8 => (fun i hi => tail_zero_105_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_105_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_105_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_105_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_105

compact_certificate theorem source_zero_106 : ∀ i : Fin 32,
    substitute basis (source (i.val+3392))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3392) :=
    (finite_range% P 3392 [
    8 => (fun i hi => source_zero_106_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_106_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_106_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_106_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_106

compact_certificate theorem tail_zero_106 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3392))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3392) :=
    (finite_range% P 3392 [
    8 => (fun i hi => tail_zero_106_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_106_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_106_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_106_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_106

compact_certificate theorem source_zero_107 : ∀ i : Fin 32,
    substitute basis (source (i.val+3424))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3424) :=
    (finite_range% P 3424 [
    8 => (fun i hi => source_zero_107_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_107_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_107_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_107_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_107

compact_certificate theorem tail_zero_107 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3424))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3424) :=
    (finite_range% P 3424 [
    8 => (fun i hi => tail_zero_107_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_107_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_107_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_107_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_107

compact_certificate theorem source_zero_108 : ∀ i : Fin 32,
    substitute basis (source (i.val+3456))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3456) :=
    (finite_range% P 3456 [
    8 => (fun i hi => source_zero_108_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_108_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_108_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_108_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_108

compact_certificate theorem tail_zero_108 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3456))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3456) :=
    (finite_range% P 3456 [
    8 => (fun i hi => tail_zero_108_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_108_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_108_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_108_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_108

compact_certificate theorem source_zero_109 : ∀ i : Fin 32,
    substitute basis (source (i.val+3488))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3488) :=
    (finite_range% P 3488 [
    8 => (fun i hi => source_zero_109_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_109_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_109_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_109_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_109

compact_certificate theorem tail_zero_109 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3488))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3488) :=
    (finite_range% P 3488 [
    8 => (fun i hi => tail_zero_109_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_109_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_109_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_109_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_109

compact_certificate theorem source_zero_110 : ∀ i : Fin 32,
    substitute basis (source (i.val+3520))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3520) :=
    (finite_range% P 3520 [
    8 => (fun i hi => source_zero_110_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_110_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_110_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_110_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_110

compact_certificate theorem tail_zero_110 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3520))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3520) :=
    (finite_range% P 3520 [
    8 => (fun i hi => tail_zero_110_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_110_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_110_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_110_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_110

compact_certificate theorem source_zero_111 : ∀ i : Fin 32,
    substitute basis (source (i.val+3552))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3552) :=
    (finite_range% P 3552 [
    8 => (fun i hi => source_zero_111_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_111_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_111_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_111_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_111

compact_certificate theorem tail_zero_111 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3552))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3552) :=
    (finite_range% P 3552 [
    8 => (fun i hi => tail_zero_111_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_111_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_111_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_111_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_111

compact_certificate theorem source_zero_112 : ∀ i : Fin 32,
    substitute basis (source (i.val+3584))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3584) :=
    (finite_range% P 3584 [
    8 => (fun i hi => source_zero_112_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_112_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_112_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_112_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_112

compact_certificate theorem tail_zero_112 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3584))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3584) :=
    (finite_range% P 3584 [
    8 => (fun i hi => tail_zero_112_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_112_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_112_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_112_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_112

compact_certificate theorem source_zero_113 : ∀ i : Fin 32,
    substitute basis (source (i.val+3616))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3616) :=
    (finite_range% P 3616 [
    8 => (fun i hi => source_zero_113_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_113_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_113_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_113_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_113

compact_certificate theorem tail_zero_113 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3616))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3616) :=
    (finite_range% P 3616 [
    8 => (fun i hi => tail_zero_113_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_113_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_113_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_113_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_113

compact_certificate theorem source_zero_114 : ∀ i : Fin 32,
    substitute basis (source (i.val+3648))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3648) :=
    (finite_range% P 3648 [
    8 => (fun i hi => source_zero_114_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_114_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_114_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_114_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_114

compact_certificate theorem tail_zero_114 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3648))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3648) :=
    (finite_range% P 3648 [
    8 => (fun i hi => tail_zero_114_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_114_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_114_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_114_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_114

compact_certificate theorem source_zero_115 : ∀ i : Fin 32,
    substitute basis (source (i.val+3680))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3680) :=
    (finite_range% P 3680 [
    8 => (fun i hi => source_zero_115_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_115_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_115_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_115_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_115

compact_certificate theorem tail_zero_115 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3680))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3680) :=
    (finite_range% P 3680 [
    8 => (fun i hi => tail_zero_115_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_115_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_115_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_115_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_115

compact_certificate theorem source_zero_116 : ∀ i : Fin 32,
    substitute basis (source (i.val+3712))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3712) :=
    (finite_range% P 3712 [
    8 => (fun i hi => source_zero_116_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_116_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_116_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_116_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_116

compact_certificate theorem tail_zero_116 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3712))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3712) :=
    (finite_range% P 3712 [
    8 => (fun i hi => tail_zero_116_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_116_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_116_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_116_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_116

compact_certificate theorem source_zero_117 : ∀ i : Fin 32,
    substitute basis (source (i.val+3744))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3744) :=
    (finite_range% P 3744 [
    8 => (fun i hi => source_zero_117_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_117_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_117_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_117_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_117

compact_certificate theorem tail_zero_117 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3744))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3744) :=
    (finite_range% P 3744 [
    8 => (fun i hi => tail_zero_117_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_117_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_117_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_117_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_117

compact_certificate theorem source_zero_118 : ∀ i : Fin 32,
    substitute basis (source (i.val+3776))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3776) :=
    (finite_range% P 3776 [
    8 => (fun i hi => source_zero_118_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_118_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_118_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_118_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_118

compact_certificate theorem tail_zero_118 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3776))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3776) :=
    (finite_range% P 3776 [
    8 => (fun i hi => tail_zero_118_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_118_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_118_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_118_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_118

compact_certificate theorem source_zero_119 : ∀ i : Fin 32,
    substitute basis (source (i.val+3808))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3808) :=
    (finite_range% P 3808 [
    8 => (fun i hi => source_zero_119_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_119_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_119_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_119_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_119

compact_certificate theorem tail_zero_119 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3808))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3808) :=
    (finite_range% P 3808 [
    8 => (fun i hi => tail_zero_119_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_119_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_119_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_119_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_119

compact_certificate theorem source_zero_120 : ∀ i : Fin 32,
    substitute basis (source (i.val+3840))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3840) :=
    (finite_range% P 3840 [
    8 => (fun i hi => source_zero_120_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_120_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_120_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_120_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_120

compact_certificate theorem tail_zero_120 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3840))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3840) :=
    (finite_range% P 3840 [
    8 => (fun i hi => tail_zero_120_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_120_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_120_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_120_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_120

compact_certificate theorem source_zero_121 : ∀ i : Fin 32,
    substitute basis (source (i.val+3872))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3872) :=
    (finite_range% P 3872 [
    8 => (fun i hi => source_zero_121_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_121_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_121_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_121_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_121

compact_certificate theorem tail_zero_121 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3872))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3872) :=
    (finite_range% P 3872 [
    8 => (fun i hi => tail_zero_121_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_121_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_121_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_121_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_121

compact_certificate theorem source_zero_122 : ∀ i : Fin 32,
    substitute basis (source (i.val+3904))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3904) :=
    (finite_range% P 3904 [
    8 => (fun i hi => source_zero_122_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_122_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_122_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_122_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_122

compact_certificate theorem tail_zero_122 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3904))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3904) :=
    (finite_range% P 3904 [
    8 => (fun i hi => tail_zero_122_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_122_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_122_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_122_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_122

compact_certificate theorem source_zero_123 : ∀ i : Fin 32,
    substitute basis (source (i.val+3936))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3936) :=
    (finite_range% P 3936 [
    8 => (fun i hi => source_zero_123_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_123_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_123_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_123_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_123

compact_certificate theorem tail_zero_123 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3936))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3936) :=
    (finite_range% P 3936 [
    8 => (fun i hi => tail_zero_123_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_123_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_123_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_123_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_123

compact_certificate theorem source_zero_124 : ∀ i : Fin 32,
    substitute basis (source (i.val+3968))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+3968) :=
    (finite_range% P 3968 [
    8 => (fun i hi => source_zero_124_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_124_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_124_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_124_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_124

compact_certificate theorem tail_zero_124 : ∀ i : Fin 32,
    substitute basis (tail (i.val+3968))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+3968) :=
    (finite_range% P 3968 [
    8 => (fun i hi => tail_zero_124_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_124_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_124_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_124_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_124

compact_certificate theorem source_zero_125 : ∀ i : Fin 32,
    substitute basis (source (i.val+4000))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4000) :=
    (finite_range% P 4000 [
    8 => (fun i hi => source_zero_125_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_125_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_125_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_125_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_125

compact_certificate theorem tail_zero_125 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4000))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4000) :=
    (finite_range% P 4000 [
    8 => (fun i hi => tail_zero_125_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_125_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_125_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_125_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_125

compact_certificate theorem source_zero_126 : ∀ i : Fin 32,
    substitute basis (source (i.val+4032))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4032) :=
    (finite_range% P 4032 [
    8 => (fun i hi => source_zero_126_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_126_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_126_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_126_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_126

compact_certificate theorem tail_zero_126 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4032))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4032) :=
    (finite_range% P 4032 [
    8 => (fun i hi => tail_zero_126_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_126_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_126_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_126_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_126

compact_certificate theorem source_zero_127 : ∀ i : Fin 32,
    substitute basis (source (i.val+4064))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4064) :=
    (finite_range% P 4064 [
    8 => (fun i hi => source_zero_127_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_127_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_127_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_127_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_127

compact_certificate theorem tail_zero_127 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4064))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4064) :=
    (finite_range% P 4064 [
    8 => (fun i hi => tail_zero_127_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_127_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_127_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_127_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_127

compact_certificate theorem source_zero_128 : ∀ i : Fin 32,
    substitute basis (source (i.val+4096))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4096) :=
    (finite_range% P 4096 [
    8 => (fun i hi => source_zero_128_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_128_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_128_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_128_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_128

compact_certificate theorem tail_zero_128 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4096))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4096) :=
    (finite_range% P 4096 [
    8 => (fun i hi => tail_zero_128_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_128_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_128_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_128_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_128

compact_certificate theorem source_zero_129 : ∀ i : Fin 32,
    substitute basis (source (i.val+4128))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4128) :=
    (finite_range% P 4128 [
    8 => (fun i hi => source_zero_129_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_129_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_129_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_129_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_129

compact_certificate theorem tail_zero_129 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4128))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4128) :=
    (finite_range% P 4128 [
    8 => (fun i hi => tail_zero_129_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_129_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_129_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_129_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_129

compact_certificate theorem source_zero_130 : ∀ i : Fin 32,
    substitute basis (source (i.val+4160))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4160) :=
    (finite_range% P 4160 [
    8 => (fun i hi => source_zero_130_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_130_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_130_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_130_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_130

compact_certificate theorem tail_zero_130 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4160))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4160) :=
    (finite_range% P 4160 [
    8 => (fun i hi => tail_zero_130_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_130_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_130_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_130_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_130

compact_certificate theorem source_zero_131 : ∀ i : Fin 32,
    substitute basis (source (i.val+4192))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4192) :=
    (finite_range% P 4192 [
    8 => (fun i hi => source_zero_131_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_131_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_131_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_131_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_131

compact_certificate theorem tail_zero_131 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4192))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4192) :=
    (finite_range% P 4192 [
    8 => (fun i hi => tail_zero_131_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_131_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_131_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_131_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_131

compact_certificate theorem source_zero_132 : ∀ i : Fin 32,
    substitute basis (source (i.val+4224))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4224) :=
    (finite_range% P 4224 [
    8 => (fun i hi => source_zero_132_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_132_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_132_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_132_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_132

compact_certificate theorem tail_zero_132 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4224))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4224) :=
    (finite_range% P 4224 [
    8 => (fun i hi => tail_zero_132_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_132_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_132_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_132_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_132

compact_certificate theorem source_zero_133 : ∀ i : Fin 32,
    substitute basis (source (i.val+4256))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4256) :=
    (finite_range% P 4256 [
    8 => (fun i hi => source_zero_133_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_133_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_133_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_133_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_133

compact_certificate theorem tail_zero_133 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4256))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4256) :=
    (finite_range% P 4256 [
    8 => (fun i hi => tail_zero_133_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_133_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_133_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_133_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_133

compact_certificate theorem source_zero_134 : ∀ i : Fin 32,
    substitute basis (source (i.val+4288))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4288) :=
    (finite_range% P 4288 [
    8 => (fun i hi => source_zero_134_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_134_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_134_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_134_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_134

compact_certificate theorem tail_zero_134 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4288))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4288) :=
    (finite_range% P 4288 [
    8 => (fun i hi => tail_zero_134_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_134_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_134_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_134_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_134

compact_certificate theorem source_zero_135 : ∀ i : Fin 32,
    substitute basis (source (i.val+4320))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4320) :=
    (finite_range% P 4320 [
    8 => (fun i hi => source_zero_135_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_135_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_135_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_135_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_135

compact_certificate theorem tail_zero_135 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4320))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4320) :=
    (finite_range% P 4320 [
    8 => (fun i hi => tail_zero_135_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_135_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_135_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_135_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_135

compact_certificate theorem source_zero_136 : ∀ i : Fin 32,
    substitute basis (source (i.val+4352))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4352) :=
    (finite_range% P 4352 [
    8 => (fun i hi => source_zero_136_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_136_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_136_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_136_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_136

compact_certificate theorem tail_zero_136 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4352))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4352) :=
    (finite_range% P 4352 [
    8 => (fun i hi => tail_zero_136_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_136_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_136_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_136_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_136

compact_certificate theorem source_zero_137 : ∀ i : Fin 32,
    substitute basis (source (i.val+4384))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4384) :=
    (finite_range% P 4384 [
    8 => (fun i hi => source_zero_137_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_137_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_137_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_137_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_137

compact_certificate theorem tail_zero_137 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4384))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4384) :=
    (finite_range% P 4384 [
    8 => (fun i hi => tail_zero_137_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_137_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_137_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_137_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_137

compact_certificate theorem source_zero_138 : ∀ i : Fin 32,
    substitute basis (source (i.val+4416))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4416) :=
    (finite_range% P 4416 [
    8 => (fun i hi => source_zero_138_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_138_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_138_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_138_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_138

compact_certificate theorem tail_zero_138 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4416))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4416) :=
    (finite_range% P 4416 [
    8 => (fun i hi => tail_zero_138_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_138_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_138_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_138_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_138

compact_certificate theorem source_zero_139 : ∀ i : Fin 32,
    substitute basis (source (i.val+4448))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4448) :=
    (finite_range% P 4448 [
    8 => (fun i hi => source_zero_139_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_139_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_139_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_139_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_139

compact_certificate theorem tail_zero_139 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4448))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4448) :=
    (finite_range% P 4448 [
    8 => (fun i hi => tail_zero_139_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_139_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_139_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_139_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_139

compact_certificate theorem source_zero_140 : ∀ i : Fin 32,
    substitute basis (source (i.val+4480))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4480) :=
    (finite_range% P 4480 [
    8 => (fun i hi => source_zero_140_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_140_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_140_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_140_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_140

compact_certificate theorem tail_zero_140 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4480))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4480) :=
    (finite_range% P 4480 [
    8 => (fun i hi => tail_zero_140_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_140_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_140_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_140_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_140

compact_certificate theorem source_zero_141 : ∀ i : Fin 32,
    substitute basis (source (i.val+4512))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4512) :=
    (finite_range% P 4512 [
    8 => (fun i hi => source_zero_141_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_141_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_141_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_141_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_141

compact_certificate theorem tail_zero_141 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4512))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4512) :=
    (finite_range% P 4512 [
    8 => (fun i hi => tail_zero_141_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_141_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_141_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_141_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_141

compact_certificate theorem source_zero_142 : ∀ i : Fin 32,
    substitute basis (source (i.val+4544))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<32, P (i+4544) :=
    (finite_range% P 4544 [
    8 => (fun i hi => source_zero_142_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_142_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_142_part2 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_142_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_142

compact_certificate theorem tail_zero_142 : ∀ i : Fin 32,
    substitute basis (tail (i.val+4544))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<32, P (i+4544) :=
    (finite_range% P 4544 [
    8 => (fun i hi => tail_zero_142_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_142_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_142_part2 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_142_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_142


}
certificate_batch {
compact_certificate theorem source_zero_143 : ∀ i : Fin 24,
    substitute basis (source (i.val+4576))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ i<24, P (i+4576) :=
    (finite_range% P 4576 [
    8 => (fun i hi => source_zero_143_part0 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_143_part1 ⟨i,hi⟩),
    8 => (fun i hi => source_zero_143_part2 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms source_zero_143

compact_certificate theorem tail_zero_143 : ∀ i : Fin 24,
    substitute basis (tail (i.val+4576))=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ i<24, P (i+4576) :=
    (finite_range% P 4576 [
    8 => (fun i hi => tail_zero_143_part0 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_143_part1 ⟨i,hi⟩),
    8 => (fun i hi => tail_zero_143_part2 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms tail_zero_143
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentKernelExponentsV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows
compact_certificate def kernelExponent0 : Exponent := (-4,-2,0,0,0,0,0)
compact_certificate def kernelExponent1 : Exponent := (-4,-1,0,0,0,1,0)
compact_certificate def kernelExponent2 : Exponent := (-4,0,0,0,0,0,0)
compact_certificate def kernelExponent3 : Exponent := (-3,-2,0,0,1,0,0)
compact_certificate def kernelExponent4 : Exponent := (-3,-1,0,0,1,1,0)
compact_certificate def kernelExponent5 : Exponent := (-3,0,0,0,1,0,0)
compact_certificate def kernelExponent6 : Exponent := (-2,-2,-2,-2,0,0,0)
compact_certificate def kernelExponent7 : Exponent := (-2,-2,-2,0,0,0,0)
compact_certificate def kernelExponent8 : Exponent := (-2,-2,-2,2,0,0,0)
compact_certificate def kernelExponent9 : Exponent := (-2,-2,0,-2,0,0,0)
compact_certificate def kernelExponent10 : Exponent := (-2,-2,0,0,0,0,0)
compact_certificate def kernelExponent11 : Exponent := (-2,-2,0,0,2,0,0)
compact_certificate def kernelExponent12 : Exponent := (-2,-2,0,2,0,0,0)
compact_certificate def kernelExponent13 : Exponent := (-2,-2,2,-2,0,0,0)
compact_certificate def kernelExponent14 : Exponent := (-2,-2,2,2,0,0,0)
compact_certificate def kernelExponent15 : Exponent := (-2,-1,-2,0,0,1,0)
compact_certificate def kernelExponent16 : Exponent := (-2,-1,0,0,0,1,0)
compact_certificate def kernelExponent17 : Exponent := (-2,-1,0,0,2,1,0)
compact_certificate def kernelExponent18 : Exponent := (-2,0,-2,-2,0,0,0)
compact_certificate def kernelExponent19 : Exponent := (-2,0,-2,0,0,0,0)
compact_certificate def kernelExponent20 : Exponent := (-2,0,-2,2,0,0,0)
compact_certificate def kernelExponent21 : Exponent := (-2,0,0,-2,0,0,0)
compact_certificate def kernelExponent22 : Exponent := (-2,0,0,0,0,0,0)
compact_certificate def kernelExponent23 : Exponent := (-2,0,0,0,2,0,0)
compact_certificate def kernelExponent24 : Exponent := (-2,0,0,2,0,0,0)
compact_certificate def kernelExponent25 : Exponent := (-2,0,2,-2,0,0,0)
compact_certificate def kernelExponent26 : Exponent := (-2,2,-2,-2,0,0,0)
compact_certificate def kernelExponent27 : Exponent := (-2,2,-2,0,0,0,0)
compact_certificate def kernelExponent28 : Exponent := (-2,2,-2,2,0,0,0)
compact_certificate def kernelExponent29 : Exponent := (-2,2,0,-2,0,0,0)
compact_certificate def kernelExponent30 : Exponent := (-2,2,0,0,0,0,0)
compact_certificate def kernelExponent31 : Exponent := (-2,2,2,-2,0,0,0)
compact_certificate def kernelExponent32 : Exponent := (-1,-2,0,0,1,0,0)
compact_certificate def kernelExponent33 : Exponent := (-1,-1,0,0,1,1,0)
compact_certificate def kernelExponent34 : Exponent := (-1,0,0,0,1,0,0)
compact_certificate def kernelExponent35 : Exponent := (-1,2,0,0,1,0,0)
compact_certificate def kernelExponent36 : Exponent := (0,-4,0,0,0,0,0)
compact_certificate def kernelExponent37 : Exponent := (0,-3,0,0,0,1,0)
compact_certificate def kernelExponent38 : Exponent := (0,-2,-2,-2,0,0,0)
compact_certificate def kernelExponent39 : Exponent := (0,-2,-2,0,0,0,0)
compact_certificate def kernelExponent40 : Exponent := (0,-2,-2,2,0,0,0)
compact_certificate def kernelExponent41 : Exponent := (0,-2,0,-2,0,0,0)
compact_certificate def kernelExponent42 : Exponent := (0,-2,0,0,0,0,0)
compact_certificate def kernelExponent43 : Exponent := (0,-2,0,0,2,0,0)
compact_certificate def kernelExponent44 : Exponent := (0,-2,0,2,0,0,0)
compact_certificate def kernelExponent45 : Exponent := (0,-2,2,-2,0,0,0)
compact_certificate def kernelExponent46 : Exponent := (0,-1,0,0,0,1,0)
compact_certificate def kernelExponent47 : Exponent := (0,-1,0,0,2,1,0)
compact_certificate def kernelExponent48 : Exponent := (0,0,-2,-2,0,0,0)
compact_certificate def kernelExponent49 : Exponent := (0,0,-2,0,0,0,0)
compact_certificate def kernelExponent50 : Exponent := (0,0,-2,2,0,0,0)
compact_certificate def kernelExponent51 : Exponent := (0,0,0,-2,0,0,0)
compact_certificate def kernelExponent52 : Exponent := (0,0,0,-1,0,0,1)
compact_certificate def kernelExponent53 : Exponent := (0,0,0,0,0,0,0)
compact_certificate def kernelExponent54 : Exponent := (0,0,0,0,2,0,0)
compact_certificate def kernelExponent55 : Exponent := (0,0,2,-2,0,0,0)
compact_certificate def kernelExponent56 : Exponent := (0,2,-2,-2,0,0,0)
compact_certificate def kernelExponent57 : Exponent := (0,2,-2,0,0,0,0)
compact_certificate def kernelExponent58 : Exponent := (0,2,0,-2,0,0,0)
compact_certificate def kernelExponent59 : Exponent := (0,2,0,0,0,0,0)
compact_certificate def kernelExponent60 : Exponent := (0,2,0,2,0,0,0)
compact_certificate def kernelExponent61 : Exponent := (0,2,2,-2,0,0,0)
compact_certificate def kernelExponent62 : Exponent := (1,-2,0,0,1,0,0)
compact_certificate def kernelExponent63 : Exponent := (1,-1,0,0,1,1,0)
compact_certificate def kernelExponent64 : Exponent := (1,0,0,0,1,0,0)
compact_certificate def kernelExponent65 : Exponent := (2,-2,-2,-2,0,0,0)
compact_certificate def kernelExponent66 : Exponent := (2,-2,-2,0,0,0,0)
compact_certificate def kernelExponent67 : Exponent := (2,-2,-2,2,0,0,0)
compact_certificate def kernelExponent68 : Exponent := (2,-2,0,-2,0,0,0)
compact_certificate def kernelExponent69 : Exponent := (2,-2,0,0,0,0,0)
compact_certificate def kernelExponent70 : Exponent := (2,-2,0,2,0,0,0)
compact_certificate def kernelExponent71 : Exponent := (2,-2,2,-2,0,0,0)
compact_certificate def kernelExponent72 : Exponent := (2,-2,2,0,0,0,0)
compact_certificate def kernelExponent73 : Exponent := (2,-1,0,0,0,1,0)
compact_certificate def kernelExponent74 : Exponent := (2,0,-2,-2,0,0,0)
compact_certificate def kernelExponent75 : Exponent := (2,0,-2,0,0,0,0)
compact_certificate def kernelExponent76 : Exponent := (2,0,0,-2,0,0,0)
compact_certificate def kernelExponent77 : Exponent := (2,0,0,-1,0,0,1)
compact_certificate def kernelExponent78 : Exponent := (2,0,0,0,0,0,0)
compact_certificate def kernelExponent79 : Exponent := (2,0,2,-2,0,0,0)
compact_certificate def kernelExponent80 : Exponent := (2,2,-2,-2,0,0,0)
compact_certificate def kernelExponent81 : Exponent := (2,2,-2,0,0,0,0)
compact_certificate def kernelExponent82 : Exponent := (2,2,0,-2,0,0,0)
compact_certificate def kernelExponent83 : Exponent := (2,2,0,0,0,0,0)
compact_certificate def kernelExponent84 : Exponent := (2,2,2,-2,0,0,0)
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentNormalTablesBundleV4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate def normalPart0 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:546:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:0:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:525:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:550:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:1:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:2:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:3:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:4:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:6:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:7:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:12:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:14:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:528:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:21:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:28:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:42:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:532:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:84:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:548:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:966:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:87:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:39:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:1008:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:504:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:543:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:1036:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:1029:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:518:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:969:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:963:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:500:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:522:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart1 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:1043:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:524:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:526:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:1022:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:1038:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:81:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:1011:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:502:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:507:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:1044:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:1046:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:1047:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:1048:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:1049:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:35:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:840:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:560:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:960:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:10:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:90:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:210:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:540:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:15:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:490:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:85:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:40:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:1035:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:965:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:1015:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:510:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:1010:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:1040:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart2 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:49:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:150:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:756:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:77:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:514:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:1007:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:56:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:24:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:511:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:567:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:882:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:1000:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:1033:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:967:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:519:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:46:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:531:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:994:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:483:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:168:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:539:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:50:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:1026:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:83:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:1004:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:406:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:102:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:63:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:534:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:350:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:975:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:9:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart3 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:924:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:588:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:88:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:1032:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:22:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:1006:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:700:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:18:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:126:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:987:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:462:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:962:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:75:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:516:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:1028:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:44:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:1041:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:182:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:486:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:13:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:868:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:564:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:36:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:875:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:252:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:972:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:547:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:91:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:506:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:175:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:798:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:544:0,0,0,0,0,0,0"
  | _ => []

compact_certificate def normalPart4 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:959:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:1014:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:78:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:503:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:72:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:651:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:1012:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:156:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:231:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:492:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:777:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:273:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:399:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:978:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:38:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:894:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:1039:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:672:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:552:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:952:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:450:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:41:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:86:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:501:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:322:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:29:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:602:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:66:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:336:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:25:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:529:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:82:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart5 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:497:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:1002:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:1023:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:686:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:100:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:609:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:938:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:513:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:16:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:693:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:954:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:508:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:343:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:434:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:1024:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:427:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:784:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:259:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:903:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:574:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:300:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:600:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:98:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:378:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:549:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:964:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:1009:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:498:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:728:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:1021:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:196:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:825:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart6 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:675:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:850:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:224:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:517:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:308:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:93:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:658:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:70:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:45:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:420:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:980:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:945:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:630:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:545:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:5:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:20:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:30:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:105:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:970:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:1005:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:530:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:520:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:1020:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:1030:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:80:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:505:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:1045:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:535:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:735:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:140:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:990:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:385:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart7 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:770:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:555:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:480:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:280:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:570:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:495:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:910:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:315:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:60:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:515:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:665:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:120:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:455:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:245:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:870:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:170:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:180:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:805:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:595:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:930:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:720:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:370:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:880:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:270:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:795:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:112:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:537:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:950:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:441:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:1034:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:861:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:54:0,0,0,0,0,0,0"
  | _ => []

compact_certificate def normalPart8 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:742:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:957:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:48:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:553:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:714:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:968:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:1025:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:27:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:364:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:294:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:973:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:900:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:1001:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:43:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:536:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:690:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:340:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:750:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:147:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:476:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:400:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:357:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:542:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:96:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:707:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:330:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:680:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:780:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:360:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:710:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:154:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:33:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart9 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:11:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:108:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:581:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:1018:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:610:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:615:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:616:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:26:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:826:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:533:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:200:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:575:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:625:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:679:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:695:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:345:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:705:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:355:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:189:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:996:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:819:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:558:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:132:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:217:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:225:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:854:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:644:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:948:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:375:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:725:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:161:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:800:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart10 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:301:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:255:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:275:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:833:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:889:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:469:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:32:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:8:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:527:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:925:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:413:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:435:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:440:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:475:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:942:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:1042:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:521:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:523:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:392:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:812:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:51:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:623:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:203:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:721:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:287:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:917:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:582:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:931:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:371:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:791:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:266:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:896:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart11 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:1017:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:325:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:133:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:468:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:763:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:238:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:999:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:448:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:984:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:650:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:250:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:749:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:637:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:847:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:119:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:329:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:125:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:775:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:425:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:918:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:351:0,0,0,0,0,0,0;1/1:701:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:349:0,0,0,0,0,0,0;1/1:699:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:352:0,0,0,0,0,0,0;1/1:702:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:348:0,0,0,0,0,0,0;1/1:698:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:354:0,0,0,0,0,0,0;1/1:704:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:346:0,0,0,0,0,0,0;1/1:696:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:645:0,0,0,0,0,0,0;1/1:855:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:195:0,0,0,0,0,0,0;1/1:405:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:230:0,0,0,0,0,0,0;1/1:860:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:190:0,0,0,0,0,0,0;1/1:820:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:240:0,0,0,0,0,0,0;1/1:660:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:390:0,0,0,0,0,0,0;1/1:810:0,0,0,0,0,0,0"
  | _ => []

compact_certificate def normalPart12 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:465:0,0,0,0,0,0,0;1/1:885:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:165:0,0,0,0,0,0,0;1/1:585:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:285:0,0,0,0,0,0,0;1/1:915:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:135:0,0,0,0,0,0,0;1/1:765:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:176:0,0,0,0,0,0,0;1/1:876:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:174:0,0,0,0,0,0,0;1/1:874:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:318:0,0,0,0,0,0,0;1/1:738:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:312:0,0,0,0,0,0,0;1/1:732:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:130:0,0,0,0,0,0,0;1/1:760:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:290:0,0,0,0,0,0,0;1/1:920:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:460:0,0,0,0,0,0,0;1/1:670:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:380:0,0,0,0,0,0,0;1/1:590:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:52:-2,0,0,0,0,0,0;1/1:538:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:64:-2,0,0,0,0,0,0;1/1:541:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:19:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:23:0,0,0,0,0,0,0;1/1:92:-2,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:144:-2,0,0,0,0,0,0;1/1:561:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:160:-2,0,0,0,0,0,0;1/1:565:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:164:-2,0,0,0,0,0,0;1/1:566:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:172:-2,0,0,0,0,0,0;1/1:568:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:569:0,0,0,0,0,0,0;-1/1:876:-2,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:192:-2,0,0,0,0,0,0;1/1:573:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:204:0,0,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:216:-2,0,0,0,0,0,0;1/1:579:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:585:0,0,0,0,0,0,0;-1/1:660:-2,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:264:-2,0,0,0,0,0,0;1/1:591:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:603:0,0,0,0,0,0,0;-1/1:732:-2,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "-1/1:660:-1,0,0,0,1,0,0;1/1:855:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "-1/1:264:-1,0,0,0,1,0,0;1/1:657:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "-1/1:660:0,0,0,0,0,0,0;1/1:765:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:185:0,0,0,0,0,0,0;1/1:740:-2,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:405:0,0,0,0,0,0,0;-1/1:810:-1,0,0,0,1,0,0"
  | _ => []
compact_certificate def normalPart13 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:220:0,0,0,0,0,0,0;1/1:745:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:243:0,0,0,0,0,0,0;1/1:768:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:246:0,0,0,0,0,0,0;1/1:771:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:249:0,0,0,0,0,0,0;1/1:774:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:251:0,0,0,0,0,0,0;1/1:776:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:253:0,0,0,0,0,0,0;1/1:778:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:257:0,0,0,0,0,0,0;1/1:782:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:258:0,0,0,0,0,0,0;1/1:783:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:260:0,0,0,0,0,0,0;1/1:785:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:261:0,0,0,0,0,0,0;1/1:786:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:262:0,0,0,0,0,0,0;1/1:787:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:263:0,0,0,0,0,0,0;1/1:788:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:264:0,0,0,0,0,0,0;1/1:789:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:265:0,0,0,0,0,0,0;1/1:790:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:267:0,0,0,0,0,0,0;1/1:792:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:268:0,0,0,0,0,0,0;1/1:793:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:272:0,0,0,0,0,0,0;1/1:797:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:274:0,0,0,0,0,0,0;1/1:799:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:276:0,0,0,0,0,0,0;1/1:801:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:279:0,0,0,0,0,0,0;1/1:804:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:282:0,0,0,0,0,0,0;1/1:807:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "-1/1:810:0,0,0,0,0,0,0;1/1:915:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:305:0,0,0,0,0,0,0;1/1:830:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:310:-2,0,0,0,0,0,0;1/1:865:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "-1/1:810:-2,0,0,0,0,0,0;1/1:885:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:393:0,0,0,0,0,0,0;-1/1:786:-1,0,0,0,1,0,0"
  | 26 => laurent_polynomial% "1/1:447:0,0,0,0,0,0,0;1/1:738:-2,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:459:0,0,0,0,0,0,0;1/1:786:-2,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:471:0,0,0,0,0,0,0;1/1:834:-2,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:474:2,0,0,0,0,0,0;1/1:846:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:477:0,0,0,0,0,0,0;1/1:858:-2,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "-1/1:174:-2,0,0,0,0,0,0;1/1:481:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart14 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:482:0,0,0,0,0,0,0;1/1:878:-2,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:484:0,0,0,0,0,0,0;1/1:886:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:485:0,0,0,0,0,0,0;1/1:890:-2,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:489:0,0,0,0,0,0,0;1/1:906:-2,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:958:-2,0,0,0,0,0,0;1/1:1027:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:974:-2,0,0,0,0,0,0;1/1:1031:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:982:0,0,0,0,0,0,0;-1/1:1016:1,0,0,0,1,0,0"
  | 7 => laurent_polynomial% "1/1:509:0,0,0,0,0,0,0;1/1:986:-2,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:353:0,0,0,0,0,0,0;1/1:703:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:356:0,0,0,0,0,0,0;1/1:706:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:358:0,0,0,0,0,0,0;1/1:708:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:359:0,0,0,0,0,0,0;1/1:709:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:362:0,0,0,0,0,0,0;1/1:712:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:590:0,0,0,0,0,0,0;-1/1:730:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:740:0,0,0,0,0,0,0;-1/1:810:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:410:0,0,0,0,0,0,0;1/1:760:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:430:0,0,0,0,0,0,0;1/1:660:0,-1,0,0,0,1,0"
  | 17 => laurent_polynomial% "1/1:260:0,0,0,0,0,0,0;-1/1:660:0,-2,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:790:0,0,0,0,0,0,0;1/1:810:0,-2,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:470:0,0,0,0,0,0,0;1/1:820:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:145:0,0,0,0,0,0,0;1/1:845:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:354:0,-2,0,0,0,0,0;1/1:856:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:310:0,0,0,0,0,0,0;1/1:660:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:172:0,0,0,0,0,0,0;1/1:872:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:173:0,0,0,0,0,0,0;1/1:873:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:177:0,0,0,0,0,0,0;1/1:877:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:178:0,0,0,0,0,0,0;1/1:878:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:194:0,0,0,0,0,0,0;1/1:696:0,-2,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:205:0,0,0,0,0,0,0;1/1:905:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "-1/1:580:0,0,0,0,0,0,0;1/1:860:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:620:0,0,0,0,0,0,0;-1/1:810:0,-1,0,0,0,1,0"
  | 31 => laurent_polynomial% "-1/1:640:0,0,0,0,0,0,0;1/1:920:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart15 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:320:0,0,0,0,0,0,0;1/1:670:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:338:0,0,0,0,0,0,0;1/1:688:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:341:0,0,0,0,0,0,0;1/1:691:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:342:0,0,0,0,0,0,0;1/1:692:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:344:0,0,0,0,0,0,0;1/1:694:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:347:0,0,0,0,0,0,0;1/1:697:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:288:0,0,0,0,0,0,0;1/1:708:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:295:0,0,0,0,0,0,0;1/1:715:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:335:0,0,0,0,0,0,0;1/1:755:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:342:0,0,0,0,0,0,0;1/1:762:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:660:0,0,0,0,0,0,0;1/1:810:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:155:0,0,0,0,0,0,0;1/1:810:-2,-1,0,0,0,1,0;-1/1:810:-1,0,0,0,1,0,0"
  | 12 => laurent_polynomial% "1/1:810:-2,-1,0,0,0,1,0;-1/1:810:-1,0,0,0,1,0,0;1/1:895:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:215:0,0,0,0,0,0,0;1/1:635:0,0,0,0,0,0,0;1/1:845:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:415:0,0,0,0,0,0,0;1/1:835:0,0,0,0,0,0,0;-1/1:905:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:220:0,0,0,0,0,0,0;1/1:640:0,0,0,0,0,0,0;1/1:810:0,-1,0,0,0,1,0"
  | 16 => laurent_polynomial% "1/1:410:0,0,0,0,0,0,0;1/1:810:0,-1,0,0,0,1,0;1/1:830:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:470:0,0,0,0,0,0,0;-1/1:810:0,-2,0,0,0,0,0;1/1:890:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:160:0,0,0,0,0,0,0;1/1:580:0,0,0,0,0,0,0;-1/1:810:0,-2,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:730:0,0,0,0,0,0,0;1/1:810:0,0,0,0,0,0,0;1/1:940:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:110:0,0,0,0,0,0,0;1/1:320:0,0,0,0,0,0,0;1/1:810:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "-1/1:618:0,0,0,0,0,0,0;1/1:738:0,0,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:282:0,0,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;1/1:732:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:114:0,0,0,0,0,0,0;1/1:324:0,0,0,0,0,0,0;1/1:744:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:306:0,0,0,0,0,0,0;1/1:726:0,0,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:228:0,0,0,0,0,0,0;1/1:678:0,0,0,0,0,0,0;1/1:828:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:222:0,0,0,0,0,0,0;1/1:372:0,0,0,0,0,0,0;1/1:822:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:17:0,0,0,0,0,0,0;-1/1:34:-1,0,0,0,1,0,0;1/1:68:-2,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "-1/1:52:-1,0,0,0,1,0,0;1/1:104:-2,0,0,0,0,0,0;1/1:551:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "-1/1:58:-1,0,0,0,1,0,0;1/1:116:-2,0,0,0,0,0,0;1/1:554:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "-1/1:64:-1,0,0,0,1,0,0;1/1:128:-2,0,0,0,0,0,0;1/1:557:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "-1/1:76:-1,0,0,0,1,0,0;1/1:152:-2,0,0,0,0,0,0;1/1:563:0,0,0,0,0,0,0"
  | _ => []

compact_certificate def normalPart16 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "-1/1:92:-1,0,0,0,1,0,0;1/1:184:-2,0,0,0,0,0,0;1/1:571:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "-1/1:144:-1,0,0,0,1,0,0;1/1:597:0,0,0,0,0,0,0;-1/1:708:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "-1/1:162:1,0,0,0,1,0,0;1/1:324:0,0,0,0,0,0,0;1/1:606:2,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "-1/1:164:-1,0,0,0,1,0,0;1/1:328:-2,0,0,0,0,0,0;1/1:607:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "-1/1:166:-1,0,0,0,1,0,0;1/1:332:-2,0,0,0,0,0,0;1/1:608:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "-1/1:172:-1,0,0,0,1,0,0;1/1:611:0,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "-1/1:174:-1,0,0,0,1,0,0;1/1:348:-2,0,0,0,0,0,0;1/1:612:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:613:0,0,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;1/1:876:-1,0,0,0,1,0,0"
  | 8 => laurent_polynomial% "-1/1:186:1,0,0,0,1,0,0;1/1:372:0,0,0,0,0,0,0;1/1:618:2,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "-1/1:192:-1,0,0,0,1,0,0;1/1:384:-2,0,0,0,0,0,0;1/1:621:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:408:-2,0,0,0,0,0,0;1/1:576:1,0,0,0,1,0,0;1/1:627:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "-1/1:216:-1,0,0,0,1,0,0;1/1:432:-2,0,0,0,0,0,0;1/1:633:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:117:0,0,0,0,0,0,0;-1/1:234:-1,0,0,0,1,0,0;1/1:642:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:123:0,0,0,0,0,0,0;-1/1:246:-1,0,0,0,1,0,0;1/1:648:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:127:0,0,0,0,0,0,0;-1/1:254:-1,0,0,0,1,0,0;1/1:652:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:129:0,0,0,0,0,0,0;-1/1:258:-1,0,0,0,1,0,0;1/1:654:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:410:0,0,0,0,0,0,0;1/1:655:0,0,0,0,0,0,0;1/1:810:-1,-2,0,0,1,0,0"
  | 17 => laurent_polynomial% "1/1:131:0,0,0,0,0,0,0;-1/1:262:-1,0,0,0,1,0,0;1/1:656:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:134:0,0,0,0,0,0,0;-1/1:268:-1,0,0,0,1,0,0;1/1:659:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:136:0,0,0,0,0,0,0;-1/1:272:-1,0,0,0,1,0,0;1/1:661:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:137:0,0,0,0,0,0,0;-1/1:274:-1,0,0,0,1,0,0;1/1:662:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:138:0,0,0,0,0,0,0;-1/1:276:-1,0,0,0,1,0,0;1/1:663:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:141:0,0,0,0,0,0,0;-1/1:282:-1,0,0,0,1,0,0;1/1:666:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:234:0,0,0,0,0,0,0;1/1:759:0,0,0,0,0,0,0;1/1:936:-2,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:237:0,0,0,0,0,0,0;-1/1:342:0,0,0,0,0,0,0;-1/1:474:-1,0,0,0,1,0,0"
  | 25 => laurent_polynomial% "1/1:241:0,0,0,0,0,0,0;1/1:766:0,0,0,0,0,0,0;1/1:878:-3,0,0,0,1,0,0"
  | 26 => laurent_polynomial% "1/1:242:0,0,0,0,0,0,0;1/1:767:0,0,0,0,0,0,0;1/1:886:-3,0,0,0,1,0,0"
  | 27 => laurent_polynomial% "1/1:254:0,0,0,0,0,0,0;1/1:779:0,0,0,0,0,0,0;1/1:1016:-2,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:256:0,0,0,0,0,0,0;-1/1:512:-1,0,0,0,1,0,0;1/1:781:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:52:-3,0,0,0,1,0,0;1/1:269:0,0,0,0,0,0,0;1/1:794:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:34:-2,0,0,0,0,0,0;1/1:271:0,0,0,0,0,0,0;1/1:796:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:164:-3,0,0,0,1,0,0;1/1:283:0,0,0,0,0,0,0;1/1:808:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart17 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:172:-3,0,0,0,1,0,0;1/1:284:0,0,0,0,0,0,0;1/1:809:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "-1/1:576:-1,0,0,0,1,0,0;-1/1:708:0,0,0,0,0,0,0;1/1:813:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:470:-2,0,0,0,0,0,0;-1/1:810:-1,-1,0,0,1,1,0;1/1:810:0,0,0,0,0,0,0;1/1:835:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:384:0,0,0,0,0,0,0;-1/1:768:-1,0,0,0,1,0,0;1/1:909:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:387:0,0,0,0,0,0,0;-1/1:774:-1,0,0,0,1,0,0;1/1:912:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:388:0,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;1/1:913:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:389:0,0,0,0,0,0,0;-1/1:778:-1,0,0,0,1,0,0;1/1:914:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:391:0,0,0,0,0,0,0;-1/1:782:-1,0,0,0,1,0,0;1/1:916:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:394:0,0,0,0,0,0,0;-1/1:788:-1,0,0,0,1,0,0;1/1:919:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:395:0,0,0,0,0,0,0;1/1:640:0,0,0,0,0,0,0;1/1:810:-1,-2,0,0,1,0,0"
  | 10 => laurent_polynomial% "1/1:396:0,0,0,0,0,0,0;-1/1:792:-1,0,0,0,1,0,0;1/1:921:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:398:0,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;1/1:923:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:402:0,0,0,0,0,0,0;-1/1:804:-1,0,0,0,1,0,0;1/1:927:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:408:0,0,0,0,0,0,0;-1/1:816:-1,0,0,0,1,0,0;1/1:933:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:417:0,0,0,0,0,0,0;1/1:618:-2,0,0,0,0,0,0;-1/1:834:-1,0,0,0,1,0,0"
  | 15 => laurent_polynomial% "1/1:423:0,0,0,0,0,0,0;1/1:474:1,0,0,0,1,0,0;1/1:642:-2,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:429:0,0,0,0,0,0,0;1/1:666:-2,0,0,0,0,0,0;-1/1:858:-1,0,0,0,1,0,0"
  | 17 => laurent_polynomial% "1/1:432:2,0,0,0,0,0,0;1/1:678:0,0,0,0,0,0,0;-1/1:864:1,0,0,0,1,0,0"
  | 18 => laurent_polynomial% "1/1:174:-1,0,0,0,1,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:437:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:438:0,0,0,0,0,0,0;1/1:702:-2,0,0,0,0,0,0;-1/1:876:-1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "1/1:439:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;-1/1:878:-1,0,0,0,1,0,0"
  | 21 => laurent_polynomial% "1/1:442:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0"
  | 22 => laurent_polynomial% "1/1:443:0,0,0,0,0,0,0;1/1:722:-2,0,0,0,0,0,0;-1/1:886:-1,0,0,0,1,0,0"
  | 23 => laurent_polynomial% "1/1:444:2,0,0,0,0,0,0;1/1:726:0,0,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0"
  | 24 => laurent_polynomial% "-1/1:342:-2,0,0,0,0,0,0;1/1:453:0,0,0,0,0,0,0;-1/1:906:-1,0,0,0,1,0,0"
  | 25 => laurent_polynomial% "1/1:822:-2,0,0,0,0,0,0;-1/1:936:-1,0,0,0,1,0,0;1/1:993:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:479:0,0,0,0,0,0,0;1/1:866:-2,0,0,0,0,0,0;-1/1:958:-1,0,0,0,1,0,0"
  | 27 => laurent_polynomial% "1/1:487:0,0,0,0,0,0,0;1/1:898:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "1/1:491:0,0,0,0,0,0,0;1/1:914:-2,0,0,0,0,0,0;1/1:1016:0,0,0,0,0,0,0;-1/1:1016:0,0,0,0,2,0,0"
  | 29 => laurent_polynomial% "1/1:493:0,0,0,0,0,0,0;1/1:922:-2,0,0,0,0,0,0;-1/1:986:-1,0,0,0,1,0,0"
  | 30 => laurent_polynomial% "1/1:496:0,0,0,0,0,0,0;1/1:934:-2,0,0,0,0,0,0;-1/1:992:-1,0,0,0,1,0,0"
  | 31 => laurent_polynomial% "1/1:499:0,0,0,0,0,0,0;1/1:946:-2,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0"
  | _ => []
compact_certificate def normalPart18 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:512:0,0,0,0,0,0,0;1/1:998:-2,0,0,0,0,0,0;1/1:1037:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:99:0,-2,0,0,0,0,0;1/1:361:0,0,0,0,0,0,0;1/1:711:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:365:0,0,0,0,0,0,0;1/1:715:0,0,0,0,0,0,0;1/1:810:0,-2,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:144:0,-2,0,0,0,0,0;1/1:366:0,0,0,0,0,0,0;1/1:716:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:162:0,-2,0,0,0,0,0;1/1:368:0,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:216:0,-2,0,0,0,0,0;1/1:374:0,0,0,0,0,0,0;1/1:724:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:377:0,0,0,0,0,0,0;1/1:727:0,0,0,0,0,0,0;-1/1:768:0,-2,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:379:0,0,0,0,0,0,0;1/1:729:0,0,0,0,0,0,0;-1/1:786:0,-2,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:394:0,0,0,0,0,0,0;1/1:396:0,-2,0,0,0,0,0;1/1:744:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:52:0,0,0,0,0,0,0;1/1:402:0,0,0,0,0,0,0;1/1:752:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "-1/1:162:0,-1,0,0,0,1,0;1/1:404:0,0,0,0,0,0,0;1/1:754:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:55:0,0,0,0,0,0,0;1/1:755:0,0,0,0,0,0,0;-1/1:810:-2,-1,0,0,0,1,0;1/1:810:-1,0,0,0,1,0,0"
  | 12 => laurent_polynomial% "1/1:95:0,0,0,0,0,0,0;1/1:445:0,0,0,0,0,0,0;-1/1:810:-1,-2,0,0,1,0,0;1/1:810:0,-1,0,0,0,1,0"
  | 13 => laurent_polynomial% "1/1:115:0,0,0,0,0,0,0;-1/1:810:-2,0,0,0,0,0,0;1/1:815:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:118:0,0,0,0,0,0,0;-1/1:354:0,-1,0,0,0,1,0;1/1:818:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:164:0,0,0,0,0,0,0;1/1:426:0,-2,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:166:0,0,0,0,0,0,0;1/1:444:0,-2,0,0,0,0,0;1/1:866:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:169:0,0,0,0,0,0,0;-1/1:834:-2,-2,0,0,0,0,0;1/1:869:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:171:0,0,0,0,0,0,0;1/1:871:0,0,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0"
  | 19 => laurent_polynomial% "-1/1:144:-2,-2,0,0,0,0,0;1/1:179:0,0,0,0,0,0,0;1/1:879:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:181:0,0,0,0,0,0,0;-1/1:216:-2,-2,0,0,0,0,0;1/1:881:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:184:0,0,0,0,0,0,0;1/1:606:0,-2,0,0,0,0,0;1/1:884:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:186:0,0,0,0,0,0,0;1/1:624:0,-2,0,0,0,0,0;1/1:886:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:232:0,0,0,0,0,0,0;-1/1:696:0,-1,0,0,0,1,0;1/1:932:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:235:0,0,0,0,0,0,0;-1/1:810:-2,0,0,0,0,0,0;1/1:935:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:605:0,0,0,0,0,0,0;-1/1:810:-1,-2,0,0,1,0,0;1/1:810:0,-1,0,0,0,1,0;1/1:955:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:635:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;1/1:810:-1,-1,0,0,1,1,0;-1/1:810:0,0,0,0,0,0,0;1/1:985:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:365:0,0,0,0,0,0,0;-1/1:810:-2,-1,0,0,0,1,0;1/1:810:-1,0,0,0,1,0,0;1/1:810:0,-2,0,0,0,0,0;1/1:995:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:296:0,0,0,0,0,0,0;1/1:646:0,0,0,0,0,0,0;-1/1:888:0,-1,0,0,0,1,0"
  | 29 => laurent_polynomial% "1/1:298:0,0,0,0,0,0,0;1/1:648:0,0,0,0,0,0,0;1/1:998:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "-1/1:264:0,-2,0,0,0,0,0;1/1:321:0,0,0,0,0,0,0;1/1:671:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "-1/1:282:0,-2,0,0,0,0,0;1/1:323:0,0,0,0,0,0,0;1/1:673:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart19 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:326:0,0,0,0,0,0,0;1/1:676:0,0,0,0,0,0,0;1/1:834:0,-2,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:332:0,0,0,0,0,0,0;1/1:682:0,0,0,0,0,0,0;1/1:888:0,-2,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:333:0,0,0,0,0,0,0;1/1:683:0,0,0,0,0,0,0;1/1:897:0,-2,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:334:0,0,0,0,0,0,0;1/1:684:0,0,0,0,0,0,0;1/1:906:0,-2,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:55:0,0,0,0,0,0,0;1/1:685:0,0,0,0,0,0,0;-1/1:810:-2,-1,0,0,0,1,0;1/1:810:-1,0,0,0,1,0,0;1/1:810:0,-2,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:339:0,0,0,0,0,0,0;1/1:689:0,0,0,0,0,0,0;1/1:951:0,-2,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:264:0,0,0,0,0,0,0;1/1:474:0,0,0,0,0,0,0;1/1:684:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:138:0,0,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;1/1:768:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:276:0,0,0,0,0,0,0;1/1:696:0,0,0,0,0,0,0;1/1:906:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:282:0,0,0,0,0,0,0;1/1:702:0,0,0,0,0,0,0;1/1:912:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:366:0,0,0,0,0,0,0;1/1:576:0,0,0,0,0,0,0;1/1:786:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:292:0,0,0,0,0,0,0;1/1:712:0,0,0,0,0,0,0;1/1:922:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:128:0,0,0,0,0,0,0;-1/1:688:0,0,0,0,0,0,0;1/1:758:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:144:0,0,0,0,0,0,0;1/1:354:0,0,0,0,0,0,0;1/1:774:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:198:0,0,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;1/1:648:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:402:0,0,0,0,0,0,0;1/1:702:0,0,0,0,0,0,0;1/1:852:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:211:0,0,0,0,0,0,0;1/1:421:0,0,0,0,0,0,0;1/1:631:0,0,0,0,0,0,0;1/1:841:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:209:0,0,0,0,0,0,0;1/1:419:0,0,0,0,0,0,0;1/1:629:0,0,0,0,0,0,0;1/1:839:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:212:0,0,0,0,0,0,0;1/1:422:0,0,0,0,0,0,0;1/1:632:0,0,0,0,0,0,0;1/1:842:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:208:0,0,0,0,0,0,0;1/1:418:0,0,0,0,0,0,0;1/1:628:0,0,0,0,0,0,0;1/1:838:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:214:0,0,0,0,0,0,0;1/1:424:0,0,0,0,0,0,0;1/1:634:0,0,0,0,0,0,0;1/1:844:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:206:0,0,0,0,0,0,0;1/1:416:0,0,0,0,0,0,0;1/1:626:0,0,0,0,0,0,0;1/1:836:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:216:0,0,0,0,0,0,0;1/1:426:0,0,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;1/1:636:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:414:0,0,0,0,0,0,0;-1/1:576:2,0,0,0,0,0,0;1/1:624:0,0,0,0,0,0,0;1/1:834:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "-1/1:410:0,0,0,0,0,0,0;1/1:445:0,0,0,0,0,0,0;-1/1:810:-1,-2,0,0,1,0,0;-1/1:935:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:640:0,0,0,0,0,0,0;-1/1:810:-2,0,0,0,0,0,0;-1/1:810:0,-1,0,0,0,1,0;1/1:815:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:246:0,0,0,0,0,0,0;1/1:456:0,0,0,0,0,0,0;1/1:666:0,0,0,0,0,0,0;1/1:876:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:174:0,0,0,0,0,0,0;1/1:384:0,0,0,0,0,0,0;1/1:594:0,0,0,0,0,0,0;1/1:804:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:320:0,0,0,0,0,0,0;-1/1:410:0,0,0,0,0,0,0;-1/1:580:0,0,0,0,0,0,0;1/1:810:0,-2,0,0,0,0,0;1/1:810:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "-1/1:470:0,0,0,0,0,0,0;-1/1:640:0,0,0,0,0,0,0;1/1:730:0,0,0,0,0,0,0;1/1:810:0,-2,0,0,0,0,0;1/1:810:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:106:0,0,0,0,0,0,0;1/1:316:0,0,0,0,0,0,0;1/1:736:0,0,0,0,0,0,0;1/1:946:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:104:0,0,0,0,0,0,0;1/1:314:0,0,0,0,0,0,0;1/1:734:0,0,0,0,0,0,0;1/1:944:0,0,0,0,0,0,0"
  | _ => []

compact_certificate def normalPart20 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:580:-2,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:845:0,0,0,0,0,0,0;1/1:985:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:65:0,0,0,0,0,0,0;1/1:470:-2,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;1/1:905:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:258:0,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;1/1:864:1,0,0,0,1,0,0;1/1:888:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:162:0,0,0,0,0,0,0;1/1:186:1,0,0,0,1,0,0;-1/1:618:2,0,0,0,0,0,0;1/1:792:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:186:0,0,0,0,0,0,0;1/1:396:0,0,0,0,0,0,0;1/1:606:0,0,0,0,0,0,0;1/1:816:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:234:0,0,0,0,0,0,0;1/1:444:0,0,0,0,0,0,0;1/1:654:0,0,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:31:0,0,0,0,0,0,0;-1/1:62:-1,0,0,0,1,0,0;1/1:124:-2,0,0,0,0,0,0;1/1:556:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;-1/1:68:-1,0,0,0,1,0,0;1/1:136:-2,0,0,0,0,0,0;1/1:559:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:37:0,0,0,0,0,0,0;-1/1:74:-1,0,0,0,1,0,0;1/1:148:-2,0,0,0,0,0,0;1/1:562:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:47:0,0,0,0,0,0,0;-1/1:94:-1,0,0,0,1,0,0;1/1:188:-2,0,0,0,0,0,0;1/1:572:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:61:0,0,0,0,0,0,0;-1/1:122:-1,0,0,0,1,0,0;1/1:244:-2,0,0,0,0,0,0;1/1:586:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:62:0,0,0,0,0,0,0;-1/1:124:-1,0,0,0,1,0,0;1/1:248:-2,0,0,0,0,0,0;1/1:587:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:64:0,0,0,0,0,0,0;-1/1:128:-1,0,0,0,1,0,0;1/1:256:-2,0,0,0,0,0,0;1/1:589:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:67:0,0,0,0,0,0,0;-1/1:134:-1,0,0,0,1,0,0;1/1:268:-2,0,0,0,0,0,0;1/1:592:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:68:0,0,0,0,0,0,0;-1/1:136:-1,0,0,0,1,0,0;1/1:272:-2,0,0,0,0,0,0;1/1:593:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:71:0,0,0,0,0,0,0;-1/1:142:-1,0,0,0,1,0,0;1/1:284:-2,0,0,0,0,0,0;1/1:596:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:76:0,0,0,0,0,0,0;-1/1:152:-1,0,0,0,1,0,0;1/1:304:-2,0,0,0,0,0,0;1/1:601:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:79:0,0,0,0,0,0,0;-1/1:158:-1,0,0,0,1,0,0;1/1:316:-2,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "-1/1:410:-2,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:580:-1,0,0,0,1,0,0;1/1:810:-2,-2,0,0,0,0,0;1/1:810:-2,0,0,0,0,0,0;1/1:810:0,-1,0,0,0,1,0;1/1:955:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:89:0,0,0,0,0,0,0;1/1:614:0,0,0,0,0,0,0;-1/1:706:-2,0,0,0,0,0,0;1/1:878:-1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "1/1:94:0,0,0,0,0,0,0;-1/1:188:-1,0,0,0,1,0,0;1/1:376:-2,0,0,0,0,0,0;1/1:619:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:97:0,0,0,0,0,0,0;1/1:388:-2,0,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0"
  | 22 => laurent_polynomial% "1/1:109:0,0,0,0,0,0,0;-1/1:218:-1,0,0,0,1,0,0;1/1:436:-2,0,0,0,0,0,0;1/1:634:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:113:0,0,0,0,0,0,0;-1/1:226:-1,0,0,0,1,0,0;1/1:452:-2,0,0,0,0,0,0;1/1:638:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:122:0,0,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:488:-2,0,0,0,0,0,0;1/1:647:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:128:0,0,0,0,0,0,0;-1/1:256:-1,0,0,0,1,0,0;1/1:512:-2,0,0,0,0,0,0;1/1:653:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:139:0,0,0,0,0,0,0;-1/1:278:-1,0,0,0,1,0,0;1/1:556:-2,0,0,0,0,0,0;1/1:664:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:142:0,0,0,0,0,0,0;-1/1:172:-4,0,0,0,0,0,0;-1/1:284:-1,0,0,0,1,0,0;1/1:667:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:143:0,0,0,0,0,0,0;-1/1:286:-1,0,0,0,1,0,0;1/1:572:-2,0,0,0,0,0,0;1/1:668:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:144:0,0,0,0,0,0,0;1/1:576:-2,0,0,0,0,0,0;1/1:669:0,0,0,0,0,0,0;1/1:708:-1,0,0,0,1,0,0"
  | 30 => laurent_polynomial% "1/1:151:0,0,0,0,0,0,0;-1/1:302:-1,0,0,0,1,0,0;1/1:604:-2,0,0,0,0,0,0;1/1:676:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "-1/1:282:-1,0,0,0,1,0,0;-1/1:432:-1,0,0,0,1,0,0;1/1:624:-2,0,0,0,0,0,0;1/1:681:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart21 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:162:0,0,0,0,0,0,0;-1/1:162:0,0,0,0,2,0,0;1/1:606:1,0,0,0,1,0,0;1/1:648:-2,0,0,0,0,0,0;1/1:687:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:166:0,0,0,0,0,0,0;-1/1:332:-1,0,0,0,1,0,0;1/1:664:-2,0,0,0,0,0,0;1/1:691:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:172:0,0,0,0,0,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;1/1:697:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:342:-2,0,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:696:-1,0,0,0,1,0,0;1/1:873:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:174:0,0,0,0,0,0,0;-1/1:348:-1,0,0,0,1,0,0;1/1:696:-2,0,0,0,0,0,0;1/1:699:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:351:0,0,0,0,0,0,0;1/1:354:-2,0,0,0,0,0,0;-1/1:702:-1,0,0,0,1,0,0;1/1:876:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:177:0,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;1/1:702:0,0,0,0,0,0,0;1/1:708:-2,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:703:0,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;1/1:712:-2,0,0,0,0,0,0;-1/1:878:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:192:0,0,0,0,0,0,0;-1/1:384:-1,0,0,0,1,0,0;1/1:717:0,0,0,0,0,0,0;1/1:768:-2,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:193:0,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:718:0,0,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "-1/1:388:-1,0,0,0,1,0,0;-1/1:696:0,-2,0,0,0,0,0;1/1:719:0,0,0,0,0,0,0;1/1:776:-2,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:197:0,0,0,0,0,0,0;-1/1:394:-1,0,0,0,1,0,0;1/1:722:0,0,0,0,0,0,0;1/1:788:-2,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:199:0,0,0,0,0,0,0;-1/1:398:-1,0,0,0,1,0,0;1/1:724:0,0,0,0,0,0,0;1/1:796:-2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:216:0,0,0,0,0,0,0;-1/1:432:-1,0,0,0,1,0,0;1/1:741:0,0,0,0,0,0,0;1/1:864:-2,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:172:-2,0,0,0,0,0,0;1/1:218:0,0,0,0,0,0,0;-1/1:436:-1,0,0,0,1,0,0;1/1:743:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:221:0,0,0,0,0,0,0;1/1:718:-3,0,0,0,1,0,0;1/1:746:0,0,0,0,0,0,0;1/1:884:-2,0,0,0,0,0,0;-1/1:884:-2,0,0,0,2,0,0"
  | 16 => laurent_polynomial% "1/1:223:0,0,0,0,0,0,0;-1/1:446:-1,0,0,0,1,0,0;1/1:748:0,0,0,0,0,0,0;1/1:892:-2,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:226:0,0,0,0,0,0,0;-1/1:452:-1,0,0,0,1,0,0;1/1:751:0,0,0,0,0,0,0;1/1:904:-2,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:229:0,0,0,0,0,0,0;-1/1:458:-1,0,0,0,1,0,0;1/1:754:0,0,0,0,0,0,0;1/1:916:-2,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:236:0,0,0,0,0,0,0;-1/1:472:-1,0,0,0,1,0,0;1/1:761:0,0,0,0,0,0,0;1/1:944:-2,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:239:0,0,0,0,0,0,0;-1/1:478:-1,0,0,0,1,0,0;1/1:764:0,0,0,0,0,0,0;1/1:956:-2,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:244:0,0,0,0,0,0,0;-1/1:488:-1,0,0,0,1,0,0;1/1:769:0,0,0,0,0,0,0;1/1:976:-2,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:247:0,0,0,0,0,0,0;-1/1:494:-1,0,0,0,1,0,0;1/1:772:0,0,0,0,0,0,0;1/1:988:-2,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:248:0,0,0,0,0,0,0;1/1:773:0,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;1/1:992:-2,0,0,0,0,0,0;-1/1:992:-2,0,0,0,2,0,0"
  | 24 => laurent_polynomial% "1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;1/1:116:-3,0,0,0,1,0,0;1/1:277:0,0,0,0,0,0,0;1/1:802:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:62:-2,0,0,0,0,0,0;1/1:278:0,0,0,0,0,0,0;-1/1:556:-1,0,0,0,1,0,0;1/1:803:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:74:-2,0,0,0,0,0,0;1/1:281:0,0,0,0,0,0,0;-1/1:562:-1,0,0,0,1,0,0;1/1:806:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:94:-2,0,0,0,0,0,0;1/1:286:0,0,0,0,0,0,0;-1/1:572:-1,0,0,0,1,0,0;1/1:811:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:122:-2,0,0,0,0,0,0;1/1:293:0,0,0,0,0,0,0;-1/1:586:-1,0,0,0,1,0,0;1/1:818:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:146:-2,0,0,0,0,0,0;1/1:299:0,0,0,0,0,0,0;-1/1:598:-1,0,0,0,1,0,0;1/1:824:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:158:-2,0,0,0,0,0,0;1/1:302:0,0,0,0,0,0,0;-1/1:604:-1,0,0,0,1,0,0;1/1:827:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:162:-2,0,0,0,0,0,0;1/1:303:0,0,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;1/1:828:0,0,0,0,0,0,0"
  | _ => []

}
certificate_batch {
compact_certificate def normalPart22 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;1/1:304:0,0,0,0,0,0,0;1/1:332:-3,0,0,0,1,0,0;1/1:829:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:307:0,0,0,0,0,0,0;-1/1:614:-1,0,0,0,1,0,0;1/1:832:0,0,0,0,0,0,0;-1/1:878:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:186:-2,0,0,0,0,0,0;1/1:309:0,0,0,0,0,0,0;-1/1:618:-1,0,0,0,1,0,0;1/1:834:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:311:0,0,0,0,0,0,0;-1/1:622:-1,0,0,0,1,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:836:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:202:-2,0,0,0,0,0,0;1/1:313:0,0,0,0,0,0,0;-1/1:626:-1,0,0,0,1,0,0;1/1:838:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:218:-2,0,0,0,0,0,0;1/1:317:0,0,0,0,0,0,0;-1/1:634:-1,0,0,0,1,0,0;1/1:842:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:226:-2,0,0,0,0,0,0;1/1:319:0,0,0,0,0,0,0;-1/1:638:-1,0,0,0,1,0,0;1/1:844:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:234:-2,0,0,0,0,0,0;1/1:321:0,0,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;-1/1:642:-1,0,0,0,1,0,0"
  | 8 => laurent_polynomial% "1/1:262:-2,0,0,0,0,0,0;1/1:328:0,0,0,0,0,0,0;-1/1:656:-1,0,0,0,1,0,0;1/1:853:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:274:-2,0,0,0,0,0,0;1/1:331:0,0,0,0,0,0,0;-1/1:354:0,-2,0,0,0,0,0;-1/1:662:-1,0,0,0,1,0,0"
  | 10 => laurent_polynomial% "1/1:278:-2,0,0,0,0,0,0;1/1:332:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;1/1:857:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:282:-2,0,0,0,0,0,0;1/1:333:0,0,0,0,0,0,0;-1/1:666:-1,0,0,0,1,0,0;1/1:858:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:302:-2,0,0,0,0,0,0;-1/1:676:-1,0,0,0,1,0,0;-1/1:688:0,0,0,0,0,0,0;1/1:863:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:386:-2,0,0,0,0,0,0;1/1:709:0,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:162:1,-2,0,0,1,0,0;1/1:386:0,0,0,0,0,0,0;-1/1:606:2,-2,0,0,0,0,0;1/1:736:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:398:-2,0,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;-1/1:724:-1,0,0,0,1,0,0;1/1:887:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:363:0,0,0,0,0,0,0;1/1:402:-2,0,0,0,0,0,0;1/1:444:1,0,0,0,1,0,0;1/1:888:0,0,0,0,0,0,0;-1/1:888:0,0,0,0,2,0,0"
  | 17 => laurent_polynomial% "1/1:367:0,0,0,0,0,0,0;1/1:418:-2,0,0,0,0,0,0;-1/1:734:-1,0,0,0,1,0,0;1/1:892:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:369:0,0,0,0,0,0,0;1/1:426:-2,0,0,0,0,0,0;-1/1:618:-1,0,0,0,1,0,0;-1/1:768:-1,0,0,0,1,0,0"
  | 19 => laurent_polynomial% "1/1:342:-1,0,0,0,1,0,0;1/1:381:0,0,0,0,0,0,0;1/1:474:-2,0,0,0,0,0,0;1/1:906:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:382:0,0,0,0,0,0,0;1/1:478:-2,0,0,0,0,0,0;-1/1:764:-1,0,0,0,1,0,0;1/1:907:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:383:0,0,0,0,0,0,0;-1/1:766:-1,0,0,0,1,0,0;-1/1:878:-4,0,0,0,0,0,0;1/1:908:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:386:0,0,0,0,0,0,0;1/1:494:-2,0,0,0,0,0,0;-1/1:772:-1,0,0,0,1,0,0;1/1:911:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "-1/1:52:-4,0,0,0,0,0,0;1/1:397:0,0,0,0,0,0,0;-1/1:794:-1,0,0,0,1,0,0;1/1:922:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:403:0,0,0,0,0,0,0;1/1:562:-2,0,0,0,0,0,0;-1/1:806:-1,0,0,0,1,0,0;1/1:928:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:407:0,0,0,0,0,0,0;1/1:578:-2,0,0,0,0,0,0;-1/1:814:-1,0,0,0,1,0,0;1/1:932:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:409:0,0,0,0,0,0,0;1/1:586:-2,0,0,0,0,0,0;-1/1:818:-1,0,0,0,1,0,0;1/1:934:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:412:0,0,0,0,0,0,0;1/1:598:-2,0,0,0,0,0,0;-1/1:824:-1,0,0,0,1,0,0;1/1:937:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:416:0,0,0,0,0,0,0;1/1:614:-2,0,0,0,0,0,0;-1/1:832:-1,0,0,0,1,0,0;1/1:941:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:418:0,0,0,0,0,0,0;1/1:622:-2,0,0,0,0,0,0;-1/1:836:-1,0,0,0,1,0,0;1/1:943:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:419:0,0,0,0,0,0,0;1/1:626:-2,0,0,0,0,0,0;-1/1:838:-1,0,0,0,1,0,0;1/1:944:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:421:0,0,0,0,0,0,0;1/1:634:-2,0,0,0,0,0,0;-1/1:842:-1,0,0,0,1,0,0;1/1:946:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart23 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:422:0,0,0,0,0,0,0;1/1:638:-2,0,0,0,0,0,0;-1/1:844:-1,0,0,0,1,0,0;1/1:947:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:424:0,0,0,0,0,0,0;1/1:646:-2,0,0,0,0,0,0;-1/1:848:-1,0,0,0,1,0,0;1/1:949:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:354:-1,-2,0,0,1,0,0;1/1:428:0,0,0,0,0,0,0;1/1:662:-2,0,0,0,0,0,0;1/1:953:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:431:0,0,0,0,0,0,0;1/1:674:-2,0,0,0,0,0,0;-1/1:862:-1,0,0,0,1,0,0;1/1:956:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:172:-1,0,0,0,1,0,0;1/1:436:0,0,0,0,0,0,0;1/1:694:-2,0,0,0,0,0,0;1/1:961:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:446:0,0,0,0,0,0,0;1/1:734:-2,0,0,0,0,0,0;-1/1:892:-1,0,0,0,1,0,0;1/1:971:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:449:0,0,0,0,0,0,0;1/1:746:-2,0,0,0,0,0,0;-1/1:898:-1,0,0,0,1,0,0;1/1:974:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:451:0,0,0,0,0,0,0;1/1:754:-2,0,0,0,0,0,0;-1/1:902:-1,0,0,0,1,0,0;1/1:976:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:454:0,0,0,0,0,0,0;1/1:766:-2,0,0,0,0,0,0;-1/1:908:-1,0,0,0,1,0,0;1/1:979:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:457:0,0,0,0,0,0,0;1/1:778:-2,0,0,0,0,0,0;-1/1:914:-1,0,0,0,1,0,0;1/1:1016:1,0,0,0,1,0,0"
  | 10 => laurent_polynomial% "1/1:458:0,0,0,0,0,0,0;1/1:782:-2,0,0,0,0,0,0;-1/1:916:-1,0,0,0,1,0,0;1/1:983:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:461:0,0,0,0,0,0,0;1/1:794:-2,0,0,0,0,0,0;-1/1:922:-1,0,0,0,1,0,0;1/1:986:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:463:0,0,0,0,0,0,0;1/1:802:-2,0,0,0,0,0,0;-1/1:926:-1,0,0,0,1,0,0;1/1:988:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:464:0,0,0,0,0,0,0;1/1:806:-2,0,0,0,0,0,0;-1/1:928:-1,0,0,0,1,0,0;1/1:989:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:466:0,0,0,0,0,0,0;1/1:814:-2,0,0,0,0,0,0;-1/1:932:-1,0,0,0,1,0,0;1/1:991:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:467:0,0,0,0,0,0,0;1/1:818:-2,0,0,0,0,0,0;-1/1:934:-1,0,0,0,1,0,0;1/1:992:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:472:0,0,0,0,0,0,0;1/1:838:-2,0,0,0,0,0,0;-1/1:944:-1,0,0,0,1,0,0;1/1:997:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:473:0,0,0,0,0,0,0;1/1:842:-2,0,0,0,0,0,0;-1/1:946:-1,0,0,0,1,0,0;1/1:998:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:478:0,0,0,0,0,0,0;1/1:862:-2,0,0,0,0,0,0;-1/1:956:-1,0,0,0,1,0,0;1/1:1003:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:488:0,0,0,0,0,0,0;1/1:902:-2,0,0,0,0,0,0;-1/1:976:-1,0,0,0,1,0,0;1/1:1013:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:494:0,0,0,0,0,0,0;1/1:926:-2,0,0,0,0,0,0;-1/1:988:-1,0,0,0,1,0,0;1/1:1019:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:234:0,-2,0,0,0,0,0;1/1:376:0,0,0,0,0,0,0;-1/1:444:2,0,0,0,0,0,0;1/1:888:1,0,0,0,1,0,0"
  | 22 => laurent_polynomial% "-1/1:282:0,0,0,0,0,0,0;1/1:382:0,0,0,0,0,0,0;-1/1:432:0,0,0,0,0,0,0;-1/1:708:0,-2,0,0,0,0,0"
  | 23 => laurent_polynomial% "-1/1:144:0,-1,0,0,0,1,0;1/1:398:0,0,0,0,0,0,0;1/1:432:0,-2,0,0,0,0,0;1/1:748:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:62:0,0,0,0,0,0,0;-1/1:186:0,-1,0,0,0,1,0;-1/1:342:0,0,0,0,0,0,0;1/1:412:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:216:0,-1,0,0,0,1,0;1/1:422:0,0,0,0,0,0,0;1/1:648:0,-2,0,0,0,0,0;1/1:772:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "-1/1:234:0,-1,0,0,0,1,0;1/1:428:0,0,0,0,0,0,0;1/1:702:0,-2,0,0,0,0,0;1/1:778:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:446:0,0,0,0,0,0,0;1/1:708:0,-1,0,0,0,1,0;1/1:796:0,0,0,0,0,0,0;1/1:864:0,-2,0,0,0,0,0"
  | 28 => laurent_polynomial% "-1/1:162:1,-1,0,0,1,1,0;1/1:458:0,0,0,0,0,0,0;1/1:606:2,-1,0,0,0,1,0;1/1:808:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:128:0,0,0,0,0,0,0;-1/1:384:0,-1,0,0,0,1,0;1/1:478:0,0,0,0,0,0,0;1/1:828:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:136:0,0,0,0,0,0,0;1/1:174:0,-2,0,0,0,0,0;-1/1:408:0,-1,0,0,0,1,0;1/1:836:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:148:0,0,0,0,0,0,0;1/1:282:0,-2,0,0,0,0,0;-1/1:444:0,-1,0,0,0,1,0;1/1:848:0,0,0,0,0,0,0"
  | _ => []

compact_certificate def normalPart24 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:162:0,0,0,0,0,0,0;1/1:408:0,-2,0,0,0,0,0;1/1:512:0,0,0,0,0,0,0;1/1:862:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:167:0,0,0,0,0,0,0;1/1:342:-2,-2,0,0,0,0,0;1/1:867:0,0,0,0,0,0,0;1/1:906:-1,-2,0,0,1,0,0"
  | 2 => laurent_polynomial% "1/1:144:-1,-2,0,0,1,0,0;1/1:183:0,0,0,0,0,0,0;1/1:708:-2,-2,0,0,0,0,0;1/1:883:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "-1/1:52:-2,0,0,0,0,0,0;1/1:188:0,0,0,0,0,0,0;1/1:642:0,-2,0,0,0,0,0;1/1:888:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:202:0,0,0,0,0,0,0;-1/1:606:0,-1,0,0,0,1,0;1/1:768:0,-2,0,0,0,0,0;1/1:902:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:234:0,0,0,0,0,0,0;1/1:584:0,0,0,0,0,0,0;-1/1:702:0,-1,0,0,0,1,0;1/1:934:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:236:0,0,0,0,0,0,0;1/1:586:0,0,0,0,0,0,0;-1/1:708:0,-1,0,0,0,1,0;1/1:936:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:242:0,0,0,0,0,0,0;1/1:444:2,-1,0,0,0,1,0;1/1:592:0,0,0,0,0,0,0;-1/1:888:1,-1,0,0,1,1,0"
  | 8 => laurent_polynomial% "1/1:248:0,0,0,0,0,0,0;1/1:394:0,-1,0,0,0,1,0;1/1:396:0,-3,0,0,0,1,0;1/1:598:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:186:0,-2,0,0,0,0,0;1/1:254:0,0,0,0,0,0,0;1/1:342:0,-1,0,0,0,1,0;1/1:604:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:278:0,0,0,0,0,0,0;1/1:402:0,-2,0,0,0,0,0;1/1:628:0,0,0,0,0,0,0;-1/1:834:0,-1,0,0,0,1,0"
  | 11 => laurent_polynomial% "1/1:638:0,0,0,0,0,0,0;-1/1:708:0,0,0,0,0,0,0;-1/1:864:0,-1,0,0,0,1,0;1/1:988:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:302:0,0,0,0,0,0,0;1/1:618:0,-2,0,0,0,0,0;1/1:652:0,0,0,0,0,0,0;-1/1:906:0,-1,0,0,0,1,0"
  | 13 => laurent_polynomial% "-1/1:342:0,-2,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;1/1:668:0,0,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:226:0,0,0,0,0,0,0;-1/1:354:0,-2,0,0,0,0,0;1/1:436:0,0,0,0,0,0,0;1/1:646:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "-1/1:648:0,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;1/1:928:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:94:0,0,0,0,0,0,0;1/1:304:0,0,0,0,0,0,0;1/1:724:0,0,0,0,0,0,0;1/1:934:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:234:-1,0,0,0,1,0,0;1/1:327:0,0,0,0,0,0,0;-1/1:642:0,0,0,0,0,0,0;1/1:747:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "-1/1:52:0,0,0,0,0,0,0;1/1:122:0,0,0,0,0,0,0;1/1:332:0,0,0,0,0,0,0;-1/1:402:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:57:0,0,0,0,0,0,0;1/1:207:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:282:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:246:0,0,0,0,0,0,0;1/1:396:0,0,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;1/1:696:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:219:0,0,0,0,0,0,0;1/1:639:0,0,0,0,0,0,0;-1/1:666:-2,0,0,0,0,0,0;1/1:849:0,0,0,0,0,0,0;1/1:858:-1,0,0,0,1,0,0"
  | 22 => laurent_polynomial% "1/1:192:-1,0,0,0,1,0,0;1/1:201:0,0,0,0,0,0,0;-1/1:384:-2,0,0,0,0,0,0;1/1:411:0,0,0,0,0,0,0;1/1:831:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "-1/1:348:0,0,0,0,0,0,0;1/1:408:0,0,0,0,0,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:648:0,0,0,0,0,0,0;1/1:828:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:174:-1,0,0,0,1,0,0;1/1:192:0,0,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:402:0,0,0,0,0,0,0;1/1:822:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:55:0,0,0,0,0,0,0;-1/1:410:-2,0,0,0,0,0,0;1/1:410:0,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:580:-1,0,0,0,1,0,0;1/1:810:-2,-2,0,0,0,0,0;1/1:810:-2,0,0,0,0,0,0;1/1:810:-1,-2,0,0,1,0,0;1/1:810:0,-1,0,0,0,1,0;1/1:905:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:410:0,0,0,0,0,0,0;1/1:470:0,0,0,0,0,0,0;1/1:580:0,0,0,0,0,0,0;1/1:640:0,0,0,0,0,0,0;-1/1:810:0,-2,0,0,0,0,0;1/1:810:0,-1,0,0,0,1,0;-1/1:810:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:234:0,0,0,0,0,0,0;-1/1:264:0,0,0,0,0,0,0;1/1:384:0,0,0,0,0,0,0;-1/1:474:0,0,0,0,0,0,0;1/1:834:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:142:0,0,0,0,0,0,0;1/1:562:0,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:772:0,0,0,0,0,0,0;1/1:1016:1,0,0,0,1,0,0"
  | 29 => laurent_polynomial% "1/1:68:0,0,0,0,0,0,0;1/1:278:0,0,0,0,0,0,0;-1/1:348:0,0,0,0,0,0,0;1/1:488:0,0,0,0,0,0,0;1/1:908:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:74:0,0,0,0,0,0,0;1/1:284:0,0,0,0,0,0,0;-1/1:354:0,0,0,0,0,0,0;1/1:494:0,0,0,0,0,0,0;1/1:914:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:136:0,0,0,0,0,0,0;1/1:556:0,0,0,0,0,0,0;-1/1:696:0,0,0,0,0,0,0;1/1:766:0,0,0,0,0,0,0;1/1:976:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart25 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:386:0,0,0,0,0,0,0;1/1:596:0,0,0,0,0,0,0;1/1:806:0,0,0,0,0,0,0;-1/1:876:0,0,0,0,0,0,0;1/1:1016:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;-1/1:174:0,0,0,0,0,0,0;1/1:244:0,0,0,0,0,0,0;1/1:454:0,0,0,0,0,0,0;1/1:664:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:55:0,0,0,0,0,0,0;1/1:410:-1,0,0,0,1,0,0;1/1:580:-1,0,0,0,1,0,0;1/1:580:0,0,0,0,0,0,0;-1/1:640:-2,0,0,0,0,0,0;-1/1:810:-2,-1,0,0,0,1,0;-1/1:810:-1,-2,0,0,1,0,0"
  | 3 => laurent_polynomial% "1/1:58:0,0,0,0,0,0,0;-1/1:116:-1,0,0,0,1,0,0;1/1:583:0,0,0,0,0,0,0;1/1:696:-2,-1,0,0,0,1,0;-1/1:932:-2,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:73:0,0,0,0,0,0,0;-1/1:146:-1,0,0,0,1,0,0;1/1:598:0,0,0,0,0,0,0;-1/1:712:-2,0,0,0,0,0,0;-1/1:922:-2,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "-1/1:410:-2,0,0,0,0,0,0;-1/1:410:-1,0,0,0,1,0,0;1/1:410:0,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:580:-1,0,0,0,1,0,0;-1/1:640:-1,0,0,0,1,0,0;-1/1:810:-2,-1,0,0,0,1,0;1/1:810:-1,-2,0,0,1,0,0;-1/1:810:-1,-1,0,0,1,1,0;1/1:810:-1,0,0,0,1,0,0;1/1:935:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:99:0,0,0,0,0,0,0;1/1:348:-1,0,0,0,1,0,0;1/1:396:-2,0,0,0,0,0,0;1/1:624:0,0,0,0,0,0,0;1/1:648:-1,0,0,0,1,0,0"
  | 7 => laurent_polynomial% "1/1:410:0,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;1/1:580:0,0,0,0,0,0,0;-1/1:640:-1,0,0,0,1,0,0;-1/1:810:0,-2,0,0,0,0,0;-1/1:810:0,0,0,0,0,0,0;1/1:845:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:365:0,0,0,0,0,0,0;1/1:410:-2,0,0,0,0,0,0;1/1:410:-1,0,0,0,1,0,0;1/1:410:0,0,0,0,0,0,0;1/1:580:-1,0,0,0,1,0,0;1/1:580:0,0,0,0,0,0,0;1/1:640:0,0,0,0,0,0,0;1/1:810:-1,-1,0,0,1,1,0;1/1:810:0,-1,0,0,0,1,0;-1/1:810:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:116:0,0,0,0,0,0,0;1/1:464:-2,0,0,0,0,0,0;1/1:641:0,0,0,0,0,0,0;-1/1:696:-1,-1,0,0,1,1,0;1/1:932:-1,0,0,0,1,0,0"
  | 10 => laurent_polynomial% "-1/1:676:-2,0,0,0,0,0,0;-1/1:688:-1,0,0,0,1,0,0;-1/1:694:0,0,0,0,0,0,0;-1/1:834:-2,-2,0,0,0,0,0;1/1:869:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:171:0,0,0,0,0,0,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:342:-1,0,0,0,1,0,0;-1/1:474:-2,0,0,0,0,0,0;1/1:696:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:354:0,0,0,0,0,0,0;-1/1:576:-2,0,0,0,0,0,0;-1/1:708:-1,0,0,0,1,0,0;-1/1:786:-2,0,0,0,0,0,0;1/1:879:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:216:-2,-2,0,0,0,0,0;-1/1:706:0,0,0,0,0,0,0;-1/1:712:-1,0,0,0,1,0,0;-1/1:724:-2,0,0,0,0,0,0;1/1:881:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:186:0,0,0,0,0,0,0;-1/1:186:0,0,0,0,2,0,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;1/1:618:1,0,0,0,1,0,0;1/1:711:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "-1/1:458:-2,0,0,0,0,0,0;1/1:727:0,0,0,0,0,0,0;1/1:754:-1,0,0,0,1,0,0;-1/1:768:0,-2,0,0,0,0,0;-1/1:902:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "-1/1:162:-1,0,0,0,1,0,0;-1/1:186:0,0,0,0,0,0,0;1/1:291:0,0,0,0,0,0,0;1/1:394:-2,0,0,0,0,0,0;1/1:396:-2,-2,0,0,0,0,0;-1/1:396:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:134:-2,0,0,0,0,0,0;-1/1:592:-1,0,0,0,1,0,0;-1/1:646:0,0,0,0,0,0,0;1/1:821:0,0,0,0,0,0,0;1/1:888:0,-1,0,0,0,1,0"
  | 18 => laurent_polynomial% "1/1:373:0,0,0,0,0,0,0;-1/1:718:-4,0,0,0,0,0,0;-1/1:746:-1,0,0,0,1,0,0;1/1:884:-3,0,0,0,1,0,0;1/1:898:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:58:-3,0,0,0,1,0,0;-1/1:116:-4,0,0,0,0,0,0;1/1:401:0,0,0,0,0,0,0;-1/1:802:-1,0,0,0,1,0,0;1/1:926:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:186:1,0,0,0,1,0,0;-1/1:348:0,-2,0,0,0,0,0;-1/1:618:2,0,0,0,0,0,0;-1/1:648:0,-2,0,0,0,0,0;1/1:722:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:94:0,0,0,0,0,0,0;-1/1:282:0,-1,0,0,0,1,0;1/1:444:0,0,0,0,0,0,0;-1/1:474:2,-2,0,0,0,0,0;1/1:794:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "-1/1:444:2,-1,0,0,0,1,0;1/1:452:0,0,0,0,0,0,0;1/1:802:0,0,0,0,0,0,0;1/1:888:1,-1,0,0,1,1,0;1/1:936:0,-1,0,0,0,1,0"
  | 23 => laurent_polynomial% "1/1:124:0,0,0,0,0,0,0;-1/1:186:1,-1,0,0,1,1,0;1/1:474:0,0,0,0,0,0,0;1/1:618:2,-1,0,0,0,1,0;1/1:824:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:158:0,0,0,0,0,0,0;1/1:186:1,-2,0,0,1,0,0;-1/1:474:0,-1,0,0,0,1,0;-1/1:618:2,-2,0,0,0,0,0;1/1:858:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:316:0,0,0,0,0,0,0;-1/1:394:0,-2,0,0,0,0,0;-1/1:396:0,-4,0,0,0,0,0;1/1:666:0,0,0,0,0,0,0;1/1:1016:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "-1/1:348:0,-2,0,0,0,0,0;-1/1:396:0,-1,0,0,0,1,0;-1/1:768:0,-2,0,0,0,0,0;1/1:832:0,0,0,0,0,0,0;-1/1:878:-2,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:134:0,0,0,0,0,0,0;1/1:186:-2,0,0,0,0,0,0;-1/1:402:0,-1,0,0,0,1,0;1/1:624:-2,-2,0,0,0,0,0;1/1:834:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:192:0,0,0,0,0,0,0;-1/1:432:2,-2,0,0,0,0,0;-1/1:576:0,-1,0,0,0,1,0;1/1:864:1,-2,0,0,1,0,0;1/1:892:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:216:0,0,0,0,0,0,0;1/1:426:-2,-2,0,0,0,0,0;-1/1:648:0,-1,0,0,0,1,0;1/1:864:-2,0,0,0,0,0,0;1/1:916:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:282:0,0,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;1/1:662:0,0,0,0,0,0,0;1/1:708:0,-2,0,0,0,0,0;-1/1:936:0,-1,0,0,0,1,0"
  | 31 => laurent_polynomial% "1/1:256:0,0,0,0,0,0,0;-1/1:576:2,-2,0,0,0,0,0;1/1:606:0,0,0,0,0,0,0;-1/1:768:0,-1,0,0,0,1,0;1/1:956:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart26 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:268:0,0,0,0,0,0,0;1/1:282:0,-2,0,0,0,0,0;1/1:432:0,-2,0,0,0,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:804:0,-1,0,0,0,1,0"
  | 1 => laurent_polynomial% "-1/1:642:0,0,0,0,0,0,0;1/1:712:0,0,0,0,0,0,0;1/1:876:0,-1,0,0,0,1,0;1/1:922:0,0,0,0,0,0,0;-1/1:992:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:162:1,0,0,0,1,0,0;-1/1:186:0,-2,0,0,0,0,0;-1/1:396:0,-2,0,0,0,0,0;-1/1:606:0,-2,0,0,0,0,0;-1/1:606:2,0,0,0,0,0,0;1/1:674:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:328:0,0,0,0,0,0,0;-1/1:402:0,-2,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:702:0,-2,0,0,0,0,0;1/1:864:1,0,0,0,1,0,0"
  | 4 => laurent_polynomial% "1/1:62:0,0,0,0,0,0,0;1/1:272:0,0,0,0,0,0,0;-1/1:342:0,0,0,0,0,0,0;-1/1:878:-2,0,0,0,0,0,0;1/1:902:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:116:0,0,0,0,0,0,0;-1/1:676:0,0,0,0,0,0,0;1/1:746:0,0,0,0,0,0,0;-1/1:834:0,-2,0,0,0,0,0;1/1:956:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:152:0,0,0,0,0,0,0;1/1:572:0,0,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;1/1:782:0,0,0,0,0,0,0;1/1:992:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:394:0,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;-1/1:606:0,-2,0,0,0,0,0;1/1:814:0,0,0,0,0,0,0;-1/1:884:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:162:0,-1,0,0,0,1,0;1/1:614:0,0,0,0,0,0,0;-1/1:696:0,-2,0,0,0,0,0;-1/1:754:0,0,0,0,0,0,0;1/1:824:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:332:0,0,0,0,0,0,0;1/1:632:0,0,0,0,0,0,0;1/1:782:0,0,0,0,0,0,0;-1/1:878:-2,0,0,0,0,0,0;1/1:932:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "-1/1:264:0,0,0,0,0,0,0;1/1:339:0,0,0,0,0,0,0;1/1:639:0,0,0,0,0,0,0;-1/1:906:-2,0,0,0,0,0,0;1/1:939:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:494:0,0,0,0,0,0,0;-1/1:694:0,0,0,0,0,0,0;-1/1:696:0,-2,0,0,0,0,0;1/1:794:0,0,0,0,0,0,0;1/1:944:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:213:0,0,0,0,0,0,0;1/1:216:-1,0,0,0,1,0,0;-1/1:432:-2,0,0,0,0,0,0;-1/1:474:1,0,0,0,1,0,0;-1/1:642:-2,0,0,0,0,0,0;1/1:843:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:207:0,0,0,0,0,0,0;-1/1:408:-2,0,0,0,0,0,0;-1/1:576:1,0,0,0,1,0,0;-1/1:618:-2,0,0,0,0,0,0;1/1:834:-1,0,0,0,1,0,0;1/1:837:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:162:0,0,0,0,0,0,0;-1/1:174:-1,0,0,0,1,0,0;1/1:342:0,0,0,0,0,0,0;1/1:348:-2,0,0,0,0,0,0;-1/1:432:0,0,0,0,0,0,0;1/1:702:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:348:0,0,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;1/1:702:-2,0,0,0,0,0,0;1/1:708:0,0,0,0,0,0,0;-1/1:876:-1,0,0,0,1,0,0;-1/1:888:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:186:0,0,0,0,0,0,0;-1/1:216:0,0,0,0,0,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:474:2,0,0,0,0,0,0;1/1:786:0,0,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:159:0,0,0,0,0,0,0;-1/1:216:-2,0,0,0,0,0,0;-1/1:264:0,0,0,0,0,0,0;-1/1:426:-2,0,0,0,0,0,0;1/1:618:-1,0,0,0,1,0,0;1/1:768:-1,0,0,0,1,0,0"
  | 18 => laurent_polynomial% "1/1:646:0,0,0,0,0,0,0;-1/1:696:0,0,0,0,0,0,0;1/1:796:0,0,0,0,0,0,0;-1/1:934:-2,0,0,0,0,0,0;1/1:946:0,0,0,0,0,0,0;1/1:992:-1,0,0,0,1,0,0"
  | 19 => laurent_polynomial% "1/1:92:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;1/1:606:-1,-2,0,0,1,0,0;1/1:617:0,0,0,0,0,0,0;-1/1:718:-2,0,0,0,0,0,0;1/1:884:-1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "1/1:234:-1,-2,0,0,1,0,0;-1/1:402:-2,0,0,0,0,0,0;-1/1:444:1,0,0,0,1,0,0;-1/1:642:0,-2,0,0,0,0,0;1/1:713:0,0,0,0,0,0,0;-1/1:888:0,0,0,0,0,0,0;1/1:888:0,0,0,0,2,0,0"
  | 21 => laurent_polynomial% "-1/1:186:-2,0,0,0,0,0,0;-1/1:396:-2,0,0,0,0,0,0;-1/1:408:-1,0,0,0,1,0,0;-1/1:576:2,0,0,0,0,0,0;-1/1:606:-2,0,0,0,0,0,0;1/1:729:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:282:0,0,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;-1/1:624:-1,0,0,0,1,0,0;-1/1:648:-2,0,0,0,0,0,0;1/1:837:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:174:-2,0,0,0,0,0,0;-1/1:174:-2,0,0,0,2,0,0;1/1:348:-3,0,0,0,1,0,0;1/1:444:2,0,0,0,0,0,0;1/1:831:0,0,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0;-1/1:936:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:339:0,0,0,0,0,0,0;1/1:432:1,0,0,0,1,0,0;1/1:444:0,0,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0;-1/1:864:0,0,0,0,2,0,0;-1/1:888:-1,0,0,0,1,0,0;-1/1:936:-2,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:104:0,0,0,0,0,0,0;1/1:444:2,-2,0,0,0,0,0;-1/1:664:0,0,0,0,0,0,0;1/1:734:0,0,0,0,0,0,0;-1/1:888:1,-2,0,0,1,0,0;1/1:944:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:166:-1,0,0,0,1,0,0;-1/1:332:-2,0,0,0,0,0,0;1/1:433:0,0,0,0,0,0,0;1/1:444:-1,-2,0,0,1,0,0;-1/1:888:-2,-2,0,0,0,0,0;1/1:958:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:64:0,0,0,0,0,0,0;-1/1:192:0,-1,0,0,0,1,0;1/1:576:0,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;-1/1:624:0,0,0,0,0,0,0;1/1:764:0,0,0,0,0,0,0;-1/1:834:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:68:0,0,0,0,0,0,0;1/1:174:-1,-2,0,0,1,0,0;-1/1:348:-2,-2,0,0,0,0,0;1/1:418:0,0,0,0,0,0,0;1/1:576:2,-1,0,0,0,1,0;1/1:768:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "-1/1:186:1,-1,0,0,1,1,0;-1/1:264:0,0,0,0,0,0,0;1/1:618:2,-1,0,0,0,1,0;-1/1:754:0,0,0,0,0,0,0;1/1:824:0,0,0,0,0,0,0;1/1:906:0,-2,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:166:0,0,0,0,0,0,0;-1/1:234:0,-2,0,0,0,0,0;1/1:444:2,0,0,0,0,0,0;1/1:586:0,0,0,0,0,0,0;1/1:796:0,0,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0"
  | 31 => laurent_polynomial% "1/1:116:0,0,0,0,0,0,0;-1/1:186:0,0,0,0,0,0,0;-1/1:348:0,-1,0,0,0,1,0;-1/1:396:0,0,0,0,0,0,0;1/1:466:0,0,0,0,0,0,0;-1/1:606:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart27 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:424:0,0,0,0,0,0,0;1/1:634:0,0,0,0,0,0,0;1/1:642:0,-1,0,0,0,1,0;1/1:844:0,0,0,0,0,0,0;-1/1:876:0,-2,0,0,0,0,0;-1/1:914:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "-1/1:216:0,0,0,0,0,0,0;1/1:286:0,0,0,0,0,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:474:0,-2,0,0,0,0,0;1/1:474:2,0,0,0,0,0,0;-1/1:858:0,-1,0,0,0,1,0;1/1:986:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "-1/1:234:0,-2,0,0,0,0,0;-1/1:444:0,-2,0,0,0,0,0;1/1:444:2,0,0,0,0,0,0;1/1:656:0,0,0,0,0,0,0;-1/1:864:0,-2,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0;-1/1:936:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:218:0,0,0,0,0,0,0;1/1:234:0,-1,0,0,0,1,0;1/1:638:0,0,0,0,0,0,0;-1/1:702:0,-2,0,0,0,0,0;-1/1:778:0,0,0,0,0,0,0;1/1:848:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:64:0,0,0,0,0,0,0;1/1:186:-2,0,0,0,0,0,0;1/1:274:0,0,0,0,0,0,0;1/1:624:-2,-2,0,0,0,0,0;1/1:694:0,0,0,0,0,0,0;1/1:904:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:146:0,0,0,0,0,0,0;1/1:426:-2,-2,0,0,0,0,0;-1/1:706:0,0,0,0,0,0,0;1/1:776:0,0,0,0,0,0,0;1/1:864:-2,0,0,0,0,0,0;1/1:986:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:162:1,-1,0,0,1,1,0;1/1:388:0,0,0,0,0,0,0;-1/1:458:0,0,0,0,0,0,0;1/1:598:0,0,0,0,0,0,0;-1/1:606:2,-1,0,0,0,1,0;-1/1:878:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:626:0,0,0,0,0,0,0;-1/1:676:0,0,0,0,0,0,0;1/1:776:0,0,0,0,0,0,0;-1/1:834:0,-2,0,0,0,0,0;-1/1:876:0,0,0,0,0,0,0;1/1:926:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "-1/1:234:0,0,0,0,0,0,0;1/1:354:0,0,0,0,0,0,0;-1/1:444:0,0,0,0,0,0,0;-1/1:576:2,0,0,0,0,0,0;1/1:804:0,0,0,0,0,0,0;-1/1:864:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "-1/1:396:0,0,0,0,0,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:474:2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;-1/1:606:0,0,0,0,0,0,0;1/1:666:0,0,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "-1/1:426:0,0,0,0,0,0,0;1/1:444:2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;1/1:696:0,0,0,0,0,0,0;-1/1:876:0,0,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0;1/1:906:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:348:0,0,0,0,0,0,0;1/1:394:0,-1,0,0,0,1,0;1/1:396:0,-3,0,0,0,1,0;-1/1:398:0,0,0,0,0,0,0;1/1:598:0,0,0,0,0,0,0;-1/1:848:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:52:-2,0,0,0,0,0,0;1/1:166:-1,0,0,0,1,0,0;-1/1:332:-2,0,0,0,0,0,0;1/1:398:0,0,0,0,0,0,0;-1/1:642:0,-2,0,0,0,0,0;1/1:818:0,0,0,0,0,0,0;-1/1:888:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:121:0,0,0,0,0,0,0;1/1:186:-4,0,0,0,0,0,0;1/1:444:1,-1,0,0,1,1,0;1/1:592:-1,0,0,0,1,0,0;1/1:624:-4,-2,0,0,0,0,0;1/1:646:0,0,0,0,0,0,0;-1/1:888:0,-1,0,0,2,1,0"
  | 14 => laurent_polynomial% "-1/1:282:0,-2,0,0,0,0,0;1/1:444:0,-1,0,0,0,1,0;1/1:592:-2,0,0,0,0,0,0;1/1:646:-1,0,0,0,1,0,0;1/1:673:0,0,0,0,0,0,0;-1/1:848:0,0,0,0,0,0,0;-1/1:888:-1,-1,0,0,1,1,0"
  | 15 => laurent_polynomial% "-1/1:234:-2,0,0,0,0,0,0;1/1:402:-1,0,0,0,1,0,0;1/1:426:0,0,0,0,0,0,0;-1/1:444:-2,0,0,0,0,0,0;1/1:702:-1,0,0,0,1,0,0;-1/1:864:-2,0,0,0,0,0,0;1/1:951:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:144:-2,-1,0,0,0,1,0;1/1:187:0,0,0,0,0,0,0;1/1:216:-1,-2,0,0,1,0,0;-1/1:398:-2,0,0,0,0,0,0;-1/1:432:-2,-2,0,0,0,0,0;1/1:712:0,0,0,0,0,0,0;1/1:724:-1,0,0,0,1,0,0"
  | 17 => laurent_polynomial% "-1/1:162:-2,0,0,0,0,0,0;-1/1:186:-1,0,0,0,1,0,0;-1/1:348:0,0,0,0,0,0,0;-1/1:396:-1,0,0,0,1,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:648:0,0,0,0,0,0,0;1/1:723:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "-1/1:464:-1,0,0,0,1,0,0;1/1:648:-2,0,0,0,0,0,0;1/1:696:0,-1,0,0,0,1,0;-1/1:718:-2,0,0,0,0,0,0;1/1:757:0,0,0,0,0,0,0;-1/1:932:0,0,0,0,0,0,0;1/1:998:-2,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:162:1,0,0,0,1,0,0;-1/1:396:-2,0,0,0,0,0,0;1/1:474:0,0,0,0,0,0,0;-1/1:606:2,0,0,0,0,0,0;-1/1:648:-1,0,0,0,1,0,0;-1/1:696:-2,0,0,0,0,0,0;1/1:849:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:402:0,0,0,0,0,0,0;-1/1:432:0,0,0,0,0,0,0;-1/1:444:-1,0,0,0,1,0,0;-1/1:642:0,0,0,0,0,0,0;1/1:702:0,0,0,0,0,0,0;1/1:747:0,0,0,0,0,0,0;1/1:888:-2,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:186:1,0,0,0,1,0,0;1/1:394:-1,0,0,0,1,0,0;1/1:396:-1,-2,0,0,1,0,0;-1/1:618:2,0,0,0,0,0,0;-1/1:702:-4,0,0,0,0,0,0;1/1:876:-3,0,0,0,1,0,0;1/1:897:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:162:0,-1,0,0,0,1,0;-1/1:162:0,-1,0,0,2,1,0;1/1:426:-4,-2,0,0,0,0,0;1/1:458:-1,0,0,0,1,0,0;1/1:606:1,-1,0,0,1,1,0;-1/1:754:0,0,0,0,0,0,0;1/1:864:-4,0,0,0,0,0,0;1/1:929:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:396:0,-1,0,0,0,1,0;1/1:432:0,0,0,0,0,0,0;-1/1:474:2,-1,0,0,0,1,0;1/1:618:0,-2,0,0,0,0,0;1/1:696:0,-1,0,0,0,1,0;1/1:768:0,-2,0,0,0,0,0;1/1:782:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "-1/1:162:0,-2,0,0,0,0,0;-1/1:186:1,-2,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;1/1:618:2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;1/1:788:0,0,0,0,0,0,0;1/1:876:-1,0,0,0,1,0,0"
  | 25 => laurent_polynomial% "1/1:172:-2,0,0,0,0,0,0;1/1:282:0,-2,0,0,0,0,0;-1/1:444:0,-1,0,0,0,1,0;1/1:638:0,0,0,0,0,0,0;-1/1:778:0,0,0,0,0,0,0;1/1:848:0,0,0,0,0,0,0;-1/1:864:0,-1,0,0,0,1,0"
  | 26 => laurent_polynomial% "-1/1:354:0,-2,0,0,0,0,0;-1/1:432:2,-1,0,0,0,1,0;1/1:436:0,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;1/1:646:0,0,0,0,0,0,0;1/1:864:1,-1,0,0,1,1,0;-1/1:926:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:144:0,0,0,0,0,0,0;-1/1:162:1,0,0,0,1,0,0;-1/1:174:0,0,0,0,0,0,0;1/1:354:0,0,0,0,0,0,0;-1/1:474:0,0,0,0,0,0,0;1/1:606:2,0,0,0,0,0,0;-1/1:624:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:174:-1,0,0,0,1,0,0;-1/1:186:1,0,0,0,1,0,0;1/1:192:0,0,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;1/1:618:2,0,0,0,0,0,0;1/1:642:0,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "-1/1:348:0,0,0,0,0,0,0;1/1:408:0,0,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;1/1:858:0,0,0,0,0,0,0;-1/1:864:1,0,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0"
  | 30 => laurent_polynomial% "1/1:153:0,0,0,0,0,0,0;1/1:174:-3,0,0,0,1,0,0;-1/1:348:-4,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:444:1,0,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;1/1:888:0,0,0,0,2,0,0;1/1:936:-1,0,0,0,1,0,0"
  | 31 => laurent_polynomial% "1/1:157:0,0,0,0,0,0,0;-1/1:278:-2,0,0,0,0,0,0;-1/1:332:0,0,0,0,0,0,0;-1/1:402:-2,-2,0,0,0,0,0;-1/1:444:1,-2,0,0,1,0,0;1/1:664:-1,0,0,0,1,0,0;1/1:834:-2,-1,0,0,0,1,0;-1/1:888:0,-2,0,0,0,0,0;1/1:888:0,-2,0,0,2,0,0"
  | _ => []

compact_certificate def normalPart28 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "-1/1:234:-1,-1,0,0,1,1,0;-1/1:354:-2,-2,0,0,0,0,0;1/1:642:0,-1,0,0,0,1,0;1/1:702:-1,-2,0,0,1,0,0;1/1:739:0,0,0,0,0,0,0;1/1:778:-1,0,0,0,1,0,0;-1/1:876:0,-2,0,0,0,0,0;-1/1:914:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "-1/1:162:0,-2,0,0,0,0,0;1/1:162:0,-2,0,0,2,0,0;1/1:216:-2,-1,0,0,0,1,0;1/1:386:-1,0,0,0,1,0,0;-1/1:606:1,-2,0,0,1,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:718:0,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;1/1:893:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:116:0,0,0,0,0,0,0;-1/1:348:0,-1,0,0,0,1,0;-1/1:396:0,0,0,0,0,0,0;-1/1:576:2,-2,0,0,0,0,0;1/1:624:0,-2,0,0,0,0,0;-1/1:676:0,0,0,0,0,0,0;-1/1:768:0,-1,0,0,0,1,0;1/1:956:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:107:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;-1/1:282:0,0,0,0,0,0,0;-1/1:474:2,-1,0,0,0,1,0;-1/1:642:-1,-1,0,0,1,1,0;-1/1:778:-2,0,0,0,0,0,0;1/1:914:-1,0,0,0,1,0,0;-1/1:1016:1,0,0,0,1,0,0"
  | 4 => laurent_polynomial% "1/1:216:0,-2,0,0,0,0,0;1/1:234:0,0,0,0,0,0,0;1/1:426:0,-2,0,0,0,0,0;-1/1:702:0,-1,0,0,0,1,0;1/1:724:0,0,0,0,0,0,0;-1/1:794:0,0,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0;1/1:934:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:92:0,0,0,0,0,0,0;-1/1:186:1,0,0,0,1,0,0;1/1:302:0,0,0,0,0,0,0;1/1:348:0,-2,0,0,0,0,0;1/1:512:0,0,0,0,0,0,0;1/1:618:2,0,0,0,0,0,0;1/1:648:0,-2,0,0,0,0,0;1/1:932:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:172:0,0,0,0,0,0,0;1/1:472:0,0,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;1/1:642:0,0,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;1/1:772:0,0,0,0,0,0,0;-1/1:876:0,-1,0,0,0,1,0;1/1:992:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:244:0,0,0,0,0,0,0;1/1:282:0,-1,0,0,0,1,0;1/1:394:0,0,0,0,0,0,0;-1/1:444:0,0,0,0,0,0,0;1/1:474:2,-2,0,0,0,0,0;1/1:694:0,0,0,0,0,0,0;-1/1:794:0,0,0,0,0,0,0;1/1:844:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "-1/1:162:1,0,0,0,1,0,0;1/1:264:0,0,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;1/1:396:0,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;1/1:606:2,0,0,0,0,0,0;-1/1:624:0,0,0,0,0,0,0;-1/1:834:0,0,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:111:0,0,0,0,0,0,0;-1/1:216:0,0,0,0,0,0,0;-1/1:402:-1,0,0,0,1,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:432:-1,0,0,0,1,0,0;1/1:444:-2,0,0,0,0,0,0;1/1:474:2,0,0,0,0,0,0;1/1:642:-1,0,0,0,1,0,0;-1/1:702:-1,0,0,0,1,0,0"
  | 10 => laurent_polynomial% "-1/1:348:-1,0,0,0,1,0,0;1/1:408:-1,0,0,0,1,0,0;1/1:576:2,0,0,0,0,0,0;1/1:606:-2,0,0,0,0,0,0;1/1:618:-1,0,0,0,1,0,0;-1/1:624:0,0,0,0,0,0,0;-1/1:648:-1,0,0,0,1,0,0;-1/1:834:0,0,0,0,0,0,0;1/1:939:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:386:-1,0,0,0,1,0,0;-1/1:562:-2,0,0,0,0,0,0;-1/1:648:0,0,0,0,0,0,0;1/1:702:-2,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;1/1:806:-1,0,0,0,1,0,0;1/1:823:0,0,0,0,0,0,0;-1/1:876:-1,0,0,0,1,0,0;-1/1:998:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "-1/1:162:0,0,0,0,0,0,0;1/1:162:0,0,0,0,2,0,0;-1/1:186:-1,-2,0,0,1,0,0;1/1:337:0,0,0,0,0,0,0;-1/1:396:-1,-2,0,0,1,0,0;-1/1:408:0,-2,0,0,0,0,0;-1/1:512:0,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:606:1,0,0,0,1,0,0;-1/1:648:-2,0,0,0,0,0,0;-1/1:998:-2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;-1/1:234:0,0,0,0,0,0,0;1/1:264:0,0,0,0,0,0,0;1/1:444:2,-2,0,0,0,0,0;1/1:474:0,0,0,0,0,0,0;1/1:734:0,0,0,0,0,0,0;-1/1:834:0,0,0,0,0,0,0;-1/1:888:1,-2,0,0,1,0,0;-1/1:936:0,-2,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:186:0,0,0,0,0,0,0;-1/1:216:0,0,0,0,0,0,0;1/1:282:-1,0,0,0,1,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:432:-1,0,0,0,1,0,0;1/1:474:2,0,0,0,0,0,0;-1/1:624:-2,0,0,0,0,0,0;-1/1:834:-2,0,0,0,0,0,0;1/1:891:0,0,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:76:0,0,0,0,0,0,0;-1/1:234:0,-2,0,0,0,0,0;-1/1:432:2,-1,0,0,0,1,0;1/1:444:2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;1/1:676:0,0,0,0,0,0,0;1/1:864:1,-1,0,0,1,1,0;-1/1:888:1,0,0,0,1,0,0;-1/1:926:0,0,0,0,0,0,0;1/1:976:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:172:0,0,0,0,0,0,0;1/1:282:0,0,0,0,0,0,0;-1/1:348:0,-2,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;1/1:592:0,0,0,0,0,0,0;1/1:618:0,-2,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;1/1:802:0,0,0,0,0,0,0;1/1:876:-1,-2,0,0,1,0,0;1/1:888:0,-2,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:162:0,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;1/1:867:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:264:0,-1,0,0,0,1,0;-1/1:348:0,0,0,0,0,0,0;1/1:408:0,0,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;1/1:474:0,-1,0,0,0,1,0;1/1:578:0,0,0,0,0,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:718:0,0,0,0,0,0,0;-1/1:864:1,0,0,0,1,0,0;1/1:998:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:216:-1,0,0,0,1,0,0;1/1:402:-2,0,0,0,0,0,0;1/1:426:-1,0,0,0,1,0,0;-1/1:432:-2,0,0,0,0,0,0;-1/1:474:1,0,0,0,1,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;1/1:702:-2,0,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0;1/1:843:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "-1/1:34:-2,0,0,0,0,0,0;1/1:52:-1,0,0,0,1,0,0;1/1:174:-2,0,0,0,0,0,0;-1/1:234:0,-2,0,0,0,0,0;-1/1:244:-2,0,0,0,0,0,0;1/1:402:-1,0,0,0,1,0,0;1/1:444:2,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0;1/1:901:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "-1/1:162:0,-1,0,0,0,1,0;-1/1:162:1,0,0,0,1,0,0;-1/1:174:-1,-1,0,0,1,1,0;1/1:348:-2,-1,0,0,0,1,0;1/1:396:0,-2,0,0,0,0,0;-1/1:432:0,-1,0,0,0,1,0;1/1:464:0,0,0,0,0,0,0;-1/1:604:0,0,0,0,0,0,0;1/1:606:0,-2,0,0,0,0,0;1/1:606:2,0,0,0,0,0,0;1/1:702:0,-1,0,0,0,1,0;1/1:884:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "-1/1:58:0,0,0,0,0,0,0;1/1:116:-1,0,0,0,1,0,0;1/1:174:0,-1,0,0,0,1,0;-1/1:186:-1,0,0,0,1,0,0;1/1:233:0,0,0,0,0,0,0;-1/1:348:-1,-1,0,0,1,1,0;-1/1:396:-1,0,0,0,1,0,0;-1/1:408:0,0,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;1/1:932:-2,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:284:0,0,0,0,0,0,0;1/1:402:0,-1,0,0,0,1,0;-1/1:426:0,-2,0,0,0,0,0;-1/1:576:0,-2,0,0,0,0,0;-1/1:606:0,-2,0,0,0,0,0;1/1:634:0,0,0,0,0,0,0;1/1:696:0,-2,0,0,0,0,0;1/1:702:0,-1,0,0,0,1,0;-1/1:876:0,-2,0,0,0,0,0;1/1:936:0,-2,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:101:0,0,0,0,0,0,0;1/1:162:-2,-1,0,0,0,1,0;-1/1:606:-1,-1,0,0,1,1,0;1/1:676:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;1/1:768:-1,-2,0,0,1,0,0;-1/1:776:0,0,0,0,0,0,0;1/1:834:0,-2,0,0,0,0,0;1/1:876:0,0,0,0,0,0,0;1/1:902:-1,0,0,0,1,0,0;-1/1:926:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:264:0,-2,0,0,0,0,0;1/1:426:-2,-2,0,0,0,0,0;1/1:474:2,0,0,0,0,0,0;-1/1:702:-2,-1,0,0,0,1,0;-1/1:706:0,0,0,0,0,0,0;1/1:776:0,0,0,0,0,0,0;1/1:864:-2,0,0,0,0,0,0;1/1:876:-1,-1,0,0,1,1,0;1/1:934:-2,0,0,0,0,0,0;1/1:986:0,0,0,0,0,0,0;-1/1:992:-1,0,0,0,1,0,0"
  | 26 => laurent_polynomial% "1/1:149:0,0,0,0,0,0,0;-1/1:162:1,0,0,0,1,0,0;1/1:186:0,-2,0,0,0,0,0;-1/1:386:-2,0,0,0,0,0,0;1/1:396:0,-2,0,0,0,0,0;1/1:606:0,-2,0,0,0,0,0;1/1:606:2,0,0,0,0,0,0;1/1:648:-1,0,0,0,1,0,0;-1/1:806:-2,0,0,0,0,0,0;1/1:876:-2,0,0,0,0,0,0;1/1:998:-1,0,0,0,1,0,0;-1/1:1016:-2,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:34:-1,0,0,0,1,0,0;-1/1:52:0,0,0,0,0,0,0;-1/1:68:-2,0,0,0,0,0,0;-1/1:174:-1,0,0,0,1,0,0;1/1:227:0,0,0,0,0,0,0;1/1:244:-1,0,0,0,1,0,0;-1/1:278:-2,0,0,0,0,0,0;1/1:348:-2,0,0,0,0,0,0;-1/1:402:0,0,0,0,0,0,0;-1/1:488:-2,0,0,0,0,0,0;1/1:664:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "1/1:58:0,0,0,0,0,0,0;-1/1:174:0,-1,0,0,0,1,0;1/1:234:0,-1,0,0,0,1,0;-1/1:264:0,-1,0,0,0,1,0;1/1:348:0,0,0,0,0,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:478:0,0,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;1/1:648:0,0,0,0,0,0,0;1/1:688:0,0,0,0,0,0,0;1/1:834:0,-1,0,0,0,1,0"
  | 29 => laurent_polynomial% "1/1:68:0,0,0,0,0,0,0;1/1:278:0,0,0,0,0,0,0;1/1:297:0,-2,0,0,0,0,0;1/1:348:-1,-1,0,0,1,1,0;-1/1:348:0,0,0,0,0,0,0;1/1:396:-2,-1,0,0,0,1,0;1/1:488:0,0,0,0,0,0,0;1/1:624:0,-1,0,0,0,1,0;1/1:648:-1,-1,0,0,1,1,0;1/1:733:0,0,0,0,0,0,0;1/1:766:-1,0,0,0,1,0,0;1/1:878:-4,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:174:-1,0,0,0,1,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:216:0,-1,0,0,0,1,0;1/1:262:0,0,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;-1/1:426:0,-1,0,0,0,1,0;1/1:432:2,-2,0,0,0,0,0;1/1:474:2,-1,0,0,0,1,0;-1/1:864:1,-2,0,0,1,0,0;-1/1:888:0,-2,0,0,0,0,0;1/1:936:0,-1,0,0,0,1,0"
  | 31 => laurent_polynomial% "1/1:186:0,0,0,0,2,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:282:-2,-1,0,0,0,1,0;1/1:402:-1,0,0,0,1,0,0;1/1:411:0,0,0,0,0,0,0;-1/1:432:-2,-1,0,0,0,1,0;-1/1:432:-1,0,0,0,1,0,0;-1/1:618:1,0,0,0,1,0,0;-1/1:642:-1,0,0,0,1,0,0;1/1:702:-1,0,0,0,1,0,0;1/1:936:0,0,0,0,0,0,0;-1/1:944:-2,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart29 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "-1/1:69:0,-2,0,0,0,0,0;-1/1:348:-1,-2,0,0,1,0,0;1/1:348:0,-1,0,0,0,1,0;1/1:416:0,0,0,0,0,0,0;1/1:426:-2,-2,0,0,0,0,0;-1/1:444:0,-2,0,0,0,0,0;1/1:576:-2,-2,0,0,0,0,0;1/1:648:0,-1,0,0,0,1,0;1/1:766:0,0,0,0,0,0,0;-1/1:768:-1,-2,0,0,1,0,0;1/1:876:-2,-2,0,0,0,0,0;1/1:888:-1,-2,0,0,1,0,0"
  | 1 => laurent_polynomial% "-1/1:76:-2,0,0,0,0,0,0;1/1:216:-2,0,0,0,0,0,0;1/1:426:-4,-2,0,0,0,0,0;1/1:458:-1,0,0,0,1,0,0;-1/1:648:-2,-1,0,0,0,1,0;1/1:649:0,0,0,0,0,0,0;-1/1:706:-2,0,0,0,0,0,0;-1/1:754:0,0,0,0,0,0,0;1/1:859:0,0,0,0,0,0,0;1/1:864:-4,0,0,0,0,0,0;1/1:878:-1,0,0,0,1,0,0"
  | 2 => laurent_polynomial% "-1/1:162:-1,0,0,0,1,0,0;-1/1:174:-2,0,0,0,0,0,0;1/1:282:-1,0,0,0,1,0,0;-1/1:426:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;-1/1:624:-2,0,0,0,0,0,0;1/1:696:0,0,0,0,0,0,0;1/1:702:-1,0,0,0,1,0,0;-1/1:876:0,0,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0;1/1:981:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:162:0,-2,0,0,0,0,0;1/1:174:-1,-2,0,0,1,0,0;-1/1:348:-2,-2,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:398:0,0,0,0,0,0,0;1/1:432:0,-2,0,0,0,0,0;1/1:458:0,0,0,0,0,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:702:0,-2,0,0,0,0,0;1/1:768:0,0,0,0,0,0,0;-1/1:848:0,0,0,0,0,0,0;1/1:878:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "-1/1:282:0,0,0,0,0,0,0;1/1:332:0,0,0,0,0,0,0;-1/1:396:0,-1,0,0,0,1,0;-1/1:432:0,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;-1/1:696:0,-1,0,0,0,1,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:768:0,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:878:-2,0,0,0,0,0,0;1/1:932:0,0,0,0,0,0,0;-1/1:1016:1,0,0,0,1,0,0"
  | 5 => laurent_polynomial% "1/1:163:0,0,0,0,0,0,0;-1/1:302:-2,0,0,0,0,0,0;1/1:426:-2,-1,0,0,0,1,0;-1/1:444:0,-1,0,0,0,1,0;1/1:576:-2,-1,0,0,0,1,0;-1/1:618:-2,-2,0,0,0,0,0;1/1:676:-1,0,0,0,1,0,0;1/1:688:0,0,0,0,0,0,0;-1/1:696:-2,-1,0,0,0,1,0;1/1:834:-1,-2,0,0,1,0,0;1/1:876:-2,-1,0,0,0,1,0;1/1:888:-1,-1,0,0,1,1,0"
  | 6 => laurent_polynomial% "-1/1:174:0,0,0,0,0,0,0;1/1:244:0,0,0,0,0,0,0;-1/1:264:0,0,0,0,0,0,0;1/1:282:0,-1,0,0,0,1,0;1/1:354:0,0,0,0,0,0,0;1/1:432:0,-1,0,0,0,1,0;-1/1:444:0,0,0,0,0,0,0;-1/1:474:0,0,0,0,0,0,0;-1/1:576:2,0,0,0,0,0,0;1/1:834:0,0,0,0,0,0,0;-1/1:864:0,0,0,0,0,0,0;1/1:944:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "-1/1:62:0,0,0,0,0,0,0;1/1:162:0,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:348:-2,0,0,0,0,0,0;1/1:348:0,-2,0,0,0,0,0;1/1:396:0,-1,0,0,0,1,0;1/1:432:0,0,0,0,0,0,0;1/1:606:0,-1,0,0,0,1,0;1/1:622:0,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:878:-2,0,0,0,0,0,0;-1/1:902:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:348:0,-2,0,0,0,0,0;-1/1:408:0,-2,0,0,0,0,0;1/1:426:0,-1,0,0,0,1,0;-1/1:432:2,-2,0,0,0,0,0;1/1:562:0,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;1/1:648:0,-2,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:772:0,0,0,0,0,0,0;-1/1:842:0,0,0,0,0,0,0;1/1:864:1,-2,0,0,1,0,0;1/1:1016:1,0,0,0,1,0,0"
  | 9 => laurent_polynomial% "1/1:174:0,-1,0,0,0,1,0;1/1:264:0,-1,0,0,0,1,0;-1/1:282:0,-2,0,0,0,0,0;-1/1:348:0,0,0,0,0,0,0;-1/1:354:0,-1,0,0,0,1,0;-1/1:432:0,-2,0,0,0,0,0;1/1:444:0,-1,0,0,0,1,0;1/1:474:0,-1,0,0,0,1,0;1/1:576:2,-1,0,0,0,1,0;-1/1:648:0,0,0,0,0,0,0;-1/1:834:0,-1,0,0,0,1,0;1/1:864:0,-1,0,0,0,1,0;1/1:898:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:69:0,0,0,0,0,0,0;-1/1:174:0,0,0,0,0,0,0;-1/1:264:0,0,0,0,0,0,0;1/1:348:-1,0,0,0,1,0,0;1/1:354:0,0,0,0,0,0,0;-1/1:426:-2,0,0,0,0,0,0;-1/1:474:0,0,0,0,0,0,0;-1/1:576:-2,0,0,0,0,0,0;-1/1:576:2,0,0,0,0,0,0;1/1:768:-1,0,0,0,1,0,0;1/1:834:0,0,0,0,0,0,0;-1/1:864:0,0,0,0,0,0,0;-1/1:876:-2,0,0,0,0,0,0;-1/1:888:-1,0,0,0,1,0,0"
  | 11 => laurent_polynomial% "1/1:52:-4,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:234:-1,0,0,0,1,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:354:-2,-1,0,0,0,1,0;1/1:398:-2,0,0,0,0,0,0;-1/1:642:-2,-2,0,0,0,0,0;-1/1:642:0,0,0,0,0,0,0;-1/1:702:-1,-1,0,0,1,1,0;1/1:817:0,0,0,0,0,0,0;1/1:876:0,-1,0,0,0,1,0;-1/1:888:-2,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:992:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "-1/1:58:-2,0,0,0,0,0,0;1/1:64:-1,0,0,0,1,0,0;1/1:174:-2,-1,0,0,0,1,0;1/1:186:-3,0,0,0,1,0,0;1/1:274:-1,0,0,0,1,0,0;-1/1:408:-2,0,0,0,0,0,0;1/1:444:2,-1,0,0,0,1,0;1/1:624:-3,-2,0,0,1,0,0;1/1:694:-1,0,0,0,1,0,0;-1/1:802:0,0,0,0,0,0,0;-1/1:888:1,-1,0,0,1,1,0;-1/1:936:0,-1,0,0,0,1,0;1/1:977:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:396:0,-1,0,0,0,1,0;1/1:402:0,0,0,0,0,0,0;-1/1:426:0,-1,0,0,0,1,0;-1/1:432:0,0,0,0,0,0,0;1/1:474:2,-1,0,0,0,1,0;1/1:572:0,0,0,0,0,0,0;-1/1:576:0,-1,0,0,0,1,0;-1/1:606:0,-1,0,0,0,1,0;1/1:702:0,0,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;-1/1:876:0,-1,0,0,0,1,0;1/1:936:0,-1,0,0,0,1,0;1/1:992:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:174:-1,-2,0,0,1,0,0;1/1:186:1,-2,0,0,1,0,0;1/1:348:-2,-2,0,0,0,0,0;-1/1:348:0,0,0,0,0,0,0;-1/1:432:0,-2,0,0,0,0,0;1/1:488:0,0,0,0,0,0,0;-1/1:576:2,-1,0,0,0,1,0;-1/1:618:2,-2,0,0,0,0,0;1/1:624:0,-1,0,0,0,1,0;-1/1:642:0,-2,0,0,0,0,0;1/1:702:0,-2,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0;1/1:834:0,-1,0,0,0,1,0;1/1:838:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:52:0,0,0,0,0,0,0;-1/1:302:0,0,0,0,0,0,0;1/1:426:0,-1,0,0,0,1,0;-1/1:444:2,-1,0,0,0,1,0;1/1:576:0,-1,0,0,0,1,0;1/1:606:0,-1,0,0,0,1,0;-1/1:618:0,-2,0,0,0,0,0;-1/1:696:0,-1,0,0,0,1,0;-1/1:702:0,0,0,0,0,0,0;-1/1:768:0,-2,0,0,0,0,0;1/1:802:0,0,0,0,0,0,0;1/1:876:0,-1,0,0,0,1,0;1/1:888:1,-1,0,0,1,1,0;-1/1:902:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "-1/1:162:1,-2,0,0,1,0,0;-1/1:174:0,-2,0,0,0,0,0;-1/1:186:0,0,0,0,0,0,0;1/1:216:0,0,0,0,0,0,0;1/1:354:0,-2,0,0,0,0,0;1/1:426:0,0,0,0,0,0,0;-1/1:474:0,-2,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;1/1:576:0,0,0,0,0,0,0;1/1:606:2,-2,0,0,0,0,0;-1/1:624:0,-2,0,0,0,0,0;-1/1:646:0,0,0,0,0,0,0;1/1:888:0,-1,0,0,0,1,0;1/1:926:0,0,0,0,0,0,0;-1/1:936:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:162:1,-1,0,0,1,1,0;1/1:166:-1,0,0,0,1,0,0;1/1:174:0,-1,0,0,0,1,0;-1/1:332:-2,0,0,0,0,0,0;1/1:402:0,-2,0,0,0,0,0;-1/1:432:0,-2,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;1/1:474:0,-1,0,0,0,1,0;-1/1:606:2,-1,0,0,0,1,0;1/1:624:0,-1,0,0,0,1,0;-1/1:642:0,-2,0,0,0,0,0;1/1:702:0,-2,0,0,0,0,0;-1/1:864:1,0,0,0,1,0,0;-1/1:888:0,0,0,0,0,0,0;1/1:958:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:183:0,0,0,0,0,0,0;-1/1:186:-1,0,0,0,1,0,0;1/1:216:-1,0,0,0,1,0,0;-1/1:282:-2,0,0,0,0,0,0;-1/1:348:0,0,0,0,0,0,0;1/1:426:-1,0,0,0,1,0,0;-1/1:432:-2,0,0,0,0,0,0;-1/1:474:1,0,0,0,1,0,0;1/1:576:-1,0,0,0,1,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;1/1:876:-1,0,0,0,1,0,0;1/1:888:0,0,0,0,0,0,0;-1/1:936:-1,0,0,0,1,0,0"
  | 19 => laurent_polynomial% "-1/1:58:-1,0,0,0,1,0,0;1/1:64:0,0,0,0,0,0,0;1/1:116:-2,0,0,0,0,0,0;1/1:174:-1,-1,0,0,1,1,0;1/1:186:-2,0,0,0,0,0,0;1/1:186:0,-2,0,0,0,0,0;-1/1:216:0,-2,0,0,0,0,0;1/1:274:0,0,0,0,0,0,0;-1/1:348:-2,-1,0,0,0,1,0;-1/1:426:0,-2,0,0,0,0,0;1/1:474:2,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;1/1:624:-2,-2,0,0,0,0,0;1/1:694:0,0,0,0,0,0,0;1/1:936:0,-2,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:76:0,0,0,0,0,0,0;-1/1:282:-2,-1,0,0,0,1,0;-1/1:426:-2,-2,0,0,0,0,0;1/1:426:-1,-1,0,0,1,1,0;1/1:426:0,0,0,0,0,0,0;-1/1:474:0,-2,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;1/1:576:-1,-1,0,0,1,1,0;1/1:606:-1,-1,0,0,1,1,0;-1/1:696:-1,-1,0,0,1,1,0;1/1:706:0,0,0,0,0,0,0;1/1:753:0,-1,0,0,0,1,0;-1/1:864:-2,0,0,0,0,0,0;-1/1:934:-2,0,0,0,0,0,0;-1/1:936:-1,-1,0,0,1,1,0;-1/1:986:0,0,0,0,0,0,0;1/1:992:-1,0,0,0,1,0,0"
  | 21 => laurent_polynomial% "-1/1:62:0,0,0,0,0,0,0;1/1:216:0,-1,0,0,0,1,0;-1/1:348:0,-2,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;-1/1:474:2,-1,0,0,0,1,0;-1/1:512:0,0,0,0,0,0,0;1/1:618:0,-2,0,0,0,0,0;-1/1:648:0,-2,0,0,0,0,0;1/1:712:0,0,0,0,0,0,0;-1/1:772:0,0,0,0,0,0,0;1/1:842:0,0,0,0,0,0,0;1/1:888:0,-2,0,0,0,0,0;-1/1:936:0,-1,0,0,0,1,0;-1/1:1016:1,0,0,0,1,0,0"
  | 22 => laurent_polynomial% "-1/1:282:-2,0,0,0,0,0,0;-1/1:348:0,0,0,0,0,0,0;1/1:408:0,0,0,0,0,0,0;1/1:426:-1,0,0,0,1,0,0;1/1:432:2,0,0,0,0,0,0;1/1:576:-1,0,0,0,1,0,0;1/1:606:-1,0,0,0,1,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:648:0,0,0,0,0,0,0;-1/1:696:-1,0,0,0,1,0,0;-1/1:702:-2,0,0,0,0,0,0;1/1:753:0,0,0,0,0,0,0;-1/1:864:1,0,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:936:-1,0,0,0,1,0,0"
  | 23 => laurent_polynomial% "1/1:58:-1,0,0,0,1,0,0;-1/1:64:0,0,0,0,0,0,0;-1/1:116:-2,0,0,0,0,0,0;-1/1:174:-1,-1,0,0,1,1,0;-1/1:186:-2,0,0,0,0,0,0;1/1:186:1,-1,0,0,1,1,0;1/1:348:-2,-1,0,0,0,1,0;1/1:402:0,-1,0,0,0,1,0;-1/1:432:0,-1,0,0,0,1,0;-1/1:576:0,-2,0,0,0,0,0;-1/1:576:2,0,0,0,0,0,0;-1/1:618:2,-1,0,0,0,1,0;-1/1:624:-2,-2,0,0,0,0,0;1/1:624:0,0,0,0,0,0,0;-1/1:642:0,-1,0,0,0,1,0;-1/1:694:0,0,0,0,0,0,0;1/1:702:0,-1,0,0,0,1,0;1/1:974:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:136:0,0,0,0,0,0,0;-1/1:166:0,0,0,0,0,0,0;1/1:174:0,-2,0,0,0,0,0;1/1:234:0,-2,0,0,0,0,0;1/1:348:0,-1,0,0,0,1,0;-1/1:386:0,0,0,0,0,0,0;-1/1:408:0,-1,0,0,0,1,0;-1/1:444:2,0,0,0,0,0,0;-1/1:618:0,-1,0,0,0,1,0;1/1:702:-2,-1,0,0,0,1,0;-1/1:796:0,0,0,0,0,0,0;-1/1:876:-1,-1,0,0,1,1,0;-1/1:888:0,-1,0,0,0,1,0;1/1:888:1,0,0,0,1,0,0;1/1:936:0,0,0,0,0,0,0;-1/1:986:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:64:0,0,0,0,0,0,0;-1/1:162:1,0,0,0,1,0,0;1/1:264:0,0,0,0,0,0,0;1/1:396:0,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;-1/1:604:0,0,0,0,0,0,0;1/1:606:0,-2,0,0,0,0,0;1/1:606:2,0,0,0,0,0,0;-1/1:624:0,0,0,0,0,0,0;1/1:642:0,-1,0,0,0,1,0;1/1:664:0,0,0,0,0,0,0;-1/1:834:0,0,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0;-1/1:876:0,-2,0,0,0,0,0;1/1:884:0,0,0,0,0,0,0;-1/1:914:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;1/1:186:-2,0,0,0,0,0,0;1/1:264:0,0,0,0,0,0,0;-1/1:426:0,-2,0,0,0,0,0;1/1:444:2,-2,0,0,0,0,0;1/1:474:0,0,0,0,0,0,0;-1/1:576:0,-2,0,0,0,0,0;-1/1:606:0,-2,0,0,0,0,0;1/1:624:-2,-2,0,0,0,0,0;1/1:634:0,0,0,0,0,0,0;1/1:696:0,-2,0,0,0,0,0;-1/1:876:0,-2,0,0,0,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:1,-2,0,0,1,0,0;1/1:934:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "-1/1:58:0,0,0,0,0,0,0;1/1:174:0,-1,0,0,0,1,0;-1/1:234:0,-1,0,0,0,1,0;1/1:264:0,-1,0,0,0,1,0;-1/1:278:0,0,0,0,0,0,0;-1/1:348:0,0,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;1/1:474:0,-1,0,0,0,1,0;1/1:618:0,0,0,0,0,0,0;-1/1:688:0,0,0,0,0,0,0;1/1:702:0,-2,0,0,0,0,0;-1/1:718:0,0,0,0,0,0,0;1/1:778:0,0,0,0,0,0,0;-1/1:864:1,0,0,0,1,0,0;-1/1:878:0,0,0,0,0,0,0;1/1:998:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:174:-1,0,0,0,1,0,0;-1/1:186:1,0,0,0,1,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:297:0,0,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:402:0,0,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;1/1:444:-1,0,0,0,1,0,0;1/1:474:-1,0,0,0,1,0,0;1/1:576:1,0,0,0,1,0,0;1/1:618:2,0,0,0,0,0,0;1/1:642:0,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:834:-1,0,0,0,1,0,0;1/1:864:-1,0,0,0,1,0,0"
  | 29 => laurent_polynomial% "1/1:264:0,-2,0,0,0,0,0;1/1:386:0,0,0,0,0,0,0;1/1:396:0,0,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;1/1:576:2,-2,0,0,0,0,0;1/1:618:0,-1,0,0,0,1,0;-1/1:624:0,-2,0,0,0,0,0;1/1:646:0,0,0,0,0,0,0;1/1:768:0,-1,0,0,0,1,0;1/1:796:0,0,0,0,0,0,0;1/1:806:0,0,0,0,0,0,0;-1/1:834:0,-2,0,0,0,0,0;1/1:864:0,-2,0,0,0,0,0;-1/1:876:0,0,0,0,0,0,0;-1/1:934:-2,0,0,0,0,0,0;1/1:992:-1,0,0,0,1,0,0;1/1:1016:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "-1/1:52:-3,0,0,0,1,0,0;1/1:59:0,0,0,0,0,0,0;1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;-1/1:234:-2,-2,0,0,0,0,0;-1/1:234:0,0,0,0,0,0,0;1/1:332:-3,0,0,0,1,0,0;-1/1:348:-2,-1,0,0,0,1,0;-1/1:354:-1,-1,0,0,1,1,0;-1/1:398:-1,0,0,0,1,0,0;1/1:444:0,0,0,0,0,0,0;1/1:618:-2,-1,0,0,0,1,0;1/1:642:-1,-2,0,0,1,0,0;-1/1:702:-4,-1,0,0,0,1,0;1/1:702:0,-1,0,0,0,1,0;1/1:796:-2,0,0,0,0,0,0;1/1:876:-3,-1,0,0,1,1,0;1/1:888:-2,-1,0,0,0,1,0;-1/1:934:0,0,0,0,0,0,0;-1/1:936:-2,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:162:1,-2,0,0,1,0,0;-1/1:264:0,-2,0,0,0,0,0;1/1:282:-1,0,0,0,1,0,0;-1/1:396:0,0,0,0,0,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:474:1,-1,0,0,1,1,0;1/1:474:2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;-1/1:576:2,-2,0,0,0,0,0;-1/1:606:0,0,0,0,0,0,0;-1/1:606:2,-2,0,0,0,0,0;1/1:624:0,-2,0,0,0,0,0;1/1:642:-2,-1,0,0,0,1,0;-1/1:702:-3,-2,0,0,1,0,0;1/1:834:0,-2,0,0,0,0,0;1/1:841:0,0,0,0,0,0,0;-1/1:864:0,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;1/1:876:-2,-2,0,0,2,0,0;-1/1:914:-2,0,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0;-1/1:1016:0,0,0,0,0,0,0;1/1:1016:0,0,0,0,2,0,0"
  | _ => []

}
certificate_batch {
compact_certificate def normalPart30 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "-1/1:162:-2,-1,0,0,0,1,0;-1/1:174:-3,-1,0,0,1,1,0;-1/1:186:-2,-2,0,0,0,0,0;1/1:302:-1,0,0,0,1,0,0;1/1:348:-4,-1,0,0,0,1,0;-1/1:426:-1,-1,0,0,1,1,0;-1/1:432:-2,-1,0,0,0,1,0;1/1:444:1,-1,0,0,1,1,0;-1/1:576:-1,-1,0,0,1,1,0;-1/1:604:-2,0,0,0,0,0,0;1/1:618:-1,-2,0,0,1,0,0;-1/1:676:0,0,0,0,0,0,0;1/1:696:-1,-1,0,0,1,1,0;1/1:702:-2,-1,0,0,0,1,0;-1/1:834:0,-2,0,0,0,0,0;1/1:851:0,0,0,0,0,0,0;-1/1:876:-1,-1,0,0,1,1,0;-1/1:888:0,-1,0,0,2,1,0"
  | 1 => laurent_polynomial% "-1/1:116:0,0,0,0,0,0,0;1/1:162:1,-2,0,0,1,0,0;1/1:166:0,0,0,0,0,0,0;1/1:186:0,0,0,0,0,0,0;-1/1:216:0,0,0,0,0,0,0;-1/1:264:0,-2,0,0,0,0,0;1/1:348:0,-1,0,0,0,1,0;-1/1:426:-2,-2,0,0,0,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:474:2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;-1/1:576:2,-2,0,0,0,0,0;-1/1:606:2,-2,0,0,0,0,0;1/1:624:0,-2,0,0,0,0,0;1/1:648:0,-1,0,0,0,1,0;1/1:766:0,0,0,0,0,0,0;1/1:834:0,-2,0,0,0,0,0;-1/1:864:-2,0,0,0,0,0,0;-1/1:864:0,-2,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0;-1/1:1016:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "-1/1:52:-2,0,0,0,0,0,0;1/1:68:0,0,0,0,0,0,0;-1/1:166:-1,0,0,0,1,0,0;1/1:172:-2,0,0,0,0,0,0;1/1:174:-1,-2,0,0,1,0,0;-1/1:234:0,-1,0,0,0,1,0;1/1:282:0,-2,0,0,0,0,0;1/1:332:-2,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:398:0,0,0,0,0,0,0;1/1:432:0,-2,0,0,0,0,0;-1/1:444:0,-1,0,0,0,1,0;1/1:618:0,0,0,0,0,0,0;1/1:642:0,-2,0,0,0,0,0;-1/1:718:0,0,0,0,0,0,0;1/1:768:0,0,0,0,0,0,0;-1/1:864:0,-1,0,0,0,1,0;1/1:888:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:186:-2,-1,0,0,0,1,0;1/1:186:-1,0,0,0,1,0,0;-1/1:216:-2,-1,0,0,0,1,0;1/1:234:-1,-2,0,0,1,0,0;1/1:348:-1,-1,0,0,1,1,0;1/1:354:0,-1,0,0,0,1,0;1/1:398:0,0,0,0,0,0,0;-1/1:426:-2,-1,0,0,0,1,0;-1/1:432:-2,0,0,0,0,0,0;-1/1:444:1,0,0,0,1,0,0;1/1:474:0,-1,0,0,0,1,0;-1/1:576:-2,-1,0,0,0,1,0;-1/1:618:-1,-1,0,0,1,1,0;-1/1:618:0,0,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;-1/1:642:0,-2,0,0,0,0,0;1/1:643:0,0,0,0,0,0,0;1/1:702:-3,-1,0,0,1,1,0;1/1:702:-2,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;-1/1:876:-2,-1,0,0,2,1,0;-1/1:888:-1,-1,0,0,1,1,0;-1/1:888:0,0,0,0,0,0,0;1/1:888:0,0,0,0,2,0,0;1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0"
  | 4 => laurent_polynomial% "1/1:166:-3,0,0,0,1,0,0;-1/1:216:-1,-2,0,0,1,0,0;-1/1:234:-1,0,0,0,1,0,0;1/1:282:-1,-1,0,0,1,1,0;-1/1:332:-4,0,0,0,0,0,0;1/1:402:0,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-1/1:426:0,-1,0,0,0,1,0;-1/1:444:-1,0,0,0,1,0,0;1/1:474:1,-2,0,0,1,0,0;-1/1:576:0,-1,0,0,0,1,0;-1/1:606:0,-1,0,0,0,1,0;1/1:618:0,-2,0,0,0,0,0;1/1:677:0,0,0,0,0,0,0;1/1:696:0,-1,0,0,0,1,0;1/1:702:-1,-1,0,0,1,1,0;1/1:702:0,0,0,0,0,0,0;1/1:768:0,-2,0,0,0,0,0;-1/1:864:-1,0,0,0,1,0,0;-1/1:876:0,-1,0,0,0,1,0;1/1:936:0,-1,0,0,0,1,0"
  | 5 => laurent_polynomial% "-1/1:162:-1,-2,0,0,1,0,0;-1/1:174:-2,-2,0,0,2,0,0;1/1:216:-2,0,0,0,0,0,0;1/1:264:0,0,0,0,0,0,0;1/1:348:-3,-2,0,0,1,0,0;1/1:348:-2,-1,0,0,0,1,0;-1/1:408:-2,-1,0,0,0,1,0;1/1:426:-2,0,0,0,0,0,0;-1/1:426:0,-2,0,0,0,0,0;-1/1:432:-1,-2,0,0,1,0,0;-1/1:432:0,-1,0,0,0,1,0;1/1:444:2,-2,0,0,0,0,0;-1/1:474:-2,-2,0,0,0,0,0;-1/1:576:0,-2,0,0,0,0,0;-1/1:618:-2,-1,0,0,0,1,0;-1/1:618:-1,0,0,0,1,0,0;1/1:696:0,-2,0,0,0,0,0;1/1:702:-4,-1,0,0,0,1,0;1/1:702:-1,-2,0,0,1,0,0;-1/1:768:-1,0,0,0,1,0,0;1/1:859:0,0,0,0,0,0,0;1/1:864:-1,-1,0,0,1,1,0;-1/1:876:-3,-1,0,0,1,1,0;-1/1:876:0,-2,0,0,0,0,0;-1/1:888:1,-2,0,0,1,0,0;-1/1:986:-2,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "-1/1:162:0,-1,0,0,2,1,0;-1/1:174:-1,-1,0,0,1,1,0;1/1:234:0,0,0,0,0,0,0;1/1:348:-2,-1,0,0,0,1,0;1/1:354:-1,-1,0,0,1,1,0;1/1:398:-1,0,0,0,1,0,0;1/1:426:0,-2,0,0,0,0,0;1/1:432:-1,-2,0,0,1,0,0;-1/1:474:-1,-1,0,0,1,1,0;1/1:606:1,-1,0,0,1,1,0;-1/1:618:-2,-1,0,0,0,1,0;-1/1:624:-1,-1,0,0,1,1,0;1/1:702:-4,-1,0,0,0,1,0;-1/1:702:0,-1,0,0,0,1,0;-1/1:794:0,0,0,0,0,0,0;-1/1:796:-2,0,0,0,0,0,0;-1/1:864:-2,-2,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0;-1/1:876:-3,-1,0,0,1,1,0;-1/1:888:-2,-1,0,0,0,1,0;1/1:899:0,0,0,0,0,0,0;1/1:934:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:162:0,0,0,0,0,0,0;1/1:282:0,0,0,0,0,0,0;1/1:302:0,0,0,0,0,0,0;-1/1:332:0,0,0,0,0,0,0;1/1:396:0,-1,0,0,0,1,0;1/1:408:0,-2,0,0,0,0,0;-1/1:426:0,-1,0,0,0,1,0;1/1:432:0,0,0,0,0,0,0;1/1:444:2,-1,0,0,0,1,0;1/1:512:0,0,0,0,0,0,0;-1/1:576:0,-1,0,0,0,1,0;2/1:618:0,-2,0,0,0,0,0;1/1:696:0,-1,0,0,0,1,0;-1/1:702:-2,-2,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:768:0,-2,0,0,0,0,0;1/1:876:-1,-2,0,0,1,0,0;-1/1:876:0,-1,0,0,0,1,0;1/1:878:-2,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:1,-1,0,0,1,1,0;1/1:1016:1,0,0,0,1,0,0"
  | 8 => laurent_polynomial% "1/1:116:-2,0,0,0,0,0,0;-1/1:234:-2,-2,0,0,0,0,0;1/1:264:-2,-2,0,0,0,0,0;1/1:278:-1,0,0,0,1,0,0;-1/1:348:-2,-1,0,0,0,1,0;1/1:386:-2,0,0,0,0,0,0;1/1:402:-1,-2,0,0,1,0,0;-1/1:444:-2,-2,0,0,0,0,0;1/1:444:0,0,0,0,0,0,0;1/1:444:2,-2,0,0,0,0,0;-1/1:474:0,0,0,0,0,0,0;1/1:618:-2,-1,0,0,0,1,0;1/1:646:-2,0,0,0,0,0,0;-1/1:664:0,0,0,0,0,0,0;-1/1:676:-2,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:796:-2,0,0,0,0,0,0;-1/1:834:-2,-2,0,0,0,0,0;-1/1:834:-1,-1,0,0,1,1,0;1/1:839:0,0,0,0,0,0,0;-1/1:876:-2,0,0,0,0,0,0;-1/1:888:-1,0,0,0,1,0,0;-1/1:888:1,-2,0,0,1,0,0;-1/1:934:-4,0,0,0,0,0,0;-1/1:936:-2,0,0,0,0,0,0;1/1:992:-3,0,0,0,1,0,0;1/1:1016:-2,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "-1/1:52:0,0,0,0,0,0,0;1/1:62:0,0,0,0,0,0,0;-1/1:162:0,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-1/1:174:-1,0,0,0,1,0,0;1/1:186:1,0,0,0,1,0,0;-1/1:216:0,-1,0,0,0,1,0;1/1:332:0,0,0,0,0,0,0;1/1:348:-2,0,0,0,0,0,0;-1/1:348:0,-2,0,0,0,0,0;-1/1:396:0,-1,0,0,0,1,0;-1/1:426:0,-1,0,0,0,1,0;-2/1:432:0,0,0,0,0,0,0;1/1:474:2,-1,0,0,0,1,0;-1/1:576:0,-1,0,0,0,1,0;-1/1:606:0,-1,0,0,0,1,0;-1/1:618:2,0,0,0,0,0,0;2/1:702:0,0,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;1/1:772:0,0,0,0,0,0,0;-1/1:876:0,-1,0,0,0,1,0;-1/1:878:-2,0,0,0,0,0,0;1/1:902:0,0,0,0,0,0,0;1/1:936:0,-1,0,0,0,1,0;1/1:992:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:174:0,0,0,0,0,0,0;-1/1:244:0,0,0,0,0,0,0;1/1:264:0,0,0,0,0,0,0;1/1:282:-1,-2,0,0,1,0,0;-1/1:282:0,-1,0,0,0,1,0;1/1:402:0,-1,0,0,0,1,0;-1/1:426:0,-2,0,0,0,0,0;-1/1:432:0,-1,0,0,0,1,0;-1/1:444:-1,-1,0,0,1,1,0;1/1:444:0,0,0,0,0,0,0;1/1:474:0,0,0,0,0,0,0;-1/1:576:0,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;1/1:599:0,0,0,0,0,0,0;-1/1:606:0,-2,0,0,0,0,0;1/1:634:0,0,0,0,0,0,0;-1/1:646:-2,0,0,0,0,0,0;-1/1:694:0,0,0,0,0,0,0;1/1:702:0,-1,0,0,0,1,0;1/1:794:0,0,0,0,0,0,0;-1/1:834:0,0,0,0,0,0,0;1/1:848:-1,0,0,0,1,0,0;1/1:864:0,0,0,0,0,0,0;-1/1:876:0,-2,0,0,0,0,0;1/1:888:-2,-1,0,0,0,1,0;-1/1:914:0,0,0,0,0,0,0;1/1:936:0,-2,0,0,0,0,0"
  | 11 => laurent_polynomial% "-1/1:162:-1,0,0,0,1,0,0;-1/1:162:1,-2,0,0,1,0,0;-1/1:174:-3,-1,0,0,1,1,0;-1/1:174:0,-2,0,0,0,0,0;1/1:186:-1,-1,0,0,1,1,0;-1/1:186:0,0,0,0,0,0,0;1/1:191:0,0,0,0,0,0,0;1/1:216:0,0,0,0,0,0,0;1/1:264:-2,0,0,0,0,0,0;-1/1:282:-1,0,0,0,1,0,0;1/1:348:-4,-1,0,0,0,1,0;1/1:348:-1,-2,0,0,1,0,0;1/1:354:0,-2,0,0,0,0,0;1/1:396:-2,-2,0,0,0,0,0;1/1:426:0,0,0,0,0,0,0;-1/1:432:-2,-1,0,0,0,1,0;-1/1:432:-1,0,0,0,1,0,0;-1/1:474:0,-2,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;1/1:576:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;1/1:606:-2,-2,0,0,0,0,0;1/1:606:0,0,0,0,0,0,0;1/1:606:2,-2,0,0,0,0,0;-1/1:618:-1,-2,0,0,1,0,0;-1/1:618:0,-1,0,0,0,1,0;-1/1:624:0,-2,0,0,0,0,0;1/1:664:-2,0,0,0,0,0,0;1/1:702:-3,-2,0,0,1,0,0;1/1:702:-2,-1,0,0,0,1,0;1/1:864:-2,0,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,2,0,0;1/1:884:-2,0,0,0,0,0,0;-1/1:888:-1,-2,0,0,1,0,0;-1/1:914:-2,0,0,0,0,0,0;-1/1:936:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:52:-2,0,0,0,0,0,0;1/1:58:0,0,0,0,0,0,0;1/1:162:0,-2,0,0,0,0,0;-1/1:172:-2,0,0,0,0,0,0;1/1:174:-1,-2,0,0,1,0,0;-1/1:174:0,-1,0,0,0,1,0;1/1:234:0,-1,0,0,0,1,0;1/1:278:0,0,0,0,0,0,0;-1/1:282:0,-2,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;2/1:348:0,0,0,0,0,0,0;1/1:432:0,-2,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;1/1:444:0,-1,0,0,0,1,0;-1/1:474:0,-1,0,0,0,1,0;1/1:576:2,-1,0,0,0,1,0;-1/1:618:0,0,0,0,0,0,0;-1/1:624:0,-1,0,0,0,1,0;1/1:702:-2,0,0,0,0,0,0;-2/1:702:0,-2,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;1/1:768:0,0,0,0,0,0,0;-1/1:834:0,-1,0,0,0,1,0;-1/1:838:0,0,0,0,0,0,0;-1/1:848:0,0,0,0,0,0,0;1/1:864:0,-1,0,0,0,1,0;1/1:864:1,0,0,0,1,0,0;-1/1:876:-1,0,0,0,1,0,0;1/1:878:0,0,0,0,0,0,0;-1/1:888:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:58:-1,0,0,0,1,0,0;1/1:116:-2,0,0,0,0,0,0;1/1:174:-1,-1,0,0,1,1,0;1/1:174:0,0,0,0,0,0,0;1/1:186:-2,0,0,0,0,0,0;1/1:186:0,-2,0,0,0,0,0;1/1:234:0,0,0,0,0,0,0;-1/1:244:0,0,0,0,0,0,0;1/1:264:0,0,0,0,0,0,0;-1/1:282:0,-1,0,0,0,1,0;-1/1:348:-2,-1,0,0,0,1,0;-1/1:426:0,-2,0,0,0,0,0;1/1:444:0,0,0,0,0,0,0;1/1:444:2,-2,0,0,0,0,0;1/1:474:0,0,0,0,0,0,0;-1/1:576:0,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;-1/1:606:0,-2,0,0,0,0,0;1/1:624:-2,-2,0,0,0,0,0;1/1:634:0,0,0,0,0,0,0;-1/1:664:0,0,0,0,0,0,0;1/1:696:0,-2,0,0,0,0,0;-1/1:702:0,-1,0,0,0,1,0;1/1:754:0,0,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0;-1/1:876:0,-2,0,0,0,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:1,-2,0,0,1,0,0;1/1:934:0,0,0,0,0,0,0;1/1:936:0,-2,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:162:1,0,0,0,1,0,0;1/1:264:-2,-2,0,0,0,0,0;1/1:264:-1,-1,0,0,1,1,0;1/1:264:0,0,0,0,0,0,0;1/1:289:0,0,0,0,0,0,0;-1/1:348:-1,0,0,0,1,0,0;1/1:386:-2,0,0,0,0,0,0;1/1:396:-2,0,0,0,0,0,0;1/1:396:0,-2,0,0,0,0,0;1/1:408:-1,0,0,0,1,0,0;1/1:426:-2,0,0,0,0,0,0;1/1:432:1,0,0,0,1,0,0;1/1:474:-1,-1,0,0,1,1,0;-1/1:474:0,0,0,0,0,0,0;1/1:576:-2,0,0,0,0,0,0;1/1:576:0,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;-1/1:604:0,0,0,0,0,0,0;1/1:606:-2,0,0,0,0,0,0;1/1:606:0,-2,0,0,0,0,0;1/1:606:2,0,0,0,0,0,0;1/1:618:-1,0,0,0,1,0,0;-1/1:624:-2,-2,0,0,0,0,0;-1/1:624:0,0,0,0,0,0,0;1/1:646:-2,0,0,0,0,0,0;-1/1:696:-2,0,0,0,0,0,0;-1/1:718:-1,0,0,0,1,0,0;1/1:796:-2,0,0,0,0,0,0;-1/1:834:-2,-2,0,0,0,0,0;-1/1:834:0,0,0,0,0,0,0;1/1:864:-2,-2,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0;-1/1:864:0,0,0,0,2,0,0;1/1:884:0,0,0,0,0,0,0;-1/1:934:-4,0,0,0,0,0,0;-1/1:936:-2,0,0,0,0,0,0;1/1:992:-3,0,0,0,1,0,0;1/1:998:-1,0,0,0,1,0,0;1/1:1016:-2,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "-1/1:62:-2,0,0,0,0,0,0;1/1:103:0,0,0,0,0,0,0;-1/1:116:-1,0,0,0,1,0,0;1/1:162:-2,0,0,0,0,0,0;1/1:174:-3,0,0,0,1,0,0;1/1:186:-2,-1,0,0,0,1,0;1/1:234:-1,-2,0,0,1,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:278:0,0,0,0,0,0,0;-1/1:348:-4,0,0,0,0,0,0;1/1:348:-1,-1,0,0,1,1,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:402:0,-2,0,0,0,0,0;1/1:432:-2,0,0,0,0,0,0;1/1:444:-1,-2,0,0,1,0,0;-1/1:444:1,0,0,0,1,0,0;1/1:474:1,0,0,0,1,0,0;-1/1:618:-1,-1,0,0,1,1,0;-1/1:646:-1,0,0,0,1,0,0;1/1:676:-1,0,0,0,1,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:706:-1,0,0,0,1,0,0;-1/1:796:-1,0,0,0,1,0,0;1/1:834:-1,-2,0,0,1,0,0;1/1:834:0,-1,0,0,0,1,0;1/1:876:-1,0,0,0,1,0,0;1/1:888:0,0,0,0,2,0,0;1/1:934:-3,0,0,0,1,0,0;1/1:936:-1,0,0,0,1,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:1016:-1,0,0,0,1,0,0"
  | 16 => laurent_polynomial% "-1/1:62:0,0,0,0,0,0,0;-1/1:162:0,0,0,0,2,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:282:-1,-1,0,0,1,1,0;1/1:282:0,0,0,0,0,0,0;-1/1:348:0,-2,0,0,0,0,0;1/1:396:-1,-2,0,0,1,0,0;1/1:432:0,0,0,0,0,0,0;1/1:444:-1,0,0,0,1,0,0;-1/1:474:1,-2,0,0,1,0,0;-1/1:512:0,0,0,0,0,0,0;1/1:576:1,0,0,0,1,0,0;1/1:606:1,0,0,0,1,0,0;1/1:618:0,-2,0,0,0,0,0;-1/1:624:-1,0,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;1/1:642:-1,-1,0,0,1,1,0;-1/1:694:-1,0,0,0,1,0,0;-1/1:702:-2,-2,0,0,0,0,0;1/1:712:0,0,0,0,0,0,0;1/1:737:0,0,0,0,0,0,0;1/1:794:-1,0,0,0,1,0,0;-1/1:834:-1,0,0,0,1,0,0;1/1:848:-2,0,0,0,0,0,0;1/1:864:-1,0,0,0,1,0,0;1/1:888:0,-2,0,0,0,0,0;-1/1:914:-1,0,0,0,1,0,0;-1/1:936:0,-1,0,0,0,1,0"
  | 17 => laurent_polynomial% "1/1:53:0,0,0,0,0,0,0;-1/1:62:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;1/1:282:-2,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:396:-1,0,0,0,1,0,0;-1/1:408:0,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;1/1:432:-2,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:474:1,0,0,0,1,0,0;-1/1:512:-2,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:1,-2,0,0,1,0,0;-1/1:606:-1,0,0,0,1,0,0;1/1:618:-2,-2,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;1/1:624:-1,-2,0,0,1,0,0;-1/1:646:-1,0,0,0,1,0,0;1/1:696:-1,0,0,0,1,0,0;-1/1:702:-4,-2,0,0,0,0,0;1/1:712:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;1/1:876:-3,-2,0,0,1,0,0;1/1:888:-2,-2,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0"
  | 18 => laurent_polynomial% "1/1:62:-1,0,0,0,1,0,0;1/1:162:-1,0,0,0,1,0,0;1/1:244:-2,0,0,0,0,0,0;-1/1:264:-2,0,0,0,0,0,0;1/1:264:0,-2,0,0,0,0,0;1/1:282:-2,-1,0,0,0,1,0;-1/1:282:-1,0,0,0,1,0,0;1/1:348:-1,-2,0,0,1,0,0;1/1:386:0,0,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;1/1:396:0,0,0,0,0,0,0;1/1:426:0,0,0,0,0,0,0;-1/1:432:-1,0,0,0,1,0,0;-1/1:444:-2,0,0,0,0,0,0;1/1:474:0,-2,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;1/1:512:-1,0,0,0,1,0,0;1/1:576:2,-2,0,0,0,0,0;-1/1:618:-1,-2,0,0,1,0,0;1/1:624:-2,0,0,0,0,0,0;-1/1:624:0,-2,0,0,0,0,0;1/1:631:0,0,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;-1/1:642:-2,-1,0,0,0,1,0;1/1:646:0,0,0,0,0,0,0;1/1:694:-2,0,0,0,0,0,0;-1/1:696:0,0,0,0,0,0,0;1/1:702:-3,-2,0,0,1,0,0;-1/1:712:-1,0,0,0,1,0,0;-1/1:794:-2,0,0,0,0,0,0;1/1:796:0,0,0,0,0,0,0;1/1:834:-2,0,0,0,0,0,0;-1/1:834:0,-2,0,0,0,0,0;-1/1:864:-2,0,0,0,0,0,0;1/1:864:0,-2,0,0,0,0,0;1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,2,0,0;-1/1:888:-1,-2,0,0,1,0,0;1/1:914:-2,0,0,0,0,0,0;-1/1:934:-2,0,0,0,0,0,0;1/1:936:-1,-1,0,0,1,1,0;-1/1:936:0,0,0,0,0,0,0;1/1:992:-1,0,0,0,1,0,0;1/1:1016:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:58:-3,0,0,0,1,0,0;1/1:62:-1,0,0,0,1,0,0;-1/1:116:-4,0,0,0,0,0,0;1/1:116:0,0,0,0,0,0,0;-1/1:162:-1,0,0,0,1,0,0;-1/1:174:-3,-1,0,0,1,1,0;-1/1:174:-2,0,0,0,0,0,0;-1/1:174:-2,0,0,0,2,0,0;-1/1:186:-4,0,0,0,0,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:234:-2,0,0,0,0,0,0;-1/1:234:0,-2,0,0,0,0,0;1/1:244:-2,0,0,0,0,0,0;1/1:264:0,-2,0,0,0,0,0;1/1:282:-2,-1,0,0,0,1,0;1/1:348:-4,-1,0,0,0,1,0;1/1:348:-3,0,0,0,1,0,0;-1/1:348:0,-1,0,0,0,1,0;1/1:386:0,0,0,0,0,0,0;-1/1:432:-1,0,0,0,1,0,0;-1/1:444:-2,0,0,0,0,0,0;-1/1:444:0,-2,0,0,0,0,0;1/1:444:2,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;1/1:606:-2,-2,0,0,0,0,0;-1/1:624:-4,-2,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;1/1:646:0,0,0,0,0,0,0;1/1:664:-2,0,0,0,0,0,0;-1/1:676:0,0,0,0,0,0,0;1/1:702:-2,-1,0,0,0,1,0;1/1:702:-1,0,0,0,1,0,0;1/1:706:0,0,0,0,0,0,0;1/1:731:0,0,0,0,0,0,0;1/1:796:0,0,0,0,0,0,0;-1/1:834:0,-2,0,0,0,0,0;-1/1:864:-2,0,0,0,0,0,0;-1/1:876:0,0,0,0,0,0,0;1/1:884:-2,0,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0;-2/1:934:-2,0,0,0,0,0,0;-1/1:936:-2,-2,0,0,0,0,0;-1/1:936:0,0,0,0,0,0,0;1/1:992:-1,0,0,0,1,0,0;1/1:1016:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:186:-3,0,0,0,1,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:278:-2,0,0,0,0,0,0;-1/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;1/1:398:-2,0,0,0,0,0,0;1/1:402:-2,-2,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-1/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;1/1:577:0,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:618:-2,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:642:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;1/1:696:-1,-2,0,0,1,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:838:-2,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0"
  | 21 => laurent_polynomial% "-1/1:52:-3,0,0,0,1,0,0;-1/1:116:-2,0,0,0,0,0,0;1/1:162:-1,-2,0,0,1,0,0;1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;1/1:172:-3,0,0,0,1,0,0;1/1:174:-2,-2,0,0,0,0,0;-1/1:174:0,0,0,0,0,0,0;-1/1:216:-2,0,0,0,0,0,0;-1/1:234:-1,-1,0,0,1,1,0;-1/1:234:0,0,0,0,0,0,0;1/1:244:0,0,0,0,0,0,0;-1/1:264:0,0,0,0,0,0,0;-1/1:278:-1,0,0,0,1,0,0;1/1:282:-1,-2,0,0,1,0,0;1/1:282:0,-1,0,0,0,1,0;1/1:332:-3,0,0,0,1,0,0;-1/1:354:-2,-2,0,0,0,0,0;1/1:354:0,0,0,0,0,0,0;-1/1:398:-1,0,0,0,1,0,0;-1/1:402:-1,-2,0,0,1,0,0;-1/1:426:-4,-2,0,0,0,0,0;-1/1:426:-2,0,0,0,0,0,0;1/1:426:0,-2,0,0,0,0,0;1/1:432:-1,-2,0,0,1,0,0;1/1:432:0,-1,0,0,0,1,0;1/1:444:-2,-2,0,0,0,0,0;-1/1:444:-1,-1,0,0,1,1,0;-1/1:444:0,0,0,0,0,0,0;-1/1:444:2,-2,0,0,0,0,0;1/1:474:-2,-2,0,0,0,0,0;-1/1:576:-2,0,0,0,0,0,0;1/1:576:0,-2,0,0,0,0,0;-1/1:576:1,-1,0,0,1,1,0;-1/1:576:2,0,0,0,0,0,0;1/1:618:-1,0,0,0,1,0,0;1/1:629:0,0,0,0,0,0,0;-1/1:634:0,0,0,0,0,0,0;1/1:642:-1,-2,0,0,1,0,0;1/1:664:0,0,0,0,0,0,0;-1/1:696:0,-2,0,0,0,0,0;-1/1:718:-1,0,0,0,1,0,0;1/1:834:-1,-1,0,0,1,1,0;1/1:838:-1,0,0,0,1,0,0;-1/1:864:-4,0,0,0,0,0,0;-1/1:864:-1,-1,0,0,1,1,0;-1/1:864:0,0,0,0,0,0,0;1/1:876:0,-2,0,0,0,0,0;1/1:884:0,0,0,0,0,0,0;1/1:888:-1,0,0,0,1,0,0;1/1:888:1,-2,0,0,1,0,0;-1/1:934:0,0,0,0,0,0,0;1/1:936:-2,0,0,0,0,0,0;-1/1:936:0,-2,0,0,0,0,0;-1/1:1016:-2,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:52:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:58:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:62:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:116:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:162:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:166:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:172:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:174:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:186:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:216:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def normalPart31 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:234:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:244:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:264:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:278:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:282:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:332:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:348:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:354:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:365:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:386:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:396:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:398:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:402:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:408:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:410:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:426:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:432:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:444:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:474:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:512:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:576:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:580:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:604:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:606:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:618:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:624:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:634:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:642:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:646:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:648:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:664:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:676:0,0,0,0,0,0,0"
  | _ => []

compact_certificate def normalPart32 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:688:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:694:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:696:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:702:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:706:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:712:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:718:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:768:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:794:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:796:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:810:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:834:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:838:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:848:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:864:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:876:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:884:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:888:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:902:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:914:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:934:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:936:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:986:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:992:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:998:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:1016:0,0,0,0,0,0,0"
  | _ => []

end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentOperationsTablesBundleV4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate def operationsPart0 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:24:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:49:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:13:0,0,0,0,0,0,0;1/1:4601:-2,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:28:0,0,0,0,0,0,0;1/1:4602:2,-2,0,-2,0,0,0"
  | 4 => laurent_polynomial% "1/1:50:0,0,0,0,0,0,0;-1/1:4601:-2,-2,-2,-2,0,0,0"
  | 5 => laurent_polynomial% "1/1:51:0,0,0,0,0,0,0;-1/1:4601:0,-2,-2,-2,0,0,0"
  | 6 => laurent_polynomial% "1/1:52:0,0,0,0,0,0,0;-1/1:4601:-2,0,-2,-2,0,0,0"
  | 7 => laurent_polynomial% "1/1:53:0,0,0,0,0,0,0;-1/1:4602:2,-2,-2,-2,0,0,0"
  | 8 => laurent_polynomial% "1/1:55:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,-2,0,0,0"
  | 9 => laurent_polynomial% "1/1:56:0,0,0,0,0,0,0;-1/1:4601:-2,-2,-2,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:59:0,0,0,0,0,0,0;-1/1:4602:2,0,-2,-2,0,0,0"
  | 11 => laurent_polynomial% "1/1:60:0,0,0,0,0,0,0;-1/1:4601:0,-2,-2,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:14:0,0,0,0,0,0,0;1/1:4611:0,2,0,-2,0,0,0"
  | 13 => laurent_polynomial% "1/1:64:0,0,0,0,0,0,0;-1/1:4601:-2,0,-2,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:66:0,0,0,0,0,0,0;-1/1:4602:2,-2,-2,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:70:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:15:0,0,0,0,0,0,0;1/1:4615:0,-2,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:78:0,0,0,0,0,0,0;-1/1:4602:2,0,-2,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:26:0,0,0,0,0,0,0;1/1:4617:0,-2,0,-2,0,0,0"
  | 19 => laurent_polynomial% "1/1:102:2,0,-2,0,0,0,0;-1/1:4602:2,0,-2,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:116:0,0,0,0,0,0,0;-1/1:4602:0,0,-2,-2,0,0,0"
  | 21 => laurent_polynomial% "1/1:126:0,0,0,0,0,0,0;1/1:4619:-2,0,0,-2,0,0,0"
  | 22 => laurent_polynomial% "-1/1:148:0,2,0,0,0,0,0;1/1:4616:0,2,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:10:0,0,0,0,0,0,0;1/1:4622:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:21:0,0,0,0,0,0,0;1/1:4623:-2,0,0,-2,0,0,0"
  | 25 => laurent_polynomial% "-1/1:141:0,-2,0,0,0,0,0;1/1:4623:0,-2,0,0,0,0,0"
  | 26 => laurent_polynomial% "-1/1:150:-2,0,0,0,0,0,0;1/1:4600:-2,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:12:0,0,0,0,0,0,0;1/1:4626:2,-2,0,0,0,0,0"
  | 28 => laurent_polynomial% "-1/1:154:-2,0,0,-2,0,0,0;1/1:4622:-2,0,0,-2,0,0,0"
  | 29 => laurent_polynomial% "1/1:181:0,0,0,0,0,0,0;1/1:4617:-2,0,0,-2,0,0,0"
  | 30 => laurent_polynomial% "1/1:243:0,0,0,0,0,0,0;-1/1:4619:0,-2,2,-2,0,0,0"
  | 31 => laurent_polynomial% "1/1:249:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,-2,0,0,0"
  | _ => []
compact_certificate def operationsPart1 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "-1/1:142:-2,-2,0,2,0,0,0;1/1:4631:-2,-2,0,2,0,0,0"
  | 1 => laurent_polynomial% "1/1:250:0,0,0,0,0,0,0;-1/1:4601:0,-2,-2,-2,0,0,0"
  | 2 => laurent_polynomial% "1/1:252:0,0,0,0,0,0,0;-1/1:4601:0,-2,-2,-2,0,0,0"
  | 3 => laurent_polynomial% "1/1:286:2,-2,-2,0,0,0,0;-1/1:4602:2,-2,-2,0,0,0,0"
  | 4 => laurent_polynomial% "-1/1:291:0,2,0,-2,0,0,0;1/1:4635:0,2,0,-2,0,0,0"
  | 5 => laurent_polynomial% "-1/1:311:-2,0,0,-2,0,0,0;1/1:4615:-2,0,0,-2,0,0,0"
  | 6 => laurent_polynomial% "-1/1:314:0,0,0,0,0,0,0;1/1:4624:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "-1/1:364:0,-2,0,-2,0,0,0;1/1:4619:0,-2,0,-2,0,0,0"
  | 8 => laurent_polynomial% "1/1:397:0,0,0,0,0,0,0;1/1:4600:-2,0,0,-2,0,0,0"
  | 9 => laurent_polynomial% "1/1:715:0,0,0,0,0,0,0;1/1:4632:2,2,0,-2,0,0,0"
  | 10 => laurent_polynomial% "1/1:816:0,0,0,0,0,0,0;-1/1:4602:2,-2,-2,-2,0,0,0"
  | 11 => laurent_polynomial% "1/1:817:0,0,0,0,0,0,0;-1/1:4601:-2,0,-2,-2,0,0,0"
  | 12 => laurent_polynomial% "1/1:818:0,0,0,0,0,0,0;-1/1:4601:0,-2,-2,-2,0,0,0"
  | 13 => laurent_polynomial% "1/1:819:0,0,0,0,0,0,0;-1/1:4601:-2,-2,-2,-2,0,0,0"
  | 14 => laurent_polynomial% "1/1:4455:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:68:2,2,0,0,0,0,0;-1/1:4646:2,2,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:33:0,0,0,0,0,0,0;1/1:4647:0,-2,0,0,0,0,0"
  | 17 => laurent_polynomial% "-1/1:47:0,0,0,-2,0,0,0;1/1:4647:0,0,0,-2,0,0,0"
  | 18 => laurent_polynomial% "1/1:58:0,0,0,0,0,0,0;-1/1:4647:0,-2,0,-2,0,0,0"
  | 19 => laurent_polynomial% "1/1:79:0,0,0,0,0,0,0;-1/1:4648:0,2,0,-2,0,0,0"
  | 20 => laurent_polynomial% "1/1:90:0,0,0,0,0,0,0;-1/1:4647:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:19:0,0,0,0,0,0,0;1/1:4652:0,0,0,-2,0,0,0"
  | 22 => laurent_polynomial% "1/1:61:0,0,0,0,0,0,0;-1/1:4652:-2,0,0,-2,0,0,0"
  | 23 => laurent_polynomial% "1/1:101:0,0,0,0,0,0,0;-1/1:4649:0,-2,0,2,0,0,0"
  | 24 => laurent_polynomial% "1/1:115:0,0,0,0,0,0,0;-1/1:4646:0,0,0,-2,0,0,0"
  | 25 => laurent_polynomial% "-1/1:138:0,-2,0,-2,0,0,0;1/1:4647:0,-2,0,-2,0,0,0"
  | 26 => laurent_polynomial% "-1/1:140:-2,2,0,-2,0,0,0;1/1:4655:-2,2,0,-2,0,0,0"
  | 27 => laurent_polynomial% "1/1:183:0,0,0,0,0,0,0;1/1:4652:-2,-2,0,-2,0,0,0"
  | 28 => laurent_polynomial% "1/1:203:-2,-2,0,2,0,0,0;-1/1:4653:-2,-2,0,2,0,0,0"
  | 29 => laurent_polynomial% "1/1:11:0,0,0,0,0,0,0;1/1:4660:2,2,0,-2,0,0,0"
  | 30 => laurent_polynomial% "-1/1:313:0,-2,0,0,0,0,0;1/1:4653:0,-2,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:811:0,0,0,0,0,0,0;-1/1:4652:0,-2,0,-2,0,0,0"
  | _ => []
compact_certificate def operationsPart2 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:4457:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:72:2,2,2,-2,0,0,0;-1/1:4664:2,2,2,-2,0,0,0"
  | 2 => laurent_polynomial% "1/1:86:0,0,-2,2,0,0,0;-1/1:4665:0,0,-2,2,0,0,0"
  | 3 => laurent_polynomial% "1/1:332:0,0,0,0,0,0,0;1/1:4666:-2,-2,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:298:0,0,0,0,0,0,0;1/1:4667:2,0,0,-2,0,0,0"
  | 5 => laurent_polynomial% "1/1:701:0,0,0,0,0,0,0;1/1:4666:-2,-2,0,-2,0,0,0"
  | 6 => laurent_polynomial% "1/1:4458:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "-1/1:130:0,2,0,-2,0,0,0;1/1:4670:0,2,0,-2,0,0,0"
  | 8 => laurent_polynomial% "1/1:297:0,0,0,0,0,0,0;1/1:4670:-2,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:308:0,0,0,0,0,0,0;1/1:4671:-2,0,0,2,0,0,0"
  | 10 => laurent_polynomial% "-1/1:35:2,0,0,0,0,0,0;1/1:4673:2,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:107:0,-2,2,-2,0,0,0;-1/1:4674:0,-2,2,-2,0,0,0"
  | 12 => laurent_polynomial% "-1/1:152:-2,-2,0,-2,0,0,0;1/1:4674:-2,-2,0,-2,0,0,0"
  | 13 => laurent_polynomial% "1/1:185:0,0,0,0,0,0,0;1/1:4674:-2,-2,0,-2,0,0,0"
  | 14 => laurent_polynomial% "1/1:302:0,0,0,0,0,0,0;1/1:4674:-2,0,0,-2,0,0,0"
  | 15 => laurent_polynomial% "1/1:368:0,0,0,0,0,0,0;1/1:4674:0,-2,0,-2,0,0,0"
  | 16 => laurent_polynomial% "1/1:3221:0,0,0,0,0,0,0;-1/1:4608:0,0,0,0,0,0,0;1/1:4610:-1,0,0,0,1,0,0;-1/1:4671:-2,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "-1/1:147:2,-2,0,2,0,0,0;1/1:4680:2,-2,0,2,0,0,0"
  | 18 => laurent_polynomial% "1/1:8:0,0,0,0,0,0,0;1/1:4681:-2,2,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:355:0,0,0,0,0,0,0;1/1:4682:2,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:18:0,0,0,0,0,0,0;1/1:4683:-2,-2,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:73:0,0,0,0,0,0,0;-1/1:4683:0,-2,2,-2,0,0,0"
  | 22 => laurent_polynomial% "-1/1:149:2,2,0,-2,0,0,0;1/1:4684:2,2,0,-2,0,0,0"
  | 23 => laurent_polynomial% "1/1:337:0,0,0,0,0,0,0;1/1:4683:-2,-2,0,-2,0,0,0"
  | 24 => laurent_polynomial% "-1/1:470:2,-2,0,-2,0,0,0;1/1:4682:2,-2,0,-2,0,0,0"
  | 25 => laurent_polynomial% "1/1:3796:0,0,0,0,0,0,0;-1/1:4623:0,-2,0,0,0,0,0;-1/1:4666:0,0,0,0,0,0,0;-1/1:4670:0,0,0,0,0,0,0;1/1:4683:0,-1,0,0,0,1,0"
  | 26 => laurent_polynomial% "1/1:348:0,0,0,0,0,0,0;1/1:4689:0,2,0,-2,0,0,0"
  | 27 => laurent_polynomial% "1/1:4459:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:16:0,0,0,0,0,0,0;1/1:4691:2,0,0,-2,0,0,0"
  | 29 => laurent_polynomial% "1/1:75:2,-2,2,0,0,0,0;-1/1:4691:2,-2,2,0,0,0,0"
  | 30 => laurent_polynomial% "-1/1:3:-2,2,0,-2,0,0,0;1/1:4693:-2,2,0,-2,0,0,0"
  | 31 => laurent_polynomial% "1/1:57:0,0,0,0,0,0,0;-1/1:4693:-2,2,-2,-2,0,0,0"
  | _ => []
compact_certificate def operationsPart3 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:97:0,2,-2,0,0,0,0;-1/1:4693:0,2,-2,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:38:0,0,0,0,0,0,0;1/1:4696:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:117:0,0,0,0,0,0,0;-1/1:4693:0,0,-2,-2,0,0,0"
  | 3 => laurent_polynomial% "-1/1:151:0,0,0,-2,0,0,0;1/1:4697:0,0,0,-2,0,0,0"
  | 4 => laurent_polynomial% "1/1:424:0,0,0,0,0,0,0;1/1:4697:0,-2,0,-2,0,0,0"
  | 5 => laurent_polynomial% "-1/1:472:0,-2,0,-2,0,0,0;1/1:4696:0,-2,0,-2,0,0,0"
  | 6 => laurent_polynomial% "1/1:2513:0,0,0,0,0,0,0;-1/1:4693:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:62:0,0,0,0,0,0,0;-1/1:4702:0,2,-2,-2,0,0,0"
  | 8 => laurent_polynomial% "1/1:83:0,0,0,0,0,0,0;-1/1:4702:0,2,-2,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:105:-2,2,-2,0,0,0,0;-1/1:4702:-2,2,-2,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:7:0,0,0,0,0,0,0;1/1:4705:2,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "-1/1:48:2,-2,0,-2,0,0,0;1/1:4705:2,-2,0,-2,0,0,0"
  | 12 => laurent_polynomial% "1/1:77:0,0,0,0,0,0,0;-1/1:4706:-2,0,2,-2,0,0,0"
  | 13 => laurent_polynomial% "1/1:246:0,0,0,0,0,0,0;-1/1:4702:0,2,-2,-2,0,0,0"
  | 14 => laurent_polynomial% "-1/1:432:0,-2,0,-2,0,0,0;1/1:4706:0,-2,0,-2,0,0,0"
  | 15 => laurent_polynomial% "1/1:448:0,0,0,0,0,0,0;1/1:4704:0,-2,0,-2,0,0,0"
  | 16 => laurent_polynomial% "1/1:812:0,0,0,0,0,0,0;-1/1:4702:-2,2,-2,-2,0,0,0"
  | 17 => laurent_polynomial% "1/1:2736:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,0,0,0,0;-1/1:4674:0,0,0,0,0,0,0;-1/1:4702:0,0,-2,0,0,0,0"
  | 18 => laurent_polynomial% "-1/1:356:0,2,0,-2,0,0,0;1/1:4713:0,2,0,-2,0,0,0"
  | 19 => laurent_polynomial% "-1/1:1848:-2,0,0,-2,0,0,0;1/1:4713:-2,0,0,-2,0,0,0"
  | 20 => laurent_polynomial% "1/1:2737:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,0,0,0,0;-1/1:4683:0,0,0,0,0,0,0;-1/1:4693:0,0,-2,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;1/1:4716:0,2,0,-2,0,0,0"
  | 22 => laurent_polynomial% "1/1:3224:2,0,0,0,0,0,0;-1/1:4692:2,0,0,0,0,0,0;-1/1:4695:2,0,0,0,0,0,0;1/1:4703:1,0,0,0,1,0,0"
  | 23 => laurent_polynomial% "1/1:69:-2,-2,2,2,0,0,0;-1/1:4718:-2,-2,2,2,0,0,0"
  | 24 => laurent_polynomial% "1/1:93:0,0,0,0,0,0,0;-1/1:4719:2,2,-2,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:1:0,0,0,-2,0,0,0;1/1:4720:0,0,0,-2,0,0,0"
  | 26 => laurent_polynomial% "1/1:25:0,0,0,0,0,0,0;1/1:4720:-2,-2,0,-2,0,0,0"
  | 27 => laurent_polynomial% "1/1:119:0,0,0,0,0,0,0;-1/1:4719:0,0,-2,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:396:0,0,0,0,0,0,0;1/1:4720:0,-2,0,-2,0,0,0"
  | 29 => laurent_polynomial% "1/1:2731:0,0,0,0,0,0,0;-1/1:4719:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:87:2,2,-2,0,0,0,0;-1/1:4725:2,2,-2,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:22:0,0,0,0,0,0,0;1/1:4726:0,-2,0,-2,0,0,0"
  | _ => []

compact_certificate def operationsPart4 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "-1/1:46:-2,-2,0,0,0,0,0;1/1:4726:-2,-2,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:283:2,2,-2,-2,0,0,0;-1/1:4725:2,2,-2,-2,0,0,0"
  | 2 => laurent_polynomial% "1/1:333:0,0,0,0,0,0,0;1/1:4726:0,0,0,-2,0,0,0"
  | 3 => laurent_polynomial% "1/1:393:0,0,0,0,0,0,0;1/1:4726:-2,-2,0,-2,0,0,0"
  | 4 => laurent_polynomial% "1/1:3233:2,0,0,0,0,0,0;-1/1:4624:2,0,0,0,0,0,0;-1/1:4703:2,0,0,0,0,0,0;1/1:4718:1,0,0,0,1,0,0"
  | 5 => laurent_polynomial% "-1/1:330:-2,0,0,2,0,0,0;1/1:4732:-2,0,0,2,0,0,0"
  | 6 => laurent_polynomial% "1/1:706:0,0,0,0,0,0,0;1/1:4733:2,-2,0,-2,0,0,0"
  | 7 => laurent_polynomial% "1/1:3254:2,0,0,0,0,0,0;-1/1:4621:2,0,0,0,0,0,0;-1/1:4717:2,0,0,0,0,0,0;1/1:4730:1,0,0,0,1,0,0"
  | 8 => laurent_polynomial% "1/1:3446:0,0,0,0,0,0,0;-1/1:4666:0,0,0,0,0,0,0;-1/1:4696:-2,0,0,0,0,0,0;1/1:4706:-1,0,0,0,1,0,0"
  | 9 => laurent_polynomial% "-1/1:358:2,0,0,-2,0,0,0;1/1:4736:2,0,0,-2,0,0,0"
  | 10 => laurent_polynomial% "1/1:3467:0,0,0,0,0,0,0;-1/1:4622:-2,0,0,0,0,0,0;1/1:4623:-1,0,0,0,1,0,0;-1/1:4720:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3488:0,0,0,0,0,0,0;1/1:4600:-1,0,0,0,1,0,0;-1/1:4615:-2,0,0,0,0,0,0;-1/1:4726:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:3614:0,0,0,0,0,0,0;-1/1:4600:-2,0,0,0,0,0,0;-1/1:4696:0,0,0,0,0,0,0;1/1:4726:-1,0,0,0,1,0,0"
  | 13 => laurent_polynomial% "-1/1:4:2,0,0,-2,0,0,0;1/1:4740:2,0,0,-2,0,0,0"
  | 14 => laurent_polynomial% "-1/1:136:2,-2,0,-2,0,0,0;1/1:4740:2,-2,0,-2,0,0,0"
  | 15 => laurent_polynomial% "1/1:3701:2,0,0,0,0,0,0;-1/1:4638:2,0,0,0,0,0,0;-1/1:4714:2,0,0,0,0,0,0;1/1:4721:1,0,0,0,1,0,0"
  | 16 => laurent_polynomial% "1/1:3729:0,0,0,0,0,0,0;-1/1:4668:0,0,0,0,0,0,0;-1/1:4701:-2,0,0,0,0,0,0;1/1:4710:-1,0,0,0,1,0,0"
  | 17 => laurent_polynomial% "1/1:4132:0,0,0,0,0,0,0;-1/1:4615:0,0,0,0,0,0,0;-1/1:4674:0,0,0,0,0,0,0;-1/1:4706:0,0,0,0,0,0,0;-1/1:4720:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:29:0,0,0,0,0,0,0;1/1:4745:0,0,0,-2,0,0,0"
  | 19 => laurent_polynomial% "-1/1:43:0,-2,0,0,0,0,0;1/1:4745:0,-2,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:100:0,0,0,0,0,0,0;-1/1:4747:0,2,2,-2,0,0,0"
  | 21 => laurent_polynomial% "-1/1:320:-2,-2,0,-2,0,0,0;1/1:4745:-2,-2,0,-2,0,0,0"
  | 22 => laurent_polynomial% "1/1:340:0,0,0,0,0,0,0;1/1:4745:0,-2,0,-2,0,0,0"
  | 23 => laurent_polynomial% "-1/1:363:-2,0,0,-2,0,0,0;1/1:4745:-2,0,0,-2,0,0,0"
  | 24 => laurent_polynomial% "1/1:2533:0,0,0,0,0,0,0;-1/1:4602:2,0,-2,0,0,0,0;-1/1:4719:2,0,-2,0,0,0,0;-1/1:4745:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:292:-2,0,0,-2,0,0,0;1/1:4752:-2,0,0,-2,0,0,0"
  | 26 => laurent_polynomial% "1/1:3992:0,0,0,0,0,0,0;1/1:4666:0,-1,0,0,0,1,0;-1/1:4683:0,-2,0,0,0,0,0;-1/1:4720:0,0,0,0,0,0,0;-1/1:4747:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:328:0,0,0,0,0,0,0;1/1:4754:0,2,0,-2,0,0,0"
  | 28 => laurent_polynomial% "1/1:4216:0,0,0,0,0,0,0;-1/1:4600:0,0,0,0,0,0,0;-1/1:4619:0,0,0,0,0,0,0;-1/1:4666:0,0,0,0,0,0,0;-1/1:4704:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:65:0,0,0,0,0,0,0;-1/1:4756:-2,-2,2,-2,0,0,0"
  | 30 => laurent_polynomial% "1/1:145:0,0,0,0,0,0,0;1/1:4756:-2,-2,0,-2,0,0,0"
  | 31 => laurent_polynomial% "-1/1:312:0,-2,0,-2,0,0,0;1/1:4756:0,-2,0,-2,0,0,0"
  | _ => []
compact_certificate def operationsPart5 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "-1/1:360:-2,-2,0,0,0,0,0;1/1:4756:-2,-2,0,0,0,0,0"
  | 1 => laurent_polynomial% "-1/1:9:2,2,0,-2,0,0,0;1/1:4760:2,2,0,-2,0,0,0"
  | 2 => laurent_polynomial% "-1/1:731:-2,0,0,-2,0,0,0;1/1:4756:-2,0,0,-2,0,0,0"
  | 3 => laurent_polynomial% "1/1:2527:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,0,0,0,0;-1/1:4702:0,0,-2,0,0,0,0;-1/1:4756:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:3240:2,0,0,0,0,0,0;-1/1:4603:2,0,0,0,0,0,0;1/1:4685:1,0,0,0,1,0,0;-1/1:4757:2,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:81:-2,2,-2,2,0,0,0;-1/1:4764:-2,2,-2,2,0,0,0"
  | 6 => laurent_polynomial% "-1/1:40:2,-2,0,0,0,0,0;1/1:4765:2,-2,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:401:0,0,0,0,0,0,0;1/1:4766:-2,2,0,-2,0,0,0"
  | 8 => laurent_polynomial% "1/1:2182:0,0,0,0,0,0,0;1/1:4766:0,0,0,-2,0,0,0"
  | 9 => laurent_polynomial% "1/1:3383:0,0,0,0,0,0,0;-1/1:4683:0,0,0,0,0,0,0;-1/1:4745:-2,0,0,0,0,0,0;1/1:4756:-1,0,0,0,1,0,0"
  | 10 => laurent_polynomial% "-1/1:44:2,0,0,-2,0,0,0;1/1:4769:2,0,0,-2,0,0,0"
  | 11 => laurent_polynomial% "1/1:398:0,0,0,0,0,0,0;1/1:4769:2,-2,0,-2,0,0,0"
  | 12 => laurent_polynomial% "1/1:2523:0,0,0,0,0,0,0;-1/1:4601:-2,0,-2,0,0,0,0;-1/1:4693:-2,0,-2,0,0,0,0;-1/1:4769:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:3649:0,0,0,0,0,0,0;1/1:4716:-1,0,0,0,1,0,0;-1/1:4728:0,0,0,0,0,0,0;-1/1:4763:-2,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:732:0,0,0,-2,0,0,0;1/1:4773:0,0,0,-2,0,0,0"
  | 15 => laurent_polynomial% "1/1:3817:0,0,0,0,0,0,0;-1/1:4667:0,0,0,0,0,0,0;1/1:4736:0,-1,0,0,0,1,0;-1/1:4738:0,0,0,0,0,0,0;-1/1:4769:0,-2,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:3824:0,0,0,0,0,0,0;-1/1:4617:0,0,0,0,0,0,0;-1/1:4666:0,-2,0,0,0,0,0;1/1:4720:0,-1,0,0,0,1,0;-1/1:4773:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:3474:0,0,0,0,0,0,0;-1/1:4625:-2,0,0,0,0,0,0;1/1:4627:-1,0,0,0,1,0,0;-1/1:4776:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:4153:0,0,0,0,0,0,0;-1/1:4682:0,0,0,0,0,0,0;-1/1:4691:0,0,0,0,0,0,0;-1/1:4739:0,0,0,0,0,0,0;-1/1:4769:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:36:0,0,0,0,0,0,0;1/1:4778:2,-2,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:95:0,0,0,0,0,0,0;-1/1:4778:2,0,2,-2,0,0,0"
  | 21 => laurent_polynomial% "1/1:3290:0,0,0,0,0,0,0;1/1:4665:-1,0,0,0,1,0,0;-1/1:4708:0,0,0,0,0,0,0;-1/1:4780:-2,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:80:0,0,0,0,0,0,0;-1/1:4781:0,-2,-2,2,0,0,0"
  | 23 => laurent_polynomial% "1/1:236:0,0,0,0,0,0,0;-1/1:4781:0,0,-2,2,0,0,0"
  | 24 => laurent_polynomial% "1/1:27:0,0,0,0,0,0,0;1/1:4783:-2,0,0,-2,0,0,0"
  | 25 => laurent_polynomial% "1/1:182:0,0,0,0,0,0,0;1/1:4783:0,-2,0,-2,0,0,0"
  | 26 => laurent_polynomial% "-1/1:318:0,-2,0,0,0,0,0;1/1:4784:0,-2,0,0,0,0,0"
  | 27 => laurent_polynomial% "-1/1:361:0,0,0,-2,0,0,0;1/1:4783:0,0,0,-2,0,0,0"
  | 28 => laurent_polynomial% "1/1:2532:0,0,0,0,0,0,0;-1/1:4602:2,0,-2,0,0,0,0;-1/1:4725:2,0,-2,0,0,0,0;-1/1:4783:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "-1/1:749:-2,0,0,-2,0,0,0;1/1:4788:-2,0,0,-2,0,0,0"
  | 30 => laurent_polynomial% "1/1:3264:2,0,0,0,0,0,0;-1/1:4664:2,0,0,0,0,0,0;-1/1:4779:2,0,0,0,0,0,0;1/1:4782:1,0,0,0,1,0,0"
  | 31 => laurent_polynomial% "1/1:89:-2,2,2,-2,0,0,0;-1/1:4790:-2,2,2,-2,0,0,0"
  | _ => []
compact_certificate def operationsPart6 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3365:0,0,0,0,0,0,0;-1/1:4665:0,0,0,0,0,0,0;1/1:4780:-1,0,0,0,1,0,0;-1/1:4781:-2,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:3890:0,0,0,0,0,0,0;-1/1:4630:0,0,0,0,0,0,0;-1/1:4665:0,0,0,0,0,0,0;1/1:4748:0,-1,0,0,0,1,0;-1/1:4780:0,-2,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:2739:0,0,-2,2,0,0,0;-1/1:4665:0,0,-2,2,0,0,0;-1/1:4696:0,0,0,0,0,0,0;-1/1:4793:0,0,-2,2,0,0,0"
  | 3 => laurent_polynomial% "1/1:300:0,0,0,0,0,0,0;1/1:4794:-2,0,0,-2,0,0,0"
  | 4 => laurent_polynomial% "1/1:4188:0,0,0,0,0,0,0;-1/1:4627:0,0,0,0,0,0,0;-1/1:4766:0,0,0,0,0,0,0;-1/1:4782:0,0,0,0,0,0,0;-1/1:4788:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:345:0,0,0,0,0,0,0;1/1:4796:-2,2,0,-2,0,0,0"
  | 6 => laurent_polynomial% "1/1:4048:0,0,0,0,0,0,0;-1/1:4622:0,0,0,0,0,0,0;1/1:4696:0,-1,0,0,0,1,0;-1/1:4745:0,-2,0,0,0,0,0;-1/1:4796:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:4460:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:71:0,0,0,0,0,0,0;-1/1:4799:-2,2,0,-2,0,0,0"
  | 9 => laurent_polynomial% "1/1:76:0,2,0,0,0,0,0;-1/1:4799:0,2,0,0,0,0,0"
  | 10 => laurent_polynomial% "-1/1:5:0,-2,0,0,0,0,0;1/1:4801:0,-2,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:98:-2,0,0,0,0,0,0;-1/1:4801:-2,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:41:0,0,0,0,0,0,0;1/1:4803:2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:23:0,0,0,0,0,0,0;1/1:4804:-2,-2,0,-2,0,0,0"
  | 14 => laurent_polynomial% "1/1:54:0,0,0,0,0,0,0;-1/1:4804:-2,-2,0,-2,0,0,0"
  | 15 => laurent_polynomial% "1/1:63:0,0,0,0,0,0,0;-1/1:4803:2,-2,0,-2,0,0,0"
  | 16 => laurent_polynomial% "1/1:67:0,0,0,0,0,0,0;-1/1:4804:0,0,0,-2,0,0,0"
  | 17 => laurent_polynomial% "1/1:82:0,0,0,0,0,0,0;-1/1:4804:-2,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "-1/1:0:2,-2,0,-2,0,0,0;1/1:4809:2,-2,0,-2,0,0,0"
  | 19 => laurent_polynomial% "1/1:109:-2,2,0,-2,0,0,0;-1/1:4802:-2,2,0,-2,0,0,0"
  | 20 => laurent_polynomial% "1/1:146:0,0,0,0,0,0,0;1/1:4803:2,-2,0,-2,0,0,0"
  | 21 => laurent_polynomial% "1/1:248:0,0,0,0,0,0,0;-1/1:4804:0,-2,0,-2,0,0,0"
  | 22 => laurent_polynomial% "1/1:285:0,0,0,-2,0,0,0;-1/1:4801:0,0,0,-2,0,0,0"
  | 23 => laurent_polynomial% "-1/1:288:0,-2,0,-2,0,0,0;1/1:4804:0,-2,0,-2,0,0,0"
  | 24 => laurent_polynomial% "1/1:334:0,0,0,0,0,0,0;1/1:4803:2,-2,0,-2,0,0,0"
  | 25 => laurent_polynomial% "1/1:395:0,0,0,0,0,0,0;1/1:4801:-2,-2,0,-2,0,0,0"
  | 26 => laurent_polynomial% "1/1:815:0,0,0,0,0,0,0;-1/1:4801:-2,-2,0,-2,0,0,0"
  | 27 => laurent_polynomial% "1/1:3225:0,0,0,0,0,0,0;-1/1:4650:0,0,0,0,0,0,0;-1/1:4657:-2,0,0,0,0,0,0;1/1:4807:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "-1/1:1883:0,2,0,2,0,0,0;1/1:4819:0,2,0,2,0,0,0"
  | 29 => laurent_polynomial% "1/1:84:0,0,0,0,0,0,0;-1/1:4820:2,-2,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:106:2,0,0,-2,0,0,0;-1/1:4820:2,0,0,-2,0,0,0"
  | 31 => laurent_polynomial% "1/1:2534:0,0,0,0,0,0,0;-1/1:4648:-2,0,0,0,0,0,0;-1/1:4652:-2,0,0,0,0,0,0;-1/1:4820:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def operationsPart7 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:2619:2,-2,2,0,0,0,0;-1/1:4648:0,0,0,0,0,0,0;-1/1:4682:2,-2,2,0,0,0,0;-1/1:4739:2,-2,2,0,0,0,0;-1/1:4769:2,-2,2,0,0,0,0;-1/1:4778:2,-2,2,0,0,0,0;-1/1:4802:0,0,0,0,0,0,0;-1/1:4821:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:31:0,0,0,0,0,0,0;1/1:4824:-2,2,0,-2,0,0,0"
  | 2 => laurent_polynomial% "1/1:241:0,0,0,0,0,0,0;-1/1:4824:0,2,0,-2,0,0,0"
  | 3 => laurent_polynomial% "1/1:2540:0,0,0,0,0,0,0;-1/1:4801:0,0,0,0,0,0,0;-1/1:4804:0,0,0,0,0,0,0;-1/1:4824:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:233:0,2,0,-2,0,0,0;-1/1:4827:0,2,0,-2,0,0,0"
  | 5 => laurent_polynomial% "-1/1:359:-2,2,0,-2,0,0,0;1/1:4827:-2,2,0,-2,0,0,0"
  | 6 => laurent_polynomial% "1/1:2621:0,0,0,0,0,0,0;-1/1:4601:0,-2,0,0,0,0,0;-1/1:4647:0,-2,0,0,0,0,0;-1/1:4652:0,-2,0,0,0,0,0;-1/1:4655:0,0,0,0,0,0,0;-1/1:4702:0,0,0,0,0,0,0;-1/1:4804:0,-2,0,0,0,0,0;-1/1:4827:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:96:0,0,0,0,0,0,0;-1/1:4830:-2,2,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:74:0,0,0,0,0,0,0;-1/1:4831:2,0,0,-2,0,0,0"
  | 9 => laurent_polynomial% "-1/1:1876:0,-2,0,-2,0,0,0;1/1:4831:0,-2,0,-2,0,0,0"
  | 10 => laurent_polynomial% "1/1:2535:0,0,0,0,0,0,0;-1/1:4647:-2,0,0,0,0,0,0;-1/1:4655:-2,0,0,0,0,0,0;-1/1:4831:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3245:2,0,0,0,0,0,0;-1/1:4808:2,0,0,0,0,0,0;-1/1:4825:2,0,0,0,0,0,0;1/1:4832:1,0,0,0,1,0,0"
  | 12 => laurent_polynomial% "-1/1:351:-2,-2,0,2,0,0,0;1/1:4835:-2,-2,0,2,0,0,0"
  | 13 => laurent_polynomial% "1/1:2605:0,0,0,0,0,0,0;-1/1:4601:-2,-2,0,0,0,0,0;-1/1:4652:-2,-2,0,0,0,0,0;-1/1:4719:0,0,0,0,0,0,0;-1/1:4801:-2,-2,0,0,0,0,0;-1/1:4804:-2,-2,0,0,0,0,0;-1/1:4834:0,0,0,0,0,0,0;-1/1:4836:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:92:2,2,0,-2,0,0,0;-1/1:4837:2,2,0,-2,0,0,0"
  | 15 => laurent_polynomial% "1/1:2735:0,0,0,0,0,0,0;-1/1:4799:0,0,0,-2,0,0,0;-1/1:4801:0,0,0,-2,0,0,0;-1/1:4838:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:3260:2,0,0,0,0,0,0;1/1:4651:1,0,0,0,1,0,0;-1/1:4800:2,0,0,0,0,0,0;-1/1:4828:2,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:88:-2,-2,0,2,0,0,0;-1/1:4840:-2,-2,0,2,0,0,0"
  | 18 => laurent_polynomial% "1/1:2606:0,0,0,0,0,0,0;-1/1:4601:-2,-2,0,0,0,0,0;-1/1:4647:-2,-2,0,0,0,0,0;-1/1:4725:0,0,0,0,0,0,0;-1/1:4801:-2,-2,0,0,0,0,0;-1/1:4804:-2,-2,0,0,0,0,0;-1/1:4823:0,0,0,0,0,0,0;-1/1:4841:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "-1/1:39:2,2,0,-2,0,0,0;1/1:4842:2,2,0,-2,0,0,0"
  | 20 => laurent_polynomial% "1/1:2627:0,0,0,0,0,0,0;-1/1:4661:0,0,0,0,0,0,0;-1/1:4693:0,2,0,-2,0,0,0;-1/1:4780:0,0,0,0,0,0,0;-1/1:4802:0,2,0,-2,0,0,0;-1/1:4821:0,2,0,-2,0,0,0;-1/1:4824:0,2,0,-2,0,0,0;-1/1:4843:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:2528:0,0,0,0,0,0,0;-1/1:4809:2,0,0,-2,0,0,0;-1/1:4836:2,0,0,-2,0,0,0;-1/1:4844:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:2734:0,0,0,0,0,0,0;-1/1:4802:0,0,0,-2,0,0,0;-1/1:4804:0,0,0,-2,0,0,0;-1/1:4840:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:4420:0,0,0,0,0,0,0;1/1:4647:0,0,0,-1,0,0,1;-1/1:4801:0,0,0,0,0,0,0;-1/1:4804:0,0,0,-2,0,0,0;-1/1:4814:0,0,0,0,0,0,0;-1/1:4828:0,0,0,0,0,0,0;-1/1:4835:0,0,0,0,0,0,0;-1/1:4838:0,0,0,0,0,0,0;-1/1:4844:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:3485:0,0,0,0,0,0,0;1/1:4653:-1,0,0,0,1,0,0;-1/1:4808:-2,0,0,0,0,0,0;-1/1:4847:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:4466:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:17:0,0,0,0,0,0,0;1/1:4849:-2,2,0,-2,0,0,0"
  | 27 => laurent_polynomial% "1/1:122:0,0,2,-2,0,0,0;-1/1:4849:0,0,2,-2,0,0,0"
  | 28 => laurent_polynomial% "1/1:99:0,0,0,0,0,0,0;-1/1:4851:-2,2,-2,2,0,0,0"
  | 29 => laurent_polynomial% "-1/1:139:2,-2,0,-2,0,0,0;1/1:4852:2,-2,0,-2,0,0,0"
  | 30 => laurent_polynomial% "1/1:2597:0,0,0,0,0,0,0;-1/1:4647:-2,0,-2,0,0,0,0;-1/1:4652:-2,0,-2,0,0,0,0;-1/1:4733:0,0,0,0,0,0,0;-1/1:4736:0,0,0,0,0,0,0;-1/1:4801:-2,0,-2,0,0,0,0;-1/1:4804:-2,0,-2,0,0,0,0;-1/1:4852:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:454:0,0,0,0,0,0,0;1/1:4854:2,0,0,-2,0,0,0"
  | _ => []

compact_certificate def operationsPart8 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:2812:0,0,0,0,0,0,0;-1/1:4647:0,-2,-2,0,0,0,0;-1/1:4652:0,-2,-2,0,0,0,0;-1/1:4747:0,0,0,0,0,0,0;-1/1:4752:0,0,0,0,0,0,0;-1/1:4801:0,-2,-2,0,0,0,0;-1/1:4804:0,-2,-2,0,0,0,0;-1/1:4849:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "-1/1:45:-2,2,0,-2,0,0,0;1/1:4856:-2,2,0,-2,0,0,0"
  | 2 => laurent_polynomial% "1/1:3227:2,0,0,0,0,0,0;-1/1:4610:2,0,0,0,0,0,0;1/1:4671:1,0,0,0,1,0,0;-1/1:4850:2,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "-1/1:325:-2,-2,0,2,0,0,0;1/1:4858:-2,-2,0,2,0,0,0"
  | 4 => laurent_polynomial% "-1/1:30:2,2,0,0,0,0,0;1/1:4859:2,2,0,0,0,0,0"
  | 5 => laurent_polynomial% "-1/1:153:0,-2,0,-2,0,0,0;1/1:4860:0,-2,0,-2,0,0,0"
  | 6 => laurent_polynomial% "1/1:287:-2,-2,2,-2,0,0,0;-1/1:4860:-2,-2,2,-2,0,0,0"
  | 7 => laurent_polynomial% "-1/1:310:-2,0,0,-2,0,0,0;1/1:4860:-2,0,0,-2,0,0,0"
  | 8 => laurent_polynomial% "1/1:2526:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,0,0,0,0;-1/1:4693:0,0,-2,0,0,0,0;-1/1:4860:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:2625:0,0,0,0,0,0,0;-1/1:4623:0,0,0,0,0,0,0;-1/1:4696:0,0,0,0,0,0,0;-1/1:4803:2,0,-2,0,0,0,0;-1/1:4809:2,0,-2,0,0,0,0;-1/1:4820:2,0,-2,0,0,0,0;-1/1:4831:2,0,-2,0,0,0,0;-1/1:4860:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "-1/1:2:-2,-2,0,0,0,0,0;1/1:4865:-2,-2,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:94:0,0,2,-2,0,0,0;-1/1:4865:0,0,2,-2,0,0,0"
  | 12 => laurent_polynomial% "1/1:108:-2,-2,-2,2,0,0,0;-1/1:4867:-2,-2,-2,2,0,0,0"
  | 13 => laurent_polynomial% "1/1:447:0,0,0,0,0,0,0;1/1:4865:-2,-2,0,-2,0,0,0"
  | 14 => laurent_polynomial% "1/1:743:0,0,0,0,0,0,0;1/1:4866:2,0,0,-2,0,0,0"
  | 15 => laurent_polynomial% "1/1:2617:0,0,0,0,0,0,0;-1/1:4602:2,0,0,-2,0,0,0;-1/1:4803:2,0,0,-2,0,0,0;-1/1:4809:2,0,0,-2,0,0,0;-1/1:4820:2,0,0,-2,0,0,0;-1/1:4826:0,0,0,0,0,0,0;-1/1:4847:0,0,0,0,0,0,0;-1/1:4867:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:2525:0,0,0,0,0,0,0;-1/1:4647:0,0,0,-2,0,0,0;-1/1:4821:0,0,0,-2,0,0,0;-1/1:4871:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:2750:0,0,0,0,0,0,0;-1/1:4665:0,0,0,0,0,0,0;-1/1:4748:0,0,0,0,0,0,0;-1/1:4780:0,0,0,0,0,0,0;-1/1:4781:0,0,0,0,0,0,0;-1/1:4867:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:85:0,0,0,0,0,0,0;-1/1:4873:-2,0,-2,2,0,0,0"
  | 19 => laurent_polynomial% "1/1:240:0,0,0,0,0,0,0;-1/1:4873:0,-2,-2,2,0,0,0"
  | 20 => laurent_polynomial% "1/1:2538:0,0,0,0,0,0,0;-1/1:4720:0,0,2,-2,0,0,0;-1/1:4754:0,0,2,-2,0,0,0;-1/1:4873:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:2620:0,0,0,0,0,0,0;-1/1:4655:-2,2,-2,0,0,0,0;-1/1:4673:0,0,0,0,0,0,0;-1/1:4738:0,0,0,0,0,0,0;-1/1:4799:-2,2,-2,0,0,0,0;-1/1:4827:-2,2,-2,0,0,0,0;-1/1:4830:-2,2,-2,0,0,0,0;-1/1:4874:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:20:0,0,0,0,0,0,0;1/1:4877:2,-2,0,-2,0,0,0"
  | 23 => laurent_polynomial% "1/1:346:0,0,0,0,0,0,0;1/1:4877:2,0,0,-2,0,0,0"
  | 24 => laurent_polynomial% "1/1:2522:0,0,0,0,0,0,0;-1/1:4601:-2,0,-2,0,0,0,0;-1/1:4702:-2,0,-2,0,0,0,0;-1/1:4877:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:2628:0,0,0,0,0,0,0;-1/1:4653:0,0,0,0,0,0,0;-1/1:4702:0,2,0,-2,0,0,0;-1/1:4799:0,2,0,-2,0,0,0;-1/1:4827:0,2,0,-2,0,0,0;-1/1:4830:0,2,0,-2,0,0,0;-1/1:4835:0,0,0,0,0,0,0;-1/1:4873:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:2529:0,0,0,0,0,0,0;-1/1:4803:2,0,0,-2,0,0,0;-1/1:4842:2,0,0,-2,0,0,0;-1/1:4881:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:2777:0,0,0,0,0,0,0;-1/1:4801:0,0,0,0,0,0,0;-1/1:4804:0,0,0,0,0,0,0;-1/1:4826:0,0,0,0,0,0,0;-1/1:4828:0,0,0,0,0,0,0;-1/1:4835:0,0,0,0,0,0,0;-1/1:4838:0,0,0,0,0,0,0;-1/1:4840:0,0,0,0,0,0,0;-1/1:4843:0,0,0,0,0,0,0;-1/1:4844:0,0,0,0,0,0,0;-1/1:4847:0,0,0,0,0,0,0;-1/1:4881:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:2618:0,0,0,0,0,0,0;-1/1:4602:2,0,0,-2,0,0,0;-1/1:4665:0,0,0,0,0,0,0;-1/1:4803:2,0,0,-2,0,0,0;-1/1:4809:2,0,0,-2,0,0,0;-1/1:4828:0,0,0,0,0,0,0;-1/1:4831:2,0,0,-2,0,0,0;-1/1:4883:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:2524:0,0,0,0,0,0,0;-1/1:4652:0,0,0,-2,0,0,0;-1/1:4830:0,0,0,-2,0,0,0;-1/1:4884:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:2826:0,0,0,0,0,0,0;-1/1:4651:0,-2,-2,2,0,0,0;-1/1:4661:0,-2,-2,2,0,0,0;-1/1:4681:0,0,0,0,0,0,0;-1/1:4776:0,0,0,0,0,0,0;-1/1:4843:0,-2,-2,2,0,0,0;-1/1:4844:0,-2,-2,2,0,0,0;-1/1:4864:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "-1/1:133:-2,2,0,-2,0,0,0;1/1:4886:-2,2,0,-2,0,0,0"
  | _ => []
compact_certificate def operationsPart9 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3226:0,0,0,0,0,0,0;1/1:4700:-1,0,0,0,1,0,0;-1/1:4711:-2,0,0,0,0,0,0;-1/1:4870:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:3242:2,0,0,0,0,0,0;-1/1:4746:2,0,0,0,0,0,0;1/1:4855:1,0,0,0,1,0,0;-1/1:4863:2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:3271:0,0,0,0,0,0,0;-1/1:4670:0,0,0,0,0,0,0;-1/1:4794:-2,0,0,0,0,0,0;1/1:4849:-1,0,0,0,1,0,0"
  | 3 => laurent_polynomial% "-1/1:747:2,0,0,-2,0,0,0;1/1:4890:2,0,0,-2,0,0,0"
  | 4 => laurent_polynomial% "1/1:3300:0,0,0,0,0,0,0;-1/1:4656:0,0,0,0,0,0,0;1/1:4839:-1,0,0,0,1,0,0;-1/1:4872:-2,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:3305:0,0,0,0,0,0,0;-1/1:4651:0,0,0,0,0,0,0;1/1:4840:-1,0,0,0,1,0,0;-1/1:4884:-2,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:3306:0,0,0,0,0,0,0;1/1:4713:-1,0,0,0,1,0,0;-1/1:4723:0,0,0,0,0,0,0;-1/1:4864:-2,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "-1/1:309:0,0,0,-2,0,0,0;1/1:4894:0,0,0,-2,0,0,0"
  | 8 => laurent_polynomial% "1/1:2590:0,0,0,0,0,0,0;-1/1:4647:0,-2,-2,0,0,0,0;-1/1:4652:0,-2,-2,0,0,0,0;-1/1:4689:0,0,0,0,0,0,0;-1/1:4790:0,0,0,0,0,0,0;-1/1:4801:0,-2,-2,0,0,0,0;-1/1:4804:0,-2,-2,0,0,0,0;-1/1:4894:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:741:0,0,0,0,0,0,0;1/1:4896:-2,0,0,-2,0,0,0"
  | 10 => laurent_polynomial% "1/1:2738:0,0,0,0,0,0,0;-1/1:4704:0,0,2,-2,0,0,0;-1/1:4867:0,0,0,0,0,0,0;-1/1:4896:0,0,2,-2,0,0,0"
  | 11 => laurent_polynomial% "1/1:3265:0,0,0,0,0,0,0;-1/1:4685:0,0,0,0,0,0,0;1/1:4764:-1,0,0,0,1,0,0;-1/1:4898:-2,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:3315:0,0,0,0,0,0,0;-1/1:4764:0,0,0,0,0,0,0;-1/1:4876:-2,0,0,0,0,0,0;1/1:4898:-1,0,0,0,1,0,0"
  | 13 => laurent_polynomial% "1/1:3369:0,0,0,0,0,0,0;1/1:4796:-1,0,0,0,1,0,0;-1/1:4886:0,0,0,0,0,0,0;-1/1:4894:-2,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:3385:0,0,0,0,0,0,0;-1/1:4839:0,0,0,0,0,0,0;1/1:4872:-1,0,0,0,1,0,0;-1/1:4882:-2,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:2521:0,0,0,0,0,0,0;-1/1:4804:-2,0,0,-2,0,0,0;-1/1:4827:-2,0,0,-2,0,0,0;-1/1:4902:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:3395:0,0,0,0,0,0,0;-1/1:4840:0,0,0,0,0,0,0;-1/1:4844:-2,0,0,0,0,0,0;1/1:4884:-1,0,0,0,1,0,0"
  | 17 => laurent_polynomial% "1/1:2520:0,0,0,0,0,0,0;-1/1:4801:-2,0,0,-2,0,0,0;-1/1:4824:-2,0,0,-2,0,0,0;-1/1:4904:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3404:0,0,0,0,0,0,0;-1/1:4666:-2,0,0,0,0,0,0;1/1:4783:-1,0,0,0,1,0,0;-1/1:4860:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "-1/1:466:2,0,0,-2,0,0,0;1/1:4906:2,0,0,-2,0,0,0"
  | 20 => laurent_polynomial% "1/1:2598:0,0,0,0,0,0,0;-1/1:4647:-2,0,-2,0,0,0,0;-1/1:4652:-2,0,-2,0,0,0,0;-1/1:4740:0,0,0,0,0,0,0;-1/1:4765:0,0,0,0,0,0,0;-1/1:4801:-2,0,-2,0,0,0,0;-1/1:4804:-2,0,-2,0,0,0,0;-1/1:4906:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:32:0,0,0,0,0,0,0;1/1:4908:2,0,0,-2,0,0,0"
  | 22 => laurent_polynomial% "1/1:3248:2,0,0,0,0,0,0;1/1:4755:1,0,0,0,1,0,0;-1/1:4887:2,0,0,0,0,0,0;-1/1:4909:2,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:3432:0,0,0,0,0,0,0;-1/1:4716:-2,0,0,0,0,0,0;1/1:4773:-1,0,0,0,1,0,0;-1/1:4856:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:3440:0,0,0,0,0,0,0;1/1:4748:-1,0,0,0,1,0,0;-1/1:4867:-2,0,0,0,0,0,0;-1/1:4873:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:91:2,-2,-2,2,0,0,0;-1/1:4912:2,-2,-2,2,0,0,0"
  | 26 => laurent_polynomial% "1/1:2589:0,0,0,0,0,0,0;-1/1:4647:0,-2,-2,0,0,0,0;-1/1:4652:0,-2,-2,0,0,0,0;-1/1:4773:0,0,0,0,0,0,0;-1/1:4794:0,0,0,0,0,0,0;-1/1:4801:0,-2,-2,0,0,0,0;-1/1:4804:0,-2,-2,0,0,0,0;-1/1:4913:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "-1/1:42:0,2,0,-2,0,0,0;1/1:4914:0,2,0,-2,0,0,0"
  | 28 => laurent_polynomial% "1/1:2860:0,0,0,0,0,0,0;-1/1:4694:0,0,0,0,0,0,0;-1/1:4708:0,0,0,0,0,0,0;-1/1:4791:0,0,0,0,0,0,0;-1/1:4792:0,0,0,0,0,0,0;-1/1:4912:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:2530:0,0,0,0,0,0,0;-1/1:4623:-2,0,2,-2,0,0,0;-1/1:4886:-2,0,2,-2,0,0,0;-1/1:4916:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:3376:0,0,0,0,0,0,0;1/1:4752:-1,0,0,0,1,0,0;-1/1:4763:0,0,0,0,0,0,0;-1/1:4914:-2,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:3415:2,0,0,0,0,0,0;1/1:4876:1,0,0,0,1,0,0;-1/1:4898:2,0,0,0,0,0,0;-1/1:4917:2,0,0,0,0,0,0"
  | _ => []
compact_certificate def operationsPart10 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:2537:0,0,0,0,0,0,0;-1/1:4733:0,0,0,0,0,0,0;-1/1:4748:-2,0,-2,2,0,0,0;-1/1:4919:-2,0,-2,2,0,0,0"
  | 1 => laurent_polynomial% "1/1:3470:0,0,0,0,0,0,0;1/1:4661:-1,0,0,0,1,0,0;-1/1:4814:-2,0,0,0,0,0,0;-1/1:4883:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:3490:0,0,0,0,0,0,0;1/1:4603:-1,0,0,0,1,0,0;-1/1:4685:-2,0,0,0,0,0,0;-1/1:4919:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:3523:0,0,0,0,0,0,0;-1/1:4713:-2,0,0,0,0,0,0;-1/1:4796:0,0,0,0,0,0,0;1/1:4894:-1,0,0,0,1,0,0"
  | 4 => laurent_polynomial% "1/1:3579:0,0,0,0,0,0,0;-1/1:4689:-2,0,0,0,0,0,0;1/1:4788:-1,0,0,0,1,0,0;-1/1:4864:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:2613:0,0,0,0,0,0,0;-1/1:4777:0,0,0,0,0,0,0;-1/1:4822:-2,-2,-2,2,0,0,0;-1/1:4828:-2,-2,-2,2,0,0,0;-1/1:4883:-2,-2,-2,2,0,0,0;-1/1:4884:-2,-2,-2,2,0,0,0;-1/1:4901:0,0,0,0,0,0,0;-1/1:4924:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "-1/1:294:2,0,0,-2,0,0,0;1/1:4925:2,0,0,-2,0,0,0"
  | 7 => laurent_polynomial% "1/1:3223:0,0,0,0,0,0,0;1/1:4768:-1,0,0,0,1,0,0;-1/1:4897:0,0,0,0,0,0,0;-1/1:4926:-2,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:3217:0,0,0,0,0,0,0;-1/1:4605:0,0,0,0,0,0,0;1/1:4607:-1,0,0,0,1,0,0;-1/1:4927:-2,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:3615:0,0,0,0,0,0,0;-1/1:4603:-2,0,0,0,0,0,0;-1/1:4876:0,0,0,0,0,0,0;1/1:4919:-1,0,0,0,1,0,0"
  | 10 => laurent_polynomial% "1/1:3628:0,0,0,0,0,0,0;-1/1:4754:-2,0,0,0,0,0,0;-1/1:4766:0,0,0,0,0,0,0;1/1:4896:-1,0,0,0,1,0,0"
  | 11 => laurent_polynomial% "1/1:3650:0,0,0,0,0,0,0;-1/1:4649:0,0,0,0,0,0,0;1/1:4838:-1,0,0,0,1,0,0;-1/1:4871:-2,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:3655:0,0,0,0,0,0,0;-1/1:4659:0,0,0,0,0,0,0;1/1:4846:-1,0,0,0,1,0,0;-1/1:4885:-2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:3690:0,0,0,0,0,0,0;-1/1:4675:0,0,0,0,0,0,0;-1/1:4793:-2,0,0,0,0,0,0;1/1:4851:-1,0,0,0,1,0,0"
  | 14 => laurent_polynomial% "1/1:3713:2,0,0,0,0,0,0;-1/1:4762:2,0,0,0,0,0,0;-1/1:4787:2,0,0,0,0,0,0;1/1:4907:1,0,0,0,1,0,0"
  | 15 => laurent_polynomial% "1/1:3732:0,0,0,0,0,0,0;-1/1:4795:0,0,0,0,0,0,0;1/1:4853:-1,0,0,0,1,0,0;-1/1:4891:-2,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:3736:0,0,0,0,0,0,0;-1/1:4642:0,0,0,0,0,0,0;-1/1:4853:-2,0,0,0,0,0,0;1/1:4935:-1,0,0,0,1,0,0"
  | 17 => laurent_polynomial% "1/1:3738:0,0,0,0,0,0,0;1/1:4642:-1,0,0,0,1,0,0;-1/1:4644:0,0,0,0,0,0,0;-1/1:4935:-2,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3782:0,0,0,0,0,0,0;-1/1:4615:0,0,0,0,0,0,0;1/1:4704:0,-1,0,0,0,1,0;-1/1:4783:0,-2,0,0,0,0,0;-1/1:4856:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:2602:0,0,0,0,0,0,0;-1/1:4713:0,0,0,0,0,0,0;-1/1:4754:0,0,0,0,0,0,0;-1/1:4803:2,-2,-2,0,0,0,0;-1/1:4809:2,-2,-2,0,0,0,0;-1/1:4820:2,-2,-2,0,0,0,0;-1/1:4831:2,-2,-2,0,0,0,0;-1/1:4938:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:453:0,0,0,0,0,0,0;1/1:4939:-2,2,0,-2,0,0,0"
  | 21 => laurent_polynomial% "1/1:3313:0,0,0,0,0,0,0;-1/1:4782:0,0,0,0,0,0,0;1/1:4790:-1,0,0,0,1,0,0;-1/1:4938:-2,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:2582:0,0,0,0,0,0,0;-1/1:4647:-2,-2,-2,0,0,0,0;-1/1:4652:-2,-2,-2,0,0,0,0;-1/1:4801:-2,-2,-2,0,0,0,0;-1/1:4804:-2,-2,-2,0,0,0,0;-1/1:4923:0,0,0,0,0,0,0;-1/1:4930:0,0,0,0,0,0,0;-1/1:4941:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:3411:0,0,0,0,0,0,0;-1/1:4776:-2,0,0,0,0,0,0;-1/1:4790:0,0,0,0,0,0,0;1/1:4938:-1,0,0,0,1,0,0"
  | 24 => laurent_polynomial% "1/1:3502:0,0,0,0,0,0,0;1/1:4779:-1,0,0,0,1,0,0;-1/1:4782:-2,0,0,0,0,0,0;-1/1:4939:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:2888:0,0,0,0,0,0,0;-1/1:4647:-2,0,-2,0,0,0,0;-1/1:4652:-2,0,-2,0,0,0,0;-1/1:4655:-2,0,-2,0,0,0,0;-1/1:4667:0,0,0,0,0,0,0;-1/1:4673:0,0,0,0,0,0,0;-1/1:4705:0,0,0,0,0,0,0;-1/1:4738:0,0,0,0,0,0,0;-1/1:4760:0,0,0,0,0,0,0;-1/1:4799:-2,0,-2,0,0,0,0;-1/1:4801:-2,0,-2,0,0,0,0;-1/1:4804:-2,0,-2,0,0,0,0;-1/1:4827:-2,0,-2,0,0,0,0;-1/1:4830:-2,0,-2,0,0,0,0;-1/1:4874:0,0,0,0,0,0,0;-1/1:4944:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:37:0,0,0,0,0,0,0;1/1:4945:2,2,0,-2,0,0,0"
  | 27 => laurent_polynomial% "1/1:3621:0,0,0,0,0,0,0;-1/1:4689:0,0,0,0,0,0,0;-1/1:4779:-2,0,0,0,0,0,0;1/1:4939:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "1/1:3761:0,0,0,0,0,0,0;-1/1:4613:0,0,0,0,0,0,0;1/1:4691:0,-1,0,0,0,1,0;-1/1:4906:0,-2,0,0,0,0,0;-1/1:4943:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:2614:0,0,0,0,0,0,0;-1/1:4826:-2,-2,-2,2,0,0,0;-1/1:4832:-2,-2,-2,2,0,0,0;-1/1:4847:-2,-2,-2,2,0,0,0;-1/1:4871:-2,-2,-2,2,0,0,0;-1/1:4890:0,0,0,0,0,0,0;-1/1:4918:0,0,0,0,0,0,0;-1/1:4948:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:3481:0,0,0,0,0,0,0;-1/1:4611:-2,0,0,0,0,0,0;1/1:4616:-1,0,0,0,1,0,0;-1/1:4949:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:2827:0,0,0,0,0,0,0;-1/1:4649:0,-2,-2,2,0,0,0;-1/1:4653:0,-2,-2,2,0,0,0;-1/1:4670:0,0,0,0,0,0,0;-1/1:4763:0,0,0,0,0,0,0;-1/1:4835:0,-2,-2,2,0,0,0;-1/1:4881:0,-2,-2,2,0,0,0;-1/1:4950:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def operationsPart11 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:709:0,0,0,0,0,0,0;1/1:4951:-2,2,0,-2,0,0,0"
  | 1 => laurent_polynomial% "1/1:2531:0,0,0,0,0,0,0;-1/1:4600:-2,0,2,-2,0,0,0;-1/1:4792:0,0,0,0,0,0,0;-1/1:4951:-2,0,2,-2,0,0,0"
  | 2 => laurent_polynomial% "1/1:3348:0,0,0,0,0,0,0;-1/1:4616:-2,0,0,0,0,0,0;-1/1:4798:0,0,0,0,0,0,0;1/1:4950:-1,0,0,0,1,0,0"
  | 3 => laurent_polynomial% "-1/1:353:2,2,0,-2,0,0,0;1/1:4954:2,2,0,-2,0,0,0"
  | 4 => laurent_polynomial% "1/1:2889:0,0,0,0,0,0,0;-1/1:4647:-2,0,-2,0,0,0,0;-1/1:4648:-2,0,-2,0,0,0,0;-1/1:4652:-2,0,-2,0,0,0,0;-1/1:4682:0,0,0,0,0,0,0;-1/1:4691:0,0,0,0,0,0,0;-1/1:4739:0,0,0,0,0,0,0;-1/1:4778:0,0,0,0,0,0,0;-1/1:4801:-2,0,-2,0,0,0,0;-1/1:4802:-2,0,-2,0,0,0,0;-1/1:4804:-2,0,-2,0,0,0,0;-1/1:4821:-2,0,-2,0,0,0,0;-1/1:4824:-2,0,-2,0,0,0,0;-1/1:4859:0,0,0,0,0,0,0;-1/1:4866:0,0,0,0,0,0,0;-1/1:4954:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:3453:0,0,0,0,0,0,0;-1/1:4747:-2,0,0,0,0,0,0;1/1:4875:-1,0,0,0,1,0,0;-1/1:4956:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "-1/1:467:-2,2,0,-2,0,0,0;1/1:4957:-2,2,0,-2,0,0,0"
  | 7 => laurent_polynomial% "1/1:2601:0,0,0,0,0,0,0;-1/1:4716:0,0,0,0,0,0,0;-1/1:4798:0,0,0,0,0,0,0;-1/1:4803:2,-2,-2,0,0,0,0;-1/1:4809:2,-2,-2,0,0,0,0;-1/1:4820:2,-2,-2,0,0,0,0;-1/1:4831:2,-2,-2,0,0,0,0;-1/1:4957:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "-1/1:6:0,2,0,-2,0,0,0;1/1:4959:0,2,0,-2,0,0,0"
  | 9 => laurent_polynomial% "1/1:2539:0,0,0,0,0,0,0;-1/1:4726:0,0,2,-2,0,0,0;-1/1:4780:0,0,0,0,0,0,0;-1/1:4959:0,0,2,-2,0,0,0"
  | 10 => laurent_polynomial% "1/1:2934:0,0,0,0,0,0,0;-1/1:4603:0,0,0,0,0,0,0;-1/1:4630:0,0,0,0,0,0,0;-1/1:4675:0,0,0,0,0,0,0;-1/1:4685:0,0,0,0,0,0,0;-1/1:4764:0,0,0,0,0,0,0;-1/1:4793:0,0,0,0,0,0,0;-1/1:4851:0,0,0,0,0,0,0;-1/1:4876:0,0,0,0,0,0,0;-1/1:4898:0,0,0,0,0,0,0;-1/1:4919:0,0,0,0,0,0,0;-1/1:4961:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:2536:0,0,0,0,0,0,0;-1/1:4740:0,0,0,0,0,0,0;-1/1:4781:-2,0,-2,2,0,0,0;-1/1:4962:-2,0,-2,2,0,0,0"
  | 12 => laurent_polynomial% "1/1:3327:0,0,0,0,0,0,0;1/1:4794:-1,0,0,0,1,0,0;-1/1:4849:0,0,0,0,0,0,0;-1/1:4959:-2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:2581:0,0,0,0,0,0,0;-1/1:4647:-2,-2,-2,0,0,0,0;-1/1:4652:-2,-2,-2,0,0,0,0;-1/1:4775:0,0,0,0,0,0,0;-1/1:4801:-2,-2,-2,0,0,0,0;-1/1:4804:-2,-2,-2,0,0,0,0;-1/1:4911:0,0,0,0,0,0,0;-1/1:4964:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:3334:0,0,0,0,0,0,0;-1/1:4875:-2,0,0,0,0,0,0;-1/1:4914:0,0,0,0,0,0,0;1/1:4957:-1,0,0,0,1,0,0"
  | 15 => laurent_polynomial% "1/1:2965:0,0,0,0,0,0,0;-1/1:4600:-2,-2,0,0,0,0,0;-1/1:4601:-2,-2,0,0,0,0,0;-1/1:4617:-2,-2,0,0,0,0,0;-1/1:4619:-2,-2,0,0,0,0,0;-1/1:4622:-2,-2,0,0,0,0,0;-1/1:4623:-2,-2,0,0,0,0,0;-1/1:4646:0,0,0,0,0,0,0;-1/1:4647:-2,-2,0,0,0,0,0;-1/1:4652:-2,-2,0,0,0,0,0;-1/1:4666:-2,-2,0,0,0,0,0;-1/1:4667:0,0,0,0,0,0,0;-1/1:4683:-2,-2,0,0,0,0,0;-1/1:4684:0,0,0,0,0,0,0;-1/1:4696:-2,-2,0,0,0,0,0;-1/1:4697:-2,-2,0,0,0,0,0;-1/1:4704:-2,-2,0,0,0,0,0;-1/1:4719:0,0,0,0,0,0,0;-1/1:4726:-2,-2,0,0,0,0,0;-1/1:4728:0,0,0,0,0,0,0;-1/1:4756:-2,-2,0,0,0,0,0;-1/1:4760:0,0,0,0,0,0,0;-1/1:4783:-2,-2,0,0,0,0,0;-1/1:4801:-2,-2,0,0,0,0,0;-1/1:4804:-2,-2,0,0,0,0,0;-1/1:4834:0,0,0,0,0,0,0;-1/1:4836:0,0,0,0,0,0,0;-1/1:4837:0,0,0,0,0,0,0;-1/1:4860:-2,-2,0,0,0,0,0;-1/1:4865:-2,-2,0,0,0,0,0;-1/1:4868:0,0,0,0,0,0,0;-1/1:4880:0,0,0,0,0,0,0;-1/1:4890:0,0,0,0,0,0,0;-1/1:4918:0,0,0,0,0,0,0;-1/1:4944:0,0,0,0,0,0,0;-1/1:4945:0,0,0,0,0,0,0;-1/1:4948:0,0,0,0,0,0,0;-1/1:4949:0,0,0,0,0,0,0;-1/1:4963:0,0,0,0,0,0,0;-1/1:4966:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:3340:0,0,0,0,0,0,0;-1/1:4630:-2,0,0,0,0,0,0;-1/1:4961:0,0,0,0,0,0,0;1/1:4962:-1,0,0,0,1,0,0"
  | 17 => laurent_polynomial% "1/1:3465:0,0,0,0,0,0,0;1/1:4630:-1,0,0,0,1,0,0;-1/1:4675:-2,0,0,0,0,0,0;-1/1:4962:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3082:0,0,0,0,0,0,0;-1/1:4757:0,0,0,0,0,0,0;-1/1:4862:0,0,0,0,0,0,0;-1/1:4899:0,0,0,0,0,0,0;-1/1:4900:0,0,0,0,0,0,0;-1/1:4917:0,0,0,0,0,0,0;-1/1:4922:0,0,0,0,0,0,0;-1/1:4929:0,0,0,0,0,0,0;-1/1:4933:0,0,0,0,0,0,0;-1/1:4953:0,0,0,0,0,0,0;-1/1:4968:0,0,0,0,0,0,0;-1/1:4969:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:3707:2,0,0,0,0,0,0;-1/1:4737:2,0,0,0,0,0,0;-1/1:4952:2,0,0,0,0,0,0;1/1:4960:1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "1/1:2514:0,0,0,0,0,0,0;-1/1:4601:-2,0,-2,-2,0,0,0;-1/1:4702:-2,0,-2,-2,0,0,0"
  | 21 => laurent_polynomial% "1/1:2515:0,0,0,0,0,0,0;-1/1:4601:-2,0,-2,-2,0,0,0;-1/1:4693:-2,0,-2,-2,0,0,0"
  | 22 => laurent_polynomial% "1/1:2516:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,-2,0,0,0;-1/1:4693:0,0,-2,-2,0,0,0"
  | 23 => laurent_polynomial% "1/1:2517:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,-2,0,0,0;-1/1:4702:0,0,-2,-2,0,0,0"
  | 24 => laurent_polynomial% "1/1:2518:0,0,0,0,0,0,0;-1/1:4602:2,0,-2,-2,0,0,0;-1/1:4725:2,0,-2,-2,0,0,0"
  | 25 => laurent_polynomial% "1/1:2519:0,0,0,0,0,0,0;-1/1:4602:2,0,-2,-2,0,0,0;-1/1:4719:2,0,-2,-2,0,0,0"
  | 26 => laurent_polynomial% "1/1:2591:0,0,0,0,0,0,0;-1/1:4601:-2,0,0,-2,0,0,0;-1/1:4647:-2,0,0,-2,0,0,0;-1/1:4801:-2,0,0,-2,0,0,0;-1/1:4804:-2,0,0,-2,0,0,0;-1/1:4912:0,0,0,0,0,0,0;-1/1:4931:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:2592:0,0,0,0,0,0,0;-1/1:4601:-2,0,0,-2,0,0,0;-1/1:4652:-2,0,0,-2,0,0,0;-1/1:4791:0,0,0,0,0,0,0;-1/1:4801:-2,0,0,-2,0,0,0;-1/1:4804:-2,0,0,-2,0,0,0;-1/1:4893:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:2595:0,0,0,0,0,0,0;-1/1:4602:2,-2,0,-2,0,0,0;-1/1:4809:2,-2,0,-2,0,0,0;-1/1:4820:2,-2,0,-2,0,0,0;-1/1:4831:2,-2,0,-2,0,0,0;-1/1:4932:0,0,0,0,0,0,0;-1/1:4961:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:2596:0,0,0,0,0,0,0;-1/1:4602:2,-2,0,-2,0,0,0;-1/1:4803:2,-2,0,-2,0,0,0;-1/1:4820:2,-2,0,-2,0,0,0;-1/1:4831:2,-2,0,-2,0,0,0;-1/1:4876:0,0,0,0,0,0,0;-1/1:4892:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:2603:0,0,0,0,0,0,0;-1/1:4601:0,0,0,-2,0,0,0;-1/1:4647:0,0,0,-2,0,0,0;-1/1:4652:0,0,0,-2,0,0,0;-1/1:4748:0,0,0,0,0,0,0;-1/1:4801:0,0,0,-2,0,0,0;-1/1:4838:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:2604:0,0,0,0,0,0,0;-1/1:4601:0,0,0,-2,0,0,0;-1/1:4647:0,0,0,-2,0,0,0;-1/1:4652:0,0,0,-2,0,0,0;-1/1:4781:0,0,0,0,0,0,0;-1/1:4804:0,0,0,-2,0,0,0;-1/1:4840:0,0,0,0,0,0,0"
  | _ => []


}
certificate_batch {
compact_certificate def operationsPart12 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:2611:0,0,0,0,0,0,0;-1/1:4655:-2,2,0,-2,0,0,0;-1/1:4702:-2,2,0,-2,0,0,0;-1/1:4792:0,0,0,0,0,0,0;-1/1:4827:-2,2,0,-2,0,0,0;-1/1:4830:-2,2,0,-2,0,0,0;-1/1:4921:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:2612:0,0,0,0,0,0,0;-1/1:4648:-2,2,0,-2,0,0,0;-1/1:4693:-2,2,0,-2,0,0,0;-1/1:4821:-2,2,0,-2,0,0,0;-1/1:4824:-2,2,0,-2,0,0,0;-1/1:4848:0,0,0,0,0,0,0;-1/1:4916:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:2623:0,0,0,0,0,0,0;-1/1:4615:-2,0,2,-2,0,0,0;-1/1:4674:-2,0,2,-2,0,0,0;-1/1:4720:-2,0,2,-2,0,0,0;-1/1:4745:-2,0,2,-2,0,0,0;-1/1:4829:0,0,0,0,0,0,0;-1/1:4904:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:2624:0,0,0,0,0,0,0;-1/1:4622:-2,0,2,-2,0,0,0;-1/1:4683:-2,0,2,-2,0,0,0;-1/1:4726:-2,0,2,-2,0,0,0;-1/1:4783:-2,0,2,-2,0,0,0;-1/1:4825:0,0,0,0,0,0,0;-1/1:4903:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:2732:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,-2,0,0,0;-1/1:4702:0,0,-2,-2,0,0,0"
  | 5 => laurent_polynomial% "1/1:2733:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,-2,0,0,0;-1/1:4693:0,0,-2,-2,0,0,0"
  | 6 => laurent_polynomial% "1/1:2808:0,0,0,0,0,0,0;-1/1:4647:0,0,-2,-2,0,0,0;-1/1:4652:0,0,-2,-2,0,0,0;-1/1:4801:0,0,-2,-2,0,0,0;-1/1:4804:0,0,-2,-2,0,0,0;-1/1:4889:0,0,0,0,0,0,0;-1/1:4915:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:2809:0,0,0,0,0,0,0;-1/1:4647:0,0,-2,-2,0,0,0;-1/1:4652:0,0,-2,-2,0,0,0;-1/1:4690:0,0,0,0,0,0,0;-1/1:4801:0,0,-2,-2,0,0,0;-1/1:4804:0,0,-2,-2,0,0,0;-1/1:4934:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:2820:0,0,0,0,0,0,0;-1/1:4623:0,-2,2,-2,0,0,0;-1/1:4696:0,-2,2,-2,0,0,0;-1/1:4810:0,0,0,0,0,0,0;-1/1:4860:0,-2,2,-2,0,0,0;-1/1:4865:0,-2,2,-2,0,0,0;-1/1:4872:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:2821:0,0,0,0,0,0,0;-1/1:4600:0,-2,2,-2,0,0,0;-1/1:4666:0,-2,2,-2,0,0,0;-1/1:4704:0,-2,2,-2,0,0,0;-1/1:4756:0,-2,2,-2,0,0,0;-1/1:4816:0,0,0,0,0,0,0;-1/1:4885:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:2902:2,0,2,-2,0,0,0;-1/1:4626:2,0,2,-2,0,0,0;-1/1:4657:0,0,0,0,0,0,0;-1/1:4684:2,0,2,-2,0,0,0;-1/1:4728:2,0,2,-2,0,0,0;-1/1:4765:2,0,2,-2,0,0,0;-1/1:4814:0,0,0,0,0,0,0;-1/1:4840:0,0,0,0,0,0,0;-1/1:4846:0,0,0,0,0,0,0;-1/1:4906:2,0,2,-2,0,0,0;-1/1:4908:2,0,2,-2,0,0,0;-1/1:4966:2,0,2,-2,0,0,0;-1/1:4967:2,0,2,-2,0,0,0;-1/1:4983:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:2903:2,0,2,-2,0,0,0;-1/1:4613:2,0,2,-2,0,0,0;-1/1:4662:0,0,0,0,0,0,0;-1/1:4672:2,0,2,-2,0,0,0;-1/1:4723:2,0,2,-2,0,0,0;-1/1:4736:2,0,2,-2,0,0,0;-1/1:4808:0,0,0,0,0,0,0;-1/1:4838:0,0,0,0,0,0,0;-1/1:4839:0,0,0,0,0,0,0;-1/1:4852:2,0,2,-2,0,0,0;-1/1:4854:2,0,2,-2,0,0,0;-1/1:4943:2,0,2,-2,0,0,0;-1/1:4947:2,0,2,-2,0,0,0;-1/1:4982:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:3228:0,0,0,0,0,0,0;-1/1:4715:0,0,0,0,0,0,0;1/1:4895:-1,0,0,0,1,0,0"
  | 13 => laurent_polynomial% "1/1:3231:0,0,0,0,0,0,0;-1/1:4768:0,0,0,0,0,0,0;1/1:4926:-1,0,0,0,1,0,0"
  | 14 => laurent_polynomial% "1/1:3234:0,0,0,0,0,0,0;-1/1:4727:0,0,0,0,0,0,0;1/1:4742:-1,0,0,0,1,0,0"
  | 15 => laurent_polynomial% "1/1:3238:0,0,0,0,0,0,0;-1/1:4618:0,0,0,0,0,0,0;1/1:4679:-1,0,0,0,1,0,0"
  | 16 => laurent_polynomial% "1/1:3251:0,0,0,0,0,0,0;-1/1:4718:0,0,0,0,0,0,0;1/1:4732:-1,0,0,0,1,0,0"
  | 17 => laurent_polynomial% "1/1:3255:0,0,0,0,0,0,0;-1/1:4657:0,0,0,0,0,0,0;1/1:4816:-1,0,0,0,1,0,0"
  | 18 => laurent_polynomial% "1/1:3256:0,0,0,0,0,0,0;-1/1:4749:0,0,0,0,0,0,0;1/1:4759:-1,0,0,0,1,0,0"
  | 19 => laurent_polynomial% "1/1:3258:0,0,0,0,0,0,0;1/1:4750:-1,0,0,0,1,0,0;-1/1:4869:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:3259:0,0,0,0,0,0,0;1/1:4698:-1,0,0,0,1,0,0;-1/1:4711:0,0,0,0,0,0,0;-1/1:4988:-2,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:3263:0,0,0,0,0,0,0;-1/1:4858:0,0,0,0,0,0,0;1/1:4879:-1,0,0,0,1,0,0"
  | 22 => laurent_polynomial% "1/1:3266:2,0,0,0,0,0,0;1/1:4690:1,0,0,0,1,0,0;-1/1:4940:2,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:3269:0,0,0,0,0,0,0;-1/1:4855:0,0,0,0,0,0,0;1/1:4889:-1,0,0,0,1,0,0"
  | 24 => laurent_polynomial% "1/1:3275:0,0,0,0,0,0,0;-1/1:4832:0,0,0,0,0,0,0;1/1:4835:-1,0,0,0,1,0,0;-1/1:4982:-2,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:3281:0,0,0,0,0,0,0;-1/1:4755:0,0,0,0,0,0,0;1/1:4910:-1,0,0,0,1,0,0"
  | 26 => laurent_polynomial% "1/1:3293:0,0,0,0,0,0,0;-1/1:4730:0,0,0,0,0,0,0;1/1:4735:-1,0,0,0,1,0,0;-1/1:4991:-2,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "-1/1:3335:0,0,0,0,0,0,0;1/1:4826:-2,0,0,0,0,0,0;1/1:4835:0,0,0,0,0,0,0;1/1:4978:0,0,0,0,0,0,0;-1/1:4982:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "1/1:3347:0,0,0,0,0,0,0;-1/1:4612:-2,0,0,0,0,0,0;-1/1:4910:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "-1/1:3350:0,0,0,0,0,0,0;1/1:4653:-2,0,0,0,0,0,0;-1/1:4847:-1,0,0,0,1,0,0;1/1:4987:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:3400:0,0,0,0,0,0,0;1/1:4845:-1,0,0,0,1,0,0;-1/1:4885:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "-1/1:3410:0,0,0,0,0,0,0;1/1:4844:0,0,0,0,0,0,0;1/1:4883:-2,0,0,0,0,0,0;1/1:4979:0,0,0,0,0,0,0;-1/1:4983:-1,0,0,0,1,0,0"
  | _ => []
compact_certificate def operationsPart13 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3435:0,0,0,0,0,0,0;-1/1:4846:-2,0,0,0,0,0,0;1/1:4932:-1,0,0,0,1,0,0"
  | 1 => laurent_polynomial% "1/1:3458:0,0,0,0,0,0,0;1/1:4714:-1,0,0,0,1,0,0;-1/1:4721:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:3461:0,0,0,0,0,0,0;1/1:4737:-1,0,0,0,1,0,0;-1/1:4960:-2,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:3464:0,0,0,0,0,0,0;1/1:4787:-1,0,0,0,1,0,0;-1/1:4907:-2,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:3466:0,0,0,0,0,0,0;1/1:4639:-1,0,0,0,1,0,0;-1/1:4688:-2,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:3468:0,0,0,0,0,0,0;1/1:4724:-1,0,0,0,1,0,0;-1/1:4734:-2,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:3472:0,0,0,0,0,0,0;1/1:4668:-1,0,0,0,1,0,0;-1/1:4710:-2,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:3473:0,0,0,0,0,0,0;-1/1:4699:-2,0,0,0,0,0,0;1/1:4709:-1,0,0,0,1,0,0"
  | 8 => laurent_polynomial% "1/1:3475:0,0,0,0,0,0,0;-1/1:4663:-2,0,0,0,0,0,0;1/1:4813:-1,0,0,0,1,0,0"
  | 9 => laurent_polynomial% "1/1:3476:0,0,0,0,0,0,0;1/1:4631:-1,0,0,0,1,0,0;-1/1:4641:-2,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:3477:0,0,0,0,0,0,0;1/1:4633:-1,0,0,0,1,0,0;-1/1:4644:-2,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3478:0,0,0,0,0,0,0;-1/1:4605:-2,0,0,0,0,0,0;1/1:4634:-1,0,0,0,1,0,0"
  | 12 => laurent_polynomial% "1/1:3479:0,0,0,0,0,0,0;-1/1:4608:-2,0,0,0,0,0,0;1/1:4612:-1,0,0,0,1,0,0"
  | 13 => laurent_polynomial% "1/1:3480:0,0,0,0,0,0,0;-1/1:4650:-2,0,0,0,0,0,0;1/1:4812:-1,0,0,0,1,0,0"
  | 14 => laurent_polynomial% "1/1:3482:0,0,0,0,0,0,0;1/1:4692:-1,0,0,0,1,0,0;-1/1:4703:-2,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:3483:0,0,0,0,0,0,0;-1/1:4700:-2,0,0,0,0,0,0;1/1:4870:-1,0,0,0,1,0,0"
  | 16 => laurent_polynomial% "1/1:3487:0,0,0,0,0,0,0;1/1:4727:-1,0,0,0,1,0,0;-1/1:4742:-2,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:3489:0,0,0,0,0,0,0;1/1:4618:-1,0,0,0,1,0,0;-1/1:4679:-2,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3491:0,0,0,0,0,0,0;1/1:4746:-1,0,0,0,1,0,0;-1/1:4855:-2,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:3494:0,0,0,0,0,0,0;-1/1:4755:-2,0,0,0,0,0,0;1/1:4909:-1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "1/1:3497:0,0,0,0,0,0,0;1/1:4717:-1,0,0,0,1,0,0;-1/1:4730:-2,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "-1/1:3500:0,0,0,0,0,0,0;1/1:4651:-2,0,0,0,0,0,0;-1/1:4828:-1,0,0,0,1,0,0;1/1:4986:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:3520:0,0,0,0,0,0,0;-1/1:4839:-2,0,0,0,0,0,0;1/1:4892:-1,0,0,0,1,0,0"
  | 23 => laurent_polynomial% "1/1:3555:0,0,0,0,0,0,0;-1/1:4872:0,0,0,0,0,0,0;1/1:4882:-1,0,0,0,1,0,0"
  | 24 => laurent_polynomial% "1/1:3575:0,0,0,0,0,0,0;1/1:4844:-1,0,0,0,1,0,0;-1/1:4884:0,0,0,0,0,0,0;-1/1:4983:-2,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:3608:0,0,0,0,0,0,0;-1/1:4631:-2,0,0,0,0,0,0;-1/1:4971:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:3662:0,0,0,0,0,0,0;-1/1:4721:0,0,0,0,0,0,0;1/1:4743:-1,0,0,0,1,0,0"
  | 27 => laurent_polynomial% "1/1:3674:0,0,0,0,0,0,0;-1/1:4960:0,0,0,0,0,0,0;1/1:4971:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "1/1:3686:0,0,0,0,0,0,0;-1/1:4907:0,0,0,0,0,0,0;1/1:4934:-1,0,0,0,1,0,0"
  | 29 => laurent_polynomial% "1/1:3689:2,0,0,0,0,0,0;1/1:4915:1,0,0,0,1,0,0;-1/1:4958:2,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:3692:0,0,0,0,0,0,0;-1/1:4761:0,0,0,0,0,0,0;1/1:4770:-1,0,0,0,1,0,0"
  | 31 => laurent_polynomial% "1/1:3696:0,0,0,0,0,0,0;-1/1:4701:0,0,0,0,0,0,0;1/1:4707:-1,0,0,0,1,0,0;-1/1:4989:-2,0,0,0,0,0,0"
  | _ => []
compact_certificate def operationsPart14 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3697:0,0,0,0,0,0,0;-1/1:4669:0,0,0,0,0,0,0;1/1:4785:-1,0,0,0,1,0,0"
  | 1 => laurent_polynomial% "1/1:3699:0,0,0,0,0,0,0;-1/1:4786:0,0,0,0,0,0,0;1/1:4861:-1,0,0,0,1,0,0"
  | 2 => laurent_polynomial% "1/1:3700:0,0,0,0,0,0,0;-1/1:4662:0,0,0,0,0,0,0;1/1:4810:-1,0,0,0,1,0,0"
  | 3 => laurent_polynomial% "1/1:3704:0,0,0,0,0,0,0;-1/1:4729:0,0,0,0,0,0,0;1/1:4741:-1,0,0,0,1,0,0"
  | 4 => laurent_polynomial% "1/1:3717:0,0,0,0,0,0,0;-1/1:4639:0,0,0,0,0,0,0;1/1:4688:-1,0,0,0,1,0,0"
  | 5 => laurent_polynomial% "1/1:3721:0,0,0,0,0,0,0;-1/1:4724:0,0,0,0,0,0,0;1/1:4734:-1,0,0,0,1,0,0"
  | 6 => laurent_polynomial% "1/1:3723:2,0,0,0,0,0,0;-1/1:4676:2,0,0,0,0,0,0;-1/1:4771:2,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:3724:0,0,0,0,0,0,0;-1/1:4853:0,0,0,0,0,0,0;1/1:4891:-1,0,0,0,1,0,0"
  | 8 => laurent_polynomial% "1/1:3743:0,0,0,0,0,0,0;-1/1:4606:0,0,0,0,0,0,0;1/1:4695:0,-1,0,0,0,1,0;-1/1:4863:0,-2,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:3746:0,0,0,0,0,0,0;-1/1:4608:0,0,0,0,0,0,0;1/1:4703:0,-1,0,0,0,1,0;-1/1:4855:0,-2,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:3748:0,0,0,0,0,0,0;1/1:4671:0,-1,0,0,0,1,0;-1/1:4732:0,-2,0,0,0,0,0;-1/1:4927:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3749:0,0,0,0,0,0,0;-1/1:4637:0,-2,0,0,0,0,0;-1/1:4695:0,0,0,0,0,0,0;1/1:4863:0,-1,0,0,0,1,0"
  | 12 => laurent_polynomial% "1/1:3752:0,0,0,0,0,0,0;-1/1:4610:0,0,0,0,0,0,0;1/1:4718:0,-1,0,0,0,1,0;-1/1:4889:0,-2,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:3770:0,0,0,0,0,0,0;-1/1:4651:0,-1,0,0,0,1,0;1/1:4808:0,0,0,0,0,0,0;1/1:4847:0,-2,0,0,0,0,0;1/1:4995:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:3780:0,0,0,0,0,0,0;-1/1:4657:0,0,0,0,0,0,0;1/1:4835:0,-1,0,0,0,1,0;-1/1:4884:0,-2,0,0,0,0,0;-1/1:4983:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:3800:0,0,0,0,0,0,0;-1/1:4653:0,-2,0,0,0,0,0;-1/1:4832:0,0,0,0,0,0,0;1/1:4840:0,-1,0,0,0,1,0"
  | 16 => laurent_polynomial% "1/1:3820:0,0,0,0,0,0,0;-1/1:4816:0,0,0,0,0,0,0;-1/1:4844:0,-2,0,0,0,0,0;-1/1:4883:0,0,0,0,0,0,0;1/1:4982:0,-1,0,0,0,1,0"
  | 17 => laurent_polynomial% "-1/1:3825:0,0,0,0,0,0,0;1/1:4656:0,0,0,0,0,0,0;-1/1:4921:0,-1,0,0,0,1,0;1/1:4931:0,0,0,0,0,0,0;1/1:5013:0,-2,0,0,0,0,0;1/1:5024:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3830:0,0,0,0,0,0,0;-1/1:4651:0,0,0,0,0,0,0;1/1:4847:0,-1,0,0,0,1,0;-1/1:4932:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:3860:0,0,0,0,0,0,0;-1/1:4808:0,-2,0,0,0,0,0;-1/1:4835:0,0,0,0,0,0,0;1/1:4884:0,-1,0,0,0,1,0"
  | 20 => laurent_polynomial% "1/1:3885:0,0,0,0,0,0,0;-1/1:4829:0,0,0,0,0,0,0;-1/1:4921:0,-2,0,0,0,0,0;1/1:4931:0,-1,0,0,0,1,0"
  | 21 => laurent_polynomial% "1/1:3896:0,0,0,0,0,0,0;-1/1:4724:0,0,0,0,0,0,0;-1/1:4735:0,0,0,0,0,0,0;1/1:4955:0,-1,0,0,0,1,0"
  | 22 => laurent_polynomial% "-1/1:3905:2,0,0,0,0,0,0;-1/1:4829:2,-1,0,0,0,1,0;1/1:4833:2,0,0,0,0,0,0;1/1:4931:2,-2,0,0,0,0,0;1/1:4985:2,0,0,0,0,0,0;-1/1:5008:2,0,0,0,0,0,0;1/1:5039:2,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:3912:0,0,0,0,0,0,0;-1/1:4631:0,0,0,0,0,0,0;1/1:4709:0,-1,0,0,0,1,0;-1/1:4787:0,-2,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:3913:0,0,0,0,0,0,0;-1/1:4640:0,-2,0,0,0,0,0;1/1:4678:0,-1,0,0,0,1,0;-1/1:4937:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:3917:0,0,0,0,0,0,0;-1/1:4624:0,-2,0,0,0,0,0;1/1:4680:0,-1,0,0,0,1,0;-1/1:4928:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:3918:0,0,0,0,0,0,0;-1/1:4612:0,0,0,0,0,0,0;1/1:4692:0,-1,0,0,0,1,0;-1/1:4746:0,-2,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:3934:0,0,0,0,0,0,0;-1/1:4727:0,0,0,0,0,0,0;-1/1:4743:0,0,0,0,0,0,0;1/1:4946:0,-1,0,0,0,1,0"
  | 28 => laurent_polynomial% "1/1:3945:0,0,0,0,0,0,0;-1/1:4825:0,0,0,0,0,0,0;-1/1:4848:0,-2,0,0,0,0,0;1/1:4893:0,-1,0,0,0,1,0"
  | 29 => laurent_polynomial% "-1/1:3970:0,0,0,0,0,0,0;1/1:4814:0,-2,0,0,0,0,0;1/1:4843:0,0,0,0,0,0,0;-1/1:4871:0,-1,0,0,0,1,0;1/1:4980:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:4010:0,0,0,0,0,0,0;-1/1:4810:0,0,0,0,0,0,0;-1/1:4847:0,0,0,0,0,0,0;-1/1:4881:0,-2,0,0,0,0,0"
  | 31 => laurent_polynomial% "-1/1:4030:0,0,0,0,0,0,0;1/1:4661:0,-2,0,0,0,0,0;1/1:4822:0,0,0,0,0,0,0;-1/1:4838:0,-1,0,0,0,1,0;1/1:4993:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def operationsPart15 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:4060:0,0,0,0,0,0,0;1/1:4649:0,-1,0,0,0,1,0;-1/1:4814:0,0,0,0,0,0,0;-1/1:4883:0,-2,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:4078:0,0,0,0,0,0,0;-1/1:4636:0,0,0,0,0,0,0;1/1:4729:0,-1,0,0,0,1,0;-1/1:4934:0,-2,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:4081:0,0,0,0,0,0,0;-1/1:4628:0,-2,0,0,0,0,0;-1/1:4712:0,0,0,0,0,0,0;1/1:4762:0,-1,0,0,0,1,0"
  | 3 => laurent_polynomial% "1/1:4082:0,0,0,0,0,0,0;1/1:4686:0,-1,0,0,0,1,0;-1/1:4741:0,-2,0,0,0,0,0;-1/1:4935:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:4084:0,0,0,0,0,0,0;-1/1:4641:0,0,0,0,0,0,0;1/1:4699:0,-1,0,0,0,1,0;-1/1:4907:0,-2,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:4087:0,0,0,0,0,0,0;-1/1:4643:0,0,0,0,0,0,0;1/1:4712:0,-1,0,0,0,1,0;-1/1:4762:0,-2,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:4168:0,0,0,0,0,0,0;-1/1:4730:0,0,0,0,0,0,0;-1/1:4787:0,0,0,0,0,0,0;-1/1:4971:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:4175:0,0,0,0,0,0,0;-1/1:4656:0,0,0,0,0,0,0;-1/1:4817:0,0,0,0,0,0,0;-1/1:4929:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:4215:0,0,0,0,0,0,0;-1/1:4659:0,0,0,0,0,0,0;-1/1:4805:0,0,0,0,0,0,0;-1/1:4968:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:4222:0,0,0,0,0,0,0;-1/1:4721:0,0,0,0,0,0,0;-1/1:4746:0,0,0,0,0,0,0;-1/1:4910:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:4360:0,0,0,0,0,0,0;-1/1:4647:0,0,0,-2,0,0,0;-1/1:4649:0,0,0,0,0,0,0;-1/1:4652:0,0,0,0,0,0,0;-1/1:4661:0,0,0,0,0,0,0;1/1:4801:0,0,0,-1,0,0,1;-1/1:4832:0,0,0,0,0,0,0;-1/1:4884:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3370:0,0,0,0,0,0,0;-1/1:4882:0,0,0,0,0,0,0;1/1:5070:-1,0,0,0,1,0,0;-1/1:5078:-2,0,0,0,0,0,0;-1/1:5090:-1,0,0,0,1,0,0"
  | 12 => laurent_polynomial% "1/1:3585:0,0,0,0,0,0,0;-1/1:4845:0,0,0,0,0,0,0;1/1:5062:-1,0,0,0,1,0,0;-1/1:5064:-2,0,0,0,0,0,0;1/1:5090:-2,-1,0,0,0,1,0"
  | 13 => laurent_polynomial% "1/1:2577:0,0,0,0,0,0,0;-1/1:4601:-2,-2,0,-2,0,0,0;-1/1:4647:-2,-2,0,-2,0,0,0;-1/1:4652:-2,-2,0,-2,0,0,0;-1/1:4801:-2,-2,0,-2,0,0,0;-1/1:4970:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:2578:0,0,0,0,0,0,0;-1/1:4601:-2,-2,0,-2,0,0,0;-1/1:4647:-2,-2,0,-2,0,0,0;-1/1:4652:-2,-2,0,-2,0,0,0;-1/1:4804:-2,-2,0,-2,0,0,0;-1/1:4900:0,0,0,0,0,0,0;-1/1:5076:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:2585:0,0,0,0,0,0,0;-1/1:4601:0,-2,0,-2,0,0,0;-1/1:4652:0,-2,0,-2,0,0,0;-1/1:4793:0,0,0,0,0,0,0;-1/1:4801:0,-2,0,-2,0,0,0;-1/1:4804:0,-2,0,-2,0,0,0;-1/1:5064:0,0,0,0,0,0,0;1/1:5090:0,-1,0,0,0,1,0"
  | 16 => laurent_polynomial% "1/1:2586:0,0,0,0,0,0,0;-1/1:4601:0,-2,0,-2,0,0,0;-1/1:4647:0,-2,0,-2,0,0,0;-1/1:4801:0,-2,0,-2,0,0,0;-1/1:4804:0,-2,0,-2,0,0,0;-1/1:4898:0,0,0,0,0,0,0;-1/1:5078:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:2615:0,0,0,0,0,0,0;-1/1:4622:0,-2,2,-2,0,0,0;-1/1:4697:0,-2,2,-2,0,0,0;-1/1:4726:0,-2,2,-2,0,0,0;-1/1:4783:0,-2,2,-2,0,0,0;-1/1:4882:0,0,0,0,0,0,0;-1/1:5065:0,0,0,0,0,0,0;-1/1:5090:0,-2,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:2616:0,0,0,0,0,0,0;-1/1:4615:0,-2,2,-2,0,0,0;-1/1:4706:0,-2,2,-2,0,0,0;-1/1:4720:0,-2,2,-2,0,0,0;-1/1:4745:0,-2,2,-2,0,0,0;-1/1:4845:0,0,0,0,0,0,0;-1/1:5066:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:2631:0,0,0,0,0,0,0;-1/1:4626:2,-2,2,-2,0,0,0;-1/1:4740:2,-2,2,-2,0,0,0;-1/1:4813:0,0,0,0,0,0,0;-1/1:4906:2,-2,2,-2,0,0,0;-1/1:4908:2,-2,2,-2,0,0,0;-1/1:5070:0,0,0,0,0,0,0;1/1:5090:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:2632:0,0,0,0,0,0,0;-1/1:4613:2,-2,2,-2,0,0,0;-1/1:4733:2,-2,2,-2,0,0,0;-1/1:4736:2,-2,2,-2,0,0,0;-1/1:4812:0,0,0,0,0,0,0;-1/1:4854:2,-2,2,-2,0,0,0;-1/1:5062:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "-1/1:2771:0,0,0,0,0,0,0;1/1:4603:0,2,-2,0,0,0,0;1/1:4683:0,0,0,0,0,0,0;1/1:4702:0,2,-2,0,0,0,0;1/1:4764:0,2,-2,0,0,0,0;1/1:4793:0,2,-2,0,0,0,0;1/1:4876:0,2,-2,0,0,0,0;1/1:4955:0,0,0,0,0,0,0;1/1:4962:0,2,-2,0,0,0,0;1/1:4971:0,0,0,0,0,0,0;1/1:4990:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:2772:0,0,0,0,0,0,0;-1/1:4630:0,2,-2,0,0,0,0;-1/1:4674:0,0,0,0,0,0,0;-1/1:4693:0,2,-2,0,0,0,0;-1/1:4851:0,2,-2,0,0,0,0;-1/1:4898:0,2,-2,0,0,0,0;-1/1:4910:0,0,0,0,0,0,0;-1/1:4919:0,2,-2,0,0,0,0;-1/1:4946:0,0,0,0,0,0,0;-1/1:4961:0,2,-2,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:2814:0,0,0,0,0,0,0;-1/1:4648:0,2,-2,-2,0,0,0;-1/1:4770:0,0,0,0,0,0,0;-1/1:4802:0,2,-2,-2,0,0,0;-1/1:4821:0,2,-2,-2,0,0,0;-1/1:4824:0,2,-2,-2,0,0,0"
  | 24 => laurent_polynomial% "1/1:2815:0,0,0,0,0,0,0;-1/1:4655:0,2,-2,-2,0,0,0;-1/1:4799:0,2,-2,-2,0,0,0;-1/1:4827:0,2,-2,-2,0,0,0;-1/1:4830:0,2,-2,-2,0,0,0;-1/1:4879:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:2863:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,0,0,0,0;-1/1:4665:0,0,-2,0,0,0,0;-1/1:4730:0,0,0,0,0,0,0;-1/1:4741:0,0,0,0,0,0,0;-1/1:4780:0,0,-2,0,0,0,0;-1/1:4781:0,0,-2,0,0,0,0;-1/1:4783:0,0,0,0,0,0,0;-1/1:4867:0,0,-2,0,0,0,0;-1/1:4873:0,0,-2,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:2864:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,0,0,0,0;-1/1:4665:0,0,-2,0,0,0,0;-1/1:4721:0,0,0,0,0,0,0;-1/1:4732:0,0,0,0,0,0,0;-1/1:4745:0,0,0,0,0,0,0;-1/1:4748:0,0,-2,0,0,0,0;-1/1:4780:0,0,-2,0,0,0,0;-1/1:4867:0,0,-2,0,0,0,0;-1/1:4873:0,0,-2,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:3232:0,0,0,0,0,0,0;-1/1:4878:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:3241:0,0,0,0,0,0,0;-1/1:4895:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:3244:0,0,0,0,0,0,0;-1/1:4753:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:3247:0,0,0,0,0,0,0;-1/1:4926:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:3253:0,0,0,0,0,0,0;-1/1:4742:0,0,0,0,0,0,0"
  | _ => []

compact_certificate def operationsPart16 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3261:0,0,0,0,0,0,0;-1/1:4679:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:3287:0,0,0,0,0,0,0;-1/1:4732:0,0,0,0,0,0,0;-1/1:5086:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:3296:2,0,0,0,0,0,0;-1/1:4637:2,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:3297:0,0,0,0,0,0,0;-1/1:4759:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:3298:0,0,0,0,0,0,0;-1/1:4687:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:3301:0,0,0,0,0,0,0;-1/1:4750:0,0,0,0,0,0,0;-1/1:5084:-2,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:3302:0,0,0,0,0,0,0;-1/1:4620:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:3303:0,0,0,0,0,0,0;-1/1:4698:0,0,0,0,0,0,0;-1/1:4974:-2,0,0,0,0,0,0;1/1:4988:-1,0,0,0,1,0,0"
  | 8 => laurent_polynomial% "1/1:3308:2,0,0,0,0,0,0;-1/1:4797:2,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:3311:0,0,0,0,0,0,0;-1/1:4879:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:3317:0,0,0,0,0,0,0;-1/1:4690:0,0,0,0,0,0,0;1/1:5006:-1,0,0,0,1,0,0"
  | 11 => laurent_polynomial% "1/1:3323:0,0,0,0,0,0,0;-1/1:4889:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:3332:0,0,0,0,0,0,0;-1/1:4955:-2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:3338:0,0,0,0,0,0,0;-1/1:4737:-2,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:3342:0,0,0,0,0,0,0;-1/1:4771:-2,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:3344:0,0,0,0,0,0,0;-1/1:4709:-2,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:3345:0,0,0,0,0,0,0;-1/1:4813:-2,0,0,0,0,0,0;-1/1:4992:0,0,0,0,0,0,0;1/1:5063:0,0,0,0,0,0,0;1/1:5065:-1,0,0,0,1,0,0;1/1:5090:-1,-2,0,0,1,0,0"
  | 17 => laurent_polynomial% "1/1:3346:0,0,0,0,0,0,0;-1/1:4633:-2,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3349:0,0,0,0,0,0,0;-1/1:4870:-2,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:3351:0,0,0,0,0,0,0;-1/1:4727:-2,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:3352:0,0,0,0,0,0,0;-1/1:4618:-2,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:3353:0,0,0,0,0,0,0;-1/1:4746:-2,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:3356:0,0,0,0,0,0,0;-1/1:4717:-2,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:3449:0,0,0,0,0,0,0;1/1:4955:-1,0,0,0,1,0,0"
  | 24 => laurent_polynomial% "1/1:3452:0,0,0,0,0,0,0;-1/1:4915:-2,0,0,0,0,0,0;-1/1:5089:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:3456:0,0,0,0,0,0,0;-1/1:4785:-2,0,0,0,0,0,0;1/1:5048:-1,0,0,0,1,0,0"
  | 26 => laurent_polynomial% "1/1:3457:0,0,0,0,0,0,0;-1/1:4861:-2,0,0,0,0,0,0;1/1:5049:-1,0,0,0,1,0,0"
  | 27 => laurent_polynomial% "1/1:3469:0,0,0,0,0,0,0;1/1:4771:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "1/1:3471:0,0,0,0,0,0,0;-1/1:4774:-2,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:3484:0,0,0,0,0,0,0;-1/1:4895:-2,0,0,0,0,0,0;1/1:4996:-1,0,0,0,1,0,0"
  | 30 => laurent_polynomial% "1/1:3486:0,0,0,0,0,0,0;1/1:4878:-1,0,0,0,1,0,0"
  | 31 => laurent_polynomial% "1/1:3498:0,0,0,0,0,0,0;-1/1:4759:-2,0,0,0,0,0,0;1/1:5002:-1,0,0,0,1,0,0"
  | _ => []
compact_certificate def operationsPart17 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3499:0,0,0,0,0,0,0;-1/1:4750:-2,0,0,0,0,0,0;1/1:5003:-1,0,0,0,1,0,0"
  | 1 => laurent_polynomial% "1/1:3503:0,0,0,0,0,0,0;-1/1:4690:-2,0,0,0,0,0,0;-1/1:5086:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:3525:0,0,0,0,0,0,0;-1/1:4981:-2,0,0,0,0,0,0;1/1:5067:-2,0,0,0,0,0,0;-1/1:5070:0,0,0,0,0,0,0;1/1:5078:-1,0,0,0,1,0,0;1/1:5090:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:3599:0,0,0,0,0,0,0;-1/1:4714:-2,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:3602:0,0,0,0,0,0,0;-1/1:4787:-2,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:3603:0,0,0,0,0,0,0;-1/1:4639:-2,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:3604:0,0,0,0,0,0,0;-1/1:4724:-2,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:3606:0,0,0,0,0,0,0;-1/1:4668:-2,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:3609:0,0,0,0,0,0,0;-1/1:4634:-2,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:3610:0,0,0,0,0,0,0;-1/1:4812:-2,0,0,0,0,0,0;1/1:5066:-1,0,0,0,1,0,0;-1/1:5079:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:3611:0,0,0,0,0,0,0;-1/1:4692:-2,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3613:0,0,0,0,0,0,0;-1/1:4878:-2,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:3617:0,0,0,0,0,0,0;-1/1:4909:-2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:3623:0,0,0,0,0,0,0;-1/1:4946:-2,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:3632:0,0,0,0,0,0,0;-1/1:4934:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:3638:0,0,0,0,0,0,0;-1/1:4915:0,0,0,0,0,0,0;1/1:5045:-1,0,0,0,1,0,0"
  | 16 => laurent_polynomial% "1/1:3644:0,0,0,0,0,0,0;-1/1:4770:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:3647:2,0,0,0,0,0,0;-1/1:4857:2,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3652:0,0,0,0,0,0,0;-1/1:4707:0,0,0,0,0,0,0;-1/1:4975:-2,0,0,0,0,0,0;1/1:4989:-1,0,0,0,1,0,0"
  | 19 => laurent_polynomial% "1/1:3653:0,0,0,0,0,0,0;-1/1:4629:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:3654:0,0,0,0,0,0,0;-1/1:4785:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:3657:0,0,0,0,0,0,0;-1/1:4677:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:3658:0,0,0,0,0,0,0;-1/1:4861:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:3659:2,0,0,0,0,0,0;-1/1:4628:2,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:3668:0,0,0,0,0,0,0;-1/1:4741:0,0,0,0,0,0,0;-1/1:5089:-2,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:3683:0,0,0,0,0,0,0;-1/1:4955:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:3694:0,0,0,0,0,0,0;-1/1:4688:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:3702:0,0,0,0,0,0,0;-1/1:4734:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:3706:0,0,0,0,0,0,0;1/1:5054:-1,0,0,0,1,0,0"
  | 29 => laurent_polynomial% "1/1:3708:0,0,0,0,0,0,0;-1/1:4891:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:3711:0,0,0,0,0,0,0;-1/1:4789:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:3714:0,0,0,0,0,0,0;-1/1:4774:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def operationsPart18 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3727:0,0,0,0,0,0,0;1/1:4774:-1,0,0,0,1,0,0"
  | 1 => laurent_polynomial% "1/1:3751:0,0,0,0,0,0,0;1/1:4887:0,-1,0,0,0,1,0;-1/1:4888:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:3755:0,0,0,0,0,0,0;-1/1:4654:0,0,0,0,0,0,0;1/1:4800:0,-1,0,0,0,1,0;-1/1:4987:0,-2,0,0,0,0,0;1/1:5013:0,-2,0,0,0,0,0;1/1:5090:0,-2,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:3756:0,0,0,0,0,0,0;-1/1:4768:0,0,0,0,0,0,0;1/1:4858:0,-1,0,0,0,1,0"
  | 4 => laurent_polynomial% "1/1:3758:0,0,0,0,0,0,0;-1/1:4703:0,0,0,0,0,0,0;1/1:4855:0,-1,0,0,0,1,0"
  | 5 => laurent_polynomial% "1/1:3764:0,0,0,0,0,0,0;-1/1:4671:0,0,0,0,0,0,0;1/1:4732:0,-1,0,0,0,1,0"
  | 6 => laurent_polynomial% "1/1:3767:0,0,0,0,0,0,0;1/1:4637:0,-1,0,0,0,1,0;-1/1:4863:0,0,0,0,0,0,0;-1/1:5017:0,-2,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:3769:0,0,0,0,0,0,0;1/1:4620:0,-1,0,0,0,1,0;-1/1:4753:0,0,0,0,0,0,0;-1/1:5025:0,-2,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:3784:0,0,0,0,0,0,0;-1/1:4711:0,0,0,0,0,0,0;1/1:4910:0,-1,0,0,0,1,0"
  | 9 => laurent_polynomial% "1/1:3792:0,0,0,0,0,0,0;1/1:4735:0,-1,0,0,0,1,0;-1/1:4955:0,-2,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:3794:0,0,0,0,0,0,0;-1/1:4714:0,-2,0,0,0,0,0;-1/1:4855:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3795:0,0,0,0,0,0,0;-1/1:4829:0,-2,0,0,0,0,0;1/1:4985:0,-1,0,0,0,1,0;-1/1:5008:0,-1,0,0,0,1,0;-1/1:5015:0,0,0,0,0,0,0;-1/1:5090:-2,-1,0,0,0,1,0"
  | 12 => laurent_polynomial% "1/1:3835:0,0,0,0,0,0,0;-1/1:4848:0,0,0,0,0,0,0;1/1:4986:0,-1,0,0,0,1,0;-1/1:5011:0,-2,0,0,0,0,0;-1/1:5037:0,-1,0,0,0,1,0;-1/1:5090:-1,-2,0,0,1,0,0"
  | 13 => laurent_polynomial% "1/1:3855:0,0,0,0,0,0,0;-1/1:4658:0,-2,0,0,0,0,0;1/1:4903:0,-1,0,0,0,1,0;-1/1:4984:0,0,0,0,0,0,0;1/1:5040:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:3858:0,0,0,0,0,0,0;-1/1:4610:0,-2,0,0,0,0,0;-1/1:4955:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:3904:0,0,0,0,0,0,0;-1/1:4668:0,0,0,0,0,0,0;1/1:4737:0,-1,0,0,0,1,0"
  | 16 => laurent_polynomial% "1/1:3906:0,0,0,0,0,0,0;-1/1:4709:0,0,0,0,0,0,0;1/1:4787:0,-1,0,0,0,1,0"
  | 17 => laurent_polynomial% "1/1:3909:0,0,0,0,0,0,0;1/1:4640:0,-1,0,0,0,1,0;-1/1:4678:0,0,0,0,0,0,0;-1/1:5044:0,-2,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3911:0,0,0,0,0,0,0;1/1:4767:0,-1,0,0,0,1,0;-1/1:4936:0,0,0,0,0,0,0;-1/1:5051:0,-2,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:3919:0,0,0,0,0,0,0;-1/1:4758:0,0,0,0,0,0,0;1/1:4850:0,-1,0,0,0,1,0;-1/1:5000:0,-2,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:3921:0,0,0,0,0,0,0;1/1:4624:0,-1,0,0,0,1,0;-1/1:4680:0,0,0,0,0,0,0;-1/1:5007:0,-2,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:3924:0,0,0,0,0,0,0;-1/1:4692:0,0,0,0,0,0,0;1/1:4746:0,-1,0,0,0,1,0"
  | 22 => laurent_polynomial% "1/1:3926:0,0,0,0,0,0,0;-1/1:4870:0,0,0,0,0,0,0;1/1:4909:0,-1,0,0,0,1,0"
  | 23 => laurent_polynomial% "1/1:3972:0,0,0,0,0,0,0;-1/1:4636:0,-2,0,0,0,0,0;-1/1:4946:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:3975:0,0,0,0,0,0,0;-1/1:4654:0,-2,0,0,0,0,0;1/1:4904:0,-1,0,0,0,1,0;-1/1:5008:0,0,0,0,0,0,0;-1/1:5090:-2,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:3995:0,0,0,0,0,0,0;-1/1:4921:0,0,0,0,0,0,0;-1/1:4979:0,-2,0,0,0,0,0;1/1:5013:0,-1,0,0,0,1,0;1/1:5015:0,-2,0,0,0,0,0;1/1:5090:0,-1,0,0,0,1,0"
  | 26 => laurent_polynomial% "1/1:4025:0,0,0,0,0,0,0;-1/1:4984:0,-2,0,0,0,0,0;-1/1:4986:0,0,0,0,0,0,0;1/1:5011:0,-1,0,0,0,1,0;1/1:5037:0,0,0,0,0,0,0;1/1:5040:0,-2,0,0,0,0,0;1/1:5090:-1,-1,0,0,1,1,0"
  | 27 => laurent_polynomial% "1/1:4035:0,0,0,0,0,0,0;-1/1:4825:0,-2,0,0,0,0,0;-1/1:4978:0,0,0,0,0,0,0;1/1:5011:0,0,0,0,0,0,0;1/1:5040:0,-1,0,0,0,1,0;-1/1:5087:0,0,0,0,0,0,0;1/1:5090:-1,0,0,0,1,0,0;1/1:5178:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:4036:0,0,0,0,0,0,0;-1/1:4717:0,-2,0,0,0,0,0;-1/1:4907:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:4038:0,0,0,0,0,0,0;1/1:4743:0,-1,0,0,0,1,0;-1/1:4946:0,-2,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:4061:0,0,0,0,0,0,0;1/1:4629:0,-1,0,0,0,1,0;-1/1:4789:0,0,0,0,0,0,0;-1/1:5028:0,-2,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:4063:0,0,0,0,0,0,0;1/1:4628:0,-1,0,0,0,1,0;-1/1:4762:0,0,0,0,0,0,0;-1/1:5036:0,-2,0,0,0,0,0"
  | _ => []
compact_certificate def operationsPart19 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:4066:0,0,0,0,0,0,0;-1/1:4686:0,0,0,0,0,0,0;1/1:4741:0,-1,0,0,0,1,0"
  | 1 => laurent_polynomial% "1/1:4072:0,0,0,0,0,0,0;-1/1:4699:0,0,0,0,0,0,0;1/1:4907:0,-1,0,0,0,1,0"
  | 2 => laurent_polynomial% "1/1:4073:0,0,0,0,0,0,0;-1/1:4676:0,0,0,0,0,0,0;1/1:4958:0,-1,0,0,0,1,0"
  | 3 => laurent_polynomial% "1/1:4074:0,0,0,0,0,0,0;1/1:4761:0,-1,0,0,0,1,0;-1/1:4853:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:4075:0,0,0,0,0,0,0;-1/1:4658:0,0,0,0,0,0,0;1/1:4811:0,-1,0,0,0,1,0;-1/1:5037:0,-2,0,0,0,0,0;-1/1:5088:0,0,0,0,0,0,0;1/1:5187:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:4079:0,0,0,0,0,0,0;-1/1:4744:0,0,0,0,0,0,0;1/1:4952:0,-1,0,0,0,1,0"
  | 6 => laurent_polynomial% "1/1:4144:0,0,0,0,0,0,0;-1/1:4743:0,0,0,0,0,0,0;-1/1:4855:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:2968:0,0,0,0,0,0,0;-1/1:4602:2,0,0,-2,0,0,0;-1/1:4613:2,0,0,-2,0,0,0;-1/1:4626:2,0,0,-2,0,0,0;-1/1:4673:2,0,0,-2,0,0,0;-1/1:4705:2,0,0,-2,0,0,0;-1/1:4709:0,0,0,0,0,0,0;-1/1:4733:2,0,0,-2,0,0,0;-1/1:4736:2,0,0,-2,0,0,0;-1/1:4738:2,0,0,-2,0,0,0;-1/1:4740:2,0,0,-2,0,0,0;-1/1:4741:0,0,0,0,0,0,0;-1/1:4743:0,0,0,0,0,0,0;-1/1:4765:2,0,0,-2,0,0,0;-1/1:4781:0,0,0,0,0,0,0;-1/1:4803:2,0,0,-2,0,0,0;-1/1:4809:2,0,0,-2,0,0,0;-1/1:4814:0,0,0,0,0,0,0;-1/1:4820:2,0,0,-2,0,0,0;-1/1:4831:2,0,0,-2,0,0,0;-1/1:4840:0,0,0,0,0,0,0;-1/1:4852:2,0,0,-2,0,0,0;-1/1:4854:2,0,0,-2,0,0,0;-1/1:4855:0,0,0,0,0,0,0;-1/1:4874:2,0,0,-2,0,0,0;-1/1:4877:2,0,0,-2,0,0,0;-1/1:4879:0,0,0,0,0,0,0;-1/1:4906:2,0,0,-2,0,0,0;-1/1:4908:2,0,0,-2,0,0,0;-1/1:4909:0,0,0,0,0,0,0;-1/1:4983:0,0,0,0,0,0,0;-1/1:5104:0,0,0,0,0,0,0;-1/1:5214:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:4156:0,0,0,0,0,0,0;-1/1:4714:0,0,0,0,0,0,0;-1/1:4755:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:4162:0,0,0,0,0,0,0;-1/1:4732:0,0,0,0,0,0,0;-1/1:4737:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:2969:0,0,0,0,0,0,0;-1/1:4602:2,0,0,-2,0,0,0;-1/1:4613:2,0,0,-2,0,0,0;-1/1:4626:2,0,0,-2,0,0,0;-1/1:4682:2,0,0,-2,0,0,0;-1/1:4691:2,0,0,-2,0,0,0;-1/1:4692:0,0,0,0,0,0,0;-1/1:4732:0,0,0,0,0,0,0;-1/1:4733:2,0,0,-2,0,0,0;-1/1:4735:0,0,0,0,0,0,0;-1/1:4736:2,0,0,-2,0,0,0;-1/1:4737:0,0,0,0,0,0,0;-1/1:4739:2,0,0,-2,0,0,0;-1/1:4740:2,0,0,-2,0,0,0;-1/1:4748:0,0,0,0,0,0,0;-1/1:4765:2,0,0,-2,0,0,0;-1/1:4769:2,0,0,-2,0,0,0;-1/1:4770:0,0,0,0,0,0,0;-1/1:4778:2,0,0,-2,0,0,0;-1/1:4803:2,0,0,-2,0,0,0;-1/1:4808:0,0,0,0,0,0,0;-1/1:4809:2,0,0,-2,0,0,0;-1/1:4820:2,0,0,-2,0,0,0;-1/1:4831:2,0,0,-2,0,0,0;-1/1:4838:0,0,0,0,0,0,0;-1/1:4852:2,0,0,-2,0,0,0;-1/1:4854:2,0,0,-2,0,0,0;-1/1:4906:2,0,0,-2,0,0,0;-1/1:4907:0,0,0,0,0,0,0;-1/1:4908:2,0,0,-2,0,0,0;-1/1:4982:0,0,0,0,0,0,0;-1/1:5103:0,0,0,0,0,0,0;-1/1:5217:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:4172:0,0,0,0,0,0,0;-1/1:4639:0,0,0,0,0,0,0;-1/1:4759:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:4218:0,0,0,0,0,0,0;-1/1:4618:0,0,0,0,0,0,0;-1/1:4861:0,0,0,0,0,0,0;-1/1:5081:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:4234:0,0,0,0,0,0,0;-1/1:4717:0,0,0,0,0,0,0;-1/1:4960:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:4348:0,0,0,0,0,0,0;-1/1:4720:0,0,0,-2,0,0,0;-1/1:4726:0,0,0,0,0,0,0;1/1:4756:0,0,0,-1,0,0,1;-1/1:4787:0,0,0,0,0,0,0;-1/1:4858:0,0,0,0,0,0,0;-1/1:4915:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:4402:0,0,0,0,0,0,0;-1/1:4690:0,0,0,0,0,0,0;-1/1:4720:0,0,0,0,0,0,0;-1/1:4726:0,0,0,-2,0,0,0;-1/1:4746:0,0,0,0,0,0,0;-1/1:4761:0,0,0,0,0,0,0;1/1:4860:0,0,0,-1,0,0,1"
  | 16 => laurent_polynomial% "1/1:2569:0,0,0,0,0,0,0;-1/1:4647:-2,-2,-2,-2,0,0,0;-1/1:4652:-2,-2,-2,-2,0,0,0;-1/1:4801:-2,-2,-2,-2,0,0,0;-1/1:4804:-2,-2,-2,-2,0,0,0"
  | 17 => laurent_polynomial% "1/1:2570:0,0,0,0,0,0,0;-1/1:4647:-2,-2,-2,-2,0,0,0;-1/1:4652:-2,-2,-2,-2,0,0,0;-1/1:4801:-2,-2,-2,-2,0,0,0;-1/1:4804:-2,-2,-2,-2,0,0,0"
  | 18 => laurent_polynomial% "1/1:2571:0,0,0,0,0,0,0;-1/1:4647:0,-2,-2,-2,0,0,0;-1/1:4652:0,-2,-2,-2,0,0,0;-1/1:4801:0,-2,-2,-2,0,0,0;-1/1:4804:0,-2,-2,-2,0,0,0"
  | 19 => laurent_polynomial% "1/1:2572:0,0,0,0,0,0,0;-1/1:4647:0,-2,-2,-2,0,0,0;-1/1:4652:0,-2,-2,-2,0,0,0;-1/1:4801:0,-2,-2,-2,0,0,0;-1/1:4804:0,-2,-2,-2,0,0,0"
  | 20 => laurent_polynomial% "1/1:2575:0,0,0,0,0,0,0;-1/1:4803:2,-2,-2,-2,0,0,0;-1/1:4809:2,-2,-2,-2,0,0,0;-1/1:4820:2,-2,-2,-2,0,0,0;-1/1:4831:2,-2,-2,-2,0,0,0"
  | 21 => laurent_polynomial% "1/1:2576:0,0,0,0,0,0,0;-1/1:4803:2,-2,-2,-2,0,0,0;-1/1:4809:2,-2,-2,-2,0,0,0;-1/1:4820:2,-2,-2,-2,0,0,0;-1/1:4831:2,-2,-2,-2,0,0,0"
  | 22 => laurent_polynomial% "1/1:2579:0,0,0,0,0,0,0;-1/1:4647:0,0,-2,-2,0,0,0;-1/1:4652:0,0,-2,-2,0,0,0;-1/1:4801:0,0,-2,-2,0,0,0;-1/1:4804:0,0,-2,-2,0,0,0;-1/1:5045:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:2580:0,0,0,0,0,0,0;-1/1:4647:0,0,-2,-2,0,0,0;-1/1:4652:0,0,-2,-2,0,0,0;-1/1:4801:0,0,-2,-2,0,0,0;-1/1:4804:0,0,-2,-2,0,0,0;-1/1:5006:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:2599:0,0,0,0,0,0,0;-1/1:4600:-2,-2,2,-2,0,0,0;-1/1:4619:-2,-2,2,-2,0,0,0;-1/1:4666:-2,-2,2,-2,0,0,0;-1/1:4704:-2,-2,2,-2,0,0,0;-1/1:5039:0,0,0,0,0,0,0;1/1:5070:-2,0,0,0,0,0,0;-1/1:5090:-2,0,0,0,0,0,0;-1/1:5128:0,0,0,0,0,0,0;-1/1:5200:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:2600:0,0,0,0,0,0,0;-1/1:4617:-2,-2,2,-2,0,0,0;-1/1:4623:-2,-2,2,-2,0,0,0;-1/1:4696:-2,-2,2,-2,0,0,0;-1/1:4865:-2,-2,2,-2,0,0,0;-1/1:5014:0,0,0,0,0,0,0;1/1:5062:-2,0,0,0,0,0,0;-1/1:5153:0,0,0,0,0,0,0;-1/1:5201:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:2607:0,0,0,0,0,0,0;-1/1:4646:2,2,-2,-2,0,0,0;-1/1:4834:2,2,-2,-2,0,0,0;-1/1:4836:2,2,-2,-2,0,0,0;-1/1:4837:2,2,-2,-2,0,0,0"
  | 27 => laurent_polynomial% "1/1:2608:0,0,0,0,0,0,0;-1/1:4660:2,2,-2,-2,0,0,0;-1/1:4823:2,2,-2,-2,0,0,0;-1/1:4841:2,2,-2,-2,0,0,0;-1/1:4842:2,2,-2,-2,0,0,0"
  | 28 => laurent_polynomial% "1/1:2765:0,0,0,0,0,0,0;-1/1:4652:0,-2,0,0,0,0,0;-1/1:4661:0,-2,0,0,0,0,0;-1/1:4830:0,0,0,0,0,0,0;-1/1:4832:0,-2,0,0,0,0,0;-1/1:4884:0,-2,0,0,0,0,0;-1/1:4892:0,0,0,0,0,0,0;-1/1:4994:0,0,0,0,0,0,0;-1/1:5063:0,0,0,0,0,0,0;-1/1:5070:0,0,0,0,0,0,0;1/1:5080:0,0,0,0,0,0,0;-1/1:5090:0,-2,0,0,0,0,0;1/1:5090:0,0,0,0,0,0,0;-1/1:5098:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:2766:0,0,0,0,0,0,0;-1/1:4647:0,-2,0,0,0,0,0;-1/1:4653:0,-2,0,0,0,0,0;-1/1:4821:0,0,0,0,0,0,0;-1/1:4822:0,-2,0,0,0,0,0;-1/1:4871:0,-2,0,0,0,0,0;-1/1:4932:0,0,0,0,0,0,0;-1/1:4982:0,-2,0,0,0,0,0;-1/1:4983:0,-2,0,0,0,0,0;-1/1:4993:0,0,0,0,0,0,0;-1/1:5061:0,0,0,0,0,0,0;-1/1:5062:0,0,0,0,0,0,0;1/1:5079:0,0,0,0,0,0,0;1/1:5090:0,-2,0,0,0,0,0;-1/1:5097:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:2806:0,0,0,0,0,0,0;-1/1:4647:0,-2,-2,-2,0,0,0;-1/1:4652:0,-2,-2,-2,0,0,0;-1/1:4801:0,-2,-2,-2,0,0,0;-1/1:4804:0,-2,-2,-2,0,0,0"
  | 31 => laurent_polynomial% "1/1:2807:0,0,0,0,0,0,0;-1/1:4647:0,-2,-2,-2,0,0,0;-1/1:4652:0,-2,-2,-2,0,0,0;-1/1:4801:0,-2,-2,-2,0,0,0;-1/1:4804:0,-2,-2,-2,0,0,0"
  | _ => []

compact_certificate def operationsPart20 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:2886:0,0,0,0,0,0,0;-1/1:4601:-2,0,0,-2,0,0,0;-1/1:4647:-2,0,0,-2,0,0,0;-1/1:4648:-2,0,0,-2,0,0,0;-1/1:4652:-2,0,0,-2,0,0,0;-1/1:4693:-2,0,0,-2,0,0,0;-1/1:4708:0,0,0,0,0,0,0;-1/1:4802:-2,0,0,-2,0,0,0;-1/1:4804:-2,0,0,-2,0,0,0;-1/1:4821:-2,0,0,-2,0,0,0;-1/1:4829:0,0,0,0,0,0,0;-1/1:4969:0,0,0,0,0,0,0;-1/1:4986:0,0,0,0,0,0,0;-1/1:5001:0,0,0,0,0,0,0;-1/1:5068:0,0,0,0,0,0,0;1/1:5098:-2,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:2887:0,0,0,0,0,0,0;-1/1:4601:-2,0,0,-2,0,0,0;-1/1:4647:-2,0,0,-2,0,0,0;-1/1:4652:-2,0,0,-2,0,0,0;-1/1:4655:-2,0,0,-2,0,0,0;-1/1:4694:0,0,0,0,0,0,0;-1/1:4702:-2,0,0,-2,0,0,0;-1/1:4799:-2,0,0,-2,0,0,0;-1/1:4801:-2,0,0,-2,0,0,0;-1/1:4825:0,0,0,0,0,0,0;-1/1:4830:-2,0,0,-2,0,0,0;-1/1:4922:0,0,0,0,0,0,0;-1/1:4987:0,0,0,0,0,0,0;-1/1:5050:0,0,0,0,0,0,0;1/1:5097:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:2962:0,0,0,0,0,0,0;-1/1:4601:0,0,0,-2,0,0,0;-1/1:4615:0,0,0,-2,0,0,0;-1/1:4617:0,0,0,-2,0,0,0;-1/1:4622:0,0,0,-2,0,0,0;-1/1:4623:0,0,0,-2,0,0,0;-1/1:4647:0,0,0,-2,0,0,0;-1/1:4651:0,0,0,0,0,0,0;-1/1:4652:0,0,0,-2,0,0,0;-1/1:4661:0,0,0,0,0,0,0;-1/1:4674:0,0,0,-2,0,0,0;-1/1:4683:0,0,0,-2,0,0,0;-1/1:4696:0,0,0,-2,0,0,0;-1/1:4697:0,0,0,-2,0,0,0;-1/1:4706:0,0,0,-2,0,0,0;-1/1:4720:0,0,0,-2,0,0,0;-1/1:4721:0,0,0,0,0,0,0;-1/1:4726:0,0,0,-2,0,0,0;-1/1:4729:0,0,0,0,0,0,0;-1/1:4745:0,0,0,-2,0,0,0;-1/1:4746:0,0,0,0,0,0,0;-1/1:4780:0,0,0,0,0,0,0;-1/1:4783:0,0,0,-2,0,0,0;-1/1:4801:0,0,0,-2,0,0,0;-1/1:4804:0,0,0,-2,0,0,0;-1/1:4843:0,0,0,0,0,0,0;-1/1:4844:0,0,0,0,0,0,0;-1/1:4858:0,0,0,0,0,0,0;-1/1:4860:0,0,0,-2,0,0,0;-1/1:4865:0,0,0,-2,0,0,0;-1/1:4910:0,0,0,0,0,0,0;-1/1:4955:0,0,0,0,0,0,0;-1/1:5089:0,0,0,0,0,0,0;-1/1:5161:0,0,0,0,0,0,0;-1/1:5235:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:2963:0,0,0,0,0,0,0;-1/1:4600:0,0,0,-2,0,0,0;-1/1:4601:0,0,0,-2,0,0,0;-1/1:4615:0,0,0,-2,0,0,0;-1/1:4619:0,0,0,-2,0,0,0;-1/1:4622:0,0,0,-2,0,0,0;-1/1:4647:0,0,0,-2,0,0,0;-1/1:4649:0,0,0,0,0,0,0;-1/1:4652:0,0,0,-2,0,0,0;-1/1:4653:0,0,0,0,0,0,0;-1/1:4666:0,0,0,-2,0,0,0;-1/1:4674:0,0,0,-2,0,0,0;-1/1:4683:0,0,0,-2,0,0,0;-1/1:4697:0,0,0,-2,0,0,0;-1/1:4704:0,0,0,-2,0,0,0;-1/1:4706:0,0,0,-2,0,0,0;-1/1:4718:0,0,0,0,0,0,0;-1/1:4720:0,0,0,-2,0,0,0;-1/1:4726:0,0,0,-2,0,0,0;-1/1:4730:0,0,0,0,0,0,0;-1/1:4745:0,0,0,-2,0,0,0;-1/1:4756:0,0,0,-2,0,0,0;-1/1:4761:0,0,0,0,0,0,0;-1/1:4783:0,0,0,-2,0,0,0;-1/1:4787:0,0,0,0,0,0,0;-1/1:4801:0,0,0,-2,0,0,0;-1/1:4804:0,0,0,-2,0,0,0;-1/1:4835:0,0,0,0,0,0,0;-1/1:4873:0,0,0,0,0,0,0;-1/1:4881:0,0,0,0,0,0,0;-1/1:4946:0,0,0,0,0,0,0;-1/1:4971:0,0,0,0,0,0,0;-1/1:5086:0,0,0,0,0,0,0;-1/1:5120:0,0,0,0,0,0,0;-1/1:5234:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:2972:0,0,0,0,0,0,0;-1/1:4614:0,2,0,-2,0,0,0;-1/1:4625:0,2,0,-2,0,0,0;-1/1:4631:0,0,0,0,0,0,0;-1/1:4655:0,2,0,-2,0,0,0;-1/1:4681:0,2,0,-2,0,0,0;-1/1:4686:0,0,0,0,0,0,0;-1/1:4689:0,2,0,-2,0,0,0;-1/1:4690:0,0,0,0,0,0,0;-1/1:4702:0,2,0,-2,0,0,0;-1/1:4716:0,2,0,-2,0,0,0;-1/1:4717:0,0,0,0,0,0,0;-1/1:4776:0,2,0,-2,0,0,0;-1/1:4779:0,2,0,-2,0,0,0;-1/1:4790:0,2,0,-2,0,0,0;-1/1:4798:0,2,0,-2,0,0,0;-1/1:4799:0,2,0,-2,0,0,0;-1/1:4826:0,0,0,0,0,0,0;-1/1:4827:0,2,0,-2,0,0,0;-1/1:4830:0,2,0,-2,0,0,0;-1/1:4832:0,0,0,0,0,0,0;-1/1:4847:0,0,0,0,0,0,0;-1/1:4864:0,2,0,-2,0,0,0;-1/1:4867:0,0,0,0,0,0,0;-1/1:4871:0,0,0,0,0,0,0;-1/1:4886:0,2,0,-2,0,0,0;-1/1:4894:0,2,0,-2,0,0,0;-1/1:4896:0,2,0,-2,0,0,0;-1/1:4934:0,0,0,0,0,0,0;-1/1:4957:0,2,0,-2,0,0,0;-1/1:4959:0,2,0,-2,0,0,0;-1/1:4960:0,0,0,0,0,0,0;-1/1:4991:0,0,0,0,0,0,0;-1/1:5221:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:2973:0,0,0,0,0,0,0;-1/1:4611:0,2,0,-2,0,0,0;-1/1:4612:0,0,0,0,0,0,0;-1/1:4635:0,2,0,-2,0,0,0;-1/1:4648:0,2,0,-2,0,0,0;-1/1:4665:0,0,0,0,0,0,0;-1/1:4670:0,2,0,-2,0,0,0;-1/1:4671:0,0,0,0,0,0,0;-1/1:4693:0,2,0,-2,0,0,0;-1/1:4713:0,2,0,-2,0,0,0;-1/1:4714:0,0,0,0,0,0,0;-1/1:4754:0,2,0,-2,0,0,0;-1/1:4755:0,0,0,0,0,0,0;-1/1:4763:0,2,0,-2,0,0,0;-1/1:4773:0,2,0,-2,0,0,0;-1/1:4794:0,2,0,-2,0,0,0;-1/1:4802:0,2,0,-2,0,0,0;-1/1:4821:0,2,0,-2,0,0,0;-1/1:4822:0,0,0,0,0,0,0;-1/1:4824:0,2,0,-2,0,0,0;-1/1:4828:0,0,0,0,0,0,0;-1/1:4875:0,2,0,-2,0,0,0;-1/1:4883:0,0,0,0,0,0,0;-1/1:4884:0,0,0,0,0,0,0;-1/1:4889:0,0,0,0,0,0,0;-1/1:4913:0,2,0,-2,0,0,0;-1/1:4914:0,2,0,-2,0,0,0;-1/1:4915:0,0,0,0,0,0,0;-1/1:4938:0,2,0,-2,0,0,0;-1/1:4939:0,2,0,-2,0,0,0;-1/1:4950:0,2,0,-2,0,0,0;-1/1:4951:0,2,0,-2,0,0,0;-1/1:4990:0,0,0,0,0,0,0;-1/1:5216:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:3246:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:3249:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:3252:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:3262:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:3276:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3277:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:3279:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:3282:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:3283:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:3286:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:3291:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:3294:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "-1/1:3295:0,0,0,0,0,0,0;1/1:4816:0,0,0,0,0,0,0;-1/1:5098:-1,0,0,0,1,0,0;1/1:5201:0,0,0,0,0,0,0;1/1:5236:-2,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:3304:0,0,0,0,0,0,0;-1/1:5057:-2,0,0,0,0,0,0;1/1:5074:-1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "1/1:3309:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:3312:0,0,0,0,0,0,0;1/1:5075:-1,0,0,0,1,0,0"
  | 22 => laurent_polynomial% "1/1:3324:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:3328:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:3337:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:3343:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:3354:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:3357:0,0,0,0,0,0,0;-1/1:5003:-2,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:3358:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:3359:0,0,0,0,0,0,0;1/1:5086:-1,0,0,0,1,0,0"
  | 30 => laurent_polynomial% "1/1:3366:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:3371:0,0,0,0,0,0,0;-1/1:4735:0,0,0,0,0,0,0;1/1:4991:-1,0,0,0,1,0,0;-1/1:5102:-1,0,0,0,1,0,0"
  | _ => []
compact_certificate def operationsPart21 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3377:0,0,0,0,0,0,0;1/1:5114:-1,0,0,0,1,0,0"
  | 1 => laurent_polynomial% "1/1:3381:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:3387:0,0,0,0,0,0,0;1/1:5084:-1,0,0,0,1,0,0"
  | 3 => laurent_polynomial% "-1/1:3388:0,0,0,0,0,0,0;1/1:4975:0,0,0,0,0,0,0;-1/1:4977:-1,0,0,0,1,0,0;1/1:5072:0,0,0,0,0,0,0;1/1:5083:-2,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:3389:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "-1/1:3391:0,0,0,0,0,0,0;1/1:4972:0,0,0,0,0,0,0;-1/1:4974:-1,0,0,0,1,0,0;1/1:4976:-2,0,0,0,0,0,0;1/1:4988:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:3392:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:3393:0,0,0,0,0,0,0;1/1:5057:-1,0,0,0,1,0,0;-1/1:5074:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:3407:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:3408:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:3409:0,0,0,0,0,0,0;-1/1:5075:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3412:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:3414:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:3431:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:3433:0,0,0,0,0,0,0;-1/1:5071:-2,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:3436:0,0,0,0,0,0,0;1/1:5165:-1,0,0,0,1,0,0"
  | 16 => laurent_polynomial% "1/1:3438:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:3441:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3444:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:3451:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:3454:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:3459:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:3462:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:3463:0,0,0,0,0,0,0;1/1:5174:-1,0,0,0,1,0,0"
  | 24 => laurent_polynomial% "1/1:3492:0,0,0,0,0,0,0;1/1:5109:-1,0,0,0,1,0,0"
  | 25 => laurent_polynomial% "1/1:3493:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:3496:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:3501:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:3508:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:3514:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:3517:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:3518:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def operationsPart22 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3519:0,0,0,0,0,0,0;1/1:5116:-1,0,0,0,1,0,0"
  | 1 => laurent_polynomial% "1/1:3522:0,0,0,0,0,0,0;-1/1:5074:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:3524:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:3526:0,0,0,0,0,0,0;-1/1:5075:-2,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:3528:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:3532:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:3534:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:3536:0,0,0,0,0,0,0;-1/1:5045:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:3543:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:3546:0,0,0,0,0,0,0;-1/1:5069:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:3547:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3548:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:3553:0,0,0,0,0,0,0;-1/1:5081:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:3574:0,0,0,0,0,0,0;1/1:5059:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:3399:2,0,0,0,0,0,0;1/1:5180:1,0,0,0,1,0,0;-1/1:5197:2,0,0,0,0,0,0;-1/1:5317:2,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:3577:0,0,0,0,0,0,0;-1/1:5060:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:3578:0,0,0,0,0,0,0;1/1:5167:-1,0,0,0,1,0,0"
  | 17 => laurent_polynomial% "1/1:3582:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3584:0,0,0,0,0,0,0;-1/1:4743:0,0,0,0,0,0,0;1/1:5101:-1,0,0,0,1,0,0"
  | 19 => laurent_polynomial% "1/1:3596:0,0,0,0,0,0,0;1/1:5089:-1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "1/1:3597:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:3598:0,0,0,0,0,0,0;-1/1:5048:-2,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:3601:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:3612:0,0,0,0,0,0,0;-1/1:4996:-2,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:3618:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:3622:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:3624:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:3627:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:3631:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:3633:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:3634:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:3636:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def operationsPart23 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3637:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:3639:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:3643:0,0,0,0,0,0,0;1/1:5069:-1,0,0,0,1,0,0"
  | 3 => laurent_polynomial% "1/1:3646:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:3651:0,0,0,0,0,0,0;1/1:5071:-1,0,0,0,1,0,0"
  | 5 => laurent_polynomial% "1/1:3661:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:3664:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:3666:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:3669:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:3672:0,0,0,0,0,0,0;-1/1:5054:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:3673:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3676:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:3678:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:3679:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:3681:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:3682:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:3687:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:3688:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3693:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:3703:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:3709:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:3766:0,0,0,0,0,0,0;1/1:4730:0,-1,0,0,0,1,0;-1/1:4895:0,0,0,0,0,0,0;-1/1:5167:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:3772:0,0,0,0,0,0,0;1/1:4879:0,-1,0,0,0,1,0;-1/1:4926:0,0,0,0,0,0,0;-1/1:5086:0,-2,0,0,0,0,0;-1/1:5102:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:3788:0,0,0,0,0,0,0;-1/1:4858:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:3802:0,0,0,0,0,0,0;-1/1:4909:0,-2,0,0,0,0,0;-1/1:5089:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:3812:0,0,0,0,0,0,0;-1/1:4732:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:3818:0,0,0,0,0,0,0;-1/1:4730:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:3836:0,0,0,0,0,0,0;-1/1:4879:0,0,0,0,0,0,0;1/1:5086:0,-1,0,0,0,1,0"
  | 28 => laurent_polynomial% "1/1:3848:0,0,0,0,0,0,0;-1/1:4721:0,-2,0,0,0,0,0;-1/1:4889:0,0,0,0,0,0,0;1/1:5114:0,-1,0,0,0,1,0"
  | 29 => laurent_polynomial% "1/1:3868:0,0,0,0,0,0,0;-1/1:4690:0,-2,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:3876:0,0,0,0,0,0,0;-1/1:4714:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:3888:0,0,0,0,0,0,0;-1/1:4787:0,0,0,0,0,0,0"
  | _ => []

compact_certificate def operationsPart24 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3902:0,0,0,0,0,0,0;1/1:4714:0,-1,0,0,0,1,0"
  | 1 => laurent_polynomial% "1/1:3907:0,0,0,0,0,0,0;1/1:4751:0,-1,0,0,0,1,0;-1/1:4795:0,0,0,0,0,0,0;-1/1:5168:0,-2,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:3923:0,0,0,0,0,0,0;1/1:4784:0,-1,0,0,0,1,0;-1/1:4897:0,0,0,0,0,0,0;-1/1:5113:0,-2,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:3928:0,0,0,0,0,0,0;1/1:4717:0,-1,0,0,0,1,0;-1/1:4996:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:3942:0,0,0,0,0,0,0;-1/1:4746:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:3974:0,0,0,0,0,0,0;-1/1:4608:0,-2,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:3976:0,0,0,0,0,0,0;-1/1:4671:0,-2,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:3982:0,0,0,0,0,0,0;-1/1:4730:0,-2,0,0,0,0,0;-1/1:4934:0,0,0,0,0,0,0;1/1:5167:0,-1,0,0,0,1,0"
  | 8 => laurent_polynomial% "1/1:3988:0,0,0,0,0,0,0;-1/1:4910:0,-2,0,0,0,0,0;-1/1:4915:0,0,0,0,0,0,0;1/1:5184:0,-1,0,0,0,1,0"
  | 9 => laurent_polynomial% "1/1:3994:0,0,0,0,0,0,0;-1/1:4770:0,0,0,0,0,0,0;1/1:5089:0,-1,0,0,0,1,0"
  | 10 => laurent_polynomial% "1/1:4018:0,0,0,0,0,0,0;-1/1:4741:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:4028:0,0,0,0,0,0,0;-1/1:4737:0,-2,0,0,0,0,0;-1/1:5086:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:4042:0,0,0,0,0,0,0;-1/1:4761:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:4058:0,0,0,0,0,0,0;1/1:4770:0,-1,0,0,0,1,0;-1/1:4891:0,0,0,0,0,0,0;-1/1:4990:0,0,0,0,0,0,0;-1/1:5089:0,-2,0,0,0,0,0;1/1:5101:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:4106:0,0,0,0,0,0,0;-1/1:4768:0,0,0,0,0,0,0;-1/1:5069:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:4178:0,0,0,0,0,0,0;-1/1:4698:0,0,0,0,0,0,0;-1/1:4771:0,0,0,0,0,0,0;-1/1:5205:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:4184:0,0,0,0,0,0,0;-1/1:4668:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:4207:0,0,0,0,0,0,0;-1/1:4850:0,0,0,0,0,0,0;-1/1:4857:0,0,0,0,0,0,0;-1/1:5124:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:4212:0,0,0,0,0,0,0;-1/1:4707:0,0,0,0,0,0,0;-1/1:4878:0,0,0,0,0,0,0;-1/1:5185:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:4357:0,0,0,0,0,0,0;-1/1:4640:0,0,0,0,0,0,0;1/1:4740:0,0,0,-1,0,0,1;-1/1:4769:0,0,0,-2,0,0,0;-1/1:4857:0,0,0,0,0,0,0;-1/1:4877:0,0,0,0,0,0,0;-1/1:5012:0,0,0,0,0,0,0;-1/1:5036:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:4396:0,0,0,0,0,0,0;-1/1:4600:0,0,0,0,0,0,0;-1/1:4623:0,0,0,-2,0,0,0;1/1:4745:0,0,0,-1,0,0,1;-1/1:4879:0,0,0,0,0,0,0;-1/1:4907:0,0,0,0,0,0,0;-1/1:5045:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:2583:0,0,0,0,0,0,0;-1/1:4648:-2,2,-2,-2,0,0,0;-1/1:4802:-2,2,-2,-2,0,0,0;-1/1:4821:-2,2,-2,-2,0,0,0;-1/1:4824:-2,2,-2,-2,0,0,0;-1/1:5160:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:2584:0,0,0,0,0,0,0;-1/1:4655:-2,2,-2,-2,0,0,0;-1/1:4799:-2,2,-2,-2,0,0,0;-1/1:4827:-2,2,-2,-2,0,0,0;-1/1:4830:-2,2,-2,-2,0,0,0;-1/1:5121:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:2588:0,0,0,0,0,0,0;-1/1:4803:2,0,-2,-2,0,0,0;-1/1:4809:2,0,-2,-2,0,0,0;-1/1:4820:2,0,-2,-2,0,0,0;-1/1:4831:2,0,-2,-2,0,0,0;-1/1:5222:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:2594:0,0,0,0,0,0,0;-1/1:4648:0,2,-2,-2,0,0,0;-1/1:4802:0,2,-2,-2,0,0,0;-1/1:4821:0,2,-2,-2,0,0,0;-1/1:4824:0,2,-2,-2,0,0,0;-1/1:5118:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:2759:0,0,0,0,0,0,0;-1/1:4801:-2,-2,0,0,0,0,0;-1/1:4814:-2,-2,0,0,0,0,0;-1/1:4828:-2,-2,0,0,0,0,0;-1/1:4835:-2,-2,0,0,0,0,0;-1/1:4836:0,0,0,0,0,0,0;-1/1:4844:-2,-2,0,0,0,0,0;-1/1:4847:-2,-2,0,0,0,0,0;-1/1:5038:0,0,0,0,0,0,0;-1/1:5091:0,0,0,0,0,0,0;1/1:5096:0,0,0,0,0,0,0;-1/1:5187:0,0,0,0,0,0,0;-1/1:5201:0,0,0,0,0,0,0;1/1:5258:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:2773:0,0,0,0,0,0,0;-1/1:4809:2,-2,0,0,0,0,0;-1/1:4824:0,0,0,0,0,0,0;-1/1:4825:2,-2,0,0,0,0,0;-1/1:4839:0,0,0,0,0,0,0;-1/1:4904:2,-2,0,0,0,0,0;-1/1:4921:2,-2,0,0,0,0,0;-1/1:5011:2,-2,0,0,0,0,0;-1/1:5015:2,-2,0,0,0,0,0;-1/1:5078:0,0,0,0,0,0,0;-1/1:5079:0,0,0,0,0,0,0;-1/1:5090:1,-2,0,0,1,0,0;-1/1:5236:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:2867:0,0,0,0,0,0,0;-1/1:4617:0,0,0,0,0,0,0;-1/1:4685:0,2,-2,0,0,0,0;-1/1:4693:0,2,-2,0,0,0,0;-1/1:4851:0,2,-2,0,0,0,0;-1/1:4898:0,2,-2,0,0,0,0;-1/1:4919:0,2,-2,0,0,0,0;-1/1:4960:0,0,0,0,0,0,0;-1/1:4961:0,2,-2,0,0,0,0;-1/1:5214:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:2882:0,0,0,0,0,0,0;-1/1:4647:0,0,-2,-2,0,0,0;-1/1:4648:0,0,-2,-2,0,0,0;-1/1:4652:0,0,-2,-2,0,0,0;-1/1:4732:0,0,0,0,0,0,0;-1/1:4737:0,0,0,0,0,0,0;-1/1:4801:0,0,-2,-2,0,0,0;-1/1:4802:0,0,-2,-2,0,0,0;-1/1:4804:0,0,-2,-2,0,0,0;-1/1:4821:0,0,-2,-2,0,0,0;-1/1:4824:0,0,-2,-2,0,0,0;-1/1:5054:0,0,0,0,0,0,0;-1/1:5217:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:2883:0,0,0,0,0,0,0;-1/1:4647:0,0,-2,-2,0,0,0;-1/1:4652:0,0,-2,-2,0,0,0;-1/1:4655:0,0,-2,-2,0,0,0;-1/1:4741:0,0,0,0,0,0,0;-1/1:4799:0,0,-2,-2,0,0,0;-1/1:4801:0,0,-2,-2,0,0,0;-1/1:4804:0,0,-2,-2,0,0,0;-1/1:4827:0,0,-2,-2,0,0,0;-1/1:4830:0,0,-2,-2,0,0,0;-1/1:4909:0,0,0,0,0,0,0;-1/1:5215:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:2884:0,0,0,0,0,0,0;-1/1:4660:2,0,-2,-2,0,0,0;-1/1:4717:0,0,0,0,0,0,0;-1/1:4803:2,0,-2,-2,0,0,0;-1/1:4809:2,0,-2,-2,0,0,0;-1/1:4820:2,0,-2,-2,0,0,0;-1/1:4823:2,0,-2,-2,0,0,0;-1/1:4831:2,0,-2,-2,0,0,0;-1/1:4841:2,0,-2,-2,0,0,0;-1/1:4842:2,0,-2,-2,0,0,0;-1/1:4960:0,0,0,0,0,0,0;-1/1:5221:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:2885:0,0,0,0,0,0,0;-1/1:4646:2,0,-2,-2,0,0,0;-1/1:4714:0,0,0,0,0,0,0;-1/1:4755:0,0,0,0,0,0,0;-1/1:4803:2,0,-2,-2,0,0,0;-1/1:4809:2,0,-2,-2,0,0,0;-1/1:4820:2,0,-2,-2,0,0,0;-1/1:4831:2,0,-2,-2,0,0,0;-1/1:4834:2,0,-2,-2,0,0,0;-1/1:4836:2,0,-2,-2,0,0,0;-1/1:4837:2,0,-2,-2,0,0,0;-1/1:5216:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def operationsPart25 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3009:0,0,0,0,0,0,0;-1/1:4647:0,0,-2,-2,0,0,0;-1/1:4652:0,0,-2,-2,0,0,0;-1/1:4655:0,0,-2,-2,0,0,0;-1/1:4718:0,0,0,0,0,0,0;-1/1:4799:0,0,-2,-2,0,0,0;-1/1:4801:0,0,-2,-2,0,0,0;-1/1:4804:0,0,-2,-2,0,0,0;-1/1:4827:0,0,-2,-2,0,0,0;-1/1:4830:0,0,-2,-2,0,0,0;-1/1:5234:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:3010:0,0,0,0,0,0,0;-1/1:4647:0,0,-2,-2,0,0,0;-1/1:4648:0,0,-2,-2,0,0,0;-1/1:4652:0,0,-2,-2,0,0,0;-1/1:4729:0,0,0,0,0,0,0;-1/1:4801:0,0,-2,-2,0,0,0;-1/1:4802:0,0,-2,-2,0,0,0;-1/1:4804:0,0,-2,-2,0,0,0;-1/1:4821:0,0,-2,-2,0,0,0;-1/1:4824:0,0,-2,-2,0,0,0;-1/1:5235:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:3270:0,0,0,0,0,0,0;-1/1:5095:-2,0,0,0,0,0,0;1/1:5100:-1,0,0,0,1,0,0;-1/1:5236:-1,0,0,0,1,0,0"
  | 3 => laurent_polynomial% "1/1:3273:0,0,0,0,0,0,0;-1/1:5199:-2,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:3288:0,0,0,0,0,0,0;-1/1:5219:-2,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "-1/1:3310:0,0,0,0,0,0,0;-1/1:4981:-1,0,0,0,1,0,0;1/1:4995:-2,0,0,0,0,0,0;-1/1:5061:-2,0,0,0,0,0,0;1/1:5067:-1,0,0,0,1,0,0;1/1:5078:0,0,0,0,0,0,0;1/1:5188:0,0,0,0,0,0,0;-1/1:5232:0,0,0,0,0,0,0;-1/1:5237:-2,0,0,0,0,0,0;-1/1:5394:-2,0,0,0,0,0,0;-1/1:5394:-1,0,0,0,1,0,0"
  | 6 => laurent_polynomial% "1/1:3314:0,0,0,0,0,0,0;1/1:5222:-1,0,0,0,1,0,0"
  | 7 => laurent_polynomial% "-1/1:3325:0,0,0,0,0,0,0;1/1:4932:-2,0,0,0,0,0,0;-1/1:5095:-1,0,0,0,1,0,0;1/1:5100:0,0,0,0,0,0,0;1/1:5202:0,0,0,0,0,0,0;-1/1:5236:0,0,0,0,0,0,0;-1/1:5240:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:2760:0,0,0,0,0,0,0;-1/1:4804:-2,-2,0,0,0,0,0;-1/1:4808:-2,-2,0,0,0,0,0;-1/1:4826:-2,-2,0,0,0,0,0;-1/1:4842:0,0,0,0,0,0,0;-1/1:4843:-2,-2,0,0,0,0,0;-1/1:4881:-2,-2,0,0,0,0,0;-1/1:4883:-2,-2,0,0,0,0,0;-1/1:5016:0,0,0,0,0,0,0;-1/1:5068:0,0,0,0,0,0,0;-1/1:5087:0,0,0,0,0,0,0;-1/1:5092:0,0,0,0,0,0,0;1/1:5095:0,0,0,0,0,0,0;1/1:5178:0,0,0,0,0,0,0;-1/1:5232:0,0,0,0,0,0,0;-1/1:5405:0,0,0,0,0,0,0;1/1:5407:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:3331:0,0,0,0,0,0,0;1/1:5199:-1,0,0,0,1,0,0"
  | 10 => laurent_polynomial% "-1/1:3384:0,0,0,0,0,0,0;-1/1:5081:-1,0,0,0,1,0,0;1/1:5193:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3386:0,0,0,0,0,0,0;-1/1:5214:-2,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "-1/1:3394:0,0,0,0,0,0,0;1/1:4976:0,0,0,0,0,0,0;-1/1:5058:-1,0,0,0,1,0,0;1/1:5179:-2,0,0,0,0,0,0;1/1:5195:0,0,0,0,0,0,0;-1/1:5218:-2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:3396:0,0,0,0,0,0,0;-1/1:5060:-1,0,0,0,1,0,0;1/1:5196:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:3401:0,0,0,0,0,0,0;1/1:5120:-1,0,0,0,1,0,0;-1/1:5184:-2,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:3417:0,0,0,0,0,0,0;1/1:5186:-1,0,0,0,1,0,0;-1/1:5364:-2,0,0,0,0,0,0;-1/1:5372:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:3506:0,0,0,0,0,0,0;1/1:4946:-1,0,0,0,1,0,0;-1/1:5103:-2,0,0,0,0,0,0;1/1:5114:-2,0,0,0,0,0,0;1/1:5184:-2,0,0,0,0,0,0;-1/1:5244:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:3511:0,0,0,0,0,0,0;-1/1:5204:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3588:0,0,0,0,0,0,0;-1/1:5165:-2,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:3616:0,0,0,0,0,0,0;-1/1:5109:-2,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:3762:0,0,0,0,0,0,0;-1/1:4700:0,0,0,0,0,0,0;1/1:4755:0,-1,0,0,0,1,0;-1/1:5120:0,0,0,0,0,0,0;-1/1:5222:0,-2,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:3834:0,0,0,0,0,0,0;-1/1:5045:0,-2,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:3842:0,0,0,0,0,0,0;-1/1:4690:0,0,0,0,0,0,0;-1/1:4971:0,-2,0,0,0,0,0;1/1:5104:0,-1,0,0,0,1,0;-1/1:5167:0,-1,0,0,0,1,0"
  | 23 => laurent_polynomial% "1/1:3864:0,0,0,0,0,0,0;-1/1:4755:0,-2,0,0,0,0,0;1/1:5120:0,-1,0,0,0,1,0"
  | 24 => laurent_polynomial% "-1/1:3867:2,0,0,0,0,0,0;1/1:4797:2,-2,0,0,0,0,0;1/1:5046:2,0,0,0,0,0,0;1/1:5126:2,0,0,0,0,0,0;1/1:5302:2,0,0,0,0,0,0;-1/1:5323:2,-1,0,0,0,1,0;1/1:5377:1,0,0,0,1,0,0;-1/1:5380:2,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:3819:2,0,0,0,0,0,0;-1/1:5136:2,-1,0,0,0,1,0;1/1:5139:2,0,0,0,0,0,0;1/1:5160:2,0,0,0,0,0,0;1/1:5257:2,0,0,0,0,0,0;-1/1:5377:2,0,0,0,0,0,0;1/1:5414:2,-2,0,0,0,0,0;1/1:5424:1,0,0,0,1,0,0"
  | 26 => laurent_polynomial% "1/1:3872:0,0,0,0,0,0,0;-1/1:4910:0,0,0,0,0,0,0;-1/1:5048:0,0,0,0,0,0,0;-1/1:5215:0,-2,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:3874:0,0,0,0,0,0,0;-1/1:4735:0,-2,0,0,0,0,0;-1/1:5049:0,0,0,0,0,0,0;1/1:5198:-2,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:3932:0,0,0,0,0,0,0;-1/1:4878:0,0,0,0,0,0,0;-1/1:5161:0,-2,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:3956:0,0,0,0,0,0,0;-1/1:4743:0,-2,0,0,0,0,0;-1/1:5002:0,0,0,0,0,0,0;1/1:5191:-2,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "-1/1:3993:2,0,0,0,0,0,0;1/1:5010:2,0,0,0,0,0,0;1/1:5021:2,0,0,0,0,0,0;1/1:5102:0,0,0,0,0,0,0;-1/1:5135:2,-1,0,0,0,1,0;1/1:5278:2,-2,0,0,0,0,0;1/1:5338:2,0,0,0,0,0,0;-1/1:5362:2,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:3996:0,0,0,0,0,0,0;-1/1:5006:0,-2,0,0,0,0,0"
  | _ => []
compact_certificate def operationsPart26 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:4008:0,0,0,0,0,0,0;-1/1:4861:0,0,0,0,0,0,0;-1/1:4991:0,-2,0,0,0,0,0;1/1:5102:0,-2,0,0,0,0,0"
  | 1 => laurent_polynomial% "-1/1:4032:0,0,0,0,0,0,0;1/1:4612:0,-2,0,0,0,0,0;1/1:5219:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:4064:0,0,0,0,0,0,0;1/1:4721:0,-1,0,0,0,1,0;-1/1:4774:0,0,0,0,0,0,0;-1/1:5114:0,0,0,0,0,0,0;-1/1:5244:0,-2,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:4068:0,0,0,0,0,0,0;-1/1:4710:0,0,0,0,0,0,0;1/1:4960:0,-1,0,0,0,1,0;-1/1:5161:0,0,0,0,0,0,0;-1/1:5223:0,-2,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:4152:0,0,0,0,0,0,0;-1/1:5048:0,0,0,0,0,0,0;-1/1:5083:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:4206:0,0,0,0,0,0,0;-1/1:4870:0,0,0,0,0,0,0;-1/1:5208:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:4242:0,0,0,0,0,0,0;-1/1:5060:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:4274:0,0,0,0,0,0,0;-1/1:4774:0,0,0,0,0,0,0;-1/1:5197:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:4284:0,0,0,0,0,0,0;-1/1:4853:0,0,0,0,0,0,0;-1/1:5075:0,0,0,0,0,0,0;-1/1:5186:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:4332:0,0,0,0,0,0,0;-1/1:4627:0,0,0,-2,0,0,0;-1/1:4713:0,0,0,0,0,0,0;1/1:4794:0,0,0,-1,0,0,1;-1/1:4926:0,0,0,0,0,0,0;-1/1:5048:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:4339:0,0,0,0,0,0,0;-1/1:4621:0,0,0,0,0,0,0;1/1:4739:0,0,0,-1,0,0,1;-1/1:4854:0,0,0,-2,0,0,0;-1/1:4906:0,0,0,0,0,0,0;-1/1:5028:0,0,0,0,0,0,0;-1/1:5051:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:4344:0,0,0,0,0,0,0;-1/1:4670:0,0,0,-2,0,0,0;-1/1:4711:0,0,0,0,0,0,0;1/1:4796:0,0,0,-1,0,0,1;-1/1:4914:0,0,0,0,0,0,0;-1/1:5075:0,0,0,0,0,0,0;-1/1:5084:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:2573:0,0,0,0,0,0,0;-1/1:4647:-2,0,-2,-2,0,0,0;-1/1:4652:-2,0,-2,-2,0,0,0;-1/1:4801:-2,0,-2,-2,0,0,0;-1/1:4804:-2,0,-2,-2,0,0,0;-1/1:5123:0,0,0,0,0,0,0;-1/1:5159:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:2574:0,0,0,0,0,0,0;-1/1:4647:-2,0,-2,-2,0,0,0;-1/1:4652:-2,0,-2,-2,0,0,0;-1/1:4801:-2,0,-2,-2,0,0,0;-1/1:4804:-2,0,-2,-2,0,0,0;-1/1:5122:0,0,0,0,0,0,0;-1/1:5158:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:2767:0,0,0,0,0,0,0;1/1:4602:2,0,-2,0,0,0,0;1/1:4706:0,0,0,0,0,0,0;1/1:4708:2,0,-2,0,0,0,0;1/1:4791:2,0,-2,0,0,0,0;1/1:4792:2,0,-2,0,0,0,0;1/1:4912:2,0,-2,0,0,0,0;1/1:4916:2,0,-2,0,0,0,0;1/1:4991:0,0,0,0,0,0,0;1/1:5089:0,0,0,0,0,0,0;-1/1:5102:0,0,0,0,0,0,0;1/1:5118:0,0,0,0,0,0,0;1/1:5217:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "-1/1:2768:0,0,0,0,0,0,0;1/1:4602:2,0,-2,0,0,0,0;1/1:4694:2,0,-2,0,0,0,0;1/1:4697:0,0,0,0,0,0,0;1/1:4791:2,0,-2,0,0,0,0;1/1:4792:2,0,-2,0,0,0,0;1/1:4912:2,0,-2,0,0,0,0;1/1:4916:2,0,-2,0,0,0,0;1/1:5086:0,0,0,0,0,0,0;1/1:5101:0,0,0,0,0,0,0;1/1:5163:0,0,0,0,0,0,0;1/1:5215:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:2776:2,2,-2,0,0,0,0;-1/1:4714:0,0,0,0,0,0,0;-1/1:4719:2,2,-2,0,0,0,0;-1/1:4756:0,0,0,0,0,0,0;-1/1:4899:2,2,-2,0,0,0,0;-1/1:4917:2,2,-2,0,0,0,0;-1/1:4922:2,2,-2,0,0,0,0;-1/1:4968:2,2,-2,0,0,0,0;-1/1:4970:2,2,-2,0,0,0,0;-1/1:5230:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:2763:0,0,0,0,0,0,0;-1/1:4630:-2,2,-2,0,0,0,0;-1/1:4685:-2,2,-2,0,0,0,0;-1/1:4693:-2,2,-2,0,0,0,0;-1/1:4765:0,0,0,0,0,0,0;-1/1:4898:-2,2,-2,0,0,0,0;-1/1:4919:-2,2,-2,0,0,0,0;-1/1:4961:-2,2,-2,0,0,0,0;-1/1:5043:0,0,0,0,0,0,0;-1/1:5135:0,0,0,0,0,0,0;-1/1:5147:0,0,0,0,0,0,0;-1/1:5306:0,0,0,0,0,0,0;1/1:5395:0,0,0,0,0,0,0;1/1:5448:-2,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:2940:0,0,0,0,0,0,0;-1/1:4600:0,0,0,0,0,0,0;-1/1:4602:2,0,-2,0,0,0,0;-1/1:4679:0,0,0,0,0,0,0;-1/1:4694:2,0,-2,0,0,0,0;-1/1:4708:2,0,-2,0,0,0,0;-1/1:4719:2,0,-2,0,0,0,0;-1/1:4790:0,0,0,0,0,0,0;-1/1:4791:2,0,-2,0,0,0,0;-1/1:4792:2,0,-2,0,0,0,0;-1/1:4862:2,0,-2,0,0,0,0;-1/1:4879:0,0,0,0,0,0,0;-1/1:4899:2,0,-2,0,0,0,0;-1/1:4907:0,0,0,0,0,0,0;-1/1:4912:2,0,-2,0,0,0,0;-1/1:4922:2,0,-2,0,0,0,0;-1/1:4968:2,0,-2,0,0,0,0;-1/1:4970:2,0,-2,0,0,0,0;-1/1:5045:0,0,0,0,0,0,0;-1/1:5174:0,0,0,0,0,0,0;-1/1:5388:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:3307:0,0,0,0,0,0,0;-1/1:5180:-2,0,0,0,0,0,0;1/1:5197:-1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "1/1:3403:0,0,0,0,0,0,0;-1/1:5185:-2,0,0,0,0,0,0;1/1:5357:-1,0,0,0,1,0,0;-1/1:5371:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:3419:0,0,0,0,0,0,0;-1/1:5006:0,0,0,0,0,0,0;-1/1:5244:-2,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "-1/1:3422:0,0,0,0,0,0,0;1/1:5102:0,0,0,0,0,0,0;-1/1:5231:-1,0,0,0,1,0,0;1/1:5391:-2,0,0,0,0,0,0;1/1:5445:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:3521:0,0,0,0,0,0,0;-1/1:5104:0,0,0,0,0,0,0;1/1:5118:-1,0,0,0,1,0,0;1/1:5167:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:3554:0,0,0,0,0,0,0;-1/1:5104:-2,0,0,0,0,0,0;1/1:5161:-1,0,0,0,1,0,0;1/1:5167:-2,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:3556:2,0,0,0,0,0,0;1/1:5082:2,0,0,0,0,0,0;1/1:5192:2,0,0,0,0,0,0;-1/1:5209:1,0,0,0,1,0,0;1/1:5239:0,0,0,0,0,0,0;-1/1:5273:2,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:3648:0,0,0,0,0,0,0;1/1:5192:-1,0,0,0,1,0,0;-1/1:5209:-2,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:3804:0,0,0,0,0,0,0;-1/1:5231:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:3808:0,0,0,0,0,0,0;1/1:5006:0,-1,0,0,0,1,0;-1/1:5118:0,-2,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:3829:0,0,0,0,0,0,0;-1/1:5028:0,0,0,0,0,0,0;1/1:5030:0,-1,0,0,0,1,0;-1/1:5034:0,-2,0,0,0,0,0;-1/1:5164:0,0,0,0,0,0,0;1/1:5216:0,-2,0,0,0,0,0;-1/1:5243:0,-1,0,0,0,1,0;-1/1:5259:0,0,0,0,0,0,0;1/1:5440:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:2957:0,0,0,0,0,0,0;-1/1:4600:0,-2,0,-2,0,0,0;-1/1:4601:0,-2,0,-2,0,0,0;-1/1:4617:0,-2,0,-2,0,0,0;-1/1:4619:0,-2,0,-2,0,0,0;-1/1:4622:0,-2,0,-2,0,0,0;-1/1:4623:0,-2,0,-2,0,0,0;-1/1:4639:0,0,0,0,0,0,0;-1/1:4647:0,-2,0,-2,0,0,0;-1/1:4652:0,-2,0,-2,0,0,0;-1/1:4657:0,0,0,0,0,0,0;-1/1:4666:0,-2,0,-2,0,0,0;-1/1:4683:0,-2,0,-2,0,0,0;-1/1:4696:0,-2,0,-2,0,0,0;-1/1:4697:0,-2,0,-2,0,0,0;-1/1:4701:0,0,0,0,0,0,0;-1/1:4704:0,-2,0,-2,0,0,0;-1/1:4726:0,-2,0,-2,0,0,0;-1/1:4727:0,0,0,0,0,0,0;-1/1:4756:0,-2,0,-2,0,0,0;-1/1:4759:0,0,0,0,0,0,0;-1/1:4783:0,-2,0,-2,0,0,0;-1/1:4785:0,0,0,0,0,0,0;-1/1:4801:0,-2,0,-2,0,0,0;-1/1:4804:0,-2,0,-2,0,0,0;-1/1:4846:0,0,0,0,0,0,0;-1/1:4860:0,-2,0,-2,0,0,0;-1/1:4865:0,-2,0,-2,0,0,0;-1/1:4962:0,0,0,0,0,0,0;-1/1:4994:0,0,0,0,0,0,0;-1/1:5211:0,0,0,0,0,0,0;1/1:5214:0,0,0,0,0,0,0;-1/1:5219:0,0,0,0,0,0,0;-1/1:5357:0,0,0,0,0,0,0;-1/1:5423:0,0,0,0,0,0,0;1/1:5461:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:3856:0,0,0,0,0,0,0;-1/1:4641:0,-2,0,0,0,0,0;-1/1:5244:0,0,0,0,0,0,0"
  | _ => []

}
certificate_batch {
compact_certificate def operationsPart27 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "-1/1:3954:0,0,0,0,0,0,0;1/1:4717:0,0,0,0,0,0,0;1/1:5228:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:4026:0,0,0,0,0,0,0;-1/1:5230:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:4046:0,0,0,0,0,0,0;-1/1:4701:0,0,0,0,0,0,0;1/1:4971:0,-1,0,0,0,1,0;-1/1:5104:0,0,0,0,0,0,0;1/1:5167:0,0,0,0,0,0,0;-1/1:5245:0,-2,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:4098:0,0,0,0,0,0,0;-1/1:4927:0,0,0,0,0,0,0;-1/1:5362:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:4154:0,0,0,0,0,0,0;-1/1:5049:0,0,0,0,0,0,0;1/1:5198:-2,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:4236:0,0,0,0,0,0,0;-1/1:5002:0,0,0,0,0,0,0;-1/1:5057:0,0,0,0,0,0,0;1/1:5191:-2,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "-1/1:4163:0,0,0,0,0,0,0;1/1:5143:0,0,0,0,0,0,0;1/1:5149:0,0,0,0,0,0,0;1/1:5173:0,0,0,0,0,0,0;-1/1:5191:-3,0,0,0,1,0,0;1/1:5279:0,0,0,0,0,0,0;-1/1:5364:0,0,0,0,0,0,0;1/1:5404:0,0,0,0,0,0,0;1/1:5469:-1,0,0,0,1,0,0"
  | 7 => laurent_polynomial% "1/1:4326:0,0,0,0,0,0,0;1/1:4713:0,0,0,-1,0,0,1;-1/1:4794:0,0,0,-2,0,0,0;-1/1:4875:0,0,0,0,0,0,0;-1/1:4895:0,0,0,0,0,0,0;-1/1:4988:0,0,0,0,0,0,0;-1/1:5208:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:4354:0,0,0,0,0,0,0;-1/1:4600:0,0,0,-2,0,0,0;-1/1:4623:0,0,0,0,0,0,0;-1/1:4770:0,0,0,0,0,0,0;1/1:4783:0,0,0,-1,0,0,1;-1/1:4855:0,0,0,0,0,0,0;-1/1:5006:0,0,0,0,0,0,0;-1/1:5245:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:2868:0,0,0,0,0,0,0;-1/1:4619:0,0,0,0,0,0,0;-1/1:4675:0,2,-2,0,0,0,0;-1/1:4702:0,2,-2,0,0,0,0;-1/1:4755:0,0,0,0,0,0,0;-1/1:4764:0,2,-2,0,0,0,0;-1/1:4793:0,2,-2,0,0,0,0;-1/1:4876:0,2,-2,0,0,0,0;-1/1:4962:0,2,-2,0,0,0,0;-1/1:5218:0,0,0,0,0,0,0;-1/1:5244:0,0,0,0,0,0,0;1/1:5448:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:2761:0,0,0,0,0,0,0;-1/1:4601:0,0,-2,0,0,0,0;-1/1:4665:0,0,-2,0,0,0,0;-1/1:4666:0,0,0,0,0,0,0;-1/1:4735:0,0,0,0,0,0,0;-1/1:4748:0,0,-2,0,0,0,0;-1/1:4780:0,0,-2,0,0,0,0;-1/1:4781:0,0,-2,0,0,0,0;-1/1:4873:0,0,-2,0,0,0,0;-1/1:5104:0,0,0,0,0,0,0;1/1:5167:0,0,0,0,0,0,0;-1/1:5234:0,0,0,0,0,0,0;1/1:5388:0,0,0,0,0,0,0;1/1:5473:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "-1/1:2938:0,0,0,0,0,0,0;1/1:4601:0,0,-2,0,0,0,0;1/1:4603:0,0,-2,0,0,0,0;1/1:4618:0,0,0,0,0,0,0;1/1:4665:0,0,-2,0,0,0,0;1/1:4675:0,0,-2,0,0,0,0;1/1:4702:0,0,-2,0,0,0,0;1/1:4726:0,0,0,0,0,0,0;1/1:4748:0,0,-2,0,0,0,0;1/1:4764:0,0,-2,0,0,0,0;1/1:4780:0,0,-2,0,0,0,0;1/1:4781:0,0,-2,0,0,0,0;1/1:4782:0,0,0,0,0,0,0;1/1:4787:0,0,0,0,0,0,0;1/1:4793:0,0,-2,0,0,0,0;1/1:4858:0,0,0,0,0,0,0;1/1:4867:0,0,-2,0,0,0,0;1/1:4915:0,0,0,0,0,0,0;1/1:4962:0,0,-2,0,0,0,0;1/1:5222:0,0,0,0,0,0,0;1/1:5376:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:3091:0,0,0,0,0,0,0;-1/1:4601:0,-2,0,-2,0,0,0;-1/1:4615:0,-2,0,-2,0,0,0;-1/1:4617:0,-2,0,-2,0,0,0;-1/1:4622:0,-2,0,-2,0,0,0;-1/1:4623:0,-2,0,-2,0,0,0;-1/1:4647:0,-2,0,-2,0,0,0;-1/1:4652:0,-2,0,-2,0,0,0;-1/1:4674:0,-2,0,-2,0,0,0;-1/1:4683:0,-2,0,-2,0,0,0;-1/1:4696:0,-2,0,-2,0,0,0;-1/1:4697:0,-2,0,-2,0,0,0;-1/1:4706:0,-2,0,-2,0,0,0;-1/1:4710:0,0,0,0,0,0,0;-1/1:4720:0,-2,0,-2,0,0,0;-1/1:4726:0,-2,0,-2,0,0,0;-1/1:4745:0,-2,0,-2,0,0,0;-1/1:4783:0,-2,0,-2,0,0,0;-1/1:4801:0,-2,0,-2,0,0,0;-1/1:4804:0,-2,0,-2,0,0,0;-1/1:4807:0,0,0,0,0,0,0;-1/1:4860:0,-2,0,-2,0,0,0;-1/1:4865:0,-2,0,-2,0,0,0;-1/1:4932:0,0,0,0,0,0,0;-1/1:4961:0,0,0,0,0,0,0;-1/1:4980:0,0,0,0,0,0,0;-1/1:5002:0,0,0,0,0,0,0;-1/1:5048:0,0,0,0,0,0,0;-1/1:5057:0,0,0,0,0,0,0;-1/1:5083:0,0,0,0,0,0,0;-1/1:5116:0,0,0,0,0,0,0;1/1:5191:-2,0,0,0,0,0,0;-1/1:5371:0,0,0,0,0,0,0;-1/1:5436:0,0,0,0,0,0,0;-1/1:5469:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:3336:0,0,0,0,0,0,0;-1/1:5049:-2,0,0,0,0,0,0;1/1:5198:-4,0,0,0,0,0,0;1/1:5375:-1,0,0,0,1,0,0"
  | 14 => laurent_polynomial% "1/1:3363:0,0,0,0,0,0,0;1/1:5204:-1,0,0,0,1,0,0;-1/1:5367:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "-1/1:3379:0,2,0,0,0,0,0;1/1:5191:0,2,0,0,0,0,0;1/1:5213:0,2,0,0,0,0,0;-1/1:5435:-1,2,0,0,1,0,0;-1/1:5456:0,2,0,0,0,0,0;1/1:5466:-2,2,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:3402:0,0,0,0,0,0,0;1/1:5181:-1,0,0,0,1,0,0;-1/1:5359:-2,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:3413:0,0,0,0,0,0,0;-1/1:5222:0,0,0,0,0,0,0;-1/1:5243:-2,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3447:0,0,0,0,0,0,0;-1/1:5199:0,0,0,0,0,0,0;-1/1:5383:-2,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:3539:0,0,0,0,0,0,0;-1/1:5114:0,0,0,0,0,0,0;-1/1:5388:-2,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "-1/1:3542:0,0,0,0,0,0,0;1/1:5223:0,0,0,0,0,0,0;1/1:5242:-2,0,0,0,0,0,0;-1/1:5245:-1,0,0,0,1,0,0;1/1:5385:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:3587:0,0,0,0,0,0,0;-1/1:5120:0,0,0,0,0,0,0;-1/1:5163:-2,0,0,0,0,0,0;1/1:5184:-1,0,0,0,1,0,0"
  | 22 => laurent_polynomial% "1/1:3619:0,0,0,0,0,0,0;-1/1:5002:-2,0,0,0,0,0,0;-1/1:5186:0,0,0,0,0,0,0;1/1:5191:-4,0,0,0,0,0,0;1/1:5364:-1,0,0,0,1,0,0"
  | 23 => laurent_polynomial% "1/1:3822:0,0,0,0,0,0,0;-1/1:4759:0,0,0,0,0,0,0;-1/1:5101:0,-2,0,0,0,0,0;1/1:5388:0,-1,0,0,0,1,0"
  | 24 => laurent_polynomial% "1/1:3828:0,0,0,0,0,0,0;-1/1:4698:0,0,0,0,0,0,0;-1/1:5163:0,0,0,0,0,0,0;-1/1:5243:0,-2,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:3958:0,0,0,0,0,0,0;1/1:4971:0,0,0,0,0,0,0;1/1:5003:0,0,0,0,0,0,0;1/1:5217:0,-2,0,0,0,0,0;-1/1:5245:0,-1,0,0,0,1,0;1/1:5467:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "-1/1:3966:0,0,0,0,0,0,0;1/1:4960:0,-2,0,0,0,0,0;-1/1:5161:0,-1,0,0,0,1,0;1/1:5382:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "-1/1:4324:0,0,0,0,0,0,0;1/1:4671:0,0,0,0,0,0,0;-1/1:4683:0,0,0,-1,0,0,1;1/1:4696:0,0,0,0,0,0,0;1/1:4704:0,0,0,-2,0,0,0;1/1:5114:0,0,0,0,0,0,0;1/1:5221:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:2587:0,0,0,0,0,0,0;-1/1:4803:2,0,-2,-2,0,0,0;-1/1:4809:2,0,-2,-2,0,0,0;-1/1:4820:2,0,-2,-2,0,0,0;-1/1:4831:2,0,-2,-2,0,0,0;-1/1:5106:0,0,0,0,0,0,0;1/1:5120:0,0,0,0,0,0,0;-1/1:5223:0,0,0,0,0,0,0;1/1:5392:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:2593:0,0,0,0,0,0,0;-1/1:4655:0,2,-2,-2,0,0,0;-1/1:4799:0,2,-2,-2,0,0,0;-1/1:4827:0,2,-2,-2,0,0,0;-1/1:4830:0,2,-2,-2,0,0,0;-1/1:5105:0,0,0,0,0,0,0;1/1:5161:0,0,0,0,0,0,0;-1/1:5163:0,0,0,0,0,0,0;1/1:5391:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:3368:0,0,0,0,0,0,0;1/1:5104:-1,0,0,0,1,0,0;-1/1:5118:-2,0,0,0,0,0,0;-1/1:5161:0,0,0,0,0,0,0;-1/1:5167:-1,0,0,0,1,0,0"
  | 31 => laurent_polynomial% "1/1:3372:0,0,0,0,0,0,0;-1/1:5209:0,0,0,0,0,0,0;1/1:5239:-1,0,0,0,1,0,0;-1/1:5378:-2,0,0,0,0,0,0;-1/1:5457:-1,0,0,0,1,0,0"
  | _ => []

compact_certificate def operationsPart28 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3429:0,0,0,0,0,0,0;-1/1:5069:-2,0,0,0,0,0,0;-1/1:5228:0,0,0,0,0,0,0;1/1:5362:-1,0,0,0,1,0,0;1/1:5464:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:3583:0,0,0,0,0,0,0;-1/1:5180:0,0,0,0,0,0,0;1/1:5318:-1,0,0,0,1,0,0;-1/1:5361:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "-1/1:3786:0,0,0,0,0,0,0;1/1:4679:0,0,0,0,0,0,0;-1/1:5215:0,-1,0,0,0,1,0;1/1:5231:0,-2,0,0,0,0,0;1/1:5437:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:3847:0,0,0,0,0,0,0;-1/1:4629:0,-2,0,0,0,0,0;-1/1:5036:0,0,0,0,0,0,0;1/1:5311:0,-1,0,0,0,1,0;-1/1:5345:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "-1/1:4044:0,0,0,0,0,0,0;1/1:4688:0,0,0,0,0,0,0;-1/1:5217:0,-1,0,0,0,1,0;1/1:5230:0,-2,0,0,0,0,0;1/1:5245:0,0,0,0,0,0,0;1/1:5384:0,0,0,0,0,0,0;-1/1:5421:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:4182:0,0,0,0,0,0,0;-1/1:5420:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:4322:0,0,0,0,0,0,0;-1/1:4614:0,0,0,-2,0,0,0;-1/1:4700:0,0,0,0,0,0,0;-1/1:4752:0,0,0,0,0,0,0;1/1:4886:0,0,0,-1,0,0,1;-1/1:5433:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:4394:0,0,0,0,0,0,0;-1/1:4681:0,0,0,0,0,0,0;-1/1:4689:0,0,0,-2,0,0,0;-1/1:4727:0,0,0,0,0,0,0;1/1:4798:0,0,0,-1,0,0,1;-1/1:5421:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "-1/1:2762:0,0,0,0,0,0,0;1/1:4601:0,0,-2,0,0,0,0;1/1:4743:0,0,0,0,0,0,0;1/1:4748:0,0,-2,0,0,0,0;1/1:4780:0,0,-2,0,0,0,0;1/1:4781:0,0,-2,0,0,0,0;1/1:4865:0,0,0,0,0,0,0;1/1:4867:0,0,-2,0,0,0,0;1/1:4873:0,0,-2,0,0,0,0;1/1:5184:0,0,0,0,0,0,0;1/1:5235:0,0,0,0,0,0,0;-1/1:5395:0,0,0,0,0,0,0;-1/1:5472:0,0,0,0,0,0,0;1/1:5491:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:3326:0,0,0,0,0,0,0;1/1:5106:-1,0,0,0,1,0,0;-1/1:5120:-1,0,0,0,1,0,0;-1/1:5230:0,0,0,0,0,0,0;-1/1:5392:-1,0,0,0,1,0,0;1/1:5492:-1,0,0,0,1,0,0"
  | 10 => laurent_polynomial% "-1/1:3329:0,0,0,0,0,0,0;1/1:5103:0,0,0,0,0,0,0;-1/1:5105:-1,0,0,0,1,0,0;-1/1:5114:0,0,0,0,0,0,0;1/1:5161:-1,0,0,0,1,0,0;-1/1:5184:0,0,0,0,0,0,0;1/1:5234:-2,0,0,0,0,0,0;-1/1:5388:-2,0,0,0,0,0,0;1/1:5391:-1,0,0,0,1,0,0;1/1:5442:0,0,0,0,0,0,0;-1/1:5456:0,0,0,0,0,0,0;-1/1:5473:-2,0,0,0,0,0,0;1/1:5474:-2,0,0,0,0,0,0;1/1:5504:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3513:0,0,0,0,0,0,0;-1/1:5205:0,0,0,0,0,0,0;-1/1:5396:-2,0,0,0,0,0,0;1/1:5400:-1,0,0,0,1,0,0"
  | 12 => laurent_polynomial% "1/1:3552:0,0,0,0,0,0,0;-1/1:5205:-2,0,0,0,0,0,0;-1/1:5368:0,0,0,0,0,0,0;1/1:5434:-1,0,0,0,1,0,0"
  | 13 => laurent_polynomial% "1/1:3774:0,0,0,0,0,0,0;1/1:4690:0,-1,0,0,0,1,0;-1/1:5104:0,-2,0,0,0,0,0;1/1:5167:0,-2,0,0,0,0,0;-1/1:5395:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:2764:0,0,0,0,0,0,0;-1/1:4603:-2,2,-2,0,0,0,0;-1/1:4675:-2,2,-2,0,0,0,0;-1/1:4702:-2,2,-2,0,0,0,0;-1/1:4793:-2,2,-2,0,0,0,0;-1/1:4852:0,0,0,0,0,0,0;-1/1:4876:-2,2,-2,0,0,0,0;-1/1:4962:-2,2,-2,0,0,0,0;-1/1:5009:0,0,0,0,0,0,0;-1/1:5134:0,0,0,0,0,0,0;-1/1:5285:0,0,0,0,0,0,0;-1/1:5416:0,0,0,0,0,0,0;1/1:5473:0,0,0,0,0,0,0;1/1:5504:-2,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:2861:0,0,0,0,0,0,0;-1/1:4601:0,-2,-2,0,0,0,0;-1/1:4665:0,-2,-2,0,0,0,0;-1/1:4748:0,-2,-2,0,0,0,0;-1/1:4781:0,-2,-2,0,0,0,0;-1/1:4867:0,-2,-2,0,0,0,0;-1/1:4873:0,-2,-2,0,0,0,0;-1/1:4896:0,0,0,0,0,0,0;-1/1:5357:0,0,0,0,0,0,0;-1/1:5382:0,0,0,0,0,0,0;1/1:5490:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:2960:0,0,0,0,0,0,0;-1/1:4602:2,-2,0,-2,0,0,0;-1/1:4603:0,0,0,0,0,0,0;-1/1:4613:2,-2,0,-2,0,0,0;-1/1:4673:2,-2,0,-2,0,0,0;-1/1:4679:0,0,0,0,0,0,0;-1/1:4682:2,-2,0,-2,0,0,0;-1/1:4691:2,-2,0,-2,0,0,0;-1/1:4698:0,0,0,0,0,0,0;-1/1:4705:2,-2,0,-2,0,0,0;-1/1:4733:2,-2,0,-2,0,0,0;-1/1:4734:0,0,0,0,0,0,0;-1/1:4736:2,-2,0,-2,0,0,0;-1/1:4738:2,-2,0,-2,0,0,0;-1/1:4739:2,-2,0,-2,0,0,0;-1/1:4769:2,-2,0,-2,0,0,0;-1/1:4771:0,0,0,0,0,0,0;-1/1:4778:2,-2,0,-2,0,0,0;-1/1:4803:2,-2,0,-2,0,0,0;-1/1:4809:2,-2,0,-2,0,0,0;-1/1:4810:0,0,0,0,0,0,0;-1/1:4820:2,-2,0,-2,0,0,0;-1/1:4831:2,-2,0,-2,0,0,0;-1/1:4852:2,-2,0,-2,0,0,0;-1/1:4854:2,-2,0,-2,0,0,0;-1/1:4872:0,0,0,0,0,0,0;-1/1:4874:2,-2,0,-2,0,0,0;-1/1:4877:2,-2,0,-2,0,0,0;-1/1:4992:0,0,0,0,0,0,0;-1/1:5198:0,0,0,0,0,0,0;-1/1:5205:0,0,0,0,0,0,0;-1/1:5358:0,0,0,0,0,0,0;-1/1:5383:0,0,0,0,0,0,0;-1/1:5431:0,0,0,0,0,0,0;-1/1:5447:0,-2,0,0,0,0,0;-1/1:5463:0,0,0,0,0,0,0;1/1:5498:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:3033:0,0,0,0,0,0,0;-1/1:4620:0,0,0,0,0,0,0;-1/1:4640:0,0,0,0,0,0,0;-1/1:4647:-2,0,-2,0,0,0,0;-1/1:4649:-2,0,-2,0,0,0,0;-1/1:4652:-2,0,-2,0,0,0,0;-1/1:4653:-2,0,-2,0,0,0,0;-1/1:4673:0,0,0,0,0,0,0;-1/1:4705:0,0,0,0,0,0,0;-1/1:4738:0,0,0,0,0,0,0;-1/1:4801:-2,0,-2,0,0,0,0;-1/1:4804:-2,0,-2,0,0,0,0;-1/1:4808:-2,0,-2,0,0,0,0;-1/1:4814:-2,0,-2,0,0,0,0;-1/1:4822:-2,0,-2,0,0,0,0;-1/1:4826:-2,0,-2,0,0,0,0;-1/1:4828:-2,0,-2,0,0,0,0;-1/1:4832:-2,0,-2,0,0,0,0;-1/1:4835:-2,0,-2,0,0,0,0;-1/1:4838:-2,0,-2,0,0,0,0;-1/1:4840:-2,0,-2,0,0,0,0;-1/1:4847:-2,0,-2,0,0,0,0;-1/1:4850:0,0,0,0,0,0,0;-1/1:4857:0,0,0,0,0,0,0;-1/1:4863:0,0,0,0,0,0,0;-1/1:4871:-2,0,-2,0,0,0,0;-1/1:4877:0,0,0,0,0,0,0;-1/1:4881:-2,0,-2,0,0,0,0;-1/1:4883:-2,0,-2,0,0,0,0;-1/1:4884:-2,0,-2,0,0,0,0;-1/1:4952:0,0,0,0,0,0,0;-1/1:4982:-2,0,-2,0,0,0,0;-1/1:4983:-2,0,-2,0,0,0,0;-1/1:5012:0,0,0,0,0,0,0;-1/1:5030:0,0,0,0,0,0,0;-1/1:5036:0,0,0,0,0,0,0;-1/1:5046:0,0,0,0,0,0,0;-1/1:5124:0,0,0,0,0,0,0;-1/1:5136:0,0,0,0,0,0,0;-1/1:5148:0,0,0,0,0,0,0;-1/1:5156:0,0,0,0,0,0,0;1/1:5217:0,0,0,0,0,0,0;-1/1:5221:-1,0,0,0,1,0,0;1/1:5243:0,0,0,0,0,0,0;-1/1:5272:0,0,0,0,0,0,0;-1/1:5278:0,0,0,0,0,0,0;-1/1:5280:0,0,0,0,0,0,0;-1/1:5385:0,0,0,0,0,0,0;-1/1:5387:0,0,0,0,0,0,0;-1/1:5395:-1,0,0,0,1,0,0;1/1:5445:0,0,0,0,0,0,0;-1/1:5446:0,0,0,0,0,0,0;1/1:5447:-2,0,0,0,0,0,0;-1/1:5454:0,0,0,0,0,0,0;-1/1:5472:-1,0,0,0,1,0,0;1/1:5484:0,0,0,0,0,0,0;1/1:5491:-1,0,0,0,1,0,0;1/1:5492:0,0,0,0,0,0,0;1/1:5493:-2,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3132:0,0,0,0,0,0,0;-1/1:4602:2,0,0,-2,0,0,0;-1/1:4609:2,0,0,-2,0,0,0;-1/1:4626:2,0,0,-2,0,0,0;-1/1:4631:0,0,0,0,0,0,0;-1/1:4660:2,0,0,-2,0,0,0;-1/1:4663:0,0,0,0,0,0,0;-1/1:4664:2,0,0,-2,0,0,0;-1/1:4673:2,0,0,-2,0,0,0;-1/1:4682:2,0,0,-2,0,0,0;-1/1:4686:0,0,0,0,0,0,0;-1/1:4690:0,0,0,0,0,0,0;-1/1:4691:2,0,0,-2,0,0,0;-1/1:4703:0,0,0,0,0,0,0;-1/1:4705:2,0,0,-2,0,0,0;-1/1:4725:2,0,0,-2,0,0,0;-1/1:4738:2,0,0,-2,0,0,0;-1/1:4739:2,0,0,-2,0,0,0;-1/1:4740:2,0,0,-2,0,0,0;-1/1:4765:2,0,0,-2,0,0,0;-1/1:4769:2,0,0,-2,0,0,0;-1/1:4772:2,0,0,-2,0,0,0;-1/1:4775:2,0,0,-2,0,0,0;-1/1:4777:2,0,0,-2,0,0,0;-1/1:4778:2,0,0,-2,0,0,0;-1/1:4803:2,0,0,-2,0,0,0;-1/1:4809:2,0,0,-2,0,0,0;-1/1:4820:2,0,0,-2,0,0,0;-1/1:4823:2,0,0,-2,0,0,0;-1/1:4826:0,0,0,0,0,0,0;-1/1:4831:2,0,0,-2,0,0,0;-1/1:4832:0,0,0,0,0,0,0;-1/1:4841:2,0,0,-2,0,0,0;-1/1:4842:2,0,0,-2,0,0,0;-1/1:4847:0,0,0,0,0,0,0;-1/1:4859:2,0,0,-2,0,0,0;-1/1:4866:2,0,0,-2,0,0,0;-1/1:4867:0,0,0,0,0,0,0;-1/1:4870:0,0,0,0,0,0,0;-1/1:4871:0,0,0,0,0,0,0;-1/1:4874:2,0,0,-2,0,0,0;-1/1:4877:2,0,0,-2,0,0,0;-1/1:4898:0,0,0,0,0,0,0;-1/1:4901:2,0,0,-2,0,0,0;-1/1:4906:2,0,0,-2,0,0,0;-1/1:4908:2,0,0,-2,0,0,0;-1/1:4911:2,0,0,-2,0,0,0;-1/1:4924:2,0,0,-2,0,0,0;-1/1:4925:2,0,0,-2,0,0,0;-1/1:4926:0,0,0,0,0,0,0;-1/1:4934:0,0,0,0,0,0,0;-1/1:4954:2,0,0,-2,0,0,0;-1/1:4956:2,0,0,-2,0,0,0;-1/1:4964:2,0,0,-2,0,0,0;-1/1:4965:2,0,0,-2,0,0,0;-1/1:4991:0,0,0,0,0,0,0;-1/1:5071:0,0,0,0,0,0,0;-1/1:5078:0,0,0,0,0,0,0;-1/1:5096:0,0,0,0,0,0,0;-1/1:5105:0,0,0,0,0,0,0;1/1:5161:0,0,0,0,0,0,0;-1/1:5163:0,0,0,0,0,0,0;-1/1:5180:0,0,0,0,0,0,0;-1/1:5208:0,0,0,0,0,0,0;-1/1:5244:0,0,0,0,0,0,0;-1/1:5375:0,0,0,0,0,0,0;1/1:5391:0,0,0,0,0,0,0;-1/1:5422:0,0,0,0,0,0,0;-1/1:5424:0,0,0,0,0,0,0;-1/1:5430:0,0,0,0,0,0,0;-1/1:5437:0,0,0,0,0,0,0;1/1:5447:0,-2,0,0,0,0,0;-1/1:5488:0,0,0,0,0,0,0;1/1:5512:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "-1/1:3428:0,0,0,0,0,0,0;1/1:5101:0,0,0,0,0,0,0;1/1:5223:-2,0,0,0,0,0,0;1/1:5444:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:3591:0,0,0,0,0,0,0;1/1:5185:-1,0,0,0,1,0,0;-1/1:5357:0,0,0,0,0,0,0;-1/1:5401:-2,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:3854:0,0,0,0,0,0,0;-1/1:4686:0,-2,0,0,0,0,0;-1/1:5103:0,0,0,0,0,0,0;1/1:5114:0,0,0,0,0,0,0;1/1:5184:0,0,0,0,0,0,0;-1/1:5439:0,0,0,0,0,0,0;1/1:5446:0,-1,0,0,0,1,0"
  | 22 => laurent_polynomial% "1/1:3973:0,0,0,0,0,0,0;-1/1:4643:0,-2,0,0,0,0,0;-1/1:5157:0,0,0,0,0,0,0;-1/1:5244:-1,0,0,0,1,0,0;1/1:5276:0,-1,0,0,0,1,0;-1/1:5403:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:4024:0,0,0,0,0,0,0;-1/1:4960:0,0,0,0,0,0,0;1/1:5223:0,-1,0,0,0,1,0;-1/1:5234:0,-2,0,0,0,0,0;1/1:5388:0,-2,0,0,0,0,0;1/1:5473:0,-2,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:3316:0,0,0,0,0,0,0;-1/1:5186:-2,0,0,0,0,0,0;1/1:5372:-1,0,0,0,1,0,0;-1/1:5471:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:3361:0,0,0,0,0,0,0;1/1:5206:0,0,0,0,0,0,0;-1/1:5219:-1,0,0,0,1,0,0;-1/1:5311:0,0,0,0,0,0,0;1/1:5373:-2,0,0,0,0,0,0;1/1:5433:-1,0,0,0,1,0,0;1/1:5469:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:3364:0,0,0,0,0,0,0;1/1:5205:-1,0,0,0,1,0,0;-1/1:5400:-2,0,0,0,0,0,0;-1/1:5434:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:3442:0,0,0,0,0,0,0;-1/1:5185:0,0,0,0,0,0,0;-1/1:5397:-2,0,0,0,0,0,0;1/1:5401:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "1/1:3448:0,0,0,0,0,0,0;-1/1:5220:0,0,0,0,0,0,0;1/1:5365:0,0,0,0,0,0,0;-1/1:5391:0,0,0,0,0,0,0;1/1:5395:0,-1,0,0,0,1,0;1/1:5463:-1,0,0,0,1,0,0;-1/1:5518:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:3773:0,0,0,0,0,0,0;-1/1:4887:0,0,0,0,0,0,0;-1/1:5325:0,0,0,0,0,0,0;1/1:5397:0,0,0,0,0,0,0;1/1:5406:0,-1,0,0,0,1,0"
  | 30 => laurent_polynomial% "-1/1:3827:0,0,0,0,0,0,0;1/1:4620:0,0,0,0,0,0,0;1/1:5023:0,-2,0,0,0,0,0;-1/1:5025:0,-1,0,0,0,1,0;1/1:5026:0,0,0,0,0,0,0;1/1:5162:0,0,0,0,0,0,0;-1/1:5242:0,-2,0,0,0,0,0;1/1:5448:0,-1,0,0,0,1,0"
  | 31 => laurent_polynomial% "-1/1:3941:0,0,0,0,0,0,0;-1/1:5010:0,-1,0,0,0,1,0;-1/1:5102:-2,-1,0,0,0,1,0;1/1:5108:0,0,0,0,0,0,0;1/1:5135:0,-2,0,0,0,0,0;1/1:5390:0,0,0,0,0,0,0;1/1:5395:-2,0,0,0,0,0,0;-1/1:5455:0,0,0,0,0,0,0;-1/1:5457:-2,0,0,0,0,0,0;-1/1:5492:-1,0,0,0,1,0,0;1/1:5509:-2,0,0,0,0,0,0;1/1:5516:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def operationsPart29 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "-1/1:3981:0,0,0,0,0,0,0;1/1:5009:0,0,0,0,0,0,0;1/1:5137:0,0,0,0,0,0,0;1/1:5332:0,0,0,0,0,0,0;1/1:5426:-1,0,0,0,1,0,0;-1/1:5440:-2,0,0,0,0,0,0;1/1:5461:-2,0,0,0,0,0,0;-1/1:5474:-2,-2,0,0,0,0,0;-1/1:5481:0,-1,0,0,0,1,0"
  | 1 => laurent_polynomial% "1/1:4109:0,0,0,0,0,0,0;-1/1:4998:0,0,0,0,0,0,0;-1/1:5164:0,0,0,0,0,0,0;-1/1:5290:0,0,0,0,0,0,0;1/1:5429:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:2880:0,0,0,0,0,0,0;-1/1:4647:-2,0,-2,-2,0,0,0;-1/1:4652:-2,0,-2,-2,0,0,0;-1/1:4655:-2,0,-2,-2,0,0,0;-1/1:4799:-2,0,-2,-2,0,0,0;-1/1:4801:-2,0,-2,-2,0,0,0;-1/1:4804:-2,0,-2,-2,0,0,0;-1/1:4827:-2,0,-2,-2,0,0,0;-1/1:4830:-2,0,-2,-2,0,0,0;-1/1:5000:0,0,0,0,0,0,0;-1/1:5018:0,0,0,0,0,0,0;-1/1:5134:0,0,0,0,0,0,0;-1/1:5172:0,0,0,0,0,0,0;-1/1:5255:0,0,0,0,0,0,0;-1/1:5298:0,0,0,0,0,0,0;-1/1:5326:0,0,0,0,0,0,0;1/1:5388:0,0,0,0,0,0,0;-1/1:5396:-1,0,0,0,1,0,0;1/1:5398:-2,0,0,0,0,0,0;1/1:5400:0,0,0,0,0,0,0;1/1:5473:0,0,0,0,0,0,0;1/1:5491:-2,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "-1/1:2955:2,0,0,0,0,0,0;1/1:4600:0,-2,0,-2,0,0,0;1/1:4601:0,-2,0,-2,0,0,0;1/1:4615:0,-2,0,-2,0,0,0;1/1:4619:0,-2,0,-2,0,0,0;1/1:4622:0,-2,0,-2,0,0,0;1/1:4647:0,-2,0,-2,0,0,0;1/1:4652:0,-2,0,-2,0,0,0;1/1:4659:2,0,0,0,0,0,0;1/1:4666:0,-2,0,-2,0,0,0;1/1:4669:2,0,0,0,0,0,0;1/1:4674:0,-2,0,-2,0,0,0;1/1:4683:0,-2,0,-2,0,0,0;1/1:4687:2,0,0,0,0,0,0;1/1:4697:0,-2,0,-2,0,0,0;1/1:4704:0,-2,0,-2,0,0,0;1/1:4706:0,-2,0,-2,0,0,0;1/1:4720:0,-2,0,-2,0,0,0;1/1:4726:0,-2,0,-2,0,0,0;1/1:4731:2,0,0,0,0,0,0;1/1:4745:0,-2,0,-2,0,0,0;1/1:4749:2,0,0,0,0,0,0;1/1:4756:0,-2,0,-2,0,0,0;1/1:4783:0,-2,0,-2,0,0,0;1/1:4801:0,-2,0,-2,0,0,0;1/1:4804:0,-2,0,-2,0,0,0;1/1:4805:2,0,0,0,0,0,0;1/1:4968:2,0,0,0,0,0,0;1/1:5020:2,0,0,0,0,0,0;1/1:5032:2,0,0,0,0,0,0;1/1:5088:2,0,0,0,0,0,0;1/1:5155:2,0,0,0,0,0,0;1/1:5182:2,0,0,0,0,0,0;1/1:5206:2,0,0,0,0,0,0;1/1:5251:2,0,0,0,0,0,0;1/1:5300:2,0,0,0,0,0,0;-1/1:5311:2,0,0,0,0,0,0;1/1:5347:2,0,0,0,0,0,0;1/1:5369:2,0,0,0,0,0,0;-1/1:5376:0,0,0,0,0,0,0;-1/1:5386:0,0,0,0,0,0,0;1/1:5413:2,0,0,0,0,0,0;-1/1:5415:2,0,0,0,0,0,0;1/1:5423:1,0,0,0,1,0,0;1/1:5433:1,0,0,0,1,0,0;-1/1:5436:2,0,0,0,0,0,0;-1/1:5446:0,-2,0,0,0,0,0;-1/1:5446:2,0,0,0,0,0,0;1/1:5452:2,0,0,0,0,0,0;-1/1:5461:1,0,0,0,1,0,0;1/1:5462:1,0,0,0,1,0,0;1/1:5475:0,0,0,0,0,0,0;-1/1:5476:2,0,0,0,0,0,0;1/1:5500:0,0,0,0,0,0,0;-1/1:5513:2,0,0,0,0,0,0;-1/1:5521:2,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "-1/1:3322:0,0,0,0,0,0,0;-1/1:5228:-1,0,0,0,1,0,0;1/1:5362:-2,0,0,0,0,0,0;1/1:5441:0,0,0,0,0,0,0;1/1:5464:-1,0,0,0,1,0,0;-1/1:5487:0,0,0,0,0,0,0;1/1:5499:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:3378:0,0,0,0,0,0,0;1/1:5208:-1,0,0,0,1,0,0;-1/1:5380:-2,0,0,0,0,0,0;-1/1:5474:-2,-1,0,0,0,1,0"
  | 6 => laurent_polynomial% "-1/1:3416:2,0,0,0,0,0,0;1/1:5167:2,0,0,0,0,0,0;1/1:5390:2,0,0,0,0,0,0;1/1:5395:0,0,0,0,0,0,0;-1/1:5455:2,0,0,0,0,0,0;1/1:5472:0,0,0,0,0,0,0;-1/1:5492:1,0,0,0,1,0,0;-1/1:5527:2,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "-1/1:3837:0,0,0,0,0,0,0;1/1:5032:0,0,0,0,0,0,0;1/1:5042:0,0,0,0,0,0,0;-1/1:5101:-2,0,0,0,0,0,0;1/1:5261:0,0,0,0,0,0,0;1/1:5275:0,-2,0,0,0,0,0;-1/1:5416:0,-1,0,0,0,1,0;-1/1:5436:0,0,0,0,0,0,0;-1/1:5446:-2,-2,0,0,0,0,0;-1/1:5446:0,0,0,0,0,0,0;-1/1:5470:-2,0,0,0,0,0,0;1/1:5475:-2,0,0,0,0,0,0;-1/1:5531:-2,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "-1/1:3882:0,0,0,0,0,0,0;1/1:4737:0,0,0,0,0,0,0;1/1:5105:0,-2,0,0,0,0,0;-1/1:5161:0,-2,0,0,0,0,0;-1/1:5391:0,-2,0,0,0,0,0;1/1:5396:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:2754:0,0,0,0,0,0,0;-1/1:4601:0,-2,-2,0,0,0,0;-1/1:4665:0,-2,-2,0,0,0,0;-1/1:4780:0,-2,-2,0,0,0,0;-1/1:4781:0,-2,-2,0,0,0,0;-1/1:4867:0,-2,-2,0,0,0,0;-1/1:4873:0,-2,-2,0,0,0,0;-1/1:4959:0,0,0,0,0,0,0;-1/1:5205:0,0,0,0,0,0,0;-1/1:5359:0,0,0,0,0,0,0;-1/1:5367:0,0,0,0,0,0,0;-1/1:5475:0,0,0,0,0,0,0;-1/1:5491:0,-1,0,0,0,1,0;1/1:5504:0,-1,0,0,0,1,0"
  | 10 => laurent_polynomial% "1/1:2881:0,0,0,0,0,0,0;-1/1:4647:-2,0,-2,-2,0,0,0;-1/1:4648:-2,0,-2,-2,0,0,0;-1/1:4652:-2,0,-2,-2,0,0,0;-1/1:4801:-2,0,-2,-2,0,0,0;-1/1:4802:-2,0,-2,-2,0,0,0;-1/1:4804:-2,0,-2,-2,0,0,0;-1/1:4821:-2,0,-2,-2,0,0,0;-1/1:4824:-2,0,-2,-2,0,0,0;-1/1:5035:0,0,0,0,0,0,0;-1/1:5051:0,0,0,0,0,0,0;-1/1:5147:0,0,0,0,0,0,0;-1/1:5247:0,0,0,0,0,0,0;-1/1:5266:0,0,0,0,0,0,0;-1/1:5293:0,0,0,0,0,0,0;-1/1:5344:0,0,0,0,0,0,0;1/1:5395:0,0,0,0,0,0,0;-1/1:5397:-1,0,0,0,1,0,0;1/1:5399:-2,0,0,0,0,0,0;1/1:5401:0,0,0,0,0,0,0;1/1:5472:0,0,0,0,0,0,0;1/1:5474:-2,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3507:0,0,0,0,0,0,0;-1/1:5190:-2,0,0,0,0,0,0;-1/1:5219:0,0,0,0,0,0,0;1/1:5373:-1,0,0,0,1,0,0;1/1:5433:0,0,0,0,0,0,0;1/1:5476:-2,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:3667:0,0,0,0,0,0,0;-1/1:5220:-2,0,0,0,0,0,0;1/1:5365:-2,0,0,0,0,0,0;-1/1:5391:-2,0,0,0,0,0,0;1/1:5395:-2,-1,0,0,0,1,0;-1/1:5422:0,0,0,0,0,0,0;1/1:5468:-1,0,0,0,1,0,0;-1/1:5524:-2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:3787:0,0,0,0,0,0,0;-1/1:5134:0,-1,0,0,0,1,0;1/1:5159:0,-2,0,0,0,0,0;1/1:5249:0,0,0,0,0,0,0;1/1:5327:0,0,0,0,0,0,0;-1/1:5371:-2,0,0,0,0,0,0;1/1:5421:-1,0,0,0,1,0,0;-1/1:5433:0,0,0,0,0,0,0;1/1:5473:0,-1,0,0,0,1,0;1/1:5484:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:3878:0,0,0,0,0,0,0;-1/1:5215:0,0,0,0,0,0,0;1/1:5231:0,-1,0,0,0,1,0;-1/1:5492:0,-2,0,0,0,0,0"
  | 15 => laurent_polynomial% "-1/1:2753:0,0,0,0,0,0,0;1/1:4601:0,-2,-2,0,0,0,0;1/1:4665:0,-2,-2,0,0,0,0;1/1:4748:0,-2,-2,0,0,0,0;1/1:4754:0,0,0,0,0,0,0;1/1:4780:0,-2,-2,0,0,0,0;1/1:4867:0,-2,-2,0,0,0,0;1/1:4873:0,-2,-2,0,0,0,0;1/1:5185:0,0,0,0,0,0,0;1/1:5422:0,0,0,0,0,0,0;1/1:5438:0,0,0,0,0,0,0;-1/1:5487:0,0,0,0,0,0,0;-1/1:5541:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:2956:0,0,0,0,0,0,0;-1/1:4600:0,-2,0,-2,0,0,0;-1/1:4601:0,-2,0,-2,0,0,0;-1/1:4615:0,-2,0,-2,0,0,0;-1/1:4617:0,-2,0,-2,0,0,0;-1/1:4618:0,0,0,0,0,0,0;-1/1:4619:0,-2,0,-2,0,0,0;-1/1:4623:0,-2,0,-2,0,0,0;-1/1:4647:0,-2,0,-2,0,0,0;-1/1:4652:0,-2,0,-2,0,0,0;-1/1:4662:0,0,0,0,0,0,0;-1/1:4666:0,-2,0,-2,0,0,0;-1/1:4674:0,-2,0,-2,0,0,0;-1/1:4696:0,-2,0,-2,0,0,0;-1/1:4704:0,-2,0,-2,0,0,0;-1/1:4706:0,-2,0,-2,0,0,0;-1/1:4711:0,0,0,0,0,0,0;-1/1:4720:0,-2,0,-2,0,0,0;-1/1:4724:0,0,0,0,0,0,0;-1/1:4745:0,-2,0,-2,0,0,0;-1/1:4750:0,0,0,0,0,0,0;-1/1:4756:0,-2,0,-2,0,0,0;-1/1:4801:0,-2,0,-2,0,0,0;-1/1:4804:0,-2,0,-2,0,0,0;-1/1:4839:0,0,0,0,0,0,0;-1/1:4860:0,-2,0,-2,0,0,0;-1/1:4861:0,0,0,0,0,0,0;-1/1:4865:0,-2,0,-2,0,0,0;-1/1:4919:0,0,0,0,0,0,0;-1/1:4995:0,0,0,0,0,0,0;-1/1:5081:0,0,0,0,0,0,0;-1/1:5179:0,0,0,0,0,0,0;-1/1:5204:0,0,0,0,0,0,0;1/1:5218:0,0,0,0,0,0,0;-1/1:5220:0,0,0,0,0,0,0;-1/1:5377:0,0,0,0,0,0,0;-1/1:5434:0,0,0,0,0,0,0;1/1:5446:0,-1,0,0,0,1,0;-1/1:5448:0,0,0,0,0,0,0;1/1:5491:0,-2,0,0,0,0,0;-1/1:5517:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:3031:0,0,0,0,0,0,0;-1/1:4614:0,0,0,0,0,0,0;-1/1:4647:0,-2,-2,0,0,0,0;-1/1:4649:0,-2,-2,0,0,0,0;-1/1:4651:0,-2,-2,0,0,0,0;-1/1:4652:0,-2,-2,0,0,0,0;-1/1:4653:0,-2,-2,0,0,0,0;-1/1:4661:0,-2,-2,0,0,0,0;-1/1:4698:0,0,0,0,0,0,0;-1/1:4716:0,0,0,0,0,0,0;-1/1:4771:0,0,0,0,0,0,0;-1/1:4798:0,0,0,0,0,0,0;-1/1:4801:0,-2,-2,0,0,0,0;-1/1:4804:0,-2,-2,0,0,0,0;-1/1:4814:0,-2,-2,0,0,0,0;-1/1:4822:0,-2,-2,0,0,0,0;-1/1:4826:0,-2,-2,0,0,0,0;-1/1:4828:0,-2,-2,0,0,0,0;-1/1:4832:0,-2,-2,0,0,0,0;-1/1:4835:0,-2,-2,0,0,0,0;-1/1:4840:0,-2,-2,0,0,0,0;-1/1:4843:0,-2,-2,0,0,0,0;-1/1:4844:0,-2,-2,0,0,0,0;-1/1:4847:0,-2,-2,0,0,0,0;-1/1:4871:0,-2,-2,0,0,0,0;-1/1:4881:0,-2,-2,0,0,0,0;-1/1:4883:0,-2,-2,0,0,0,0;-1/1:4884:0,-2,-2,0,0,0,0;-1/1:4891:0,0,0,0,0,0,0;-1/1:4957:0,0,0,0,0,0,0;-1/1:4983:0,-2,-2,0,0,0,0;-1/1:4996:0,0,0,0,0,0,0;-1/1:5003:0,0,0,0,0,0,0;-1/1:5058:0,0,0,0,0,0,0;-1/1:5074:0,0,0,0,0,0,0;-1/1:5190:0,0,0,0,0,0,0;-1/1:5364:0,0,0,0,0,0,0;-1/1:5379:0,0,0,0,0,0,0;-1/1:5383:0,0,0,0,0,0,0;-1/1:5432:0,0,0,0,0,0,0;-1/1:5435:0,0,0,0,0,0,0;-1/1:5470:0,0,0,0,0,0,0;-1/1:5472:0,-1,0,0,0,1,0;1/1:5475:0,0,0,0,0,0,0;1/1:5476:0,0,0,0,0,0,0;1/1:5489:0,0,0,0,0,0,0;-1/1:5504:0,-1,0,0,0,1,0;-1/1:5524:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3032:0,0,0,0,0,0,0;-1/1:4624:0,0,0,0,0,0,0;-1/1:4629:0,0,0,0,0,0,0;-1/1:4647:-2,0,-2,0,0,0,0;-1/1:4651:-2,0,-2,0,0,0,0;-1/1:4652:-2,0,-2,0,0,0,0;-1/1:4661:-2,0,-2,0,0,0,0;-1/1:4682:0,0,0,0,0,0,0;-1/1:4691:0,0,0,0,0,0,0;-1/1:4739:0,0,0,0,0,0,0;-1/1:4762:0,0,0,0,0,0,0;-1/1:4767:0,0,0,0,0,0,0;-1/1:4769:0,0,0,0,0,0,0;-1/1:4797:0,0,0,0,0,0,0;-1/1:4801:-2,0,-2,0,0,0,0;-1/1:4804:-2,0,-2,0,0,0,0;-1/1:4808:-2,0,-2,0,0,0,0;-1/1:4814:-2,0,-2,0,0,0,0;-1/1:4822:-2,0,-2,0,0,0,0;-1/1:4826:-2,0,-2,0,0,0,0;-1/1:4828:-2,0,-2,0,0,0,0;-1/1:4832:-2,0,-2,0,0,0,0;-1/1:4838:-2,0,-2,0,0,0,0;-1/1:4840:-2,0,-2,0,0,0,0;-1/1:4843:-2,0,-2,0,0,0,0;-1/1:4844:-2,0,-2,0,0,0,0;-1/1:4847:-2,0,-2,0,0,0,0;-1/1:4871:-2,0,-2,0,0,0,0;-1/1:4883:-2,0,-2,0,0,0,0;-1/1:4884:-2,0,-2,0,0,0,0;-1/1:4887:0,0,0,0,0,0,0;-1/1:4982:-2,0,-2,0,0,0,0;-1/1:4983:-2,0,-2,0,0,0,0;-1/1:5005:0,0,0,0,0,0,0;-1/1:5017:0,0,0,0,0,0,0;-1/1:5023:0,0,0,0,0,0,0;-1/1:5041:0,0,0,0,0,0,0;-1/1:5125:0,0,0,0,0,0,0;-1/1:5133:0,0,0,0,0,0,0;-1/1:5145:0,0,0,0,0,0,0;-1/1:5157:0,0,0,0,0,0,0;-1/1:5169:0,0,0,0,0,0,0;1/1:5215:0,0,0,0,0,0,0;-1/1:5216:-1,0,0,0,1,0,0;1/1:5242:0,0,0,0,0,0,0;-1/1:5244:-1,0,0,0,1,0,0;-1/1:5275:0,0,0,0,0,0,0;-1/1:5315:0,0,0,0,0,0,0;-1/1:5320:0,0,0,0,0,0,0;-1/1:5388:-1,0,0,0,1,0,0;1/1:5392:-2,0,0,0,0,0,0;1/1:5446:-2,0,0,0,0,0,0;-1/1:5447:0,0,0,0,0,0,0;-1/1:5448:-1,0,0,0,1,0,0;-1/1:5473:-1,0,0,0,1,0,0;1/1:5474:-1,0,0,0,1,0,0;-1/1:5481:0,0,0,0,0,0,0;1/1:5493:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "-1/1:3594:0,0,0,0,0,0,0;1/1:5183:0,0,0,0,0,0,0;-1/1:5220:-1,0,0,0,1,0,0;1/1:5365:-1,0,0,0,1,0,0;-1/1:5391:-1,0,0,0,1,0,0;1/1:5395:-1,-1,0,0,1,1,0;1/1:5448:0,-2,0,0,0,0,0;-1/1:5453:0,0,0,0,0,0,0;1/1:5463:-2,0,0,0,0,0,0;1/1:5468:0,0,0,0,0,0,0;-1/1:5524:-1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "-1/1:3991:0,0,0,0,0,0,0;1/1:5020:0,0,0,0,0,0,0;1/1:5256:0,0,0,0,0,0,0;-1/1:5384:-2,0,0,0,0,0,0;1/1:5421:-2,0,0,0,0,0,0;1/1:5438:-1,0,0,0,1,0,0;1/1:5449:0,-2,0,0,0,0,0;1/1:5479:0,0,0,0,0,0,0;-1/1:5487:-1,0,0,0,1,0,0;1/1:5500:-2,0,0,0,0,0,0;-1/1:5521:0,0,0,0,0,0,0;-1/1:5541:-1,0,0,0,1,0,0"
  | 21 => laurent_polynomial% "-1/1:4362:0,0,0,0,0,0,0;1/1:4707:0,0,0,0,0,0,0;1/1:4766:0,0,0,-2,0,0,0;-1/1:4773:0,0,0,-1,0,0,1;1/1:4939:0,0,0,0,0,0,0;1/1:5060:0,0,0,0,0,0,0;1/1:5226:0,0,0,0,0,0,0;-1/1:5361:0,0,0,0,0,0,0;1/1:5430:0,0,0,0,0,0,0;-1/1:5441:0,0,0,0,0,0,0;-1/1:5447:0,-2,0,0,0,0,0;1/1:5487:0,0,0,0,0,0,0;1/1:5532:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:2755:0,0,0,0,0,0,0;-1/1:4601:-2,0,-2,0,0,0,0;-1/1:4665:-2,0,-2,0,0,0,0;-1/1:4748:-2,0,-2,0,0,0,0;-1/1:4778:0,0,0,0,0,0,0;-1/1:4780:-2,0,-2,0,0,0,0;-1/1:4781:-2,0,-2,0,0,0,0;-1/1:4867:-2,0,-2,0,0,0,0;-1/1:5010:0,0,0,0,0,0,0;-1/1:5102:-2,0,0,0,0,0,0;-1/1:5168:0,0,0,0,0,0,0;-1/1:5303:0,0,0,0,0,0,0;1/1:5391:0,0,0,0,0,0,0;-1/1:5446:-2,0,0,0,0,0,0;-1/1:5474:-1,0,0,0,1,0,0;-1/1:5494:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "-1/1:3128:0,0,0,0,0,0,0;1/1:4600:-2,0,0,-2,0,0,0;1/1:4601:-2,0,0,-2,0,0,0;1/1:4614:-2,0,0,-2,0,0,0;1/1:4615:-2,0,0,-2,0,0,0;1/1:4616:-2,0,0,-2,0,0,0;1/1:4619:-2,0,0,-2,0,0,0;1/1:4622:-2,0,0,-2,0,0,0;1/1:4625:-2,0,0,-2,0,0,0;1/1:4647:-2,0,0,-2,0,0,0;1/1:4652:-2,0,0,-2,0,0,0;1/1:4654:0,0,0,0,0,0,0;1/1:4655:-2,0,0,-2,0,0,0;1/1:4666:-2,0,0,-2,0,0,0;1/1:4674:-2,0,0,-2,0,0,0;1/1:4678:0,0,0,0,0,0,0;1/1:4683:-2,0,0,-2,0,0,0;1/1:4689:-2,0,0,-2,0,0,0;1/1:4697:-2,0,0,-2,0,0,0;1/1:4702:-2,0,0,-2,0,0,0;1/1:4704:-2,0,0,-2,0,0,0;1/1:4706:-2,0,0,-2,0,0,0;1/1:4716:-2,0,0,-2,0,0,0;1/1:4720:-2,0,0,-2,0,0,0;1/1:4726:-2,0,0,-2,0,0,0;1/1:4745:-2,0,0,-2,0,0,0;1/1:4747:-2,0,0,-2,0,0,0;1/1:4752:-2,0,0,-2,0,0,0;1/1:4753:0,0,0,0,0,0,0;1/1:4756:-2,0,0,-2,0,0,0;1/1:4762:0,0,0,0,0,0,0;1/1:4783:-2,0,0,-2,0,0,0;1/1:4790:-2,0,0,-2,0,0,0;1/1:4798:-2,0,0,-2,0,0,0;1/1:4799:-2,0,0,-2,0,0,0;1/1:4801:-2,0,0,-2,0,0,0;1/1:4804:-2,0,0,-2,0,0,0;1/1:4827:-2,0,0,-2,0,0,0;1/1:4830:-2,0,0,-2,0,0,0;1/1:4849:-2,0,0,-2,0,0,0;1/1:4856:-2,0,0,-2,0,0,0;1/1:4894:-2,0,0,-2,0,0,0;1/1:4896:-2,0,0,-2,0,0,0;1/1:4897:0,0,0,0,0,0,0;1/1:4899:0,0,0,0,0,0,0;1/1:4912:0,0,0,0,0,0,0;1/1:4931:0,0,0,0,0,0,0;1/1:4957:-2,0,0,-2,0,0,0;1/1:4959:-2,0,0,-2,0,0,0;1/1:4978:0,0,0,0,0,0,0;1/1:5010:0,0,0,0,0,0,0;1/1:5024:0,0,0,0,0,0,0;1/1:5030:0,0,0,0,0,0,0;1/1:5041:0,0,0,0,0,0,0;1/1:5046:0,0,0,0,0,0,0;-1/1:5065:0,0,0,0,0,0,0;-1/1:5090:0,-2,0,0,0,0,0;1/1:5091:0,0,0,0,0,0,0;1/1:5102:-2,0,0,0,0,0,0;1/1:5130:0,0,0,0,0,0,0;1/1:5145:0,0,0,0,0,0,0;1/1:5176:0,0,0,0,0,0,0;1/1:5203:0,0,0,0,0,0,0;1/1:5207:0,0,0,0,0,0,0;-1/1:5243:0,0,0,0,0,0,0;1/1:5263:0,0,0,0,0,0,0;1/1:5272:0,0,0,0,0,0,0;1/1:5283:0,0,0,0,0,0,0;1/1:5286:0,0,0,0,0,0,0;1/1:5292:0,0,0,0,0,0,0;1/1:5302:0,0,0,0,0,0,0;1/1:5306:0,0,0,0,0,0,0;1/1:5329:0,0,0,0,0,0,0;1/1:5338:0,0,0,0,0,0,0;1/1:5342:0,0,0,0,0,0,0;-1/1:5362:0,0,0,0,0,0,0;1/1:5382:-1,0,0,0,1,0,0;1/1:5387:0,0,0,0,0,0,0;1/1:5406:0,0,0,0,0,0,0;1/1:5410:0,0,0,0,0,0,0;-1/1:5420:0,0,0,0,0,0,0;-1/1:5422:-2,0,0,0,0,0,0;-1/1:5424:-2,0,0,0,0,0,0;-1/1:5427:0,0,0,0,0,0,0;-1/1:5430:-2,0,0,0,0,0,0;1/1:5432:-1,0,0,0,1,0,0;-1/1:5437:-2,0,0,0,0,0,0;1/1:5439:-1,0,0,0,1,0,0;-1/1:5445:0,0,0,0,0,0,0;1/1:5447:-2,-2,0,0,0,0,0;1/1:5447:0,0,0,0,0,0,0;1/1:5448:-1,0,0,0,1,0,0;1/1:5451:0,0,0,0,0,0,0;1/1:5453:0,0,0,0,0,0,0;1/1:5454:0,0,0,0,0,0,0;-1/1:5459:0,0,0,0,0,0,0;-1/1:5467:0,0,0,0,0,0,0;1/1:5472:-1,-1,0,0,1,1,0;-1/1:5478:0,0,0,0,0,0,0;1/1:5485:0,0,0,0,0,0,0;-1/1:5488:-2,0,0,0,0,0,0;-1/1:5492:0,-1,0,0,0,1,0;-1/1:5501:0,0,0,0,0,0,0;-1/1:5504:-1,0,0,0,1,0,0;1/1:5506:0,0,0,0,0,0,0;1/1:5512:-2,0,0,0,0,0,0;-1/1:5514:-2,0,0,0,0,0,0;1/1:5524:-1,0,0,0,1,0,0;1/1:5537:-1,0,0,0,1,0,0;1/1:5546:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:4311:0,0,0,0,0,0,0;1/1:4667:0,0,0,-1,0,0,1;-1/1:4684:0,0,0,-2,0,0,0;-1/1:4888:0,0,0,0,0,0,0;-1/1:4918:0,0,0,0,0,0,0;-1/1:5117:0,0,0,0,0,0,0;-1/1:5291:0,0,0,0,0,0,0;-1/1:5307:0,0,0,0,0,0,0;-1/1:5326:0,0,0,0,0,0,0;-1/1:5347:0,0,0,0,0,0,0;1/1:5366:0,0,0,0,0,0,0;1/1:5374:0,0,0,0,0,0,0;-1/1:5433:-1,0,0,0,1,0,0;1/1:5443:-2,0,0,0,0,0,0;1/1:5447:0,-1,0,0,0,1,0;-1/1:5462:0,0,0,0,0,0,0;-1/1:5502:-1,0,0,0,1,0,0"
  | 25 => laurent_polynomial% "-1/1:4314:0,0,0,0,0,0,0;1/1:4611:0,0,0,0,0,0,0;1/1:4763:0,0,0,-2,0,0,0;-1/1:4782:0,0,0,-1,0,0,1;1/1:5191:0,0,0,0,0,0,0;1/1:5239:0,0,0,0,0,0,0;1/1:5440:0,0,0,0,0,0,0;-1/1:5457:0,0,0,0,0,0,0;1/1:5459:0,0,0,0,0,0,0;-1/1:5461:0,0,0,0,0,0,0;1/1:5474:0,-2,0,0,0,0,0;1/1:5492:0,-1,0,0,0,1,0;1/1:5517:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:4334:0,0,0,0,0,0,0;-1/1:4776:0,0,0,0,0,0,0;-1/1:4894:0,0,0,-2,0,0,0;1/1:4957:0,0,0,-1,0,0,1;-1/1:5049:0,0,0,0,0,0,0;-1/1:5197:0,0,0,0,0,0,0;1/1:5198:-2,0,0,0,0,0,0;-1/1:5211:0,0,0,0,0,0,0;1/1:5214:0,0,0,0,0,0,0;1/1:5474:0,-2,0,0,0,0,0"
  | 27 => laurent_polynomial% "-1/1:4307:2,0,0,0,0,0,0;1/1:4609:2,0,0,0,0,0,0;-1/1:4664:2,0,0,-1,0,0,1;1/1:4772:2,0,0,-2,0,0,0;1/1:5115:2,0,0,0,0,0,0;1/1:5191:1,0,0,0,1,0,0;1/1:5305:2,0,0,0,0,0,0;1/1:5324:2,0,0,0,0,0,0;1/1:5345:2,0,0,0,0,0,0;-1/1:5358:2,0,0,0,0,0,0;-1/1:5426:2,0,0,0,0,0,0;-1/1:5435:0,0,0,0,0,0,0;1/1:5440:1,0,0,0,1,0,0;-1/1:5447:2,-2,0,0,0,0,0;1/1:5459:1,0,0,0,1,0,0;-1/1:5461:1,0,0,0,1,0,0;1/1:5474:1,-2,0,0,1,0,0;1/1:5482:2,0,0,0,0,0,0;1/1:5492:1,-1,0,0,1,1,0;1/1:5495:2,0,0,0,0,0,0;1/1:5517:1,0,0,0,1,0,0;-1/1:5524:0,0,0,0,0,0,0;1/1:5532:2,0,0,0,0,0,0;-1/1:5553:1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "1/1:2756:0,0,0,0,0,0,0;-1/1:4601:-2,0,-2,0,0,0,0;-1/1:4665:-2,0,-2,0,0,0,0;-1/1:4748:-2,0,-2,0,0,0,0;-1/1:4781:-2,0,-2,0,0,0,0;-1/1:4867:-2,0,-2,0,0,0,0;-1/1:4873:-2,0,-2,0,0,0,0;-1/1:4874:0,0,0,0,0,0,0;-1/1:5042:0,0,0,0,0,0,0;1/1:5101:-2,0,0,0,0,0,0;-1/1:5113:0,0,0,0,0,0,0;-1/1:5447:-2,0,0,0,0,0,0;-1/1:5484:0,0,0,0,0,0,0;-1/1:5485:0,0,0,0,0,0,0;-1/1:5491:-1,0,0,0,1,0,0;1/1:5504:-1,0,0,0,1,0,0"
  | 29 => laurent_polynomial% "-1/1:2758:0,0,0,0,0,0,0;1/1:4602:2,-2,-2,0,0,0,0;1/1:4694:2,-2,-2,0,0,0,0;1/1:4708:2,-2,-2,0,0,0,0;1/1:4791:2,-2,-2,0,0,0,0;1/1:4792:2,-2,-2,0,0,0,0;1/1:4916:2,-2,-2,0,0,0,0;1/1:4951:0,0,0,0,0,0,0;1/1:5204:0,0,0,0,0,0,0;1/1:5363:0,0,0,0,0,0,0;1/1:5400:0,0,0,0,0,0,0;1/1:5437:0,0,0,0,0,0,0;-1/1:5447:0,-1,0,0,0,1,0;1/1:5469:0,0,0,0,0,0,0;-1/1:5498:0,0,0,0,0,0,0;-1/1:5521:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:3274:0,0,0,0,0,0,0;1/1:5190:-1,0,0,0,1,0,0;-1/1:5373:0,0,0,0,0,0,0;-1/1:5374:-2,0,0,0,0,0,0;-1/1:5447:-2,-1,0,0,0,1,0;1/1:5462:-2,0,0,0,0,0,0;-1/1:5476:-1,0,0,0,1,0,0"
  | 31 => laurent_polynomial% "1/1:3531:0,0,0,0,0,0,0;-1/1:5228:-2,0,0,0,0,0,0;-1/1:5425:0,0,0,0,0,0,0;1/1:5441:-1,0,0,0,1,0,0;1/1:5464:-2,0,0,0,0,0,0;1/1:5473:0,0,0,0,0,0,0;-1/1:5487:-1,0,0,0,1,0,0;-1/1:5504:0,-2,0,0,0,0,0;-1/1:5532:-1,0,0,0,1,0,0"
  | _ => []

}
certificate_batch {
compact_certificate def operationsPart30 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:3541:0,0,0,0,0,0,0;-1/1:5208:0,0,0,0,0,0,0;-1/1:5377:-2,0,0,0,0,0,0;1/1:5380:-1,0,0,0,1,0,0;1/1:5446:-2,-1,0,0,0,1,0;1/1:5474:-1,-1,0,0,1,1,0"
  | 1 => laurent_polynomial% "1/1:4316:0,0,0,0,0,0,0;-1/1:4768:0,0,0,0,0,0,0;-1/1:4776:0,0,0,-2,0,0,0;1/1:4849:0,0,0,-1,0,0,1;-1/1:4894:0,0,0,0,0,0,0;-1/1:5425:0,0,0,0,0,0,0;-1/1:5429:0,0,0,0,0,0,0;-1/1:5463:0,0,0,0,0,0,0;1/1:5473:0,0,0,0,0,0,0;-1/1:5504:0,-2,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:4368:0,0,0,0,0,0,0;-1/1:4627:0,0,0,0,0,0,0;-1/1:4713:0,0,0,-2,0,0,0;-1/1:4861:0,0,0,0,0,0,0;1/1:4875:0,0,0,-1,0,0,1;-1/1:5180:0,0,0,0,0,0,0;-1/1:5381:0,0,0,0,0,0,0;-1/1:5446:0,-2,0,0,0,0,0;-1/1:5467:0,0,0,0,0,0,0;-1/1:5476:0,0,0,0,0,0,0;1/1:5489:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:3129:0,0,0,0,0,0,0;-1/1:4601:-2,0,0,-2,0,0,0;-1/1:4611:-2,0,0,-2,0,0,0;-1/1:4615:-2,0,0,-2,0,0,0;-1/1:4617:-2,0,0,-2,0,0,0;-1/1:4622:-2,0,0,-2,0,0,0;-1/1:4623:-2,0,0,-2,0,0,0;-1/1:4627:-2,0,0,-2,0,0,0;-1/1:4635:-2,0,0,-2,0,0,0;-1/1:4647:-2,0,0,-2,0,0,0;-1/1:4648:-2,0,0,-2,0,0,0;-1/1:4652:-2,0,0,-2,0,0,0;-1/1:4658:0,0,0,0,0,0,0;-1/1:4674:-2,0,0,-2,0,0,0;-1/1:4680:0,0,0,0,0,0,0;-1/1:4683:-2,0,0,-2,0,0,0;-1/1:4693:-2,0,0,-2,0,0,0;-1/1:4696:-2,0,0,-2,0,0,0;-1/1:4697:-2,0,0,-2,0,0,0;-1/1:4706:-2,0,0,-2,0,0,0;-1/1:4713:-2,0,0,-2,0,0,0;-1/1:4715:0,0,0,0,0,0,0;-1/1:4720:-2,0,0,-2,0,0,0;-1/1:4726:-2,0,0,-2,0,0,0;-1/1:4745:-2,0,0,-2,0,0,0;-1/1:4754:-2,0,0,-2,0,0,0;-1/1:4766:-2,0,0,-2,0,0,0;-1/1:4773:-2,0,0,-2,0,0,0;-1/1:4782:-2,0,0,-2,0,0,0;-1/1:4783:-2,0,0,-2,0,0,0;-1/1:4788:-2,0,0,-2,0,0,0;-1/1:4789:0,0,0,0,0,0,0;-1/1:4791:0,0,0,0,0,0,0;-1/1:4794:-2,0,0,-2,0,0,0;-1/1:4795:0,0,0,0,0,0,0;-1/1:4796:-2,0,0,-2,0,0,0;-1/1:4801:-2,0,0,-2,0,0,0;-1/1:4802:-2,0,0,-2,0,0,0;-1/1:4804:-2,0,0,-2,0,0,0;-1/1:4821:-2,0,0,-2,0,0,0;-1/1:4824:-2,0,0,-2,0,0,0;-1/1:4860:-2,0,0,-2,0,0,0;-1/1:4863:0,0,0,0,0,0,0;-1/1:4865:-2,0,0,-2,0,0,0;-1/1:4893:0,0,0,0,0,0,0;-1/1:4913:-2,0,0,-2,0,0,0;-1/1:4914:-2,0,0,-2,0,0,0;-1/1:4933:0,0,0,0,0,0,0;-1/1:4938:-2,0,0,-2,0,0,0;-1/1:4939:-2,0,0,-2,0,0,0;-1/1:4979:0,0,0,0,0,0,0;-1/1:5005:0,0,0,0,0,0,0;-1/1:5012:0,0,0,0,0,0,0;-1/1:5023:0,0,0,0,0,0,0;-1/1:5029:0,0,0,0,0,0,0;-1/1:5042:0,0,0,0,0,0,0;1/1:5066:0,0,0,0,0,0,0;-1/1:5092:0,0,0,0,0,0,0;1/1:5101:-2,0,0,0,0,0,0;-1/1:5136:0,0,0,0,0,0,0;-1/1:5151:0,0,0,0,0,0,0;-1/1:5169:0,0,0,0,0,0,0;-1/1:5196:0,0,0,0,0,0,0;-1/1:5212:0,0,0,0,0,0,0;1/1:5242:0,0,0,0,0,0,0;-1/1:5256:0,0,0,0,0,0,0;-1/1:5261:0,0,0,0,0,0,0;-1/1:5285:0,0,0,0,0,0,0;-1/1:5288:0,0,0,0,0,0,0;-1/1:5299:0,0,0,0,0,0,0;-1/1:5305:0,0,0,0,0,0,0;-1/1:5311:0,0,0,0,0,0,0;-1/1:5312:0,0,0,0,0,0,0;-1/1:5320:0,0,0,0,0,0,0;-1/1:5331:0,0,0,0,0,0,0;1/1:5359:0,0,0,0,0,0,0;1/1:5360:0,0,0,0,0,0,0;-1/1:5363:-1,0,0,0,1,0,0;1/1:5384:-2,0,0,0,0,0,0;1/1:5392:-2,0,0,0,0,0,0;1/1:5413:0,0,0,0,0,0,0;-1/1:5415:0,0,0,0,0,0,0;1/1:5426:0,0,0,0,0,0,0;1/1:5428:-2,0,0,0,0,0,0;1/1:5429:0,0,0,0,0,0,0;1/1:5435:0,0,0,0,0,0,0;-1/1:5438:-1,0,0,0,1,0,0;-1/1:5440:-1,0,0,0,1,0,0;1/1:5447:-1,-1,0,0,1,1,0;-1/1:5458:0,0,0,0,0,0,0;1/1:5465:0,0,0,0,0,0,0;-1/1:5466:-1,0,0,0,1,0,0;1/1:5470:-2,0,0,0,0,0,0;-1/1:5479:0,0,0,0,0,0,0;1/1:5491:0,-1,0,0,0,1,0;-1/1:5492:-2,0,0,0,0,0,0;1/1:5493:0,-1,0,0,0,1,0;-1/1:5494:0,0,0,0,0,0,0;-1/1:5505:0,0,0,0,0,0,0;-1/1:5513:0,0,0,0,0,0,0;1/1:5526:-2,0,0,0,0,0,0;1/1:5535:0,0,0,0,0,0,0;1/1:5545:0,0,0,0,0,0,0;1/1:5548:0,0,0,0,0,0,0;-1/1:5550:0,-1,0,0,0,1,0"
  | 4 => laurent_polynomial% "1/1:3367:0,0,0,0,0,0,0;-1/1:5116:-2,0,0,0,0,0,0;1/1:5384:-1,0,0,0,1,0,0;-1/1:5421:-1,0,0,0,1,0,0;-1/1:5438:0,0,0,0,0,0,0;1/1:5487:0,0,0,0,0,0,0;-1/1:5500:-1,0,0,0,1,0,0;1/1:5541:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "-1/1:3339:0,0,0,0,0,0,0;1/1:5174:-2,0,0,0,0,0,0;-1/1:5376:-1,0,0,0,1,0,0;1/1:5423:0,0,0,0,0,0,0;-1/1:5461:0,0,0,0,0,0,0;1/1:5474:0,-2,0,0,0,0,0;1/1:5475:-1,0,0,0,1,0,0;1/1:5529:0,0,0,0,0,0,0;-1/1:5531:-1,0,0,0,1,0,0;1/1:5548:-2,0,0,0,0,0,0;-1/1:5550:-2,-1,0,0,0,1,0"
  | 6 => laurent_polynomial% "1/1:3589:0,0,0,0,0,0,0;-1/1:5181:0,0,0,0,0,0,0;1/1:5359:-1,0,0,0,1,0,0;-1/1:5363:-2,0,0,0,0,0,0;1/1:5447:-2,-1,0,0,0,1,0;1/1:5491:-1,-1,0,0,1,1,0;1/1:5500:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:2954:0,0,0,0,0,0,0;-1/1:4601:-2,-2,0,-2,0,0,0;-1/1:4615:-2,-2,0,-2,0,0,0;-1/1:4617:-2,-2,0,-2,0,0,0;-1/1:4622:-2,-2,0,-2,0,0,0;-1/1:4623:-2,-2,0,-2,0,0,0;-1/1:4647:-2,-2,0,-2,0,0,0;-1/1:4652:-2,-2,0,-2,0,0,0;-1/1:4656:0,0,0,0,0,0,0;-1/1:4674:-2,-2,0,-2,0,0,0;-1/1:4677:0,0,0,0,0,0,0;-1/1:4683:-2,-2,0,-2,0,0,0;-1/1:4696:-2,-2,0,-2,0,0,0;-1/1:4697:-2,-2,0,-2,0,0,0;-1/1:4706:-2,-2,0,-2,0,0,0;-1/1:4720:-2,-2,0,-2,0,0,0;-1/1:4722:0,0,0,0,0,0,0;-1/1:4726:-2,-2,0,-2,0,0,0;-1/1:4745:-2,-2,0,-2,0,0,0;-1/1:4783:-2,-2,0,-2,0,0,0;-1/1:4786:0,0,0,0,0,0,0;-1/1:4801:-2,-2,0,-2,0,0,0;-1/1:4804:-2,-2,0,-2,0,0,0;-1/1:4817:0,0,0,0,0,0,0;-1/1:4860:-2,-2,0,-2,0,0,0;-1/1:4865:-2,-2,0,-2,0,0,0;-1/1:4869:0,0,0,0,0,0,0;-1/1:4929:0,0,0,0,0,0,0;-1/1:5021:0,0,0,0,0,0,0;-1/1:5033:0,0,0,0,0,0,0;-1/1:5087:0,0,0,0,0,0,0;-1/1:5126:0,0,0,0,0,0,0;-1/1:5183:0,0,0,0,0,0,0;-1/1:5193:0,0,0,0,0,0,0;-1/1:5252:0,0,0,0,0,0,0;-1/1:5348:0,0,0,0,0,0,0;-1/1:5365:-1,0,0,0,1,0,0;-1/1:5370:0,0,0,0,0,0,0;-1/1:5377:-1,0,0,0,1,0,0;1/1:5379:0,0,0,0,0,0,0;1/1:5380:0,0,0,0,0,0,0;1/1:5391:-1,0,0,0,1,0,0;-1/1:5395:-1,-1,0,0,1,1,0;1/1:5410:0,0,0,0,0,0,0;1/1:5431:-2,0,0,0,0,0,0;1/1:5446:-1,-1,0,0,1,1,0;1/1:5447:-2,-2,0,0,0,0,0;1/1:5447:0,0,0,0,0,0,0;-1/1:5448:0,-2,0,0,0,0,0;1/1:5453:0,0,0,0,0,0,0;1/1:5474:0,-1,0,0,0,1,0;-1/1:5478:0,0,0,0,0,0,0;-1/1:5482:0,0,0,0,0,0,0;-1/1:5489:0,0,0,0,0,0,0;1/1:5491:-1,-2,0,0,1,0,0;-1/1:5498:-2,0,0,0,0,0,0;-1/1:5508:0,0,0,0,0,0,0;1/1:5512:-2,0,0,0,0,0,0;-1/1:5517:-1,0,0,0,1,0,0;1/1:5524:-1,0,0,0,1,0,0;-1/1:5532:0,0,0,0,0,0,0;-1/1:5544:-1,0,0,0,1,0,0;1/1:5546:0,0,0,0,0,0,0;1/1:5547:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:3529:0,0,0,0,0,0,0;-1/1:5229:-2,0,0,0,0,0,0;-1/1:5239:0,0,0,0,0,0,0;1/1:5366:-2,0,0,0,0,0,0;1/1:5378:-1,0,0,0,1,0,0;1/1:5457:0,0,0,0,0,0,0;1/1:5471:-2,0,0,0,0,0,0;-1/1:5521:-2,0,0,0,0,0,0;1/1:5528:-2,0,0,0,0,0,0;1/1:5538:-2,-2,0,0,0,0,0;-1/1:5544:-2,0,0,0,0,0,0;-1/1:5552:-2,0,0,0,0,0,0;-1/1:5561:-2,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "-1/1:3133:0,0,0,0,0,0,0;1/1:4602:2,0,0,-2,0,0,0;1/1:4612:0,0,0,0,0,0,0;1/1:4613:2,0,0,-2,0,0,0;1/1:4632:2,0,0,-2,0,0,0;1/1:4646:2,0,0,-2,0,0,0;1/1:4650:0,0,0,0,0,0,0;1/1:4665:0,0,0,0,0,0,0;1/1:4667:2,0,0,-2,0,0,0;1/1:4668:0,0,0,0,0,0,0;1/1:4671:0,0,0,0,0,0,0;1/1:4673:2,0,0,-2,0,0,0;1/1:4682:2,0,0,-2,0,0,0;1/1:4691:2,0,0,-2,0,0,0;1/1:4699:0,0,0,0,0,0,0;1/1:4705:2,0,0,-2,0,0,0;1/1:4719:2,0,0,-2,0,0,0;1/1:4733:2,0,0,-2,0,0,0;1/1:4736:2,0,0,-2,0,0,0;1/1:4738:2,0,0,-2,0,0,0;1/1:4739:2,0,0,-2,0,0,0;1/1:4760:2,0,0,-2,0,0,0;1/1:4769:2,0,0,-2,0,0,0;1/1:4778:2,0,0,-2,0,0,0;1/1:4793:0,0,0,0,0,0,0;1/1:4803:2,0,0,-2,0,0,0;1/1:4809:2,0,0,-2,0,0,0;1/1:4820:2,0,0,-2,0,0,0;1/1:4822:0,0,0,0,0,0,0;1/1:4828:0,0,0,0,0,0,0;1/1:4831:2,0,0,-2,0,0,0;1/1:4834:2,0,0,-2,0,0,0;1/1:4836:2,0,0,-2,0,0,0;1/1:4837:2,0,0,-2,0,0,0;1/1:4852:2,0,0,-2,0,0,0;1/1:4854:2,0,0,-2,0,0,0;1/1:4868:2,0,0,-2,0,0,0;1/1:4874:2,0,0,-2,0,0,0;1/1:4877:2,0,0,-2,0,0,0;1/1:4880:2,0,0,-2,0,0,0;1/1:4883:0,0,0,0,0,0,0;1/1:4884:0,0,0,0,0,0,0;1/1:4889:0,0,0,0,0,0,0;1/1:4890:2,0,0,-2,0,0,0;1/1:4891:0,0,0,0,0,0,0;1/1:4915:0,0,0,0,0,0,0;1/1:4918:2,0,0,-2,0,0,0;1/1:4923:2,0,0,-2,0,0,0;1/1:4930:2,0,0,-2,0,0,0;1/1:4941:2,0,0,-2,0,0,0;1/1:4942:2,0,0,-2,0,0,0;1/1:4944:2,0,0,-2,0,0,0;1/1:4945:2,0,0,-2,0,0,0;1/1:4948:2,0,0,-2,0,0,0;1/1:4949:2,0,0,-2,0,0,0;1/1:4990:0,0,0,0,0,0,0;1/1:5064:0,0,0,0,0,0,0;1/1:5074:0,0,0,0,0,0,0;-1/1:5090:0,-1,0,0,0,1,0;1/1:5095:0,0,0,0,0,0,0;1/1:5118:0,0,0,0,0,0,0;1/1:5209:0,0,0,0,0,0,0;1/1:5245:0,0,0,0,0,0,0;1/1:5364:0,0,0,0,0,0,0;1/1:5384:0,0,0,0,0,0,0;1/1:5392:0,0,0,0,0,0,0;1/1:5428:0,0,0,0,0,0,0;1/1:5470:0,0,0,0,0,0,0;-1/1:5492:0,0,0,0,0,0,0;1/1:5502:0,0,0,0,0,0,0;1/1:5526:0,0,0,0,0,0,0;-1/1:5535:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:3289:0,0,0,0,0,0,0;-1/1:5204:-2,0,0,0,0,0,0;1/1:5367:-1,0,0,0,1,0,0;-1/1:5398:0,0,0,0,0,0,0;1/1:5443:0,0,0,0,0,0,0;1/1:5519:0,0,0,0,0,0,0;-1/1:5534:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:3406:0,0,0,0,0,0,0;-1/1:5179:0,0,0,0,0,0,0;1/1:5218:0,0,0,0,0,0,0;1/1:5358:-1,0,0,0,1,0,0;1/1:5447:-1,-2,0,0,1,0,0;-1/1:5448:0,0,0,0,0,0,0;-1/1:5459:-2,0,0,0,0,0,0;1/1:5491:0,-2,0,0,0,0,0;-1/1:5492:-2,-1,0,0,0,1,0;1/1:5553:-2,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "-1/1:4308:0,0,0,0,0,0,0;-1/1:4670:0,0,0,-1,0,0,1;1/1:4796:0,0,0,0,0,0,0;1/1:4927:0,0,0,0,0,0,0;1/1:4938:0,0,0,-2,0,0,0;1/1:5116:0,0,0,0,0,0,0;1/1:5220:0,0,0,0,0,0,0;-1/1:5365:0,0,0,0,0,0,0;1/1:5391:0,0,0,0,0,0,0;-1/1:5395:0,-1,0,0,0,1,0;1/1:5397:0,0,0,0,0,0,0;1/1:5424:0,0,0,0,0,0,0;-1/1:5493:0,0,0,0,0,0,0;1/1:5524:0,0,0,0,0,0,0;1/1:5531:0,0,0,0,0,0,0;-1/1:5542:0,0,0,0,0,0,0;-1/1:5562:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:2751:2,0,0,0,0,0,0;1/1:4601:0,-2,-2,0,0,0,0;1/1:4748:0,-2,-2,0,0,0,0;1/1:4780:0,-2,-2,0,0,0,0;1/1:4781:0,-2,-2,0,0,0,0;1/1:4867:0,-2,-2,0,0,0,0;1/1:4873:0,-2,-2,0,0,0,0;1/1:4920:2,0,0,0,0,0,0;1/1:5256:2,0,0,0,0,0,0;1/1:5270:2,0,0,0,0,0,0;1/1:5289:2,0,0,0,0,0,0;1/1:5343:2,0,0,0,0,0,0;-1/1:5382:2,0,0,0,0,0,0;-1/1:5384:0,0,0,0,0,0,0;1/1:5421:0,0,0,0,0,0,0;1/1:5422:1,0,0,0,1,0,0;1/1:5438:1,0,0,0,1,0,0;-1/1:5468:0,0,0,0,0,0,0;-1/1:5487:1,0,0,0,1,0,0;1/1:5490:2,0,0,0,0,0,0;1/1:5500:0,0,0,0,0,0,0;-1/1:5511:2,0,0,0,0,0,0;1/1:5516:2,0,0,0,0,0,0;-1/1:5541:1,0,0,0,1,0,0;-1/1:5543:1,0,0,0,1,0,0;1/1:5547:0,0,0,0,0,0,0;1/1:5554:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:3148:0,0,0,0,0,0,0;-1/1:4621:0,0,0,0,0,0,0;-1/1:4626:0,0,0,0,0,0,0;-1/1:4628:0,0,0,0,0,0,0;-1/1:4647:-2,0,-2,0,0,0,0;-1/1:4648:-2,0,-2,0,0,0,0;-1/1:4649:-2,0,-2,0,0,0,0;-1/1:4651:-2,0,-2,0,0,0,0;-1/1:4652:-2,0,-2,0,0,0,0;-1/1:4653:-2,0,-2,0,0,0,0;-1/1:4661:-2,0,-2,0,0,0,0;-1/1:4663:-2,0,-2,0,0,0,0;-1/1:4678:0,0,0,0,0,0,0;-1/1:4695:0,0,0,0,0,0,0;-1/1:4744:0,0,0,0,0,0,0;-1/1:4758:0,0,0,0,0,0,0;-1/1:4765:0,0,0,0,0,0,0;-1/1:4777:0,0,0,0,0,0,0;-1/1:4786:0,0,0,0,0,0,0;-1/1:4801:-2,0,-2,0,0,0,0;-1/1:4802:-2,0,-2,0,0,0,0;-1/1:4804:-2,0,-2,0,0,0,0;-1/1:4807:-2,0,-2,0,0,0,0;-1/1:4812:-2,0,-2,0,0,0,0;-1/1:4814:-2,0,-2,0,0,0,0;-1/1:4816:-2,0,-2,0,0,0,0;-1/1:4821:-2,0,-2,0,0,0,0;-1/1:4822:-2,0,-2,0,0,0,0;-1/1:4824:-2,0,-2,0,0,0,0;-1/1:4826:-2,0,-2,0,0,0,0;-1/1:4828:-2,0,-2,0,0,0,0;-1/1:4832:-2,0,-2,0,0,0,0;-1/1:4835:-2,0,-2,0,0,0,0;-1/1:4840:-2,0,-2,0,0,0,0;-1/1:4843:-2,0,-2,0,0,0,0;-1/1:4844:-2,0,-2,0,0,0,0;-1/1:4847:-2,0,-2,0,0,0,0;-1/1:4871:-2,0,-2,0,0,0,0;-1/1:4881:-2,0,-2,0,0,0,0;-1/1:4882:-2,0,-2,0,0,0,0;-1/1:4883:-2,0,-2,0,0,0,0;-1/1:4884:-2,0,-2,0,0,0,0;-1/1:4885:-2,0,-2,0,0,0,0;-1/1:4901:0,0,0,0,0,0,0;-1/1:4906:0,0,0,0,0,0,0;-1/1:4908:0,0,0,0,0,0,0;-1/1:4924:0,0,0,0,0,0,0;-1/1:4925:0,0,0,0,0,0,0;-1/1:4932:-2,0,-2,0,0,0,0;-1/1:4980:-2,0,-2,0,0,0,0;-1/1:4983:-2,0,-2,0,0,0,0;-1/1:4993:-2,0,-2,0,0,0,0;-1/1:4998:0,0,0,0,0,0,0;-1/1:5007:0,0,0,0,0,0,0;-1/1:5028:0,0,0,0,0,0,0;-1/1:5043:0,0,0,0,0,0,0;-1/1:5062:-2,0,-2,0,0,0,0;-1/1:5065:-2,0,-2,0,0,0,0;-1/1:5078:-2,0,-2,0,0,0,0;-1/1:5090:-2,-2,-2,0,0,0,0;-1/1:5096:-2,0,-2,0,0,0,0;-1/1:5097:-2,0,-2,0,0,0,0;-1/1:5100:-2,0,-2,0,0,0,0;-1/1:5127:0,0,0,0,0,0,0;-1/1:5135:0,0,0,0,0,0,0;-1/1:5152:0,0,0,0,0,0,0;-1/1:5160:0,0,0,0,0,0,0;-1/1:5164:0,0,0,0,0,0,0;-1/1:5183:0,0,0,0,0,0,0;-1/1:5193:0,0,0,0,0,0,0;-1/1:5242:-1,0,0,0,1,0,0;1/1:5245:0,0,0,0,0,0,0;-1/1:5252:0,0,0,0,0,0,0;-1/1:5257:0,0,0,0,0,0,0;-1/1:5260:0,0,0,0,0,0,0;-1/1:5262:0,0,0,0,0,0,0;-1/1:5269:0,0,0,0,0,0,0;-1/1:5290:0,0,0,0,0,0,0;-1/1:5304:0,0,0,0,0,0,0;-1/1:5306:0,0,0,0,0,0,0;-1/1:5310:0,0,0,0,0,0,0;-1/1:5317:0,0,0,0,0,0,0;-1/1:5322:0,0,0,0,0,0,0;-1/1:5330:0,0,0,0,0,0,0;1/1:5357:-2,0,0,0,0,0,0;-1/1:5365:-1,0,0,0,1,0,0;-1/1:5371:-1,0,0,0,1,0,0;1/1:5382:-2,0,0,0,0,0,0;1/1:5384:0,0,0,0,0,0,0;-1/1:5389:0,0,0,0,0,0,0;1/1:5391:-1,0,0,0,1,0,0;-1/1:5395:-1,-1,0,0,1,1,0;1/1:5410:0,0,0,0,0,0,0;-1/1:5412:0,0,0,0,0,0,0;-1/1:5424:-1,0,0,0,1,0,0;1/1:5425:-2,0,0,0,0,0,0;1/1:5429:-2,0,0,0,0,0,0;1/1:5431:-2,0,0,0,0,0,0;-1/1:5448:0,-2,0,0,0,0,0;-1/1:5449:0,0,0,0,0,0,0;-1/1:5456:0,0,0,0,0,0,0;1/1:5462:-2,0,0,0,0,0,0;-1/1:5467:-1,0,0,0,1,0,0;-1/1:5473:-2,0,0,0,0,0,0;-1/1:5476:-1,0,0,0,1,0,0;1/1:5483:0,0,0,0,0,0,0;-1/1:5488:-1,0,0,0,1,0,0;1/1:5491:0,0,0,0,0,0,0;1/1:5493:-1,0,0,0,1,0,0;-1/1:5496:0,0,0,0,0,0,0;-1/1:5498:-2,0,0,0,0,0,0;-1/1:5500:0,0,0,0,0,0,0;1/1:5503:0,0,0,0,0,0,0;1/1:5504:-2,-2,0,0,0,0,0;-1/1:5506:0,0,0,0,0,0,0;1/1:5524:-1,0,0,0,1,0,0;-1/1:5531:-1,0,0,0,1,0,0;1/1:5548:-2,0,0,0,0,0,0;-1/1:5550:-2,-1,0,0,0,1,0;1/1:5553:0,0,0,0,0,0,0;-1/1:5565:0,0,0,0,0,0,0;1/1:5573:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:3318:0,0,0,0,0,0,0;1/1:5229:-1,0,0,0,1,0,0;-1/1:5360:-2,0,0,0,0,0,0;-1/1:5366:-1,0,0,0,1,0,0;-1/1:5378:0,0,0,0,0,0,0;-1/1:5446:-2,0,0,0,0,0,0;-1/1:5471:-1,0,0,0,1,0,0;1/1:5521:-1,0,0,0,1,0,0;-1/1:5528:-1,0,0,0,1,0,0;-1/1:5538:-1,-2,0,0,1,0,0;1/1:5544:-1,0,0,0,1,0,0;1/1:5552:-1,0,0,0,1,0,0;1/1:5561:-1,0,0,0,1,0,0"
  | 16 => laurent_polynomial% "1/1:3427:0,0,0,0,0,0,0;-1/1:5226:0,0,0,0,0,0,0;1/1:5361:0,0,0,0,0,0,0;1/1:5441:0,0,0,0,0,0,0;1/1:5464:-1,0,0,0,1,0,0;-1/1:5487:0,0,0,0,0,0,0;-1/1:5503:-1,0,0,0,1,0,0;1/1:5504:-1,0,0,0,1,0,0;-1/1:5532:0,0,0,0,0,0,0;1/1:5549:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:3206:0,0,0,0,0,0,0;-1/1:4601:-2,0,0,0,0,0,0;-1/1:4602:0,0,0,0,0,0,0;-1/1:4603:-2,0,0,0,0,0,0;-1/1:4606:0,0,0,0,0,0,0;-1/1:4607:-2,0,0,0,0,0,0;-1/1:4610:-2,0,0,0,0,0,0;-1/1:4614:-2,0,0,0,0,0,0;-1/1:4615:-2,0,0,0,0,0,0;-1/1:4616:-2,0,0,0,0,0,0;-1/1:4617:-2,0,0,0,0,0,0;-1/1:4620:0,0,0,0,0,0,0;-1/1:4621:0,0,0,0,0,0,0;-1/1:4622:-2,0,0,0,0,0,0;-1/1:4623:-2,0,0,0,0,0,0;-1/1:4624:0,0,0,0,0,0,0;-1/1:4626:0,0,0,0,0,0,0;-1/1:4628:0,0,0,0,0,0,0;-1/1:4629:0,0,0,0,0,0,0;-1/1:4631:-2,0,0,0,0,0,0;-1/1:4632:0,0,0,0,0,0,0;-1/1:4636:-2,0,0,0,0,0,0;-1/1:4639:-2,0,0,0,0,0,0;-1/1:4640:0,0,0,0,0,0,0;-1/1:4641:-2,0,0,0,0,0,0;-1/1:4643:0,0,0,0,0,0,0;-1/1:4644:-2,0,0,0,0,0,0;-1/1:4645:0,0,0,0,0,0,0;-1/1:4646:0,0,0,0,0,0,0;-1/1:4647:-2,0,0,0,0,0,0;-1/1:4649:-2,0,0,0,0,0,0;-1/1:4651:-2,0,0,0,0,0,0;-1/1:4652:-2,0,0,0,0,0,0;-1/1:4653:-2,0,0,0,0,0,0;-1/1:4655:-2,0,0,0,0,0,0;-1/1:4657:-2,0,0,0,0,0,0;-1/1:4658:0,0,0,0,0,0,0;-1/1:4659:0,0,0,0,0,0,0;-1/1:4661:-2,0,0,0,0,0,0;-1/1:4667:0,0,0,0,0,0,0;-1/1:4669:0,0,0,0,0,0,0;-1/1:4673:0,0,0,0,0,0,0;-1/1:4674:-2,0,0,0,0,0,0;-1/1:4675:-2,0,0,0,0,0,0;-1/1:4681:-2,0,0,0,0,0,0;-1/1:4682:0,0,0,0,0,0,0;-1/1:4683:-2,0,0,0,0,0,0;-1/1:4684:0,0,0,0,0,0,0;-1/1:4687:0,0,0,0,0,0,0;-1/1:4690:-2,0,0,0,0,0,0;-1/1:4691:0,0,0,0,0,0,0;-1/1:4692:-2,0,0,0,0,0,0;-1/1:4694:0,0,0,0,0,0,0;-1/1:4695:0,0,0,0,0,0,0;-1/1:4696:-2,0,0,0,0,0,0;-1/1:4697:-2,0,0,0,0,0,0;-1/1:4698:-2,0,0,0,0,0,0;-1/1:4700:-2,0,0,0,0,0,0;-1/1:4702:-2,0,0,0,0,0,0;-1/1:4703:-2,0,0,0,0,0,0;-1/1:4705:0,0,0,0,0,0,0;-1/1:4706:-2,0,0,0,0,0,0;-1/1:4708:0,0,0,0,0,0,0;-1/1:4716:-2,0,0,0,0,0,0;-1/1:4717:-2,0,0,0,0,0,0;-1/1:4719:0,0,0,0,0,0,0;-1/1:4720:-2,0,0,0,0,0,0;-1/1:4721:-2,0,0,0,0,0,0;-1/1:4726:-2,0,0,0,0,0,0;-1/1:4727:-2,0,0,0,0,0,0;-1/1:4728:0,0,0,0,0,0,0;-1/1:4729:-2,0,0,0,0,0,0;-1/1:4730:-2,0,0,0,0,0,0;-1/1:4731:0,0,0,0,0,0,0;-1/1:4732:-2,0,0,0,0,0,0;-1/1:4734:-2,0,0,0,0,0,0;-1/1:4737:-2,0,0,0,0,0,0;-1/1:4738:0,0,0,0,0,0,0;-1/1:4739:0,0,0,0,0,0,0;-1/1:4740:0,0,0,0,0,0,0;-1/1:4741:-2,0,0,0,0,0,0;-1/1:4743:-2,0,0,0,0,0,0;-1/1:4745:-2,0,0,0,0,0,0;-1/1:4746:-2,0,0,0,0,0,0;-1/1:4747:-2,0,0,0,0,0,0;-1/1:4748:-2,0,0,0,0,0,0;-1/1:4752:-2,0,0,0,0,0,0;-1/1:4759:-2,0,0,0,0,0,0;-1/1:4760:0,0,0,0,0,0,0;-1/1:4761:-2,0,0,0,0,0,0;-1/1:4764:-2,0,0,0,0,0,0;-1/1:4765:0,0,0,0,0,0,0;-1/1:4767:0,0,0,0,0,0,0;-1/1:4769:0,0,0,0,0,0,0;-1/1:4770:-2,0,0,0,0,0,0;-1/1:4771:-2,0,0,0,0,0,0;-1/1:4774:-2,0,0,0,0,0,0;-1/1:4776:-2,0,0,0,0,0,0;-1/1:4778:0,0,0,0,0,0,0;-1/1:4779:-2,0,0,0,0,0,0;-1/1:4780:-2,0,0,0,0,0,0;-1/1:4781:-2,0,0,0,0,0,0;-1/1:4783:-2,0,0,0,0,0,0;-1/1:4784:0,0,0,0,0,0,0;-1/1:4785:-2,0,0,0,0,0,0;-1/1:4787:-2,0,0,0,0,0,0;-1/1:4791:0,0,0,0,0,0,0;-1/1:4792:0,0,0,0,0,0,0;-1/1:4797:0,0,0,0,0,0,0;-1/1:4798:-2,0,0,0,0,0,0;-1/1:4799:-2,0,0,0,0,0,0;-1/1:4800:0,0,0,0,0,0,0;-1/1:4801:-2,0,0,0,0,0,0;-1/1:4803:0,0,0,0,0,0,0;-1/1:4804:-2,0,0,0,0,0,0;-1/1:4805:0,0,0,0,0,0,0;-1/1:4806:0,0,0,0,0,0,0;-1/1:4808:-2,0,0,0,0,0,0;-1/1:4809:0,0,0,0,0,0,0;-1/1:4810:-2,0,0,0,0,0,0;-1/1:4811:0,0,0,0,0,0,0;-1/1:4813:-2,0,0,0,0,0,0;-1/1:4814:-2,0,0,0,0,0,0;-1/1:4815:-2,0,0,0,0,0,0;-1/1:4820:0,0,0,0,0,0,0;-1/1:4825:0,0,0,0,0,0,0;-1/1:4826:-2,0,0,0,0,0,0;-1/1:4827:-2,0,0,0,0,0,0;-1/1:4829:0,0,0,0,0,0,0;-1/1:4830:-2,0,0,0,0,0,0;-1/1:4831:0,0,0,0,0,0,0;-1/1:4832:-2,0,0,0,0,0,0;-1/1:4833:0,0,0,0,0,0,0;-1/1:4834:0,0,0,0,0,0,0;-1/1:4835:-2,0,0,0,0,0,0;-1/1:4836:0,0,0,0,0,0,0;-1/1:4837:0,0,0,0,0,0,0;-1/1:4838:-2,0,0,0,0,0,0;-1/1:4840:-2,0,0,0,0,0,0;-1/1:4843:-2,0,0,0,0,0,0;-1/1:4844:-2,0,0,0,0,0,0;-1/1:4845:-2,0,0,0,0,0,0;-1/1:4846:-2,0,0,0,0,0,0;-1/1:4847:-2,0,0,0,0,0,0;-1/1:4848:0,0,0,0,0,0,0;-1/1:4849:-2,0,0,0,0,0,0;-1/1:4850:0,0,0,0,0,0,0;-1/1:4855:-2,0,0,0,0,0,0;-1/1:4856:-2,0,0,0,0,0,0;-1/1:4857:0,0,0,0,0,0,0;-1/1:4858:-2,0,0,0,0,0,0;-1/1:4860:-2,0,0,0,0,0,0;-1/1:4862:0,0,0,0,0,0,0;-1/1:4863:0,0,0,0,0,0,0;-1/1:4864:-2,0,0,0,0,0,0;-1/1:4865:-2,0,0,0,0,0,0;-1/1:4867:-2,0,0,0,0,0,0;-1/1:4871:-2,0,0,0,0,0,0;-1/1:4872:-2,0,0,0,0,0,0;-1/1:4873:-2,0,0,0,0,0,0;-1/1:4874:0,0,0,0,0,0,0;-1/1:4876:-2,0,0,0,0,0,0;-1/1:4877:0,0,0,0,0,0,0;-1/1:4880:0,0,0,0,0,0,0;-1/1:4881:-2,0,0,0,0,0,0;-1/1:4886:-2,0,0,0,0,0,0;-1/1:4887:0,0,0,0,0,0,0;-1/1:4892:-2,0,0,0,0,0,0;-1/1:4893:0,0,0,0,0,0,0;-1/1:4902:0,0,0,0,0,0,0;-1/1:4903:0,0,0,0,0,0,0;-1/1:4904:0,0,0,0,0,0,0;-1/1:4906:0,0,0,0,0,0,0;-1/1:4908:0,0,0,0,0,0,0;-1/1:4909:-2,0,0,0,0,0,0;-1/1:4910:-2,0,0,0,0,0,0;-1/1:4916:0,0,0,0,0,0,0;-1/1:4917:0,0,0,0,0,0,0;-1/1:4921:0,0,0,0,0,0,0;-1/1:4922:0,0,0,0,0,0,0;-1/1:4923:0,0,0,0,0,0,0;-1/1:4928:0,0,0,0,0,0,0;-1/1:4930:0,0,0,0,0,0,0;-1/1:4934:-2,0,0,0,0,0,0;-1/1:4935:-2,0,0,0,0,0,0;-1/1:4941:0,0,0,0,0,0,0;-1/1:4942:0,0,0,0,0,0,0;-1/1:4944:0,0,0,0,0,0,0;-1/1:4945:0,0,0,0,0,0,0;-1/1:4946:-2,0,0,0,0,0,0;-1/1:4952:0,0,0,0,0,0,0;-1/1:4955:-2,0,0,0,0,0,0;-1/1:4957:-2,0,0,0,0,0,0;-1/1:4958:0,0,0,0,0,0,0;-1/1:4959:-2,0,0,0,0,0,0;-1/1:4960:-2,0,0,0,0,0,0;-1/1:4962:-2,0,0,0,0,0,0;-1/1:4963:0,0,0,0,0,0,0;-1/1:4966:0,0,0,0,0,0,0;-1/1:4967:0,0,0,0,0,0,0;-1/1:4968:0,0,0,0,0,0,0;-1/1:4970:0,0,0,0,0,0,0;-1/1:4971:-2,0,0,0,0,0,0;-1/1:4974:-2,0,0,0,0,0,0;-1/1:4979:0,0,0,0,0,0,0;-1/1:4981:-2,0,0,0,0,0,0;-1/1:4982:-2,0,0,0,0,0,0;-1/1:4983:-2,0,0,0,0,0,0;-1/1:4984:0,0,0,0,0,0,0;-1/1:4985:0,0,0,0,0,0,0;-1/1:4986:0,0,0,0,0,0,0;-1/1:4987:0,0,0,0,0,0,0;-1/1:4989:-2,0,0,0,0,0,0;-1/1:4991:-2,0,0,0,0,0,0;-1/1:4992:-2,0,0,0,0,0,0;-1/1:4994:-2,0,0,0,0,0,0;-1/1:4996:-2,0,0,0,0,0,0;-1/1:4999:0,0,0,0,0,0,0;-1/1:5003:-2,0,0,0,0,0,0;-1/1:5004:0,0,0,0,0,0,0;-1/1:5005:0,0,0,0,0,0,0;-1/1:5006:-2,0,0,0,0,0,0;-1/1:5007:0,0,0,0,0,0,0;-1/1:5012:0,0,0,0,0,0,0;-1/1:5014:0,0,0,0,0,0,0;-1/1:5017:0,0,0,0,0,0,0;-1/1:5019:0,0,0,0,0,0,0;-1/1:5022:0,0,0,0,0,0,0;-1/1:5023:0,0,0,0,0,0,0;-1/1:5027:0,0,0,0,0,0,0;-1/1:5028:0,0,0,0,0,0,0;-1/1:5032:0,0,0,0,0,0,0;-1/1:5035:0,0,0,0,0,0,0;-1/1:5036:0,0,0,0,0,0,0;-1/1:5038:0,0,0,0,0,0,0;-1/1:5042:0,0,0,0,0,0,0;-1/1:5043:0,0,0,0,0,0,0;-1/1:5049:-2,0,0,0,0,0,0;-1/1:5050:0,0,0,0,0,0,0;-1/1:5051:0,0,0,0,0,0,0;-1/1:5054:-2,0,0,0,0,0,0;-1/1:5055:0,0,0,0,0,0,0;-1/1:5056:0,0,0,0,0,0,0;-1/1:5058:-2,0,0,0,0,0,0;-1/1:5059:0,0,0,0,0,0,0;1/1:5062:-2,0,0,0,0,0,0;-1/1:5066:-2,0,0,0,0,0,0;-1/1:5070:-2,0,0,0,0,0,0;-1/1:5072:0,0,0,0,0,0,0;-1/1:5085:0,0,0,0,0,0,0;-1/1:5086:-2,0,0,0,0,0,0;-1/1:5088:0,0,0,0,0,0,0;-1/1:5089:-2,0,0,0,0,0,0;1/1:5090:-2,0,0,0,0,0,0;-1/1:5093:0,0,0,0,0,0,0;1/1:5096:0,0,0,0,0,0,0;1/1:5097:-2,0,0,0,0,0,0;-1/1:5098:-2,0,0,0,0,0,0;-1/1:5099:-2,0,0,0,0,0,0;1/1:5101:-2,0,0,0,0,0,0;-1/1:5103:-2,0,0,0,0,0,0;-1/1:5105:-2,0,0,0,0,0,0;-1/1:5106:-2,0,0,0,0,0,0;-1/1:5107:0,0,0,0,0,0,0;-1/1:5110:0,0,0,0,0,0,0;-1/1:5111:0,0,0,0,0,0,0;-1/1:5113:0,0,0,0,0,0,0;-1/1:5122:0,0,0,0,0,0,0;-1/1:5123:0,0,0,0,0,0,0;-1/1:5124:0,0,0,0,0,0,0;-1/1:5125:0,0,0,0,0,0,0;-1/1:5127:0,0,0,0,0,0,0;-1/1:5132:0,0,0,0,0,0,0;-1/1:5133:0,0,0,0,0,0,0;-1/1:5135:0,0,0,0,0,0,0;-1/1:5136:0,0,0,0,0,0,0;-1/1:5138:0,0,0,0,0,0,0;-1/1:5139:0,0,0,0,0,0,0;-1/1:5141:0,0,0,0,0,0,0;-1/1:5144:0,0,0,0,0,0,0;-1/1:5147:0,0,0,0,0,0,0;-1/1:5148:0,0,0,0,0,0,0;-1/1:5150:0,0,0,0,0,0,0;-1/1:5153:0,0,0,0,0,0,0;-1/1:5155:0,0,0,0,0,0,0;-1/1:5156:0,0,0,0,0,0,0;-1/1:5157:0,0,0,0,0,0,0;-1/1:5158:0,0,0,0,0,0,0;-1/1:5159:0,0,0,0,0,0,0;-1/1:5160:0,0,0,0,0,0,0;-1/1:5162:0,0,0,0,0,0,0;-1/1:5163:-2,0,0,0,0,0,0;-1/1:5165:-2,0,0,0,0,0,0;-1/1:5166:0,0,0,0,0,0,0;-1/1:5168:0,0,0,0,0,0,0;-1/1:5169:0,0,0,0,0,0,0;-1/1:5170:0,0,0,0,0,0,0;-1/1:5182:0,0,0,0,0,0,0;-1/1:5188:0,0,0,0,0,0,0;-1/1:5190:-2,0,0,0,0,0,0;1/1:5192:-2,0,0,0,0,0,0;-1/1:5195:0,0,0,0,0,0,0;-1/1:5197:-2,0,0,0,0,0,0;1/1:5198:-4,0,0,0,0,0,0;1/1:5198:-3,0,0,0,1,0,0;-1/1:5198:-1,0,0,0,1,0,0;-1/1:5199:-2,0,0,0,0,0,0;-1/1:5201:0,0,0,0,0,0,0;-1/1:5205:-2,0,0,0,0,0,0;-1/1:5210:0,0,0,0,0,0,0;-1/1:5211:-2,0,0,0,0,0,0;-1/1:5213:0,0,0,0,0,0,0;-1/1:5215:-2,0,0,0,0,0,0;1/1:5215:0,0,0,0,0,0,0;-1/1:5216:-1,0,0,0,1,0,0;-1/1:5217:-2,0,0,0,0,0,0;1/1:5217:0,0,0,0,0,0,0;-1/1:5219:-2,0,0,0,0,0,0;-1/1:5221:-2,0,0,0,0,0,0;-1/1:5221:-1,0,0,0,1,0,0;1/1:5221:0,0,0,0,0,0,0;-1/1:5222:-2,0,0,0,0,0,0;-1/1:5223:-2,0,0,0,0,0,0;-1/1:5225:0,0,0,0,0,0,0;-1/1:5227:-2,0,0,0,0,0,0;-1/1:5228:-2,0,0,0,0,0,0;-1/1:5231:-2,0,0,0,0,0,0;1/1:5232:0,0,0,0,0,0,0;-1/1:5233:0,0,0,0,0,0,0;-1/1:5235:-2,0,0,0,0,0,0;-1/1:5241:0,0,0,0,0,0,0;-1/1:5242:-2,0,0,0,0,0,0;-1/1:5242:-1,0,0,0,1,0,0;1/1:5242:0,0,0,0,0,0,0;-1/1:5243:-2,0,0,0,0,0,0;-1/1:5244:-1,0,0,0,1,0,0;1/1:5245:0,0,0,0,0,0,0;-1/1:5249:0,0,0,0,0,0,0;-1/1:5251:0,0,0,0,0,0,0;-1/1:5254:0,0,0,0,0,0,0;-1/1:5259:0,0,0,0,0,0,0;-1/1:5264:0,0,0,0,0,0,0;-1/1:5265:0,0,0,0,0,0,0;-1/1:5268:0,0,0,0,0,0,0;-1/1:5269:0,0,0,0,0,0,0;1/1:5274:0,0,0,0,0,0,0;-1/1:5276:0,0,0,0,0,0,0;-1/1:5278:0,0,0,0,0,0,0;1/1:5279:0,0,0,0,0,0,0;-1/1:5280:0,0,0,0,0,0,0;-1/1:5282:0,0,0,0,0,0,0;-1/1:5295:0,0,0,0,0,0,0;-1/1:5297:0,0,0,0,0,0,0;-1/1:5300:0,0,0,0,0,0,0;-1/1:5301:0,0,0,0,0,0,0;-1/1:5303:0,0,0,0,0,0,0;-1/1:5309:0,0,0,0,0,0,0;-1/1:5314:0,0,0,0,0,0,0;-1/1:5316:0,0,0,0,0,0,0;1/1:5317:0,0,0,0,0,0,0;-1/1:5319:0,0,0,0,0,0,0;-1/1:5320:0,0,0,0,0,0,0;-1/1:5322:0,0,0,0,0,0,0;-1/1:5325:0,0,0,0,0,0,0;-1/1:5336:0,0,0,0,0,0,0;-1/1:5346:0,0,0,0,0,0,0;-1/1:5349:0,0,0,0,0,0,0;-1/1:5351:0,0,0,0,0,0,0;-1/1:5353:0,0,0,0,0,0,0;-1/1:5355:0,0,0,0,0,0,0;-1/1:5356:0,0,0,0,0,0,0;-1/1:5358:-2,0,0,0,0,0,0;-1/1:5359:-2,0,0,0,0,0,0;-1/1:5360:-2,0,0,0,0,0,0;1/1:5361:0,0,0,0,0,0,0;1/1:5365:-2,0,0,0,0,0,0;1/1:5365:0,0,0,0,0,0,0;-1/1:5367:-2,0,0,0,0,0,0;-1/1:5368:-2,0,0,0,0,0,0;-1/1:5369:0,0,0,0,0,0,0;1/1:5371:-2,0,0,0,0,0,0;-1/1:5372:-2,0,0,0,0,0,0;1/1:5375:0,0,0,0,0,0,0;1/1:5376:-2,0,0,0,0,0,0;1/1:5376:0,0,0,0,0,0,0;1/1:5377:0,0,0,0,0,0,0;-1/1:5379:-2,0,0,0,0,0,0;-1/1:5379:-1,0,0,0,1,0,0;-1/1:5380:-2,0,0,0,0,0,0;1/1:5381:0,0,0,0,0,0,0;-1/1:5383:-2,0,0,0,0,0,0;-1/1:5383:-1,0,0,0,1,0,0;-1/1:5385:0,0,0,0,0,0,0;1/1:5386:-2,0,0,0,0,0,0;1/1:5386:0,0,0,0,0,0,0;-1/1:5388:-1,0,0,0,1,0,0;-1/1:5389:0,0,0,0,0,0,0;-1/1:5391:-2,0,0,0,0,0,0;2/1:5392:-2,0,0,0,0,0,0;1/1:5395:-2,-1,0,0,0,1,0;-1/1:5395:-1,0,0,0,1,0,0;1/1:5395:0,-1,0,0,0,1,0;1/1:5395:0,0,0,0,0,0,0;-1/1:5396:-2,0,0,0,0,0,0;1/1:5397:0,0,0,0,0,0,0;-1/1:5399:-1,0,0,0,1,0,0;-1/1:5401:-2,0,0,0,0,0,0;1/1:5415:0,0,0,0,0,0,0;1/1:5420:-2,0,0,0,0,0,0;-1/1:5421:-1,0,0,0,1,0,0;-1/1:5423:-2,0,0,0,0,0,0;-1/1:5423:-1,0,0,0,1,0,0;-1/1:5426:-2,0,0,0,0,0,0;-1/1:5429:-1,0,0,0,1,0,0;1/1:5430:0,0,0,0,0,0,0;-1/1:5431:-1,0,0,0,1,0,0;-1/1:5432:-2,0,0,0,0,0,0;-1/1:5435:-2,0,0,0,0,0,0;1/1:5436:-2,0,0,0,0,0,0;1/1:5436:0,0,0,0,0,0,0;1/1:5438:-2,0,0,0,0,0,0;-1/1:5439:-2,0,0,0,0,0,0;1/1:5440:0,0,0,0,0,0,0;1/1:5443:0,0,0,0,0,0,0;-1/1:5444:0,0,0,0,0,0,0;-1/1:5445:0,0,0,0,0,0,0;1/1:5446:-2,-2,0,0,0,0,0;-1/1:5446:-2,0,0,0,0,0,0;1/1:5446:0,-2,0,0,0,0,0;-1/1:5446:0,-1,0,0,0,1,0;-1/1:5447:-2,-2,0,0,0,0,0;-1/1:5447:0,-2,0,0,0,0,0;1/1:5448:-2,0,0,0,0,0,0;-1/1:5449:0,0,0,0,0,0,0;-1/1:5450:-1,0,0,0,1,0,0;-1/1:5452:0,0,0,0,0,0,0;1/1:5461:-2,0,0,0,0,0,0;1/1:5461:-1,0,0,0,1,0,0;-1/1:5462:-1,0,0,0,1,0,0;-1/1:5465:-1,0,0,0,1,0,0;1/1:5467:-2,0,0,0,0,0,0;-1/1:5468:-2,0,0,0,0,0,0;1/1:5469:-2,0,0,0,0,0,0;-1/1:5470:-1,0,0,0,1,0,0;-1/1:5472:-2,-1,0,0,0,1,0;-1/1:5472:-1,0,0,0,1,0,0;1/1:5472:0,0,0,0,0,0,0;-1/1:5474:-2,-1,0,0,0,1,0;1/1:5474:-2,0,0,0,0,0,0;-1/1:5475:-2,0,0,0,0,0,0;-1/1:5475:0,0,0,0,0,0,0;2/1:5476:-2,0,0,0,0,0,0;1/1:5476:0,0,0,0,0,0,0;1/1:5479:0,-2,0,0,0,0,0;-1/1:5481:0,0,0,0,0,0,0;1/1:5485:0,-2,0,0,0,0,0;-1/1:5486:0,0,0,0,0,0,0;1/1:5487:0,0,0,0,0,0,0;1/1:5488:0,0,0,0,0,0,0;1/1:5489:-2,0,0,0,0,0,0;1/1:5489:-1,0,0,0,1,0,0;-1/1:5491:-2,-2,0,0,0,0,0;-1/1:5491:-2,-1,0,0,0,1,0;-1/1:5492:-2,0,0,0,0,0,0;1/1:5492:0,0,0,0,0,0,0;-1/1:5493:-2,0,0,0,0,0,0;-1/1:5493:-1,-1,0,0,1,1,0;-1/1:5494:0,0,0,0,0,0,0;-1/1:5497:0,0,0,0,0,0,0;1/1:5498:-1,0,0,0,1,0,0;-1/1:5499:0,0,0,0,0,0,0;-1/1:5500:-1,0,0,0,1,0,0;1/1:5501:-2,0,0,0,0,0,0;-1/1:5503:-1,0,0,0,1,0,0;-1/1:5504:-1,-2,0,0,1,0,0;1/1:5504:-1,0,0,0,1,0,0;-1/1:5512:-2,0,0,0,0,0,0;-1/1:5512:0,0,0,0,0,0,0;1/1:5517:0,0,0,0,0,0,0;-1/1:5518:0,0,0,0,0,0,0;1/1:5519:0,0,0,0,0,0,0;-1/1:5522:0,0,0,0,0,0,0;-1/1:5523:0,0,0,0,0,0,0;-2/1:5524:-2,0,0,0,0,0,0;-1/1:5524:0,0,0,0,0,0,0;1/1:5531:-2,0,0,0,0,0,0;1/1:5531:0,0,0,0,0,0,0;1/1:5532:-2,0,0,0,0,0,0;-1/1:5534:0,0,0,0,0,0,0;-1/1:5535:-2,0,0,0,0,0,0;-1/1:5537:-2,0,0,0,0,0,0;-1/1:5538:0,0,0,0,0,0,0;-1/1:5540:0,0,0,0,0,0,0;1/1:5541:0,0,0,0,0,0,0;1/1:5544:-2,0,0,0,0,0,0;-1/1:5545:-2,0,0,0,0,0,0;-1/1:5545:-1,0,0,0,1,0,0;-1/1:5548:-1,0,0,0,1,0,0;1/1:5549:-2,0,0,0,0,0,0;1/1:5549:0,0,0,0,0,0,0;1/1:5550:-1,-1,0,0,1,1,0;-1/1:5550:0,0,0,0,0,0,0;-1/1:5556:0,0,0,0,0,0,0;-1/1:5558:0,0,0,0,0,0,0;-1/1:5564:0,0,0,0,0,0,0;-1/1:5566:0,0,0,0,0,0,0;1/1:5567:-2,0,0,0,0,0,0;-1/1:5570:0,0,0,0,0,0,0;-1/1:5576:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:3321:0,0,0,0,0,0,0;1/1:5226:-1,0,0,0,1,0,0;-1/1:5238:0,0,0,0,0,0,0;1/1:5318:0,0,0,0,0,0,0;-1/1:5361:-1,0,0,0,1,0,0;1/1:5425:0,0,0,0,0,0,0;-1/1:5441:-1,0,0,0,1,0,0;1/1:5450:0,0,0,0,0,0,0;-1/1:5464:-2,0,0,0,0,0,0;-1/1:5473:0,0,0,0,0,0,0;1/1:5487:-1,0,0,0,1,0,0;1/1:5503:-2,0,0,0,0,0,0;-1/1:5504:-2,0,0,0,0,0,0;1/1:5504:0,-2,0,0,0,0,0;1/1:5532:-1,0,0,0,1,0,0;-1/1:5549:-1,0,0,0,1,0,0"
  | 19 => laurent_polynomial% "1/1:3147:0,0,0,0,0,0,0;-1/1:4613:0,0,0,0,0,0,0;-1/1:4637:0,0,0,0,0,0,0;-1/1:4638:0,0,0,0,0,0,0;-1/1:4647:-2,0,-2,0,0,0,0;-1/1:4649:-2,0,-2,0,0,0,0;-1/1:4650:-2,0,-2,0,0,0,0;-1/1:4651:-2,0,-2,0,0,0,0;-1/1:4652:-2,0,-2,0,0,0,0;-1/1:4653:-2,0,-2,0,0,0,0;-1/1:4655:-2,0,-2,0,0,0,0;-1/1:4661:-2,0,-2,0,0,0,0;-1/1:4680:0,0,0,0,0,0,0;-1/1:4712:0,0,0,0,0,0,0;-1/1:4736:0,0,0,0,0,0,0;-1/1:4749:0,0,0,0,0,0,0;-1/1:4799:-2,0,-2,0,0,0,0;-1/1:4801:-2,0,-2,0,0,0,0;-1/1:4804:-2,0,-2,0,0,0,0;-1/1:4808:-2,0,-2,0,0,0,0;-1/1:4810:-2,0,-2,0,0,0,0;-1/1:4813:-2,0,-2,0,0,0,0;-1/1:4815:-2,0,-2,0,0,0,0;-1/1:4822:-2,0,-2,0,0,0,0;-1/1:4826:-2,0,-2,0,0,0,0;-1/1:4827:-2,0,-2,0,0,0,0;-1/1:4828:-2,0,-2,0,0,0,0;-1/1:4830:-2,0,-2,0,0,0,0;-1/1:4832:-2,0,-2,0,0,0,0;-1/1:4835:-2,0,-2,0,0,0,0;-1/1:4838:-2,0,-2,0,0,0,0;-1/1:4843:-2,0,-2,0,0,0,0;-1/1:4844:-2,0,-2,0,0,0,0;-1/1:4845:-2,0,-2,0,0,0,0;-1/1:4847:-2,0,-2,0,0,0,0;-1/1:4852:0,0,0,0,0,0,0;-1/1:4854:0,0,0,0,0,0,0;-1/1:4871:-2,0,-2,0,0,0,0;-1/1:4872:-2,0,-2,0,0,0,0;-1/1:4881:-2,0,-2,0,0,0,0;-1/1:4883:-2,0,-2,0,0,0,0;-1/1:4884:-2,0,-2,0,0,0,0;-1/1:4888:0,0,0,0,0,0,0;-1/1:4890:0,0,0,0,0,0,0;-1/1:4892:-2,0,-2,0,0,0,0;-1/1:4918:0,0,0,0,0,0,0;-1/1:4936:0,0,0,0,0,0,0;-1/1:4948:0,0,0,0,0,0,0;-1/1:4949:0,0,0,0,0,0,0;-1/1:4981:-2,0,-2,0,0,0,0;-1/1:4982:-2,0,-2,0,0,0,0;-1/1:4992:-2,0,-2,0,0,0,0;-1/1:5009:0,0,0,0,0,0,0;-1/1:5025:0,0,0,0,0,0,0;-1/1:5044:0,0,0,0,0,0,0;-1/1:5053:0,0,0,0,0,0,0;-1/1:5064:-2,0,-2,0,0,0,0;-1/1:5066:-2,0,-2,0,0,0,0;-1/1:5070:-2,0,-2,0,0,0,0;-1/1:5082:0,0,0,0,0,0,0;1/1:5090:-2,-1,-2,0,0,1,0;1/1:5090:-2,0,-2,0,0,0,0;-1/1:5095:-2,0,-2,0,0,0,0;-1/1:5098:-2,0,-2,0,0,0,0;-1/1:5099:-2,0,-2,0,0,0,0;-1/1:5117:0,0,0,0,0,0,0;-1/1:5121:0,0,0,0,0,0,0;-1/1:5129:0,0,0,0,0,0,0;-1/1:5154:0,0,0,0,0,0,0;-1/1:5206:0,0,0,0,0,0,0;-1/1:5243:-1,0,0,0,1,0,0;-1/1:5271:0,0,0,0,0,0,0;1/1:5273:0,0,0,0,0,0,0;-1/1:5285:0,0,0,0,0,0,0;-1/1:5287:0,0,0,0,0,0,0;-1/1:5291:0,0,0,0,0,0,0;-1/1:5307:0,0,0,0,0,0,0;-1/1:5323:0,0,0,0,0,0,0;-1/1:5332:0,0,0,0,0,0,0;-1/1:5339:0,0,0,0,0,0,0;-1/1:5341:0,0,0,0,0,0,0;-1/1:5347:0,0,0,0,0,0,0;1/1:5363:0,0,0,0,0,0,0;1/1:5366:0,0,0,0,0,0,0;-1/1:5368:-1,0,0,0,1,0,0;1/1:5374:0,0,0,0,0,0,0;1/1:5395:-2,0,0,0,0,0,0;-1/1:5409:0,0,0,0,0,0,0;-1/1:5411:0,0,0,0,0,0,0;-1/1:5413:0,0,0,0,0,0,0;-1/1:5414:0,0,0,0,0,0,0;-1/1:5416:0,0,0,0,0,0,0;-1/1:5417:0,0,0,0,0,0,0;-1/1:5426:-1,0,0,0,1,0,0;1/1:5427:-2,0,0,0,0,0,0;-1/1:5428:-1,0,0,0,1,0,0;-1/1:5433:-1,0,0,0,1,0,0;1/1:5434:-2,0,0,0,0,0,0;1/1:5437:0,0,0,0,0,0,0;1/1:5440:-2,0,0,0,0,0,0;1/1:5448:0,0,0,0,0,0,0;-1/1:5455:0,0,0,0,0,0,0;-1/1:5461:-2,0,0,0,0,0,0;-1/1:5462:0,0,0,0,0,0,0;1/1:5466:0,0,0,0,0,0,0;1/1:5474:-2,-2,0,0,0,0,0;1/1:5474:0,0,0,0,0,0,0;-1/1:5500:-2,0,0,0,0,0,0;-1/1:5502:-1,0,0,0,1,0,0;-1/1:5505:0,0,0,0,0,0,0;1/1:5509:-2,0,0,0,0,0,0;-1/1:5510:0,0,0,0,0,0,0;-1/1:5512:-1,0,0,0,1,0,0;1/1:5517:-2,0,0,0,0,0,0;-1/1:5526:-1,0,0,0,1,0,0;-1/1:5527:0,0,0,0,0,0,0;1/1:5528:0,0,0,0,0,0,0;1/1:5532:-1,0,0,0,1,0,0;1/1:5538:0,-2,0,0,0,0,0;1/1:5543:-1,0,0,0,1,0,0;1/1:5551:-2,0,0,0,0,0,0;-1/1:5552:0,0,0,0,0,0,0;1/1:5553:-2,0,0,0,0,0,0;-1/1:5554:-2,0,0,0,0,0,0;-1/1:5561:0,0,0,0,0,0,0;1/1:5567:-1,0,0,0,1,0,0;1/1:5569:-1,0,0,0,1,0,0;-1/1:5571:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:3173:0,0,0,0,0,0,0;-1/1:4600:-2,-2,0,0,0,0,0;-1/1:4601:-2,-2,0,0,0,0,0;-1/1:4609:0,0,0,0,0,0,0;-1/1:4610:-2,-2,0,0,0,0,0;-1/1:4612:-2,-2,0,0,0,0,0;-1/1:4615:-2,-2,0,0,0,0,0;-1/1:4619:-2,-2,0,0,0,0,0;-1/1:4622:-2,-2,0,0,0,0,0;-1/1:4631:-2,-2,0,0,0,0,0;-1/1:4636:-2,-2,0,0,0,0,0;-1/1:4647:-2,-2,0,0,0,0,0;-1/1:4649:-2,-2,0,0,0,0,0;-1/1:4652:-2,-2,0,0,0,0,0;-1/1:4653:-2,-2,0,0,0,0,0;-1/1:4660:0,0,0,0,0,0,0;-1/1:4664:0,0,0,0,0,0,0;-1/1:4665:-2,-2,0,0,0,0,0;-1/1:4666:-2,-2,0,0,0,0,0;-1/1:4674:-2,-2,0,0,0,0,0;-1/1:4676:0,0,0,0,0,0,0;-1/1:4683:-2,-2,0,0,0,0,0;-1/1:4686:-2,-2,0,0,0,0,0;-1/1:4690:-2,-2,0,0,0,0,0;-1/1:4697:-2,-2,0,0,0,0,0;-1/1:4699:-2,-2,0,0,0,0,0;-1/1:4703:-2,-2,0,0,0,0,0;-1/1:4704:-2,-2,0,0,0,0,0;-1/1:4706:-2,-2,0,0,0,0,0;-1/1:4709:-2,-2,0,0,0,0,0;-1/1:4714:-2,-2,0,0,0,0,0;-1/1:4715:0,0,0,0,0,0,0;-1/1:4718:-2,-2,0,0,0,0,0;-1/1:4720:-2,-2,0,0,0,0,0;-1/1:4725:0,0,0,0,0,0,0;-1/1:4726:-2,-2,0,0,0,0,0;-1/1:4730:-2,-2,0,0,0,0,0;-1/1:4732:-2,-2,0,0,0,0,0;-1/1:4735:-2,-2,0,0,0,0,0;-1/1:4737:-2,-2,0,0,0,0,0;-1/1:4741:-2,-2,0,0,0,0,0;-1/1:4744:0,0,0,0,0,0,0;-1/1:4745:-2,-2,0,0,0,0,0;-1/1:4748:-2,-2,0,0,0,0,0;-1/1:4755:-2,-2,0,0,0,0,0;-1/1:4756:-2,-2,0,0,0,0,0;-1/1:4757:0,0,0,0,0,0,0;-1/1:4758:0,0,0,0,0,0,0;-1/1:4761:-2,-2,0,0,0,0,0;-1/1:4772:0,0,0,0,0,0,0;-1/1:4775:0,0,0,0,0,0,0;-1/1:4777:0,0,0,0,0,0,0;-1/1:4781:-2,-2,0,0,0,0,0;-1/1:4783:-2,-2,0,0,0,0,0;-1/1:4787:-2,-2,0,0,0,0,0;-1/1:4795:0,0,0,0,0,0,0;-1/1:4801:-2,-2,0,0,0,0,0;-1/1:4804:-2,-2,0,0,0,0,0;-1/1:4808:-2,-2,0,0,0,0,0;-1/1:4814:-2,-2,0,0,0,0,0;-1/1:4818:0,0,0,0,0,0,0;-1/1:4819:0,0,0,0,0,0,0;-1/1:4822:-2,-2,0,0,0,0,0;-1/1:4823:0,0,0,0,0,0,0;-1/1:4826:-2,-2,0,0,0,0,0;-1/1:4828:-2,-2,0,0,0,0,0;-1/1:4832:-2,-2,0,0,0,0,0;-1/1:4835:-2,-2,0,0,0,0,0;-1/1:4838:-2,-2,0,0,0,0,0;-1/1:4840:-2,-2,0,0,0,0,0;-1/1:4841:0,0,0,0,0,0,0;-1/1:4842:0,0,0,0,0,0,0;-1/1:4847:-2,-2,0,0,0,0,0;-1/1:4859:0,0,0,0,0,0,0;-1/1:4866:0,0,0,0,0,0,0;-1/1:4867:-2,-2,0,0,0,0,0;-1/1:4871:-2,-2,0,0,0,0,0;-1/1:4873:-2,-2,0,0,0,0,0;-1/1:4879:-2,-2,0,0,0,0,0;-1/1:4881:-2,-2,0,0,0,0,0;-1/1:4883:-2,-2,0,0,0,0,0;-1/1:4884:-2,-2,0,0,0,0,0;-1/1:4889:-2,-2,0,0,0,0,0;-1/1:4900:0,0,0,0,0,0,0;-1/1:4901:0,0,0,0,0,0,0;-1/1:4905:0,0,0,0,0,0,0;-1/1:4907:-2,-2,0,0,0,0,0;-1/1:4909:-2,-2,0,0,0,0,0;-1/1:4911:0,0,0,0,0,0,0;-1/1:4915:-2,-2,0,0,0,0,0;-1/1:4924:0,0,0,0,0,0,0;-1/1:4925:0,0,0,0,0,0,0;-1/1:4933:0,0,0,0,0,0,0;-1/1:4934:-2,-2,0,0,0,0,0;-1/1:4937:0,0,0,0,0,0,0;-1/1:4946:-2,-2,0,0,0,0,0;-1/1:4953:0,0,0,0,0,0,0;-1/1:4954:0,0,0,0,0,0,0;-1/1:4956:0,0,0,0,0,0,0;-1/1:4964:0,0,0,0,0,0,0;-1/1:4965:0,0,0,0,0,0,0;-1/1:4969:0,0,0,0,0,0,0;-1/1:4971:-2,-2,0,0,0,0,0;-1/1:4973:0,0,0,0,0,0,0;-1/1:4982:-2,-2,0,0,0,0,0;-1/1:4983:-2,-2,0,0,0,0,0;-1/1:4990:-2,-2,0,0,0,0,0;-1/1:4991:-2,-2,0,0,0,0,0;-1/1:4998:0,0,0,0,0,0,0;-1/1:5001:0,0,0,0,0,0,0;-1/1:5016:0,0,0,0,0,0,0;-1/1:5026:0,0,0,0,0,0,0;-1/1:5029:0,0,0,0,0,0,0;-1/1:5031:0,0,0,0,0,0,0;-1/1:5039:0,0,0,0,0,0,0;-1/1:5052:0,0,0,0,0,0,0;1/1:5066:0,0,0,0,0,0,0;-1/1:5068:0,0,0,0,0,0,0;1/1:5070:-2,0,0,0,0,0,0;-1/1:5073:0,0,0,0,0,0,0;-1/1:5076:0,0,0,0,0,0,0;-1/1:5086:-2,-2,0,0,0,0,0;-1/1:5090:-2,0,0,0,0,0,0;-1/1:5092:0,0,0,0,0,0,0;-1/1:5094:0,0,0,0,0,0,0;1/1:5095:0,0,0,0,0,0,0;1/1:5098:-2,0,0,0,0,0,0;-1/1:5104:-2,-2,0,0,0,0,0;-1/1:5105:-2,-2,0,0,0,0,0;-1/1:5106:-2,-2,0,0,0,0,0;-1/1:5115:0,0,0,0,0,0,0;-1/1:5118:-2,-2,0,0,0,0,0;-1/1:5119:0,0,0,0,0,0,0;-1/1:5128:0,0,0,0,0,0,0;-1/1:5143:0,0,0,0,0,0,0;-1/1:5149:0,0,0,0,0,0,0;-1/1:5152:0,0,0,0,0,0,0;1/1:5161:-2,-2,0,0,0,0,0;-1/1:5163:-2,-2,0,0,0,0,0;-1/1:5164:0,0,0,0,0,0,0;-1/1:5171:0,0,0,0,0,0,0;-1/1:5173:0,0,0,0,0,0,0;-1/1:5175:0,0,0,0,0,0,0;-1/1:5189:0,0,0,0,0,0,0;1/1:5191:-3,0,0,0,1,0,0;-1/1:5191:-1,0,0,0,1,0,0;-1/1:5200:0,0,0,0,0,0,0;-1/1:5212:0,0,0,0,0,0,0;-1/1:5215:-2,-2,0,0,0,0,0;-1/1:5216:-2,-2,0,0,0,0,0;-1/1:5217:-2,-2,0,0,0,0,0;-1/1:5218:-2,-2,0,0,0,0,0;-1/1:5222:-2,-2,0,0,0,0,0;-1/1:5223:-2,-2,0,0,0,0,0;-1/1:5232:0,0,0,0,0,0,0;1/1:5233:0,0,0,0,0,0,0;-1/1:5234:-2,-2,0,0,0,0,0;-1/1:5240:0,0,0,0,0,0,0;-1/1:5243:-2,-2,0,0,0,0,0;-1/1:5244:-2,-2,0,0,0,0,0;-1/1:5247:0,0,0,0,0,0,0;-1/1:5248:0,0,0,0,0,0,0;-1/1:5253:0,0,0,0,0,0,0;-1/1:5257:0,0,0,0,0,0,0;-1/1:5260:0,0,0,0,0,0,0;-1/1:5261:0,0,0,0,0,0,0;-1/1:5262:0,0,0,0,0,0,0;-1/1:5266:0,0,0,0,0,0,0;-1/1:5267:0,0,0,0,0,0,0;-1/1:5274:0,0,0,0,0,0,0;1/1:5276:0,0,0,0,0,0,0;1/1:5278:0,0,0,0,0,0,0;-1/1:5279:0,0,0,0,0,0,0;-1/1:5281:0,0,0,0,0,0,0;-1/1:5284:0,0,0,0,0,0,0;-1/1:5288:0,0,0,0,0,0,0;-1/1:5290:0,0,0,0,0,0,0;-1/1:5293:0,0,0,0,0,0,0;-1/1:5294:0,0,0,0,0,0,0;-1/1:5296:0,0,0,0,0,0,0;-1/1:5304:0,0,0,0,0,0,0;-1/1:5305:0,0,0,0,0,0,0;-1/1:5308:0,0,0,0,0,0,0;-1/1:5310:0,0,0,0,0,0,0;-1/1:5312:0,0,0,0,0,0,0;-1/1:5317:0,0,0,0,0,0,0;-1/1:5321:0,0,0,0,0,0,0;-1/1:5324:0,0,0,0,0,0,0;-1/1:5327:0,0,0,0,0,0,0;-1/1:5328:0,0,0,0,0,0,0;-1/1:5330:0,0,0,0,0,0,0;-1/1:5331:0,0,0,0,0,0,0;-1/1:5333:0,0,0,0,0,0,0;-1/1:5337:0,0,0,0,0,0,0;-1/1:5344:0,0,0,0,0,0,0;-1/1:5345:0,0,0,0,0,0,0;-1/1:5352:0,0,0,0,0,0,0;-1/1:5354:0,0,0,0,0,0,0;1/1:5357:-2,0,0,0,0,0,0;1/1:5358:0,0,0,0,0,0,0;1/1:5359:0,0,0,0,0,0,0;1/1:5360:0,0,0,0,0,0,0;-1/1:5363:-1,0,0,0,1,0,0;1/1:5364:0,0,0,0,0,0,0;-1/1:5366:-1,0,0,0,1,0,0;1/1:5367:-2,0,0,0,0,0,0;1/1:5368:-2,0,0,0,0,0,0;-1/1:5371:-1,0,0,0,1,0,0;1/1:5372:-2,0,0,0,0,0,0;1/1:5379:-2,0,0,0,0,0,0;1/1:5382:-2,0,0,0,0,0,0;1/1:5383:0,0,0,0,0,0,0;1/1:5384:0,0,0,0,0,0,0;1/1:5396:0,0,0,0,0,0,0;-1/1:5397:-1,0,0,0,1,0,0;-1/1:5398:-1,0,0,0,1,0,0;1/1:5399:-2,0,0,0,0,0,0;1/1:5401:0,0,0,0,0,0,0;-1/1:5403:0,0,0,0,0,0,0;-1/1:5404:0,0,0,0,0,0,0;-1/1:5415:0,0,0,0,0,0,0;-1/1:5418:0,0,0,0,0,0,0;-1/1:5424:-1,0,0,0,1,0,0;1/1:5425:-2,0,0,0,0,0,0;1/1:5426:0,0,0,0,0,0,0;-1/1:5427:-1,0,0,0,1,0,0;1/1:5428:-2,0,0,0,0,0,0;1/1:5428:0,0,0,0,0,0,0;1/1:5429:-2,0,0,0,0,0,0;1/1:5432:-2,0,0,0,0,0,0;1/1:5432:0,0,0,0,0,0,0;1/1:5433:0,0,0,0,0,0,0;1/1:5435:-2,0,0,0,0,0,0;1/1:5435:0,0,0,0,0,0,0;-1/1:5437:-1,0,0,0,1,0,0;-1/1:5440:-1,0,0,0,1,0,0;1/1:5446:0,0,0,0,0,0,0;1/1:5447:-1,-1,0,0,1,1,0;1/1:5447:0,-2,0,0,0,0,0;1/1:5450:-2,0,0,0,0,0,0;-1/1:5458:0,0,0,0,0,0,0;-1/1:5459:-1,0,0,0,1,0,0;1/1:5460:-2,0,0,0,0,0,0;1/1:5460:0,0,0,0,0,0,0;1/1:5462:-2,0,0,0,0,0,0;1/1:5464:0,0,0,0,0,0,0;-1/1:5466:-1,0,0,0,1,0,0;-1/1:5467:-1,0,0,0,1,0,0;-1/1:5469:-1,0,0,0,1,0,0;1/1:5470:-2,0,0,0,0,0,0;1/1:5470:0,0,0,0,0,0,0;-1/1:5471:-1,0,0,0,1,0,0;1/1:5472:-2,-1,0,0,0,1,0;1/1:5472:0,-1,0,0,0,1,0;-1/1:5473:-2,0,0,0,0,0,0;-1/1:5476:-1,0,0,0,1,0,0;-1/1:5480:0,0,0,0,0,0,0;-1/1:5488:-1,0,0,0,1,0,0;-1/1:5489:-2,0,0,0,0,0,0;1/1:5491:-2,-1,0,0,0,1,0;1/1:5491:0,-1,0,0,0,1,0;-1/1:5492:-2,-2,0,0,0,0,0;-1/1:5492:-2,0,0,0,0,0,0;-1/1:5492:-1,-1,0,0,1,1,0;-1/1:5492:0,0,0,0,0,0,0;-1/1:5493:-2,-2,0,0,0,0,0;1/1:5493:-1,0,0,0,1,0,0;-1/1:5495:0,0,0,0,0,0,0;-1/1:5496:0,0,0,0,0,0,0;1/1:5500:-1,0,0,0,1,0,0;1/1:5502:0,0,0,0,0,0,0;1/1:5504:-2,-2,0,0,0,0,0;1/1:5504:0,0,0,0,0,0,0;-1/1:5507:0,0,0,0,0,0,0;-1/1:5509:-1,0,0,0,1,0,0;1/1:5512:0,0,0,0,0,0,0;1/1:5521:-1,0,0,0,1,0,0;1/1:5524:-2,0,0,0,0,0,0;1/1:5524:0,0,0,0,0,0,0;-1/1:5525:0,0,0,0,0,0,0;1/1:5526:-2,0,0,0,0,0,0;1/1:5526:0,0,0,0,0,0,0;-1/1:5529:0,0,0,0,0,0,0;-1/1:5532:-2,0,0,0,0,0,0;-1/1:5533:0,0,0,0,0,0,0;-1/1:5534:-1,0,0,0,1,0,0;1/1:5535:-2,0,0,0,0,0,0;1/1:5537:-2,0,0,0,0,0,0;1/1:5537:0,0,0,0,0,0,0;-1/1:5539:0,0,0,0,0,0,0;1/1:5542:0,0,0,0,0,0,0;1/1:5544:-1,0,0,0,1,0,0;1/1:5545:-2,0,0,0,0,0,0;1/1:5545:0,0,0,0,0,0,0;-1/1:5551:-1,0,0,0,1,0,0;1/1:5552:-1,0,0,0,1,0,0;1/1:5554:-1,0,0,0,1,0,0;1/1:5556:0,-2,0,0,0,0,0;1/1:5561:-1,0,0,0,1,0,0;-1/1:5562:-2,0,0,0,0,0,0;-1/1:5563:0,0,0,0,0,0,0;-1/1:5567:-2,0,0,0,0,0,0;-1/1:5569:0,0,0,0,0,0,0;-1/1:5574:0,0,0,0,0,0,0;-1/1:5575:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:3319:0,0,0,0,0,0,0;1/1:5227:-1,0,0,0,1,0,0;-1/1:5378:-1,0,0,0,1,0,0;-1/1:5457:0,0,0,0,0,0,0;-1/1:5460:-1,0,0,0,1,0,0;1/1:5509:0,0,0,0,0,0,0;-1/1:5528:-2,0,0,0,0,0,0;1/1:5534:0,0,0,0,0,0,0;-1/1:5538:-2,-2,0,0,0,0,0;-1/1:5554:0,0,0,0,0,0,0;1/1:5561:-2,0,0,0,0,0,0;1/1:5562:-1,0,0,0,1,0,0"
  | _ => []

end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentTritailTablesBundleV4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate def triTailPart0 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => []
  | 21 => []
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | 26 => []
  | 27 => []
  | 28 => []
  | 29 => []
  | 30 => []
  | 31 => []
  | _ => []
compact_certificate def triTailPart1 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => []
  | 21 => []
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | 26 => []
  | 27 => []
  | 28 => []
  | 29 => []
  | 30 => []
  | 31 => []
  | _ => []
compact_certificate def triTailPart2 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => []
  | 21 => []
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | 26 => []
  | 27 => []
  | 28 => []
  | 29 => []
  | 30 => []
  | 31 => []
  | _ => []
compact_certificate def triTailPart3 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => []
  | 21 => []
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | 26 => []
  | 27 => []
  | 28 => []
  | 29 => []
  | 30 => []
  | 31 => []
  | _ => []

compact_certificate def triTailPart4 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => []
  | 21 => []
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | 26 => []
  | 27 => []
  | 28 => []
  | 29 => []
  | 30 => []
  | 31 => []
  | _ => []
compact_certificate def triTailPart5 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => []
  | 21 => []
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | 26 => []
  | 27 => []
  | 28 => []
  | 29 => []
  | 30 => []
  | 31 => []
  | _ => []
compact_certificate def triTailPart6 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => []
  | 21 => []
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | 26 => []
  | 27 => []
  | 28 => []
  | 29 => []
  | 30 => []
  | 31 => []
  | _ => []
compact_certificate def triTailPart7 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => []
  | 21 => []
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | 26 => []
  | 27 => []
  | 28 => []
  | 29 => []
  | 30 => []
  | 31 => []
  | _ => []

compact_certificate def triTailPart8 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => []
  | 21 => []
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | 26 => []
  | 27 => []
  | 28 => []
  | 29 => []
  | 30 => []
  | 31 => []
  | _ => []
compact_certificate def triTailPart9 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => []
  | 21 => []
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | 26 => []
  | 27 => []
  | 28 => []
  | 29 => []
  | 30 => []
  | 31 => []
  | _ => []
compact_certificate def triTailPart10 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => []
  | 21 => []
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | 26 => []
  | 27 => []
  | 28 => []
  | 29 => []
  | 30 => []
  | 31 => []
  | _ => []
compact_certificate def triTailPart11 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => laurent_polynomial% "1/1:351:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:699:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:702:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:348:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:354:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:696:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:855:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:405:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:860:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:820:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:660:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:810:0,0,0,0,0,0,0"
  | _ => []

compact_certificate def triTailPart12 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:885:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:585:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:915:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:765:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:876:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:174:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:738:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:732:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:760:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:920:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:670:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:590:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:52:-2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:64:-2,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:76:-2,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:92:-2,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:144:-2,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:160:-2,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:164:-2,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:172:-2,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "-1/1:876:-2,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:192:-2,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:576:2,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:216:-2,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "-1/1:660:-2,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:264:-2,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "-1/1:732:-2,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "-1/1:660:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "-1/1:264:-1,0,0,0,1,0,0"
  | 29 => laurent_polynomial% "-1/1:660:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:740:-2,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "-1/1:810:-1,0,0,0,1,0,0"
  | _ => []
compact_certificate def triTailPart13 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:220:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:768:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:246:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:774:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:776:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:778:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:782:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:258:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:260:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:786:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:262:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:788:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:264:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:790:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:792:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:268:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:272:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:274:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:276:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:804:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:282:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "-1/1:810:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:830:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:310:-2,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "-1/1:810:-2,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:786:-1,0,0,0,1,0,0"
  | 26 => laurent_polynomial% "1/1:738:-2,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:786:-2,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:834:-2,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:474:2,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:858:-2,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "-1/1:174:-2,0,0,0,0,0,0"
  | _ => []
compact_certificate def triTailPart14 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:878:-2,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:886:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:890:-2,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:906:-2,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:958:-2,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:974:-2,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "-1/1:1016:1,0,0,0,1,0,0"
  | 7 => laurent_polynomial% "1/1:986:-2,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:703:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:706:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:708:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:709:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:712:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:730:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:810:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:410:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:660:0,-1,0,0,0,1,0"
  | 17 => laurent_polynomial% "-1/1:660:0,-2,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:810:0,-2,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:470:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:845:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:354:0,-2,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:660:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:172:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:873:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:177:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:878:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:696:0,-2,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:905:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "-1/1:580:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "-1/1:810:0,-1,0,0,0,1,0"
  | 31 => laurent_polynomial% "-1/1:640:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def triTailPart15 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:320:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:688:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:691:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:342:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:694:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:697:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:708:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:715:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:755:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:342:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:810:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:810:-2,-1,0,0,0,1,0;-1/1:810:-1,0,0,0,1,0,0"
  | 12 => laurent_polynomial% "1/1:810:-2,-1,0,0,0,1,0;-1/1:810:-1,0,0,0,1,0,0"
  | 13 => laurent_polynomial% "1/1:635:0,0,0,0,0,0,0;1/1:845:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:835:0,0,0,0,0,0,0;-1/1:905:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:640:0,0,0,0,0,0,0;1/1:810:0,-1,0,0,0,1,0"
  | 16 => laurent_polynomial% "1/1:410:0,0,0,0,0,0,0;1/1:810:0,-1,0,0,0,1,0"
  | 17 => laurent_polynomial% "1/1:470:0,0,0,0,0,0,0;-1/1:810:0,-2,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:580:0,0,0,0,0,0,0;-1/1:810:0,-2,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:730:0,0,0,0,0,0,0;1/1:810:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:320:0,0,0,0,0,0,0;1/1:810:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "-1/1:618:0,0,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:282:0,0,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:324:0,0,0,0,0,0,0;1/1:744:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:726:0,0,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:678:0,0,0,0,0,0,0;1/1:828:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:372:0,0,0,0,0,0,0;1/1:822:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "-1/1:34:-1,0,0,0,1,0,0;1/1:68:-2,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "-1/1:52:-1,0,0,0,1,0,0;1/1:104:-2,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "-1/1:58:-1,0,0,0,1,0,0;1/1:116:-2,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "-1/1:64:-1,0,0,0,1,0,0;1/1:128:-2,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "-1/1:76:-1,0,0,0,1,0,0;1/1:152:-2,0,0,0,0,0,0"
  | _ => []

compact_certificate def triTailPart16 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "-1/1:92:-1,0,0,0,1,0,0;1/1:184:-2,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "-1/1:144:-1,0,0,0,1,0,0;-1/1:708:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "-1/1:162:1,0,0,0,1,0,0;1/1:606:2,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "-1/1:164:-1,0,0,0,1,0,0;1/1:328:-2,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "-1/1:166:-1,0,0,0,1,0,0;1/1:332:-2,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "-1/1:172:-1,0,0,0,1,0,0;-1/1:694:-2,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "-1/1:174:-1,0,0,0,1,0,0;1/1:348:-2,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "-1/1:702:-2,0,0,0,0,0,0;1/1:876:-1,0,0,0,1,0,0"
  | 8 => laurent_polynomial% "-1/1:186:1,0,0,0,1,0,0;1/1:618:2,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "-1/1:192:-1,0,0,0,1,0,0;1/1:384:-2,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:408:-2,0,0,0,0,0,0;1/1:576:1,0,0,0,1,0,0"
  | 11 => laurent_polynomial% "-1/1:216:-1,0,0,0,1,0,0;1/1:432:-2,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "-1/1:234:-1,0,0,0,1,0,0;1/1:642:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:246:-1,0,0,0,1,0,0;1/1:648:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:254:-1,0,0,0,1,0,0;1/1:652:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "-1/1:258:-1,0,0,0,1,0,0;1/1:654:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:410:0,0,0,0,0,0,0;1/1:810:-1,-2,0,0,1,0,0"
  | 17 => laurent_polynomial% "-1/1:262:-1,0,0,0,1,0,0;1/1:656:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:134:0,0,0,0,0,0,0;-1/1:268:-1,0,0,0,1,0,0"
  | 19 => laurent_polynomial% "1/1:136:0,0,0,0,0,0,0;-1/1:272:-1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "-1/1:274:-1,0,0,0,1,0,0;1/1:662:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:138:0,0,0,0,0,0,0;-1/1:276:-1,0,0,0,1,0,0"
  | 22 => laurent_polynomial% "-1/1:282:-1,0,0,0,1,0,0;1/1:666:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:234:0,0,0,0,0,0,0;1/1:936:-2,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "-1/1:342:0,0,0,0,0,0,0;-1/1:474:-1,0,0,0,1,0,0"
  | 25 => laurent_polynomial% "1/1:766:0,0,0,0,0,0,0;1/1:878:-3,0,0,0,1,0,0"
  | 26 => laurent_polynomial% "1/1:242:0,0,0,0,0,0,0;1/1:886:-3,0,0,0,1,0,0"
  | 27 => laurent_polynomial% "1/1:254:0,0,0,0,0,0,0;1/1:1016:-2,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:256:0,0,0,0,0,0,0;-1/1:512:-1,0,0,0,1,0,0"
  | 29 => laurent_polynomial% "1/1:52:-3,0,0,0,1,0,0;1/1:794:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:34:-2,0,0,0,0,0,0;1/1:796:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:164:-3,0,0,0,1,0,0;1/1:808:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def triTailPart17 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:172:-3,0,0,0,1,0,0;1/1:284:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "-1/1:576:-1,0,0,0,1,0,0;-1/1:708:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:470:-2,0,0,0,0,0,0;-1/1:810:-1,-1,0,0,1,1,0;1/1:810:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:384:0,0,0,0,0,0,0;-1/1:768:-1,0,0,0,1,0,0"
  | 4 => laurent_polynomial% "-1/1:774:-1,0,0,0,1,0,0;1/1:912:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:388:0,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0"
  | 6 => laurent_polynomial% "-1/1:778:-1,0,0,0,1,0,0;1/1:914:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "-1/1:782:-1,0,0,0,1,0,0;1/1:916:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:394:0,0,0,0,0,0,0;-1/1:788:-1,0,0,0,1,0,0"
  | 9 => laurent_polynomial% "1/1:640:0,0,0,0,0,0,0;1/1:810:-1,-2,0,0,1,0,0"
  | 10 => laurent_polynomial% "1/1:396:0,0,0,0,0,0,0;-1/1:792:-1,0,0,0,1,0,0"
  | 11 => laurent_polynomial% "1/1:398:0,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0"
  | 12 => laurent_polynomial% "1/1:402:0,0,0,0,0,0,0;-1/1:804:-1,0,0,0,1,0,0"
  | 13 => laurent_polynomial% "1/1:408:0,0,0,0,0,0,0;-1/1:816:-1,0,0,0,1,0,0"
  | 14 => laurent_polynomial% "1/1:618:-2,0,0,0,0,0,0;-1/1:834:-1,0,0,0,1,0,0"
  | 15 => laurent_polynomial% "1/1:474:1,0,0,0,1,0,0;1/1:642:-2,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:666:-2,0,0,0,0,0,0;-1/1:858:-1,0,0,0,1,0,0"
  | 17 => laurent_polynomial% "1/1:432:2,0,0,0,0,0,0;-1/1:864:1,0,0,0,1,0,0"
  | 18 => laurent_polynomial% "1/1:174:-1,0,0,0,1,0,0;-1/1:348:-2,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:702:-2,0,0,0,0,0,0;-1/1:876:-1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "1/1:706:-2,0,0,0,0,0,0;-1/1:878:-1,0,0,0,1,0,0"
  | 21 => laurent_polynomial% "1/1:718:-2,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0"
  | 22 => laurent_polynomial% "1/1:722:-2,0,0,0,0,0,0;-1/1:886:-1,0,0,0,1,0,0"
  | 23 => laurent_polynomial% "1/1:444:2,0,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0"
  | 24 => laurent_polynomial% "-1/1:342:-2,0,0,0,0,0,0;-1/1:906:-1,0,0,0,1,0,0"
  | 25 => laurent_polynomial% "1/1:822:-2,0,0,0,0,0,0;-1/1:936:-1,0,0,0,1,0,0"
  | 26 => laurent_polynomial% "1/1:866:-2,0,0,0,0,0,0;-1/1:958:-1,0,0,0,1,0,0"
  | 27 => laurent_polynomial% "1/1:898:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "1/1:914:-2,0,0,0,0,0,0;1/1:1016:0,0,0,0,0,0,0;-1/1:1016:0,0,0,0,2,0,0"
  | 29 => laurent_polynomial% "1/1:922:-2,0,0,0,0,0,0;-1/1:986:-1,0,0,0,1,0,0"
  | 30 => laurent_polynomial% "1/1:934:-2,0,0,0,0,0,0;-1/1:992:-1,0,0,0,1,0,0"
  | 31 => laurent_polynomial% "1/1:946:-2,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0"
  | _ => []
compact_certificate def triTailPart18 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:512:0,0,0,0,0,0,0;1/1:998:-2,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:99:0,-2,0,0,0,0,0;1/1:711:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:365:0,0,0,0,0,0,0;1/1:810:0,-2,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:144:0,-2,0,0,0,0,0;1/1:366:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:162:0,-2,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:216:0,-2,0,0,0,0,0;1/1:724:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:727:0,0,0,0,0,0,0;-1/1:768:0,-2,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:729:0,0,0,0,0,0,0;-1/1:786:0,-2,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:394:0,0,0,0,0,0,0;1/1:396:0,-2,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:52:0,0,0,0,0,0,0;1/1:402:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "-1/1:162:0,-1,0,0,0,1,0;1/1:754:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:55:0,0,0,0,0,0,0;-1/1:810:-2,-1,0,0,0,1,0;1/1:810:-1,0,0,0,1,0,0"
  | 12 => laurent_polynomial% "1/1:445:0,0,0,0,0,0,0;-1/1:810:-1,-2,0,0,1,0,0;1/1:810:0,-1,0,0,0,1,0"
  | 13 => laurent_polynomial% "-1/1:810:-2,0,0,0,0,0,0;1/1:815:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:354:0,-1,0,0,0,1,0;1/1:818:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:426:0,-2,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:166:0,0,0,0,0,0,0;1/1:444:0,-2,0,0,0,0,0"
  | 17 => laurent_polynomial% "-1/1:834:-2,-2,0,0,0,0,0;1/1:869:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:171:0,0,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0"
  | 19 => laurent_polynomial% "-1/1:144:-2,-2,0,0,0,0,0;1/1:879:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "-1/1:216:-2,-2,0,0,0,0,0;1/1:881:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:606:0,-2,0,0,0,0,0;1/1:884:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:186:0,0,0,0,0,0,0;1/1:624:0,-2,0,0,0,0,0"
  | 23 => laurent_polynomial% "-1/1:696:0,-1,0,0,0,1,0;1/1:932:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "-1/1:810:-2,0,0,0,0,0,0;1/1:935:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:810:-1,-2,0,0,1,0,0;1/1:810:0,-1,0,0,0,1,0;1/1:955:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "-1/1:810:-2,-2,0,0,0,0,0;1/1:810:-1,-1,0,0,1,1,0;-1/1:810:0,0,0,0,0,0,0;1/1:985:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:365:0,0,0,0,0,0,0;-1/1:810:-2,-1,0,0,0,1,0;1/1:810:-1,0,0,0,1,0,0;1/1:810:0,-2,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:646:0,0,0,0,0,0,0;-1/1:888:0,-1,0,0,0,1,0"
  | 29 => laurent_polynomial% "1/1:648:0,0,0,0,0,0,0;1/1:998:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "-1/1:264:0,-2,0,0,0,0,0;1/1:321:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "-1/1:282:0,-2,0,0,0,0,0;1/1:673:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def triTailPart19 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:676:0,0,0,0,0,0,0;1/1:834:0,-2,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:332:0,0,0,0,0,0,0;1/1:888:0,-2,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:333:0,0,0,0,0,0,0;1/1:897:0,-2,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:684:0,0,0,0,0,0,0;1/1:906:0,-2,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:55:0,0,0,0,0,0,0;-1/1:810:-2,-1,0,0,0,1,0;1/1:810:-1,0,0,0,1,0,0;1/1:810:0,-2,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:339:0,0,0,0,0,0,0;1/1:951:0,-2,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:264:0,0,0,0,0,0,0;1/1:474:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:348:0,0,0,0,0,0,0;1/1:768:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:696:0,0,0,0,0,0,0;1/1:906:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:282:0,0,0,0,0,0,0;1/1:702:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:576:0,0,0,0,0,0,0;1/1:786:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:712:0,0,0,0,0,0,0;1/1:922:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:128:0,0,0,0,0,0,0;-1/1:688:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:144:0,0,0,0,0,0,0;1/1:354:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:348:0,0,0,0,0,0,0;1/1:648:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:402:0,0,0,0,0,0,0;1/1:702:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:421:0,0,0,0,0,0,0;1/1:631:0,0,0,0,0,0,0;1/1:841:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:419:0,0,0,0,0,0,0;1/1:629:0,0,0,0,0,0,0;1/1:839:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:422:0,0,0,0,0,0,0;1/1:632:0,0,0,0,0,0,0;1/1:842:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:418:0,0,0,0,0,0,0;1/1:628:0,0,0,0,0,0,0;1/1:838:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:424:0,0,0,0,0,0,0;1/1:634:0,0,0,0,0,0,0;1/1:844:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:416:0,0,0,0,0,0,0;1/1:626:0,0,0,0,0,0,0;1/1:836:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:216:0,0,0,0,0,0,0;1/1:426:0,0,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "-1/1:576:2,0,0,0,0,0,0;1/1:624:0,0,0,0,0,0,0;1/1:834:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "-1/1:410:0,0,0,0,0,0,0;-1/1:810:-1,-2,0,0,1,0,0;-1/1:935:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:640:0,0,0,0,0,0,0;-1/1:810:-2,0,0,0,0,0,0;-1/1:810:0,-1,0,0,0,1,0;-1/1:955:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:246:0,0,0,0,0,0,0;1/1:666:0,0,0,0,0,0,0;1/1:876:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:174:0,0,0,0,0,0,0;1/1:384:0,0,0,0,0,0,0;1/1:804:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "-1/1:410:0,0,0,0,0,0,0;-1/1:580:0,0,0,0,0,0,0;1/1:810:0,-2,0,0,0,0,0;1/1:810:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "-1/1:470:0,0,0,0,0,0,0;-1/1:640:0,0,0,0,0,0,0;1/1:810:0,-2,0,0,0,0,0;1/1:810:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:316:0,0,0,0,0,0,0;1/1:736:0,0,0,0,0,0,0;1/1:946:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:104:0,0,0,0,0,0,0;1/1:734:0,0,0,0,0,0,0;1/1:944:0,0,0,0,0,0,0"
  | _ => []


}
certificate_batch {
compact_certificate def triTailPart20 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:580:-2,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:845:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:470:-2,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;1/1:905:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "-1/1:432:2,0,0,0,0,0,0;1/1:864:1,0,0,0,1,0,0;1/1:888:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:162:0,0,0,0,0,0,0;1/1:186:1,0,0,0,1,0,0;-1/1:618:2,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:186:0,0,0,0,0,0,0;1/1:396:0,0,0,0,0,0,0;1/1:606:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:234:0,0,0,0,0,0,0;1/1:444:0,0,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "-1/1:62:-1,0,0,0,1,0,0;1/1:124:-2,0,0,0,0,0,0;1/1:556:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;-1/1:68:-1,0,0,0,1,0,0;1/1:136:-2,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "-1/1:74:-1,0,0,0,1,0,0;1/1:148:-2,0,0,0,0,0,0;1/1:562:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "-1/1:94:-1,0,0,0,1,0,0;1/1:188:-2,0,0,0,0,0,0;1/1:572:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "-1/1:122:-1,0,0,0,1,0,0;1/1:244:-2,0,0,0,0,0,0;1/1:586:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:62:0,0,0,0,0,0,0;-1/1:124:-1,0,0,0,1,0,0;1/1:248:-2,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:64:0,0,0,0,0,0,0;-1/1:128:-1,0,0,0,1,0,0;1/1:256:-2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:134:-1,0,0,0,1,0,0;1/1:268:-2,0,0,0,0,0,0;1/1:592:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:68:0,0,0,0,0,0,0;-1/1:136:-1,0,0,0,1,0,0;1/1:272:-2,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "-1/1:142:-1,0,0,0,1,0,0;1/1:284:-2,0,0,0,0,0,0;1/1:596:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:76:0,0,0,0,0,0,0;-1/1:152:-1,0,0,0,1,0,0;1/1:304:-2,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "-1/1:158:-1,0,0,0,1,0,0;1/1:316:-2,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "-1/1:410:-2,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:580:-1,0,0,0,1,0,0;1/1:810:-2,-2,0,0,0,0,0;1/1:810:-2,0,0,0,0,0,0;1/1:810:0,-1,0,0,0,1,0"
  | 19 => laurent_polynomial% "1/1:614:0,0,0,0,0,0,0;-1/1:706:-2,0,0,0,0,0,0;1/1:878:-1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "1/1:94:0,0,0,0,0,0,0;-1/1:188:-1,0,0,0,1,0,0;1/1:376:-2,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:388:-2,0,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0"
  | 22 => laurent_polynomial% "-1/1:218:-1,0,0,0,1,0,0;1/1:436:-2,0,0,0,0,0,0;1/1:634:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "-1/1:226:-1,0,0,0,1,0,0;1/1:452:-2,0,0,0,0,0,0;1/1:638:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:122:0,0,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:488:-2,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:128:0,0,0,0,0,0,0;-1/1:256:-1,0,0,0,1,0,0;1/1:512:-2,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "-1/1:278:-1,0,0,0,1,0,0;1/1:556:-2,0,0,0,0,0,0;1/1:664:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:142:0,0,0,0,0,0,0;-1/1:172:-4,0,0,0,0,0,0;-1/1:284:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "-1/1:286:-1,0,0,0,1,0,0;1/1:572:-2,0,0,0,0,0,0;1/1:668:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:144:0,0,0,0,0,0,0;1/1:576:-2,0,0,0,0,0,0;1/1:708:-1,0,0,0,1,0,0"
  | 30 => laurent_polynomial% "-1/1:302:-1,0,0,0,1,0,0;1/1:604:-2,0,0,0,0,0,0;1/1:676:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "-1/1:282:-1,0,0,0,1,0,0;-1/1:432:-1,0,0,0,1,0,0;1/1:624:-2,0,0,0,0,0,0"
  | _ => []
compact_certificate def triTailPart21 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:162:0,0,0,0,0,0,0;-1/1:162:0,0,0,0,2,0,0;1/1:606:1,0,0,0,1,0,0;1/1:648:-2,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:166:0,0,0,0,0,0,0;-1/1:332:-1,0,0,0,1,0,0;1/1:664:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:172:0,0,0,0,0,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0"
  | 3 => laurent_polynomial% "1/1:342:-2,0,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:696:-1,0,0,0,1,0,0"
  | 4 => laurent_polynomial% "1/1:174:0,0,0,0,0,0,0;-1/1:348:-1,0,0,0,1,0,0;1/1:696:-2,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:354:-2,0,0,0,0,0,0;-1/1:702:-1,0,0,0,1,0,0;1/1:876:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "-1/1:354:-1,0,0,0,1,0,0;1/1:702:0,0,0,0,0,0,0;1/1:708:-2,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:706:-1,0,0,0,1,0,0;1/1:712:-2,0,0,0,0,0,0;-1/1:878:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:192:0,0,0,0,0,0,0;-1/1:384:-1,0,0,0,1,0,0;1/1:768:-2,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "-1/1:386:-1,0,0,0,1,0,0;1/1:718:0,0,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "-1/1:388:-1,0,0,0,1,0,0;-1/1:696:0,-2,0,0,0,0,0;1/1:776:-2,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "-1/1:394:-1,0,0,0,1,0,0;1/1:722:0,0,0,0,0,0,0;1/1:788:-2,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "-1/1:398:-1,0,0,0,1,0,0;1/1:724:0,0,0,0,0,0,0;1/1:796:-2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:216:0,0,0,0,0,0,0;-1/1:432:-1,0,0,0,1,0,0;1/1:864:-2,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:172:-2,0,0,0,0,0,0;1/1:218:0,0,0,0,0,0,0;-1/1:436:-1,0,0,0,1,0,0"
  | 15 => laurent_polynomial% "1/1:718:-3,0,0,0,1,0,0;1/1:746:0,0,0,0,0,0,0;1/1:884:-2,0,0,0,0,0,0;-1/1:884:-2,0,0,0,2,0,0"
  | 16 => laurent_polynomial% "-1/1:446:-1,0,0,0,1,0,0;1/1:748:0,0,0,0,0,0,0;1/1:892:-2,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:226:0,0,0,0,0,0,0;-1/1:452:-1,0,0,0,1,0,0;1/1:904:-2,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "-1/1:458:-1,0,0,0,1,0,0;1/1:754:0,0,0,0,0,0,0;1/1:916:-2,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:236:0,0,0,0,0,0,0;-1/1:472:-1,0,0,0,1,0,0;1/1:944:-2,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "-1/1:478:-1,0,0,0,1,0,0;1/1:764:0,0,0,0,0,0,0;1/1:956:-2,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:244:0,0,0,0,0,0,0;-1/1:488:-1,0,0,0,1,0,0;1/1:976:-2,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "-1/1:494:-1,0,0,0,1,0,0;1/1:772:0,0,0,0,0,0,0;1/1:988:-2,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:248:0,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;1/1:992:-2,0,0,0,0,0,0;-1/1:992:-2,0,0,0,2,0,0"
  | 24 => laurent_polynomial% "1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;1/1:116:-3,0,0,0,1,0,0;1/1:802:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:62:-2,0,0,0,0,0,0;1/1:278:0,0,0,0,0,0,0;-1/1:556:-1,0,0,0,1,0,0"
  | 26 => laurent_polynomial% "1/1:74:-2,0,0,0,0,0,0;-1/1:562:-1,0,0,0,1,0,0;1/1:806:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:94:-2,0,0,0,0,0,0;1/1:286:0,0,0,0,0,0,0;-1/1:572:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "1/1:122:-2,0,0,0,0,0,0;-1/1:586:-1,0,0,0,1,0,0;1/1:818:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "1/1:146:-2,0,0,0,0,0,0;-1/1:598:-1,0,0,0,1,0,0;1/1:824:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:158:-2,0,0,0,0,0,0;1/1:302:0,0,0,0,0,0,0;-1/1:604:-1,0,0,0,1,0,0"
  | 31 => laurent_polynomial% "1/1:162:-2,0,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;1/1:828:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def triTailPart22 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;1/1:304:0,0,0,0,0,0,0;1/1:332:-3,0,0,0,1,0,0"
  | 1 => laurent_polynomial% "-1/1:614:-1,0,0,0,1,0,0;1/1:832:0,0,0,0,0,0,0;-1/1:878:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:186:-2,0,0,0,0,0,0;-1/1:618:-1,0,0,0,1,0,0;1/1:834:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "-1/1:622:-1,0,0,0,1,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:836:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:202:-2,0,0,0,0,0,0;-1/1:626:-1,0,0,0,1,0,0;1/1:838:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:218:-2,0,0,0,0,0,0;-1/1:634:-1,0,0,0,1,0,0;1/1:842:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:226:-2,0,0,0,0,0,0;-1/1:638:-1,0,0,0,1,0,0;1/1:844:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:234:-2,0,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;-1/1:642:-1,0,0,0,1,0,0"
  | 8 => laurent_polynomial% "1/1:262:-2,0,0,0,0,0,0;1/1:328:0,0,0,0,0,0,0;-1/1:656:-1,0,0,0,1,0,0"
  | 9 => laurent_polynomial% "1/1:274:-2,0,0,0,0,0,0;-1/1:354:0,-2,0,0,0,0,0;-1/1:662:-1,0,0,0,1,0,0"
  | 10 => laurent_polynomial% "1/1:278:-2,0,0,0,0,0,0;1/1:332:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0"
  | 11 => laurent_polynomial% "1/1:282:-2,0,0,0,0,0,0;-1/1:666:-1,0,0,0,1,0,0;1/1:858:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:302:-2,0,0,0,0,0,0;-1/1:676:-1,0,0,0,1,0,0;-1/1:688:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:386:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:162:1,-2,0,0,1,0,0;1/1:386:0,0,0,0,0,0,0;-1/1:606:2,-2,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:398:-2,0,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;-1/1:724:-1,0,0,0,1,0,0"
  | 16 => laurent_polynomial% "1/1:402:-2,0,0,0,0,0,0;1/1:444:1,0,0,0,1,0,0;1/1:888:0,0,0,0,0,0,0;-1/1:888:0,0,0,0,2,0,0"
  | 17 => laurent_polynomial% "1/1:418:-2,0,0,0,0,0,0;-1/1:734:-1,0,0,0,1,0,0;1/1:892:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:426:-2,0,0,0,0,0,0;-1/1:618:-1,0,0,0,1,0,0;-1/1:768:-1,0,0,0,1,0,0"
  | 19 => laurent_polynomial% "1/1:342:-1,0,0,0,1,0,0;1/1:474:-2,0,0,0,0,0,0;1/1:906:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:382:0,0,0,0,0,0,0;1/1:478:-2,0,0,0,0,0,0;-1/1:764:-1,0,0,0,1,0,0"
  | 21 => laurent_polynomial% "-1/1:766:-1,0,0,0,1,0,0;-1/1:878:-4,0,0,0,0,0,0;1/1:908:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:386:0,0,0,0,0,0,0;1/1:494:-2,0,0,0,0,0,0;-1/1:772:-1,0,0,0,1,0,0"
  | 23 => laurent_polynomial% "-1/1:52:-4,0,0,0,0,0,0;-1/1:794:-1,0,0,0,1,0,0;1/1:922:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:562:-2,0,0,0,0,0,0;-1/1:806:-1,0,0,0,1,0,0;1/1:928:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:578:-2,0,0,0,0,0,0;-1/1:814:-1,0,0,0,1,0,0;1/1:932:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:586:-2,0,0,0,0,0,0;-1/1:818:-1,0,0,0,1,0,0;1/1:934:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:412:0,0,0,0,0,0,0;1/1:598:-2,0,0,0,0,0,0;-1/1:824:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "1/1:416:0,0,0,0,0,0,0;1/1:614:-2,0,0,0,0,0,0;-1/1:832:-1,0,0,0,1,0,0"
  | 29 => laurent_polynomial% "1/1:418:0,0,0,0,0,0,0;1/1:622:-2,0,0,0,0,0,0;-1/1:836:-1,0,0,0,1,0,0"
  | 30 => laurent_polynomial% "1/1:626:-2,0,0,0,0,0,0;-1/1:838:-1,0,0,0,1,0,0;1/1:944:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:634:-2,0,0,0,0,0,0;-1/1:842:-1,0,0,0,1,0,0;1/1:946:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def triTailPart23 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:422:0,0,0,0,0,0,0;1/1:638:-2,0,0,0,0,0,0;-1/1:844:-1,0,0,0,1,0,0"
  | 1 => laurent_polynomial% "1/1:424:0,0,0,0,0,0,0;1/1:646:-2,0,0,0,0,0,0;-1/1:848:-1,0,0,0,1,0,0"
  | 2 => laurent_polynomial% "1/1:354:-1,-2,0,0,1,0,0;1/1:428:0,0,0,0,0,0,0;1/1:662:-2,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:674:-2,0,0,0,0,0,0;-1/1:862:-1,0,0,0,1,0,0;1/1:956:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:172:-1,0,0,0,1,0,0;1/1:436:0,0,0,0,0,0,0;1/1:694:-2,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:446:0,0,0,0,0,0,0;1/1:734:-2,0,0,0,0,0,0;-1/1:892:-1,0,0,0,1,0,0"
  | 6 => laurent_polynomial% "1/1:746:-2,0,0,0,0,0,0;-1/1:898:-1,0,0,0,1,0,0;1/1:974:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:754:-2,0,0,0,0,0,0;-1/1:902:-1,0,0,0,1,0,0;1/1:976:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:454:0,0,0,0,0,0,0;1/1:766:-2,0,0,0,0,0,0;-1/1:908:-1,0,0,0,1,0,0"
  | 9 => laurent_polynomial% "1/1:778:-2,0,0,0,0,0,0;-1/1:914:-1,0,0,0,1,0,0;1/1:1016:1,0,0,0,1,0,0"
  | 10 => laurent_polynomial% "1/1:458:0,0,0,0,0,0,0;1/1:782:-2,0,0,0,0,0,0;-1/1:916:-1,0,0,0,1,0,0"
  | 11 => laurent_polynomial% "1/1:794:-2,0,0,0,0,0,0;-1/1:922:-1,0,0,0,1,0,0;1/1:986:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:802:-2,0,0,0,0,0,0;-1/1:926:-1,0,0,0,1,0,0;1/1:988:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:464:0,0,0,0,0,0,0;1/1:806:-2,0,0,0,0,0,0;-1/1:928:-1,0,0,0,1,0,0"
  | 14 => laurent_polynomial% "1/1:466:0,0,0,0,0,0,0;1/1:814:-2,0,0,0,0,0,0;-1/1:932:-1,0,0,0,1,0,0"
  | 15 => laurent_polynomial% "1/1:818:-2,0,0,0,0,0,0;-1/1:934:-1,0,0,0,1,0,0;1/1:992:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:472:0,0,0,0,0,0,0;1/1:838:-2,0,0,0,0,0,0;-1/1:944:-1,0,0,0,1,0,0"
  | 17 => laurent_polynomial% "1/1:842:-2,0,0,0,0,0,0;-1/1:946:-1,0,0,0,1,0,0;1/1:998:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:478:0,0,0,0,0,0,0;1/1:862:-2,0,0,0,0,0,0;-1/1:956:-1,0,0,0,1,0,0"
  | 19 => laurent_polynomial% "1/1:488:0,0,0,0,0,0,0;1/1:902:-2,0,0,0,0,0,0;-1/1:976:-1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "1/1:494:0,0,0,0,0,0,0;1/1:926:-2,0,0,0,0,0,0;-1/1:988:-1,0,0,0,1,0,0"
  | 21 => laurent_polynomial% "1/1:234:0,-2,0,0,0,0,0;-1/1:444:2,0,0,0,0,0,0;1/1:888:1,0,0,0,1,0,0"
  | 22 => laurent_polynomial% "-1/1:282:0,0,0,0,0,0,0;-1/1:432:0,0,0,0,0,0,0;-1/1:708:0,-2,0,0,0,0,0"
  | 23 => laurent_polynomial% "-1/1:144:0,-1,0,0,0,1,0;1/1:398:0,0,0,0,0,0,0;1/1:432:0,-2,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:62:0,0,0,0,0,0,0;-1/1:186:0,-1,0,0,0,1,0;-1/1:342:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:216:0,-1,0,0,0,1,0;1/1:648:0,-2,0,0,0,0,0;1/1:772:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "-1/1:234:0,-1,0,0,0,1,0;1/1:702:0,-2,0,0,0,0,0;1/1:778:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:708:0,-1,0,0,0,1,0;1/1:796:0,0,0,0,0,0,0;1/1:864:0,-2,0,0,0,0,0"
  | 28 => laurent_polynomial% "-1/1:162:1,-1,0,0,1,1,0;1/1:458:0,0,0,0,0,0,0;1/1:606:2,-1,0,0,0,1,0"
  | 29 => laurent_polynomial% "-1/1:384:0,-1,0,0,0,1,0;1/1:478:0,0,0,0,0,0,0;1/1:828:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:136:0,0,0,0,0,0,0;1/1:174:0,-2,0,0,0,0,0;-1/1:408:0,-1,0,0,0,1,0"
  | 31 => laurent_polynomial% "1/1:282:0,-2,0,0,0,0,0;-1/1:444:0,-1,0,0,0,1,0;1/1:848:0,0,0,0,0,0,0"
  | _ => []

compact_certificate def triTailPart24 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:162:0,0,0,0,0,0,0;1/1:408:0,-2,0,0,0,0,0;1/1:512:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:342:-2,-2,0,0,0,0,0;1/1:867:0,0,0,0,0,0,0;1/1:906:-1,-2,0,0,1,0,0"
  | 2 => laurent_polynomial% "1/1:144:-1,-2,0,0,1,0,0;1/1:183:0,0,0,0,0,0,0;1/1:708:-2,-2,0,0,0,0,0"
  | 3 => laurent_polynomial% "-1/1:52:-2,0,0,0,0,0,0;1/1:642:0,-2,0,0,0,0,0;1/1:888:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "-1/1:606:0,-1,0,0,0,1,0;1/1:768:0,-2,0,0,0,0,0;1/1:902:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:234:0,0,0,0,0,0,0;-1/1:702:0,-1,0,0,0,1,0;1/1:934:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:586:0,0,0,0,0,0,0;-1/1:708:0,-1,0,0,0,1,0;1/1:936:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:444:2,-1,0,0,0,1,0;1/1:592:0,0,0,0,0,0,0;-1/1:888:1,-1,0,0,1,1,0"
  | 8 => laurent_polynomial% "1/1:394:0,-1,0,0,0,1,0;1/1:396:0,-3,0,0,0,1,0;1/1:598:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:186:0,-2,0,0,0,0,0;1/1:342:0,-1,0,0,0,1,0;1/1:604:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:278:0,0,0,0,0,0,0;1/1:402:0,-2,0,0,0,0,0;-1/1:834:0,-1,0,0,0,1,0"
  | 11 => laurent_polynomial% "1/1:638:0,0,0,0,0,0,0;-1/1:708:0,0,0,0,0,0,0;-1/1:864:0,-1,0,0,0,1,0"
  | 12 => laurent_polynomial% "1/1:302:0,0,0,0,0,0,0;1/1:618:0,-2,0,0,0,0,0;-1/1:906:0,-1,0,0,0,1,0"
  | 13 => laurent_polynomial% "-1/1:342:0,-2,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:354:0,-2,0,0,0,0,0;1/1:436:0,0,0,0,0,0,0;1/1:646:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "-1/1:648:0,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:94:0,0,0,0,0,0,0;1/1:724:0,0,0,0,0,0,0;1/1:934:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:234:-1,0,0,0,1,0,0;-1/1:642:0,0,0,0,0,0,0;1/1:747:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "-1/1:52:0,0,0,0,0,0,0;1/1:332:0,0,0,0,0,0,0;-1/1:402:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:207:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:282:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:396:0,0,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;1/1:696:0,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:639:0,0,0,0,0,0,0;-1/1:666:-2,0,0,0,0,0,0;1/1:849:0,0,0,0,0,0,0;1/1:858:-1,0,0,0,1,0,0"
  | 22 => laurent_polynomial% "1/1:192:-1,0,0,0,1,0,0;-1/1:384:-2,0,0,0,0,0,0;1/1:411:0,0,0,0,0,0,0;1/1:831:0,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "-1/1:348:0,0,0,0,0,0,0;1/1:408:0,0,0,0,0,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:648:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:174:-1,0,0,0,1,0,0;1/1:192:0,0,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:402:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:55:0,0,0,0,0,0,0;-1/1:410:-2,0,0,0,0,0,0;1/1:410:0,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:580:-1,0,0,0,1,0,0;1/1:810:-2,-2,0,0,0,0,0;1/1:810:-2,0,0,0,0,0,0;1/1:810:-1,-2,0,0,1,0,0;1/1:810:0,-1,0,0,0,1,0"
  | 26 => laurent_polynomial% "1/1:410:0,0,0,0,0,0,0;1/1:580:0,0,0,0,0,0,0;1/1:640:0,0,0,0,0,0,0;-1/1:810:0,-2,0,0,0,0,0;1/1:810:0,-1,0,0,0,1,0;-1/1:810:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:234:0,0,0,0,0,0,0;-1/1:264:0,0,0,0,0,0,0;-1/1:474:0,0,0,0,0,0,0;1/1:834:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:562:0,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:772:0,0,0,0,0,0,0;1/1:1016:1,0,0,0,1,0,0"
  | 29 => laurent_polynomial% "1/1:68:0,0,0,0,0,0,0;1/1:278:0,0,0,0,0,0,0;-1/1:348:0,0,0,0,0,0,0;1/1:488:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:284:0,0,0,0,0,0,0;-1/1:354:0,0,0,0,0,0,0;1/1:494:0,0,0,0,0,0,0;1/1:914:0,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:136:0,0,0,0,0,0,0;-1/1:696:0,0,0,0,0,0,0;1/1:766:0,0,0,0,0,0,0;1/1:976:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def triTailPart25 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:386:0,0,0,0,0,0,0;1/1:806:0,0,0,0,0,0,0;-1/1:876:0,0,0,0,0,0,0;1/1:1016:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;-1/1:174:0,0,0,0,0,0,0;1/1:244:0,0,0,0,0,0,0;1/1:664:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:410:-1,0,0,0,1,0,0;1/1:580:-1,0,0,0,1,0,0;1/1:580:0,0,0,0,0,0,0;-1/1:640:-2,0,0,0,0,0,0;-1/1:810:-2,-1,0,0,0,1,0;-1/1:810:-1,-2,0,0,1,0,0"
  | 3 => laurent_polynomial% "1/1:58:0,0,0,0,0,0,0;-1/1:116:-1,0,0,0,1,0,0;1/1:696:-2,-1,0,0,0,1,0;-1/1:932:-2,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "-1/1:146:-1,0,0,0,1,0,0;1/1:598:0,0,0,0,0,0,0;-1/1:712:-2,0,0,0,0,0,0;-1/1:922:-2,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "-1/1:410:-2,0,0,0,0,0,0;-1/1:410:-1,0,0,0,1,0,0;1/1:410:0,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:580:-1,0,0,0,1,0,0;-1/1:640:-1,0,0,0,1,0,0;-1/1:810:-2,-1,0,0,0,1,0;1/1:810:-1,-2,0,0,1,0,0;-1/1:810:-1,-1,0,0,1,1,0;1/1:810:-1,0,0,0,1,0,0"
  | 6 => laurent_polynomial% "1/1:348:-1,0,0,0,1,0,0;1/1:396:-2,0,0,0,0,0,0;1/1:624:0,0,0,0,0,0,0;1/1:648:-1,0,0,0,1,0,0"
  | 7 => laurent_polynomial% "1/1:410:0,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;1/1:580:0,0,0,0,0,0,0;-1/1:640:-1,0,0,0,1,0,0;-1/1:810:0,-2,0,0,0,0,0;-1/1:810:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:365:0,0,0,0,0,0,0;1/1:410:-2,0,0,0,0,0,0;1/1:410:-1,0,0,0,1,0,0;1/1:410:0,0,0,0,0,0,0;1/1:580:-1,0,0,0,1,0,0;1/1:580:0,0,0,0,0,0,0;1/1:810:-1,-1,0,0,1,1,0;1/1:810:0,-1,0,0,0,1,0;-1/1:810:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:116:0,0,0,0,0,0,0;1/1:464:-2,0,0,0,0,0,0;-1/1:696:-1,-1,0,0,1,1,0;1/1:932:-1,0,0,0,1,0,0"
  | 10 => laurent_polynomial% "-1/1:676:-2,0,0,0,0,0,0;-1/1:688:-1,0,0,0,1,0,0;-1/1:694:0,0,0,0,0,0,0;-1/1:834:-2,-2,0,0,0,0,0"
  | 11 => laurent_polynomial% "-1/1:264:-2,0,0,0,0,0,0;-1/1:342:-1,0,0,0,1,0,0;-1/1:474:-2,0,0,0,0,0,0;1/1:696:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:354:0,0,0,0,0,0,0;-1/1:576:-2,0,0,0,0,0,0;-1/1:708:-1,0,0,0,1,0,0;-1/1:786:-2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:216:-2,-2,0,0,0,0,0;-1/1:706:0,0,0,0,0,0,0;-1/1:712:-1,0,0,0,1,0,0;-1/1:724:-2,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:186:0,0,0,0,0,0,0;-1/1:186:0,0,0,0,2,0,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;1/1:618:1,0,0,0,1,0,0"
  | 15 => laurent_polynomial% "-1/1:458:-2,0,0,0,0,0,0;1/1:754:-1,0,0,0,1,0,0;-1/1:768:0,-2,0,0,0,0,0;-1/1:902:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "-1/1:162:-1,0,0,0,1,0,0;-1/1:186:0,0,0,0,0,0,0;1/1:394:-2,0,0,0,0,0,0;1/1:396:-2,-2,0,0,0,0,0;-1/1:396:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:134:-2,0,0,0,0,0,0;-1/1:592:-1,0,0,0,1,0,0;-1/1:646:0,0,0,0,0,0,0;1/1:888:0,-1,0,0,0,1,0"
  | 18 => laurent_polynomial% "-1/1:718:-4,0,0,0,0,0,0;-1/1:746:-1,0,0,0,1,0,0;1/1:884:-3,0,0,0,1,0,0;1/1:898:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:58:-3,0,0,0,1,0,0;-1/1:116:-4,0,0,0,0,0,0;-1/1:802:-1,0,0,0,1,0,0;1/1:926:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:186:1,0,0,0,1,0,0;-1/1:348:0,-2,0,0,0,0,0;-1/1:618:2,0,0,0,0,0,0;-1/1:648:0,-2,0,0,0,0,0"
  | 21 => laurent_polynomial% "-1/1:282:0,-1,0,0,0,1,0;1/1:444:0,0,0,0,0,0,0;-1/1:474:2,-2,0,0,0,0,0;1/1:794:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "-1/1:444:2,-1,0,0,0,1,0;1/1:802:0,0,0,0,0,0,0;1/1:888:1,-1,0,0,1,1,0;1/1:936:0,-1,0,0,0,1,0"
  | 23 => laurent_polynomial% "-1/1:186:1,-1,0,0,1,1,0;1/1:474:0,0,0,0,0,0,0;1/1:618:2,-1,0,0,0,1,0;1/1:824:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:186:1,-2,0,0,1,0,0;-1/1:474:0,-1,0,0,0,1,0;-1/1:618:2,-2,0,0,0,0,0;1/1:858:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:394:0,-2,0,0,0,0,0;-1/1:396:0,-4,0,0,0,0,0;1/1:666:0,0,0,0,0,0,0;1/1:1016:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "-1/1:348:0,-2,0,0,0,0,0;-1/1:396:0,-1,0,0,0,1,0;-1/1:768:0,-2,0,0,0,0,0;-1/1:878:-2,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:186:-2,0,0,0,0,0,0;-1/1:402:0,-1,0,0,0,1,0;1/1:624:-2,-2,0,0,0,0,0;1/1:834:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:192:0,0,0,0,0,0,0;-1/1:432:2,-2,0,0,0,0,0;-1/1:576:0,-1,0,0,0,1,0;1/1:864:1,-2,0,0,1,0,0"
  | 29 => laurent_polynomial% "1/1:216:0,0,0,0,0,0,0;1/1:426:-2,-2,0,0,0,0,0;-1/1:648:0,-1,0,0,0,1,0;1/1:864:-2,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:282:0,0,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;1/1:708:0,-2,0,0,0,0,0;-1/1:936:0,-1,0,0,0,1,0"
  | 31 => laurent_polynomial% "-1/1:576:2,-2,0,0,0,0,0;1/1:606:0,0,0,0,0,0,0;-1/1:768:0,-1,0,0,0,1,0;1/1:956:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def triTailPart26 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:282:0,-2,0,0,0,0,0;1/1:432:0,-2,0,0,0,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:804:0,-1,0,0,0,1,0"
  | 1 => laurent_polynomial% "-1/1:642:0,0,0,0,0,0,0;1/1:712:0,0,0,0,0,0,0;1/1:876:0,-1,0,0,0,1,0;-1/1:992:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:162:1,0,0,0,1,0,0;-1/1:186:0,-2,0,0,0,0,0;-1/1:396:0,-2,0,0,0,0,0;-1/1:606:0,-2,0,0,0,0,0;-1/1:606:2,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "-1/1:402:0,-2,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:702:0,-2,0,0,0,0,0;1/1:864:1,0,0,0,1,0,0"
  | 4 => laurent_polynomial% "1/1:62:0,0,0,0,0,0,0;-1/1:342:0,0,0,0,0,0,0;-1/1:878:-2,0,0,0,0,0,0;1/1:902:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:116:0,0,0,0,0,0,0;-1/1:676:0,0,0,0,0,0,0;-1/1:834:0,-2,0,0,0,0,0;1/1:956:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:572:0,0,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;1/1:782:0,0,0,0,0,0,0;1/1:992:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:394:0,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;-1/1:606:0,-2,0,0,0,0,0;-1/1:884:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:162:0,-1,0,0,0,1,0;-1/1:696:0,-2,0,0,0,0,0;-1/1:754:0,0,0,0,0,0,0;1/1:824:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "1/1:332:0,0,0,0,0,0,0;1/1:782:0,0,0,0,0,0,0;-1/1:878:-2,0,0,0,0,0,0;1/1:932:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "-1/1:264:0,0,0,0,0,0,0;1/1:339:0,0,0,0,0,0,0;-1/1:906:-2,0,0,0,0,0,0;1/1:939:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "-1/1:694:0,0,0,0,0,0,0;-1/1:696:0,-2,0,0,0,0,0;1/1:794:0,0,0,0,0,0,0;1/1:944:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:216:-1,0,0,0,1,0,0;-1/1:432:-2,0,0,0,0,0,0;-1/1:474:1,0,0,0,1,0,0;-1/1:642:-2,0,0,0,0,0,0;1/1:843:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:408:-2,0,0,0,0,0,0;-1/1:576:1,0,0,0,1,0,0;-1/1:618:-2,0,0,0,0,0,0;1/1:834:-1,0,0,0,1,0,0;1/1:837:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:162:0,0,0,0,0,0,0;-1/1:174:-1,0,0,0,1,0,0;1/1:348:-2,0,0,0,0,0,0;-1/1:432:0,0,0,0,0,0,0;1/1:702:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:348:0,0,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;1/1:702:-2,0,0,0,0,0,0;-1/1:876:-1,0,0,0,1,0,0;-1/1:888:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:186:0,0,0,0,0,0,0;-1/1:216:0,0,0,0,0,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:474:2,0,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "-1/1:216:-2,0,0,0,0,0,0;-1/1:264:0,0,0,0,0,0,0;-1/1:426:-2,0,0,0,0,0,0;1/1:618:-1,0,0,0,1,0,0;1/1:768:-1,0,0,0,1,0,0"
  | 18 => laurent_polynomial% "1/1:646:0,0,0,0,0,0,0;-1/1:696:0,0,0,0,0,0,0;1/1:796:0,0,0,0,0,0,0;-1/1:934:-2,0,0,0,0,0,0;1/1:992:-1,0,0,0,1,0,0"
  | 19 => laurent_polynomial% "1/1:92:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;1/1:606:-1,-2,0,0,1,0,0;-1/1:718:-2,0,0,0,0,0,0;1/1:884:-1,0,0,0,1,0,0"
  | 20 => laurent_polynomial% "1/1:234:-1,-2,0,0,1,0,0;-1/1:402:-2,0,0,0,0,0,0;-1/1:444:1,0,0,0,1,0,0;-1/1:642:0,-2,0,0,0,0,0;-1/1:888:0,0,0,0,0,0,0;1/1:888:0,0,0,0,2,0,0"
  | 21 => laurent_polynomial% "-1/1:186:-2,0,0,0,0,0,0;-1/1:396:-2,0,0,0,0,0,0;-1/1:408:-1,0,0,0,1,0,0;-1/1:576:2,0,0,0,0,0,0;-1/1:606:-2,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "1/1:282:0,0,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;-1/1:624:-1,0,0,0,1,0,0;-1/1:648:-2,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:174:-2,0,0,0,0,0,0;-1/1:174:-2,0,0,0,2,0,0;1/1:348:-3,0,0,0,1,0,0;1/1:444:2,0,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0;-1/1:936:0,0,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:432:1,0,0,0,1,0,0;1/1:444:0,0,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0;-1/1:864:0,0,0,0,2,0,0;-1/1:888:-1,0,0,0,1,0,0;-1/1:936:-2,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "1/1:444:2,-2,0,0,0,0,0;-1/1:664:0,0,0,0,0,0,0;1/1:734:0,0,0,0,0,0,0;-1/1:888:1,-2,0,0,1,0,0;1/1:944:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:166:-1,0,0,0,1,0,0;-1/1:332:-2,0,0,0,0,0,0;1/1:444:-1,-2,0,0,1,0,0;-1/1:888:-2,-2,0,0,0,0,0;1/1:958:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:64:0,0,0,0,0,0,0;-1/1:192:0,-1,0,0,0,1,0;1/1:576:0,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;-1/1:624:0,0,0,0,0,0,0;-1/1:834:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:68:0,0,0,0,0,0,0;1/1:174:-1,-2,0,0,1,0,0;-1/1:348:-2,-2,0,0,0,0,0;1/1:576:2,-1,0,0,0,1,0;1/1:768:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "-1/1:186:1,-1,0,0,1,1,0;-1/1:264:0,0,0,0,0,0,0;1/1:618:2,-1,0,0,0,1,0;-1/1:754:0,0,0,0,0,0,0;1/1:906:0,-2,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:166:0,0,0,0,0,0,0;-1/1:234:0,-2,0,0,0,0,0;1/1:444:2,0,0,0,0,0,0;1/1:796:0,0,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0"
  | 31 => laurent_polynomial% "1/1:116:0,0,0,0,0,0,0;-1/1:186:0,0,0,0,0,0,0;-1/1:348:0,-1,0,0,0,1,0;-1/1:396:0,0,0,0,0,0,0;-1/1:606:0,0,0,0,0,0,0"
  | _ => []
compact_certificate def triTailPart27 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "1/1:634:0,0,0,0,0,0,0;1/1:642:0,-1,0,0,0,1,0;1/1:844:0,0,0,0,0,0,0;-1/1:876:0,-2,0,0,0,0,0;-1/1:914:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "-1/1:216:0,0,0,0,0,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:474:0,-2,0,0,0,0,0;1/1:474:2,0,0,0,0,0,0;-1/1:858:0,-1,0,0,0,1,0;1/1:986:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "-1/1:234:0,-2,0,0,0,0,0;-1/1:444:0,-2,0,0,0,0,0;1/1:444:2,0,0,0,0,0,0;-1/1:864:0,-2,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0;-1/1:936:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:234:0,-1,0,0,0,1,0;1/1:638:0,0,0,0,0,0,0;-1/1:702:0,-2,0,0,0,0,0;-1/1:778:0,0,0,0,0,0,0;1/1:848:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "1/1:64:0,0,0,0,0,0,0;1/1:186:-2,0,0,0,0,0,0;1/1:274:0,0,0,0,0,0,0;1/1:624:-2,-2,0,0,0,0,0;1/1:694:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "1/1:426:-2,-2,0,0,0,0,0;-1/1:706:0,0,0,0,0,0,0;1/1:776:0,0,0,0,0,0,0;1/1:864:-2,0,0,0,0,0,0;1/1:986:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:162:1,-1,0,0,1,1,0;-1/1:458:0,0,0,0,0,0,0;1/1:598:0,0,0,0,0,0,0;-1/1:606:2,-1,0,0,0,1,0;-1/1:878:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "-1/1:676:0,0,0,0,0,0,0;1/1:776:0,0,0,0,0,0,0;-1/1:834:0,-2,0,0,0,0,0;-1/1:876:0,0,0,0,0,0,0;1/1:926:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "-1/1:234:0,0,0,0,0,0,0;1/1:354:0,0,0,0,0,0,0;-1/1:444:0,0,0,0,0,0,0;-1/1:576:2,0,0,0,0,0,0;-1/1:864:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "-1/1:396:0,0,0,0,0,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:474:2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;-1/1:606:0,0,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "-1/1:426:0,0,0,0,0,0,0;1/1:444:2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;1/1:696:0,0,0,0,0,0,0;-1/1:876:0,0,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0"
  | 11 => laurent_polynomial% "1/1:348:0,0,0,0,0,0,0;1/1:394:0,-1,0,0,0,1,0;1/1:396:0,-3,0,0,0,1,0;-1/1:398:0,0,0,0,0,0,0;-1/1:848:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:52:-2,0,0,0,0,0,0;1/1:166:-1,0,0,0,1,0,0;-1/1:332:-2,0,0,0,0,0,0;1/1:398:0,0,0,0,0,0,0;-1/1:642:0,-2,0,0,0,0,0;-1/1:888:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:186:-4,0,0,0,0,0,0;1/1:444:1,-1,0,0,1,1,0;1/1:592:-1,0,0,0,1,0,0;1/1:624:-4,-2,0,0,0,0,0;1/1:646:0,0,0,0,0,0,0;-1/1:888:0,-1,0,0,2,1,0"
  | 14 => laurent_polynomial% "-1/1:282:0,-2,0,0,0,0,0;1/1:444:0,-1,0,0,0,1,0;1/1:592:-2,0,0,0,0,0,0;1/1:646:-1,0,0,0,1,0,0;-1/1:848:0,0,0,0,0,0,0;-1/1:888:-1,-1,0,0,1,1,0"
  | 15 => laurent_polynomial% "-1/1:234:-2,0,0,0,0,0,0;1/1:402:-1,0,0,0,1,0,0;1/1:426:0,0,0,0,0,0,0;-1/1:444:-2,0,0,0,0,0,0;1/1:702:-1,0,0,0,1,0,0;-1/1:864:-2,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:144:-2,-1,0,0,0,1,0;1/1:216:-1,-2,0,0,1,0,0;-1/1:398:-2,0,0,0,0,0,0;-1/1:432:-2,-2,0,0,0,0,0;1/1:712:0,0,0,0,0,0,0;1/1:724:-1,0,0,0,1,0,0"
  | 17 => laurent_polynomial% "-1/1:162:-2,0,0,0,0,0,0;-1/1:186:-1,0,0,0,1,0,0;-1/1:348:0,0,0,0,0,0,0;-1/1:396:-1,0,0,0,1,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:648:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "-1/1:464:-1,0,0,0,1,0,0;1/1:648:-2,0,0,0,0,0,0;1/1:696:0,-1,0,0,0,1,0;-1/1:718:-2,0,0,0,0,0,0;-1/1:932:0,0,0,0,0,0,0;1/1:998:-2,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:162:1,0,0,0,1,0,0;-1/1:396:-2,0,0,0,0,0,0;1/1:474:0,0,0,0,0,0,0;-1/1:606:2,0,0,0,0,0,0;-1/1:648:-1,0,0,0,1,0,0;-1/1:696:-2,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:402:0,0,0,0,0,0,0;-1/1:432:0,0,0,0,0,0,0;-1/1:444:-1,0,0,0,1,0,0;-1/1:642:0,0,0,0,0,0,0;1/1:702:0,0,0,0,0,0,0;1/1:888:-2,0,0,0,0,0,0"
  | 21 => laurent_polynomial% "1/1:186:1,0,0,0,1,0,0;1/1:394:-1,0,0,0,1,0,0;1/1:396:-1,-2,0,0,1,0,0;-1/1:618:2,0,0,0,0,0,0;-1/1:702:-4,0,0,0,0,0,0;1/1:876:-3,0,0,0,1,0,0"
  | 22 => laurent_polynomial% "1/1:162:0,-1,0,0,0,1,0;-1/1:162:0,-1,0,0,2,1,0;1/1:426:-4,-2,0,0,0,0,0;1/1:458:-1,0,0,0,1,0,0;1/1:606:1,-1,0,0,1,1,0;-1/1:754:0,0,0,0,0,0,0;1/1:864:-4,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:396:0,-1,0,0,0,1,0;1/1:432:0,0,0,0,0,0,0;-1/1:474:2,-1,0,0,0,1,0;1/1:618:0,-2,0,0,0,0,0;1/1:696:0,-1,0,0,0,1,0;1/1:768:0,-2,0,0,0,0,0"
  | 24 => laurent_polynomial% "-1/1:162:0,-2,0,0,0,0,0;-1/1:186:1,-2,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;1/1:618:2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;1/1:876:-1,0,0,0,1,0,0"
  | 25 => laurent_polynomial% "1/1:172:-2,0,0,0,0,0,0;1/1:282:0,-2,0,0,0,0,0;-1/1:444:0,-1,0,0,0,1,0;-1/1:778:0,0,0,0,0,0,0;1/1:848:0,0,0,0,0,0,0;-1/1:864:0,-1,0,0,0,1,0"
  | 26 => laurent_polynomial% "-1/1:354:0,-2,0,0,0,0,0;-1/1:432:2,-1,0,0,0,1,0;-1/1:576:0,0,0,0,0,0,0;1/1:646:0,0,0,0,0,0,0;1/1:864:1,-1,0,0,1,1,0;-1/1:926:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "-1/1:162:1,0,0,0,1,0,0;-1/1:174:0,0,0,0,0,0,0;1/1:354:0,0,0,0,0,0,0;-1/1:474:0,0,0,0,0,0,0;1/1:606:2,0,0,0,0,0,0;-1/1:624:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:174:-1,0,0,0,1,0,0;-1/1:186:1,0,0,0,1,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;1/1:618:2,0,0,0,0,0,0;1/1:642:0,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0"
  | 29 => laurent_polynomial% "-1/1:348:0,0,0,0,0,0,0;1/1:408:0,0,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:864:1,0,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0"
  | 30 => laurent_polynomial% "1/1:174:-3,0,0,0,1,0,0;-1/1:348:-4,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:444:1,0,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;1/1:888:0,0,0,0,2,0,0;1/1:936:-1,0,0,0,1,0,0"
  | 31 => laurent_polynomial% "-1/1:278:-2,0,0,0,0,0,0;-1/1:332:0,0,0,0,0,0,0;-1/1:402:-2,-2,0,0,0,0,0;-1/1:444:1,-2,0,0,1,0,0;1/1:664:-1,0,0,0,1,0,0;1/1:834:-2,-1,0,0,0,1,0;-1/1:888:0,-2,0,0,0,0,0;1/1:888:0,-2,0,0,2,0,0"
  | _ => []

compact_certificate def triTailPart28 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "-1/1:234:-1,-1,0,0,1,1,0;-1/1:354:-2,-2,0,0,0,0,0;1/1:642:0,-1,0,0,0,1,0;1/1:702:-1,-2,0,0,1,0,0;1/1:778:-1,0,0,0,1,0,0;-1/1:876:0,-2,0,0,0,0,0;-1/1:914:0,0,0,0,0,0,0"
  | 1 => laurent_polynomial% "-1/1:162:0,-2,0,0,0,0,0;1/1:162:0,-2,0,0,2,0,0;1/1:216:-2,-1,0,0,0,1,0;1/1:386:-1,0,0,0,1,0,0;-1/1:606:1,-2,0,0,1,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:718:0,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "1/1:116:0,0,0,0,0,0,0;-1/1:348:0,-1,0,0,0,1,0;-1/1:396:0,0,0,0,0,0,0;-1/1:576:2,-2,0,0,0,0,0;1/1:624:0,-2,0,0,0,0,0;-1/1:676:0,0,0,0,0,0,0;-1/1:768:0,-1,0,0,0,1,0"
  | 3 => laurent_polynomial% "1/1:234:-2,-1,0,0,0,1,0;-1/1:282:0,0,0,0,0,0,0;-1/1:474:2,-1,0,0,0,1,0;-1/1:642:-1,-1,0,0,1,1,0;-1/1:778:-2,0,0,0,0,0,0;1/1:914:-1,0,0,0,1,0,0;-1/1:1016:1,0,0,0,1,0,0"
  | 4 => laurent_polynomial% "1/1:216:0,-2,0,0,0,0,0;1/1:234:0,0,0,0,0,0,0;1/1:426:0,-2,0,0,0,0,0;-1/1:702:0,-1,0,0,0,1,0;-1/1:794:0,0,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0;1/1:934:0,0,0,0,0,0,0"
  | 5 => laurent_polynomial% "-1/1:186:1,0,0,0,1,0,0;1/1:302:0,0,0,0,0,0,0;1/1:348:0,-2,0,0,0,0,0;1/1:512:0,0,0,0,0,0,0;1/1:618:2,0,0,0,0,0,0;1/1:648:0,-2,0,0,0,0,0;1/1:932:0,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "1/1:172:0,0,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;1/1:642:0,0,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;1/1:772:0,0,0,0,0,0,0;-1/1:876:0,-1,0,0,0,1,0;1/1:992:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:244:0,0,0,0,0,0,0;1/1:282:0,-1,0,0,0,1,0;1/1:394:0,0,0,0,0,0,0;-1/1:444:0,0,0,0,0,0,0;1/1:474:2,-2,0,0,0,0,0;1/1:694:0,0,0,0,0,0,0;-1/1:794:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "-1/1:162:1,0,0,0,1,0,0;1/1:264:0,0,0,0,0,0,0;1/1:396:0,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;1/1:606:2,0,0,0,0,0,0;-1/1:624:0,0,0,0,0,0,0;-1/1:834:0,0,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "-1/1:216:0,0,0,0,0,0,0;-1/1:402:-1,0,0,0,1,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:432:-1,0,0,0,1,0,0;1/1:444:-2,0,0,0,0,0,0;1/1:474:2,0,0,0,0,0,0;1/1:642:-1,0,0,0,1,0,0;-1/1:702:-1,0,0,0,1,0,0"
  | 10 => laurent_polynomial% "-1/1:348:-1,0,0,0,1,0,0;1/1:408:-1,0,0,0,1,0,0;1/1:576:2,0,0,0,0,0,0;1/1:606:-2,0,0,0,0,0,0;1/1:618:-1,0,0,0,1,0,0;-1/1:624:0,0,0,0,0,0,0;-1/1:648:-1,0,0,0,1,0,0;-1/1:834:0,0,0,0,0,0,0"
  | 11 => laurent_polynomial% "1/1:386:-1,0,0,0,1,0,0;-1/1:562:-2,0,0,0,0,0,0;-1/1:648:0,0,0,0,0,0,0;1/1:702:-2,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;1/1:806:-1,0,0,0,1,0,0;-1/1:876:-1,0,0,0,1,0,0;-1/1:998:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "-1/1:162:0,0,0,0,0,0,0;1/1:162:0,0,0,0,2,0,0;-1/1:186:-1,-2,0,0,1,0,0;-1/1:396:-1,-2,0,0,1,0,0;-1/1:408:0,-2,0,0,0,0,0;-1/1:512:0,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:606:1,0,0,0,1,0,0;-1/1:648:-2,0,0,0,0,0,0;-1/1:998:-2,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;-1/1:234:0,0,0,0,0,0,0;1/1:264:0,0,0,0,0,0,0;1/1:444:2,-2,0,0,0,0,0;1/1:474:0,0,0,0,0,0,0;-1/1:834:0,0,0,0,0,0,0;-1/1:888:1,-2,0,0,1,0,0;-1/1:936:0,-2,0,0,0,0,0"
  | 14 => laurent_polynomial% "1/1:186:0,0,0,0,0,0,0;-1/1:216:0,0,0,0,0,0,0;1/1:282:-1,0,0,0,1,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:432:-1,0,0,0,1,0,0;1/1:474:2,0,0,0,0,0,0;-1/1:624:-2,0,0,0,0,0,0;-1/1:834:-2,0,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:76:0,0,0,0,0,0,0;-1/1:234:0,-2,0,0,0,0,0;-1/1:432:2,-1,0,0,0,1,0;1/1:444:2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;1/1:676:0,0,0,0,0,0,0;1/1:864:1,-1,0,0,1,1,0;-1/1:888:1,0,0,0,1,0,0;-1/1:926:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "1/1:172:0,0,0,0,0,0,0;1/1:282:0,0,0,0,0,0,0;-1/1:348:0,-2,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;1/1:618:0,-2,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;1/1:802:0,0,0,0,0,0,0;1/1:876:-1,-2,0,0,1,0,0;1/1:888:0,-2,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:162:0,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "1/1:264:0,-1,0,0,0,1,0;-1/1:348:0,0,0,0,0,0,0;1/1:408:0,0,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;1/1:474:0,-1,0,0,0,1,0;1/1:618:0,0,0,0,0,0,0;-1/1:718:0,0,0,0,0,0,0;-1/1:864:1,0,0,0,1,0,0;1/1:998:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:216:-1,0,0,0,1,0,0;1/1:402:-2,0,0,0,0,0,0;1/1:426:-1,0,0,0,1,0,0;-1/1:432:-2,0,0,0,0,0,0;-1/1:474:1,0,0,0,1,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;1/1:702:-2,0,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "-1/1:34:-2,0,0,0,0,0,0;1/1:52:-1,0,0,0,1,0,0;1/1:174:-2,0,0,0,0,0,0;-1/1:234:0,-2,0,0,0,0,0;-1/1:244:-2,0,0,0,0,0,0;1/1:402:-1,0,0,0,1,0,0;1/1:444:2,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0"
  | 21 => laurent_polynomial% "-1/1:162:0,-1,0,0,0,1,0;-1/1:162:1,0,0,0,1,0,0;-1/1:174:-1,-1,0,0,1,1,0;1/1:348:-2,-1,0,0,0,1,0;1/1:396:0,-2,0,0,0,0,0;-1/1:432:0,-1,0,0,0,1,0;-1/1:604:0,0,0,0,0,0,0;1/1:606:0,-2,0,0,0,0,0;1/1:606:2,0,0,0,0,0,0;1/1:702:0,-1,0,0,0,1,0;1/1:884:0,0,0,0,0,0,0"
  | 22 => laurent_polynomial% "-1/1:58:0,0,0,0,0,0,0;1/1:116:-1,0,0,0,1,0,0;1/1:174:0,-1,0,0,0,1,0;-1/1:186:-1,0,0,0,1,0,0;-1/1:348:-1,-1,0,0,1,1,0;-1/1:396:-1,0,0,0,1,0,0;-1/1:408:0,0,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;1/1:932:-2,0,0,0,0,0,0"
  | 23 => laurent_polynomial% "1/1:402:0,-1,0,0,0,1,0;-1/1:426:0,-2,0,0,0,0,0;-1/1:576:0,-2,0,0,0,0,0;-1/1:606:0,-2,0,0,0,0,0;1/1:634:0,0,0,0,0,0,0;1/1:696:0,-2,0,0,0,0,0;1/1:702:0,-1,0,0,0,1,0;-1/1:876:0,-2,0,0,0,0,0;1/1:936:0,-2,0,0,0,0,0"
  | 24 => laurent_polynomial% "1/1:162:-2,-1,0,0,0,1,0;-1/1:606:-1,-1,0,0,1,1,0;1/1:676:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;1/1:768:-1,-2,0,0,1,0,0;-1/1:776:0,0,0,0,0,0,0;1/1:834:0,-2,0,0,0,0,0;1/1:876:0,0,0,0,0,0,0;1/1:902:-1,0,0,0,1,0,0;-1/1:926:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:264:0,-2,0,0,0,0,0;1/1:426:-2,-2,0,0,0,0,0;1/1:474:2,0,0,0,0,0,0;-1/1:702:-2,-1,0,0,0,1,0;-1/1:706:0,0,0,0,0,0,0;1/1:864:-2,0,0,0,0,0,0;1/1:876:-1,-1,0,0,1,1,0;1/1:934:-2,0,0,0,0,0,0;1/1:986:0,0,0,0,0,0,0;-1/1:992:-1,0,0,0,1,0,0"
  | 26 => laurent_polynomial% "-1/1:162:1,0,0,0,1,0,0;1/1:186:0,-2,0,0,0,0,0;-1/1:386:-2,0,0,0,0,0,0;1/1:396:0,-2,0,0,0,0,0;1/1:606:0,-2,0,0,0,0,0;1/1:606:2,0,0,0,0,0,0;1/1:648:-1,0,0,0,1,0,0;-1/1:806:-2,0,0,0,0,0,0;1/1:876:-2,0,0,0,0,0,0;1/1:998:-1,0,0,0,1,0,0;-1/1:1016:-2,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "1/1:34:-1,0,0,0,1,0,0;-1/1:52:0,0,0,0,0,0,0;-1/1:68:-2,0,0,0,0,0,0;-1/1:174:-1,0,0,0,1,0,0;1/1:244:-1,0,0,0,1,0,0;-1/1:278:-2,0,0,0,0,0,0;1/1:348:-2,0,0,0,0,0,0;-1/1:402:0,0,0,0,0,0,0;-1/1:488:-2,0,0,0,0,0,0;1/1:664:-1,0,0,0,1,0,0"
  | 28 => laurent_polynomial% "1/1:58:0,0,0,0,0,0,0;-1/1:174:0,-1,0,0,0,1,0;1/1:234:0,-1,0,0,0,1,0;-1/1:264:0,-1,0,0,0,1,0;1/1:348:0,0,0,0,0,0,0;-1/1:474:0,-1,0,0,0,1,0;-1/1:618:0,0,0,0,0,0,0;1/1:648:0,0,0,0,0,0,0;1/1:688:0,0,0,0,0,0,0;1/1:834:0,-1,0,0,0,1,0"
  | 29 => laurent_polynomial% "1/1:68:0,0,0,0,0,0,0;1/1:278:0,0,0,0,0,0,0;1/1:297:0,-2,0,0,0,0,0;1/1:348:-1,-1,0,0,1,1,0;-1/1:348:0,0,0,0,0,0,0;1/1:396:-2,-1,0,0,0,1,0;1/1:488:0,0,0,0,0,0,0;1/1:624:0,-1,0,0,0,1,0;1/1:648:-1,-1,0,0,1,1,0;1/1:766:-1,0,0,0,1,0,0;1/1:878:-4,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "1/1:174:-1,0,0,0,1,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:216:0,-1,0,0,0,1,0;-1/1:348:-2,0,0,0,0,0,0;-1/1:426:0,-1,0,0,0,1,0;1/1:432:2,-2,0,0,0,0,0;1/1:474:2,-1,0,0,0,1,0;-1/1:864:1,-2,0,0,1,0,0;-1/1:888:0,-2,0,0,0,0,0;1/1:936:0,-1,0,0,0,1,0"
  | 31 => laurent_polynomial% "1/1:186:0,0,0,0,2,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:282:-2,-1,0,0,0,1,0;1/1:402:-1,0,0,0,1,0,0;-1/1:432:-2,-1,0,0,0,1,0;-1/1:432:-1,0,0,0,1,0,0;-1/1:618:1,0,0,0,1,0,0;-1/1:642:-1,0,0,0,1,0,0;1/1:702:-1,0,0,0,1,0,0;1/1:936:0,0,0,0,0,0,0;-1/1:944:-2,0,0,0,0,0,0"
  | _ => []
compact_certificate def triTailPart29 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "-1/1:69:0,-2,0,0,0,0,0;-1/1:348:-1,-2,0,0,1,0,0;1/1:348:0,-1,0,0,0,1,0;1/1:426:-2,-2,0,0,0,0,0;-1/1:444:0,-2,0,0,0,0,0;1/1:576:-2,-2,0,0,0,0,0;1/1:648:0,-1,0,0,0,1,0;1/1:766:0,0,0,0,0,0,0;-1/1:768:-1,-2,0,0,1,0,0;1/1:876:-2,-2,0,0,0,0,0;1/1:888:-1,-2,0,0,1,0,0"
  | 1 => laurent_polynomial% "-1/1:76:-2,0,0,0,0,0,0;1/1:216:-2,0,0,0,0,0,0;1/1:426:-4,-2,0,0,0,0,0;1/1:458:-1,0,0,0,1,0,0;-1/1:648:-2,-1,0,0,0,1,0;-1/1:706:-2,0,0,0,0,0,0;-1/1:754:0,0,0,0,0,0,0;1/1:859:0,0,0,0,0,0,0;1/1:864:-4,0,0,0,0,0,0;1/1:878:-1,0,0,0,1,0,0"
  | 2 => laurent_polynomial% "-1/1:162:-1,0,0,0,1,0,0;-1/1:174:-2,0,0,0,0,0,0;1/1:282:-1,0,0,0,1,0,0;-1/1:426:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;-1/1:624:-2,0,0,0,0,0,0;1/1:696:0,0,0,0,0,0,0;1/1:702:-1,0,0,0,1,0,0;-1/1:876:0,0,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:162:0,-2,0,0,0,0,0;1/1:174:-1,-2,0,0,1,0,0;-1/1:348:-2,-2,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:398:0,0,0,0,0,0,0;1/1:432:0,-2,0,0,0,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:702:0,-2,0,0,0,0,0;1/1:768:0,0,0,0,0,0,0;-1/1:848:0,0,0,0,0,0,0;1/1:878:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0"
  | 4 => laurent_polynomial% "-1/1:282:0,0,0,0,0,0,0;1/1:332:0,0,0,0,0,0,0;-1/1:396:0,-1,0,0,0,1,0;-1/1:432:0,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;-1/1:696:0,-1,0,0,0,1,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:768:0,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:878:-2,0,0,0,0,0,0;-1/1:1016:1,0,0,0,1,0,0"
  | 5 => laurent_polynomial% "-1/1:302:-2,0,0,0,0,0,0;1/1:426:-2,-1,0,0,0,1,0;-1/1:444:0,-1,0,0,0,1,0;1/1:576:-2,-1,0,0,0,1,0;-1/1:618:-2,-2,0,0,0,0,0;1/1:676:-1,0,0,0,1,0,0;1/1:688:0,0,0,0,0,0,0;-1/1:696:-2,-1,0,0,0,1,0;1/1:834:-1,-2,0,0,1,0,0;1/1:876:-2,-1,0,0,0,1,0;1/1:888:-1,-1,0,0,1,1,0"
  | 6 => laurent_polynomial% "-1/1:174:0,0,0,0,0,0,0;1/1:244:0,0,0,0,0,0,0;-1/1:264:0,0,0,0,0,0,0;1/1:282:0,-1,0,0,0,1,0;1/1:354:0,0,0,0,0,0,0;1/1:432:0,-1,0,0,0,1,0;-1/1:444:0,0,0,0,0,0,0;-1/1:474:0,0,0,0,0,0,0;-1/1:576:2,0,0,0,0,0,0;1/1:834:0,0,0,0,0,0,0;-1/1:864:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "-1/1:62:0,0,0,0,0,0,0;1/1:162:0,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:348:-2,0,0,0,0,0,0;1/1:348:0,-2,0,0,0,0,0;1/1:396:0,-1,0,0,0,1,0;1/1:432:0,0,0,0,0,0,0;1/1:606:0,-1,0,0,0,1,0;-1/1:702:0,0,0,0,0,0,0;1/1:878:-2,0,0,0,0,0,0;-1/1:902:0,0,0,0,0,0,0"
  | 8 => laurent_polynomial% "1/1:348:0,-2,0,0,0,0,0;-1/1:408:0,-2,0,0,0,0,0;1/1:426:0,-1,0,0,0,1,0;-1/1:432:2,-2,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;1/1:648:0,-2,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:772:0,0,0,0,0,0,0;-1/1:842:0,0,0,0,0,0,0;1/1:864:1,-2,0,0,1,0,0;1/1:1016:1,0,0,0,1,0,0"
  | 9 => laurent_polynomial% "1/1:174:0,-1,0,0,0,1,0;1/1:264:0,-1,0,0,0,1,0;-1/1:282:0,-2,0,0,0,0,0;-1/1:348:0,0,0,0,0,0,0;-1/1:354:0,-1,0,0,0,1,0;-1/1:432:0,-2,0,0,0,0,0;1/1:444:0,-1,0,0,0,1,0;1/1:474:0,-1,0,0,0,1,0;1/1:576:2,-1,0,0,0,1,0;-1/1:648:0,0,0,0,0,0,0;-1/1:834:0,-1,0,0,0,1,0;1/1:864:0,-1,0,0,0,1,0"
  | 10 => laurent_polynomial% "-1/1:174:0,0,0,0,0,0,0;-1/1:264:0,0,0,0,0,0,0;1/1:348:-1,0,0,0,1,0,0;1/1:354:0,0,0,0,0,0,0;-1/1:426:-2,0,0,0,0,0,0;-1/1:474:0,0,0,0,0,0,0;-1/1:576:-2,0,0,0,0,0,0;-1/1:576:2,0,0,0,0,0,0;1/1:768:-1,0,0,0,1,0,0;1/1:834:0,0,0,0,0,0,0;-1/1:864:0,0,0,0,0,0,0;-1/1:876:-2,0,0,0,0,0,0;-1/1:888:-1,0,0,0,1,0,0"
  | 11 => laurent_polynomial% "1/1:52:-4,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:234:-1,0,0,0,1,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:354:-2,-1,0,0,0,1,0;1/1:398:-2,0,0,0,0,0,0;-1/1:642:-2,-2,0,0,0,0,0;-1/1:642:0,0,0,0,0,0,0;-1/1:702:-1,-1,0,0,1,1,0;1/1:876:0,-1,0,0,0,1,0;-1/1:888:-2,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:992:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "-1/1:58:-2,0,0,0,0,0,0;1/1:64:-1,0,0,0,1,0,0;1/1:174:-2,-1,0,0,0,1,0;1/1:186:-3,0,0,0,1,0,0;1/1:274:-1,0,0,0,1,0,0;-1/1:408:-2,0,0,0,0,0,0;1/1:444:2,-1,0,0,0,1,0;1/1:624:-3,-2,0,0,1,0,0;1/1:694:-1,0,0,0,1,0,0;-1/1:802:0,0,0,0,0,0,0;-1/1:888:1,-1,0,0,1,1,0;-1/1:936:0,-1,0,0,0,1,0"
  | 13 => laurent_polynomial% "-1/1:396:0,-1,0,0,0,1,0;1/1:402:0,0,0,0,0,0,0;-1/1:426:0,-1,0,0,0,1,0;-1/1:432:0,0,0,0,0,0,0;1/1:474:2,-1,0,0,0,1,0;-1/1:576:0,-1,0,0,0,1,0;-1/1:606:0,-1,0,0,0,1,0;1/1:702:0,0,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;-1/1:876:0,-1,0,0,0,1,0;1/1:936:0,-1,0,0,0,1,0;1/1:992:0,0,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:174:-1,-2,0,0,1,0,0;1/1:186:1,-2,0,0,1,0,0;1/1:348:-2,-2,0,0,0,0,0;-1/1:348:0,0,0,0,0,0,0;-1/1:432:0,-2,0,0,0,0,0;-1/1:576:2,-1,0,0,0,1,0;-1/1:618:2,-2,0,0,0,0,0;1/1:624:0,-1,0,0,0,1,0;-1/1:642:0,-2,0,0,0,0,0;1/1:702:0,-2,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0;1/1:834:0,-1,0,0,0,1,0;1/1:838:0,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "1/1:52:0,0,0,0,0,0,0;-1/1:302:0,0,0,0,0,0,0;1/1:426:0,-1,0,0,0,1,0;-1/1:444:2,-1,0,0,0,1,0;1/1:576:0,-1,0,0,0,1,0;1/1:606:0,-1,0,0,0,1,0;-1/1:618:0,-2,0,0,0,0,0;-1/1:696:0,-1,0,0,0,1,0;-1/1:702:0,0,0,0,0,0,0;-1/1:768:0,-2,0,0,0,0,0;1/1:876:0,-1,0,0,0,1,0;1/1:888:1,-1,0,0,1,1,0;-1/1:902:0,0,0,0,0,0,0"
  | 16 => laurent_polynomial% "-1/1:162:1,-2,0,0,1,0,0;-1/1:174:0,-2,0,0,0,0,0;-1/1:186:0,0,0,0,0,0,0;1/1:216:0,0,0,0,0,0,0;1/1:354:0,-2,0,0,0,0,0;1/1:426:0,0,0,0,0,0,0;-1/1:474:0,-2,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;1/1:576:0,0,0,0,0,0,0;1/1:606:2,-2,0,0,0,0,0;-1/1:624:0,-2,0,0,0,0,0;-1/1:646:0,0,0,0,0,0,0;1/1:888:0,-1,0,0,0,1,0;-1/1:936:0,0,0,0,0,0,0"
  | 17 => laurent_polynomial% "1/1:162:1,-1,0,0,1,1,0;1/1:166:-1,0,0,0,1,0,0;1/1:174:0,-1,0,0,0,1,0;-1/1:332:-2,0,0,0,0,0,0;1/1:402:0,-2,0,0,0,0,0;-1/1:432:0,-2,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;1/1:474:0,-1,0,0,0,1,0;-1/1:606:2,-1,0,0,0,1,0;1/1:624:0,-1,0,0,0,1,0;-1/1:642:0,-2,0,0,0,0,0;1/1:702:0,-2,0,0,0,0,0;-1/1:864:1,0,0,0,1,0,0;-1/1:888:0,0,0,0,0,0,0"
  | 18 => laurent_polynomial% "-1/1:186:-1,0,0,0,1,0,0;1/1:216:-1,0,0,0,1,0,0;-1/1:282:-2,0,0,0,0,0,0;-1/1:348:0,0,0,0,0,0,0;1/1:426:-1,0,0,0,1,0,0;-1/1:432:-2,0,0,0,0,0,0;-1/1:474:1,0,0,0,1,0,0;1/1:576:-1,0,0,0,1,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;1/1:876:-1,0,0,0,1,0,0;1/1:888:0,0,0,0,0,0,0;-1/1:936:-1,0,0,0,1,0,0"
  | 19 => laurent_polynomial% "-1/1:58:-1,0,0,0,1,0,0;1/1:64:0,0,0,0,0,0,0;1/1:116:-2,0,0,0,0,0,0;1/1:174:-1,-1,0,0,1,1,0;1/1:186:-2,0,0,0,0,0,0;1/1:186:0,-2,0,0,0,0,0;-1/1:216:0,-2,0,0,0,0,0;-1/1:348:-2,-1,0,0,0,1,0;-1/1:426:0,-2,0,0,0,0,0;1/1:474:2,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;1/1:624:-2,-2,0,0,0,0,0;1/1:694:0,0,0,0,0,0,0;1/1:936:0,-2,0,0,0,0,0"
  | 20 => laurent_polynomial% "-1/1:282:-2,-1,0,0,0,1,0;-1/1:426:-2,-2,0,0,0,0,0;1/1:426:-1,-1,0,0,1,1,0;1/1:426:0,0,0,0,0,0,0;-1/1:474:0,-2,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;1/1:576:-1,-1,0,0,1,1,0;1/1:606:-1,-1,0,0,1,1,0;-1/1:696:-1,-1,0,0,1,1,0;1/1:706:0,0,0,0,0,0,0;1/1:753:0,-1,0,0,0,1,0;-1/1:864:-2,0,0,0,0,0,0;-1/1:934:-2,0,0,0,0,0,0;-1/1:936:-1,-1,0,0,1,1,0;-1/1:986:0,0,0,0,0,0,0;1/1:992:-1,0,0,0,1,0,0"
  | 21 => laurent_polynomial% "-1/1:62:0,0,0,0,0,0,0;1/1:216:0,-1,0,0,0,1,0;-1/1:348:0,-2,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;-1/1:474:2,-1,0,0,0,1,0;-1/1:512:0,0,0,0,0,0,0;1/1:618:0,-2,0,0,0,0,0;-1/1:648:0,-2,0,0,0,0,0;1/1:712:0,0,0,0,0,0,0;-1/1:772:0,0,0,0,0,0,0;1/1:888:0,-2,0,0,0,0,0;-1/1:936:0,-1,0,0,0,1,0;-1/1:1016:1,0,0,0,1,0,0"
  | 22 => laurent_polynomial% "-1/1:282:-2,0,0,0,0,0,0;-1/1:348:0,0,0,0,0,0,0;1/1:408:0,0,0,0,0,0,0;1/1:426:-1,0,0,0,1,0,0;1/1:432:2,0,0,0,0,0,0;1/1:576:-1,0,0,0,1,0,0;1/1:606:-1,0,0,0,1,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:648:0,0,0,0,0,0,0;-1/1:696:-1,0,0,0,1,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:864:1,0,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:936:-1,0,0,0,1,0,0"
  | 23 => laurent_polynomial% "1/1:58:-1,0,0,0,1,0,0;-1/1:64:0,0,0,0,0,0,0;-1/1:116:-2,0,0,0,0,0,0;-1/1:174:-1,-1,0,0,1,1,0;-1/1:186:-2,0,0,0,0,0,0;1/1:186:1,-1,0,0,1,1,0;1/1:348:-2,-1,0,0,0,1,0;1/1:402:0,-1,0,0,0,1,0;-1/1:432:0,-1,0,0,0,1,0;-1/1:576:0,-2,0,0,0,0,0;-1/1:576:2,0,0,0,0,0,0;-1/1:618:2,-1,0,0,0,1,0;-1/1:624:-2,-2,0,0,0,0,0;1/1:624:0,0,0,0,0,0,0;-1/1:642:0,-1,0,0,0,1,0;-1/1:694:0,0,0,0,0,0,0;1/1:702:0,-1,0,0,0,1,0"
  | 24 => laurent_polynomial% "-1/1:166:0,0,0,0,0,0,0;1/1:174:0,-2,0,0,0,0,0;1/1:234:0,-2,0,0,0,0,0;1/1:348:0,-1,0,0,0,1,0;-1/1:386:0,0,0,0,0,0,0;-1/1:408:0,-1,0,0,0,1,0;-1/1:444:2,0,0,0,0,0,0;-1/1:618:0,-1,0,0,0,1,0;1/1:702:-2,-1,0,0,0,1,0;-1/1:796:0,0,0,0,0,0,0;-1/1:876:-1,-1,0,0,1,1,0;-1/1:888:0,-1,0,0,0,1,0;1/1:888:1,0,0,0,1,0,0;1/1:936:0,0,0,0,0,0,0;-1/1:986:0,0,0,0,0,0,0"
  | 25 => laurent_polynomial% "-1/1:162:1,0,0,0,1,0,0;1/1:264:0,0,0,0,0,0,0;1/1:396:0,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;-1/1:604:0,0,0,0,0,0,0;1/1:606:0,-2,0,0,0,0,0;1/1:606:2,0,0,0,0,0,0;-1/1:624:0,0,0,0,0,0,0;1/1:642:0,-1,0,0,0,1,0;1/1:664:0,0,0,0,0,0,0;-1/1:834:0,0,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0;-1/1:876:0,-2,0,0,0,0,0;1/1:884:0,0,0,0,0,0,0;-1/1:914:0,0,0,0,0,0,0"
  | 26 => laurent_polynomial% "1/1:186:-2,0,0,0,0,0,0;1/1:264:0,0,0,0,0,0,0;-1/1:426:0,-2,0,0,0,0,0;1/1:444:2,-2,0,0,0,0,0;1/1:474:0,0,0,0,0,0,0;-1/1:576:0,-2,0,0,0,0,0;-1/1:606:0,-2,0,0,0,0,0;1/1:624:-2,-2,0,0,0,0,0;1/1:634:0,0,0,0,0,0,0;1/1:696:0,-2,0,0,0,0,0;-1/1:876:0,-2,0,0,0,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:1,-2,0,0,1,0,0;1/1:934:0,0,0,0,0,0,0"
  | 27 => laurent_polynomial% "-1/1:58:0,0,0,0,0,0,0;1/1:174:0,-1,0,0,0,1,0;-1/1:234:0,-1,0,0,0,1,0;1/1:264:0,-1,0,0,0,1,0;-1/1:278:0,0,0,0,0,0,0;-1/1:348:0,0,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;1/1:474:0,-1,0,0,0,1,0;1/1:618:0,0,0,0,0,0,0;-1/1:688:0,0,0,0,0,0,0;1/1:702:0,-2,0,0,0,0,0;-1/1:718:0,0,0,0,0,0,0;-1/1:864:1,0,0,0,1,0,0;-1/1:878:0,0,0,0,0,0,0;1/1:998:0,0,0,0,0,0,0"
  | 28 => laurent_polynomial% "1/1:174:-1,0,0,0,1,0,0;-1/1:186:1,0,0,0,1,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:348:-2,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:402:0,0,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;1/1:444:-1,0,0,0,1,0,0;1/1:474:-1,0,0,0,1,0,0;1/1:576:1,0,0,0,1,0,0;1/1:618:2,0,0,0,0,0,0;1/1:642:0,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:834:-1,0,0,0,1,0,0;1/1:864:-1,0,0,0,1,0,0"
  | 29 => laurent_polynomial% "1/1:264:0,-2,0,0,0,0,0;1/1:386:0,0,0,0,0,0,0;1/1:396:0,0,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;1/1:576:2,-2,0,0,0,0,0;1/1:618:0,-1,0,0,0,1,0;-1/1:624:0,-2,0,0,0,0,0;1/1:646:0,0,0,0,0,0,0;1/1:768:0,-1,0,0,0,1,0;1/1:796:0,0,0,0,0,0,0;-1/1:834:0,-2,0,0,0,0,0;1/1:864:0,-2,0,0,0,0,0;-1/1:876:0,0,0,0,0,0,0;-1/1:934:-2,0,0,0,0,0,0;1/1:992:-1,0,0,0,1,0,0;1/1:1016:0,0,0,0,0,0,0"
  | 30 => laurent_polynomial% "-1/1:52:-3,0,0,0,1,0,0;1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;-1/1:234:-2,-2,0,0,0,0,0;-1/1:234:0,0,0,0,0,0,0;1/1:332:-3,0,0,0,1,0,0;-1/1:348:-2,-1,0,0,0,1,0;-1/1:354:-1,-1,0,0,1,1,0;-1/1:398:-1,0,0,0,1,0,0;1/1:444:0,0,0,0,0,0,0;1/1:618:-2,-1,0,0,0,1,0;1/1:642:-1,-2,0,0,1,0,0;-1/1:702:-4,-1,0,0,0,1,0;1/1:702:0,-1,0,0,0,1,0;1/1:796:-2,0,0,0,0,0,0;1/1:876:-3,-1,0,0,1,1,0;1/1:888:-2,-1,0,0,0,1,0;-1/1:934:0,0,0,0,0,0,0;-1/1:936:-2,0,0,0,0,0,0"
  | 31 => laurent_polynomial% "1/1:162:1,-2,0,0,1,0,0;-1/1:264:0,-2,0,0,0,0,0;1/1:282:-1,0,0,0,1,0,0;-1/1:396:0,0,0,0,0,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:474:1,-1,0,0,1,1,0;1/1:474:2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;-1/1:576:2,-2,0,0,0,0,0;-1/1:606:0,0,0,0,0,0,0;-1/1:606:2,-2,0,0,0,0,0;1/1:624:0,-2,0,0,0,0,0;1/1:642:-2,-1,0,0,0,1,0;-1/1:702:-3,-2,0,0,1,0,0;1/1:834:0,-2,0,0,0,0,0;-1/1:864:0,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;1/1:876:-2,-2,0,0,2,0,0;-1/1:914:-2,0,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0;-1/1:1016:0,0,0,0,0,0,0;1/1:1016:0,0,0,0,2,0,0"
  | _ => []

}
certificate_batch {
compact_certificate def triTailPart30 (i : ℕ) : Poly :=
  match i with
  | 0 => laurent_polynomial% "-1/1:162:-2,-1,0,0,0,1,0;-1/1:174:-3,-1,0,0,1,1,0;-1/1:186:-2,-2,0,0,0,0,0;1/1:302:-1,0,0,0,1,0,0;1/1:348:-4,-1,0,0,0,1,0;-1/1:426:-1,-1,0,0,1,1,0;-1/1:432:-2,-1,0,0,0,1,0;1/1:444:1,-1,0,0,1,1,0;-1/1:576:-1,-1,0,0,1,1,0;-1/1:604:-2,0,0,0,0,0,0;1/1:618:-1,-2,0,0,1,0,0;-1/1:676:0,0,0,0,0,0,0;1/1:696:-1,-1,0,0,1,1,0;1/1:702:-2,-1,0,0,0,1,0;-1/1:834:0,-2,0,0,0,0,0;-1/1:876:-1,-1,0,0,1,1,0;-1/1:888:0,-1,0,0,2,1,0"
  | 1 => laurent_polynomial% "-1/1:116:0,0,0,0,0,0,0;1/1:162:1,-2,0,0,1,0,0;1/1:166:0,0,0,0,0,0,0;1/1:186:0,0,0,0,0,0,0;-1/1:216:0,0,0,0,0,0,0;-1/1:264:0,-2,0,0,0,0,0;1/1:348:0,-1,0,0,0,1,0;-1/1:426:-2,-2,0,0,0,0,0;-1/1:426:0,0,0,0,0,0,0;1/1:474:2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;-1/1:576:2,-2,0,0,0,0,0;-1/1:606:2,-2,0,0,0,0,0;1/1:624:0,-2,0,0,0,0,0;1/1:648:0,-1,0,0,0,1,0;1/1:834:0,-2,0,0,0,0,0;-1/1:864:-2,0,0,0,0,0,0;-1/1:864:0,-2,0,0,0,0,0;1/1:936:0,0,0,0,0,0,0;-1/1:1016:0,0,0,0,0,0,0"
  | 2 => laurent_polynomial% "-1/1:52:-2,0,0,0,0,0,0;-1/1:166:-1,0,0,0,1,0,0;1/1:172:-2,0,0,0,0,0,0;1/1:174:-1,-2,0,0,1,0,0;-1/1:234:0,-1,0,0,0,1,0;1/1:282:0,-2,0,0,0,0,0;1/1:332:-2,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:398:0,0,0,0,0,0,0;1/1:432:0,-2,0,0,0,0,0;-1/1:444:0,-1,0,0,0,1,0;1/1:618:0,0,0,0,0,0,0;1/1:642:0,-2,0,0,0,0,0;-1/1:718:0,0,0,0,0,0,0;1/1:768:0,0,0,0,0,0,0;-1/1:864:0,-1,0,0,0,1,0;1/1:888:0,0,0,0,0,0,0"
  | 3 => laurent_polynomial% "1/1:186:-2,-1,0,0,0,1,0;1/1:186:-1,0,0,0,1,0,0;-1/1:216:-2,-1,0,0,0,1,0;1/1:234:-1,-2,0,0,1,0,0;1/1:348:-1,-1,0,0,1,1,0;1/1:354:0,-1,0,0,0,1,0;1/1:398:0,0,0,0,0,0,0;-1/1:426:-2,-1,0,0,0,1,0;-1/1:432:-2,0,0,0,0,0,0;-1/1:444:1,0,0,0,1,0,0;1/1:474:0,-1,0,0,0,1,0;-1/1:576:-2,-1,0,0,0,1,0;-1/1:618:-1,-1,0,0,1,1,0;-1/1:618:0,0,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;-1/1:642:0,-2,0,0,0,0,0;1/1:702:-3,-1,0,0,1,1,0;1/1:702:-2,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;-1/1:876:-2,-1,0,0,2,1,0;-1/1:888:-1,-1,0,0,1,1,0;-1/1:888:0,0,0,0,0,0,0;1/1:888:0,0,0,0,2,0,0;1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0"
  | 4 => laurent_polynomial% "1/1:166:-3,0,0,0,1,0,0;-1/1:216:-1,-2,0,0,1,0,0;-1/1:234:-1,0,0,0,1,0,0;1/1:282:-1,-1,0,0,1,1,0;-1/1:332:-4,0,0,0,0,0,0;1/1:402:0,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-1/1:426:0,-1,0,0,0,1,0;-1/1:444:-1,0,0,0,1,0,0;1/1:474:1,-2,0,0,1,0,0;-1/1:576:0,-1,0,0,0,1,0;-1/1:606:0,-1,0,0,0,1,0;1/1:618:0,-2,0,0,0,0,0;1/1:696:0,-1,0,0,0,1,0;1/1:702:-1,-1,0,0,1,1,0;1/1:702:0,0,0,0,0,0,0;1/1:768:0,-2,0,0,0,0,0;-1/1:864:-1,0,0,0,1,0,0;-1/1:876:0,-1,0,0,0,1,0;1/1:936:0,-1,0,0,0,1,0"
  | 5 => laurent_polynomial% "-1/1:162:-1,-2,0,0,1,0,0;-1/1:174:-2,-2,0,0,2,0,0;1/1:216:-2,0,0,0,0,0,0;1/1:264:0,0,0,0,0,0,0;1/1:348:-3,-2,0,0,1,0,0;1/1:348:-2,-1,0,0,0,1,0;-1/1:408:-2,-1,0,0,0,1,0;1/1:426:-2,0,0,0,0,0,0;-1/1:426:0,-2,0,0,0,0,0;-1/1:432:-1,-2,0,0,1,0,0;-1/1:432:0,-1,0,0,0,1,0;1/1:444:2,-2,0,0,0,0,0;-1/1:474:-2,-2,0,0,0,0,0;-1/1:576:0,-2,0,0,0,0,0;-1/1:618:-2,-1,0,0,0,1,0;-1/1:618:-1,0,0,0,1,0,0;1/1:696:0,-2,0,0,0,0,0;1/1:702:-4,-1,0,0,0,1,0;1/1:702:-1,-2,0,0,1,0,0;-1/1:768:-1,0,0,0,1,0,0;1/1:864:-1,-1,0,0,1,1,0;-1/1:876:-3,-1,0,0,1,1,0;-1/1:876:0,-2,0,0,0,0,0;-1/1:888:1,-2,0,0,1,0,0;-1/1:986:-2,0,0,0,0,0,0"
  | 6 => laurent_polynomial% "-1/1:162:0,-1,0,0,2,1,0;-1/1:174:-1,-1,0,0,1,1,0;1/1:234:0,0,0,0,0,0,0;1/1:348:-2,-1,0,0,0,1,0;1/1:354:-1,-1,0,0,1,1,0;1/1:398:-1,0,0,0,1,0,0;1/1:426:0,-2,0,0,0,0,0;1/1:432:-1,-2,0,0,1,0,0;-1/1:474:-1,-1,0,0,1,1,0;1/1:606:1,-1,0,0,1,1,0;-1/1:618:-2,-1,0,0,0,1,0;-1/1:624:-1,-1,0,0,1,1,0;1/1:702:-4,-1,0,0,0,1,0;-1/1:702:0,-1,0,0,0,1,0;-1/1:794:0,0,0,0,0,0,0;-1/1:796:-2,0,0,0,0,0,0;-1/1:864:-2,-2,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0;-1/1:876:-3,-1,0,0,1,1,0;-1/1:888:-2,-1,0,0,0,1,0;1/1:934:0,0,0,0,0,0,0"
  | 7 => laurent_polynomial% "1/1:162:0,0,0,0,0,0,0;1/1:282:0,0,0,0,0,0,0;-1/1:332:0,0,0,0,0,0,0;1/1:396:0,-1,0,0,0,1,0;1/1:408:0,-2,0,0,0,0,0;-1/1:426:0,-1,0,0,0,1,0;1/1:432:0,0,0,0,0,0,0;1/1:444:2,-1,0,0,0,1,0;1/1:512:0,0,0,0,0,0,0;-1/1:576:0,-1,0,0,0,1,0;2/1:618:0,-2,0,0,0,0,0;1/1:696:0,-1,0,0,0,1,0;-1/1:702:-2,-2,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:768:0,-2,0,0,0,0,0;1/1:876:-1,-2,0,0,1,0,0;-1/1:876:0,-1,0,0,0,1,0;1/1:878:-2,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:1,-1,0,0,1,1,0;1/1:1016:1,0,0,0,1,0,0"
  | 8 => laurent_polynomial% "1/1:116:-2,0,0,0,0,0,0;-1/1:234:-2,-2,0,0,0,0,0;1/1:264:-2,-2,0,0,0,0,0;1/1:278:-1,0,0,0,1,0,0;-1/1:348:-2,-1,0,0,0,1,0;1/1:386:-2,0,0,0,0,0,0;1/1:402:-1,-2,0,0,1,0,0;-1/1:444:-2,-2,0,0,0,0,0;1/1:444:0,0,0,0,0,0,0;1/1:444:2,-2,0,0,0,0,0;-1/1:474:0,0,0,0,0,0,0;1/1:618:-2,-1,0,0,0,1,0;1/1:646:-2,0,0,0,0,0,0;-1/1:664:0,0,0,0,0,0,0;-1/1:676:-2,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:796:-2,0,0,0,0,0,0;-1/1:834:-2,-2,0,0,0,0,0;-1/1:834:-1,-1,0,0,1,1,0;-1/1:876:-2,0,0,0,0,0,0;-1/1:888:-1,0,0,0,1,0,0;-1/1:888:1,-2,0,0,1,0,0;-1/1:934:-4,0,0,0,0,0,0;-1/1:936:-2,0,0,0,0,0,0;1/1:992:-3,0,0,0,1,0,0;1/1:1016:-2,0,0,0,0,0,0"
  | 9 => laurent_polynomial% "-1/1:52:0,0,0,0,0,0,0;1/1:62:0,0,0,0,0,0,0;-1/1:162:0,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-1/1:174:-1,0,0,0,1,0,0;1/1:186:1,0,0,0,1,0,0;-1/1:216:0,-1,0,0,0,1,0;1/1:332:0,0,0,0,0,0,0;1/1:348:-2,0,0,0,0,0,0;-1/1:348:0,-2,0,0,0,0,0;-1/1:396:0,-1,0,0,0,1,0;-1/1:426:0,-1,0,0,0,1,0;-2/1:432:0,0,0,0,0,0,0;1/1:474:2,-1,0,0,0,1,0;-1/1:576:0,-1,0,0,0,1,0;-1/1:606:0,-1,0,0,0,1,0;-1/1:618:2,0,0,0,0,0,0;2/1:702:0,0,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;-1/1:876:0,-1,0,0,0,1,0;-1/1:878:-2,0,0,0,0,0,0;1/1:902:0,0,0,0,0,0,0;1/1:936:0,-1,0,0,0,1,0;1/1:992:0,0,0,0,0,0,0"
  | 10 => laurent_polynomial% "1/1:174:0,0,0,0,0,0,0;-1/1:244:0,0,0,0,0,0,0;1/1:264:0,0,0,0,0,0,0;1/1:282:-1,-2,0,0,1,0,0;-1/1:282:0,-1,0,0,0,1,0;1/1:402:0,-1,0,0,0,1,0;-1/1:426:0,-2,0,0,0,0,0;-1/1:432:0,-1,0,0,0,1,0;-1/1:444:-1,-1,0,0,1,1,0;1/1:444:0,0,0,0,0,0,0;1/1:474:0,0,0,0,0,0,0;-1/1:576:0,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;-1/1:606:0,-2,0,0,0,0,0;1/1:634:0,0,0,0,0,0,0;-1/1:646:-2,0,0,0,0,0,0;-1/1:694:0,0,0,0,0,0,0;1/1:702:0,-1,0,0,0,1,0;1/1:794:0,0,0,0,0,0,0;-1/1:834:0,0,0,0,0,0,0;1/1:848:-1,0,0,0,1,0,0;1/1:864:0,0,0,0,0,0,0;-1/1:876:0,-2,0,0,0,0,0;1/1:888:-2,-1,0,0,0,1,0;-1/1:914:0,0,0,0,0,0,0;1/1:936:0,-2,0,0,0,0,0"
  | 11 => laurent_polynomial% "-1/1:162:-1,0,0,0,1,0,0;-1/1:162:1,-2,0,0,1,0,0;-1/1:174:-3,-1,0,0,1,1,0;-1/1:174:0,-2,0,0,0,0,0;1/1:186:-1,-1,0,0,1,1,0;-1/1:186:0,0,0,0,0,0,0;1/1:216:0,0,0,0,0,0,0;1/1:264:-2,0,0,0,0,0,0;-1/1:282:-1,0,0,0,1,0,0;1/1:348:-4,-1,0,0,0,1,0;1/1:348:-1,-2,0,0,1,0,0;1/1:354:0,-2,0,0,0,0,0;1/1:396:-2,-2,0,0,0,0,0;1/1:426:0,0,0,0,0,0,0;-1/1:432:-2,-1,0,0,0,1,0;-1/1:432:-1,0,0,0,1,0,0;-1/1:474:0,-2,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;1/1:576:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;1/1:606:-2,-2,0,0,0,0,0;1/1:606:0,0,0,0,0,0,0;1/1:606:2,-2,0,0,0,0,0;-1/1:618:-1,-2,0,0,1,0,0;-1/1:618:0,-1,0,0,0,1,0;-1/1:624:0,-2,0,0,0,0,0;1/1:664:-2,0,0,0,0,0,0;1/1:702:-3,-2,0,0,1,0,0;1/1:702:-2,-1,0,0,0,1,0;1/1:864:-2,0,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,2,0,0;1/1:884:-2,0,0,0,0,0,0;-1/1:888:-1,-2,0,0,1,0,0;-1/1:914:-2,0,0,0,0,0,0;-1/1:936:0,0,0,0,0,0,0"
  | 12 => laurent_polynomial% "1/1:52:-2,0,0,0,0,0,0;1/1:58:0,0,0,0,0,0,0;1/1:162:0,-2,0,0,0,0,0;-1/1:172:-2,0,0,0,0,0,0;1/1:174:-1,-2,0,0,1,0,0;-1/1:174:0,-1,0,0,0,1,0;1/1:234:0,-1,0,0,0,1,0;1/1:278:0,0,0,0,0,0,0;-1/1:282:0,-2,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;2/1:348:0,0,0,0,0,0,0;1/1:432:0,-2,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;1/1:444:0,-1,0,0,0,1,0;-1/1:474:0,-1,0,0,0,1,0;1/1:576:2,-1,0,0,0,1,0;-1/1:618:0,0,0,0,0,0,0;-1/1:624:0,-1,0,0,0,1,0;1/1:702:-2,0,0,0,0,0,0;-2/1:702:0,-2,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;1/1:768:0,0,0,0,0,0,0;-1/1:834:0,-1,0,0,0,1,0;-1/1:838:0,0,0,0,0,0,0;-1/1:848:0,0,0,0,0,0,0;1/1:864:0,-1,0,0,0,1,0;1/1:864:1,0,0,0,1,0,0;-1/1:876:-1,0,0,0,1,0,0;-1/1:888:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0"
  | 13 => laurent_polynomial% "-1/1:58:-1,0,0,0,1,0,0;1/1:116:-2,0,0,0,0,0,0;1/1:174:-1,-1,0,0,1,1,0;1/1:174:0,0,0,0,0,0,0;1/1:186:-2,0,0,0,0,0,0;1/1:186:0,-2,0,0,0,0,0;1/1:234:0,0,0,0,0,0,0;-1/1:244:0,0,0,0,0,0,0;1/1:264:0,0,0,0,0,0,0;-1/1:282:0,-1,0,0,0,1,0;-1/1:348:-2,-1,0,0,0,1,0;-1/1:426:0,-2,0,0,0,0,0;1/1:444:0,0,0,0,0,0,0;1/1:444:2,-2,0,0,0,0,0;1/1:474:0,0,0,0,0,0,0;-1/1:576:0,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;-1/1:606:0,-2,0,0,0,0,0;1/1:624:-2,-2,0,0,0,0,0;1/1:634:0,0,0,0,0,0,0;-1/1:664:0,0,0,0,0,0,0;1/1:696:0,-2,0,0,0,0,0;-1/1:702:0,-1,0,0,0,1,0;1/1:864:0,0,0,0,0,0,0;-1/1:876:0,-2,0,0,0,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:1,-2,0,0,1,0,0;1/1:934:0,0,0,0,0,0,0;1/1:936:0,-2,0,0,0,0,0"
  | 14 => laurent_polynomial% "-1/1:162:1,0,0,0,1,0,0;1/1:264:-2,-2,0,0,0,0,0;1/1:264:-1,-1,0,0,1,1,0;1/1:264:0,0,0,0,0,0,0;-1/1:348:-1,0,0,0,1,0,0;1/1:386:-2,0,0,0,0,0,0;1/1:396:-2,0,0,0,0,0,0;1/1:396:0,-2,0,0,0,0,0;1/1:408:-1,0,0,0,1,0,0;1/1:426:-2,0,0,0,0,0,0;1/1:432:1,0,0,0,1,0,0;1/1:474:-1,-1,0,0,1,1,0;-1/1:474:0,0,0,0,0,0,0;1/1:576:-2,0,0,0,0,0,0;1/1:576:0,-2,0,0,0,0,0;1/1:576:2,0,0,0,0,0,0;-1/1:604:0,0,0,0,0,0,0;1/1:606:-2,0,0,0,0,0,0;1/1:606:0,-2,0,0,0,0,0;1/1:606:2,0,0,0,0,0,0;1/1:618:-1,0,0,0,1,0,0;-1/1:624:-2,-2,0,0,0,0,0;-1/1:624:0,0,0,0,0,0,0;1/1:646:-2,0,0,0,0,0,0;-1/1:696:-2,0,0,0,0,0,0;-1/1:718:-1,0,0,0,1,0,0;1/1:796:-2,0,0,0,0,0,0;-1/1:834:-2,-2,0,0,0,0,0;-1/1:834:0,0,0,0,0,0,0;1/1:864:-2,-2,0,0,0,0,0;1/1:864:0,0,0,0,0,0,0;-1/1:864:0,0,0,0,2,0,0;1/1:884:0,0,0,0,0,0,0;-1/1:934:-4,0,0,0,0,0,0;-1/1:936:-2,0,0,0,0,0,0;1/1:992:-3,0,0,0,1,0,0;1/1:998:-1,0,0,0,1,0,0;1/1:1016:-2,0,0,0,0,0,0"
  | 15 => laurent_polynomial% "-1/1:62:-2,0,0,0,0,0,0;-1/1:116:-1,0,0,0,1,0,0;1/1:162:-2,0,0,0,0,0,0;1/1:174:-3,0,0,0,1,0,0;1/1:186:-2,-1,0,0,0,1,0;1/1:234:-1,-2,0,0,1,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:278:0,0,0,0,0,0,0;-1/1:348:-4,0,0,0,0,0,0;1/1:348:-1,-1,0,0,1,1,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:402:0,-2,0,0,0,0,0;1/1:432:-2,0,0,0,0,0,0;1/1:444:-1,-2,0,0,1,0,0;-1/1:444:1,0,0,0,1,0,0;1/1:474:1,0,0,0,1,0,0;-1/1:618:-1,-1,0,0,1,1,0;-1/1:646:-1,0,0,0,1,0,0;1/1:676:-1,0,0,0,1,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:706:-1,0,0,0,1,0,0;-1/1:796:-1,0,0,0,1,0,0;1/1:834:-1,-2,0,0,1,0,0;1/1:834:0,-1,0,0,0,1,0;1/1:876:-1,0,0,0,1,0,0;1/1:888:0,0,0,0,2,0,0;1/1:934:-3,0,0,0,1,0,0;1/1:936:-1,0,0,0,1,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:1016:-1,0,0,0,1,0,0"
  | 16 => laurent_polynomial% "-1/1:62:0,0,0,0,0,0,0;-1/1:162:0,0,0,0,2,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:282:-1,-1,0,0,1,1,0;1/1:282:0,0,0,0,0,0,0;-1/1:348:0,-2,0,0,0,0,0;1/1:396:-1,-2,0,0,1,0,0;1/1:432:0,0,0,0,0,0,0;1/1:444:-1,0,0,0,1,0,0;-1/1:474:1,-2,0,0,1,0,0;-1/1:512:0,0,0,0,0,0,0;1/1:576:1,0,0,0,1,0,0;1/1:606:1,0,0,0,1,0,0;1/1:618:0,-2,0,0,0,0,0;-1/1:624:-1,0,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;1/1:642:-1,-1,0,0,1,1,0;-1/1:694:-1,0,0,0,1,0,0;-1/1:702:-2,-2,0,0,0,0,0;1/1:712:0,0,0,0,0,0,0;1/1:794:-1,0,0,0,1,0,0;-1/1:834:-1,0,0,0,1,0,0;1/1:848:-2,0,0,0,0,0,0;1/1:864:-1,0,0,0,1,0,0;1/1:888:0,-2,0,0,0,0,0;-1/1:914:-1,0,0,0,1,0,0;-1/1:936:0,-1,0,0,0,1,0"
  | 17 => laurent_polynomial% "-1/1:62:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;1/1:282:-2,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:396:-1,0,0,0,1,0,0;-1/1:408:0,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;1/1:432:-2,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:474:1,0,0,0,1,0,0;-1/1:512:-2,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:1,-2,0,0,1,0,0;-1/1:606:-1,0,0,0,1,0,0;1/1:618:-2,-2,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;1/1:624:-1,-2,0,0,1,0,0;-1/1:646:-1,0,0,0,1,0,0;1/1:696:-1,0,0,0,1,0,0;-1/1:702:-4,-2,0,0,0,0,0;1/1:712:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;1/1:876:-3,-2,0,0,1,0,0;1/1:888:-2,-2,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0"
  | 18 => laurent_polynomial% "1/1:62:-1,0,0,0,1,0,0;1/1:162:-1,0,0,0,1,0,0;1/1:244:-2,0,0,0,0,0,0;-1/1:264:-2,0,0,0,0,0,0;1/1:264:0,-2,0,0,0,0,0;1/1:282:-2,-1,0,0,0,1,0;-1/1:282:-1,0,0,0,1,0,0;1/1:348:-1,-2,0,0,1,0,0;1/1:386:0,0,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;1/1:396:0,0,0,0,0,0,0;1/1:426:0,0,0,0,0,0,0;-1/1:432:-1,0,0,0,1,0,0;-1/1:444:-2,0,0,0,0,0,0;1/1:474:0,-2,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;1/1:512:-1,0,0,0,1,0,0;1/1:576:2,-2,0,0,0,0,0;-1/1:618:-1,-2,0,0,1,0,0;1/1:624:-2,0,0,0,0,0,0;-1/1:624:0,-2,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;-1/1:642:-2,-1,0,0,0,1,0;1/1:646:0,0,0,0,0,0,0;1/1:694:-2,0,0,0,0,0,0;-1/1:696:0,0,0,0,0,0,0;1/1:702:-3,-2,0,0,1,0,0;-1/1:712:-1,0,0,0,1,0,0;-1/1:794:-2,0,0,0,0,0,0;1/1:796:0,0,0,0,0,0,0;1/1:834:-2,0,0,0,0,0,0;-1/1:834:0,-2,0,0,0,0,0;-1/1:864:-2,0,0,0,0,0,0;1/1:864:0,-2,0,0,0,0,0;1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,2,0,0;-1/1:888:-1,-2,0,0,1,0,0;1/1:914:-2,0,0,0,0,0,0;-1/1:934:-2,0,0,0,0,0,0;1/1:936:-1,-1,0,0,1,1,0;-1/1:936:0,0,0,0,0,0,0;1/1:992:-1,0,0,0,1,0,0;1/1:1016:0,0,0,0,0,0,0"
  | 19 => laurent_polynomial% "1/1:58:-3,0,0,0,1,0,0;1/1:62:-1,0,0,0,1,0,0;-1/1:116:-4,0,0,0,0,0,0;1/1:116:0,0,0,0,0,0,0;-1/1:162:-1,0,0,0,1,0,0;-1/1:174:-3,-1,0,0,1,1,0;-1/1:174:-2,0,0,0,0,0,0;-1/1:174:-2,0,0,0,2,0,0;-1/1:186:-4,0,0,0,0,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:234:-2,0,0,0,0,0,0;-1/1:234:0,-2,0,0,0,0,0;1/1:244:-2,0,0,0,0,0,0;1/1:264:0,-2,0,0,0,0,0;1/1:282:-2,-1,0,0,0,1,0;1/1:348:-4,-1,0,0,0,1,0;1/1:348:-3,0,0,0,1,0,0;-1/1:348:0,-1,0,0,0,1,0;1/1:386:0,0,0,0,0,0,0;-1/1:432:-1,0,0,0,1,0,0;-1/1:444:-2,0,0,0,0,0,0;-1/1:444:0,-2,0,0,0,0,0;1/1:444:2,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:2,0,0,0,0,0,0;-1/1:576:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;1/1:606:-2,-2,0,0,0,0,0;-1/1:624:-4,-2,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;1/1:646:0,0,0,0,0,0,0;1/1:664:-2,0,0,0,0,0,0;-1/1:676:0,0,0,0,0,0,0;1/1:702:-2,-1,0,0,0,1,0;1/1:702:-1,0,0,0,1,0,0;1/1:706:0,0,0,0,0,0,0;1/1:796:0,0,0,0,0,0,0;-1/1:834:0,-2,0,0,0,0,0;-1/1:864:-2,0,0,0,0,0,0;-1/1:876:0,0,0,0,0,0,0;1/1:884:-2,0,0,0,0,0,0;-1/1:888:1,0,0,0,1,0,0;-2/1:934:-2,0,0,0,0,0,0;-1/1:936:-2,-2,0,0,0,0,0;-1/1:936:0,0,0,0,0,0,0;1/1:992:-1,0,0,0,1,0,0;1/1:1016:0,0,0,0,0,0,0"
  | 20 => laurent_polynomial% "1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:186:-3,0,0,0,1,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:278:-2,0,0,0,0,0,0;-1/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;1/1:398:-2,0,0,0,0,0,0;1/1:402:-2,-2,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-1/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:618:-2,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:642:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;1/1:696:-1,-2,0,0,1,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:838:-2,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0"
  | 21 => laurent_polynomial% "-1/1:52:-3,0,0,0,1,0,0;-1/1:116:-2,0,0,0,0,0,0;1/1:162:-1,-2,0,0,1,0,0;1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;1/1:172:-3,0,0,0,1,0,0;1/1:174:-2,-2,0,0,0,0,0;-1/1:174:0,0,0,0,0,0,0;-1/1:216:-2,0,0,0,0,0,0;-1/1:234:-1,-1,0,0,1,1,0;-1/1:234:0,0,0,0,0,0,0;1/1:244:0,0,0,0,0,0,0;-1/1:264:0,0,0,0,0,0,0;-1/1:278:-1,0,0,0,1,0,0;1/1:282:-1,-2,0,0,1,0,0;1/1:282:0,-1,0,0,0,1,0;1/1:332:-3,0,0,0,1,0,0;-1/1:354:-2,-2,0,0,0,0,0;1/1:354:0,0,0,0,0,0,0;-1/1:398:-1,0,0,0,1,0,0;-1/1:402:-1,-2,0,0,1,0,0;-1/1:426:-4,-2,0,0,0,0,0;-1/1:426:-2,0,0,0,0,0,0;1/1:426:0,-2,0,0,0,0,0;1/1:432:-1,-2,0,0,1,0,0;1/1:432:0,-1,0,0,0,1,0;1/1:444:-2,-2,0,0,0,0,0;-1/1:444:-1,-1,0,0,1,1,0;-1/1:444:0,0,0,0,0,0,0;-1/1:444:2,-2,0,0,0,0,0;1/1:474:-2,-2,0,0,0,0,0;-1/1:576:-2,0,0,0,0,0,0;1/1:576:0,-2,0,0,0,0,0;-1/1:576:1,-1,0,0,1,1,0;-1/1:576:2,0,0,0,0,0,0;1/1:618:-1,0,0,0,1,0,0;-1/1:634:0,0,0,0,0,0,0;1/1:642:-1,-2,0,0,1,0,0;1/1:664:0,0,0,0,0,0,0;-1/1:696:0,-2,0,0,0,0,0;-1/1:718:-1,0,0,0,1,0,0;1/1:834:-1,-1,0,0,1,1,0;1/1:838:-1,0,0,0,1,0,0;-1/1:864:-4,0,0,0,0,0,0;-1/1:864:-1,-1,0,0,1,1,0;-1/1:864:0,0,0,0,0,0,0;1/1:876:0,-2,0,0,0,0,0;1/1:884:0,0,0,0,0,0,0;1/1:888:-1,0,0,0,1,0,0;1/1:888:1,-2,0,0,1,0,0;-1/1:934:0,0,0,0,0,0,0;1/1:936:-2,0,0,0,0,0,0;-1/1:936:0,-2,0,0,0,0,0;-1/1:1016:-2,0,0,0,0,0,0"
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | 26 => []
  | 27 => []
  | 28 => []
  | 29 => []
  | 30 => []
  | 31 => []
  | _ => []
compact_certificate def triTailPart31 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => []
  | 21 => []
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | 26 => []
  | 27 => []
  | 28 => []
  | 29 => []
  | 30 => []
  | 31 => []
  | _ => []

compact_certificate def triTailPart32 (i : ℕ) : Poly :=
  match i with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []
  | 10 => []
  | 11 => []
  | 12 => []
  | 13 => []
  | 14 => []
  | 15 => []
  | 16 => []
  | 17 => []
  | 18 => []
  | 19 => []
  | 20 => []
  | 21 => []
  | 22 => []
  | 23 => []
  | 24 => []
  | 25 => []
  | _ => []

end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentKernelDataV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate noncomputable def normal (i : ℕ) : Poly :=
  match i/32 with
  | 0 => normalPart0 (i%32)
  | 1 => normalPart1 (i%32)
  | 2 => normalPart2 (i%32)
  | 3 => normalPart3 (i%32)
  | 4 => normalPart4 (i%32)
  | 5 => normalPart5 (i%32)
  | 6 => normalPart6 (i%32)
  | 7 => normalPart7 (i%32)
  | 8 => normalPart8 (i%32)
  | 9 => normalPart9 (i%32)
  | 10 => normalPart10 (i%32)
  | 11 => normalPart11 (i%32)
  | 12 => normalPart12 (i%32)
  | 13 => normalPart13 (i%32)
  | 14 => normalPart14 (i%32)
  | 15 => normalPart15 (i%32)
  | 16 => normalPart16 (i%32)
  | 17 => normalPart17 (i%32)
  | 18 => normalPart18 (i%32)
  | 19 => normalPart19 (i%32)
  | 20 => normalPart20 (i%32)
  | 21 => normalPart21 (i%32)
  | 22 => normalPart22 (i%32)
  | 23 => normalPart23 (i%32)
  | 24 => normalPart24 (i%32)
  | 25 => normalPart25 (i%32)
  | 26 => normalPart26 (i%32)
  | 27 => normalPart27 (i%32)
  | 28 => normalPart28 (i%32)
  | 29 => normalPart29 (i%32)
  | 30 => normalPart30 (i%32)
  | 31 => normalPart31 (i%32)
  | 32 => normalPart32 (i%32)
  | _ => []

compact_certificate noncomputable def operations (i : ℕ) : Poly :=
  match i/32 with
  | 0 => operationsPart0 (i%32)
  | 1 => operationsPart1 (i%32)
  | 2 => operationsPart2 (i%32)
  | 3 => operationsPart3 (i%32)
  | 4 => operationsPart4 (i%32)
  | 5 => operationsPart5 (i%32)
  | 6 => operationsPart6 (i%32)
  | 7 => operationsPart7 (i%32)
  | 8 => operationsPart8 (i%32)
  | 9 => operationsPart9 (i%32)
  | 10 => operationsPart10 (i%32)
  | 11 => operationsPart11 (i%32)
  | 12 => operationsPart12 (i%32)
  | 13 => operationsPart13 (i%32)
  | 14 => operationsPart14 (i%32)
  | 15 => operationsPart15 (i%32)
  | 16 => operationsPart16 (i%32)
  | 17 => operationsPart17 (i%32)
  | 18 => operationsPart18 (i%32)
  | 19 => operationsPart19 (i%32)
  | 20 => operationsPart20 (i%32)
  | 21 => operationsPart21 (i%32)
  | 22 => operationsPart22 (i%32)
  | 23 => operationsPart23 (i%32)
  | 24 => operationsPart24 (i%32)
  | 25 => operationsPart25 (i%32)
  | 26 => operationsPart26 (i%32)
  | 27 => operationsPart27 (i%32)
  | 28 => operationsPart28 (i%32)
  | 29 => operationsPart29 (i%32)
  | 30 => operationsPart30 (i%32)
  | _ => []

compact_certificate noncomputable def triTail (i : ℕ) : Poly :=
  match i/32 with
  | 0 => triTailPart0 (i%32)
  | 1 => triTailPart1 (i%32)
  | 2 => triTailPart2 (i%32)
  | 3 => triTailPart3 (i%32)
  | 4 => triTailPart4 (i%32)
  | 5 => triTailPart5 (i%32)
  | 6 => triTailPart6 (i%32)
  | 7 => triTailPart7 (i%32)
  | 8 => triTailPart8 (i%32)
  | 9 => triTailPart9 (i%32)
  | 10 => triTailPart10 (i%32)
  | 11 => triTailPart11 (i%32)
  | 12 => triTailPart12 (i%32)
  | 13 => triTailPart13 (i%32)
  | 14 => triTailPart14 (i%32)
  | 15 => triTailPart15 (i%32)
  | 16 => triTailPart16 (i%32)
  | 17 => triTailPart17 (i%32)
  | 18 => triTailPart18 (i%32)
  | 19 => triTailPart19 (i%32)
  | 20 => triTailPart20 (i%32)
  | 21 => triTailPart21 (i%32)
  | 22 => triTailPart22 (i%32)
  | 23 => triTailPart23 (i%32)
  | 24 => triTailPart24 (i%32)
  | 25 => triTailPart25 (i%32)
  | 26 => triTailPart26 (i%32)
  | 27 => triTailPart27 (i%32)
  | 28 => triTailPart28 (i%32)
  | 29 => triTailPart29 (i%32)
  | 30 => triTailPart30 (i%32)
  | 31 => triTailPart31 (i%32)
  | 32 => triTailPart32 (i%32)
  | _ => []

compact_certificate noncomputable def coordinates : List ℕ := [546,0,525,550,1,2,3,4,6,7,12,14,528,21,28,42,532,84,548,966,87,39,1008,504,543,1036,1029,518,969,963,500,522,1043,524,526,1022,1038,81,1011,502,507,1044,1046,1047,1048,1049,35,840,560,960,10,90,210,540,15,490,85,40,1035,965,1015,510,1010,1040,49,150,756,77,514,1007,56,24,511,567,882,1000,1033,967,519,46,531,994,483,168,539,50,1026,83,1004,406,102,63,534,350,975,9,924,588,88,1032,22,1006,700,18,126,987,462,962,75,516,1028,44,1041,182,486,13,868,564,36,875,252,972,547,91,506,175,798,544,959,1014,78,503,72,651,1012,156,231,492,777,273,399,978,38,894,1039,672,552,952,450,41,86,501,322,29,602,66,336,25,529,82,497,1002,1023,686,100,609,938,513,16,693,954,508,343,434,1024,427,784,259,903,574,300,600,98,378,549,964,1009,498,728,1021,196,825,675,850,224,517,308,93,658,70,45,420,980,945,630,545,5,20,30,105,970,1005,530,520,1020,1030,80,505,1045,535,735,140,990,385,770,555,480,280,570,495,910,315,60,515,665,120,455,245,870,170,180,805,595,930,720,370,880,270,795,112,537,950,441,1034,861,54,742,957,48,553,714,968,1025,27,364,294,973,900,1001,43,536,690,340,750,147,476,400,357,542,96,707,330,680,780,360,710,154,33,11,108,581,1018,610,615,616,26,826,533,200,575,625,679,695,345,705,355,189,996,819,558,132,217,225,854,644,948,375,725,161,800,301,255,275,833,889,469,32,8,527,925,413,435,440,475,942,1042,521,523,392,812,51,623,203,721,287,917,582,931,371,791,266,896,1017,325,133,468,763,238,999,448,984,650,250,749,637,847,119,329,125,775,425,918,701,349,352,698,704,346,645,195,230,190,240,390,465,165,285,135,176,874,318,312,130,290,460,380,538,541,19,23,561,565,566,568,569,573,204,579,585,591,603,855,657,765,185,405,745,243,771,249,251,253,257,783,785,261,787,263,789,265,267,793,797,799,801,279,807,915,305,865,885,393,447,459,471,846,477,481,482,484,485,489,1027,1031,982,509,353,356,358,359,362,590,740,760,430,260,790,820,145,856,310,872,173,877,178,194,205,860,620,920,670,338,341,692,344,347,288,295,335,762,660,155,895,215,415,220,830,890,160,940,110,738,732,114,306,228,222,17,551,554,557,563,571,597,324,607,608,611,612,613,372,621,627,633,117,123,127,129,655,131,659,661,137,663,141,759,237,241,767,779,781,269,271,283,809,813,835,909,387,913,389,391,919,395,921,923,927,933,417,423,429,678,437,438,439,442,443,726,453,993,479,487,491,493,496,499,1037,361,715,716,368,374,377,379,744,752,404,755,95,115,118,164,866,169,871,179,181,184,886,232,235,605,635,995,296,298,671,323,326,682,683,334,685,689,684,138,276,912,366,292,758,774,198,852,211,209,212,208,214,206,636,414,445,815,456,594,320,730,106,314,985,65,258,792,816,654,31,559,37,47,61,587,589,67,593,71,601,79,955,89,619,97,109,113,647,653,139,667,143,669,151,681,687,691,697,873,699,351,177,703,717,193,719,197,199,741,743,221,223,751,229,761,239,769,247,773,277,803,281,811,293,299,827,303,829,307,309,311,313,317,319,321,853,331,857,333,863,709,736,887,363,367,369,381,907,383,911,397,403,407,409,937,941,943,419,421,947,949,953,431,961,971,449,451,979,457,983,461,463,989,991,467,997,473,1003,1013,1019,376,382,748,412,422,428,446,808,128,836,148,862,167,883,188,202,584,236,242,248,254,628,988,652,668,226,928,304,327,122,57,246,219,201,828,822,905,470,384,142,908,74,556,596,454,55,583,73,935,99,845,640,641,869,171,879,881,711,727,291,821,373,401,722,94,452,124,158,316,832,134,892,916,662,256,268,922,674,328,272,746,152,814,614,632,639,494,213,207,342,708,786,159,946,617,713,729,837,831,339,104,433,764,418,824,586,466,424,286,656,218,904,146,388,626,804,666,906,598,818,121,673,951,187,723,757,849,747,897,929,782,788,638,436,144,192,858,153,157,739,893,956,107,724,92,472,844,394,111,939,823,337,734,891,976,592,867,578,843,901,464,233,284,101,776,149,227,478,733,262,411,416,649,981,458,932,163,944,622,562,898,69,817,977,572,488,802,926,958,183,274,76,842,753,974,136,64,34,778,297,806,59,841,851,766,68,643,677,859,899,302,839,772,599,191,878,754,289,103,737,53,631,731,577,629,52,58,62,116,162,166,172,174,186,216,234,244,264,278,282,332,348,354,365,386,396,398,402,408,410,426,432,444,474,512,576,580,604,606,618,624,634,642,646,648,664,676,688,694,696,702,706,712,718,768,794,796,810,834,838,848,864,876,884,888,902,914,934,936,986,992,998,1016]
compact_certificate noncomputable def coordinate (i : ℕ) : ℕ := coordinates.getD i 0

compact_certificate noncomputable def positions : List ℕ := [1,4,5,6,7,206,8,9,327,95,50,288,10,115,11,54,168,507,103,398,207,13,100,399,71,157,295,263,14,153,208,646,326,287,954,46,118,648,142,21,57,149,15,269,111,200,79,649,258,64,85,340,982,977,255,802,70,787,983,958,232,650,984,91,953,641,155,653,962,938,199,655,132,804,798,108,948,67,130,657,216,37,159,87,17,56,150,20,98,659,51,123,901,197,821,588,279,661,182,806,164,920,90,975,857,209,638,899,289,662,500,905,249,663,503,589,985,524,590,366,235,877,786,525,823,368,104,526,765,527,392,529,310,354,827,387,952,532,615,666,221,534,796,668,891,468,869,274,767,922,65,670,838,894,286,491,135,895,824,849,498,318,986,933,591,385,987,769,83,593,239,811,988,472,989,125,388,678,474,595,240,596,113,946,597,414,990,880,771,306,381,971,892,681,475,379,190,683,622,684,298,790,772,342,406,476,629,845,627,625,52,624,626,844,628,493,991,311,867,789,495,687,506,688,194,312,782,923,505,690,380,136,599,918,992,600,774,536,357,692,382,537,775,417,993,237,788,694,776,419,362,420,120,421,777,321,831,422,642,177,465,425,926,427,994,429,350,430,832,541,247,542,836,139,947,322,616,696,995,435,227,698,996,543,919,386,865,344,486,974,393,816,619,700,265,487,604,956,605,701,180,320,967,703,784,438,504,705,196,706,470,707,391,708,639,231,825,709,390,710,636,711,152,607,514,353,608,785,835,367,281,713,997,715,611,488,156,908,481,856,272,482,846,172,484,303,377,485,998,373,93,677,374,456,999,305,457,277,458,459,284,577,460,720,264,1000,618,721,580,722,245,348,520,818,581,316,757,582,183,583,395,723,758,725,795,223,1001,548,870,550,383,551,338,441,904,553,1002,727,1003,140,276,819,1004,728,586,415,89,729,1005,730,1006,927,760,330,631,494,928,558,860,734,201,735,761,559,864,370,1007,175,762,560,464,739,1008,858,173,331,890,562,563,564,332,252,565,566,1009,632,763,442,359,742,148,743,822,568,801,236,634,745,931,443,394,747,106,748,917,384,863,751,355,325,794,444,902,753,1010,333,275,446,924,570,226,447,448,82,449,450,114,571,942,451,55,572,137,573,843,229,574,160,187,575,30,151,39,131,23,217,124,40,171,455,61,72,1011,167,68,233,109,195,27,78,213,336,31,337,33,2,34,328,12,158,212,80,16,297,92,219,270,250,396,84,53,397,278,24,127,205,0,122,18,184,3,508,146,259,509,225,799,510,309,647,48,400,936,511,117,401,402,73,403,404,228,512,941,405,179,299,1012,980,914,407,1013,290,346,803,773,408,862,651,97,652,461,409,912,654,635,242,800,513,875,970,181,656,154,410,1014,601,1015,515,516,165,292,517,518,519,840,293,294,851,1016,660,478,521,935,341,1017,300,871,522,778,981,204,978,841,523,1018,602,630,364,889,842,808,809,1019,963,314,378,1020,664,1021,929,361,133,780,665,645,528,866,412,198,530,490,531,830,533,1022,234,873,667,781,669,480,606,145,878,834,192,1023,964,561,301,282,671,609,610,614,612,163,672,1024,613,271,673,483,169,1025,302,1026,674,375,676,102,372,1027,679,376,304,1028,280,847,717,285,814,1029,852,260,578,579,680,1030,682,244,343,820,881,900,317,567,815,188,853,637,979,502,925,909,220,718,976,501,896,462,685,256,686,584,416,837,884,759,363,273,689,585,950,973,587,66,882,620,535,463,691,489,356,859,413,961,538,1031,693,224,418,969,695,621,369,921,138,955,539,283,540,887,423,176,424,848,426,888,428,466,349,643,431,1032,248,1033,432,126,433,319,434,943,697,872,241,957,436,764,544,1034,699,339,545,839,633,644,939,876,308,467,817,792,907,861,191,296,702,791,704,496,855,826,323,1035,546,766,854,1036,968,47,959,949,915,903,807,445,365,1037,883,193,960,623,712,313,411,469,714,893,965,477,254,768,716,1038,439,592,913,116,810,238,594,471,675,389,119,1039,473,972,812,246,813,74,770,1040,440,598,719,1041,324,497,910,828,897,143,492,351,885,937,966,267,916,1042,178,868,793,874,724,797,547,230,726,617,549,1043,437,829,345,371,552,479,554,833,555,96,329,944,556,783,886,243,347,932,557,1044,805,1045,731,166,906,499,732,334,733,934,203,850,736,315,737,251,879,147,738,170,658,898,257,945,128,49,740,107,29,185,59,19,77,261,28,210,741,121,266,951,94,911,940,141,744,202,930,454,746,360,640,1046,105,779,749,222,750,1047,569,81,603,307,752,1048,358,75,268,161,754,88,211,101,69,22,186,62,38,134,755,129,60,1049,352,291,756,214,189,35,162,174,262,86,452,110,26,215,453,99,76,253,58,25,576,36,144,63,112,335,32,41,218,42,43,44,45]
compact_certificate noncomputable def position (i : ℕ) : ℕ := positions.getD i 0

end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentStagedOperation977ExponentsV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows
compact_certificate def operation977Exponent0 : Exponent := (-4,-2,0,0,0,0,0)
compact_certificate def operation977Exponent1 : Exponent := (-4,-1,0,0,0,1,0)
compact_certificate def operation977Exponent2 : Exponent := (-4,0,0,0,0,0,0)
compact_certificate def operation977Exponent3 : Exponent := (-3,-2,0,0,1,0,0)
compact_certificate def operation977Exponent4 : Exponent := (-3,-1,0,0,1,1,0)
compact_certificate def operation977Exponent5 : Exponent := (-3,0,0,0,1,0,0)
compact_certificate def operation977Exponent6 : Exponent := (-2,-3,0,0,0,1,0)
compact_certificate def operation977Exponent7 : Exponent := (-2,-2,0,0,0,0,0)
compact_certificate def operation977Exponent8 : Exponent := (-2,-1,0,0,0,1,0)
compact_certificate def operation977Exponent9 : Exponent := (-2,-1,0,0,2,1,0)
compact_certificate def operation977Exponent10 : Exponent := (-2,0,0,0,0,0,0)
compact_certificate def operation977Exponent11 : Exponent := (-2,0,0,0,2,0,0)
compact_certificate def operation977Exponent12 : Exponent := (-1,-4,0,0,1,0,0)
compact_certificate def operation977Exponent13 : Exponent := (-1,-2,0,0,1,0,0)
compact_certificate def operation977Exponent14 : Exponent := (-1,-1,0,0,1,1,0)
compact_certificate def operation977Exponent15 : Exponent := (-1,0,0,0,1,0,0)
compact_certificate def operation977Exponent16 : Exponent := (0,-3,0,0,0,1,0)
compact_certificate def operation977Exponent17 : Exponent := (0,-2,0,0,0,0,0)
compact_certificate def operation977Exponent18 : Exponent := (0,-2,0,0,2,0,0)
compact_certificate def operation977Exponent19 : Exponent := (0,-1,0,0,0,1,0)
compact_certificate def operation977Exponent20 : Exponent := (0,-1,0,0,2,1,0)
compact_certificate def operation977Exponent21 : Exponent := (0,0,0,0,0,0,0)
compact_certificate def operation977Exponent22 : Exponent := (0,0,0,0,2,0,0)
compact_certificate def operation977Exponent23 : Exponent := (1,-2,0,0,1,0,0)
compact_certificate def operation977Exponent24 : Exponent := (1,-1,0,0,1,1,0)
compact_certificate def operation977Exponent25 : Exponent := (1,0,0,0,1,0,0)
compact_certificate def operation977Exponent26 : Exponent := (2,-2,0,0,0,0,0)
compact_certificate def operation977Exponent27 : Exponent := (2,-1,0,0,0,1,0)
compact_certificate def operation977Exponent28 : Exponent := (2,0,0,0,0,0,0)
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentStagedOperation977CoefficientsV1 -/
section
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
compact_certificate def operation977Coeff0 : ℚ := -1
compact_certificate def operation977Coeff1 : ℚ := -2
compact_certificate def operation977Coeff2 : ℚ := -3
compact_certificate def operation977Coeff3 : ℚ := -4
compact_certificate def operation977Coeff4 : ℚ := 1
compact_certificate def operation977Coeff5 : ℚ := 2
compact_certificate def operation977Coeff6 : ℚ := 3
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentStagedOperation977Step0000V1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate def operation977Result509 : Poly := []

compact_certificate theorem operation977_suffix509 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 509)=operation977Result509 := by
  decide +kernel

compact_certificate def operation977Result480 : Poly := laurent_polynomial% "-1/1:34:-1,0,0,0,1,0,0;1/1:52:-3,0,0,0,1,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:58:0,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;-1/1:64:-1,0,0,0,1,0,0;1/1:68:-2,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:76:-1,0,0,0,1,0,0;-1/1:149:0,0,0,0,0,0,0;1/1:162:-2,-2,0,0,0,0,0;-1/1:162:-1,-2,0,0,1,0,0;-1/1:162:-1,-1,0,0,1,1,0;1/1:162:0,-2,0,0,0,0,0;1/1:162:0,0,0,0,2,0,0;1/1:162:1,0,0,0,1,0,0;-2/1:166:-3,0,0,0,1,0,0;-1/1:166:-2,0,0,0,0,0,0;1/1:174:-3,-2,0,0,1,0,0;-1/1:174:-3,0,0,0,1,0,0;-1/1:174:-2,-2,0,0,0,0,0;-1/1:174:-2,-1,0,0,0,1,0;1/1:174:-1,-2,0,0,1,0,0;1/1:174:0,-1,0,0,0,1,0;1/1:174:0,0,0,0,0,0,0;-1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-1,0,0,0,1,0;-1/1:186:-2,0,0,0,0,0,0;-1/1:186:0,-2,0,0,0,0,0;1/1:186:1,0,0,0,1,0,0;1/1:216:-2,-1,0,0,0,1,0;1/1:216:-2,0,0,0,0,0,0;1/1:216:-1,-2,0,0,1,0,0;1/1:216:0,-1,0,0,0,1,0;-1/1:227:0,0,0,0,0,0,0;1/1:234:-2,-2,0,0,0,0,0;-2/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:234:0,-1,0,0,0,1,0;1/1:264:-2,-1,0,0,0,1,0;-2/1:264:-1,0,0,0,1,0,0;1/1:264:0,-1,0,0,0,1,0;1/1:264:0,0,0,0,0,0,0;-1/1:274:-1,0,0,0,1,0,0;1/1:278:-2,0,0,0,0,0,0;1/1:282:-2,-2,0,0,0,0,0;1/1:282:-2,0,0,0,0,0,0;-1/1:282:-1,-2,0,0,1,0,0;-1/1:282:0,0,0,0,0,0,0;1/1:284:0,0,0,0,0,0,0;-1/1:297:0,0,0,0,0,0,0;1/1:302:-2,0,0,0,0,0,0;2/1:332:-4,0,0,0,0,0,0;-1/1:348:-4,-2,0,0,0,0,0;1/1:348:-4,0,0,0,0,0,0;-3/1:348:-2,-2,0,0,0,0,0;-1/1:348:-1,-1,0,0,1,1,0;-1/1:348:-1,0,0,0,1,0,0;1/1:348:0,0,0,0,0,0,0;1/1:354:-2,-2,0,0,0,0,0;1/1:354:-2,-1,0,0,0,1,0;1/1:354:-1,0,0,0,1,0,0;-2/1:354:0,0,0,0,0,0,0;1/1:386:-2,0,0,0,0,0,0;-1/1:396:-2,-1,0,0,0,1,0;-1/1:396:-1,-2,0,0,1,0,0;-1/1:396:0,-2,0,0,0,0,0;-1/1:396:0,-1,0,0,0,1,0;-1/1:398:-2,0,0,0,0,0,0;-1/1:398:0,0,0,0,0,0,0;-1/1:402:-2,-2,0,0,0,0,0;-1/1:402:-1,-2,0,0,1,0,0;2/1:402:0,0,0,0,0,0,0;1/1:408:-2,-2,0,0,0,0,0;1/1:408:-2,0,0,0,0,0,0;1/1:408:-1,-1,0,0,1,1,0;-1/1:408:0,0,0,0,0,0,0;1/1:426:-3,-2,0,0,1,0,0;-1/1:426:-2,-1,0,0,0,1,0;2/1:426:-2,0,0,0,0,0,0;1/1:426:-1,-2,0,0,1,0,0;-2/1:426:-1,0,0,0,1,0,0;-1/1:426:0,-2,0,0,0,0,0;3/1:432:-2,-2,0,0,0,0,0;1/1:432:0,-2,0,0,0,0,0;-3/1:432:0,0,0,0,0,0,0;1/1:432:1,-1,0,0,1,1,0;-1/1:432:1,0,0,0,1,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,-1,0,0,1,1,0;-1/1:444:-1,0,0,0,1,0,0;1/1:444:0,-1,0,0,0,1,0;-1/1:444:0,0,0,0,0,0,0;-1/1:444:2,-1,0,0,0,1,0;1/1:458:-2,0,0,0,0,0,0;1/1:458:0,0,0,0,0,0,0;-1/1:474:-2,-2,0,0,0,0,0;1/1:474:-1,-2,0,0,1,0,0;-1/1:474:-1,0,0,0,1,0,0;1/1:474:1,0,0,0,1,0,0;-2/1:478:-2,0,0,0,0,0,0;-1/1:478:0,0,0,0,0,0,0;1/1:488:-2,0,0,0,0,0,0;1/1:572:0,0,0,0,0,0,0;-1/1:576:-2,-1,0,0,0,1,0;2/1:576:-2,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:0,-1,0,0,0,1,0;-2/1:576:1,0,0,0,1,0,0;1/1:576:2,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:606:-2,-1,0,0,0,1,0;-1/1:606:-1,0,0,0,1,0,0;1/1:606:0,-1,0,0,0,1,0;-1/1:606:1,0,0,0,1,0,0;-1/1:606:2,0,0,0,0,0,0;2/1:618:-2,-2,0,0,0,0,0;3/1:618:-2,0,0,0,0,0,0;1/1:618:-1,-1,0,0,1,1,0;-1/1:618:0,-2,0,0,0,0,0;1/1:618:0,0,0,0,0,0,0;-1/1:618:2,0,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:624:-3,-2,0,0,1,0,0;-1/1:624:-2,-2,0,0,0,0,0;-1/1:624:-2,-1,0,0,0,1,0;1/1:624:-1,0,0,0,1,0,0;-1/1:634:-1,0,0,0,1,0,0;1/1:642:-2,-2,0,0,0,0,0;-1/1:642:-1,-1,0,0,1,1,0;-1/1:642:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:648:-2,0,0,0,0,0,0;-1/1:648:-1,-1,0,0,1,1,0;-1/1:648:-1,0,0,0,1,0,0;-1/1:648:0,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:677:0,0,0,0,0,0,0;-2/1:688:-2,0,0,0,0,0,0;-1/1:688:0,0,0,0,0,0,0;1/1:694:0,0,0,0,0,0,0;1/1:696:-1,0,0,0,1,0,0;1/1:696:0,-2,0,0,0,0,0;-1/1:696:0,-1,0,0,0,1,0;-1/1:702:-3,-1,0,0,1,1,0;-1/1:702:-2,-2,0,0,0,0,0;2/1:702:-2,0,0,0,0,0,0;-1/1:702:-1,-2,0,0,1,0,0;-1/1:702:-1,-1,0,0,1,1,0;-1/1:702:0,-2,0,0,0,0,0;1/1:702:0,0,0,0,0,0,0;-1/1:706:-1,0,0,0,1,0,0;1/1:712:-2,0,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;1/1:718:-4,0,0,0,0,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;2/1:768:-2,0,0,0,0,0,0;-1/1:768:-1,0,0,0,1,0,0;-1/1:768:0,-2,0,0,0,0,0;1/1:768:0,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;-1/1:772:0,0,0,0,0,0,0;-1/1:794:-1,0,0,0,1,0,0;1/1:802:0,0,0,0,0,0,0;1/1:806:-2,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;2/1:834:-1,0,0,0,1,0,0;-1/1:834:0,-1,0,0,0,1,0;-1/1:834:0,0,0,0,0,0,0;1/1:842:-2,0,0,0,0,0,0;1/1:842:0,0,0,0,0,0,0;-2/1:848:-2,0,0,0,0,0,0;-1/1:848:-1,0,0,0,1,0,0;-1/1:848:0,0,0,0,0,0,0;1/1:864:-3,0,0,0,1,0,0;1/1:864:-2,-2,0,0,0,0,0;-1/1:864:-2,-1,0,0,0,1,0;-1/1:864:0,-1,0,0,2,1,0;1/1:864:0,0,0,0,2,0,0;1/1:864:1,0,0,0,1,0,0;-1/1:876:-2,-1,0,0,0,1,0;1/1:876:-2,-1,0,0,2,1,0;-1/1:876:-1,0,0,0,1,0,0;-1/1:878:-4,0,0,0,0,0,0;1/1:878:-2,0,0,0,0,0,0;1/1:878:0,0,0,0,0,0,0;-1/1:884:-3,0,0,0,1,0,0;1/1:888:-2,-2,0,0,0,0,0;1/1:888:-2,0,0,0,0,0,0;-1/1:888:-1,-1,0,0,1,1,0;2/1:888:-1,0,0,0,1,0,0;1/1:888:1,-1,0,0,1,1,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;1/1:902:-2,0,0,0,0,0,0;1/1:914:-1,0,0,0,1,0,0;1/1:914:0,0,0,0,0,0,0;1/1:926:-2,0,0,0,0,0,0;1/1:932:-2,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0;1/1:936:0,-1,0,0,0,1,0;-1/1:944:0,0,0,0,0,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:958:-1,0,0,0,1,0,0;-1/1:977:0,0,0,0,0,0,0;1/1:986:-1,0,0,0,1,0,0;-1/1:992:-2,0,0,0,2,0,0;1/1:992:0,0,0,0,0,0,0;-1/1:998:-2,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;-1/1:998:0,0,0,0,0,0,0;1/1:1016:-2,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0;-1/1:1016:1,0,0,0,1,0,0"

compact_certificate theorem operation977_suffix480 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 480)=operation977Result480 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 480 29
    operation977Result480 operation977Result509 operation977_suffix509
  decide +kernel

compact_certificate def operation977Result448 : Poly := laurent_polynomial% "-1/1:34:-1,0,0,0,1,0,0;2/1:52:-4,0,0,0,0,0,0;1/1:52:-3,0,0,0,1,0,0;1/1:52:-2,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;-1/1:64:-1,0,0,0,1,0,0;1/1:68:-2,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:76:-1,0,0,0,1,0,0;1/1:92:-2,0,0,0,0,0,0;-1/1:107:0,0,0,0,0,0,0;-1/1:144:-2,-2,0,0,0,0,0;-1/1:144:-2,-1,0,0,0,1,0;-1/1:149:0,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;1/1:162:-2,-2,0,0,0,0,0;1/1:162:-2,0,0,0,0,0,0;1/1:162:0,-2,0,0,0,0,0;-2/1:162:0,-1,0,0,0,1,0;1/1:162:0,-1,0,0,2,1,0;-1/1:166:-2,0,0,0,0,0,0;1/1:166:-1,0,0,0,1,0,0;1/1:172:-4,0,0,0,0,0,0;1/1:172:-3,0,0,0,1,0,0;-1/1:172:-2,0,0,0,0,0,0;-1/1:172:0,0,0,0,0,0,0;1/1:174:-3,-2,0,0,1,0,0;-3/1:174:-3,0,0,0,1,0,0;1/1:174:-1,-2,0,0,1,0,0;-1/1:174:-1,-1,0,0,1,1,0;1/1:174:-1,0,0,0,1,0,0;1/1:174:0,0,0,0,0,0,0;-1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-1,0,0,0,1,0;-1/1:186:-2,0,0,0,0,0,0;2/1:186:-1,0,0,0,1,0,0;-1/1:186:0,-2,0,0,0,0,0;-1/1:192:-2,0,0,0,0,0,0;1/1:192:0,0,0,0,0,0,0;1/1:216:-2,0,0,0,0,0,0;1/1:216:0,-1,0,0,0,1,0;-1/1:227:0,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-3/1:234:-2,-1,0,0,0,1,0;-1/1:234:0,-1,0,0,0,1,0;-1/1:244:-1,0,0,0,1,0,0;1/1:264:-2,-1,0,0,0,1,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:-1,0,0,0,1,0,0;1/1:264:0,0,0,0,0,0,0;-1/1:274:-1,0,0,0,1,0,0;1/1:278:-2,0,0,0,0,0,0;2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:282:0,0,0,0,0,0,0;1/1:284:0,0,0,0,0,0,0;-1/1:297:0,0,0,0,0,0,0;2/1:302:-2,0,0,0,0,0,0;-1/1:332:-2,0,0,0,0,0,0;-1/1:348:-4,-2,0,0,0,0,0;3/1:348:-4,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;1/1:348:-2,-1,0,0,0,1,0;-1/1:348:-2,0,0,0,0,0,0;-1/1:348:-1,0,0,0,1,0,0;1/1:348:0,-2,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;1/1:354:-1,0,0,0,1,0,0;-2/1:354:0,0,0,0,0,0,0;1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:394:-2,-1,0,0,0,1,0;-1/1:394:0,-1,0,0,0,1,0;-1/1:396:-2,-3,0,0,0,1,0;-1/1:396:-2,-1,0,0,0,1,0;1/1:396:-1,0,0,0,1,0,0;-1/1:396:0,-3,0,0,0,1,0;2/1:398:-2,0,0,0,0,0,0;1/1:398:0,0,0,0,0,0,0;-1/1:402:-2,-2,0,0,0,0,0;2/1:402:0,0,0,0,0,0,0;1/1:408:-2,-2,0,0,0,0,0;-1/1:426:-4,-2,0,0,0,0,0;1/1:426:-3,-2,0,0,1,0,0;-1/1:426:-2,-1,0,0,0,1,0;1/1:426:-2,0,0,0,0,0,0;-2/1:426:-1,0,0,0,1,0,0;3/1:432:-2,-2,0,0,0,0,0;-2/1:432:-2,0,0,0,0,0,0;1/1:432:0,-2,0,0,0,0,0;-1/1:432:0,-1,0,0,0,1,0;-3/1:432:0,0,0,0,0,0,0;-1/1:432:1,0,0,0,1,0,0;-1/1:444:-2,-2,0,0,0,0,0;-2/1:444:-2,-1,0,0,0,1,0;1/1:444:0,-1,0,0,0,1,0;1/1:444:1,0,0,0,1,0,0;-1/1:444:2,-1,0,0,0,1,0;1/1:458:-2,0,0,0,0,0,0;-1/1:458:-1,0,0,0,1,0,0;1/1:458:0,0,0,0,0,0,0;1/1:464:0,0,0,0,0,0,0;1/1:474:-2,-1,0,0,0,1,0;1/1:474:-1,-2,0,0,1,0,0;-1/1:474:-1,0,0,0,1,0,0;-1/1:474:1,-2,0,0,1,0,0;1/1:474:1,0,0,0,1,0,0;-2/1:478:-2,0,0,0,0,0,0;-1/1:478:0,0,0,0,0,0,0;1/1:488:-2,0,0,0,0,0,0;1/1:512:-2,0,0,0,0,0,0;1/1:572:0,0,0,0,0,0,0;-1/1:576:-2,-1,0,0,0,1,0;1/1:576:-2,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:0,-1,0,0,0,1,0;-2/1:576:1,-2,0,0,1,0,0;-1/1:576:1,0,0,0,1,0,0;1/1:576:2,0,0,0,0,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:592:0,0,0,0,0,0,0;-1/1:598:-2,0,0,0,0,0,0;-1/1:598:0,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:604:0,0,0,0,0,0,0;-1/1:606:-2,-1,0,0,0,1,0;-1/1:606:1,-1,0,0,1,1,0;1/1:618:-2,-2,0,0,0,0,0;2/1:618:-2,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:624:-3,-2,0,0,1,0,0;2/1:624:-1,-2,0,0,1,0,0;-1/1:634:-1,0,0,0,1,0,0;1/1:638:-2,0,0,0,0,0,0;1/1:638:-1,0,0,0,1,0,0;-1/1:642:-2,-2,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;-1/1:642:0,-2,0,0,0,0,0;1/1:648:-2,-2,0,0,0,0,0;-1/1:648:-2,0,0,0,0,0,0;-1/1:648:-1,-1,0,0,1,1,0;-1/1:648:-1,0,0,0,1,0,0;-1/1:648:0,-2,0,0,0,0,0;1/1:648:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:676:-1,0,0,0,1,0,0;-1/1:677:0,0,0,0,0,0,0;-2/1:688:-2,0,0,0,0,0,0;-1/1:688:0,0,0,0,0,0,0;-1/1:694:-1,0,0,0,1,0,0;1/1:694:0,0,0,0,0,0,0;1/1:696:-2,0,0,0,0,0,0;1/1:696:-1,0,0,0,1,0,0;1/1:696:0,-2,0,0,0,0,0;1/1:702:-4,0,0,0,0,0,0;2/1:702:-2,0,0,0,0,0,0;-1/1:702:0,-2,0,0,0,0,0;1/1:702:0,-1,0,0,0,1,0;-1/1:706:-1,0,0,0,1,0,0;1/1:712:-2,0,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;1/1:718:-4,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;-1/1:724:-1,0,0,0,1,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;1/1:754:0,0,0,0,0,0,0;2/1:768:-2,0,0,0,0,0,0;-1/1:768:-1,-1,0,0,1,1,0;-1/1:768:-1,0,0,0,1,0,0;1/1:768:0,0,0,0,0,0,0;-1/1:772:0,0,0,0,0,0,0;-1/1:778:-1,0,0,0,1,0,0;1/1:782:0,0,0,0,0,0,0;1/1:788:0,0,0,0,0,0,0;1/1:794:-1,0,0,0,1,0,0;-1/1:802:-2,0,0,0,0,0,0;1/1:806:-2,0,0,0,0,0,0;2/1:818:-2,0,0,0,0,0,0;1/1:818:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;1/1:834:-1,-2,0,0,1,0,0;1/1:834:-1,0,0,0,1,0,0;-1/1:834:0,-1,0,0,0,1,0;-1/1:834:0,0,0,0,0,0,0;1/1:842:-2,0,0,0,0,0,0;1/1:842:0,0,0,0,0,0,0;-1/1:844:-1,0,0,0,1,0,0;-1/1:858:-2,0,0,0,0,0,0;-1/1:858:-1,-1,0,0,1,1,0;-1/1:864:-4,0,0,0,0,0,0;1/1:864:-3,0,0,0,1,0,0;-2/1:864:-2,-1,0,0,0,1,0;-1/1:864:-1,-2,0,0,1,0,0;-1/1:864:-1,-1,0,0,1,1,0;1/1:864:-1,0,0,0,1,0,0;1/1:864:0,0,0,0,2,0,0;-1/1:876:-3,0,0,0,1,0,0;-1/1:876:-2,-1,0,0,0,1,0;-1/1:876:-2,0,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:878:-4,0,0,0,0,0,0;1/1:878:-2,0,0,0,0,0,0;1/1:878:0,0,0,0,0,0,0;-1/1:884:-3,0,0,0,1,0,0;1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:-1,-1,0,0,1,1,0;1/1:888:-1,0,0,0,1,0,0;-1/1:888:0,-2,0,0,0,0,0;-1/1:888:0,0,0,0,0,0,0;-1/1:888:0,0,0,0,2,0,0;1/1:888:1,-1,0,0,1,1,0;-1/1:893:0,0,0,0,0,0,0;1/1:897:0,-2,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;1/1:902:-2,0,0,0,0,0,0;1/1:906:-2,0,0,0,0,0,0;1/1:914:0,0,0,0,0,0,0;1/1:926:-2,0,0,0,0,0,0;-1/1:929:0,0,0,0,0,0,0;1/1:932:-2,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:0,-1,0,0,0,1,0;-1/1:944:0,0,0,0,0,0,0;1/1:951:0,-2,0,0,0,0,0;1/1:956:-1,0,0,0,1,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:958:-1,0,0,0,1,0,0;-1/1:977:0,0,0,0,0,0,0;1/1:986:-1,0,0,0,1,0,0;-1/1:992:-2,0,0,0,2,0,0;1/1:992:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;1/1:1016:-2,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0"

compact_certificate theorem operation977_suffix448 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 448)=operation977Result448 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 448 32
    operation977Result448 operation977Result480 operation977_suffix480
  decide +kernel

compact_certificate def operation977Result416 : Poly := laurent_polynomial% "-1/1:34:-1,0,0,0,1,0,0;2/1:52:-4,0,0,0,0,0,0;1/1:52:-3,0,0,0,1,0,0;1/1:52:-2,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;1/1:62:-2,0,0,0,0,0,0;1/1:62:0,0,0,0,0,0,0;-1/1:64:-2,0,0,0,0,0,0;-1/1:64:-1,0,0,0,1,0,0;1/1:68:-2,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:76:-1,0,0,0,1,0,0;1/1:92:-2,0,0,0,0,0,0;-1/1:107:0,0,0,0,0,0,0;-1/1:144:-2,-2,0,0,0,0,0;-1/1:144:-2,-1,0,0,0,1,0;1/1:146:-2,0,0,0,0,0,0;-1/1:149:0,0,0,0,0,0,0;1/1:152:-2,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;-1/1:159:0,0,0,0,0,0,0;2/1:162:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,0,0,0;1/1:172:-4,0,0,0,0,0,0;1/1:172:-3,0,0,0,1,0,0;-1/1:172:-2,0,0,0,0,0,0;-1/1:172:0,0,0,0,0,0,0;-2/1:174:-3,0,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:174:0,0,0,0,0,0,0;-1/1:186:-4,0,0,0,0,0,0;-1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-1,0,0,0,1,0;-1/1:186:-1,-1,0,0,1,1,0;2/1:186:-1,0,0,0,1,0,0;-1/1:186:0,-2,0,0,0,0,0;-1/1:186:0,-1,0,0,2,1,0;-1/1:192:-2,0,0,0,0,0,0;1/1:192:0,0,0,0,0,0,0;-1/1:207:0,0,0,0,0,0,0;-1/1:213:0,0,0,0,0,0,0;1/1:216:-2,0,0,0,0,0,0;1/1:216:0,-1,0,0,0,1,0;1/1:218:-2,0,0,0,0,0,0;-1/1:227:0,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:234:0,-1,0,0,0,1,0;-1/1:234:0,0,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:264:-2,-1,0,0,0,1,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-2/1:264:-1,0,0,0,1,0,0;2/1:264:0,0,0,0,0,0,0;-1/1:268:-2,0,0,0,0,0,0;1/1:272:-2,0,0,0,0,0,0;1/1:272:0,0,0,0,0,0,0;-1/1:274:-2,0,0,0,0,0,0;-1/1:274:-1,0,0,0,1,0,0;1/1:278:-2,0,0,0,0,0,0;1/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:282:0,0,0,0,0,0,0;1/1:284:0,0,0,0,0,0,0;-1/1:286:-1,0,0,0,1,0,0;-1/1:297:0,0,0,0,0,0,0;2/1:302:-2,0,0,0,0,0,0;-1/1:328:-2,0,0,0,0,0,0;-1/1:332:-2,0,0,0,0,0,0;1/1:342:-2,-2,0,0,0,0,0;-2/1:342:-2,0,0,0,0,0,0;1/1:342:0,-2,0,0,0,0,0;-1/1:342:0,-1,0,0,0,1,0;-1/1:342:0,0,0,0,0,0,0;2/1:348:-4,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;-1/1:348:-1,0,0,0,1,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:354:-2,-1,0,0,0,1,0;-1/1:354:0,0,0,0,0,0,0;1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:388:-1,0,0,0,1,0,0;-1/1:394:-2,-1,0,0,0,1,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:394:0,-1,0,0,0,1,0;-1/1:396:-2,-3,0,0,0,1,0;-1/1:396:-2,-1,0,0,0,1,0;1/1:396:-1,0,0,0,1,0,0;-1/1:396:0,-3,0,0,0,1,0;2/1:398:-2,0,0,0,0,0,0;1/1:398:0,0,0,0,0,0,0;1/1:402:-2,0,0,0,0,0,0;2/1:402:0,0,0,0,0,0,0;1/1:408:-2,-2,0,0,0,0,0;1/1:408:-2,0,0,0,0,0,0;1/1:426:-3,-2,0,0,1,0,0;1/1:426:-2,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;1/1:432:-2,-2,0,0,0,0,0;-2/1:432:0,0,0,0,0,0,0;-1/1:432:1,0,0,0,1,0,0;-1/1:444:-2,-2,0,0,0,0,0;-1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;-1/1:444:0,0,0,0,0,0,0;1/1:444:1,0,0,0,1,0,0;-1/1:444:2,-1,0,0,0,1,0;1/1:458:-2,0,0,0,0,0,0;1/1:458:0,0,0,0,0,0,0;1/1:464:0,0,0,0,0,0,0;1/1:474:-2,-1,0,0,0,1,0;-1/1:474:-1,0,0,0,1,0,0;1/1:474:0,0,0,0,0,0,0;-1/1:474:1,-2,0,0,1,0,0;1/1:474:1,0,0,0,1,0,0;-2/1:478:-2,0,0,0,0,0,0;-1/1:478:0,0,0,0,0,0,0;1/1:488:-2,0,0,0,0,0,0;1/1:494:0,0,0,0,0,0,0;1/1:512:-2,0,0,0,0,0,0;1/1:572:-2,0,0,0,0,0,0;1/1:572:0,0,0,0,0,0,0;1/1:576:-2,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-2/1:576:1,-2,0,0,1,0,0;1/1:576:1,0,0,0,1,0,0;-1/1:586:-1,0,0,0,1,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:592:0,0,0,0,0,0,0;-1/1:598:-2,0,0,0,0,0,0;-1/1:598:-1,0,0,0,1,0,0;-1/1:598:0,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;-1/1:604:0,0,0,0,0,0,0;1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-2,-1,0,0,0,1,0;1/1:614:0,0,0,0,0,0,0;2/1:618:-2,-2,0,0,0,0,0;2/1:618:-2,0,0,0,0,0,0;-1/1:618:-1,0,0,0,1,0,0;1/1:618:0,-1,0,0,0,1,0;1/1:618:1,-1,0,0,1,1,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:624:-4,-2,0,0,0,0,0;-1/1:624:-3,-2,0,0,1,0,0;2/1:624:-1,-2,0,0,1,0,0;-1/1:634:-1,0,0,0,1,0,0;2/1:638:-2,0,0,0,0,0,0;1/1:638:-1,0,0,0,1,0,0;-1/1:642:-2,-2,0,0,0,0,0;-1/1:646:-1,0,0,0,1,0,0;1/1:648:-2,-2,0,0,0,0,0;-1/1:648:-2,0,0,0,0,0,0;-1/1:648:-1,-1,0,0,1,1,0;-1/1:648:-1,0,0,0,1,0,0;-1/1:648:0,-2,0,0,0,0,0;1/1:648:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:676:-1,0,0,0,1,0,0;-1/1:677:0,0,0,0,0,0,0;-2/1:688:-2,0,0,0,0,0,0;-1/1:688:0,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0;-1/1:694:-1,0,0,0,1,0,0;-1/1:696:-2,-1,0,0,0,1,0;1/1:696:-2,0,0,0,0,0,0;2/1:696:-1,0,0,0,1,0,0;-1/1:696:0,-2,0,0,0,0,0;-1/1:702:-4,-2,0,0,0,0,0;1/1:702:-4,0,0,0,0,0,0;1/1:702:-2,0,0,0,0,0,0;-1/1:706:-2,0,0,0,0,0,0;-1/1:706:-1,0,0,0,1,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:708:0,-2,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;-1/1:713:0,0,0,0,0,0,0;1/1:718:-4,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;-1/1:724:-1,0,0,0,1,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;-1/1:754:-1,0,0,0,1,0,0;2/1:768:-2,0,0,0,0,0,0;-1/1:768:-1,-1,0,0,1,1,0;-2/1:768:-1,0,0,0,1,0,0;1/1:768:0,0,0,0,0,0,0;-1/1:772:0,0,0,0,0,0,0;1/1:776:-2,0,0,0,0,0,0;-1/1:778:-2,0,0,0,0,0,0;-1/1:778:-1,0,0,0,1,0,0;1/1:782:-2,0,0,0,0,0,0;1/1:782:0,0,0,0,0,0,0;1/1:786:-2,0,0,0,0,0,0;1/1:788:0,0,0,0,0,0,0;1/1:794:-1,0,0,0,1,0,0;1/1:794:0,0,0,0,0,0,0;-2/1:796:-1,0,0,0,1,0,0;-1/1:802:-2,0,0,0,0,0,0;-1/1:804:-1,0,0,0,1,0,0;1/1:804:0,0,0,0,0,0,0;1/1:806:-2,0,0,0,0,0,0;-1/1:814:-2,0,0,0,0,0,0;2/1:818:-2,0,0,0,0,0,0;1/1:818:0,0,0,0,0,0,0;1/1:824:-2,0,0,0,0,0,0;1/1:824:-1,0,0,0,1,0,0;1/1:824:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:834:0,-1,0,0,0,1,0;-1/1:834:0,0,0,0,0,0,0;-1/1:837:0,0,0,0,0,0,0;1/1:842:-2,0,0,0,0,0,0;1/1:842:0,0,0,0,0,0,0;-1/1:843:0,0,0,0,0,0,0;-1/1:844:-1,0,0,0,1,0,0;1/1:848:-2,0,0,0,0,0,0;-1/1:858:-2,0,0,0,0,0,0;1/1:864:-3,0,0,0,1,0,0;-1/1:864:-2,-1,0,0,0,1,0;-1/1:864:-1,-2,0,0,1,0,0;-1/1:864:-1,-1,0,0,1,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:864:0,0,0,0,0,0,0;1/1:864:0,0,0,0,2,0,0;1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-3,0,0,0,1,0,0;-1/1:876:-2,0,0,0,0,0,0;-2/1:878:-4,0,0,0,0,0,0;1/1:878:-1,0,0,0,1,0,0;1/1:878:0,0,0,0,0,0,0;-1/1:884:-3,0,0,0,1,0,0;1/1:884:-2,0,0,0,0,0,0;1/1:884:0,0,0,0,0,0,0;1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;1/1:888:-1,0,0,0,1,0,0;-1/1:888:0,0,0,0,2,0,0;1/1:888:1,-1,0,0,1,1,0;-1/1:893:0,0,0,0,0,0,0;1/1:897:0,-2,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;2/1:902:-2,0,0,0,0,0,0;1/1:902:0,0,0,0,0,0,0;-1/1:904:-2,0,0,0,0,0,0;1/1:906:-2,-2,0,0,0,0,0;-1/1:906:-2,-1,0,0,0,1,0;1/1:906:-2,0,0,0,0,0,0;1/1:906:-1,-2,0,0,1,0,0;1/1:914:0,0,0,0,0,0,0;1/1:926:-2,0,0,0,0,0,0;-1/1:929:0,0,0,0,0,0,0;1/1:932:-2,0,0,0,0,0,0;2/1:934:-3,0,0,0,1,0,0;-1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-2,0,0,0,0,0,0;1/1:936:0,-1,0,0,0,1,0;-1/1:946:-1,0,0,0,1,0,0;1/1:951:0,-2,0,0,0,0,0;1/1:956:-1,0,0,0,1,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:958:-1,0,0,0,1,0,0;-1/1:977:0,0,0,0,0,0,0;1/1:986:-2,0,0,0,0,0,0;1/1:992:-2,0,0,0,0,0,0;-2/1:992:-2,0,0,0,2,0,0;1/1:992:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;1/1:1016:-2,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0"

compact_certificate theorem operation977_suffix416 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 416)=operation977Result416 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 416 32
    operation977Result416 operation977Result448 operation977_suffix448
  decide +kernel

compact_certificate def operation977Result384 : Poly := laurent_polynomial% "-1/1:34:-2,0,0,0,0,0,0;-1/1:34:-1,0,0,0,1,0,0;2/1:52:-4,0,0,0,0,0,0;1/1:52:-3,0,0,0,1,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;1/1:62:-2,0,0,0,0,0,0;1/1:62:0,0,0,0,0,0,0;-1/1:64:-2,0,0,0,0,0,0;-1/1:64:-1,0,0,0,1,0,0;1/1:68:-2,0,0,0,0,0,0;1/1:68:0,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:76:-1,0,0,0,1,0,0;1/1:92:-2,0,0,0,0,0,0;-1/1:94:-1,0,0,0,1,0,0;-1/1:107:0,0,0,0,0,0,0;1/1:122:-2,0,0,0,0,0,0;1/1:122:0,0,0,0,0,0,0;-1/1:124:-2,0,0,0,0,0,0;-1/1:124:-1,0,0,0,1,0,0;-1/1:136:-1,0,0,0,1,0,0;-1/1:142:-2,0,0,0,0,0,0;-1/1:144:-2,-2,0,0,0,0,0;-1/1:144:-2,-1,0,0,0,1,0;1/1:146:-2,0,0,0,0,0,0;-1/1:149:0,0,0,0,0,0,0;1/1:152:-2,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;-1/1:159:0,0,0,0,0,0,0;2/1:162:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,0,0,0;1/1:172:-4,0,0,0,0,0,0;1/1:172:-3,0,0,0,1,0,0;-1/1:172:-2,0,0,0,0,0,0;-1/1:172:0,0,0,0,0,0,0;1/1:174:-2,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:174:0,0,0,0,0,0,0;-1/1:186:-4,0,0,0,0,0,0;-1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-1,0,0,0,1,0;3/1:186:-1,0,0,0,1,0,0;1/1:192:-2,0,0,0,0,0,0;1/1:192:0,0,0,0,0,0,0;-1/1:207:0,0,0,0,0,0,0;-1/1:213:0,0,0,0,0,0,0;1/1:216:-2,0,0,0,0,0,0;-1/1:216:-1,0,0,0,1,0,0;1/1:216:0,-1,0,0,0,1,0;1/1:218:-2,0,0,0,0,0,0;-1/1:219:0,0,0,0,0,0,0;-1/1:227:0,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-1/1:234:-1,0,0,0,1,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-1,0,0,0,1,0,0;1/1:248:0,0,0,0,0,0,0;1/1:254:0,0,0,0,0,0,0;-1/1:256:-1,0,0,0,1,0,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:-1,0,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;1/1:264:0,0,0,0,0,0,0;-1/1:268:-2,0,0,0,0,0,0;1/1:272:-2,0,0,0,0,0,0;1/1:272:0,0,0,0,0,0,0;-1/1:274:-2,0,0,0,0,0,0;-1/1:274:-1,0,0,0,1,0,0;1/1:278:-2,0,0,0,0,0,0;1/1:278:0,0,0,0,0,0,0;1/1:282:-2,-2,0,0,0,0,0;1/1:284:0,0,0,0,0,0,0;-1/1:286:-1,0,0,0,1,0,0;-1/1:297:0,0,0,0,0,0,0;1/1:302:-2,0,0,0,0,0,0;-1/1:327:0,0,0,0,0,0,0;-1/1:328:-2,0,0,0,0,0,0;1/1:332:0,0,0,0,0,0,0;1/1:342:-2,-2,0,0,0,0,0;-2/1:342:-2,0,0,0,0,0,0;-1/1:342:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-1,0,0,0,1,0,0;-1/1:354:-2,-1,0,0,0,1,0;-1/1:354:0,0,0,0,0,0,0;1/1:384:-2,-1,0,0,0,1,0;-1/1:384:-1,0,0,0,1,0,0;1/1:384:0,-1,0,0,0,1,0;1/1:384:0,0,0,0,0,0,0;1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:388:-1,0,0,0,1,0,0;-1/1:394:-2,-1,0,0,0,1,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:396:-2,-3,0,0,0,1,0;2/1:398:-2,0,0,0,0,0,0;1/1:398:0,0,0,0,0,0,0;2/1:402:-2,0,0,0,0,0,0;1/1:402:0,0,0,0,0,0,0;1/1:408:-2,-2,0,0,0,0,0;1/1:426:-2,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;1/1:432:-2,-2,0,0,0,0,0;-1/1:432:0,0,0,0,0,0,0;-1/1:432:1,0,0,0,1,0,0;-1/1:444:-2,-2,0,0,0,0,0;-1/1:444:-2,-1,0,0,0,1,0;-1/1:444:0,0,0,0,0,0,0;1/1:444:1,0,0,0,1,0,0;-1/1:444:2,-1,0,0,0,1,0;-1/1:454:-2,0,0,0,0,0,0;1/1:458:0,0,0,0,0,0,0;1/1:464:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:-1,0,0,0,1,0,0;-1/1:474:0,-1,0,0,0,1,0;2/1:474:1,0,0,0,1,0,0;-2/1:478:-2,0,0,0,0,0,0;-1/1:478:0,0,0,0,0,0,0;1/1:488:-2,0,0,0,0,0,0;1/1:488:0,0,0,0,0,0,0;1/1:494:0,0,0,0,0,0,0;1/1:512:-2,0,0,0,0,0,0;-1/1:556:-1,0,0,0,1,0,0;-1/1:562:-2,0,0,0,0,0,0;1/1:572:-2,0,0,0,0,0,0;1/1:572:0,0,0,0,0,0,0;1/1:576:-2,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:1,-2,0,0,1,0,0;1/1:576:1,0,0,0,1,0,0;-1/1:586:-1,0,0,0,1,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:592:0,0,0,0,0,0,0;-1/1:598:-2,0,0,0,0,0,0;-1/1:598:-1,0,0,0,1,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-2,-1,0,0,0,1,0;-1/1:606:-1,0,0,0,1,0,0;1/1:614:0,0,0,0,0,0,0;1/1:618:-2,-2,0,0,0,0,0;1/1:618:-2,0,0,0,0,0,0;-1/1:618:-1,0,0,0,1,0,0;-2/1:618:0,0,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:624:-4,-2,0,0,0,0,0;-1/1:624:-3,-2,0,0,1,0,0;2/1:624:-1,-2,0,0,1,0,0;-1/1:634:-1,0,0,0,1,0,0;1/1:638:-2,0,0,0,0,0,0;-1/1:639:0,0,0,0,0,0,0;-1/1:642:-2,-2,0,0,0,0,0;1/1:642:0,0,0,0,0,0,0;-1/1:646:-1,0,0,0,1,0,0;1/1:648:-2,0,0,0,0,0,0;-1/1:648:0,-2,0,0,0,0,0;1/1:648:0,0,0,0,0,0,0;-1/1:652:-2,0,0,0,0,0,0;1/1:662:0,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;1/1:666:-2,0,0,0,0,0,0;1/1:668:0,0,0,0,0,0,0;-1/1:676:-1,0,0,0,1,0,0;-1/1:677:0,0,0,0,0,0,0;-2/1:688:-2,0,0,0,0,0,0;-1/1:688:0,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0;-1/1:694:-1,0,0,0,1,0,0;-1/1:696:-2,-1,0,0,0,1,0;1/1:696:-2,0,0,0,0,0,0;2/1:696:-1,0,0,0,1,0,0;-1/1:696:0,-2,0,0,0,0,0;-1/1:702:-4,-2,0,0,0,0,0;1/1:702:-4,0,0,0,0,0,0;2/1:702:-2,0,0,0,0,0,0;-1/1:706:-2,0,0,0,0,0,0;-1/1:706:-1,0,0,0,1,0,0;-1/1:708:-2,-2,0,0,0,0,0;1/1:708:-2,0,0,0,0,0,0;1/1:708:-1,0,0,0,1,0,0;-1/1:712:0,0,0,0,0,0,0;-1/1:713:0,0,0,0,0,0,0;1/1:718:-4,0,0,0,0,0,0;-1/1:718:-2,0,0,0,0,0,0;-1/1:718:-1,0,0,0,1,0,0;1/1:718:0,0,0,0,0,0,0;1/1:722:-2,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;-1/1:724:-1,0,0,0,1,0,0;1/1:727:0,0,0,0,0,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:747:0,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;-1/1:766:-1,0,0,0,1,0,0;1/1:768:-2,-2,0,0,0,0,0;2/1:768:-2,0,0,0,0,0,0;-2/1:768:-1,0,0,0,1,0,0;-1/1:768:0,-2,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;-1/1:772:0,0,0,0,0,0,0;1/1:776:-2,0,0,0,0,0,0;-1/1:778:-2,0,0,0,0,0,0;-1/1:778:-1,0,0,0,1,0,0;1/1:782:-2,0,0,0,0,0,0;1/1:782:0,0,0,0,0,0,0;1/1:786:-2,0,0,0,0,0,0;1/1:788:0,0,0,0,0,0,0;1/1:794:0,0,0,0,0,0,0;-2/1:796:-1,0,0,0,1,0,0;-1/1:802:-2,0,0,0,0,0,0;-1/1:804:-1,0,0,0,1,0,0;1/1:804:0,0,0,0,0,0,0;1/1:806:-2,0,0,0,0,0,0;-1/1:814:-2,0,0,0,0,0,0;2/1:818:-2,0,0,0,0,0,0;1/1:818:0,0,0,0,0,0,0;2/1:822:-2,0,0,0,0,0,0;1/1:824:0,0,0,0,0,0,0;-1/1:828:-2,0,0,0,0,0,0;-1/1:832:-2,0,0,0,0,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:834:-1,0,0,0,1,0,0;-1/1:837:0,0,0,0,0,0,0;1/1:842:-2,0,0,0,0,0,0;1/1:842:0,0,0,0,0,0,0;-1/1:843:0,0,0,0,0,0,0;-1/1:844:-1,0,0,0,1,0,0;1/1:848:-2,0,0,0,0,0,0;-1/1:849:0,0,0,0,0,0,0;-1/1:858:-2,0,0,0,0,0,0;-1/1:858:-1,0,0,0,1,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:-1,0,0,0,1,0,0;-1/1:864:0,0,0,0,0,0,0;1/1:864:0,0,0,0,2,0,0;1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-3,0,0,0,1,0,0;-1/1:876:-2,0,0,0,0,0,0;-1/1:878:-4,0,0,0,0,0,0;1/1:878:-1,0,0,0,1,0,0;1/1:878:0,0,0,0,0,0,0;-1/1:884:-3,0,0,0,1,0,0;1/1:884:-2,0,0,0,0,0,0;1/1:884:0,0,0,0,0,0,0;1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;1/1:888:-1,0,0,0,1,0,0;-1/1:888:0,0,0,0,2,0,0;1/1:888:1,-1,0,0,1,1,0;-1/1:893:0,0,0,0,0,0,0;1/1:897:0,-2,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;2/1:902:-2,0,0,0,0,0,0;-1/1:904:-2,0,0,0,0,0,0;1/1:906:-2,-2,0,0,0,0,0;1/1:906:-2,0,0,0,0,0,0;1/1:906:-1,-2,0,0,1,0,0;1/1:908:0,0,0,0,0,0,0;1/1:914:0,0,0,0,0,0,0;-1/1:916:-1,0,0,0,1,0,0;1/1:926:-2,0,0,0,0,0,0;-1/1:928:-2,0,0,0,0,0,0;-1/1:928:-1,0,0,0,1,0,0;-1/1:929:0,0,0,0,0,0,0;1/1:932:-2,0,0,0,0,0,0;2/1:934:-3,0,0,0,1,0,0;-1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-2,0,0,0,0,0,0;-1/1:946:-1,0,0,0,1,0,0;1/1:951:0,-2,0,0,0,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:958:-1,0,0,0,1,0,0;-1/1:976:-1,0,0,0,1,0,0;-1/1:977:0,0,0,0,0,0,0;1/1:986:-2,0,0,0,0,0,0;-1/1:988:-2,0,0,0,0,0,0;-1/1:988:-1,0,0,0,1,0,0;1/1:992:-2,0,0,0,0,0,0;-2/1:992:-2,0,0,0,2,0,0;1/1:992:0,0,0,0,0,0,0;1/1:998:-2,0,0,0,0,0,0;1/1:1016:-2,0,0,0,0,0,0;-2/1:1016:-1,0,0,0,1,0,0"

compact_certificate theorem operation977_suffix384 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 384)=operation977Result384 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 384 32
    operation977Result384 operation977Result416 operation977_suffix416
  decide +kernel


}
certificate_batch {
compact_certificate def operation977Result352 : Poly := laurent_polynomial% "-1/1:34:-2,0,0,0,0,0,0;-1/1:34:-1,0,0,0,1,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:-3,0,0,0,1,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;-1/1:62:-2,0,0,0,0,0,0;1/1:62:0,0,0,0,0,0,0;-1/1:64:-2,0,0,0,0,0,0;-1/1:64:-1,0,0,0,1,0,0;1/1:68:-2,0,0,0,0,0,0;1/1:68:0,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:76:-1,0,0,0,1,0,0;1/1:92:-2,0,0,0,0,0,0;-1/1:94:-1,0,0,0,1,0,0;-1/1:107:0,0,0,0,0,0,0;1/1:122:0,0,0,0,0,0,0;-1/1:124:-2,0,0,0,0,0,0;-1/1:124:-1,0,0,0,1,0,0;1/1:128:-2,0,0,0,0,0,0;1/1:128:0,0,0,0,0,0,0;-1/1:136:-1,0,0,0,1,0,0;-1/1:142:-2,0,0,0,0,0,0;-1/1:144:-2,-2,0,0,0,0,0;-1/1:148:-2,0,0,0,0,0,0;-1/1:149:0,0,0,0,0,0,0;1/1:152:-2,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;-1/1:159:0,0,0,0,0,0,0;-1/1:166:-2,0,0,0,0,0,0;-1/1:167:0,0,0,0,0,0,0;1/1:172:-4,0,0,0,0,0,0;1/1:172:-3,0,0,0,1,0,0;-1/1:172:-2,0,0,0,0,0,0;-1/1:172:0,0,0,0,0,0,0;1/1:174:-2,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:174:0,0,0,0,0,0,0;-1/1:186:-4,0,0,0,0,0,0;-1/1:186:-3,0,0,0,1,0,0;3/1:186:-1,0,0,0,1,0,0;1/1:188:-2,0,0,0,0,0,0;1/1:192:-2,0,0,0,0,0,0;1/1:192:0,0,0,0,0,0,0;-1/1:202:-2,0,0,0,0,0,0;-1/1:207:0,0,0,0,0,0,0;-1/1:213:0,0,0,0,0,0,0;1/1:216:-2,0,0,0,0,0,0;-1/1:216:-1,0,0,0,1,0,0;-1/1:219:0,0,0,0,0,0,0;-1/1:227:0,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-1/1:234:-1,0,0,0,1,0,0;1/1:242:0,0,0,0,0,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-1,0,0,0,1,0,0;1/1:248:-2,0,0,0,0,0,0;1/1:248:0,0,0,0,0,0,0;1/1:254:0,0,0,0,0,0,0;-1/1:256:-1,0,0,0,1,0,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:-1,0,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;1/1:264:0,0,0,0,0,0,0;-1/1:268:-2,0,0,0,0,0,0;1/1:272:-2,0,0,0,0,0,0;1/1:272:0,0,0,0,0,0,0;-1/1:274:-2,0,0,0,0,0,0;-1/1:274:-1,0,0,0,1,0,0;1/1:282:-2,0,0,0,0,0,0;1/1:284:0,0,0,0,0,0,0;-1/1:286:-1,0,0,0,1,0,0;-1/1:293:0,0,0,0,0,0,0;-1/1:297:0,0,0,0,0,0,0;-1/1:299:0,0,0,0,0,0,0;-1/1:303:0,0,0,0,0,0,0;-1/1:317:0,0,0,0,0,0,0;-1/1:327:0,0,0,0,0,0,0;-1/1:328:-2,0,0,0,0,0,0;-1/1:342:-2,0,0,0,0,0,0;-1/1:342:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-1,0,0,0,1,0,0;-1/1:354:-2,-1,0,0,0,1,0;-1/1:354:0,0,0,0,0,0,0;-1/1:363:0,0,0,0,0,0,0;-1/1:369:0,0,0,0,0,0,0;-1/1:382:-2,0,0,0,0,0,0;-1/1:383:0,0,0,0,0,0,0;-1/1:384:-1,0,0,0,1,0,0;1/1:384:0,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:388:-1,0,0,0,1,0,0;-1/1:394:-2,0,0,0,0,0,0;1/1:398:0,0,0,0,0,0,0;1/1:402:-2,0,0,0,0,0,0;1/1:402:0,0,0,0,0,0,0;-1/1:412:-2,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;1/1:432:-2,0,0,0,0,0,0;-1/1:432:0,0,0,0,0,0,0;-1/1:432:1,0,0,0,1,0,0;-1/1:444:-2,-2,0,0,0,0,0;-1/1:444:0,0,0,0,0,0,0;-1/1:454:-2,0,0,0,0,0,0;-1/1:467:0,0,0,0,0,0,0;-1/1:473:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:-1,0,0,0,1,0,0;-1/1:474:0,-1,0,0,0,1,0;2/1:474:1,0,0,0,1,0,0;-1/1:478:-2,0,0,0,0,0,0;1/1:488:-2,0,0,0,0,0,0;-1/1:562:-2,0,0,0,0,0,0;1/1:572:-2,0,0,0,0,0,0;1/1:572:0,0,0,0,0,0,0;1/1:576:-2,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:1,-2,0,0,1,0,0;1/1:576:1,0,0,0,1,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;1/1:606:-2,-2,0,0,0,0,0;1/1:614:0,0,0,0,0,0,0;1/1:618:-2,-2,0,0,0,0,0;1/1:618:-2,0,0,0,0,0,0;-2/1:618:0,0,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:624:-4,-2,0,0,0,0,0;-1/1:624:-3,-2,0,0,1,0,0;2/1:624:-1,-2,0,0,1,0,0;-1/1:639:0,0,0,0,0,0,0;1/1:642:0,0,0,0,0,0,0;-1/1:646:-1,0,0,0,1,0,0;1/1:648:-2,0,0,0,0,0,0;1/1:648:0,0,0,0,0,0,0;-1/1:652:-2,0,0,0,0,0,0;1/1:662:0,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;1/1:666:-2,0,0,0,0,0,0;1/1:668:0,0,0,0,0,0,0;-1/1:677:0,0,0,0,0,0,0;-2/1:688:-2,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0;-1/1:694:-1,0,0,0,1,0,0;-1/1:696:-2,-1,0,0,0,1,0;1/1:696:-2,0,0,0,0,0,0;2/1:696:-1,0,0,0,1,0,0;-1/1:696:0,-2,0,0,0,0,0;-1/1:702:-4,-2,0,0,0,0,0;1/1:702:-4,0,0,0,0,0,0;2/1:702:-2,0,0,0,0,0,0;-1/1:706:-2,0,0,0,0,0,0;-1/1:706:-1,0,0,0,1,0,0;1/1:708:-2,0,0,0,0,0,0;1/1:708:-1,0,0,0,1,0,0;1/1:709:0,0,0,0,0,0,0;-1/1:713:0,0,0,0,0,0,0;1/1:718:-4,0,0,0,0,0,0;-1/1:718:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;1/1:722:-2,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;1/1:727:0,0,0,0,0,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:747:0,0,0,0,0,0,0;-1/1:748:-2,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;2/1:768:-2,0,0,0,0,0,0;-1/1:768:-1,0,0,0,1,0,0;-1/1:768:0,-2,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;1/1:776:-2,0,0,0,0,0,0;-1/1:778:-2,0,0,0,0,0,0;-1/1:778:-1,0,0,0,1,0,0;1/1:782:0,0,0,0,0,0,0;1/1:786:-2,0,0,0,0,0,0;1/1:788:0,0,0,0,0,0,0;1/1:794:0,0,0,0,0,0,0;-2/1:796:-1,0,0,0,1,0,0;-1/1:802:-2,0,0,0,0,0,0;-1/1:803:0,0,0,0,0,0,0;-1/1:804:-1,0,0,0,1,0,0;1/1:804:0,0,0,0,0,0,0;-1/1:814:-2,0,0,0,0,0,0;1/1:818:-2,0,0,0,0,0,0;2/1:822:-2,0,0,0,0,0,0;-1/1:832:-2,0,0,0,0,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:834:-1,0,0,0,1,0,0;-1/1:837:0,0,0,0,0,0,0;-1/1:843:0,0,0,0,0,0,0;-1/1:849:0,0,0,0,0,0,0;-1/1:857:0,0,0,0,0,0,0;-1/1:858:-2,0,0,0,0,0,0;-1/1:858:-1,0,0,0,1,0,0;-1/1:862:-2,0,0,0,0,0,0;-1/1:863:0,0,0,0,0,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:-1,0,0,0,1,0,0;-1/1:864:0,0,0,0,0,0,0;1/1:864:0,0,0,0,2,0,0;-1/1:867:0,0,0,0,0,0,0;1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-3,0,0,0,1,0,0;-1/1:876:-2,0,0,0,0,0,0;1/1:878:-1,0,0,0,1,0,0;1/1:878:0,0,0,0,0,0,0;-1/1:884:-3,0,0,0,1,0,0;1/1:884:-2,0,0,0,0,0,0;-1/1:887:0,0,0,0,0,0,0;1/1:888:-2,-2,0,0,0,0,0;1/1:888:-1,0,0,0,1,0,0;-1/1:888:0,0,0,0,0,0,0;-1/1:893:0,0,0,0,0,0,0;1/1:897:0,-2,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;-1/1:904:-2,0,0,0,0,0,0;1/1:906:-2,-2,0,0,0,0,0;1/1:906:-2,0,0,0,0,0,0;1/1:914:0,0,0,0,0,0,0;-1/1:928:-2,0,0,0,0,0,0;-1/1:929:0,0,0,0,0,0,0;1/1:932:-2,0,0,0,0,0,0;2/1:934:-3,0,0,0,1,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-2,0,0,0,0,0,0;-1/1:947:0,0,0,0,0,0,0;1/1:951:0,-2,0,0,0,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:958:-1,0,0,0,1,0,0;-1/1:977:0,0,0,0,0,0,0;-1/1:983:0,0,0,0,0,0,0;1/1:986:-2,0,0,0,0,0,0;-1/1:988:-2,0,0,0,0,0,0;-1/1:989:0,0,0,0,0,0,0;1/1:992:-2,0,0,0,0,0,0;-2/1:992:-2,0,0,0,2,0,0;1/1:998:-2,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:1013:0,0,0,0,0,0,0;1/1:1016:-2,0,0,0,0,0,0;-2/1:1016:-1,0,0,0,1,0,0;-1/1:1019:0,0,0,0,0,0,0"

compact_certificate theorem operation977_suffix352 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 352)=operation977Result352 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 352 32
    operation977Result352 operation977Result384 operation977_suffix384
  decide +kernel

compact_certificate def operation977Result320 : Poly := laurent_polynomial% "-1/1:34:-2,0,0,0,0,0,0;-1/1:34:-1,0,0,0,1,0,0;-1/1:47:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:-3,0,0,0,1,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;-1/1:62:-2,0,0,0,0,0,0;-1/1:64:-2,0,0,0,0,0,0;-1/1:64:-1,0,0,0,1,0,0;-1/1:65:0,0,0,0,0,0,0;1/1:68:-2,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:76:-1,0,0,0,1,0,0;-1/1:89:0,0,0,0,0,0,0;1/1:92:-2,0,0,0,0,0,0;-1/1:107:0,0,0,0,0,0,0;-1/1:124:-2,0,0,0,0,0,0;1/1:128:-2,0,0,0,0,0,0;-1/1:142:-2,0,0,0,0,0,0;-1/1:143:0,0,0,0,0,0,0;-1/1:144:-2,-2,0,0,0,0,0;-1/1:148:-2,0,0,0,0,0,0;-1/1:149:0,0,0,0,0,0,0;1/1:152:-2,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;-1/1:159:0,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,0,0,0;-1/1:167:0,0,0,0,0,0,0;1/1:172:-4,0,0,0,0,0,0;1/1:172:-3,0,0,0,1,0,0;-1/1:172:-2,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:177:0,0,0,0,0,0,0;-1/1:186:-4,0,0,0,0,0,0;-1/1:186:-3,0,0,0,1,0,0;1/1:186:-1,0,0,0,1,0,0;1/1:192:-2,0,0,0,0,0,0;-1/1:198:-2,0,0,0,0,0,0;-1/1:202:-2,0,0,0,0,0,0;-1/1:207:0,0,0,0,0,0,0;-1/1:208:-2,0,0,0,0,0,0;-1/1:209:0,0,0,0,0,0,0;-1/1:213:0,0,0,0,0,0,0;-1/1:214:-2,0,0,0,0,0,0;1/1:216:-2,0,0,0,0,0,0;-1/1:216:-1,0,0,0,1,0,0;-1/1:219:0,0,0,0,0,0,0;-1/1:227:0,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-1/1:234:-1,0,0,0,1,0,0;1/1:234:0,0,0,0,0,0,0;1/1:242:0,0,0,0,0,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:246:-1,0,0,0,1,0,0;1/1:254:0,0,0,0,0,0,0;-1/1:258:-2,0,0,0,0,0,0;-1/1:258:-1,0,0,0,1,0,0;1/1:258:0,0,0,0,0,0,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:-1,0,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;1/1:264:0,0,0,0,0,0,0;-1/1:268:-2,0,0,0,0,0,0;1/1:272:0,0,0,0,0,0,0;-1/1:274:-2,0,0,0,0,0,0;-1/1:274:-1,0,0,0,1,0,0;1/1:282:-2,0,0,0,0,0,0;1/1:284:0,0,0,0,0,0,0;-1/1:293:0,0,0,0,0,0,0;-1/1:297:0,0,0,0,0,0,0;-1/1:299:0,0,0,0,0,0,0;-1/1:303:0,0,0,0,0,0,0;-1/1:317:0,0,0,0,0,0,0;-1/1:327:0,0,0,0,0,0,0;-1/1:328:-2,0,0,0,0,0,0;-1/1:342:-2,0,0,0,0,0,0;-1/1:342:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;-1/1:354:-2,-1,0,0,0,1,0;1/1:354:-1,0,0,0,1,0,0;-1/1:363:0,0,0,0,0,0,0;-1/1:369:0,0,0,0,0,0,0;-1/1:382:-2,0,0,0,0,0,0;-1/1:383:0,0,0,0,0,0,0;-1/1:384:-2,0,0,0,0,0,0;1/1:384:0,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:396:-1,0,0,0,1,0,0;1/1:398:0,0,0,0,0,0,0;1/1:402:0,0,0,0,0,0,0;-1/1:410:0,0,0,0,0,0,0;-1/1:412:-2,0,0,0,0,0,0;-1/1:414:-2,0,0,0,0,0,0;-1/1:418:-2,0,0,0,0,0,0;-1/1:419:0,0,0,0,0,0,0;-1/1:424:-2,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;1/1:432:-2,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:444:-2,-2,0,0,0,0,0;1/1:445:0,0,0,0,0,0,0;-1/1:454:-2,0,0,0,0,0,0;-1/1:467:0,0,0,0,0,0,0;-1/1:470:-2,0,0,0,0,0,0;-1/1:473:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:-1,0,0,0,1,0,0;-1/1:474:0,-1,0,0,0,1,0;2/1:474:1,0,0,0,1,0,0;-1/1:478:-2,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;-1/1:562:-2,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;1/1:576:0,0,0,0,0,0,0;-1/1:576:1,-2,0,0,1,0,0;1/1:576:1,0,0,0,1,0,0;-1/1:587:0,0,0,0,0,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:593:0,0,0,0,0,0,0;-1/1:594:-2,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;1/1:618:-2,-2,0,0,0,0,0;1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:624:-4,-2,0,0,0,0,0;-1/1:624:-3,-2,0,0,1,0,0;-1/1:624:-2,0,0,0,0,0,0;2/1:624:-1,-2,0,0,1,0,0;-1/1:628:-2,0,0,0,0,0,0;-1/1:629:0,0,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;-1/1:639:0,0,0,0,0,0,0;1/1:640:0,0,0,0,0,0,0;1/1:642:0,0,0,0,0,0,0;-1/1:646:-1,0,0,0,1,0,0;-1/1:647:0,0,0,0,0,0,0;1/1:648:0,0,0,0,0,0,0;-1/1:652:-2,0,0,0,0,0,0;-1/1:653:0,0,0,0,0,0,0;1/1:654:0,0,0,0,0,0,0;1/1:662:0,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;1/1:666:-2,0,0,0,0,0,0;-1/1:669:0,0,0,0,0,0,0;-1/1:677:0,0,0,0,0,0,0;-1/1:688:-2,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0;-1/1:696:-2,-1,0,0,0,1,0;2/1:696:-1,0,0,0,1,0,0;1/1:697:0,0,0,0,0,0,0;-1/1:699:0,0,0,0,0,0,0;-1/1:702:-4,-2,0,0,0,0,0;1/1:702:-4,0,0,0,0,0,0;1/1:702:-2,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:703:0,0,0,0,0,0,0;1/1:709:0,0,0,0,0,0,0;1/1:712:-2,0,0,0,0,0,0;-1/1:713:0,0,0,0,0,0,0;-1/1:717:0,0,0,0,0,0,0;1/1:718:-4,0,0,0,0,0,0;-1/1:718:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:719:0,0,0,0,0,0,0;1/1:722:-2,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;1/1:727:0,0,0,0,0,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:747:0,0,0,0,0,0,0;-1/1:748:-2,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;1/1:768:-2,0,0,0,0,0,0;-1/1:768:-1,0,0,0,1,0,0;-1/1:768:0,-2,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;-1/1:773:0,0,0,0,0,0,0;1/1:774:0,0,0,0,0,0,0;-1/1:778:-2,0,0,0,0,0,0;-1/1:778:-1,0,0,0,1,0,0;1/1:782:0,0,0,0,0,0,0;1/1:786:-2,0,0,0,0,0,0;1/1:788:0,0,0,0,0,0,0;-1/1:792:-2,0,0,0,0,0,0;1/1:794:0,0,0,0,0,0,0;-2/1:796:-1,0,0,0,1,0,0;-1/1:802:-2,0,0,0,0,0,0;-1/1:803:0,0,0,0,0,0,0;-1/1:804:-2,0,0,0,0,0,0;-1/1:804:-1,0,0,0,1,0,0;1/1:804:0,0,0,0,0,0,0;1/1:810:-2,-2,0,0,0,0,0;1/1:810:-2,0,0,0,0,0,0;-1/1:810:-1,-2,0,0,1,0,0;1/1:810:0,-1,0,0,0,1,0;-1/1:814:-2,0,0,0,0,0,0;-1/1:815:0,0,0,0,0,0,0;-1/1:816:-1,0,0,0,1,0,0;1/1:818:-2,0,0,0,0,0,0;2/1:822:-2,0,0,0,0,0,0;-1/1:832:-2,0,0,0,0,0,0;-1/1:834:-2,0,0,0,0,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:834:-1,0,0,0,1,0,0;-1/1:837:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:839:0,0,0,0,0,0,0;-1/1:843:0,0,0,0,0,0,0;-1/1:844:-2,0,0,0,0,0,0;-1/1:849:0,0,0,0,0,0,0;-1/1:852:-2,0,0,0,0,0,0;-1/1:857:0,0,0,0,0,0,0;-1/1:858:-2,0,0,0,0,0,0;-1/1:858:-1,0,0,0,1,0,0;-1/1:862:-2,0,0,0,0,0,0;-1/1:863:0,0,0,0,0,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;-1/1:867:0,0,0,0,0,0,0;1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-3,0,0,0,1,0,0;-1/1:876:-2,0,0,0,0,0,0;-1/1:884:-3,0,0,0,1,0,0;1/1:884:-2,0,0,0,0,0,0;-1/1:887:0,0,0,0,0,0,0;1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:893:0,0,0,0,0,0,0;1/1:897:0,-2,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;-1/1:904:-2,0,0,0,0,0,0;-1/1:905:0,0,0,0,0,0,0;1/1:906:-2,-2,0,0,0,0,0;1/1:906:-2,0,0,0,0,0,0;1/1:914:0,0,0,0,0,0,0;-1/1:928:-2,0,0,0,0,0,0;-1/1:929:0,0,0,0,0,0,0;1/1:932:-2,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:935:0,0,0,0,0,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-2,0,0,0,0,0,0;-1/1:947:0,0,0,0,0,0,0;1/1:951:0,-2,0,0,0,0,0;1/1:955:0,0,0,0,0,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:958:-1,0,0,0,1,0,0;-1/1:977:0,0,0,0,0,0,0;-1/1:983:0,0,0,0,0,0,0;1/1:986:-2,0,0,0,0,0,0;-1/1:988:-2,0,0,0,0,0,0;-1/1:989:0,0,0,0,0,0,0;-1/1:992:-2,0,0,0,2,0,0;1/1:998:-2,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:1013:0,0,0,0,0,0,0;1/1:1016:-2,0,0,0,0,0,0;-2/1:1016:-1,0,0,0,1,0,0;-1/1:1019:0,0,0,0,0,0,0"

compact_certificate theorem operation977_suffix320 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 320)=operation977Result320 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 320 32
    operation977Result320 operation977Result352 operation977_suffix352
  decide +kernel

compact_certificate def operation977Result288 : Poly := laurent_polynomial% "-1/1:34:-2,0,0,0,0,0,0;-1/1:34:-1,0,0,0,1,0,0;-1/1:47:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:-3,0,0,0,1,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;-1/1:62:-2,0,0,0,0,0,0;-1/1:64:-2,0,0,0,0,0,0;-1/1:64:-1,0,0,0,1,0,0;-1/1:65:0,0,0,0,0,0,0;1/1:68:-2,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:76:-1,0,0,0,1,0,0;-1/1:89:0,0,0,0,0,0,0;1/1:92:-2,0,0,0,0,0,0;-1/1:95:0,0,0,0,0,0,0;-1/1:107:0,0,0,0,0,0,0;-1/1:118:-2,0,0,0,0,0,0;-1/1:124:-2,0,0,0,0,0,0;1/1:128:-2,0,0,0,0,0,0;-1/1:138:-2,0,0,0,0,0,0;1/1:138:0,0,0,0,0,0,0;-1/1:142:-2,0,0,0,0,0,0;-1/1:143:0,0,0,0,0,0,0;-1/1:144:-2,0,0,0,0,0,0;-1/1:144:-1,0,0,0,1,0,0;-1/1:148:-2,0,0,0,0,0,0;-1/1:149:0,0,0,0,0,0,0;1/1:152:-2,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;-1/1:159:0,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;-1/1:167:0,0,0,0,0,0,0;1/1:172:-4,0,0,0,0,0,0;1/1:172:-3,0,0,0,1,0,0;-1/1:172:-2,0,0,0,0,0,0;-1/1:177:0,0,0,0,0,0,0;-1/1:179:0,0,0,0,0,0,0;-1/1:184:-2,0,0,0,0,0,0;1/1:192:-2,0,0,0,0,0,0;-1/1:198:-2,0,0,0,0,0,0;-1/1:202:-2,0,0,0,0,0,0;-1/1:207:0,0,0,0,0,0,0;-1/1:208:-2,0,0,0,0,0,0;-1/1:209:0,0,0,0,0,0,0;-1/1:213:0,0,0,0,0,0,0;-1/1:214:-2,0,0,0,0,0,0;1/1:216:-2,0,0,0,0,0,0;-1/1:216:-1,0,0,0,1,0,0;-1/1:219:0,0,0,0,0,0,0;-1/1:227:0,0,0,0,0,0,0;-1/1:232:-2,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-1/1:234:-1,0,0,0,1,0,0;1/1:234:0,0,0,0,0,0,0;1/1:242:0,0,0,0,0,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:246:-1,0,0,0,1,0,0;1/1:254:0,0,0,0,0,0,0;-1/1:258:-2,0,0,0,0,0,0;-1/1:258:-1,0,0,0,1,0,0;1/1:258:0,0,0,0,0,0,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:-1,0,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;1/1:264:0,0,0,0,0,0,0;-1/1:268:-2,0,0,0,0,0,0;1/1:272:0,0,0,0,0,0,0;-1/1:274:-2,0,0,0,0,0,0;-1/1:274:-1,0,0,0,1,0,0;-1/1:276:-1,0,0,0,1,0,0;1/1:282:0,0,0,0,0,0,0;1/1:284:0,0,0,0,0,0,0;-1/1:292:-2,0,0,0,0,0,0;-1/1:293:0,0,0,0,0,0,0;-1/1:297:0,0,0,0,0,0,0;-1/1:298:-2,0,0,0,0,0,0;-1/1:299:0,0,0,0,0,0,0;-1/1:303:0,0,0,0,0,0,0;-1/1:317:0,0,0,0,0,0,0;-1/1:327:0,0,0,0,0,0,0;-1/1:328:-2,0,0,0,0,0,0;-1/1:333:0,0,0,0,0,0,0;-1/1:334:-2,0,0,0,0,0,0;-1/1:339:0,0,0,0,0,0,0;-1/1:342:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:354:-2,0,0,0,0,0,0;-1/1:363:0,0,0,0,0,0,0;-1/1:369:0,0,0,0,0,0,0;-1/1:377:0,0,0,0,0,0,0;-1/1:382:-2,0,0,0,0,0,0;-1/1:383:0,0,0,0,0,0,0;-1/1:384:-2,0,0,0,0,0,0;1/1:384:0,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:396:-1,0,0,0,1,0,0;1/1:398:0,0,0,0,0,0,0;1/1:402:0,0,0,0,0,0,0;-1/1:410:0,0,0,0,0,0,0;-1/1:412:-2,0,0,0,0,0,0;-1/1:414:-2,0,0,0,0,0,0;-1/1:418:-2,0,0,0,0,0,0;-1/1:419:0,0,0,0,0,0,0;-1/1:423:0,0,0,0,0,0,0;-1/1:424:-2,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;-1/1:429:0,0,0,0,0,0,0;1/1:432:-2,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:437:0,0,0,0,0,0,0;-1/1:438:-2,0,0,0,0,0,0;-1/1:442:-2,0,0,0,0,0,0;-1/1:443:0,0,0,0,0,0,0;-1/1:453:0,0,0,0,0,0,0;-1/1:454:-2,0,0,0,0,0,0;-1/1:467:0,0,0,0,0,0,0;-1/1:470:-2,0,0,0,0,0,0;-1/1:473:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:-1,0,0,0,1,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:474:1,0,0,0,1,0,0;-1/1:478:-2,0,0,0,0,0,0;-1/1:479:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;-1/1:562:-2,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;1/1:576:0,0,0,0,0,0,0;-1/1:576:1,-2,0,0,1,0,0;1/1:576:1,0,0,0,1,0,0;-1/1:587:0,0,0,0,0,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:593:0,0,0,0,0,0,0;-1/1:594:-2,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;-1/1:605:0,0,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;1/1:618:-2,-2,0,0,0,0,0;1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:624:-2,0,0,0,0,0,0;1/1:624:-1,-2,0,0,1,0,0;-1/1:628:-2,0,0,0,0,0,0;-1/1:629:0,0,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;-1/1:639:0,0,0,0,0,0,0;1/1:640:0,0,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;1/1:642:0,0,0,0,0,0,0;-1/1:646:-1,0,0,0,1,0,0;-1/1:647:0,0,0,0,0,0,0;-1/1:648:-2,0,0,0,0,0,0;1/1:648:0,0,0,0,0,0,0;-1/1:652:-2,0,0,0,0,0,0;-1/1:653:0,0,0,0,0,0,0;1/1:654:0,0,0,0,0,0,0;1/1:662:0,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;-1/1:669:0,0,0,0,0,0,0;-1/1:677:0,0,0,0,0,0,0;-1/1:683:0,0,0,0,0,0,0;-1/1:684:-2,0,0,0,0,0,0;-1/1:688:-2,0,0,0,0,0,0;-1/1:689:0,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0;1/1:696:-1,0,0,0,1,0,0;1/1:697:0,0,0,0,0,0,0;-1/1:699:0,0,0,0,0,0,0;-1/1:702:-4,-2,0,0,0,0,0;1/1:703:0,0,0,0,0,0,0;1/1:709:0,0,0,0,0,0,0;-1/1:713:0,0,0,0,0,0,0;-1/1:717:0,0,0,0,0,0,0;-1/1:718:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:719:0,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:747:0,0,0,0,0,0,0;-1/1:748:-2,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;-1/1:768:-1,0,0,0,1,0,0;1/1:768:0,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;-1/1:773:0,0,0,0,0,0,0;-1/1:774:-2,0,0,0,0,0,0;-1/1:774:-1,0,0,0,1,0,0;1/1:774:0,0,0,0,0,0,0;-1/1:778:-2,0,0,0,0,0,0;-1/1:778:-1,0,0,0,1,0,0;1/1:782:0,0,0,0,0,0,0;1/1:786:-2,0,0,0,0,0,0;1/1:788:0,0,0,0,0,0,0;-1/1:792:-2,0,0,0,0,0,0;1/1:794:0,0,0,0,0,0,0;-2/1:796:-1,0,0,0,1,0,0;-1/1:802:-2,0,0,0,0,0,0;-1/1:803:0,0,0,0,0,0,0;-1/1:804:-2,0,0,0,0,0,0;-1/1:804:-1,0,0,0,1,0,0;1/1:804:0,0,0,0,0,0,0;1/1:810:-2,-2,0,0,0,0,0;1/1:810:-2,0,0,0,0,0,0;1/1:810:-1,-2,0,0,1,0,0;-1/1:810:0,-1,0,0,0,1,0;-1/1:814:-2,0,0,0,0,0,0;-1/1:815:0,0,0,0,0,0,0;-1/1:816:-1,0,0,0,1,0,0;1/1:822:-2,0,0,0,0,0,0;-1/1:832:-2,0,0,0,0,0,0;-1/1:834:-2,0,0,0,0,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:834:-1,0,0,0,1,0,0;-1/1:837:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:839:0,0,0,0,0,0,0;-1/1:843:0,0,0,0,0,0,0;-1/1:844:-2,0,0,0,0,0,0;-1/1:849:0,0,0,0,0,0,0;-1/1:852:-2,0,0,0,0,0,0;-1/1:857:0,0,0,0,0,0,0;-1/1:858:-2,0,0,0,0,0,0;-1/1:862:-2,0,0,0,0,0,0;-1/1:863:0,0,0,0,0,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;-1/1:867:0,0,0,0,0,0,0;1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-2,0,0,0,0,0,0;-1/1:879:0,0,0,0,0,0,0;1/1:886:-4,0,0,0,0,0,0;1/1:886:-3,0,0,0,1,0,0;-1/1:887:0,0,0,0,0,0,0;1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:893:0,0,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;-1/1:904:-2,0,0,0,0,0,0;-1/1:905:0,0,0,0,0,0,0;1/1:906:-2,0,0,0,0,0,0;-1/1:912:-2,0,0,0,0,0,0;1/1:912:0,0,0,0,0,0,0;1/1:914:0,0,0,0,0,0,0;-1/1:922:-2,0,0,0,0,0,0;-1/1:928:-2,0,0,0,0,0,0;-1/1:929:0,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:935:0,0,0,0,0,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-2,0,0,0,0,0,0;1/1:936:-1,0,0,0,1,0,0;-1/1:947:0,0,0,0,0,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:977:0,0,0,0,0,0,0;-1/1:983:0,0,0,0,0,0,0;1/1:986:-2,0,0,0,0,0,0;-1/1:988:-2,0,0,0,0,0,0;-1/1:989:0,0,0,0,0,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:993:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:1013:0,0,0,0,0,0,0;1/1:1016:-2,0,0,0,0,0,0;-2/1:1016:-1,0,0,0,1,0,0;-1/1:1019:0,0,0,0,0,0,0"

compact_certificate theorem operation977_suffix288 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 288)=operation977Result288 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 288 32
    operation977Result288 operation977Result320 operation977_suffix320
  decide +kernel

compact_certificate def operation977Result256 : Poly := laurent_polynomial% "-1/1:17:0,0,0,0,0,0,0;-1/1:34:-2,0,0,0,0,0,0;-1/1:47:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;-1/1:62:-2,0,0,0,0,0,0;-1/1:64:-2,0,0,0,0,0,0;-1/1:65:0,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:89:0,0,0,0,0,0,0;1/1:92:-2,0,0,0,0,0,0;-1/1:95:0,0,0,0,0,0,0;-1/1:107:0,0,0,0,0,0,0;-1/1:114:-2,0,0,0,0,0,0;-1/1:117:0,0,0,0,0,0,0;-1/1:118:-2,0,0,0,0,0,0;-1/1:123:0,0,0,0,0,0,0;-1/1:124:-2,0,0,0,0,0,0;-1/1:129:0,0,0,0,0,0,0;-1/1:137:0,0,0,0,0,0,0;-1/1:138:-2,0,0,0,0,0,0;-1/1:142:-2,0,0,0,0,0,0;-1/1:143:0,0,0,0,0,0,0;-1/1:144:-2,0,0,0,0,0,0;-1/1:148:-2,0,0,0,0,0,0;-1/1:149:0,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;-1/1:159:0,0,0,0,0,0,0;-1/1:160:-2,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;-1/1:167:0,0,0,0,0,0,0;1/1:172:-4,0,0,0,0,0,0;-1/1:172:-2,0,0,0,0,0,0;-1/1:177:0,0,0,0,0,0,0;-1/1:179:0,0,0,0,0,0,0;-1/1:184:-2,0,0,0,0,0,0;1/1:192:-2,0,0,0,0,0,0;-1/1:198:-2,0,0,0,0,0,0;-1/1:202:-2,0,0,0,0,0,0;-1/1:207:0,0,0,0,0,0,0;-1/1:208:-2,0,0,0,0,0,0;-1/1:209:0,0,0,0,0,0,0;-1/1:213:0,0,0,0,0,0,0;-1/1:214:-2,0,0,0,0,0,0;1/1:216:-2,0,0,0,0,0,0;-1/1:219:0,0,0,0,0,0,0;-1/1:222:-2,0,0,0,0,0,0;-1/1:227:0,0,0,0,0,0,0;-1/1:228:-2,0,0,0,0,0,0;-1/1:232:-2,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-1/1:237:0,0,0,0,0,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:258:-2,0,0,0,0,0,0;1/1:258:0,0,0,0,0,0,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:-1,0,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;1/1:264:0,0,0,0,0,0,0;-1/1:268:-2,0,0,0,0,0,0;-1/1:269:0,0,0,0,0,0,0;1/1:272:0,0,0,0,0,0,0;-1/1:274:-2,0,0,0,0,0,0;1/1:282:0,0,0,0,0,0,0;-1/1:292:-2,0,0,0,0,0,0;-1/1:293:0,0,0,0,0,0,0;-1/1:297:0,0,0,0,0,0,0;-1/1:298:-2,0,0,0,0,0,0;-1/1:299:0,0,0,0,0,0,0;-1/1:303:0,0,0,0,0,0,0;-1/1:317:0,0,0,0,0,0,0;-1/1:324:-2,0,0,0,0,0,0;-1/1:327:0,0,0,0,0,0,0;-1/1:328:-2,0,0,0,0,0,0;-1/1:333:0,0,0,0,0,0,0;-1/1:334:-2,0,0,0,0,0,0;-1/1:339:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:354:-2,0,0,0,0,0,0;-1/1:363:0,0,0,0,0,0,0;-1/1:369:0,0,0,0,0,0,0;-1/1:372:-2,0,0,0,0,0,0;-1/1:377:0,0,0,0,0,0,0;-1/1:382:-2,0,0,0,0,0,0;-1/1:383:0,0,0,0,0,0,0;-1/1:384:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:387:0,0,0,0,0,0,0;-1/1:389:0,0,0,0,0,0,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:395:0,0,0,0,0,0,0;-1/1:396:-1,0,0,0,1,0,0;-1/1:408:-2,0,0,0,0,0,0;-1/1:408:0,0,0,0,0,0,0;-1/1:410:0,0,0,0,0,0,0;-1/1:412:-2,0,0,0,0,0,0;-1/1:414:-2,0,0,0,0,0,0;-1/1:417:0,0,0,0,0,0,0;-1/1:418:-2,0,0,0,0,0,0;-1/1:419:0,0,0,0,0,0,0;-1/1:423:0,0,0,0,0,0,0;-1/1:424:-2,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;-1/1:429:0,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:437:0,0,0,0,0,0,0;-1/1:438:-2,0,0,0,0,0,0;-1/1:442:-2,0,0,0,0,0,0;-1/1:443:0,0,0,0,0,0,0;-1/1:453:0,0,0,0,0,0,0;-1/1:454:-2,0,0,0,0,0,0;-1/1:467:0,0,0,0,0,0,0;-1/1:473:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:474:1,0,0,0,1,0,0;-1/1:478:-2,0,0,0,0,0,0;-1/1:479:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;-1/1:557:0,0,0,0,0,0,0;-1/1:562:-2,0,0,0,0,0,0;-1/1:563:0,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;1/1:576:0,0,0,0,0,0,0;-1/1:576:1,-2,0,0,1,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:587:0,0,0,0,0,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:593:0,0,0,0,0,0,0;-1/1:594:-2,0,0,0,0,0,0;-1/1:597:0,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;-1/1:605:0,0,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:624:-2,0,0,0,0,0,0;1/1:624:-1,-2,0,0,1,0,0;-1/1:627:0,0,0,0,0,0,0;-1/1:628:-2,0,0,0,0,0,0;-1/1:629:0,0,0,0,0,0,0;-1/1:633:0,0,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;-1/1:639:0,0,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;-1/1:646:-1,0,0,0,1,0,0;-1/1:647:0,0,0,0,0,0,0;-1/1:648:-2,0,0,0,0,0,0;-1/1:652:-2,0,0,0,0,0,0;-1/1:653:0,0,0,0,0,0,0;-1/1:663:0,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;-1/1:669:0,0,0,0,0,0,0;-1/1:677:0,0,0,0,0,0,0;-1/1:678:-2,0,0,0,0,0,0;-1/1:683:0,0,0,0,0,0,0;-1/1:684:-2,0,0,0,0,0,0;-1/1:688:-2,0,0,0,0,0,0;-1/1:689:0,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0;1/1:696:-1,0,0,0,1,0,0;1/1:697:0,0,0,0,0,0,0;-1/1:699:0,0,0,0,0,0,0;-1/1:702:-4,-2,0,0,0,0,0;1/1:703:0,0,0,0,0,0,0;1/1:708:-2,0,0,0,0,0,0;1/1:709:0,0,0,0,0,0,0;-1/1:713:0,0,0,0,0,0,0;-1/1:717:0,0,0,0,0,0,0;-1/1:718:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:719:0,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;-1/1:730:-2,0,0,0,0,0,0;-1/1:737:0,0,0,0,0,0,0;1/1:738:-2,0,0,0,0,0,0;-1/1:744:-2,0,0,0,0,0,0;-1/1:747:0,0,0,0,0,0,0;-1/1:748:-2,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;-1/1:759:0,0,0,0,0,0,0;-1/1:767:0,0,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;1/1:768:0,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;-1/1:773:0,0,0,0,0,0,0;-1/1:774:-2,0,0,0,0,0,0;1/1:774:0,0,0,0,0,0,0;-1/1:778:-2,0,0,0,0,0,0;-1/1:779:0,0,0,0,0,0,0;1/1:782:0,0,0,0,0,0,0;1/1:786:-2,0,0,0,0,0,0;1/1:788:0,0,0,0,0,0,0;-1/1:792:-2,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;-1/1:802:-2,0,0,0,0,0,0;-1/1:803:0,0,0,0,0,0,0;-1/1:804:-2,0,0,0,0,0,0;1/1:804:0,0,0,0,0,0,0;-1/1:809:0,0,0,0,0,0,0;1/1:810:-2,-2,0,0,0,0,0;-1/1:810:0,-1,0,0,0,1,0;-1/1:814:-2,0,0,0,0,0,0;-1/1:815:0,0,0,0,0,0,0;-1/1:828:-2,0,0,0,0,0,0;-1/1:832:-2,0,0,0,0,0,0;-1/1:834:-2,0,0,0,0,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:837:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:839:0,0,0,0,0,0,0;-1/1:843:0,0,0,0,0,0,0;-1/1:844:-2,0,0,0,0,0,0;-1/1:849:0,0,0,0,0,0,0;-1/1:852:-2,0,0,0,0,0,0;-1/1:857:0,0,0,0,0,0,0;-1/1:858:-2,0,0,0,0,0,0;-1/1:862:-2,0,0,0,0,0,0;-1/1:863:0,0,0,0,0,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;-1/1:867:0,0,0,0,0,0,0;1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-2,0,0,0,0,0,0;-1/1:879:0,0,0,0,0,0,0;1/1:886:-4,0,0,0,0,0,0;-1/1:887:0,0,0,0,0,0,0;1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;1/1:890:-2,0,0,0,0,0,0;-1/1:893:0,0,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;-1/1:904:-2,0,0,0,0,0,0;-1/1:905:0,0,0,0,0,0,0;1/1:906:-2,0,0,0,0,0,0;-1/1:909:0,0,0,0,0,0,0;-1/1:912:-2,0,0,0,0,0,0;-1/1:922:-2,0,0,0,0,0,0;-1/1:923:0,0,0,0,0,0,0;-1/1:927:0,0,0,0,0,0,0;-1/1:928:-2,0,0,0,0,0,0;-1/1:929:0,0,0,0,0,0,0;-1/1:933:0,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:935:0,0,0,0,0,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0;-1/1:940:-2,0,0,0,0,0,0;-1/1:947:0,0,0,0,0,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:977:0,0,0,0,0,0,0;-1/1:983:0,0,0,0,0,0,0;1/1:986:-2,0,0,0,0,0,0;-1/1:988:-2,0,0,0,0,0,0;-1/1:989:0,0,0,0,0,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:993:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:1013:0,0,0,0,0,0,0;-2/1:1016:-1,0,0,0,1,0,0;-1/1:1019:0,0,0,0,0,0,0"

compact_certificate theorem operation977_suffix256 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 256)=operation977Result256 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 256 32
    operation977Result256 operation977Result288 operation977_suffix288
  decide +kernel

compact_certificate def operation977Result224 : Poly := laurent_polynomial% "-1/1:17:0,0,0,0,0,0,0;-1/1:34:-2,0,0,0,0,0,0;-1/1:47:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;-1/1:62:-2,0,0,0,0,0,0;-1/1:64:-2,0,0,0,0,0,0;-1/1:65:0,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:89:0,0,0,0,0,0,0;1/1:92:-2,0,0,0,0,0,0;-1/1:95:0,0,0,0,0,0,0;-1/1:107:0,0,0,0,0,0,0;-1/1:114:-2,0,0,0,0,0,0;-1/1:117:0,0,0,0,0,0,0;-1/1:118:-2,0,0,0,0,0,0;-1/1:123:0,0,0,0,0,0,0;-1/1:124:-2,0,0,0,0,0,0;-1/1:129:0,0,0,0,0,0,0;-1/1:137:0,0,0,0,0,0,0;-1/1:138:-2,0,0,0,0,0,0;-1/1:142:-2,0,0,0,0,0,0;-1/1:143:0,0,0,0,0,0,0;-1/1:144:-2,0,0,0,0,0,0;-1/1:148:-2,0,0,0,0,0,0;-1/1:149:0,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;-1/1:159:0,0,0,0,0,0,0;-1/1:160:-2,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;-1/1:167:0,0,0,0,0,0,0;1/1:172:-4,0,0,0,0,0,0;-1/1:172:-2,0,0,0,0,0,0;-1/1:173:0,0,0,0,0,0,0;-1/1:177:0,0,0,0,0,0,0;-1/1:179:0,0,0,0,0,0,0;-1/1:184:-2,0,0,0,0,0,0;-1/1:185:0,0,0,0,0,0,0;1/1:192:-2,0,0,0,0,0,0;-1/1:198:-2,0,0,0,0,0,0;-1/1:202:-2,0,0,0,0,0,0;-1/1:207:0,0,0,0,0,0,0;-1/1:208:-2,0,0,0,0,0,0;-1/1:209:0,0,0,0,0,0,0;-1/1:213:0,0,0,0,0,0,0;-1/1:214:-2,0,0,0,0,0,0;-1/1:215:0,0,0,0,0,0,0;1/1:216:-2,0,0,0,0,0,0;-1/1:219:0,0,0,0,0,0,0;-1/1:222:-2,0,0,0,0,0,0;-1/1:227:0,0,0,0,0,0,0;-1/1:228:-2,0,0,0,0,0,0;-1/1:232:-2,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-1/1:237:0,0,0,0,0,0,0;-1/1:243:0,0,0,0,0,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:249:0,0,0,0,0,0,0;-1/1:257:0,0,0,0,0,0,0;-1/1:258:-2,0,0,0,0,0,0;-1/1:263:0,0,0,0,0,0,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:-1,0,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;-1/1:268:-2,0,0,0,0,0,0;-1/1:269:0,0,0,0,0,0,0;-1/1:274:-2,0,0,0,0,0,0;-1/1:279:0,0,0,0,0,0,0;-1/1:288:-2,0,0,0,0,0,0;-1/1:292:-2,0,0,0,0,0,0;-1/1:293:0,0,0,0,0,0,0;-1/1:297:0,0,0,0,0,0,0;-1/1:298:-2,0,0,0,0,0,0;-1/1:299:0,0,0,0,0,0,0;-1/1:303:0,0,0,0,0,0,0;-1/1:305:0,0,0,0,0,0,0;-1/1:310:-2,0,0,0,0,0,0;-1/1:317:0,0,0,0,0,0,0;-1/1:324:-2,0,0,0,0,0,0;-1/1:327:0,0,0,0,0,0,0;-1/1:328:-2,0,0,0,0,0,0;-1/1:333:0,0,0,0,0,0,0;-1/1:334:-2,0,0,0,0,0,0;-1/1:335:0,0,0,0,0,0,0;-1/1:339:0,0,0,0,0,0,0;-1/1:342:-2,0,0,0,0,0,0;-1/1:347:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:353:0,0,0,0,0,0,0;-1/1:354:-2,0,0,0,0,0,0;-1/1:358:-2,0,0,0,0,0,0;-1/1:359:0,0,0,0,0,0,0;-1/1:363:0,0,0,0,0,0,0;-1/1:369:0,0,0,0,0,0,0;-1/1:372:-2,0,0,0,0,0,0;-1/1:377:0,0,0,0,0,0,0;-1/1:382:-2,0,0,0,0,0,0;-1/1:383:0,0,0,0,0,0,0;-1/1:384:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:387:0,0,0,0,0,0,0;-1/1:389:0,0,0,0,0,0,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:395:0,0,0,0,0,0,0;-1/1:396:-1,0,0,0,1,0,0;-1/1:408:-2,0,0,0,0,0,0;-1/1:408:0,0,0,0,0,0,0;-1/1:412:-2,0,0,0,0,0,0;-1/1:414:-2,0,0,0,0,0,0;-1/1:417:0,0,0,0,0,0,0;-1/1:418:-2,0,0,0,0,0,0;-1/1:419:0,0,0,0,0,0,0;-1/1:423:0,0,0,0,0,0,0;-1/1:424:-2,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;-1/1:429:0,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:437:0,0,0,0,0,0,0;-1/1:438:-2,0,0,0,0,0,0;-1/1:442:-2,0,0,0,0,0,0;-1/1:443:0,0,0,0,0,0,0;-1/1:447:0,0,0,0,0,0,0;-1/1:453:0,0,0,0,0,0,0;-1/1:454:-2,0,0,0,0,0,0;-1/1:459:0,0,0,0,0,0,0;-1/1:467:0,0,0,0,0,0,0;-1/1:473:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:474:1,0,0,0,1,0,0;-1/1:478:-2,0,0,0,0,0,0;-1/1:479:0,0,0,0,0,0,0;-1/1:484:-2,0,0,0,0,0,0;-1/1:485:0,0,0,0,0,0,0;-1/1:489:0,0,0,0,0,0,0;-1/1:509:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;-1/1:557:0,0,0,0,0,0,0;-1/1:562:-2,0,0,0,0,0,0;-1/1:563:0,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;1/1:576:0,0,0,0,0,0,0;-1/1:576:1,-2,0,0,1,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:587:0,0,0,0,0,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:593:0,0,0,0,0,0,0;-1/1:594:-2,0,0,0,0,0,0;-1/1:597:0,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;-1/1:605:0,0,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:624:-2,0,0,0,0,0,0;1/1:624:-1,-2,0,0,1,0,0;-1/1:627:0,0,0,0,0,0,0;-1/1:628:-2,0,0,0,0,0,0;-1/1:629:0,0,0,0,0,0,0;-1/1:633:0,0,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;-1/1:635:0,0,0,0,0,0,0;-1/1:639:0,0,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;-1/1:646:-1,0,0,0,1,0,0;-1/1:647:0,0,0,0,0,0,0;-1/1:648:-2,0,0,0,0,0,0;-1/1:652:-2,0,0,0,0,0,0;-1/1:653:0,0,0,0,0,0,0;-1/1:663:0,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;-1/1:669:0,0,0,0,0,0,0;-1/1:677:0,0,0,0,0,0,0;-1/1:678:-2,0,0,0,0,0,0;-1/1:683:0,0,0,0,0,0,0;-1/1:684:-2,0,0,0,0,0,0;-1/1:688:-2,0,0,0,0,0,0;-1/1:689:0,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0;1/1:696:-1,0,0,0,1,0,0;-1/1:699:0,0,0,0,0,0,0;-1/1:702:-4,-2,0,0,0,0,0;-1/1:708:-2,0,0,0,0,0,0;-1/1:713:0,0,0,0,0,0,0;-1/1:717:0,0,0,0,0,0,0;-1/1:718:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:719:0,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;-1/1:730:-2,0,0,0,0,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:744:-2,0,0,0,0,0,0;-1/1:747:0,0,0,0,0,0,0;-1/1:748:-2,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;-1/1:755:0,0,0,0,0,0,0;-1/1:759:0,0,0,0,0,0,0;-1/1:762:-2,0,0,0,0,0,0;-1/1:767:0,0,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;-1/1:773:0,0,0,0,0,0,0;-1/1:774:-2,0,0,0,0,0,0;-1/1:778:-2,0,0,0,0,0,0;-1/1:779:0,0,0,0,0,0,0;-1/1:783:0,0,0,0,0,0,0;-1/1:789:0,0,0,0,0,0,0;-1/1:790:-2,0,0,0,0,0,0;-1/1:792:-2,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;-1/1:797:0,0,0,0,0,0,0;-1/1:802:-2,0,0,0,0,0,0;-1/1:803:0,0,0,0,0,0,0;-1/1:804:-2,0,0,0,0,0,0;-1/1:807:0,0,0,0,0,0,0;-1/1:809:0,0,0,0,0,0,0;-1/1:814:-2,0,0,0,0,0,0;-1/1:815:0,0,0,0,0,0,0;-1/1:828:-2,0,0,0,0,0,0;-1/1:832:-2,0,0,0,0,0,0;-1/1:834:-2,0,0,0,0,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:837:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:839:0,0,0,0,0,0,0;-1/1:843:0,0,0,0,0,0,0;-1/1:844:-2,0,0,0,0,0,0;-1/1:845:0,0,0,0,0,0,0;-1/1:849:0,0,0,0,0,0,0;-1/1:852:-2,0,0,0,0,0,0;-1/1:857:0,0,0,0,0,0,0;-1/1:858:-2,0,0,0,0,0,0;-1/1:862:-2,0,0,0,0,0,0;-1/1:863:0,0,0,0,0,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;-1/1:867:0,0,0,0,0,0,0;-1/1:873:0,0,0,0,0,0,0;1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-2,0,0,0,0,0,0;-1/1:879:0,0,0,0,0,0,0;-1/1:887:0,0,0,0,0,0,0;1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:893:0,0,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;-1/1:904:-2,0,0,0,0,0,0;-1/1:905:0,0,0,0,0,0,0;-1/1:909:0,0,0,0,0,0,0;-1/1:912:-2,0,0,0,0,0,0;-1/1:922:-2,0,0,0,0,0,0;-1/1:923:0,0,0,0,0,0,0;-1/1:927:0,0,0,0,0,0,0;-1/1:928:-2,0,0,0,0,0,0;-1/1:929:0,0,0,0,0,0,0;-1/1:933:0,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:935:0,0,0,0,0,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0;-1/1:940:-2,0,0,0,0,0,0;-1/1:947:0,0,0,0,0,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:977:0,0,0,0,0,0,0;-1/1:982:-2,0,0,0,0,0,0;-1/1:983:0,0,0,0,0,0,0;-1/1:988:-2,0,0,0,0,0,0;-1/1:989:0,0,0,0,0,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:993:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:1013:0,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0;-1/1:1019:0,0,0,0,0,0,0"

compact_certificate theorem operation977_suffix224 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 224)=operation977Result224 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 224 32
    operation977Result224 operation977Result256 operation977_suffix256
  decide +kernel

compact_certificate def operation977Result192 : Poly := laurent_polynomial% "-1/1:17:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;-1/1:34:-2,0,0,0,0,0,0;-1/1:47:0,0,0,0,0,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;-1/1:62:-2,0,0,0,0,0,0;-1/1:64:-2,0,0,0,0,0,0;-1/1:65:0,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:89:0,0,0,0,0,0,0;-1/1:95:0,0,0,0,0,0,0;-1/1:107:0,0,0,0,0,0,0;-1/1:114:-2,0,0,0,0,0,0;-1/1:117:0,0,0,0,0,0,0;-1/1:118:-2,0,0,0,0,0,0;-1/1:119:0,0,0,0,0,0,0;-1/1:123:0,0,0,0,0,0,0;-1/1:124:-2,0,0,0,0,0,0;-1/1:125:0,0,0,0,0,0,0;-1/1:129:0,0,0,0,0,0,0;-1/1:130:-2,0,0,0,0,0,0;-1/1:135:0,0,0,0,0,0,0;-1/1:137:0,0,0,0,0,0,0;-1/1:138:-2,0,0,0,0,0,0;-1/1:142:-2,0,0,0,0,0,0;-1/1:143:0,0,0,0,0,0,0;-1/1:144:-2,0,0,0,0,0,0;-1/1:148:-2,0,0,0,0,0,0;-1/1:149:0,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;-1/1:159:0,0,0,0,0,0,0;-1/1:160:-2,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;-1/1:165:0,0,0,0,0,0,0;-1/1:167:0,0,0,0,0,0,0;-1/1:172:-2,0,0,0,0,0,0;-1/1:173:0,0,0,0,0,0,0;-1/1:174:-2,0,0,0,0,0,0;-1/1:177:0,0,0,0,0,0,0;-1/1:179:0,0,0,0,0,0,0;-1/1:184:-2,0,0,0,0,0,0;-1/1:185:0,0,0,0,0,0,0;-1/1:190:-2,0,0,0,0,0,0;-1/1:195:0,0,0,0,0,0,0;-1/1:198:-2,0,0,0,0,0,0;-1/1:202:-2,0,0,0,0,0,0;-1/1:204:-2,0,0,0,0,0,0;-1/1:207:0,0,0,0,0,0,0;-1/1:208:-2,0,0,0,0,0,0;-1/1:209:0,0,0,0,0,0,0;-1/1:213:0,0,0,0,0,0,0;-1/1:214:-2,0,0,0,0,0,0;-1/1:215:0,0,0,0,0,0,0;-1/1:219:0,0,0,0,0,0,0;-1/1:222:-2,0,0,0,0,0,0;-1/1:227:0,0,0,0,0,0,0;-1/1:228:-2,0,0,0,0,0,0;-1/1:232:-2,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-1/1:237:0,0,0,0,0,0,0;-1/1:238:-2,0,0,0,0,0,0;-1/1:240:-2,0,0,0,0,0,0;-1/1:243:0,0,0,0,0,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:249:0,0,0,0,0,0,0;-1/1:250:-2,0,0,0,0,0,0;-1/1:257:0,0,0,0,0,0,0;-1/1:258:-2,0,0,0,0,0,0;-1/1:263:0,0,0,0,0,0,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;-1/1:268:-2,0,0,0,0,0,0;-1/1:269:0,0,0,0,0,0,0;-1/1:274:-2,0,0,0,0,0,0;-1/1:279:0,0,0,0,0,0,0;-1/1:285:0,0,0,0,0,0,0;-1/1:288:-2,0,0,0,0,0,0;-1/1:292:-2,0,0,0,0,0,0;-1/1:293:0,0,0,0,0,0,0;-1/1:297:0,0,0,0,0,0,0;-1/1:298:-2,0,0,0,0,0,0;-1/1:299:0,0,0,0,0,0,0;-1/1:303:0,0,0,0,0,0,0;-1/1:305:0,0,0,0,0,0,0;-1/1:310:-2,0,0,0,0,0,0;-1/1:312:-2,0,0,0,0,0,0;-1/1:317:0,0,0,0,0,0,0;-1/1:324:-2,0,0,0,0,0,0;-1/1:327:0,0,0,0,0,0,0;-1/1:328:-2,0,0,0,0,0,0;-1/1:329:0,0,0,0,0,0,0;-1/1:333:0,0,0,0,0,0,0;-1/1:334:-2,0,0,0,0,0,0;-1/1:335:0,0,0,0,0,0,0;-1/1:339:0,0,0,0,0,0,0;-1/1:342:-2,0,0,0,0,0,0;-1/1:347:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:352:-2,0,0,0,0,0,0;-1/1:353:0,0,0,0,0,0,0;-1/1:354:-2,0,0,0,0,0,0;-1/1:358:-2,0,0,0,0,0,0;-1/1:359:0,0,0,0,0,0,0;-1/1:363:0,0,0,0,0,0,0;-1/1:369:0,0,0,0,0,0,0;-1/1:372:-2,0,0,0,0,0,0;-1/1:377:0,0,0,0,0,0,0;-1/1:382:-2,0,0,0,0,0,0;-1/1:383:0,0,0,0,0,0,0;-1/1:384:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:387:0,0,0,0,0,0,0;-1/1:389:0,0,0,0,0,0,0;-1/1:390:-2,0,0,0,0,0,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:395:0,0,0,0,0,0,0;-1/1:396:-1,0,0,0,1,0,0;-1/1:405:0,0,0,0,0,0,0;-1/1:408:-2,0,0,0,0,0,0;-1/1:408:0,0,0,0,0,0,0;-1/1:412:-2,0,0,0,0,0,0;-1/1:414:-2,0,0,0,0,0,0;-1/1:417:0,0,0,0,0,0,0;-1/1:418:-2,0,0,0,0,0,0;-1/1:419:0,0,0,0,0,0,0;-1/1:423:0,0,0,0,0,0,0;-1/1:424:-2,0,0,0,0,0,0;-1/1:425:0,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;-1/1:429:0,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:437:0,0,0,0,0,0,0;-1/1:438:-2,0,0,0,0,0,0;-1/1:442:-2,0,0,0,0,0,0;-1/1:443:0,0,0,0,0,0,0;-1/1:447:0,0,0,0,0,0,0;-1/1:448:-2,0,0,0,0,0,0;-1/1:453:0,0,0,0,0,0,0;-1/1:454:-2,0,0,0,0,0,0;-1/1:459:0,0,0,0,0,0,0;-1/1:460:-2,0,0,0,0,0,0;-1/1:465:0,0,0,0,0,0,0;-1/1:467:0,0,0,0,0,0,0;-1/1:473:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:474:1,0,0,0,1,0,0;-1/1:478:-2,0,0,0,0,0,0;-1/1:479:0,0,0,0,0,0,0;-1/1:484:-2,0,0,0,0,0,0;-1/1:485:0,0,0,0,0,0,0;-1/1:489:0,0,0,0,0,0,0;-1/1:509:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;-1/1:538:-2,0,0,0,0,0,0;-1/1:557:0,0,0,0,0,0,0;-1/1:562:-2,0,0,0,0,0,0;-1/1:563:0,0,0,0,0,0,0;-1/1:568:-2,0,0,0,0,0,0;-1/1:569:0,0,0,0,0,0,0;-1/1:573:0,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:1,-2,0,0,1,0,0;-1/1:579:0,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:585:0,0,0,0,0,0,0;-1/1:587:0,0,0,0,0,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:593:0,0,0,0,0,0,0;-1/1:594:-2,0,0,0,0,0,0;-1/1:597:0,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;-1/1:605:0,0,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:624:-2,0,0,0,0,0,0;1/1:624:-1,-2,0,0,1,0,0;-1/1:627:0,0,0,0,0,0,0;-1/1:628:-2,0,0,0,0,0,0;-1/1:629:0,0,0,0,0,0,0;-1/1:633:0,0,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;-1/1:635:0,0,0,0,0,0,0;-1/1:639:0,0,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;-1/1:646:-1,0,0,0,1,0,0;-1/1:647:0,0,0,0,0,0,0;-1/1:648:-2,0,0,0,0,0,0;-1/1:652:-2,0,0,0,0,0,0;-1/1:653:0,0,0,0,0,0,0;-1/1:657:0,0,0,0,0,0,0;-1/1:660:-2,0,0,0,0,0,0;-1/1:663:0,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;-1/1:669:0,0,0,0,0,0,0;-1/1:670:-2,0,0,0,0,0,0;-1/1:677:0,0,0,0,0,0,0;-1/1:678:-2,0,0,0,0,0,0;-1/1:683:0,0,0,0,0,0,0;-1/1:684:-2,0,0,0,0,0,0;-1/1:688:-2,0,0,0,0,0,0;-1/1:689:0,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0;1/1:696:-1,0,0,0,1,0,0;-1/1:699:0,0,0,0,0,0,0;-1/1:702:-4,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:708:-2,0,0,0,0,0,0;-1/1:713:0,0,0,0,0,0,0;-1/1:717:0,0,0,0,0,0,0;-1/1:718:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:719:0,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;-1/1:730:-2,0,0,0,0,0,0;-1/1:732:-2,0,0,0,0,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:744:-2,0,0,0,0,0,0;-1/1:747:0,0,0,0,0,0,0;-1/1:748:-2,0,0,0,0,0,0;-1/1:749:0,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;-1/1:755:0,0,0,0,0,0,0;-1/1:759:0,0,0,0,0,0,0;-1/1:760:-2,0,0,0,0,0,0;-1/1:762:-2,0,0,0,0,0,0;-1/1:765:0,0,0,0,0,0,0;-1/1:767:0,0,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;-1/1:773:0,0,0,0,0,0,0;-1/1:774:-2,0,0,0,0,0,0;-1/1:778:-2,0,0,0,0,0,0;-1/1:779:0,0,0,0,0,0,0;-1/1:783:0,0,0,0,0,0,0;-1/1:789:0,0,0,0,0,0,0;-1/1:790:-2,0,0,0,0,0,0;-1/1:792:-2,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;-1/1:797:0,0,0,0,0,0,0;-1/1:802:-2,0,0,0,0,0,0;-1/1:803:0,0,0,0,0,0,0;-1/1:804:-2,0,0,0,0,0,0;-1/1:807:0,0,0,0,0,0,0;-1/1:809:0,0,0,0,0,0,0;-1/1:810:-2,0,0,0,0,0,0;-1/1:814:-2,0,0,0,0,0,0;-1/1:815:0,0,0,0,0,0,0;-1/1:820:-2,0,0,0,0,0,0;-1/1:828:-2,0,0,0,0,0,0;-1/1:832:-2,0,0,0,0,0,0;-1/1:834:-2,0,0,0,0,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:837:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:839:0,0,0,0,0,0,0;-1/1:843:0,0,0,0,0,0,0;-1/1:844:-2,0,0,0,0,0,0;-1/1:845:0,0,0,0,0,0,0;-1/1:849:0,0,0,0,0,0,0;-1/1:852:-2,0,0,0,0,0,0;-1/1:857:0,0,0,0,0,0,0;-1/1:858:-2,0,0,0,0,0,0;-1/1:862:-2,0,0,0,0,0,0;-1/1:863:0,0,0,0,0,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;-1/1:867:0,0,0,0,0,0,0;-1/1:873:0,0,0,0,0,0,0;-1/1:874:-2,0,0,0,0,0,0;1/1:876:-3,-2,0,0,1,0,0;-1/1:879:0,0,0,0,0,0,0;-1/1:885:0,0,0,0,0,0,0;-1/1:887:0,0,0,0,0,0,0;1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:893:0,0,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;-1/1:904:-2,0,0,0,0,0,0;-1/1:905:0,0,0,0,0,0,0;-1/1:909:0,0,0,0,0,0,0;-1/1:912:-2,0,0,0,0,0,0;-1/1:915:0,0,0,0,0,0,0;-1/1:918:-2,0,0,0,0,0,0;-1/1:922:-2,0,0,0,0,0,0;-1/1:923:0,0,0,0,0,0,0;-1/1:927:0,0,0,0,0,0,0;-1/1:928:-2,0,0,0,0,0,0;-1/1:929:0,0,0,0,0,0,0;-1/1:933:0,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:935:0,0,0,0,0,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0;-1/1:940:-2,0,0,0,0,0,0;-1/1:947:0,0,0,0,0,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:977:0,0,0,0,0,0,0;-1/1:982:-2,0,0,0,0,0,0;-1/1:983:0,0,0,0,0,0,0;-1/1:984:-2,0,0,0,0,0,0;-1/1:988:-2,0,0,0,0,0,0;-1/1:989:0,0,0,0,0,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:993:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:999:0,0,0,0,0,0,0;-1/1:1013:0,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0;-1/1:1019:0,0,0,0,0,0,0"

compact_certificate theorem operation977_suffix192 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 192)=operation977Result192 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 192 32
    operation977Result192 operation977Result224 operation977_suffix224
  decide +kernel

compact_certificate def operation977Result160 : Poly := laurent_polynomial% "-1/1:17:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;-1/1:33:0,0,0,0,0,0,0;-1/1:34:-2,0,0,0,0,0,0;-1/1:47:0,0,0,0,0,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;-1/1:62:-2,0,0,0,0,0,0;-1/1:64:-2,0,0,0,0,0,0;-1/1:65:0,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:89:0,0,0,0,0,0,0;-1/1:95:0,0,0,0,0,0,0;-1/1:107:0,0,0,0,0,0,0;-1/1:114:-2,0,0,0,0,0,0;-1/1:117:0,0,0,0,0,0,0;-1/1:118:-2,0,0,0,0,0,0;-1/1:119:0,0,0,0,0,0,0;-1/1:123:0,0,0,0,0,0,0;-1/1:124:-2,0,0,0,0,0,0;-1/1:125:0,0,0,0,0,0,0;-1/1:129:0,0,0,0,0,0,0;-1/1:130:-2,0,0,0,0,0,0;-1/1:132:-2,0,0,0,0,0,0;-1/1:135:0,0,0,0,0,0,0;-1/1:137:0,0,0,0,0,0,0;-1/1:138:-2,0,0,0,0,0,0;-1/1:142:-2,0,0,0,0,0,0;-1/1:143:0,0,0,0,0,0,0;-1/1:144:-2,0,0,0,0,0,0;-1/1:147:0,0,0,0,0,0,0;-1/1:148:-2,0,0,0,0,0,0;-1/1:149:0,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;-1/1:154:-2,0,0,0,0,0,0;-1/1:159:0,0,0,0,0,0,0;-1/1:160:-2,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;-1/1:165:0,0,0,0,0,0,0;-1/1:167:0,0,0,0,0,0,0;-1/1:172:-2,0,0,0,0,0,0;-1/1:173:0,0,0,0,0,0,0;-1/1:174:-2,0,0,0,0,0,0;-1/1:177:0,0,0,0,0,0,0;-1/1:179:0,0,0,0,0,0,0;-1/1:184:-2,0,0,0,0,0,0;-1/1:185:0,0,0,0,0,0,0;-1/1:189:0,0,0,0,0,0,0;-1/1:190:-2,0,0,0,0,0,0;-1/1:195:0,0,0,0,0,0,0;-1/1:198:-2,0,0,0,0,0,0;-1/1:202:-2,0,0,0,0,0,0;-1/1:203:0,0,0,0,0,0,0;-1/1:204:-2,0,0,0,0,0,0;-1/1:207:0,0,0,0,0,0,0;-1/1:208:-2,0,0,0,0,0,0;-1/1:209:0,0,0,0,0,0,0;-1/1:213:0,0,0,0,0,0,0;-1/1:214:-2,0,0,0,0,0,0;-1/1:215:0,0,0,0,0,0,0;-1/1:219:0,0,0,0,0,0,0;-1/1:222:-2,0,0,0,0,0,0;-1/1:227:0,0,0,0,0,0,0;-1/1:228:-2,0,0,0,0,0,0;-1/1:232:-2,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-1/1:237:0,0,0,0,0,0,0;-1/1:238:-2,0,0,0,0,0,0;-1/1:240:-2,0,0,0,0,0,0;-1/1:243:0,0,0,0,0,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:249:0,0,0,0,0,0,0;-1/1:250:-2,0,0,0,0,0,0;-1/1:255:0,0,0,0,0,0,0;-1/1:257:0,0,0,0,0,0,0;-1/1:258:-2,0,0,0,0,0,0;-1/1:263:0,0,0,0,0,0,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;-1/1:268:-2,0,0,0,0,0,0;-1/1:269:0,0,0,0,0,0,0;-1/1:274:-2,0,0,0,0,0,0;-1/1:275:0,0,0,0,0,0,0;-1/1:279:0,0,0,0,0,0,0;-1/1:285:0,0,0,0,0,0,0;-1/1:287:0,0,0,0,0,0,0;-1/1:288:-2,0,0,0,0,0,0;-1/1:292:-2,0,0,0,0,0,0;-1/1:293:0,0,0,0,0,0,0;-1/1:297:0,0,0,0,0,0,0;-1/1:298:-2,0,0,0,0,0,0;-1/1:299:0,0,0,0,0,0,0;-1/1:303:0,0,0,0,0,0,0;-1/1:305:0,0,0,0,0,0,0;-1/1:310:-2,0,0,0,0,0,0;-1/1:312:-2,0,0,0,0,0,0;-1/1:317:0,0,0,0,0,0,0;-1/1:324:-2,0,0,0,0,0,0;-1/1:327:0,0,0,0,0,0,0;-1/1:328:-2,0,0,0,0,0,0;-1/1:329:0,0,0,0,0,0,0;-1/1:330:-2,0,0,0,0,0,0;-1/1:333:0,0,0,0,0,0,0;-1/1:334:-2,0,0,0,0,0,0;-1/1:335:0,0,0,0,0,0,0;-1/1:339:0,0,0,0,0,0,0;-1/1:342:-2,0,0,0,0,0,0;-1/1:345:0,0,0,0,0,0,0;-1/1:347:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:352:-2,0,0,0,0,0,0;-1/1:353:0,0,0,0,0,0,0;-1/1:354:-2,0,0,0,0,0,0;-1/1:357:0,0,0,0,0,0,0;-1/1:358:-2,0,0,0,0,0,0;-1/1:359:0,0,0,0,0,0,0;-1/1:363:0,0,0,0,0,0,0;-1/1:369:0,0,0,0,0,0,0;-1/1:372:-2,0,0,0,0,0,0;-1/1:375:0,0,0,0,0,0,0;-1/1:377:0,0,0,0,0,0,0;-1/1:382:-2,0,0,0,0,0,0;-1/1:383:0,0,0,0,0,0,0;-1/1:384:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:387:0,0,0,0,0,0,0;-1/1:389:0,0,0,0,0,0,0;-1/1:390:-2,0,0,0,0,0,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:395:0,0,0,0,0,0,0;-1/1:396:-1,0,0,0,1,0,0;-1/1:400:-2,0,0,0,0,0,0;-1/1:405:0,0,0,0,0,0,0;-1/1:408:-2,0,0,0,0,0,0;-1/1:408:0,0,0,0,0,0,0;-1/1:412:-2,0,0,0,0,0,0;-1/1:413:0,0,0,0,0,0,0;-1/1:414:-2,0,0,0,0,0,0;-1/1:417:0,0,0,0,0,0,0;-1/1:418:-2,0,0,0,0,0,0;-1/1:419:0,0,0,0,0,0,0;-1/1:423:0,0,0,0,0,0,0;-1/1:424:-2,0,0,0,0,0,0;-1/1:425:0,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;-1/1:429:0,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:437:0,0,0,0,0,0,0;-1/1:438:-2,0,0,0,0,0,0;-1/1:442:-2,0,0,0,0,0,0;-1/1:443:0,0,0,0,0,0,0;-1/1:447:0,0,0,0,0,0,0;-1/1:448:-2,0,0,0,0,0,0;-1/1:453:0,0,0,0,0,0,0;-1/1:454:-2,0,0,0,0,0,0;-1/1:459:0,0,0,0,0,0,0;-1/1:460:-2,0,0,0,0,0,0;-1/1:465:0,0,0,0,0,0,0;-1/1:467:0,0,0,0,0,0,0;-1/1:468:-2,0,0,0,0,0,0;-1/1:473:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:474:1,0,0,0,1,0,0;-1/1:478:-2,0,0,0,0,0,0;-1/1:479:0,0,0,0,0,0,0;-1/1:484:-2,0,0,0,0,0,0;-1/1:485:0,0,0,0,0,0,0;-1/1:489:0,0,0,0,0,0,0;-1/1:509:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;-1/1:527:0,0,0,0,0,0,0;-1/1:538:-2,0,0,0,0,0,0;-1/1:557:0,0,0,0,0,0,0;-1/1:558:-2,0,0,0,0,0,0;-1/1:562:-2,0,0,0,0,0,0;-1/1:563:0,0,0,0,0,0,0;-1/1:568:-2,0,0,0,0,0,0;-1/1:569:0,0,0,0,0,0,0;-1/1:573:0,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:1,-2,0,0,1,0,0;-1/1:579:0,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:582:-2,0,0,0,0,0,0;-1/1:585:0,0,0,0,0,0,0;-1/1:587:0,0,0,0,0,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:593:0,0,0,0,0,0,0;-1/1:594:-2,0,0,0,0,0,0;-1/1:597:0,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;-1/1:605:0,0,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;-1/1:610:-2,0,0,0,0,0,0;-1/1:615:0,0,0,0,0,0,0;1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:623:0,0,0,0,0,0,0;-1/1:624:-2,0,0,0,0,0,0;1/1:624:-1,-2,0,0,1,0,0;-1/1:627:0,0,0,0,0,0,0;-1/1:628:-2,0,0,0,0,0,0;-1/1:629:0,0,0,0,0,0,0;-1/1:633:0,0,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;-1/1:635:0,0,0,0,0,0,0;-1/1:639:0,0,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;-1/1:646:-1,0,0,0,1,0,0;-1/1:647:0,0,0,0,0,0,0;-1/1:648:-2,0,0,0,0,0,0;-1/1:652:-2,0,0,0,0,0,0;-1/1:653:0,0,0,0,0,0,0;-1/1:657:0,0,0,0,0,0,0;-1/1:660:-2,0,0,0,0,0,0;-1/1:663:0,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;-1/1:669:0,0,0,0,0,0,0;-1/1:670:-2,0,0,0,0,0,0;-1/1:677:0,0,0,0,0,0,0;-1/1:678:-2,0,0,0,0,0,0;-1/1:683:0,0,0,0,0,0,0;-1/1:684:-2,0,0,0,0,0,0;-1/1:688:-2,0,0,0,0,0,0;-1/1:689:0,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0;-1/1:695:0,0,0,0,0,0,0;1/1:696:-1,0,0,0,1,0,0;-1/1:699:0,0,0,0,0,0,0;-1/1:702:-4,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:705:0,0,0,0,0,0,0;-1/1:707:0,0,0,0,0,0,0;-1/1:708:-2,0,0,0,0,0,0;-1/1:713:0,0,0,0,0,0,0;-1/1:717:0,0,0,0,0,0,0;-1/1:718:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:719:0,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;-1/1:725:0,0,0,0,0,0,0;-1/1:730:-2,0,0,0,0,0,0;-1/1:732:-2,0,0,0,0,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:744:-2,0,0,0,0,0,0;-1/1:747:0,0,0,0,0,0,0;-1/1:748:-2,0,0,0,0,0,0;-1/1:749:0,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;-1/1:755:0,0,0,0,0,0,0;-1/1:759:0,0,0,0,0,0,0;-1/1:760:-2,0,0,0,0,0,0;-1/1:762:-2,0,0,0,0,0,0;-1/1:765:0,0,0,0,0,0,0;-1/1:767:0,0,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;-1/1:773:0,0,0,0,0,0,0;-1/1:774:-2,0,0,0,0,0,0;-1/1:778:-2,0,0,0,0,0,0;-1/1:779:0,0,0,0,0,0,0;-1/1:783:0,0,0,0,0,0,0;-1/1:789:0,0,0,0,0,0,0;-1/1:790:-2,0,0,0,0,0,0;-1/1:792:-2,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;-1/1:797:0,0,0,0,0,0,0;-1/1:802:-2,0,0,0,0,0,0;-1/1:803:0,0,0,0,0,0,0;-1/1:804:-2,0,0,0,0,0,0;-1/1:807:0,0,0,0,0,0,0;-1/1:809:0,0,0,0,0,0,0;-1/1:810:-2,0,0,0,0,0,0;-1/1:814:-2,0,0,0,0,0,0;-1/1:815:0,0,0,0,0,0,0;-1/1:819:0,0,0,0,0,0,0;-1/1:820:-2,0,0,0,0,0,0;-1/1:828:-2,0,0,0,0,0,0;-1/1:832:-2,0,0,0,0,0,0;-1/1:833:0,0,0,0,0,0,0;-1/1:834:-2,0,0,0,0,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:837:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:839:0,0,0,0,0,0,0;-1/1:843:0,0,0,0,0,0,0;-1/1:844:-2,0,0,0,0,0,0;-1/1:845:0,0,0,0,0,0,0;-1/1:849:0,0,0,0,0,0,0;-1/1:852:-2,0,0,0,0,0,0;-1/1:857:0,0,0,0,0,0,0;-1/1:858:-2,0,0,0,0,0,0;-1/1:862:-2,0,0,0,0,0,0;-1/1:863:0,0,0,0,0,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;-1/1:867:0,0,0,0,0,0,0;-1/1:873:0,0,0,0,0,0,0;-1/1:874:-2,0,0,0,0,0,0;1/1:876:-3,-2,0,0,1,0,0;-1/1:879:0,0,0,0,0,0,0;-1/1:885:0,0,0,0,0,0,0;-1/1:887:0,0,0,0,0,0,0;1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:893:0,0,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;-1/1:904:-2,0,0,0,0,0,0;-1/1:905:0,0,0,0,0,0,0;-1/1:909:0,0,0,0,0,0,0;-1/1:912:-2,0,0,0,0,0,0;-1/1:915:0,0,0,0,0,0,0;-1/1:917:0,0,0,0,0,0,0;-1/1:918:-2,0,0,0,0,0,0;-1/1:922:-2,0,0,0,0,0,0;-1/1:923:0,0,0,0,0,0,0;-1/1:927:0,0,0,0,0,0,0;-1/1:928:-2,0,0,0,0,0,0;-1/1:929:0,0,0,0,0,0,0;-1/1:933:0,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:935:0,0,0,0,0,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0;-1/1:940:-2,0,0,0,0,0,0;-1/1:942:-2,0,0,0,0,0,0;-1/1:947:0,0,0,0,0,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:977:0,0,0,0,0,0,0;-1/1:982:-2,0,0,0,0,0,0;-1/1:983:0,0,0,0,0,0,0;-1/1:984:-2,0,0,0,0,0,0;-1/1:988:-2,0,0,0,0,0,0;-1/1:989:0,0,0,0,0,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:993:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:999:0,0,0,0,0,0,0;-1/1:1013:0,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0;-1/1:1017:0,0,0,0,0,0,0;-1/1:1019:0,0,0,0,0,0,0;-1/1:1042:-2,0,0,0,0,0,0"

compact_certificate theorem operation977_suffix160 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 160)=operation977Result160 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 160 32
    operation977Result160 operation977Result192 operation977_suffix192
  decide +kernel

compact_certificate def operation977Result128 : Poly := laurent_polynomial% "-1/1:17:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;-1/1:27:0,0,0,0,0,0,0;-1/1:33:0,0,0,0,0,0,0;-1/1:34:-2,0,0,0,0,0,0;-1/1:47:0,0,0,0,0,0,0;-1/1:48:-2,0,0,0,0,0,0;-1/1:54:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;-1/1:60:-2,0,0,0,0,0,0;-1/1:62:-2,0,0,0,0,0,0;-1/1:64:-2,0,0,0,0,0,0;-1/1:65:0,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:89:0,0,0,0,0,0,0;-1/1:95:0,0,0,0,0,0,0;-1/1:107:0,0,0,0,0,0,0;-1/1:112:-2,0,0,0,0,0,0;-1/1:114:-2,0,0,0,0,0,0;-1/1:117:0,0,0,0,0,0,0;-1/1:118:-2,0,0,0,0,0,0;-1/1:119:0,0,0,0,0,0,0;-1/1:120:-2,0,0,0,0,0,0;-1/1:123:0,0,0,0,0,0,0;-1/1:124:-2,0,0,0,0,0,0;-1/1:125:0,0,0,0,0,0,0;-1/1:129:0,0,0,0,0,0,0;-1/1:130:-2,0,0,0,0,0,0;-1/1:132:-2,0,0,0,0,0,0;-1/1:135:0,0,0,0,0,0,0;-1/1:137:0,0,0,0,0,0,0;-1/1:138:-2,0,0,0,0,0,0;-1/1:142:-2,0,0,0,0,0,0;-1/1:143:0,0,0,0,0,0,0;-1/1:144:-2,0,0,0,0,0,0;-1/1:147:0,0,0,0,0,0,0;-1/1:148:-2,0,0,0,0,0,0;-1/1:149:0,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;-1/1:154:-2,0,0,0,0,0,0;-1/1:159:0,0,0,0,0,0,0;-1/1:160:-2,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;-1/1:165:0,0,0,0,0,0,0;-1/1:167:0,0,0,0,0,0,0;-1/1:172:-2,0,0,0,0,0,0;-1/1:173:0,0,0,0,0,0,0;-1/1:174:-2,0,0,0,0,0,0;-1/1:177:0,0,0,0,0,0,0;-1/1:179:0,0,0,0,0,0,0;-1/1:180:-2,0,0,0,0,0,0;-1/1:184:-2,0,0,0,0,0,0;-1/1:185:0,0,0,0,0,0,0;-1/1:189:0,0,0,0,0,0,0;-1/1:190:-2,0,0,0,0,0,0;-1/1:195:0,0,0,0,0,0,0;-1/1:198:-2,0,0,0,0,0,0;-1/1:202:-2,0,0,0,0,0,0;-1/1:203:0,0,0,0,0,0,0;-1/1:204:-2,0,0,0,0,0,0;-1/1:207:0,0,0,0,0,0,0;-1/1:208:-2,0,0,0,0,0,0;-1/1:209:0,0,0,0,0,0,0;-1/1:213:0,0,0,0,0,0,0;-1/1:214:-2,0,0,0,0,0,0;-1/1:215:0,0,0,0,0,0,0;-1/1:219:0,0,0,0,0,0,0;-1/1:222:-2,0,0,0,0,0,0;-1/1:227:0,0,0,0,0,0,0;-1/1:228:-2,0,0,0,0,0,0;-1/1:232:-2,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-1/1:237:0,0,0,0,0,0,0;-1/1:238:-2,0,0,0,0,0,0;-1/1:240:-2,0,0,0,0,0,0;-1/1:243:0,0,0,0,0,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:245:0,0,0,0,0,0,0;-1/1:249:0,0,0,0,0,0,0;-1/1:250:-2,0,0,0,0,0,0;-1/1:255:0,0,0,0,0,0,0;-1/1:257:0,0,0,0,0,0,0;-1/1:258:-2,0,0,0,0,0,0;-1/1:263:0,0,0,0,0,0,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;-1/1:268:-2,0,0,0,0,0,0;-1/1:269:0,0,0,0,0,0,0;-1/1:270:-2,0,0,0,0,0,0;-1/1:274:-2,0,0,0,0,0,0;-1/1:275:0,0,0,0,0,0,0;-1/1:279:0,0,0,0,0,0,0;-1/1:285:0,0,0,0,0,0,0;-1/1:287:0,0,0,0,0,0,0;-1/1:288:-2,0,0,0,0,0,0;-1/1:292:-2,0,0,0,0,0,0;-1/1:293:0,0,0,0,0,0,0;-1/1:294:-2,0,0,0,0,0,0;-1/1:297:0,0,0,0,0,0,0;-1/1:298:-2,0,0,0,0,0,0;-1/1:299:0,0,0,0,0,0,0;-1/1:303:0,0,0,0,0,0,0;-1/1:305:0,0,0,0,0,0,0;-1/1:310:-2,0,0,0,0,0,0;-1/1:312:-2,0,0,0,0,0,0;-1/1:315:0,0,0,0,0,0,0;-1/1:317:0,0,0,0,0,0,0;-1/1:324:-2,0,0,0,0,0,0;-1/1:327:0,0,0,0,0,0,0;-1/1:328:-2,0,0,0,0,0,0;-1/1:329:0,0,0,0,0,0,0;-1/1:330:-2,0,0,0,0,0,0;-1/1:333:0,0,0,0,0,0,0;-1/1:334:-2,0,0,0,0,0,0;-1/1:335:0,0,0,0,0,0,0;-1/1:339:0,0,0,0,0,0,0;-1/1:340:-2,0,0,0,0,0,0;-1/1:342:-2,0,0,0,0,0,0;-1/1:345:0,0,0,0,0,0,0;-1/1:347:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:352:-2,0,0,0,0,0,0;-1/1:353:0,0,0,0,0,0,0;-1/1:354:-2,0,0,0,0,0,0;-1/1:357:0,0,0,0,0,0,0;-1/1:358:-2,0,0,0,0,0,0;-1/1:359:0,0,0,0,0,0,0;-1/1:363:0,0,0,0,0,0,0;-1/1:364:-2,0,0,0,0,0,0;-1/1:369:0,0,0,0,0,0,0;-1/1:370:-2,0,0,0,0,0,0;-1/1:372:-2,0,0,0,0,0,0;-1/1:375:0,0,0,0,0,0,0;-1/1:377:0,0,0,0,0,0,0;-1/1:382:-2,0,0,0,0,0,0;-1/1:383:0,0,0,0,0,0,0;-1/1:384:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:387:0,0,0,0,0,0,0;-1/1:389:0,0,0,0,0,0,0;-1/1:390:-2,0,0,0,0,0,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:395:0,0,0,0,0,0,0;-1/1:396:-1,0,0,0,1,0,0;-1/1:400:-2,0,0,0,0,0,0;-1/1:405:0,0,0,0,0,0,0;-1/1:408:-2,0,0,0,0,0,0;-1/1:408:0,0,0,0,0,0,0;-1/1:412:-2,0,0,0,0,0,0;-1/1:413:0,0,0,0,0,0,0;-1/1:414:-2,0,0,0,0,0,0;-1/1:417:0,0,0,0,0,0,0;-1/1:418:-2,0,0,0,0,0,0;-1/1:419:0,0,0,0,0,0,0;-1/1:423:0,0,0,0,0,0,0;-1/1:424:-2,0,0,0,0,0,0;-1/1:425:0,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;-1/1:429:0,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:437:0,0,0,0,0,0,0;-1/1:438:-2,0,0,0,0,0,0;-1/1:442:-2,0,0,0,0,0,0;-1/1:443:0,0,0,0,0,0,0;-1/1:447:0,0,0,0,0,0,0;-1/1:448:-2,0,0,0,0,0,0;-1/1:453:0,0,0,0,0,0,0;-1/1:454:-2,0,0,0,0,0,0;-1/1:455:0,0,0,0,0,0,0;-1/1:459:0,0,0,0,0,0,0;-1/1:460:-2,0,0,0,0,0,0;-1/1:465:0,0,0,0,0,0,0;-1/1:467:0,0,0,0,0,0,0;-1/1:468:-2,0,0,0,0,0,0;-1/1:473:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:474:1,0,0,0,1,0,0;-1/1:478:-2,0,0,0,0,0,0;-1/1:479:0,0,0,0,0,0,0;-1/1:484:-2,0,0,0,0,0,0;-1/1:485:0,0,0,0,0,0,0;-1/1:489:0,0,0,0,0,0,0;-1/1:495:0,0,0,0,0,0,0;-1/1:509:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;-1/1:515:0,0,0,0,0,0,0;-1/1:527:0,0,0,0,0,0,0;-1/1:537:0,0,0,0,0,0,0;-1/1:538:-2,0,0,0,0,0,0;-1/1:557:0,0,0,0,0,0,0;-1/1:558:-2,0,0,0,0,0,0;-1/1:562:-2,0,0,0,0,0,0;-1/1:563:0,0,0,0,0,0,0;-1/1:568:-2,0,0,0,0,0,0;-1/1:569:0,0,0,0,0,0,0;-1/1:573:0,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:1,-2,0,0,1,0,0;-1/1:579:0,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:582:-2,0,0,0,0,0,0;-1/1:585:0,0,0,0,0,0,0;-1/1:587:0,0,0,0,0,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:593:0,0,0,0,0,0,0;-1/1:594:-2,0,0,0,0,0,0;-1/1:597:0,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;-1/1:605:0,0,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;-1/1:610:-2,0,0,0,0,0,0;-1/1:615:0,0,0,0,0,0,0;1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:623:0,0,0,0,0,0,0;-1/1:624:-2,0,0,0,0,0,0;1/1:624:-1,-2,0,0,1,0,0;-1/1:627:0,0,0,0,0,0,0;-1/1:628:-2,0,0,0,0,0,0;-1/1:629:0,0,0,0,0,0,0;-1/1:633:0,0,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;-1/1:635:0,0,0,0,0,0,0;-1/1:639:0,0,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;-1/1:646:-1,0,0,0,1,0,0;-1/1:647:0,0,0,0,0,0,0;-1/1:648:-2,0,0,0,0,0,0;-1/1:652:-2,0,0,0,0,0,0;-1/1:653:0,0,0,0,0,0,0;-1/1:657:0,0,0,0,0,0,0;-1/1:660:-2,0,0,0,0,0,0;-1/1:663:0,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;-1/1:665:0,0,0,0,0,0,0;-1/1:669:0,0,0,0,0,0,0;-1/1:670:-2,0,0,0,0,0,0;-1/1:677:0,0,0,0,0,0,0;-1/1:678:-2,0,0,0,0,0,0;-1/1:683:0,0,0,0,0,0,0;-1/1:684:-2,0,0,0,0,0,0;-1/1:688:-2,0,0,0,0,0,0;-1/1:689:0,0,0,0,0,0,0;-1/1:690:-2,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0;-1/1:695:0,0,0,0,0,0,0;1/1:696:-1,0,0,0,1,0,0;-1/1:699:0,0,0,0,0,0,0;-1/1:702:-4,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:705:0,0,0,0,0,0,0;-1/1:707:0,0,0,0,0,0,0;-1/1:708:-2,0,0,0,0,0,0;-1/1:713:0,0,0,0,0,0,0;-1/1:714:-2,0,0,0,0,0,0;-1/1:717:0,0,0,0,0,0,0;-1/1:718:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:719:0,0,0,0,0,0,0;-1/1:720:-2,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;-1/1:725:0,0,0,0,0,0,0;-1/1:730:-2,0,0,0,0,0,0;-1/1:732:-2,0,0,0,0,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:742:-2,0,0,0,0,0,0;-1/1:744:-2,0,0,0,0,0,0;-1/1:747:0,0,0,0,0,0,0;-1/1:748:-2,0,0,0,0,0,0;-1/1:749:0,0,0,0,0,0,0;-1/1:750:-2,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;-1/1:755:0,0,0,0,0,0,0;-1/1:759:0,0,0,0,0,0,0;-1/1:760:-2,0,0,0,0,0,0;-1/1:762:-2,0,0,0,0,0,0;-1/1:765:0,0,0,0,0,0,0;-1/1:767:0,0,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;-1/1:773:0,0,0,0,0,0,0;-1/1:774:-2,0,0,0,0,0,0;-1/1:778:-2,0,0,0,0,0,0;-1/1:779:0,0,0,0,0,0,0;-1/1:783:0,0,0,0,0,0,0;-1/1:789:0,0,0,0,0,0,0;-1/1:790:-2,0,0,0,0,0,0;-1/1:792:-2,0,0,0,0,0,0;-1/1:795:0,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;-1/1:797:0,0,0,0,0,0,0;-1/1:802:-2,0,0,0,0,0,0;-1/1:803:0,0,0,0,0,0,0;-1/1:804:-2,0,0,0,0,0,0;-1/1:807:0,0,0,0,0,0,0;-1/1:809:0,0,0,0,0,0,0;-1/1:810:-2,0,0,0,0,0,0;-1/1:814:-2,0,0,0,0,0,0;-1/1:815:0,0,0,0,0,0,0;-1/1:819:0,0,0,0,0,0,0;-1/1:820:-2,0,0,0,0,0,0;-1/1:828:-2,0,0,0,0,0,0;-1/1:832:-2,0,0,0,0,0,0;-1/1:833:0,0,0,0,0,0,0;-1/1:834:-2,0,0,0,0,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:837:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:839:0,0,0,0,0,0,0;-1/1:843:0,0,0,0,0,0,0;-1/1:844:-2,0,0,0,0,0,0;-1/1:845:0,0,0,0,0,0,0;-1/1:849:0,0,0,0,0,0,0;-1/1:852:-2,0,0,0,0,0,0;-1/1:857:0,0,0,0,0,0,0;-1/1:858:-2,0,0,0,0,0,0;-1/1:862:-2,0,0,0,0,0,0;-1/1:863:0,0,0,0,0,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;-1/1:867:0,0,0,0,0,0,0;-1/1:870:-2,0,0,0,0,0,0;-1/1:873:0,0,0,0,0,0,0;-1/1:874:-2,0,0,0,0,0,0;1/1:876:-3,-2,0,0,1,0,0;-1/1:879:0,0,0,0,0,0,0;-1/1:880:-2,0,0,0,0,0,0;-1/1:885:0,0,0,0,0,0,0;-1/1:887:0,0,0,0,0,0,0;1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:893:0,0,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;-1/1:900:-2,0,0,0,0,0,0;-1/1:904:-2,0,0,0,0,0,0;-1/1:905:0,0,0,0,0,0,0;-1/1:909:0,0,0,0,0,0,0;-1/1:910:-2,0,0,0,0,0,0;-1/1:912:-2,0,0,0,0,0,0;-1/1:915:0,0,0,0,0,0,0;-1/1:917:0,0,0,0,0,0,0;-1/1:918:-2,0,0,0,0,0,0;-1/1:922:-2,0,0,0,0,0,0;-1/1:923:0,0,0,0,0,0,0;-1/1:927:0,0,0,0,0,0,0;-1/1:928:-2,0,0,0,0,0,0;-1/1:929:0,0,0,0,0,0,0;-1/1:930:-2,0,0,0,0,0,0;-1/1:933:0,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:935:0,0,0,0,0,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0;-1/1:940:-2,0,0,0,0,0,0;-1/1:942:-2,0,0,0,0,0,0;-1/1:947:0,0,0,0,0,0,0;-1/1:957:0,0,0,0,0,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:977:0,0,0,0,0,0,0;-1/1:982:-2,0,0,0,0,0,0;-1/1:983:0,0,0,0,0,0,0;-1/1:984:-2,0,0,0,0,0,0;-1/1:988:-2,0,0,0,0,0,0;-1/1:989:0,0,0,0,0,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:993:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:999:0,0,0,0,0,0,0;-1/1:1013:0,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0;-1/1:1017:0,0,0,0,0,0,0;-1/1:1019:0,0,0,0,0,0,0;-1/1:1025:0,0,0,0,0,0,0;-1/1:1042:-2,0,0,0,0,0,0"

compact_certificate theorem operation977_suffix128 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 128)=operation977Result128 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 128 32
    operation977Result128 operation977Result160 operation977_suffix160
  decide +kernel


}
certificate_batch {
compact_certificate def operation977Result96 : Poly := laurent_polynomial% "-1/1:5:0,0,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;-1/1:27:0,0,0,0,0,0,0;-1/1:30:-2,0,0,0,0,0,0;-1/1:33:0,0,0,0,0,0,0;-1/1:34:-2,0,0,0,0,0,0;-1/1:45:0,0,0,0,0,0,0;-1/1:47:0,0,0,0,0,0,0;-1/1:48:-2,0,0,0,0,0,0;-1/1:54:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;-1/1:60:-2,0,0,0,0,0,0;-1/1:62:-2,0,0,0,0,0,0;-1/1:64:-2,0,0,0,0,0,0;-1/1:65:0,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:70:-2,0,0,0,0,0,0;-1/1:89:0,0,0,0,0,0,0;-1/1:93:0,0,0,0,0,0,0;-1/1:95:0,0,0,0,0,0,0;-1/1:105:0,0,0,0,0,0,0;-1/1:107:0,0,0,0,0,0,0;-1/1:112:-2,0,0,0,0,0,0;-1/1:114:-2,0,0,0,0,0,0;-1/1:117:0,0,0,0,0,0,0;-1/1:118:-2,0,0,0,0,0,0;-1/1:119:0,0,0,0,0,0,0;-1/1:120:-2,0,0,0,0,0,0;-1/1:123:0,0,0,0,0,0,0;-1/1:124:-2,0,0,0,0,0,0;-1/1:125:0,0,0,0,0,0,0;-1/1:129:0,0,0,0,0,0,0;-1/1:130:-2,0,0,0,0,0,0;-1/1:132:-2,0,0,0,0,0,0;-1/1:135:0,0,0,0,0,0,0;-1/1:137:0,0,0,0,0,0,0;-1/1:138:-2,0,0,0,0,0,0;-1/1:142:-2,0,0,0,0,0,0;-1/1:143:0,0,0,0,0,0,0;-1/1:144:-2,0,0,0,0,0,0;-1/1:147:0,0,0,0,0,0,0;-1/1:148:-2,0,0,0,0,0,0;-1/1:149:0,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;-1/1:154:-2,0,0,0,0,0,0;-1/1:159:0,0,0,0,0,0,0;-1/1:160:-2,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;-1/1:165:0,0,0,0,0,0,0;-1/1:167:0,0,0,0,0,0,0;-1/1:172:-2,0,0,0,0,0,0;-1/1:173:0,0,0,0,0,0,0;-1/1:174:-2,0,0,0,0,0,0;-1/1:177:0,0,0,0,0,0,0;-1/1:179:0,0,0,0,0,0,0;-1/1:180:-2,0,0,0,0,0,0;-1/1:184:-2,0,0,0,0,0,0;-1/1:185:0,0,0,0,0,0,0;-1/1:189:0,0,0,0,0,0,0;-1/1:190:-2,0,0,0,0,0,0;-1/1:195:0,0,0,0,0,0,0;-1/1:198:-2,0,0,0,0,0,0;-1/1:202:-2,0,0,0,0,0,0;-1/1:203:0,0,0,0,0,0,0;-1/1:204:-2,0,0,0,0,0,0;-1/1:207:0,0,0,0,0,0,0;-1/1:208:-2,0,0,0,0,0,0;-1/1:209:0,0,0,0,0,0,0;-1/1:213:0,0,0,0,0,0,0;-1/1:214:-2,0,0,0,0,0,0;-1/1:215:0,0,0,0,0,0,0;-1/1:219:0,0,0,0,0,0,0;-1/1:222:-2,0,0,0,0,0,0;-1/1:227:0,0,0,0,0,0,0;-1/1:228:-2,0,0,0,0,0,0;-1/1:232:-2,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-1/1:237:0,0,0,0,0,0,0;-1/1:238:-2,0,0,0,0,0,0;-1/1:240:-2,0,0,0,0,0,0;-1/1:243:0,0,0,0,0,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:245:0,0,0,0,0,0,0;-1/1:249:0,0,0,0,0,0,0;-1/1:250:-2,0,0,0,0,0,0;-1/1:255:0,0,0,0,0,0,0;-1/1:257:0,0,0,0,0,0,0;-1/1:258:-2,0,0,0,0,0,0;-1/1:263:0,0,0,0,0,0,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;-1/1:268:-2,0,0,0,0,0,0;-1/1:269:0,0,0,0,0,0,0;-1/1:270:-2,0,0,0,0,0,0;-1/1:274:-2,0,0,0,0,0,0;-1/1:275:0,0,0,0,0,0,0;-1/1:279:0,0,0,0,0,0,0;-1/1:280:-2,0,0,0,0,0,0;-1/1:285:0,0,0,0,0,0,0;-1/1:287:0,0,0,0,0,0,0;-1/1:288:-2,0,0,0,0,0,0;-1/1:292:-2,0,0,0,0,0,0;-1/1:293:0,0,0,0,0,0,0;-1/1:294:-2,0,0,0,0,0,0;-1/1:297:0,0,0,0,0,0,0;-1/1:298:-2,0,0,0,0,0,0;-1/1:299:0,0,0,0,0,0,0;-1/1:300:-2,0,0,0,0,0,0;-1/1:303:0,0,0,0,0,0,0;-1/1:305:0,0,0,0,0,0,0;-1/1:310:-2,0,0,0,0,0,0;-1/1:312:-2,0,0,0,0,0,0;-1/1:315:0,0,0,0,0,0,0;-1/1:317:0,0,0,0,0,0,0;-1/1:324:-2,0,0,0,0,0,0;-1/1:327:0,0,0,0,0,0,0;-1/1:328:-2,0,0,0,0,0,0;-1/1:329:0,0,0,0,0,0,0;-1/1:330:-2,0,0,0,0,0,0;-1/1:333:0,0,0,0,0,0,0;-1/1:334:-2,0,0,0,0,0,0;-1/1:335:0,0,0,0,0,0,0;-1/1:339:0,0,0,0,0,0,0;-1/1:340:-2,0,0,0,0,0,0;-1/1:342:-2,0,0,0,0,0,0;-1/1:345:0,0,0,0,0,0,0;-1/1:347:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:352:-2,0,0,0,0,0,0;-1/1:353:0,0,0,0,0,0,0;-1/1:354:-2,0,0,0,0,0,0;-1/1:357:0,0,0,0,0,0,0;-1/1:358:-2,0,0,0,0,0,0;-1/1:359:0,0,0,0,0,0,0;-1/1:363:0,0,0,0,0,0,0;-1/1:364:-2,0,0,0,0,0,0;-1/1:369:0,0,0,0,0,0,0;-1/1:370:-2,0,0,0,0,0,0;-1/1:372:-2,0,0,0,0,0,0;-1/1:375:0,0,0,0,0,0,0;-1/1:377:0,0,0,0,0,0,0;-1/1:378:-2,0,0,0,0,0,0;-1/1:382:-2,0,0,0,0,0,0;-1/1:383:0,0,0,0,0,0,0;-1/1:384:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:387:0,0,0,0,0,0,0;-1/1:389:0,0,0,0,0,0,0;-1/1:390:-2,0,0,0,0,0,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:395:0,0,0,0,0,0,0;-1/1:396:-1,0,0,0,1,0,0;-1/1:400:-2,0,0,0,0,0,0;-1/1:405:0,0,0,0,0,0,0;-1/1:408:-2,0,0,0,0,0,0;-1/1:408:0,0,0,0,0,0,0;-1/1:412:-2,0,0,0,0,0,0;-1/1:413:0,0,0,0,0,0,0;-1/1:414:-2,0,0,0,0,0,0;-1/1:417:0,0,0,0,0,0,0;-1/1:418:-2,0,0,0,0,0,0;-1/1:419:0,0,0,0,0,0,0;-1/1:420:-2,0,0,0,0,0,0;-1/1:423:0,0,0,0,0,0,0;-1/1:424:-2,0,0,0,0,0,0;-1/1:425:0,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;-1/1:429:0,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:437:0,0,0,0,0,0,0;-1/1:438:-2,0,0,0,0,0,0;-1/1:442:-2,0,0,0,0,0,0;-1/1:443:0,0,0,0,0,0,0;-1/1:447:0,0,0,0,0,0,0;-1/1:448:-2,0,0,0,0,0,0;-1/1:453:0,0,0,0,0,0,0;-1/1:454:-2,0,0,0,0,0,0;-1/1:455:0,0,0,0,0,0,0;-1/1:459:0,0,0,0,0,0,0;-1/1:460:-2,0,0,0,0,0,0;-1/1:465:0,0,0,0,0,0,0;-1/1:467:0,0,0,0,0,0,0;-1/1:468:-2,0,0,0,0,0,0;-1/1:473:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:474:1,0,0,0,1,0,0;-1/1:478:-2,0,0,0,0,0,0;-1/1:479:0,0,0,0,0,0,0;-1/1:480:-2,0,0,0,0,0,0;-1/1:484:-2,0,0,0,0,0,0;-1/1:485:0,0,0,0,0,0,0;-1/1:489:0,0,0,0,0,0,0;-1/1:495:0,0,0,0,0,0,0;-1/1:498:-2,0,0,0,0,0,0;-1/1:509:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;-1/1:515:0,0,0,0,0,0,0;-1/1:520:-2,0,0,0,0,0,0;-1/1:527:0,0,0,0,0,0,0;-1/1:537:0,0,0,0,0,0,0;-1/1:538:-2,0,0,0,0,0,0;-1/1:545:0,0,0,0,0,0,0;-1/1:549:0,0,0,0,0,0,0;-1/1:555:0,0,0,0,0,0,0;-1/1:557:0,0,0,0,0,0,0;-1/1:558:-2,0,0,0,0,0,0;-1/1:562:-2,0,0,0,0,0,0;-1/1:563:0,0,0,0,0,0,0;-1/1:568:-2,0,0,0,0,0,0;-1/1:569:0,0,0,0,0,0,0;-1/1:573:0,0,0,0,0,0,0;-1/1:574:-2,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:1,-2,0,0,1,0,0;-1/1:579:0,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:582:-2,0,0,0,0,0,0;-1/1:585:0,0,0,0,0,0,0;-1/1:587:0,0,0,0,0,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:593:0,0,0,0,0,0,0;-1/1:594:-2,0,0,0,0,0,0;-1/1:597:0,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:600:-2,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;-1/1:605:0,0,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;-1/1:610:-2,0,0,0,0,0,0;-1/1:615:0,0,0,0,0,0,0;1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:623:0,0,0,0,0,0,0;-1/1:624:-2,0,0,0,0,0,0;1/1:624:-1,-2,0,0,1,0,0;-1/1:627:0,0,0,0,0,0,0;-1/1:628:-2,0,0,0,0,0,0;-1/1:629:0,0,0,0,0,0,0;-1/1:630:-2,0,0,0,0,0,0;-1/1:633:0,0,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;-1/1:635:0,0,0,0,0,0,0;-1/1:639:0,0,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;-1/1:646:-1,0,0,0,1,0,0;-1/1:647:0,0,0,0,0,0,0;-1/1:648:-2,0,0,0,0,0,0;-1/1:652:-2,0,0,0,0,0,0;-1/1:653:0,0,0,0,0,0,0;-1/1:657:0,0,0,0,0,0,0;-1/1:658:-2,0,0,0,0,0,0;-1/1:660:-2,0,0,0,0,0,0;-1/1:663:0,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;-1/1:665:0,0,0,0,0,0,0;-1/1:669:0,0,0,0,0,0,0;-1/1:670:-2,0,0,0,0,0,0;-1/1:675:0,0,0,0,0,0,0;-1/1:677:0,0,0,0,0,0,0;-1/1:678:-2,0,0,0,0,0,0;-1/1:683:0,0,0,0,0,0,0;-1/1:684:-2,0,0,0,0,0,0;-1/1:688:-2,0,0,0,0,0,0;-1/1:689:0,0,0,0,0,0,0;-1/1:690:-2,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0;-1/1:695:0,0,0,0,0,0,0;1/1:696:-1,0,0,0,1,0,0;-1/1:699:0,0,0,0,0,0,0;-1/1:702:-4,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:705:0,0,0,0,0,0,0;-1/1:707:0,0,0,0,0,0,0;-1/1:708:-2,0,0,0,0,0,0;-1/1:713:0,0,0,0,0,0,0;-1/1:714:-2,0,0,0,0,0,0;-1/1:717:0,0,0,0,0,0,0;-1/1:718:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:719:0,0,0,0,0,0,0;-1/1:720:-2,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;-1/1:725:0,0,0,0,0,0,0;-1/1:730:-2,0,0,0,0,0,0;-1/1:732:-2,0,0,0,0,0,0;-1/1:735:0,0,0,0,0,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:742:-2,0,0,0,0,0,0;-1/1:744:-2,0,0,0,0,0,0;-1/1:747:0,0,0,0,0,0,0;-1/1:748:-2,0,0,0,0,0,0;-1/1:749:0,0,0,0,0,0,0;-1/1:750:-2,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;-1/1:755:0,0,0,0,0,0,0;-1/1:759:0,0,0,0,0,0,0;-1/1:760:-2,0,0,0,0,0,0;-1/1:762:-2,0,0,0,0,0,0;-1/1:765:0,0,0,0,0,0,0;-1/1:767:0,0,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;-1/1:773:0,0,0,0,0,0,0;-1/1:774:-2,0,0,0,0,0,0;-1/1:778:-2,0,0,0,0,0,0;-1/1:779:0,0,0,0,0,0,0;-1/1:783:0,0,0,0,0,0,0;-1/1:784:-2,0,0,0,0,0,0;-1/1:789:0,0,0,0,0,0,0;-1/1:790:-2,0,0,0,0,0,0;-1/1:792:-2,0,0,0,0,0,0;-1/1:795:0,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;-1/1:797:0,0,0,0,0,0,0;-1/1:802:-2,0,0,0,0,0,0;-1/1:803:0,0,0,0,0,0,0;-1/1:804:-2,0,0,0,0,0,0;-1/1:807:0,0,0,0,0,0,0;-1/1:809:0,0,0,0,0,0,0;-1/1:810:-2,0,0,0,0,0,0;-1/1:814:-2,0,0,0,0,0,0;-1/1:815:0,0,0,0,0,0,0;-1/1:819:0,0,0,0,0,0,0;-1/1:820:-2,0,0,0,0,0,0;-1/1:825:0,0,0,0,0,0,0;-1/1:828:-2,0,0,0,0,0,0;-1/1:832:-2,0,0,0,0,0,0;-1/1:833:0,0,0,0,0,0,0;-1/1:834:-2,0,0,0,0,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:837:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:839:0,0,0,0,0,0,0;-1/1:843:0,0,0,0,0,0,0;-1/1:844:-2,0,0,0,0,0,0;-1/1:845:0,0,0,0,0,0,0;-1/1:849:0,0,0,0,0,0,0;-1/1:852:-2,0,0,0,0,0,0;-1/1:857:0,0,0,0,0,0,0;-1/1:858:-2,0,0,0,0,0,0;-1/1:862:-2,0,0,0,0,0,0;-1/1:863:0,0,0,0,0,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;-1/1:867:0,0,0,0,0,0,0;-1/1:870:-2,0,0,0,0,0,0;-1/1:873:0,0,0,0,0,0,0;-1/1:874:-2,0,0,0,0,0,0;1/1:876:-3,-2,0,0,1,0,0;-1/1:879:0,0,0,0,0,0,0;-1/1:880:-2,0,0,0,0,0,0;-1/1:885:0,0,0,0,0,0,0;-1/1:887:0,0,0,0,0,0,0;1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:893:0,0,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;-1/1:900:-2,0,0,0,0,0,0;-1/1:903:0,0,0,0,0,0,0;-1/1:904:-2,0,0,0,0,0,0;-1/1:905:0,0,0,0,0,0,0;-1/1:909:0,0,0,0,0,0,0;-1/1:910:-2,0,0,0,0,0,0;-1/1:912:-2,0,0,0,0,0,0;-1/1:915:0,0,0,0,0,0,0;-1/1:917:0,0,0,0,0,0,0;-1/1:918:-2,0,0,0,0,0,0;-1/1:922:-2,0,0,0,0,0,0;-1/1:923:0,0,0,0,0,0,0;-1/1:927:0,0,0,0,0,0,0;-1/1:928:-2,0,0,0,0,0,0;-1/1:929:0,0,0,0,0,0,0;-1/1:930:-2,0,0,0,0,0,0;-1/1:933:0,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:935:0,0,0,0,0,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0;-1/1:940:-2,0,0,0,0,0,0;-1/1:942:-2,0,0,0,0,0,0;-1/1:945:0,0,0,0,0,0,0;-1/1:947:0,0,0,0,0,0,0;-1/1:957:0,0,0,0,0,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:964:-2,0,0,0,0,0,0;-1/1:970:-2,0,0,0,0,0,0;-1/1:977:0,0,0,0,0,0,0;-1/1:982:-2,0,0,0,0,0,0;-1/1:983:0,0,0,0,0,0,0;-1/1:984:-2,0,0,0,0,0,0;-1/1:988:-2,0,0,0,0,0,0;-1/1:989:0,0,0,0,0,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:993:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:999:0,0,0,0,0,0,0;-1/1:1005:0,0,0,0,0,0,0;-1/1:1013:0,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0;-1/1:1017:0,0,0,0,0,0,0;-1/1:1019:0,0,0,0,0,0,0;-1/1:1020:-2,0,0,0,0,0,0;-1/1:1024:-2,0,0,0,0,0,0;-1/1:1025:0,0,0,0,0,0,0;-1/1:1030:-2,0,0,0,0,0,0;-1/1:1042:-2,0,0,0,0,0,0"

compact_certificate theorem operation977_suffix96 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 96)=operation977Result96 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 96 32
    operation977Result96 operation977Result128 operation977_suffix128
  decide +kernel

compact_certificate def operation977Result64 : Poly := laurent_polynomial% "-1/1:5:0,0,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;-1/1:27:0,0,0,0,0,0,0;-1/1:30:-2,0,0,0,0,0,0;-1/1:33:0,0,0,0,0,0,0;-1/1:34:-2,0,0,0,0,0,0;-1/1:45:0,0,0,0,0,0,0;-1/1:47:0,0,0,0,0,0,0;-1/1:48:-2,0,0,0,0,0,0;-1/1:54:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;-1/1:60:-2,0,0,0,0,0,0;-1/1:62:-2,0,0,0,0,0,0;-1/1:64:-2,0,0,0,0,0,0;-1/1:65:0,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:70:-2,0,0,0,0,0,0;-1/1:72:-2,0,0,0,0,0,0;-1/1:78:-2,0,0,0,0,0,0;-1/1:82:-2,0,0,0,0,0,0;-1/1:89:0,0,0,0,0,0,0;-1/1:93:0,0,0,0,0,0,0;-1/1:95:0,0,0,0,0,0,0;-1/1:100:-2,0,0,0,0,0,0;-1/1:105:0,0,0,0,0,0,0;-1/1:107:0,0,0,0,0,0,0;-1/1:112:-2,0,0,0,0,0,0;-1/1:114:-2,0,0,0,0,0,0;-1/1:117:0,0,0,0,0,0,0;-1/1:118:-2,0,0,0,0,0,0;-1/1:119:0,0,0,0,0,0,0;-1/1:120:-2,0,0,0,0,0,0;-1/1:123:0,0,0,0,0,0,0;-1/1:124:-2,0,0,0,0,0,0;-1/1:125:0,0,0,0,0,0,0;-1/1:129:0,0,0,0,0,0,0;-1/1:130:-2,0,0,0,0,0,0;-1/1:132:-2,0,0,0,0,0,0;-1/1:135:0,0,0,0,0,0,0;-1/1:137:0,0,0,0,0,0,0;-1/1:138:-2,0,0,0,0,0,0;-1/1:142:-2,0,0,0,0,0,0;-1/1:143:0,0,0,0,0,0,0;-1/1:144:-2,0,0,0,0,0,0;-1/1:147:0,0,0,0,0,0,0;-1/1:148:-2,0,0,0,0,0,0;-1/1:149:0,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;-1/1:154:-2,0,0,0,0,0,0;-1/1:159:0,0,0,0,0,0,0;-1/1:160:-2,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;-1/1:165:0,0,0,0,0,0,0;-1/1:167:0,0,0,0,0,0,0;-1/1:172:-2,0,0,0,0,0,0;-1/1:173:0,0,0,0,0,0,0;-1/1:174:-2,0,0,0,0,0,0;-1/1:177:0,0,0,0,0,0,0;-1/1:179:0,0,0,0,0,0,0;-1/1:180:-2,0,0,0,0,0,0;-1/1:184:-2,0,0,0,0,0,0;-1/1:185:0,0,0,0,0,0,0;-1/1:189:0,0,0,0,0,0,0;-1/1:190:-2,0,0,0,0,0,0;-1/1:195:0,0,0,0,0,0,0;-1/1:198:-2,0,0,0,0,0,0;-1/1:202:-2,0,0,0,0,0,0;-1/1:203:0,0,0,0,0,0,0;-1/1:204:-2,0,0,0,0,0,0;-1/1:207:0,0,0,0,0,0,0;-1/1:208:-2,0,0,0,0,0,0;-1/1:209:0,0,0,0,0,0,0;-1/1:213:0,0,0,0,0,0,0;-1/1:214:-2,0,0,0,0,0,0;-1/1:215:0,0,0,0,0,0,0;-1/1:219:0,0,0,0,0,0,0;-1/1:222:-2,0,0,0,0,0,0;-1/1:227:0,0,0,0,0,0,0;-1/1:228:-2,0,0,0,0,0,0;-1/1:232:-2,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-1/1:237:0,0,0,0,0,0,0;-1/1:238:-2,0,0,0,0,0,0;-1/1:240:-2,0,0,0,0,0,0;-1/1:243:0,0,0,0,0,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:245:0,0,0,0,0,0,0;-1/1:249:0,0,0,0,0,0,0;-1/1:250:-2,0,0,0,0,0,0;-1/1:252:-2,0,0,0,0,0,0;-1/1:255:0,0,0,0,0,0,0;-1/1:257:0,0,0,0,0,0,0;-1/1:258:-2,0,0,0,0,0,0;-1/1:263:0,0,0,0,0,0,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;-1/1:268:-2,0,0,0,0,0,0;-1/1:269:0,0,0,0,0,0,0;-1/1:270:-2,0,0,0,0,0,0;-1/1:273:0,0,0,0,0,0,0;-1/1:274:-2,0,0,0,0,0,0;-1/1:275:0,0,0,0,0,0,0;-1/1:279:0,0,0,0,0,0,0;-1/1:280:-2,0,0,0,0,0,0;-1/1:285:0,0,0,0,0,0,0;-1/1:287:0,0,0,0,0,0,0;-1/1:288:-2,0,0,0,0,0,0;-1/1:292:-2,0,0,0,0,0,0;-1/1:293:0,0,0,0,0,0,0;-1/1:294:-2,0,0,0,0,0,0;-1/1:297:0,0,0,0,0,0,0;-1/1:298:-2,0,0,0,0,0,0;-1/1:299:0,0,0,0,0,0,0;-1/1:300:-2,0,0,0,0,0,0;-1/1:303:0,0,0,0,0,0,0;-1/1:305:0,0,0,0,0,0,0;-1/1:310:-2,0,0,0,0,0,0;-1/1:312:-2,0,0,0,0,0,0;-1/1:315:0,0,0,0,0,0,0;-1/1:317:0,0,0,0,0,0,0;-1/1:322:-2,0,0,0,0,0,0;-1/1:324:-2,0,0,0,0,0,0;-1/1:327:0,0,0,0,0,0,0;-1/1:328:-2,0,0,0,0,0,0;-1/1:329:0,0,0,0,0,0,0;-1/1:330:-2,0,0,0,0,0,0;-1/1:333:0,0,0,0,0,0,0;-1/1:334:-2,0,0,0,0,0,0;-1/1:335:0,0,0,0,0,0,0;-1/1:339:0,0,0,0,0,0,0;-1/1:340:-2,0,0,0,0,0,0;-1/1:342:-2,0,0,0,0,0,0;-1/1:345:0,0,0,0,0,0,0;-1/1:347:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:352:-2,0,0,0,0,0,0;-1/1:353:0,0,0,0,0,0,0;-1/1:354:-2,0,0,0,0,0,0;-1/1:357:0,0,0,0,0,0,0;-1/1:358:-2,0,0,0,0,0,0;-1/1:359:0,0,0,0,0,0,0;-1/1:363:0,0,0,0,0,0,0;-1/1:364:-2,0,0,0,0,0,0;-1/1:369:0,0,0,0,0,0,0;-1/1:370:-2,0,0,0,0,0,0;-1/1:372:-2,0,0,0,0,0,0;-1/1:375:0,0,0,0,0,0,0;-1/1:377:0,0,0,0,0,0,0;-1/1:378:-2,0,0,0,0,0,0;-1/1:382:-2,0,0,0,0,0,0;-1/1:383:0,0,0,0,0,0,0;-1/1:384:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:387:0,0,0,0,0,0,0;-1/1:389:0,0,0,0,0,0,0;-1/1:390:-2,0,0,0,0,0,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:395:0,0,0,0,0,0,0;-1/1:396:-1,0,0,0,1,0,0;-1/1:399:0,0,0,0,0,0,0;-1/1:400:-2,0,0,0,0,0,0;-1/1:405:0,0,0,0,0,0,0;-1/1:408:-2,0,0,0,0,0,0;-1/1:408:0,0,0,0,0,0,0;-1/1:412:-2,0,0,0,0,0,0;-1/1:413:0,0,0,0,0,0,0;-1/1:414:-2,0,0,0,0,0,0;-1/1:417:0,0,0,0,0,0,0;-1/1:418:-2,0,0,0,0,0,0;-1/1:419:0,0,0,0,0,0,0;-1/1:420:-2,0,0,0,0,0,0;-1/1:423:0,0,0,0,0,0,0;-1/1:424:-2,0,0,0,0,0,0;-1/1:425:0,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;-1/1:429:0,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:437:0,0,0,0,0,0,0;-1/1:438:-2,0,0,0,0,0,0;-1/1:442:-2,0,0,0,0,0,0;-1/1:443:0,0,0,0,0,0,0;-1/1:447:0,0,0,0,0,0,0;-1/1:448:-2,0,0,0,0,0,0;-1/1:450:-2,0,0,0,0,0,0;-1/1:453:0,0,0,0,0,0,0;-1/1:454:-2,0,0,0,0,0,0;-1/1:455:0,0,0,0,0,0,0;-1/1:459:0,0,0,0,0,0,0;-1/1:460:-2,0,0,0,0,0,0;-1/1:465:0,0,0,0,0,0,0;-1/1:467:0,0,0,0,0,0,0;-1/1:468:-2,0,0,0,0,0,0;-1/1:473:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:474:1,0,0,0,1,0,0;-1/1:478:-2,0,0,0,0,0,0;-1/1:479:0,0,0,0,0,0,0;-1/1:480:-2,0,0,0,0,0,0;-1/1:484:-2,0,0,0,0,0,0;-1/1:485:0,0,0,0,0,0,0;-1/1:489:0,0,0,0,0,0,0;-1/1:492:-2,0,0,0,0,0,0;-1/1:495:0,0,0,0,0,0,0;-1/1:497:0,0,0,0,0,0,0;-1/1:498:-2,0,0,0,0,0,0;-1/1:503:0,0,0,0,0,0,0;-1/1:508:-2,0,0,0,0,0,0;-1/1:509:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;-1/1:513:0,0,0,0,0,0,0;-1/1:515:0,0,0,0,0,0,0;-1/1:520:-2,0,0,0,0,0,0;-1/1:527:0,0,0,0,0,0,0;-1/1:537:0,0,0,0,0,0,0;-1/1:538:-2,0,0,0,0,0,0;-1/1:544:-2,0,0,0,0,0,0;-1/1:545:0,0,0,0,0,0,0;-1/1:549:0,0,0,0,0,0,0;-1/1:552:-2,0,0,0,0,0,0;-1/1:555:0,0,0,0,0,0,0;-1/1:557:0,0,0,0,0,0,0;-1/1:558:-2,0,0,0,0,0,0;-1/1:562:-2,0,0,0,0,0,0;-1/1:563:0,0,0,0,0,0,0;-1/1:564:-2,0,0,0,0,0,0;-1/1:568:-2,0,0,0,0,0,0;-1/1:569:0,0,0,0,0,0,0;-1/1:573:0,0,0,0,0,0,0;-1/1:574:-2,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:1,-2,0,0,1,0,0;-1/1:579:0,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:582:-2,0,0,0,0,0,0;-1/1:585:0,0,0,0,0,0,0;-1/1:587:0,0,0,0,0,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:593:0,0,0,0,0,0,0;-1/1:594:-2,0,0,0,0,0,0;-1/1:597:0,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:600:-2,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;-1/1:605:0,0,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;-1/1:609:0,0,0,0,0,0,0;-1/1:610:-2,0,0,0,0,0,0;-1/1:615:0,0,0,0,0,0,0;1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:623:0,0,0,0,0,0,0;-1/1:624:-2,0,0,0,0,0,0;1/1:624:-1,-2,0,0,1,0,0;-1/1:627:0,0,0,0,0,0,0;-1/1:628:-2,0,0,0,0,0,0;-1/1:629:0,0,0,0,0,0,0;-1/1:630:-2,0,0,0,0,0,0;-1/1:633:0,0,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;-1/1:635:0,0,0,0,0,0,0;-1/1:639:0,0,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;-1/1:646:-1,0,0,0,1,0,0;-1/1:647:0,0,0,0,0,0,0;-1/1:648:-2,0,0,0,0,0,0;-1/1:652:-2,0,0,0,0,0,0;-1/1:653:0,0,0,0,0,0,0;-1/1:657:0,0,0,0,0,0,0;-1/1:658:-2,0,0,0,0,0,0;-1/1:660:-2,0,0,0,0,0,0;-1/1:663:0,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;-1/1:665:0,0,0,0,0,0,0;-1/1:669:0,0,0,0,0,0,0;-1/1:670:-2,0,0,0,0,0,0;-1/1:672:-2,0,0,0,0,0,0;-1/1:675:0,0,0,0,0,0,0;-1/1:677:0,0,0,0,0,0,0;-1/1:678:-2,0,0,0,0,0,0;-1/1:683:0,0,0,0,0,0,0;-1/1:684:-2,0,0,0,0,0,0;-1/1:688:-2,0,0,0,0,0,0;-1/1:689:0,0,0,0,0,0,0;-1/1:690:-2,0,0,0,0,0,0;-1/1:693:0,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0;-1/1:695:0,0,0,0,0,0,0;1/1:696:-1,0,0,0,1,0,0;-1/1:699:0,0,0,0,0,0,0;-1/1:702:-4,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:705:0,0,0,0,0,0,0;-1/1:707:0,0,0,0,0,0,0;-1/1:708:-2,0,0,0,0,0,0;-1/1:713:0,0,0,0,0,0,0;-1/1:714:-2,0,0,0,0,0,0;-1/1:717:0,0,0,0,0,0,0;-1/1:718:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:719:0,0,0,0,0,0,0;-1/1:720:-2,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;-1/1:725:0,0,0,0,0,0,0;-1/1:730:-2,0,0,0,0,0,0;-1/1:732:-2,0,0,0,0,0,0;-1/1:735:0,0,0,0,0,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:742:-2,0,0,0,0,0,0;-1/1:744:-2,0,0,0,0,0,0;-1/1:747:0,0,0,0,0,0,0;-1/1:748:-2,0,0,0,0,0,0;-1/1:749:0,0,0,0,0,0,0;-1/1:750:-2,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;-1/1:755:0,0,0,0,0,0,0;-1/1:759:0,0,0,0,0,0,0;-1/1:760:-2,0,0,0,0,0,0;-1/1:762:-2,0,0,0,0,0,0;-1/1:765:0,0,0,0,0,0,0;-1/1:767:0,0,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;-1/1:773:0,0,0,0,0,0,0;-1/1:774:-2,0,0,0,0,0,0;-1/1:777:0,0,0,0,0,0,0;-1/1:778:-2,0,0,0,0,0,0;-1/1:779:0,0,0,0,0,0,0;-1/1:783:0,0,0,0,0,0,0;-1/1:784:-2,0,0,0,0,0,0;-1/1:789:0,0,0,0,0,0,0;-1/1:790:-2,0,0,0,0,0,0;-1/1:792:-2,0,0,0,0,0,0;-1/1:795:0,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;-1/1:797:0,0,0,0,0,0,0;-1/1:798:-2,0,0,0,0,0,0;-1/1:802:-2,0,0,0,0,0,0;-1/1:803:0,0,0,0,0,0,0;-1/1:804:-2,0,0,0,0,0,0;-1/1:807:0,0,0,0,0,0,0;-1/1:809:0,0,0,0,0,0,0;-1/1:810:-2,0,0,0,0,0,0;-1/1:814:-2,0,0,0,0,0,0;-1/1:815:0,0,0,0,0,0,0;-1/1:819:0,0,0,0,0,0,0;-1/1:820:-2,0,0,0,0,0,0;-1/1:825:0,0,0,0,0,0,0;-1/1:828:-2,0,0,0,0,0,0;-1/1:832:-2,0,0,0,0,0,0;-1/1:833:0,0,0,0,0,0,0;-1/1:834:-2,0,0,0,0,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:837:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:839:0,0,0,0,0,0,0;-1/1:843:0,0,0,0,0,0,0;-1/1:844:-2,0,0,0,0,0,0;-1/1:845:0,0,0,0,0,0,0;-1/1:849:0,0,0,0,0,0,0;-1/1:852:-2,0,0,0,0,0,0;-1/1:857:0,0,0,0,0,0,0;-1/1:858:-2,0,0,0,0,0,0;-1/1:862:-2,0,0,0,0,0,0;-1/1:863:0,0,0,0,0,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;-1/1:867:0,0,0,0,0,0,0;-1/1:870:-2,0,0,0,0,0,0;-1/1:873:0,0,0,0,0,0,0;-1/1:874:-2,0,0,0,0,0,0;-1/1:875:0,0,0,0,0,0,0;1/1:876:-3,-2,0,0,1,0,0;-1/1:879:0,0,0,0,0,0,0;-1/1:880:-2,0,0,0,0,0,0;-1/1:885:0,0,0,0,0,0,0;-1/1:887:0,0,0,0,0,0,0;1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:893:0,0,0,0,0,0,0;-1/1:894:-2,0,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;-1/1:900:-2,0,0,0,0,0,0;-1/1:903:0,0,0,0,0,0,0;-1/1:904:-2,0,0,0,0,0,0;-1/1:905:0,0,0,0,0,0,0;-1/1:909:0,0,0,0,0,0,0;-1/1:910:-2,0,0,0,0,0,0;-1/1:912:-2,0,0,0,0,0,0;-1/1:915:0,0,0,0,0,0,0;-1/1:917:0,0,0,0,0,0,0;-1/1:918:-2,0,0,0,0,0,0;-1/1:922:-2,0,0,0,0,0,0;-1/1:923:0,0,0,0,0,0,0;-1/1:927:0,0,0,0,0,0,0;-1/1:928:-2,0,0,0,0,0,0;-1/1:929:0,0,0,0,0,0,0;-1/1:930:-2,0,0,0,0,0,0;-1/1:933:0,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:935:0,0,0,0,0,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0;-1/1:940:-2,0,0,0,0,0,0;-1/1:942:-2,0,0,0,0,0,0;-1/1:945:0,0,0,0,0,0,0;-1/1:947:0,0,0,0,0,0,0;-1/1:952:-2,0,0,0,0,0,0;-1/1:954:-2,0,0,0,0,0,0;-1/1:957:0,0,0,0,0,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:959:0,0,0,0,0,0,0;-1/1:964:-2,0,0,0,0,0,0;-1/1:970:-2,0,0,0,0,0,0;-1/1:972:-2,0,0,0,0,0,0;-1/1:977:0,0,0,0,0,0,0;-1/1:978:-2,0,0,0,0,0,0;-1/1:982:-2,0,0,0,0,0,0;-1/1:983:0,0,0,0,0,0,0;-1/1:984:-2,0,0,0,0,0,0;-1/1:988:-2,0,0,0,0,0,0;-1/1:989:0,0,0,0,0,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:993:0,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:999:0,0,0,0,0,0,0;-1/1:1002:-2,0,0,0,0,0,0;-1/1:1005:0,0,0,0,0,0,0;-1/1:1012:-2,0,0,0,0,0,0;-1/1:1013:0,0,0,0,0,0,0;-1/1:1014:-2,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0;-1/1:1017:0,0,0,0,0,0,0;-1/1:1019:0,0,0,0,0,0,0;-1/1:1020:-2,0,0,0,0,0,0;-1/1:1024:-2,0,0,0,0,0,0;-1/1:1025:0,0,0,0,0,0,0;-1/1:1030:-2,0,0,0,0,0,0;-1/1:1042:-2,0,0,0,0,0,0"

compact_certificate theorem operation977_suffix64 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 64)=operation977Result64 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 64 32
    operation977Result64 operation977Result96 operation977_suffix96
  decide +kernel

compact_certificate def operation977Result32 : Poly := laurent_polynomial% "-1/1:5:0,0,0,0,0,0,0;-1/1:9:0,0,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-1/1:18:-2,0,0,0,0,0,0;-1/1:22:-2,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;-1/1:27:0,0,0,0,0,0,0;-1/1:30:-2,0,0,0,0,0,0;-1/1:33:0,0,0,0,0,0,0;-1/1:34:-2,0,0,0,0,0,0;-1/1:40:-2,0,0,0,0,0,0;-1/1:45:0,0,0,0,0,0,0;-1/1:47:0,0,0,0,0,0,0;-1/1:48:-2,0,0,0,0,0,0;-1/1:54:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,0,0,0;-1/1:59:0,0,0,0,0,0,0;-1/1:60:-2,0,0,0,0,0,0;-1/1:62:-2,0,0,0,0,0,0;-1/1:63:0,0,0,0,0,0,0;-1/1:64:-2,0,0,0,0,0,0;-1/1:65:0,0,0,0,0,0,0;-1/1:69:0,0,0,0,0,0,0;-1/1:70:-2,0,0,0,0,0,0;-1/1:72:-2,0,0,0,0,0,0;-1/1:75:0,0,0,0,0,0,0;-1/1:77:0,0,0,0,0,0,0;-1/1:78:-2,0,0,0,0,0,0;-1/1:82:-2,0,0,0,0,0,0;-1/1:83:0,0,0,0,0,0,0;-1/1:88:-2,0,0,0,0,0,0;-1/1:89:0,0,0,0,0,0,0;-1/1:93:0,0,0,0,0,0,0;-1/1:95:0,0,0,0,0,0,0;-1/1:100:-2,0,0,0,0,0,0;-1/1:102:-2,0,0,0,0,0,0;-1/1:105:0,0,0,0,0,0,0;-1/1:107:0,0,0,0,0,0,0;-1/1:112:-2,0,0,0,0,0,0;-1/1:114:-2,0,0,0,0,0,0;-1/1:117:0,0,0,0,0,0,0;-1/1:118:-2,0,0,0,0,0,0;-1/1:119:0,0,0,0,0,0,0;-1/1:120:-2,0,0,0,0,0,0;-1/1:123:0,0,0,0,0,0,0;-1/1:124:-2,0,0,0,0,0,0;-1/1:125:0,0,0,0,0,0,0;-1/1:129:0,0,0,0,0,0,0;-1/1:130:-2,0,0,0,0,0,0;-1/1:132:-2,0,0,0,0,0,0;-1/1:135:0,0,0,0,0,0,0;-1/1:137:0,0,0,0,0,0,0;-1/1:138:-2,0,0,0,0,0,0;-1/1:142:-2,0,0,0,0,0,0;-1/1:143:0,0,0,0,0,0,0;-1/1:144:-2,0,0,0,0,0,0;-1/1:147:0,0,0,0,0,0,0;-1/1:148:-2,0,0,0,0,0,0;-1/1:149:0,0,0,0,0,0,0;-1/1:153:0,0,0,0,0,0,0;-1/1:154:-2,0,0,0,0,0,0;-1/1:159:0,0,0,0,0,0,0;-1/1:160:-2,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;-1/1:165:0,0,0,0,0,0,0;-1/1:167:0,0,0,0,0,0,0;-1/1:168:-2,0,0,0,0,0,0;-1/1:172:-2,0,0,0,0,0,0;-1/1:173:0,0,0,0,0,0,0;-1/1:174:-2,0,0,0,0,0,0;-1/1:177:0,0,0,0,0,0,0;-1/1:179:0,0,0,0,0,0,0;-1/1:180:-2,0,0,0,0,0,0;-1/1:184:-2,0,0,0,0,0,0;-1/1:185:0,0,0,0,0,0,0;-1/1:189:0,0,0,0,0,0,0;-1/1:190:-2,0,0,0,0,0,0;-1/1:195:0,0,0,0,0,0,0;-1/1:198:-2,0,0,0,0,0,0;-1/1:202:-2,0,0,0,0,0,0;-1/1:203:0,0,0,0,0,0,0;-1/1:204:-2,0,0,0,0,0,0;-1/1:207:0,0,0,0,0,0,0;-1/1:208:-2,0,0,0,0,0,0;-1/1:209:0,0,0,0,0,0,0;-1/1:210:-2,0,0,0,0,0,0;-1/1:213:0,0,0,0,0,0,0;-1/1:214:-2,0,0,0,0,0,0;-1/1:215:0,0,0,0,0,0,0;-1/1:219:0,0,0,0,0,0,0;-1/1:222:-2,0,0,0,0,0,0;-1/1:227:0,0,0,0,0,0,0;-1/1:228:-2,0,0,0,0,0,0;-1/1:232:-2,0,0,0,0,0,0;-1/1:233:0,0,0,0,0,0,0;-1/1:237:0,0,0,0,0,0,0;-1/1:238:-2,0,0,0,0,0,0;-1/1:240:-2,0,0,0,0,0,0;-1/1:243:0,0,0,0,0,0,0;-1/1:244:-2,0,0,0,0,0,0;-1/1:245:0,0,0,0,0,0,0;-1/1:249:0,0,0,0,0,0,0;-1/1:250:-2,0,0,0,0,0,0;-1/1:252:-2,0,0,0,0,0,0;-1/1:255:0,0,0,0,0,0,0;-1/1:257:0,0,0,0,0,0,0;-1/1:258:-2,0,0,0,0,0,0;-1/1:263:0,0,0,0,0,0,0;-1/1:264:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;-1/1:268:-2,0,0,0,0,0,0;-1/1:269:0,0,0,0,0,0,0;-1/1:270:-2,0,0,0,0,0,0;-1/1:273:0,0,0,0,0,0,0;-1/1:274:-2,0,0,0,0,0,0;-1/1:275:0,0,0,0,0,0,0;-1/1:279:0,0,0,0,0,0,0;-1/1:280:-2,0,0,0,0,0,0;-1/1:285:0,0,0,0,0,0,0;-1/1:287:0,0,0,0,0,0,0;-1/1:288:-2,0,0,0,0,0,0;-1/1:292:-2,0,0,0,0,0,0;-1/1:293:0,0,0,0,0,0,0;-1/1:294:-2,0,0,0,0,0,0;-1/1:297:0,0,0,0,0,0,0;-1/1:298:-2,0,0,0,0,0,0;-1/1:299:0,0,0,0,0,0,0;-1/1:300:-2,0,0,0,0,0,0;-1/1:303:0,0,0,0,0,0,0;-1/1:305:0,0,0,0,0,0,0;-1/1:310:-2,0,0,0,0,0,0;-1/1:312:-2,0,0,0,0,0,0;-1/1:315:0,0,0,0,0,0,0;-1/1:317:0,0,0,0,0,0,0;-1/1:322:-2,0,0,0,0,0,0;-1/1:324:-2,0,0,0,0,0,0;-1/1:327:0,0,0,0,0,0,0;-1/1:328:-2,0,0,0,0,0,0;-1/1:329:0,0,0,0,0,0,0;-1/1:330:-2,0,0,0,0,0,0;-1/1:333:0,0,0,0,0,0,0;-1/1:334:-2,0,0,0,0,0,0;-1/1:335:0,0,0,0,0,0,0;-1/1:339:0,0,0,0,0,0,0;-1/1:340:-2,0,0,0,0,0,0;-1/1:342:-2,0,0,0,0,0,0;-1/1:345:0,0,0,0,0,0,0;-1/1:347:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:352:-2,0,0,0,0,0,0;-1/1:353:0,0,0,0,0,0,0;-1/1:354:-2,0,0,0,0,0,0;-1/1:357:0,0,0,0,0,0,0;-1/1:358:-2,0,0,0,0,0,0;-1/1:359:0,0,0,0,0,0,0;-1/1:363:0,0,0,0,0,0,0;-1/1:364:-2,0,0,0,0,0,0;-1/1:369:0,0,0,0,0,0,0;-1/1:370:-2,0,0,0,0,0,0;-1/1:372:-2,0,0,0,0,0,0;-1/1:375:0,0,0,0,0,0,0;-1/1:377:0,0,0,0,0,0,0;-1/1:378:-2,0,0,0,0,0,0;-1/1:382:-2,0,0,0,0,0,0;-1/1:383:0,0,0,0,0,0,0;-1/1:384:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:387:0,0,0,0,0,0,0;-1/1:389:0,0,0,0,0,0,0;-1/1:390:-2,0,0,0,0,0,0;-1/1:394:-2,0,0,0,0,0,0;-1/1:395:0,0,0,0,0,0,0;-1/1:396:-1,0,0,0,1,0,0;-1/1:399:0,0,0,0,0,0,0;-1/1:400:-2,0,0,0,0,0,0;-1/1:405:0,0,0,0,0,0,0;-1/1:408:-2,0,0,0,0,0,0;-1/1:408:0,0,0,0,0,0,0;-1/1:412:-2,0,0,0,0,0,0;-1/1:413:0,0,0,0,0,0,0;-1/1:414:-2,0,0,0,0,0,0;-1/1:417:0,0,0,0,0,0,0;-1/1:418:-2,0,0,0,0,0,0;-1/1:419:0,0,0,0,0,0,0;-1/1:420:-2,0,0,0,0,0,0;-1/1:423:0,0,0,0,0,0,0;-1/1:424:-2,0,0,0,0,0,0;-1/1:425:0,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;-1/1:429:0,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:437:0,0,0,0,0,0,0;-1/1:438:-2,0,0,0,0,0,0;-1/1:442:-2,0,0,0,0,0,0;-1/1:443:0,0,0,0,0,0,0;-1/1:447:0,0,0,0,0,0,0;-1/1:448:-2,0,0,0,0,0,0;-1/1:450:-2,0,0,0,0,0,0;-1/1:453:0,0,0,0,0,0,0;-1/1:454:-2,0,0,0,0,0,0;-1/1:455:0,0,0,0,0,0,0;-1/1:459:0,0,0,0,0,0,0;-1/1:460:-2,0,0,0,0,0,0;-1/1:462:-2,0,0,0,0,0,0;-1/1:465:0,0,0,0,0,0,0;-1/1:467:0,0,0,0,0,0,0;-1/1:468:-2,0,0,0,0,0,0;-1/1:473:0,0,0,0,0,0,0;-1/1:474:-2,0,0,0,0,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:474:1,0,0,0,1,0,0;-1/1:478:-2,0,0,0,0,0,0;-1/1:479:0,0,0,0,0,0,0;-1/1:480:-2,0,0,0,0,0,0;-1/1:483:0,0,0,0,0,0,0;-1/1:484:-2,0,0,0,0,0,0;-1/1:485:0,0,0,0,0,0,0;-1/1:489:0,0,0,0,0,0,0;-1/1:490:-2,0,0,0,0,0,0;-1/1:492:-2,0,0,0,0,0,0;-1/1:495:0,0,0,0,0,0,0;-1/1:497:0,0,0,0,0,0,0;-1/1:498:-2,0,0,0,0,0,0;-1/1:503:0,0,0,0,0,0,0;-1/1:508:-2,0,0,0,0,0,0;-1/1:509:0,0,0,0,0,0,0;-1/1:510:-2,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;-1/1:513:0,0,0,0,0,0,0;-1/1:515:0,0,0,0,0,0,0;-1/1:520:-2,0,0,0,0,0,0;-1/1:527:0,0,0,0,0,0,0;-1/1:534:-2,0,0,0,0,0,0;-1/1:537:0,0,0,0,0,0,0;-1/1:538:-2,0,0,0,0,0,0;-1/1:539:0,0,0,0,0,0,0;-1/1:540:-2,0,0,0,0,0,0;-1/1:544:-2,0,0,0,0,0,0;-1/1:545:0,0,0,0,0,0,0;-1/1:549:0,0,0,0,0,0,0;-1/1:552:-2,0,0,0,0,0,0;-1/1:555:0,0,0,0,0,0,0;-1/1:557:0,0,0,0,0,0,0;-1/1:558:-2,0,0,0,0,0,0;-1/1:562:-2,0,0,0,0,0,0;-1/1:563:0,0,0,0,0,0,0;-1/1:564:-2,0,0,0,0,0,0;-1/1:567:0,0,0,0,0,0,0;-1/1:568:-2,0,0,0,0,0,0;-1/1:569:0,0,0,0,0,0,0;-1/1:573:0,0,0,0,0,0,0;-1/1:574:-2,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:1,-2,0,0,1,0,0;-1/1:579:0,0,0,0,0,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:582:-2,0,0,0,0,0,0;-1/1:585:0,0,0,0,0,0,0;-1/1:587:0,0,0,0,0,0,0;-1/1:588:-2,0,0,0,0,0,0;-1/1:592:-2,0,0,0,0,0,0;-1/1:593:0,0,0,0,0,0,0;-1/1:594:-2,0,0,0,0,0,0;-1/1:597:0,0,0,0,0,0,0;-1/1:599:0,0,0,0,0,0,0;-1/1:600:-2,0,0,0,0,0,0;-1/1:604:-2,0,0,0,0,0,0;-1/1:605:0,0,0,0,0,0,0;-1/1:606:-1,0,0,0,1,0,0;-1/1:609:0,0,0,0,0,0,0;-1/1:610:-2,0,0,0,0,0,0;-1/1:615:0,0,0,0,0,0,0;1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:622:-2,0,0,0,0,0,0;-1/1:623:0,0,0,0,0,0,0;-1/1:624:-2,0,0,0,0,0,0;1/1:624:-1,-2,0,0,1,0,0;-1/1:627:0,0,0,0,0,0,0;-1/1:628:-2,0,0,0,0,0,0;-1/1:629:0,0,0,0,0,0,0;-1/1:630:-2,0,0,0,0,0,0;-1/1:633:0,0,0,0,0,0,0;-1/1:634:-2,0,0,0,0,0,0;-1/1:635:0,0,0,0,0,0,0;-1/1:639:0,0,0,0,0,0,0;-1/1:642:-2,0,0,0,0,0,0;-1/1:646:-1,0,0,0,1,0,0;-1/1:647:0,0,0,0,0,0,0;-1/1:648:-2,0,0,0,0,0,0;-1/1:652:-2,0,0,0,0,0,0;-1/1:653:0,0,0,0,0,0,0;-1/1:657:0,0,0,0,0,0,0;-1/1:658:-2,0,0,0,0,0,0;-1/1:660:-2,0,0,0,0,0,0;-1/1:663:0,0,0,0,0,0,0;-1/1:664:-2,0,0,0,0,0,0;-1/1:665:0,0,0,0,0,0,0;-1/1:669:0,0,0,0,0,0,0;-1/1:670:-2,0,0,0,0,0,0;-1/1:672:-2,0,0,0,0,0,0;-1/1:675:0,0,0,0,0,0,0;-1/1:677:0,0,0,0,0,0,0;-1/1:678:-2,0,0,0,0,0,0;-1/1:683:0,0,0,0,0,0,0;-1/1:684:-2,0,0,0,0,0,0;-1/1:688:-2,0,0,0,0,0,0;-1/1:689:0,0,0,0,0,0,0;-1/1:690:-2,0,0,0,0,0,0;-1/1:693:0,0,0,0,0,0,0;-1/1:694:-2,0,0,0,0,0,0;-1/1:695:0,0,0,0,0,0,0;1/1:696:-1,0,0,0,1,0,0;-1/1:699:0,0,0,0,0,0,0;-1/1:700:-2,0,0,0,0,0,0;-1/1:702:-4,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:705:0,0,0,0,0,0,0;-1/1:707:0,0,0,0,0,0,0;-1/1:708:-2,0,0,0,0,0,0;-1/1:713:0,0,0,0,0,0,0;-1/1:714:-2,0,0,0,0,0,0;-1/1:717:0,0,0,0,0,0,0;-1/1:718:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:719:0,0,0,0,0,0,0;-1/1:720:-2,0,0,0,0,0,0;-1/1:723:0,0,0,0,0,0,0;-1/1:725:0,0,0,0,0,0,0;-1/1:730:-2,0,0,0,0,0,0;-1/1:732:-2,0,0,0,0,0,0;-1/1:735:0,0,0,0,0,0,0;-1/1:737:0,0,0,0,0,0,0;-1/1:742:-2,0,0,0,0,0,0;-1/1:744:-2,0,0,0,0,0,0;-1/1:747:0,0,0,0,0,0,0;-1/1:748:-2,0,0,0,0,0,0;-1/1:749:0,0,0,0,0,0,0;-1/1:750:-2,0,0,0,0,0,0;-1/1:753:0,0,0,0,0,0,0;-1/1:754:-2,0,0,0,0,0,0;-1/1:755:0,0,0,0,0,0,0;-1/1:759:0,0,0,0,0,0,0;-1/1:760:-2,0,0,0,0,0,0;-1/1:762:-2,0,0,0,0,0,0;-1/1:765:0,0,0,0,0,0,0;-1/1:767:0,0,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:772:-2,0,0,0,0,0,0;-1/1:773:0,0,0,0,0,0,0;-1/1:774:-2,0,0,0,0,0,0;-1/1:777:0,0,0,0,0,0,0;-1/1:778:-2,0,0,0,0,0,0;-1/1:779:0,0,0,0,0,0,0;-1/1:783:0,0,0,0,0,0,0;-1/1:784:-2,0,0,0,0,0,0;-1/1:789:0,0,0,0,0,0,0;-1/1:790:-2,0,0,0,0,0,0;-1/1:792:-2,0,0,0,0,0,0;-1/1:795:0,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;-1/1:797:0,0,0,0,0,0,0;-1/1:798:-2,0,0,0,0,0,0;-1/1:802:-2,0,0,0,0,0,0;-1/1:803:0,0,0,0,0,0,0;-1/1:804:-2,0,0,0,0,0,0;-1/1:807:0,0,0,0,0,0,0;-1/1:809:0,0,0,0,0,0,0;-1/1:810:-2,0,0,0,0,0,0;-1/1:814:-2,0,0,0,0,0,0;-1/1:815:0,0,0,0,0,0,0;-1/1:819:0,0,0,0,0,0,0;-1/1:820:-2,0,0,0,0,0,0;-1/1:825:0,0,0,0,0,0,0;-1/1:828:-2,0,0,0,0,0,0;-1/1:832:-2,0,0,0,0,0,0;-1/1:833:0,0,0,0,0,0,0;-1/1:834:-2,0,0,0,0,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:837:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:839:0,0,0,0,0,0,0;-1/1:843:0,0,0,0,0,0,0;-1/1:844:-2,0,0,0,0,0,0;-1/1:845:0,0,0,0,0,0,0;-1/1:849:0,0,0,0,0,0,0;-1/1:852:-2,0,0,0,0,0,0;-1/1:857:0,0,0,0,0,0,0;-1/1:858:-2,0,0,0,0,0,0;-1/1:862:-2,0,0,0,0,0,0;-1/1:863:0,0,0,0,0,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;-1/1:867:0,0,0,0,0,0,0;-1/1:868:-2,0,0,0,0,0,0;-1/1:870:-2,0,0,0,0,0,0;-1/1:873:0,0,0,0,0,0,0;-1/1:874:-2,0,0,0,0,0,0;-1/1:875:0,0,0,0,0,0,0;1/1:876:-3,-2,0,0,1,0,0;-1/1:879:0,0,0,0,0,0,0;-1/1:880:-2,0,0,0,0,0,0;-1/1:882:-2,0,0,0,0,0,0;-1/1:885:0,0,0,0,0,0,0;-1/1:887:0,0,0,0,0,0,0;1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:893:0,0,0,0,0,0,0;-1/1:894:-2,0,0,0,0,0,0;-1/1:898:-2,0,0,0,0,0,0;-1/1:899:0,0,0,0,0,0,0;-1/1:900:-2,0,0,0,0,0,0;-1/1:903:0,0,0,0,0,0,0;-1/1:904:-2,0,0,0,0,0,0;-1/1:905:0,0,0,0,0,0,0;-1/1:909:0,0,0,0,0,0,0;-1/1:910:-2,0,0,0,0,0,0;-1/1:912:-2,0,0,0,0,0,0;-1/1:915:0,0,0,0,0,0,0;-1/1:917:0,0,0,0,0,0,0;-1/1:918:-2,0,0,0,0,0,0;-1/1:922:-2,0,0,0,0,0,0;-1/1:923:0,0,0,0,0,0,0;-1/1:924:-2,0,0,0,0,0,0;-1/1:927:0,0,0,0,0,0,0;-1/1:928:-2,0,0,0,0,0,0;-1/1:929:0,0,0,0,0,0,0;-1/1:930:-2,0,0,0,0,0,0;-1/1:933:0,0,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:935:0,0,0,0,0,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0;-1/1:940:-2,0,0,0,0,0,0;-1/1:942:-2,0,0,0,0,0,0;-1/1:945:0,0,0,0,0,0,0;-1/1:947:0,0,0,0,0,0,0;-1/1:952:-2,0,0,0,0,0,0;-1/1:954:-2,0,0,0,0,0,0;-1/1:957:0,0,0,0,0,0,0;-1/1:958:-2,0,0,0,0,0,0;-1/1:959:0,0,0,0,0,0,0;-1/1:964:-2,0,0,0,0,0,0;-1/1:965:0,0,0,0,0,0,0;-1/1:970:-2,0,0,0,0,0,0;-1/1:972:-2,0,0,0,0,0,0;-1/1:975:0,0,0,0,0,0,0;-1/1:977:0,0,0,0,0,0,0;-1/1:978:-2,0,0,0,0,0,0;-1/1:982:-2,0,0,0,0,0,0;-1/1:983:0,0,0,0,0,0,0;-1/1:984:-2,0,0,0,0,0,0;-1/1:987:0,0,0,0,0,0,0;-1/1:988:-2,0,0,0,0,0,0;-1/1:989:0,0,0,0,0,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:993:0,0,0,0,0,0,0;-1/1:994:-2,0,0,0,0,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:999:0,0,0,0,0,0,0;-1/1:1000:-2,0,0,0,0,0,0;-1/1:1002:-2,0,0,0,0,0,0;-1/1:1005:0,0,0,0,0,0,0;-1/1:1007:0,0,0,0,0,0,0;-1/1:1012:-2,0,0,0,0,0,0;-1/1:1013:0,0,0,0,0,0,0;-1/1:1014:-2,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0;-1/1:1017:0,0,0,0,0,0,0;-1/1:1019:0,0,0,0,0,0,0;-1/1:1020:-2,0,0,0,0,0,0;-1/1:1024:-2,0,0,0,0,0,0;-1/1:1025:0,0,0,0,0,0,0;-1/1:1030:-2,0,0,0,0,0,0;-1/1:1035:0,0,0,0,0,0,0;-1/1:1042:-2,0,0,0,0,0,0"

compact_certificate theorem operation977_suffix32 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 32)=operation977Result32 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 32 32
    operation977Result32 operation977Result64 operation977_suffix64
  decide +kernel

compact_certificate def operation977Result0 : Poly := laurent_polynomial% "1/1:53:0,0,0,0,0,0,0;-1/1:62:-2,0,0,0,0,0,0;-1/1:264:-1,-2,0,0,1,0,0;-1/1:264:0,-1,0,0,0,1,0;1/1:282:-2,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;1/1:348:0,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;-1/1:396:-1,0,0,0,1,0,0;-1/1:408:0,0,0,0,0,0,0;-1/1:426:-1,0,0,0,1,0,0;1/1:432:-2,0,0,0,0,0,0;-1/1:432:2,0,0,0,0,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:474:1,0,0,0,1,0,0;-1/1:512:-2,0,0,0,0,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:1,-2,0,0,1,0,0;-1/1:606:-1,0,0,0,1,0,0;1/1:618:-2,-2,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;1/1:624:-1,-2,0,0,1,0,0;-1/1:646:-1,0,0,0,1,0,0;1/1:696:-1,0,0,0,1,0,0;-1/1:702:-4,-2,0,0,0,0,0;1/1:712:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;-1/1:796:-1,0,0,0,1,0,0;1/1:834:-1,-2,0,0,1,0,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:1,0,0,0,1,0,0;1/1:876:-3,-2,0,0,1,0,0;1/1:888:-2,-2,0,0,0,0,0;1/1:934:-3,0,0,0,1,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-1,0,0,0,1,0,0;-1/1:992:-2,0,0,0,2,0,0;-1/1:998:0,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0"

compact_certificate theorem operation977_suffix0 : substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 977).drop 0)=operation977Result0 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 977) 0 32
    operation977Result0 operation977Result32 operation977_suffix32
  decide +kernel

#print axioms operation977_suffix0
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentEliminationCheck30SingleFamilyV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows
compact_certificate theorem operations_checked_30_single0 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 960)=normal 960 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single0 : ∀ t ∈ operations 960,
    t.2.1<4600+960 := by decide +kernel
#print axioms operations_checked_30_single0
#print axioms operations_prior_30_single0

compact_certificate theorem operations_checked_30_single1 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 961)=normal 961 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single1 : ∀ t ∈ operations 961,
    t.2.1<4600+961 := by decide +kernel
#print axioms operations_checked_30_single1
#print axioms operations_prior_30_single1

compact_certificate theorem operations_checked_30_single2 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 962)=normal 962 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single2 : ∀ t ∈ operations 962,
    t.2.1<4600+962 := by decide +kernel
#print axioms operations_checked_30_single2
#print axioms operations_prior_30_single2

compact_certificate theorem operations_checked_30_single3 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 963)=normal 963 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single3 : ∀ t ∈ operations 963,
    t.2.1<4600+963 := by decide +kernel
#print axioms operations_checked_30_single3
#print axioms operations_prior_30_single3

compact_certificate theorem operations_checked_30_single4 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 964)=normal 964 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single4 : ∀ t ∈ operations 964,
    t.2.1<4600+964 := by decide +kernel
#print axioms operations_checked_30_single4
#print axioms operations_prior_30_single4

compact_certificate theorem operations_checked_30_single5 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 965)=normal 965 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single5 : ∀ t ∈ operations 965,
    t.2.1<4600+965 := by decide +kernel
#print axioms operations_checked_30_single5
#print axioms operations_prior_30_single5

compact_certificate theorem operations_checked_30_single6 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 966)=normal 966 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single6 : ∀ t ∈ operations 966,
    t.2.1<4600+966 := by decide +kernel
#print axioms operations_checked_30_single6
#print axioms operations_prior_30_single6

compact_certificate theorem operations_checked_30_single7 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 967)=normal 967 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single7 : ∀ t ∈ operations 967,
    t.2.1<4600+967 := by decide +kernel
#print axioms operations_checked_30_single7
#print axioms operations_prior_30_single7

compact_certificate theorem operations_checked_30_single8 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 968)=normal 968 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single8 : ∀ t ∈ operations 968,
    t.2.1<4600+968 := by decide +kernel
#print axioms operations_checked_30_single8
#print axioms operations_prior_30_single8

compact_certificate theorem operations_checked_30_single9 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 969)=normal 969 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single9 : ∀ t ∈ operations 969,
    t.2.1<4600+969 := by decide +kernel
#print axioms operations_checked_30_single9
#print axioms operations_prior_30_single9

compact_certificate theorem operations_checked_30_single10 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 970)=normal 970 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single10 : ∀ t ∈ operations 970,
    t.2.1<4600+970 := by decide +kernel
#print axioms operations_checked_30_single10
#print axioms operations_prior_30_single10

compact_certificate theorem operations_checked_30_single11 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 971)=normal 971 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single11 : ∀ t ∈ operations 971,
    t.2.1<4600+971 := by decide +kernel
#print axioms operations_checked_30_single11
#print axioms operations_prior_30_single11

compact_certificate theorem operations_checked_30_single12 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 972)=normal 972 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single12 : ∀ t ∈ operations 972,
    t.2.1<4600+972 := by decide +kernel
#print axioms operations_checked_30_single12
#print axioms operations_prior_30_single12

compact_certificate theorem operations_checked_30_single13 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 973)=normal 973 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single13 : ∀ t ∈ operations 973,
    t.2.1<4600+973 := by decide +kernel
#print axioms operations_checked_30_single13
#print axioms operations_prior_30_single13

compact_certificate theorem operations_checked_30_single14 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 974)=normal 974 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single14 : ∀ t ∈ operations 974,
    t.2.1<4600+974 := by decide +kernel
#print axioms operations_checked_30_single14
#print axioms operations_prior_30_single14

compact_certificate theorem operations_checked_30_single15 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 975)=normal 975 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single15 : ∀ t ∈ operations 975,
    t.2.1<4600+975 := by decide +kernel
#print axioms operations_checked_30_single15
#print axioms operations_prior_30_single15

compact_certificate theorem operations_checked_30_single16 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 976)=normal 976 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single16 : ∀ t ∈ operations 976,
    t.2.1<4600+976 := by decide +kernel
#print axioms operations_checked_30_single16
#print axioms operations_prior_30_single16

compact_certificate theorem operations_checked_30_single17 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 977)=normal 977 := by
  rw [← substituteCompute_eq]
  calc
    _ = operation977Result0 := by simpa only [List.drop_zero] using operation977_suffix0
    _ = normal 977 := by decide +kernel
compact_certificate theorem operations_prior_30_single17 : ∀ t ∈ operations 977,
    t.2.1<4600+977 := by decide +kernel
#print axioms operations_checked_30_single17
#print axioms operations_prior_30_single17

compact_certificate theorem operations_checked_30_single18 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 978)=normal 978 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single18 : ∀ t ∈ operations 978,
    t.2.1<4600+978 := by decide +kernel
#print axioms operations_checked_30_single18
#print axioms operations_prior_30_single18

compact_certificate theorem operations_checked_30_single19 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 979)=normal 979 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single19 : ∀ t ∈ operations 979,
    t.2.1<4600+979 := by decide +kernel
#print axioms operations_checked_30_single19
#print axioms operations_prior_30_single19

compact_certificate private def operation980BoundedValue305 : Poly := []

compact_certificate private theorem operation980BoundedCheck305 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 305) = operation980BoundedValue305 := by
  decide +kernel

compact_certificate private def operation980BoundedValue304 : Poly := laurent_polynomial% "1/1:62:-2,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-1,0,0,0,1,0,0;-1/1:162:-2,0,0,0,0,0,0;-1/1:174:-3,0,0,0,1,0,0;-1/1:186:-2,-1,0,0,0,1,0;-1/1:234:-1,-2,0,0,1,0,0;1/1:264:-1,-2,0,0,1,0,0;1/1:278:0,0,0,0,0,0,0;1/1:348:-4,0,0,0,0,0,0;-1/1:348:-1,-1,0,0,1,1,0;1/1:386:-1,0,0,0,1,0,0;1/1:402:0,-2,0,0,0,0,0;-1/1:432:-2,0,0,0,0,0,0;-1/1:444:-1,-2,0,0,1,0,0;1/1:444:1,0,0,0,1,0,0;-1/1:474:1,0,0,0,1,0,0;1/1:618:-1,-1,0,0,1,1,0;1/1:646:-1,0,0,0,1,0,0;-1/1:676:-1,0,0,0,1,0,0;1/1:702:-2,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;1/1:796:-1,0,0,0,1,0,0;-1/1:834:-1,-2,0,0,1,0,0;-1/1:834:0,-1,0,0,0,1,0;-1/1:876:-1,0,0,0,1,0,0;-1/1:888:0,0,0,0,2,0,0;-1/1:934:-3,0,0,0,1,0,0;-1/1:936:-1,0,0,0,1,0,0;1/1:992:-2,0,0,0,2,0,0;1/1:1016:-1,0,0,0,1,0,0"

compact_certificate private theorem operation980BoundedCheck304 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 304) = operation980BoundedValue304 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 304 1
    operation980BoundedValue304 operation980BoundedValue305 operation980BoundedCheck305
  decide +kernel

compact_certificate private def operation980BoundedValue296 : Poly := laurent_polynomial% "1/1:34:-1,0,0,0,1,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;1/1:62:-2,0,0,0,0,0,0;-1/1:62:0,0,0,0,0,0,0;-1/1:68:-2,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-2/1:162:-2,0,0,0,0,0,0;1/1:162:0,-2,0,0,2,0,0;1/1:162:0,0,0,0,0,0,0;1/1:162:1,0,0,0,1,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-1,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;-1/1:172:0,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;-1/1:174:-3,0,0,0,1,0,0;1/1:174:-1,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:186:-3,0,0,0,1,0,0;-2/1:186:-2,-1,0,0,0,1,0;-1/1:186:1,-2,0,0,1,0,0;-1/1:186:1,0,0,0,1,0,0;1/1:216:-2,-1,0,0,0,1,0;-1/1:216:-1,0,0,0,1,0,0;1/1:216:0,-1,0,0,0,1,0;1/1:234:-2,-1,0,0,0,1,0;-2/1:234:-1,-2,0,0,1,0,0;-1/1:264:-2,-2,0,0,0,0,0;1/1:264:-1,-2,0,0,1,0,0;-1/1:264:-1,-1,0,0,1,1,0;1/1:264:-1,0,0,0,1,0,0;-1/1:264:0,0,0,0,0,0,0;1/1:278:0,0,0,0,0,0,0;-1/1:282:-2,-2,0,0,0,0,0;-1/1:282:-2,0,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;1/1:297:0,-2,0,0,0,0,0;-1/1:302:-2,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:332:-2,0,0,0,0,0,0;-1/1:332:0,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;1/1:348:-4,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;-1/1:348:-1,-1,0,0,1,1,0;1/1:348:-1,0,0,0,1,0,0;1/1:348:0,-2,0,0,0,0,0;-1/1:354:-1,-2,0,0,1,0,0;-1/1:354:0,-1,0,0,0,1,0;-1/1:386:-2,0,0,0,0,0,0;1/1:386:-1,0,0,0,1,0,0;-1/1:396:-2,-1,0,0,0,1,0;-1/1:396:-2,0,0,0,0,0,0;-1/1:396:0,-2,0,0,0,0,0;1/1:396:0,-1,0,0,0,1,0;1/1:398:-2,0,0,0,0,0,0;-1/1:398:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:408:-1,0,0,0,1,0,0;-1/1:426:-3,-2,0,0,1,0,0;2/1:426:-2,-1,0,0,0,1,0;-1/1:426:-2,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-1/1:426:-1,0,0,0,1,0,0;1/1:426:0,-1,0,0,0,1,0;-1/1:432:-2,-2,0,0,0,0,0;-1/1:432:-2,0,0,0,0,0,0;1/1:432:0,-2,0,0,0,0,0;2/1:432:0,0,0,0,0,0,0;-1/1:432:1,0,0,0,1,0,0;1/1:444:-2,-1,0,0,0,1,0;-1/1:444:0,-1,0,0,0,1,0;1/1:444:1,-2,0,0,1,0,0;2/1:444:1,0,0,0,1,0,0;1/1:474:-1,-2,0,0,1,0,0;-1/1:474:-1,-1,0,0,1,1,0;1/1:474:-1,0,0,0,1,0,0;-1/1:474:0,-1,0,0,0,1,0;1/1:474:0,0,0,0,0,0,0;-1/1:474:2,-1,0,0,0,1,0;-1/1:512:-2,0,0,0,0,0,0;2/1:576:-2,-1,0,0,0,1,0;-1/1:576:-2,0,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;-1/1:576:-1,0,0,0,1,0,0;-1/1:576:0,-2,0,0,0,0,0;1/1:576:0,-1,0,0,0,1,0;-1/1:576:2,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;-1/1:606:-2,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:606:0,-2,0,0,0,0,0;1/1:606:0,-1,0,0,0,1,0;-1/1:606:1,-2,0,0,1,0,0;-1/1:606:2,0,0,0,0,0,0;-2/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;2/1:618:-1,-1,0,0,1,1,0;-1/1:618:-1,0,0,0,1,0,0;1/1:618:0,0,0,0,0,0,0;1/1:618:2,-2,0,0,0,0,0;1/1:618:2,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:624:-2,-2,0,0,0,0,0;1/1:624:-1,-2,0,0,1,0,0;1/1:624:0,0,0,0,0,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:642:-2,-2,0,0,0,0,0;1/1:642:-2,0,0,0,0,0,0;2/1:642:0,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:646:-2,0,0,0,0,0,0;1/1:646:-1,0,0,0,1,0,0;1/1:648:-1,-1,0,0,1,1,0;-1/1:676:-1,0,0,0,1,0,0;-1/1:696:-2,-1,0,0,0,1,0;1/1:696:-2,0,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;-1/1:702:-3,-1,0,0,1,1,0;-1/1:702:0,-2,0,0,0,0,0;-2/1:702:0,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;1/1:712:0,0,0,0,0,0,0;-1/1:718:-4,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;1/1:766:-1,0,0,0,1,0,0;-2/1:768:-2,-2,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:772:0,0,0,0,0,0,0;-1/1:796:-2,0,0,0,0,0,0;2/1:796:-1,0,0,0,1,0,0;1/1:834:-2,-2,0,0,0,0,0;-1/1:834:-1,-2,0,0,1,0,0;-1/1:834:0,-1,0,0,0,1,0;1/1:834:0,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;-1/1:864:-2,-2,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;-1/1:864:0,0,0,0,0,0,0;1/1:864:0,0,0,0,2,0,0;-1/1:876:-3,-2,0,0,1,0,0;1/1:876:-2,-1,0,0,0,1,0;1/1:876:-2,-1,0,0,2,1,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:876:-1,0,0,0,1,0,0;1/1:876:0,-1,0,0,0,1,0;-1/1:878:-4,0,0,0,0,0,0;1/1:878:-2,0,0,0,0,0,0;1/1:884:-3,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;2/1:888:-1,-1,0,0,1,1,0;-1/1:888:0,-2,0,0,2,0,0;1/1:888:0,0,0,0,0,0,0;-2/1:888:0,0,0,0,2,0,0;-1/1:902:0,0,0,0,0,0,0;1/1:934:-4,0,0,0,0,0,0;-1/1:934:-3,0,0,0,1,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-2,0,0,0,0,0,0;-1/1:936:-1,0,0,0,1,0,0;-1/1:936:0,-1,0,0,0,1,0;-1/1:992:-3,0,0,0,1,0,0;1/1:992:-2,0,0,0,2,0,0;-1/1:992:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;-1/1:1016:-2,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0"

compact_certificate private theorem operation980BoundedCheck296 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 296) = operation980BoundedValue296 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 296 8
    operation980BoundedValue296 operation980BoundedValue304 operation980BoundedCheck304
  decide +kernel

compact_certificate private def operation980BoundedValue288 : Poly := laurent_polynomial% "1/1:34:-1,0,0,0,1,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;1/1:62:-2,0,0,0,0,0,0;-1/1:62:0,0,0,0,0,0,0;1/1:64:-1,0,0,0,1,0,0;-1/1:68:-2,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;1/1:136:-1,0,0,0,1,0,0;-2/1:162:-2,0,0,0,0,0,0;1/1:162:-1,-1,0,0,1,1,0;1/1:162:0,0,0,0,0,0,0;1/1:162:1,-1,0,0,1,1,0;1/1:162:1,0,0,0,1,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-1,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;-1/1:172:0,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;-1/1:174:-3,0,0,0,1,0,0;1/1:174:-2,-1,0,0,0,1,0;1/1:174:-2,-1,0,0,2,1,0;1/1:174:-1,0,0,0,1,0,0;2/1:174:0,-1,0,0,0,1,0;2/1:186:-3,0,0,0,1,0,0;-2/1:186:-2,-1,0,0,0,1,0;-1/1:186:-1,0,0,0,1,0,0;-1/1:186:0,-1,0,0,2,1,0;-1/1:186:1,0,0,0,1,0,0;1/1:216:-2,-1,0,0,0,1,0;1/1:216:0,-1,0,0,0,1,0;1/1:234:-2,-1,0,0,0,1,0;-1/1:234:-1,-2,0,0,1,0,0;-1/1:234:-1,0,0,0,1,0,0;-1/1:264:-2,-2,0,0,0,0,0;1/1:264:-1,-2,0,0,1,0,0;-1/1:264:-1,-1,0,0,1,1,0;1/1:264:-1,0,0,0,1,0,0;1/1:264:0,-1,0,0,0,1,0;-1/1:264:0,0,0,0,0,0,0;1/1:278:0,0,0,0,0,0,0;-1/1:282:-2,-2,0,0,0,0,0;-1/1:282:-2,0,0,0,0,0,0;-1/1:282:0,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;1/1:297:0,-2,0,0,0,0,0;-1/1:302:-2,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:332:0,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;1/1:348:-4,0,0,0,0,0,0;-1/1:348:-3,-1,0,0,1,1,0;-1/1:348:-2,0,0,0,0,0,0;1/1:348:-1,0,0,0,1,0,0;1/1:348:0,-2,0,0,0,0,0;-2/1:348:0,0,0,0,0,0,0;-1/1:354:-2,-1,0,0,0,1,0;-2/1:354:0,-1,0,0,0,1,0;-1/1:386:-2,0,0,0,0,0,0;-1/1:396:-2,-1,0,0,0,1,0;-1/1:396:-2,0,0,0,0,0,0;-1/1:396:0,-2,0,0,0,0,0;1/1:396:0,-1,0,0,0,1,0;-1/1:398:0,0,0,0,0,0,0;1/1:402:-2,-2,0,0,0,0,0;-1/1:402:-1,-1,0,0,1,1,0;1/1:402:0,-2,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:408:-1,-1,0,0,1,1,0;-1/1:408:-1,0,0,0,1,0,0;-1/1:426:-3,-2,0,0,1,0,0;2/1:426:-2,-1,0,0,0,1,0;-1/1:426:-2,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;1/1:426:0,-1,0,0,0,1,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-2,0,0,0,0,0,0;1/1:432:-1,-1,0,0,1,1,0;-2/1:432:0,-2,0,0,0,0,0;3/1:432:0,0,0,0,0,0,0;-1/1:432:1,0,0,0,1,0,0;1/1:432:2,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:1,-2,0,0,1,0,0;1/1:444:1,0,0,0,1,0,0;1/1:474:-2,-1,0,0,0,1,0;-1/1:474:-1,-1,0,0,1,1,0;1/1:474:-1,0,0,0,1,0,0;1/1:474:0,-1,0,0,0,1,0;1/1:474:0,0,0,0,0,0,0;-1/1:474:1,0,0,0,1,0,0;-1/1:474:2,-1,0,0,0,1,0;1/1:488:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;2/1:576:-2,-1,0,0,0,1,0;-1/1:576:-2,0,0,0,0,0,0;-1/1:576:0,-2,0,0,0,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:576:2,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;-1/1:606:-2,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:606:0,-2,0,0,0,0,0;-1/1:606:2,-1,0,0,0,1,0;-1/1:606:2,0,0,0,0,0,0;-2/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;1/1:618:-1,-1,0,0,1,1,0;-1/1:618:-1,0,0,0,1,0,0;1/1:618:0,0,0,0,0,0,0;1/1:618:1,-1,0,0,1,1,0;1/1:618:2,0,0,0,0,0,0;2/1:624:-3,-2,0,0,1,0,0;1/1:624:-2,-2,0,0,0,0,0;1/1:624:-2,-1,0,0,0,1,0;-1/1:624:-1,0,0,0,1,0,0;2/1:624:0,-1,0,0,0,1,0;1/1:624:0,0,0,0,0,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:642:-2,-2,0,0,0,0,0;1/1:642:-2,0,0,0,0,0,0;1/1:642:-1,-1,0,0,1,1,0;1/1:642:0,0,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:646:-2,0,0,0,0,0,0;1/1:648:-1,-1,0,0,1,1,0;-1/1:648:0,0,0,0,0,0,0;-1/1:676:-1,0,0,0,1,0,0;1/1:694:-1,0,0,0,1,0,0;-1/1:696:-2,-1,0,0,0,1,0;1/1:696:-2,0,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;1/1:702:-2,-2,0,0,0,0,0;1/1:702:0,-2,0,0,0,0,0;-2/1:702:0,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;1/1:712:0,0,0,0,0,0,0;-1/1:718:-4,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;1/1:766:-1,0,0,0,1,0,0;-2/1:768:-2,-2,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0;-1/1:772:0,0,0,0,0,0,0;-1/1:796:-2,0,0,0,0,0,0;1/1:796:-1,0,0,0,1,0,0;-1/1:817:0,0,0,0,0,0,0;1/1:834:-2,-2,0,0,0,0,0;-1/1:834:-1,-2,0,0,1,0,0;-1/1:834:0,-1,0,0,0,1,0;1/1:834:0,0,0,0,0,0,0;1/1:838:0,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;-1/1:864:-2,-2,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;-1/1:864:-1,0,0,0,1,0,0;1/1:864:0,-1,0,0,0,1,0;-1/1:864:0,0,0,0,0,0,0;1/1:864:0,0,0,0,2,0,0;-1/1:864:1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;1/1:876:-2,-1,0,0,0,1,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:876:-1,0,0,0,1,0,0;-1/1:878:-4,0,0,0,0,0,0;1/1:878:-2,0,0,0,0,0,0;1/1:884:-3,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;2/1:888:-1,-1,0,0,1,1,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:888:0,0,0,0,2,0,0;1/1:898:0,0,0,0,0,0,0;-1/1:902:0,0,0,0,0,0,0;1/1:926:-1,0,0,0,1,0,0;1/1:934:-4,0,0,0,0,0,0;-1/1:934:-3,0,0,0,1,0,0;-1/1:936:-2,-1,0,0,0,1,0;1/1:936:-2,0,0,0,0,0,0;-1/1:936:-1,0,0,0,1,0,0;-1/1:936:0,-1,0,0,0,1,0;1/1:958:-2,0,0,0,0,0,0;1/1:958:0,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:986:-1,0,0,0,1,0,0;-1/1:992:-3,0,0,0,1,0,0;1/1:992:-2,0,0,0,2,0,0;-1/1:998:-1,0,0,0,1,0,0;-1/1:1016:-2,0,0,0,0,0,0;-1/1:1016:-1,0,0,0,1,0,0"

compact_certificate private theorem operation980BoundedCheck288 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 288) = operation980BoundedValue288 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 288 8
    operation980BoundedValue288 operation980BoundedValue296 operation980BoundedCheck296
  decide +kernel

compact_certificate private def operation980BoundedValue280 : Poly := laurent_polynomial% "1/1:34:-1,0,0,0,1,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;-1/1:62:0,0,0,0,0,0,0;1/1:64:-1,0,0,0,1,0,0;-1/1:68:-2,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;1/1:136:-1,0,0,0,1,0,0;-1/1:162:-2,0,0,0,0,0,0;1/1:162:-1,-1,0,0,1,1,0;1/1:162:0,0,0,0,0,0,0;1/1:162:1,-1,0,0,1,1,0;1/1:162:1,0,0,0,1,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-1,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;-1/1:172:0,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-3,0,0,0,1,0,0;2/1:174:-2,-1,0,0,0,1,0;1/1:174:-2,-1,0,0,2,1,0;3/1:174:-1,0,0,0,1,0,0;2/1:174:0,-1,0,0,0,1,0;2/1:186:-3,0,0,0,1,0,0;-1/1:186:-1,0,0,0,1,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:186:0,-1,0,0,2,1,0;-1/1:186:1,0,0,0,1,0,0;-1/1:216:-2,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;-1/1:234:-1,-2,0,0,1,0,0;-1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:262:-2,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;-1/1:264:-2,-2,0,0,0,0,0;1/1:264:-2,-1,0,0,0,1,0;1/1:264:-1,-2,0,0,1,0,0;-1/1:264:-1,-1,0,0,1,1,0;2/1:264:-1,0,0,0,1,0,0;1/1:264:0,-1,0,0,0,1,0;-1/1:264:0,0,0,0,0,0,0;1/1:278:0,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:282:0,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;1/1:297:0,-2,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:332:-2,0,0,0,0,0,0;-1/1:332:0,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;-1/1:348:-4,0,0,0,0,0,0;-1/1:348:-3,-1,0,0,1,1,0;1/1:348:-2,-2,0,0,0,0,0;-3/1:348:-2,0,0,0,0,0,0;1/1:348:-1,0,0,0,1,0,0;1/1:348:0,-2,0,0,0,0,0;-2/1:348:0,0,0,0,0,0,0;-2/1:354:-2,-1,0,0,0,1,0;-1/1:354:-1,0,0,0,1,0,0;-2/1:354:0,-1,0,0,0,1,0;-1/1:386:-2,0,0,0,0,0,0;1/1:396:-2,-1,0,0,0,1,0;-1/1:396:-2,0,0,0,0,0,0;-1/1:396:0,-2,0,0,0,0,0;1/1:396:0,-1,0,0,0,1,0;-1/1:398:0,0,0,0,0,0,0;1/1:402:-2,-2,0,0,0,0,0;-1/1:402:-1,-1,0,0,1,1,0;1/1:402:0,-2,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:408:-1,-1,0,0,1,1,0;-1/1:408:-1,0,0,0,1,0,0;-1/1:426:-4,-2,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-1/1:426:-2,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-3/1:432:-2,-2,0,0,0,0,0;1/1:432:-2,0,0,0,0,0,0;-1/1:432:0,-2,0,0,0,0,0;3/1:432:0,0,0,0,0,0,0;-1/1:432:1,0,0,0,1,0,0;1/1:432:2,-2,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;2/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:0,-1,0,0,0,1,0;1/1:444:1,-2,0,0,1,0,0;1/1:444:1,0,0,0,1,0,0;-1/1:458:-1,0,0,0,1,0,0;2/1:474:-2,-1,0,0,0,1,0;-1/1:474:-1,-1,0,0,1,1,0;2/1:474:-1,0,0,0,1,0,0;2/1:474:0,-1,0,0,0,1,0;1/1:474:0,0,0,0,0,0,0;-1/1:474:1,0,0,0,1,0,0;1/1:488:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;1/1:576:-2,-1,0,0,0,1,0;-1/1:576:-2,0,0,0,0,0,0;-1/1:576:0,-2,0,0,0,0,0;2/1:576:0,-1,0,0,0,1,0;2/1:576:1,0,0,0,1,0,0;-1/1:576:2,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;1/1:606:-2,-1,0,0,0,1,0;-1/1:606:-2,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:606:0,-2,0,0,0,0,0;-1/1:606:2,-1,0,0,0,1,0;-1/1:606:2,0,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;1/1:618:-1,-1,0,0,1,1,0;-1/1:618:-1,0,0,0,1,0,0;1/1:618:0,0,0,0,0,0,0;1/1:618:1,-1,0,0,1,1,0;1/1:618:2,0,0,0,0,0,0;1/1:622:-2,0,0,0,0,0,0;2/1:624:-3,-2,0,0,1,0,0;1/1:624:-2,-2,0,0,0,0,0;1/1:624:-2,-1,0,0,0,1,0;-1/1:624:-1,0,0,0,1,0,0;2/1:624:0,-1,0,0,0,1,0;1/1:624:0,0,0,0,0,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:642:-2,-2,0,0,0,0,0;1/1:642:-2,0,0,0,0,0,0;1/1:642:-1,-1,0,0,1,1,0;1/1:642:0,0,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:646:-2,0,0,0,0,0,0;1/1:648:-2,-1,0,0,0,1,0;-1/1:648:-2,0,0,0,0,0,0;1/1:648:-1,-1,0,0,1,1,0;-1/1:648:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-2/1:676:-1,0,0,0,1,0,0;-1/1:688:0,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;1/1:696:-2,-1,0,0,0,1,0;1/1:696:-2,0,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;1/1:702:0,-2,0,0,0,0,0;-2/1:702:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;1/1:712:0,0,0,0,0,0,0;-1/1:718:-4,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;1/1:754:0,0,0,0,0,0,0;1/1:766:-1,0,0,0,1,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0;-1/1:772:0,0,0,0,0,0,0;-1/1:796:-2,0,0,0,0,0,0;1/1:796:-1,0,0,0,1,0,0;-1/1:817:0,0,0,0,0,0,0;1/1:834:-2,-2,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-2/1:834:-1,-2,0,0,1,0,0;-1/1:834:-1,0,0,0,1,0,0;-1/1:834:0,-1,0,0,0,1,0;1/1:834:0,0,0,0,0,0,0;1/1:838:0,0,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-4,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;-1/1:864:-2,-2,0,0,0,0,0;2/1:864:-2,-1,0,0,0,1,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:0,-1,0,0,0,1,0;-1/1:864:0,0,0,0,0,0,0;1/1:864:0,0,0,0,2,0,0;-1/1:864:1,-2,0,0,1,0,0;-1/1:864:1,0,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:876:-1,0,0,0,1,0,0;1/1:878:-4,0,0,0,0,0,0;1/1:878:-2,0,0,0,0,0,0;-1/1:878:-1,0,0,0,1,0,0;1/1:884:-3,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;1/1:888:-1,-1,0,0,1,1,0;-1/1:888:0,-2,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:888:0,0,0,0,2,0,0;1/1:898:-2,0,0,0,0,0,0;1/1:898:0,0,0,0,0,0,0;-1/1:902:-2,0,0,0,0,0,0;-1/1:902:0,0,0,0,0,0,0;1/1:926:-1,0,0,0,1,0,0;-1/1:932:-2,0,0,0,0,0,0;1/1:934:-4,0,0,0,0,0,0;-1/1:934:-3,0,0,0,1,0,0;1/1:936:-2,0,0,0,0,0,0;-1/1:936:-1,0,0,0,1,0,0;-1/1:944:-1,0,0,0,1,0,0;1/1:958:-2,0,0,0,0,0,0;1/1:958:0,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:986:-1,0,0,0,1,0,0;-1/1:992:-3,0,0,0,1,0,0;1/1:992:-2,0,0,0,2,0,0;-1/1:998:-1,0,0,0,1,0,0;-1/1:1016:-2,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck280 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 280) = operation980BoundedValue280 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 280 8
    operation980BoundedValue280 operation980BoundedValue288 operation980BoundedCheck288
  decide +kernel

compact_certificate private def operation980BoundedValue272 : Poly := laurent_polynomial% "1/1:52:0,0,0,0,0,0,0;1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;1/1:58:0,0,0,0,0,0,0;-1/1:62:0,0,0,0,0,0,0;1/1:64:-1,0,0,0,1,0,0;-1/1:68:-2,0,0,0,0,0,0;-1/1:68:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;1/1:136:-1,0,0,0,1,0,0;-1/1:162:-2,0,0,0,0,0,0;1/1:162:-1,-1,0,0,1,1,0;1/1:162:0,0,0,0,0,0,0;1/1:162:1,-1,0,0,1,1,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-1,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-3,0,0,0,1,0,0;1/1:174:-2,-1,0,0,0,1,0;1/1:174:-2,-1,0,0,2,1,0;3/1:174:-1,0,0,0,1,0,0;1/1:174:0,-1,0,0,0,1,0;2/1:186:-3,0,0,0,1,0,0;-1/1:186:-1,0,0,0,1,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:186:0,-1,0,0,2,1,0;-1/1:186:1,0,0,0,1,0,0;-1/1:216:-2,0,0,0,0,0,0;2/1:234:-2,-1,0,0,0,1,0;-1/1:234:-1,-2,0,0,1,0,0;1/1:234:0,-1,0,0,0,1,0;-1/1:244:-1,0,0,0,1,0,0;1/1:262:-2,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;-1/1:264:-2,-2,0,0,0,0,0;-1/1:264:-1,-1,0,0,1,1,0;1/1:264:-1,0,0,0,1,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:282:0,-2,0,0,0,0,0;1/1:282:0,0,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:332:-2,0,0,0,0,0,0;-1/1:332:0,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;-1/1:348:-4,0,0,0,0,0,0;-1/1:348:-3,-1,0,0,1,1,0;1/1:348:-2,-2,0,0,0,0,0;-2/1:348:-2,0,0,0,0,0,0;-1/1:348:-1,-1,0,0,1,1,0;1/1:348:-1,0,0,0,1,0,0;-2/1:354:-2,-1,0,0,0,1,0;-1/1:354:-1,0,0,0,1,0,0;-2/1:354:0,-1,0,0,0,1,0;-1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:394:0,0,0,0,0,0,0;-1/1:396:-2,0,0,0,0,0,0;1/1:396:0,-1,0,0,0,1,0;-1/1:398:0,0,0,0,0,0,0;1/1:402:-2,-2,0,0,0,0,0;-1/1:402:-1,-1,0,0,1,1,0;1/1:402:0,-2,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:408:-1,-1,0,0,1,1,0;-1/1:408:-1,0,0,0,1,0,0;-1/1:426:-4,-2,0,0,0,0,0;-1/1:426:-2,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-3/1:432:-2,-2,0,0,0,0,0;1/1:432:-2,0,0,0,0,0,0;-1/1:432:0,-2,0,0,0,0,0;4/1:432:0,0,0,0,0,0,0;-1/1:432:1,0,0,0,1,0,0;1/1:432:2,-2,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;2/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:0,-1,0,0,0,1,0;1/1:444:1,0,0,0,1,0,0;-1/1:458:-1,0,0,0,1,0,0;1/1:474:-2,-1,0,0,0,1,0;-1/1:474:-1,-1,0,0,1,1,0;1/1:474:-1,0,0,0,1,0,0;1/1:474:0,-1,0,0,0,1,0;1/1:474:0,0,0,0,0,0,0;1/1:478:-2,0,0,0,0,0,0;1/1:478:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;1/1:562:-2,0,0,0,0,0,0;1/1:576:-2,-1,0,0,0,1,0;-1/1:576:-2,0,0,0,0,0,0;-1/1:576:0,-2,0,0,0,0,0;2/1:576:0,-1,0,0,0,1,0;2/1:576:1,0,0,0,1,0,0;1/1:592:0,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;1/1:606:-2,-1,0,0,0,1,0;-1/1:606:-2,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:606:0,-2,0,0,0,0,0;-1/1:606:2,-1,0,0,0,1,0;-2/1:618:-2,0,0,0,0,0,0;1/1:618:-1,-1,0,0,1,1,0;-1/1:618:-1,0,0,0,1,0,0;1/1:618:0,-2,0,0,0,0,0;1/1:618:1,-1,0,0,1,1,0;1/1:618:2,0,0,0,0,0,0;1/1:622:-2,0,0,0,0,0,0;2/1:624:-3,-2,0,0,1,0,0;1/1:624:-2,-2,0,0,0,0,0;1/1:624:-2,-1,0,0,0,1,0;-1/1:624:-1,0,0,0,1,0,0;1/1:624:0,-1,0,0,0,1,0;1/1:634:-1,0,0,0,1,0,0;-1/1:642:-2,-2,0,0,0,0,0;1/1:642:-2,0,0,0,0,0,0;1/1:642:-1,-1,0,0,1,1,0;1/1:642:0,0,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:646:-2,0,0,0,0,0,0;1/1:648:-2,-1,0,0,0,1,0;1/1:648:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-2/1:676:-1,0,0,0,1,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;1/1:696:-2,-1,0,0,0,1,0;1/1:696:-2,0,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:702:-3,-1,0,0,1,1,0;-2/1:702:-2,0,0,0,0,0,0;1/1:702:0,-2,0,0,0,0,0;-2/1:702:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:712:0,0,0,0,0,0,0;-1/1:718:-4,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:734:-1,0,0,0,1,0,0;1/1:754:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0;-1/1:772:0,0,0,0,0,0,0;1/1:776:-1,0,0,0,1,0,0;-1/1:796:-2,0,0,0,0,0,0;1/1:796:-1,0,0,0,1,0,0;1/1:802:0,0,0,0,0,0,0;-1/1:806:-1,0,0,0,1,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;1/1:834:-2,-2,0,0,0,0,0;-2/1:834:-1,-2,0,0,1,0,0;1/1:838:0,0,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-4,0,0,0,0,0,0;-1/1:864:-2,-2,0,0,0,0,0;2/1:864:-2,-1,0,0,0,1,0;-1/1:864:-1,-2,0,0,1,0,0;1/1:864:0,-1,0,0,0,1,0;1/1:864:0,0,0,0,2,0,0;-1/1:864:1,-2,0,0,1,0,0;-1/1:864:1,0,0,0,1,0,0;1/1:876:-2,-1,0,0,2,1,0;1/1:878:-2,0,0,0,0,0,0;-1/1:878:-1,0,0,0,1,0,0;1/1:884:-3,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;1/1:888:-1,-1,0,0,1,1,0;-1/1:888:0,0,0,0,2,0,0;1/1:898:-2,0,0,0,0,0,0;1/1:898:0,0,0,0,0,0,0;-1/1:902:-2,0,0,0,0,0,0;-1/1:902:0,0,0,0,0,0,0;1/1:926:-1,0,0,0,1,0,0;-1/1:932:-2,0,0,0,0,0,0;1/1:934:-4,0,0,0,0,0,0;1/1:936:-2,0,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:936:-1,0,0,0,1,0,0;-1/1:944:-1,0,0,0,1,0,0;1/1:958:-2,0,0,0,0,0,0;1/1:958:0,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:992:-3,0,0,0,1,0,0;-1/1:998:-1,0,0,0,1,0,0;1/1:998:0,0,0,0,0,0,0;-1/1:1016:-2,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck272 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 272) = operation980BoundedValue272 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 272 8
    operation980BoundedValue272 operation980BoundedValue280 operation980BoundedCheck280
  decide +kernel

compact_certificate private def operation980BoundedValue264 : Poly := laurent_polynomial% "1/1:52:0,0,0,0,0,0,0;1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;1/1:58:0,0,0,0,0,0,0;-1/1:62:0,0,0,0,0,0,0;1/1:64:-1,0,0,0,1,0,0;-1/1:68:-2,0,0,0,0,0,0;-1/1:68:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;1/1:136:-1,0,0,0,1,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;-1/1:162:-1,-2,0,0,1,0,0;1/1:162:-1,-1,0,0,1,1,0;1/1:162:0,0,0,0,0,0,0;1/1:162:1,-1,0,0,1,1,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-1,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-3,0,0,0,1,0,0;1/1:174:-2,-1,0,0,0,1,0;1/1:174:-2,-1,0,0,2,1,0;2/1:174:-1,0,0,0,1,0,0;1/1:174:0,-1,0,0,0,1,0;2/1:186:-3,0,0,0,1,0,0;-1/1:186:-1,0,0,0,1,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:186:0,-1,0,0,2,1,0;-1/1:192:0,0,0,0,0,0,0;-1/1:216:-2,0,0,0,0,0,0;1/1:216:-1,-2,0,0,1,0,0;2/1:234:-2,-1,0,0,0,1,0;-1/1:234:-1,-2,0,0,1,0,0;1/1:234:-1,-1,0,0,1,1,0;1/1:234:-1,0,0,0,1,0,0;1/1:234:0,-1,0,0,0,1,0;-1/1:244:-1,0,0,0,1,0,0;1/1:262:-2,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;-1/1:264:-1,-1,0,0,1,1,0;1/1:264:-1,0,0,0,1,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:282:0,-2,0,0,0,0,0;1/1:282:0,0,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:332:-2,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;-1/1:348:-4,0,0,0,0,0,0;-1/1:348:-3,-1,0,0,1,1,0;2/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;-1/1:348:-1,-1,0,0,1,1,0;1/1:354:-2,-2,0,0,0,0,0;-2/1:354:-2,-1,0,0,0,1,0;-1/1:354:-1,0,0,0,1,0,0;-2/1:354:0,-1,0,0,0,1,0;-1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:394:-2,-2,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;1/1:396:-2,-4,0,0,0,0,0;-1/1:396:-2,0,0,0,0,0,0;1/1:396:0,-1,0,0,0,1,0;-1/1:398:0,0,0,0,0,0,0;2/1:402:-2,-2,0,0,0,0,0;-1/1:402:-1,-1,0,0,1,1,0;1/1:402:0,-2,0,0,0,0,0;-2/1:408:-2,-2,0,0,0,0,0;-1/1:408:-1,-1,0,0,1,1,0;-1/1:426:-4,-2,0,0,0,0,0;-1/1:426:-2,0,0,0,0,0,0;-3/1:432:-2,-2,0,0,0,0,0;1/1:432:-2,0,0,0,0,0,0;-2/1:432:0,-2,0,0,0,0,0;3/1:432:0,0,0,0,0,0,0;1/1:432:2,-2,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;2/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:0,-1,0,0,0,1,0;1/1:444:1,-2,0,0,1,0,0;1/1:444:1,0,0,0,1,0,0;-1/1:458:-1,0,0,0,1,0,0;1/1:472:0,0,0,0,0,0,0;1/1:474:-2,-1,0,0,0,1,0;-1/1:474:-1,-1,0,0,1,1,0;1/1:474:-1,0,0,0,1,0,0;1/1:474:0,-1,0,0,0,1,0;1/1:474:0,0,0,0,0,0,0;1/1:478:-2,0,0,0,0,0,0;1/1:478:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;1/1:562:-2,0,0,0,0,0,0;1/1:576:-2,-1,0,0,0,1,0;-1/1:576:-2,0,0,0,0,0,0;2/1:576:0,-1,0,0,0,1,0;2/1:576:1,0,0,0,1,0,0;1/1:592:0,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;1/1:606:-2,-1,0,0,0,1,0;-1/1:606:-2,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:606:2,-1,0,0,0,1,0;-1/1:618:-2,-2,0,0,0,0,0;-2/1:618:-2,0,0,0,0,0,0;1/1:618:-1,-1,0,0,1,1,0;1/1:618:0,-2,0,0,0,0,0;1/1:618:1,-1,0,0,1,1,0;1/1:622:-2,0,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;2/1:624:-3,-2,0,0,1,0,0;1/1:624:-2,-1,0,0,0,1,0;-1/1:624:-1,0,0,0,1,0,0;1/1:624:0,-1,0,0,0,1,0;1/1:634:-1,0,0,0,1,0,0;-1/1:642:-2,-2,0,0,0,0,0;1/1:642:-2,0,0,0,0,0,0;1/1:642:-1,-1,0,0,1,1,0;-1/1:642:0,-1,0,0,0,1,0;1/1:642:0,0,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:646:-2,0,0,0,0,0,0;1/1:648:-2,-1,0,0,0,1,0;1/1:648:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-2/1:676:-1,0,0,0,1,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;1/1:696:-2,-1,0,0,0,1,0;1/1:696:-2,0,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;-1/1:702:-3,-1,0,0,1,1,0;-1/1:702:-3,0,0,0,1,0,0;-2/1:702:-2,0,0,0,0,0,0;-1/1:702:-1,-2,0,0,1,0,0;-1/1:702:-1,-1,0,0,1,1,0;1/1:702:0,-2,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;-1/1:718:-4,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;1/1:724:-1,0,0,0,1,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:734:-1,0,0,0,1,0,0;-1/1:739:0,0,0,0,0,0,0;1/1:754:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0;1/1:776:-1,0,0,0,1,0,0;-1/1:778:-1,0,0,0,1,0,0;-1/1:794:-1,0,0,0,1,0,0;-1/1:796:-2,0,0,0,0,0,0;1/1:796:-1,0,0,0,1,0,0;1/1:802:0,0,0,0,0,0,0;-1/1:806:-1,0,0,0,1,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-2/1:834:-1,-2,0,0,1,0,0;1/1:838:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;1/1:858:-1,0,0,0,1,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-4,0,0,0,0,0,0;2/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;1/1:864:0,-1,0,0,0,1,0;-1/1:864:1,-2,0,0,1,0,0;-1/1:864:1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;1/1:876:-2,-1,0,0,2,1,0;1/1:876:-2,0,0,0,2,0,0;1/1:876:0,-2,0,0,0,0,0;-1/1:876:0,-1,0,0,0,1,0;1/1:878:-2,0,0,0,0,0,0;-1/1:878:-1,0,0,0,1,0,0;1/1:884:-3,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;1/1:888:-1,-1,0,0,1,1,0;1/1:888:0,-2,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:888:0,0,0,0,2,0,0;1/1:898:-2,0,0,0,0,0,0;1/1:898:0,0,0,0,0,0,0;-1/1:902:-2,0,0,0,0,0,0;-1/1:902:0,0,0,0,0,0,0;1/1:914:0,0,0,0,0,0,0;1/1:926:-1,0,0,0,1,0,0;-1/1:932:-2,0,0,0,0,0,0;1/1:934:-4,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-2,0,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:936:-1,0,0,0,1,0,0;-1/1:944:-1,0,0,0,1,0,0;1/1:958:-2,0,0,0,0,0,0;1/1:958:0,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:992:-3,0,0,0,1,0,0;1/1:992:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;1/1:998:0,0,0,0,0,0,0;-1/1:1016:-2,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck264 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 264) = operation980BoundedValue264 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 264 8
    operation980BoundedValue264 operation980BoundedValue272 operation980BoundedCheck272
  decide +kernel

compact_certificate private def operation980BoundedValue256 : Poly := laurent_polynomial% "1/1:52:0,0,0,0,0,0,0;1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;1/1:58:0,0,0,0,0,0,0;-1/1:62:0,0,0,0,0,0,0;1/1:64:-1,0,0,0,1,0,0;-1/1:68:-2,0,0,0,0,0,0;-1/1:68:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;1/1:136:-1,0,0,0,1,0,0;1/1:144:0,-1,0,0,0,1,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;1/1:162:0,0,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-1,0,0,0,1,0,0;-2/1:172:-4,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-2/1:174:-3,-2,0,0,1,0,0;2/1:174:-1,0,0,0,1,0,0;2/1:186:-3,0,0,0,1,0,0;1/1:186:-1,-2,0,0,1,0,0;1/1:186:0,-2,0,0,2,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:192:-2,0,0,0,0,0,0;-1/1:192:-1,-1,0,0,1,1,0;-1/1:192:0,0,0,0,0,0,0;-1/1:216:-2,0,0,0,0,0,0;2/1:234:-2,-1,0,0,0,1,0;-1/1:234:-1,-2,0,0,1,0,0;1/1:234:-1,-1,0,0,1,1,0;1/1:234:-1,0,0,0,1,0,0;1/1:234:0,-1,0,0,0,1,0;-1/1:244:-1,0,0,0,1,0,0;1/1:262:-2,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:278:-2,0,0,0,0,0,0;-3/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:282:0,-2,0,0,0,0,0;1/1:282:0,0,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:332:-2,0,0,0,0,0,0;2/1:348:-4,-2,0,0,0,0,0;2/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;-1/1:348:-1,-1,0,0,1,1,0;1/1:354:-2,-2,0,0,0,0,0;-1/1:354:-2,-1,0,0,0,1,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:354:0,-1,0,0,0,1,0;-1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:394:-2,-2,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;1/1:396:-2,-4,0,0,0,0,0;-1/1:396:-2,0,0,0,0,0,0;1/1:396:0,-1,0,0,0,1,0;1/1:398:-2,0,0,0,0,0,0;-1/1:398:0,0,0,0,0,0,0;2/1:402:-2,-2,0,0,0,0,0;-1/1:402:-1,-1,0,0,1,1,0;1/1:402:0,-2,0,0,0,0,0;-2/1:408:-2,-2,0,0,0,0,0;-1/1:408:-1,-1,0,0,1,1,0;-1/1:426:-4,-2,0,0,0,0,0;-1/1:426:-2,0,0,0,0,0,0;-3/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-2/1:432:0,-2,0,0,0,0,0;3/1:432:0,0,0,0,0,0,0;1/1:432:2,-2,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;3/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:0,-1,0,0,0,1,0;1/1:444:1,-2,0,0,1,0,0;1/1:444:1,0,0,0,1,0,0;-1/1:458:-1,0,0,0,1,0,0;1/1:472:0,0,0,0,0,0,0;-1/1:474:-1,-1,0,0,1,1,0;1/1:474:-1,0,0,0,1,0,0;1/1:474:0,0,0,0,0,0,0;1/1:478:-2,0,0,0,0,0,0;1/1:478:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;1/1:562:-2,0,0,0,0,0,0;1/1:576:-2,-1,0,0,0,1,0;-1/1:576:-2,0,0,0,0,0,0;2/1:576:0,-1,0,0,0,1,0;2/1:576:1,0,0,0,1,0,0;1/1:592:0,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;1/1:606:-2,-1,0,0,0,1,0;-1/1:606:-2,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;1/1:606:0,-1,0,0,0,1,0;-1/1:618:-2,-2,0,0,0,0,0;-2/1:618:-2,0,0,0,0,0,0;1/1:618:-1,-1,0,0,1,1,0;-1/1:618:0,0,0,0,0,0,0;-1/1:618:1,-2,0,0,1,0,0;1/1:622:-2,0,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;2/1:624:-3,-2,0,0,1,0,0;-1/1:624:-1,0,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:638:-2,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:642:0,-1,0,0,0,1,0;1/1:642:0,0,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:646:-2,0,0,0,0,0,0;1/1:648:-2,-1,0,0,0,1,0;1/1:648:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-2/1:676:-1,0,0,0,1,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;1/1:696:-2,-1,0,0,0,1,0;1/1:696:-2,0,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;-1/1:702:-3,-1,0,0,1,1,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:702:-1,-2,0,0,1,0,0;1/1:702:0,-2,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;-1/1:718:-4,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:734:-1,0,0,0,1,0,0;-1/1:739:0,0,0,0,0,0,0;1/1:754:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0;1/1:776:-1,0,0,0,1,0,0;1/1:778:-2,0,0,0,0,0,0;-1/1:778:-1,0,0,0,1,0,0;-1/1:788:-1,0,0,0,1,0,0;-1/1:794:-1,0,0,0,1,0,0;-1/1:796:-2,0,0,0,0,0,0;1/1:796:-1,0,0,0,1,0,0;1/1:802:0,0,0,0,0,0,0;-1/1:806:-1,0,0,0,1,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-2/1:834:-1,-2,0,0,1,0,0;1/1:838:0,0,0,0,0,0,0;-1/1:848:-2,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;1/1:858:-1,0,0,0,1,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-4,0,0,0,0,0,0;3/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;1/1:864:0,-1,0,0,0,1,0;-1/1:864:1,-2,0,0,1,0,0;-1/1:864:1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;1/1:876:-2,-1,0,0,2,1,0;1/1:876:0,-2,0,0,0,0,0;-1/1:876:0,-1,0,0,0,1,0;1/1:878:-2,0,0,0,0,0,0;-1/1:878:-1,0,0,0,1,0,0;1/1:884:-3,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;1/1:888:-1,-1,0,0,1,1,0;1/1:888:0,-2,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:888:0,0,0,0,2,0,0;1/1:898:-2,0,0,0,0,0,0;1/1:898:0,0,0,0,0,0,0;-1/1:902:-2,0,0,0,0,0,0;-1/1:902:0,0,0,0,0,0,0;1/1:914:0,0,0,0,0,0,0;1/1:926:-1,0,0,0,1,0,0;-1/1:932:-2,0,0,0,0,0,0;1/1:934:-4,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-2,0,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:936:-1,0,0,0,1,0,0;-1/1:944:-1,0,0,0,1,0,0;1/1:958:-2,0,0,0,0,0,0;1/1:958:0,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:992:-3,0,0,0,1,0,0;1/1:992:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;1/1:998:0,0,0,0,0,0,0;-1/1:1016:-2,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck256 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 256) = operation980BoundedValue256 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 256 8
    operation980BoundedValue256 operation980BoundedValue264 operation980BoundedCheck264
  decide +kernel

compact_certificate private def operation980BoundedValue248 : Poly := laurent_polynomial% "-1/1:52:-3,0,0,0,1,0,0;1/1:52:0,0,0,0,0,0,0;1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;1/1:58:0,0,0,0,0,0,0;-1/1:62:0,0,0,0,0,0,0;1/1:64:-1,0,0,0,1,0,0;-1/1:68:-2,0,0,0,0,0,0;-1/1:68:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;1/1:136:-1,0,0,0,1,0,0;1/1:144:0,-1,0,0,0,1,0;-1/1:146:-1,0,0,0,1,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;1/1:162:-1,-1,0,0,1,1,0;1/1:162:0,0,0,0,0,0,0;1/1:162:1,-1,0,0,1,1,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:166:-2,0,0,0,2,0,0;1/1:166:-1,0,0,0,1,0,0;-2/1:172:-4,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-2/1:174:-3,-2,0,0,1,0,0;2/1:174:-1,0,0,0,1,0,0;2/1:186:-3,0,0,0,1,0,0;1/1:186:-1,-2,0,0,1,0,0;1/1:186:0,-2,0,0,2,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:192:-2,0,0,0,0,0,0;-1/1:192:-1,-1,0,0,1,1,0;-1/1:192:0,0,0,0,0,0,0;-1/1:216:-2,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;-1/1:234:-1,-2,0,0,1,0,0;1/1:234:-1,-1,0,0,1,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:262:-2,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:278:-2,0,0,0,0,0,0;-3/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:282:0,-2,0,0,0,0,0;1/1:282:0,0,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:332:-3,0,0,0,1,0,0;-1/1:332:-2,0,0,0,0,0,0;2/1:348:-4,-2,0,0,0,0,0;2/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;-1/1:348:-1,-1,0,0,1,1,0;1/1:354:-2,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:388:-2,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:-2,-2,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;1/1:396:-2,-4,0,0,0,0,0;1/1:396:0,-1,0,0,0,1,0;1/1:398:-2,0,0,0,0,0,0;-1/1:398:-1,0,0,0,1,0,0;-1/1:398:0,0,0,0,0,0,0;2/1:402:-2,-2,0,0,0,0,0;-1/1:402:-1,-1,0,0,1,1,0;1/1:402:0,-2,0,0,0,0,0;-2/1:408:-2,-2,0,0,0,0,0;-1/1:408:-1,-1,0,0,1,1,0;-1/1:426:-4,-2,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-3/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-2/1:432:0,-2,0,0,0,0,0;3/1:432:0,0,0,0,0,0,0;1/1:432:2,-2,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;2/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;1/1:444:1,0,0,0,1,0,0;-1/1:458:-2,0,0,0,0,0,0;-1/1:458:-1,0,0,0,1,0,0;-1/1:458:0,0,0,0,0,0,0;1/1:472:0,0,0,0,0,0,0;-1/1:474:-1,-1,0,0,1,1,0;1/1:474:-1,0,0,0,1,0,0;1/1:478:-2,0,0,0,0,0,0;1/1:478:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;1/1:562:-2,0,0,0,0,0,0;1/1:576:-2,-1,0,0,0,1,0;1/1:576:0,-1,0,0,0,1,0;2/1:576:1,0,0,0,1,0,0;-1/1:576:2,-1,0,0,0,1,0;1/1:592:0,0,0,0,0,0,0;1/1:598:-2,0,0,0,0,0,0;1/1:598:0,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;1/1:606:-2,-1,0,0,0,1,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:606:2,-1,0,0,0,1,0;-1/1:618:-2,-2,0,0,0,0,0;-2/1:618:-2,0,0,0,0,0,0;1/1:618:-1,-1,0,0,1,1,0;-1/1:618:0,0,0,0,0,0,0;-1/1:618:1,-2,0,0,1,0,0;1/1:622:-2,0,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;2/1:624:-3,-2,0,0,1,0,0;-1/1:624:-1,0,0,0,1,0,0;-1/1:626:-1,0,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:638:-2,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;1/1:642:-1,-2,0,0,1,0,0;-1/1:642:0,-1,0,0,0,1,0;1/1:642:0,0,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:646:-2,0,0,0,0,0,0;1/1:648:-2,-1,0,0,0,1,0;1/1:648:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,0,0,0,0,0,0;-1/1:676:-1,0,0,0,1,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;1/1:696:-2,-1,0,0,0,1,0;1/1:696:-2,0,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;-1/1:702:-3,-1,0,0,1,1,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:702:-1,-2,0,0,1,0,0;1/1:702:0,-2,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;-1/1:712:0,0,0,0,0,0,0;-1/1:718:-4,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:734:-1,0,0,0,1,0,0;-1/1:739:0,0,0,0,0,0,0;1/1:754:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:768:-2,0,0,0,0,0,0;-1/1:768:0,0,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;1/1:778:-2,0,0,0,0,0,0;-1/1:778:-1,0,0,0,1,0,0;-1/1:788:-1,0,0,0,1,0,0;-1/1:794:-1,0,0,0,1,0,0;-1/1:796:-2,0,0,0,0,0,0;1/1:796:-1,0,0,0,1,0,0;1/1:802:0,0,0,0,0,0,0;1/1:804:-2,-1,0,0,0,1,0;1/1:804:0,-1,0,0,0,1,0;-1/1:806:-1,0,0,0,1,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:818:-1,0,0,0,1,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:834:-1,-2,0,0,1,0,0;1/1:838:0,0,0,0,0,0,0;-1/1:848:-2,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;1/1:858:-1,0,0,0,1,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-4,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;2/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:864:1,-2,0,0,1,0,0;-1/1:864:1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;1/1:876:-2,-1,0,0,2,1,0;1/1:876:-1,0,0,0,1,0,0;1/1:876:0,-2,0,0,0,0,0;-1/1:876:0,-1,0,0,0,1,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:878:0,0,0,0,0,0,0;1/1:884:-3,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,-2,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;1/1:888:-1,-1,0,0,1,1,0;1/1:888:-1,0,0,0,1,0,0;1/1:888:0,-2,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:888:0,0,0,0,2,0,0;1/1:898:-2,0,0,0,0,0,0;1/1:898:0,0,0,0,0,0,0;-1/1:902:-2,0,0,0,0,0,0;-1/1:902:0,0,0,0,0,0,0;1/1:914:0,0,0,0,0,0,0;-1/1:932:-2,0,0,0,0,0,0;1/1:934:-4,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:936:-1,0,0,0,1,0,0;-1/1:944:-1,0,0,0,1,0,0;1/1:958:-2,0,0,0,0,0,0;1/1:958:0,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:986:-1,0,0,0,1,0,0;-1/1:992:-3,0,0,0,1,0,0;1/1:992:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;1/1:998:0,0,0,0,0,0,0;-1/1:1016:-2,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck248 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 248) = operation980BoundedValue248 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 248 8
    operation980BoundedValue248 operation980BoundedValue256 operation980BoundedCheck256
  decide +kernel

compact_certificate private def operation980BoundedValue240 : Poly := laurent_polynomial% "-1/1:52:-3,0,0,0,1,0,0;1/1:52:0,0,0,0,0,0,0;1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;1/1:58:0,0,0,0,0,0,0;-1/1:62:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;1/1:136:-1,0,0,0,1,0,0;1/1:144:0,-1,0,0,0,1,0;-1/1:146:-1,0,0,0,1,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;1/1:162:-1,-1,0,0,1,1,0;1/1:162:0,0,0,0,0,0,0;1/1:162:1,-1,0,0,1,1,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;-2/1:172:-4,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,-2,0,0,1,0,0;2/1:174:-1,0,0,0,1,0,0;2/1:186:-3,0,0,0,1,0,0;1/1:186:-1,-2,0,0,1,0,0;1/1:186:0,-2,0,0,2,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:192:-2,0,0,0,0,0,0;-1/1:192:0,0,0,0,0,0,0;-1/1:216:-2,0,0,0,0,0,0;-1/1:218:-1,0,0,0,1,0,0;-1/1:234:-2,-2,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:262:-2,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:278:-2,0,0,0,0,0,0;-3/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:282:0,-2,0,0,0,0,0;1/1:282:0,0,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:332:-3,0,0,0,1,0,0;1/1:348:-4,-2,0,0,0,0,0;1/1:348:-2,-2,0,0,0,0,0;-1/1:348:-2,0,0,0,0,0,0;-1/1:348:-1,-1,0,0,1,1,0;1/1:354:-2,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:388:-2,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:-2,-2,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;1/1:396:-2,-4,0,0,0,0,0;1/1:396:0,-1,0,0,0,1,0;1/1:398:-2,0,0,0,0,0,0;-1/1:398:-1,0,0,0,1,0,0;-1/1:398:0,0,0,0,0,0,0;2/1:402:-2,-2,0,0,0,0,0;-1/1:402:-1,-1,0,0,1,1,0;1/1:402:0,-2,0,0,0,0,0;-2/1:408:-2,-2,0,0,0,0,0;-1/1:408:-1,-1,0,0,1,1,0;1/1:418:-2,0,0,0,0,0,0;1/1:418:0,0,0,0,0,0,0;1/1:424:0,0,0,0,0,0,0;-1/1:426:-4,-2,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-3/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-2/1:432:0,-2,0,0,0,0,0;3/1:432:0,0,0,0,0,0,0;1/1:432:2,-2,0,0,0,0,0;1/1:432:2,0,0,0,0,0,0;-1/1:433:0,0,0,0,0,0,0;2/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:0,0,0,0,0,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:458:-2,0,0,0,0,0,0;-1/1:458:-1,0,0,0,1,0,0;-1/1:458:0,0,0,0,0,0,0;1/1:472:0,0,0,0,0,0,0;-1/1:474:-1,-1,0,0,1,1,0;1/1:474:-1,0,0,0,1,0,0;1/1:478:-2,0,0,0,0,0,0;1/1:478:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;1/1:562:-2,0,0,0,0,0,0;1/1:576:-2,-1,0,0,0,1,0;-1/1:576:-1,-2,0,0,1,0,0;2/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;1/1:586:-2,0,0,0,0,0,0;1/1:592:0,0,0,0,0,0,0;1/1:598:-2,0,0,0,0,0,0;1/1:598:0,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;1/1:606:-2,-1,0,0,0,1,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:606:2,-1,0,0,0,1,0;-1/1:618:-2,-2,0,0,0,0,0;-2/1:618:-2,0,0,0,0,0,0;1/1:618:-1,-1,0,0,1,1,0;-1/1:618:0,0,0,0,0,0,0;-1/1:618:1,-2,0,0,1,0,0;1/1:622:-2,0,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;2/1:624:-3,-2,0,0,1,0,0;-1/1:626:-1,0,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;1/1:634:0,0,0,0,0,0,0;-1/1:638:-2,0,0,0,0,0,0;-1/1:638:-1,0,0,0,1,0,0;-2/1:642:-2,-2,0,0,0,0,0;1/1:642:-1,-2,0,0,1,0,0;1/1:642:0,0,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:646:-2,0,0,0,0,0,0;1/1:648:-2,-1,0,0,0,1,0;1/1:648:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:656:-1,0,0,0,1,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,0,0,0,0,0,0;-1/1:676:-1,0,0,0,1,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;1/1:696:-2,-1,0,0,0,1,0;1/1:696:-2,0,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;-1/1:702:-3,-1,0,0,1,1,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;1/1:702:0,-2,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;-1/1:712:0,0,0,0,0,0,0;-1/1:718:-4,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:734:-1,0,0,0,1,0,0;-1/1:739:0,0,0,0,0,0,0;1/1:754:0,0,0,0,0,0,0;-1/1:764:-1,0,0,0,1,0,0;-1/1:768:-2,-2,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;1/1:778:-2,0,0,0,0,0,0;-1/1:788:-1,0,0,0,1,0,0;-1/1:794:-1,0,0,0,1,0,0;1/1:796:-1,0,0,0,1,0,0;1/1:802:0,0,0,0,0,0,0;1/1:804:-2,-1,0,0,0,1,0;1/1:804:0,-1,0,0,0,1,0;-1/1:806:-1,0,0,0,1,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:818:-1,0,0,0,1,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:834:-1,-2,0,0,1,0,0;1/1:834:-1,0,0,0,1,0,0;1/1:838:0,0,0,0,0,0,0;1/1:844:0,0,0,0,0,0,0;-1/1:848:-2,0,0,0,0,0,0;-1/1:848:-1,0,0,0,1,0,0;-1/1:858:-2,-2,0,0,0,0,0;1/1:858:-1,0,0,0,1,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-4,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;2/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,-2,0,0,1,0,0;1/1:864:-1,0,0,0,1,0,0;-1/1:864:1,-2,0,0,1,0,0;-1/1:864:1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;1/1:876:-2,-1,0,0,2,1,0;1/1:876:-1,0,0,0,1,0,0;-1/1:876:0,-1,0,0,0,1,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:878:0,0,0,0,0,0,0;1/1:884:-3,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;1/1:888:-1,-1,0,0,1,1,0;1/1:888:0,-2,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:898:-2,0,0,0,0,0,0;1/1:898:0,0,0,0,0,0,0;-1/1:902:-2,0,0,0,0,0,0;-1/1:902:0,0,0,0,0,0,0;-1/1:932:-2,0,0,0,0,0,0;1/1:934:-4,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:944:-1,0,0,0,1,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:986:-1,0,0,0,1,0,0;-1/1:992:-3,0,0,0,1,0,0;1/1:992:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;1/1:998:0,0,0,0,0,0,0;-1/1:1016:-2,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck240 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 240) = operation980BoundedValue240 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 240 8
    operation980BoundedValue240 operation980BoundedValue248 operation980BoundedCheck248
  decide +kernel

compact_certificate private def operation980BoundedValue232 : Poly := laurent_polynomial% "-1/1:52:-3,0,0,0,1,0,0;1/1:52:0,0,0,0,0,0,0;1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;1/1:58:0,0,0,0,0,0,0;-1/1:62:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;-1/1:116:-1,0,0,0,1,0,0;1/1:136:-1,0,0,0,1,0,0;1/1:144:0,-1,0,0,0,1,0;-1/1:146:-1,0,0,0,1,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;1/1:162:1,-1,0,0,1,1,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;-2/1:172:-4,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;2/1:186:-3,0,0,0,1,0,0;1/1:186:-1,-2,0,0,1,0,0;1/1:186:0,-2,0,0,2,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:192:-2,0,0,0,0,0,0;-1/1:192:0,0,0,0,0,0,0;-1/1:216:-2,0,0,0,0,0,0;-1/1:218:-1,0,0,0,1,0,0;-1/1:234:-2,-2,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:262:-2,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:278:-2,0,0,0,0,0,0;-3/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:282:0,-2,0,0,0,0,0;1/1:282:0,0,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;1/1:328:-2,0,0,0,0,0,0;1/1:328:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:332:-3,0,0,0,1,0,0;1/1:342:0,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;1/1:348:-2,-2,0,0,0,0,0;1/1:348:0,-2,0,0,0,0,0;1/1:354:-2,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:388:-2,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:-2,-2,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;1/1:396:-2,-4,0,0,0,0,0;1/1:396:0,-1,0,0,0,1,0;1/1:398:-2,0,0,0,0,0,0;-1/1:398:-1,0,0,0,1,0,0;-1/1:398:0,0,0,0,0,0,0;1/1:402:-2,-2,0,0,0,0,0;-1/1:402:-1,-1,0,0,1,1,0;-2/1:408:-2,-2,0,0,0,0,0;-1/1:408:-1,-1,0,0,1,1,0;1/1:418:-2,0,0,0,0,0,0;1/1:418:0,0,0,0,0,0,0;1/1:424:0,0,0,0,0,0,0;-1/1:426:-4,-2,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-3/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-2/1:432:0,-2,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;1/1:432:2,-2,0,0,0,0,0;-1/1:433:0,0,0,0,0,0,0;2/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:0,0,0,0,0,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:458:-2,0,0,0,0,0,0;-1/1:458:-1,0,0,0,1,0,0;-1/1:458:0,0,0,0,0,0,0;1/1:472:0,0,0,0,0,0,0;-1/1:474:-1,-1,0,0,1,1,0;1/1:474:-1,0,0,0,1,0,0;1/1:478:-2,0,0,0,0,0,0;1/1:478:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;1/1:562:-2,0,0,0,0,0,0;1/1:576:-2,-1,0,0,0,1,0;-1/1:576:-1,-2,0,0,1,0,0;2/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;1/1:586:-2,0,0,0,0,0,0;1/1:592:0,0,0,0,0,0,0;1/1:598:-2,0,0,0,0,0,0;1/1:598:0,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;1/1:606:-2,-1,0,0,0,1,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:606:2,-1,0,0,0,1,0;-1/1:614:-1,0,0,0,1,0,0;-1/1:618:-2,-2,0,0,0,0,0;-2/1:618:-2,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;-1/1:618:0,0,0,0,0,0,0;-1/1:618:1,-2,0,0,1,0,0;1/1:622:-2,0,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;2/1:624:-3,-2,0,0,1,0,0;-1/1:626:-1,0,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;1/1:634:0,0,0,0,0,0,0;-1/1:638:-2,0,0,0,0,0,0;-1/1:638:-1,0,0,0,1,0,0;-2/1:642:-2,-2,0,0,0,0,0;1/1:642:-1,-2,0,0,1,0,0;1/1:642:0,0,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;1/1:648:-2,-1,0,0,0,1,0;1/1:648:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:656:-1,0,0,0,1,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,0,0,0,0,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;1/1:696:-2,-1,0,0,0,1,0;2/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;1/1:708:-1,-1,0,0,1,1,0;1/1:708:0,-2,0,0,0,0,0;-1/1:712:0,0,0,0,0,0,0;-1/1:718:-4,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:734:-1,0,0,0,1,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:746:-1,0,0,0,1,0,0;1/1:754:-1,0,0,0,1,0,0;1/1:754:0,0,0,0,0,0,0;-1/1:764:-1,0,0,0,1,0,0;-1/1:768:-2,-2,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;1/1:778:-2,0,0,0,0,0,0;-1/1:788:-1,0,0,0,1,0,0;-1/1:794:-1,0,0,0,1,0,0;1/1:796:-2,0,0,0,0,0,0;1/1:796:-1,0,0,0,1,0,0;1/1:802:0,0,0,0,0,0,0;1/1:804:-2,-1,0,0,0,1,0;1/1:804:0,-1,0,0,0,1,0;-1/1:806:-1,0,0,0,1,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:818:-1,0,0,0,1,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:824:-1,0,0,0,1,0,0;-1/1:834:-2,-1,0,0,0,1,0;1/1:834:-1,0,0,0,1,0,0;1/1:838:0,0,0,0,0,0,0;1/1:844:0,0,0,0,0,0,0;-1/1:848:-2,0,0,0,0,0,0;-1/1:848:-1,0,0,0,1,0,0;-1/1:858:-2,-2,0,0,0,0,0;1/1:858:-1,0,0,0,1,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-4,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;2/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,-2,0,0,1,0,0;2/1:864:-1,0,0,0,1,0,0;-1/1:864:1,-2,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:876:0,-1,0,0,0,1,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:878:0,0,0,0,0,0,0;1/1:884:-3,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:898:-2,0,0,0,0,0,0;1/1:898:0,0,0,0,0,0,0;-1/1:902:-2,0,0,0,0,0,0;-1/1:902:0,0,0,0,0,0,0;-1/1:932:-2,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:944:-1,0,0,0,1,0,0;1/1:946:-2,0,0,0,0,0,0;-1/1:956:-1,0,0,0,1,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:986:-1,0,0,0,1,0,0;1/1:992:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;1/1:998:0,0,0,0,0,0,0;-1/1:1016:-2,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck232 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 232) = operation980BoundedValue232 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 232 8
    operation980BoundedValue232 operation980BoundedValue240 operation980BoundedCheck240
  decide +kernel

compact_certificate private def operation980BoundedValue224 : Poly := laurent_polynomial% "-1/1:52:-3,0,0,0,1,0,0;1/1:52:0,0,0,0,0,0,0;1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;1/1:58:0,0,0,0,0,0,0;-1/1:62:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;-1/1:116:-1,0,0,0,1,0,0;-1/1:134:-1,0,0,0,1,0,0;1/1:136:-1,0,0,0,1,0,0;1/1:144:0,-1,0,0,0,1,0;-1/1:146:-1,0,0,0,1,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,0,0,0,0,0,0;1/1:162:1,-1,0,0,1,1,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;-2/1:172:-4,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:186:-3,0,0,0,1,0,0;1/1:186:-1,-2,0,0,1,0,0;1/1:186:0,-2,0,0,2,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:218:-1,0,0,0,1,0,0;-1/1:234:-2,-2,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:262:-2,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:-2,0,0,0,0,0,0;1/1:268:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;1/1:282:0,0,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;1/1:328:-2,0,0,0,0,0,0;1/1:328:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:332:-3,0,0,0,1,0,0;1/1:342:0,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;1/1:348:-2,-2,0,0,0,0,0;1/1:354:-2,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:388:-2,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:-2,-2,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;1/1:396:-2,-4,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:398:-1,0,0,0,1,0,0;-1/1:398:0,0,0,0,0,0,0;1/1:402:-2,-2,0,0,0,0,0;-2/1:408:-2,-2,0,0,0,0,0;-1/1:408:-1,-1,0,0,1,1,0;1/1:418:-2,0,0,0,0,0,0;1/1:418:0,0,0,0,0,0,0;1/1:424:0,0,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-2/1:432:0,-2,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;-1/1:433:0,0,0,0,0,0,0;2/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:0,0,0,0,0,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:458:-2,0,0,0,0,0,0;-1/1:458:-1,0,0,0,1,0,0;-1/1:458:0,0,0,0,0,0,0;1/1:472:0,0,0,0,0,0,0;-1/1:474:-1,-1,0,0,1,1,0;1/1:474:-1,0,0,0,1,0,0;1/1:478:-2,0,0,0,0,0,0;1/1:478:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;1/1:562:-2,0,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;1/1:586:-2,0,0,0,0,0,0;1/1:592:0,0,0,0,0,0,0;1/1:598:-2,0,0,0,0,0,0;1/1:598:0,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;1/1:606:-2,-1,0,0,0,1,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:606:2,-1,0,0,0,1,0;-1/1:614:-1,0,0,0,1,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;-1/1:618:1,-2,0,0,1,0,0;1/1:622:-2,0,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:626:-1,0,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;1/1:634:0,0,0,0,0,0,0;-1/1:638:-2,0,0,0,0,0,0;-1/1:638:-1,0,0,0,1,0,0;-2/1:642:-2,-2,0,0,0,0,0;1/1:642:-1,-2,0,0,1,0,0;-1/1:643:0,0,0,0,0,0,0;1/1:648:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:656:-1,0,0,0,1,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,0,0,0,0,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;1/1:696:-2,-1,0,0,0,1,0;2/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;1/1:708:-1,-1,0,0,1,1,0;1/1:708:0,-2,0,0,0,0,0;-1/1:718:-4,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:734:-1,0,0,0,1,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:746:-1,0,0,0,1,0,0;1/1:754:-1,0,0,0,1,0,0;1/1:754:0,0,0,0,0,0,0;-1/1:764:-1,0,0,0,1,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:768:0,-2,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;1/1:778:-2,0,0,0,0,0,0;-1/1:788:-1,0,0,0,1,0,0;-1/1:794:-1,0,0,0,1,0,0;1/1:796:-2,0,0,0,0,0,0;1/1:796:-1,0,0,0,1,0,0;1/1:802:0,0,0,0,0,0,0;-1/1:806:-1,0,0,0,1,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:818:-1,0,0,0,1,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:824:-1,0,0,0,1,0,0;1/1:832:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;1/1:838:0,0,0,0,0,0,0;1/1:844:0,0,0,0,0,0,0;-1/1:848:-2,0,0,0,0,0,0;-1/1:848:-1,0,0,0,1,0,0;-1/1:858:-2,-2,0,0,0,0,0;1/1:858:-1,0,0,0,1,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;2/1:864:-2,-1,0,0,0,1,0;2/1:864:-1,-2,0,0,1,0,0;2/1:864:-1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:878:-2,0,0,0,0,0,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:878:0,0,0,0,0,0,0;1/1:884:-3,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:892:-2,0,0,0,0,0,0;1/1:892:0,0,0,0,0,0,0;1/1:898:-2,0,0,0,0,0,0;1/1:898:0,0,0,0,0,0,0;-1/1:902:-2,0,0,0,0,0,0;-1/1:902:0,0,0,0,0,0,0;1/1:916:-2,0,0,0,0,0,0;1/1:922:0,0,0,0,0,0,0;-1/1:932:-2,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:944:-1,0,0,0,1,0,0;1/1:946:-2,0,0,0,0,0,0;-1/1:956:-1,0,0,0,1,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:986:-1,0,0,0,1,0,0;-1/1:998:-1,0,0,0,1,0,0;1/1:998:0,0,0,0,0,0,0;-1/1:1016:-2,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck224 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 224) = operation980BoundedValue224 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 224 8
    operation980BoundedValue224 operation980BoundedValue232 operation980BoundedCheck232
  decide +kernel

compact_certificate private def operation980BoundedValue216 : Poly := laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;-1/1:52:-3,0,0,0,1,0,0;1/1:52:0,0,0,0,0,0,0;1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;-1/1:62:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;-1/1:134:-1,0,0,0,1,0,0;1/1:136:-2,0,0,0,0,0,0;1/1:136:-1,0,0,0,1,0,0;1/1:144:0,-1,0,0,0,1,0;-1/1:157:0,0,0,0,0,0,0;-1/1:158:-1,0,0,0,1,0,0;-1/1:162:-2,0,0,0,0,0,0;1/1:162:1,-1,0,0,1,1,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;-2/1:172:-4,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:174:0,0,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;1/1:186:-1,-2,0,0,1,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:218:-1,0,0,0,1,0,0;-1/1:234:-2,-2,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:244:0,0,0,0,0,0,0;1/1:262:-2,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:-2,0,0,0,0,0,0;1/1:268:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;1/1:282:0,0,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;1/1:316:-2,0,0,0,0,0,0;1/1:328:-2,0,0,0,0,0,0;1/1:328:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:332:-3,0,0,0,1,0,0;1/1:342:0,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;1/1:348:-2,-2,0,0,0,0,0;1/1:354:-2,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:388:-2,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:398:-1,0,0,0,1,0,0;-1/1:398:0,0,0,0,0,0,0;1/1:402:-2,-2,0,0,0,0,0;-2/1:408:-2,-2,0,0,0,0,0;-1/1:408:-1,-1,0,0,1,1,0;1/1:418:-2,0,0,0,0,0,0;1/1:418:0,0,0,0,0,0,0;1/1:424:0,0,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-2/1:432:0,-2,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;-1/1:433:0,0,0,0,0,0,0;2/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:0,0,0,0,0,0,0;1/1:444:1,-2,0,0,1,0,0;1/1:454:0,0,0,0,0,0,0;-1/1:458:-1,0,0,0,1,0,0;-1/1:458:0,0,0,0,0,0,0;1/1:472:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;1/1:478:-2,0,0,0,0,0,0;1/1:478:0,0,0,0,0,0,0;-1/1:512:-2,0,0,0,0,0,0;1/1:556:-2,0,0,0,0,0,0;1/1:562:-2,0,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:583:0,0,0,0,0,0,0;1/1:586:-2,0,0,0,0,0,0;1/1:592:0,0,0,0,0,0,0;1/1:598:-2,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;1/1:606:-2,-1,0,0,0,1,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:606:2,-1,0,0,0,1,0;-1/1:614:-1,0,0,0,1,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;1/1:622:-2,0,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:626:-1,0,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;1/1:634:0,0,0,0,0,0,0;-1/1:638:-2,0,0,0,0,0,0;-1/1:638:-1,0,0,0,1,0,0;-2/1:642:-2,-2,0,0,0,0,0;1/1:642:-1,-2,0,0,1,0,0;-1/1:643:0,0,0,0,0,0,0;1/1:648:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:656:-1,0,0,0,1,0,0;-1/1:664:-1,0,0,0,1,0,0;1/1:664:0,0,0,0,0,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;-1/1:696:-2,0,0,0,0,0,0;2/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;1/1:708:-1,-1,0,0,1,1,0;1/1:708:0,-2,0,0,0,0,0;1/1:712:-2,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:734:-1,0,0,0,1,0,0;-1/1:739:0,0,0,0,0,0,0;1/1:754:0,0,0,0,0,0,0;-1/1:764:-1,0,0,0,1,0,0;1/1:766:-2,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;1/1:778:-2,0,0,0,0,0,0;-1/1:788:-1,0,0,0,1,0,0;-1/1:794:-1,0,0,0,1,0,0;1/1:796:-2,0,0,0,0,0,0;1/1:796:-1,0,0,0,1,0,0;1/1:802:0,0,0,0,0,0,0;-1/1:806:-1,0,0,0,1,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:818:-1,0,0,0,1,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:824:-1,0,0,0,1,0,0;1/1:832:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;1/1:838:0,0,0,0,0,0,0;1/1:844:0,0,0,0,0,0,0;-1/1:848:-2,0,0,0,0,0,0;-1/1:848:-1,0,0,0,1,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;2/1:864:-2,-1,0,0,0,1,0;2/1:864:-1,-2,0,0,1,0,0;2/1:864:-1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:878:-2,0,0,0,0,0,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:878:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:892:-2,0,0,0,0,0,0;1/1:892:0,0,0,0,0,0,0;1/1:898:-2,0,0,0,0,0,0;-1/1:902:-2,0,0,0,0,0,0;1/1:916:-2,0,0,0,0,0,0;1/1:922:-2,0,0,0,0,0,0;1/1:922:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:944:-1,0,0,0,1,0,0;1/1:946:-2,0,0,0,0,0,0;-1/1:956:-1,0,0,0,1,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;1/1:976:-2,0,0,0,0,0,0;-1/1:986:-1,0,0,0,1,0,0;-1/1:998:-1,0,0,0,1,0,0;1/1:998:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck216 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 216) = operation980BoundedValue216 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 216 8
    operation980BoundedValue216 operation980BoundedValue224 operation980BoundedCheck224
  decide +kernel

compact_certificate private def operation980BoundedValue208 : Poly := laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;-1/1:52:-3,0,0,0,1,0,0;1/1:52:0,0,0,0,0,0,0;1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;-1/1:62:0,0,0,0,0,0,0;-1/1:68:-1,0,0,0,1,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:74:-1,0,0,0,1,0,0;1/1:76:-2,0,0,0,0,0,0;1/1:94:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;-1/1:134:-1,0,0,0,1,0,0;1/1:136:-2,0,0,0,0,0,0;1/1:136:-1,0,0,0,1,0,0;1/1:142:0,0,0,0,0,0,0;1/1:144:0,-1,0,0,0,1,0;-1/1:157:0,0,0,0,0,0,0;-1/1:158:-1,0,0,0,1,0,0;-1/1:162:-2,0,0,0,0,0,0;1/1:162:1,-1,0,0,1,1,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;-2/1:172:-4,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:174:0,0,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;1/1:186:-1,-2,0,0,1,0,0;1/1:186:0,-1,0,0,0,1,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;1/1:202:-2,0,0,0,0,0,0;-1/1:218:-1,0,0,0,1,0,0;1/1:226:-2,0,0,0,0,0,0;-1/1:234:-2,-2,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:244:0,0,0,0,0,0,0;1/1:262:-2,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:-2,0,0,0,0,0,0;1/1:268:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-1/1:278:-1,0,0,0,1,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;1/1:282:0,0,0,0,0,0,0;-1/1:284:-1,0,0,0,1,0,0;-1/1:289:0,0,0,0,0,0,0;1/1:304:0,0,0,0,0,0,0;1/1:316:-2,0,0,0,0,0,0;1/1:328:-2,0,0,0,0,0,0;1/1:328:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:332:-3,0,0,0,1,0,0;1/1:342:0,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;1/1:348:-2,-2,0,0,0,0,0;1/1:348:-1,0,0,0,1,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:388:-2,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:398:-1,0,0,0,1,0,0;-1/1:398:0,0,0,0,0,0,0;1/1:402:-2,-2,0,0,0,0,0;-2/1:408:-2,-2,0,0,0,0,0;-1/1:408:-1,-1,0,0,1,1,0;1/1:418:-2,0,0,0,0,0,0;1/1:418:0,0,0,0,0,0,0;1/1:424:0,0,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-2/1:432:0,-2,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;-1/1:433:0,0,0,0,0,0,0;1/1:436:-2,0,0,0,0,0,0;2/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:0,0,0,0,0,0,0;1/1:444:1,-2,0,0,1,0,0;1/1:454:0,0,0,0,0,0,0;-1/1:458:-1,0,0,0,1,0,0;-1/1:458:0,0,0,0,0,0,0;1/1:472:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;1/1:478:-2,0,0,0,0,0,0;1/1:478:0,0,0,0,0,0,0;-1/1:488:-1,0,0,0,1,0,0;-1/1:494:-1,0,0,0,1,0,0;-1/1:512:-2,0,0,0,0,0,0;1/1:556:-2,0,0,0,0,0,0;1/1:562:-2,0,0,0,0,0,0;1/1:562:0,0,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:583:0,0,0,0,0,0,0;1/1:586:-2,0,0,0,0,0,0;1/1:592:0,0,0,0,0,0,0;1/1:598:-2,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:606:2,-1,0,0,0,1,0;-1/1:614:-1,0,0,0,1,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;1/1:622:-2,0,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:626:-1,0,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;1/1:634:0,0,0,0,0,0,0;-1/1:638:-1,0,0,0,1,0,0;-2/1:642:-2,-2,0,0,0,0,0;1/1:642:-1,-2,0,0,1,0,0;-1/1:643:0,0,0,0,0,0,0;1/1:646:-2,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:656:-1,0,0,0,1,0,0;-1/1:664:-1,0,0,0,1,0,0;1/1:664:0,0,0,0,0,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;-1/1:696:-2,0,0,0,0,0,0;2/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;-1/1:708:-2,0,0,0,0,0,0;1/1:708:-1,-1,0,0,1,1,0;1/1:708:0,-2,0,0,0,0,0;1/1:712:-2,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;1/1:718:0,0,0,0,0,0,0;1/1:724:0,0,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:734:-1,0,0,0,1,0,0;-1/1:739:0,0,0,0,0,0,0;1/1:754:0,0,0,0,0,0,0;-1/1:764:-1,0,0,0,1,0,0;1/1:766:-2,0,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0;1/1:772:0,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;1/1:778:-2,0,0,0,0,0,0;-1/1:788:-1,0,0,0,1,0,0;-1/1:794:-1,0,0,0,1,0,0;1/1:796:-2,0,0,0,0,0,0;1/1:796:-1,0,0,0,1,0,0;1/1:802:0,0,0,0,0,0,0;-1/1:806:-1,0,0,0,1,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:818:-1,0,0,0,1,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:824:-1,0,0,0,1,0,0;1/1:832:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;1/1:838:0,0,0,0,0,0,0;1/1:844:0,0,0,0,0,0,0;-1/1:848:-2,0,0,0,0,0,0;-1/1:848:-1,0,0,0,1,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;1/1:864:-2,-1,0,0,0,1,0;2/1:864:-1,-2,0,0,1,0,0;2/1:864:-1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:878:-2,0,0,0,0,0,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:878:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:892:-2,0,0,0,0,0,0;1/1:892:0,0,0,0,0,0,0;1/1:898:-2,0,0,0,0,0,0;-1/1:908:-1,0,0,0,1,0,0;-1/1:914:-1,0,0,0,1,0,0;1/1:916:-2,0,0,0,0,0,0;1/1:922:-2,0,0,0,0,0,0;1/1:922:0,0,0,0,0,0,0;1/1:928:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:934:0,0,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:944:-1,0,0,0,1,0,0;1/1:946:-2,0,0,0,0,0,0;-1/1:956:-1,0,0,0,1,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;1/1:976:-2,0,0,0,0,0,0;-1/1:986:-1,0,0,0,1,0,0;1/1:988:-2,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;1/1:1016:1,0,0,0,1,0,0"

compact_certificate private theorem operation980BoundedCheck208 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 208) = operation980BoundedValue208 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 208 8
    operation980BoundedValue208 operation980BoundedValue216 operation980BoundedCheck216
  decide +kernel

compact_certificate private def operation980BoundedValue200 : Poly := laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;-1/1:68:-1,0,0,0,1,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:74:-1,0,0,0,1,0,0;1/1:76:-2,0,0,0,0,0,0;1/1:94:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;-1/1:134:-1,0,0,0,1,0,0;1/1:136:-2,0,0,0,0,0,0;1/1:142:0,0,0,0,0,0,0;1/1:148:-2,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:158:-1,0,0,0,1,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;-2/1:172:-4,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:174:0,0,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;1/1:186:-1,-2,0,0,1,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:188:-1,0,0,0,1,0,0;-1/1:192:-2,-2,0,0,0,0,0;1/1:202:-2,0,0,0,0,0,0;-1/1:218:-1,0,0,0,1,0,0;1/1:226:-2,0,0,0,0,0,0;-1/1:234:-2,-2,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:244:0,0,0,0,0,0,0;1/1:262:-2,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:-2,0,0,0,0,0,0;1/1:268:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-1/1:278:-1,0,0,0,1,0,0;-1/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;1/1:282:0,0,0,0,0,0,0;-1/1:284:-1,0,0,0,1,0,0;-1/1:289:0,0,0,0,0,0,0;1/1:304:0,0,0,0,0,0,0;1/1:316:-2,0,0,0,0,0,0;1/1:328:-2,0,0,0,0,0,0;1/1:328:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:332:-3,0,0,0,1,0,0;1/1:348:-4,-2,0,0,0,0,0;1/1:348:-2,-2,0,0,0,0,0;1/1:348:-1,0,0,0,1,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:388:-2,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:398:-1,0,0,0,1,0,0;1/1:402:-2,-2,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;1/1:412:0,0,0,0,0,0,0;1/1:418:-2,0,0,0,0,0,0;1/1:418:0,0,0,0,0,0,0;1/1:424:0,0,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:432:0,-2,0,0,0,0,0;1/1:432:0,0,0,0,0,0,0;-1/1:433:0,0,0,0,0,0,0;1/1:436:-2,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:0,0,0,0,0,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:446:-1,0,0,0,1,0,0;1/1:454:0,0,0,0,0,0,0;-1/1:458:-1,0,0,0,1,0,0;1/1:472:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;1/1:478:-2,0,0,0,0,0,0;1/1:478:0,0,0,0,0,0,0;-1/1:488:-1,0,0,0,1,0,0;-1/1:494:-1,0,0,0,1,0,0;1/1:556:-2,0,0,0,0,0,0;1/1:562:-2,0,0,0,0,0,0;1/1:562:0,0,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:583:0,0,0,0,0,0,0;1/1:586:-2,0,0,0,0,0,0;1/1:592:0,0,0,0,0,0,0;1/1:598:-2,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:614:-1,0,0,0,1,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;1/1:622:-2,0,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:626:-1,0,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;1/1:634:0,0,0,0,0,0,0;-1/1:638:-1,0,0,0,1,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;1/1:646:-2,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:656:-1,0,0,0,1,0,0;-1/1:664:-1,0,0,0,1,0,0;1/1:664:0,0,0,0,0,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;-1/1:696:-2,0,0,0,0,0,0;2/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;-1/1:708:-2,0,0,0,0,0,0;1/1:708:0,-2,0,0,0,0,0;1/1:712:-2,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;1/1:718:0,0,0,0,0,0,0;1/1:724:0,0,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:734:-1,0,0,0,1,0,0;-1/1:739:0,0,0,0,0,0,0;1/1:748:0,0,0,0,0,0,0;1/1:754:0,0,0,0,0,0,0;-1/1:764:-1,0,0,0,1,0,0;1/1:766:-2,0,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0;1/1:772:0,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;1/1:778:-2,0,0,0,0,0,0;-1/1:788:-1,0,0,0,1,0,0;-1/1:794:-1,0,0,0,1,0,0;1/1:796:-2,0,0,0,0,0,0;1/1:802:0,0,0,0,0,0,0;-1/1:806:-1,0,0,0,1,0,0;1/1:808:0,0,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:818:-1,0,0,0,1,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:824:-1,0,0,0,1,0,0;1/1:832:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:836:-1,0,0,0,1,0,0;1/1:838:0,0,0,0,0,0,0;1/1:844:0,0,0,0,0,0,0;-1/1:848:-1,0,0,0,1,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:862:-2,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,-2,0,0,1,0,0;2/1:864:-1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:878:-2,0,0,0,0,0,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:878:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:-1,0,0,0,1,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:892:-2,0,0,0,0,0,0;1/1:892:0,0,0,0,0,0,0;1/1:898:-2,0,0,0,0,0,0;-1/1:908:-1,0,0,0,1,0,0;-1/1:914:-1,0,0,0,1,0,0;1/1:916:-2,0,0,0,0,0,0;1/1:922:-2,0,0,0,0,0,0;1/1:922:0,0,0,0,0,0,0;1/1:928:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:934:0,0,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:944:-1,0,0,0,1,0,0;1/1:946:-2,0,0,0,0,0,0;-1/1:956:-1,0,0,0,1,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;1/1:976:-2,0,0,0,0,0,0;-1/1:986:-1,0,0,0,1,0,0;1/1:988:-2,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;1/1:1016:1,0,0,0,1,0,0"

compact_certificate private theorem operation980BoundedCheck200 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 200) = operation980BoundedValue200 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 200 8
    operation980BoundedValue200 operation980BoundedValue208 operation980BoundedCheck208
  decide +kernel

compact_certificate private def operation980BoundedValue192 : Poly := laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;-1/1:68:-1,0,0,0,1,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:74:-1,0,0,0,1,0,0;1/1:76:-2,0,0,0,0,0,0;1/1:94:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;-1/1:134:-1,0,0,0,1,0,0;1/1:136:-2,0,0,0,0,0,0;1/1:142:0,0,0,0,0,0,0;1/1:148:-2,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:158:-1,0,0,0,1,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;-2/1:172:-4,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:174:0,0,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;1/1:186:-1,-2,0,0,1,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:188:-1,0,0,0,1,0,0;-1/1:192:-2,-2,0,0,0,0,0;1/1:202:-2,0,0,0,0,0,0;-1/1:218:-1,0,0,0,1,0,0;1/1:226:-2,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:244:0,0,0,0,0,0,0;1/1:262:-2,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:-2,0,0,0,0,0,0;1/1:268:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-1/1:278:-1,0,0,0,1,0,0;-1/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:284:-1,0,0,0,1,0,0;-1/1:289:0,0,0,0,0,0,0;1/1:304:0,0,0,0,0,0,0;1/1:316:-2,0,0,0,0,0,0;1/1:328:-2,0,0,0,0,0,0;1/1:328:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:332:-3,0,0,0,1,0,0;1/1:348:-4,-2,0,0,0,0,0;1/1:348:-2,-2,0,0,0,0,0;1/1:348:-1,0,0,0,1,0,0;-1/1:373:0,0,0,0,0,0,0;1/1:376:-2,0,0,0,0,0,0;1/1:382:0,0,0,0,0,0,0;-1/1:386:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:388:-2,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:398:-1,0,0,0,1,0,0;1/1:402:-2,-2,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;1/1:412:0,0,0,0,0,0,0;1/1:418:-2,0,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:432:0,-2,0,0,0,0,0;-1/1:433:0,0,0,0,0,0,0;1/1:436:-2,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:446:-1,0,0,0,1,0,0;-1/1:457:0,0,0,0,0,0,0;-1/1:458:-1,0,0,0,1,0,0;1/1:474:-1,0,0,0,1,0,0;1/1:478:-2,0,0,0,0,0,0;-1/1:488:-1,0,0,0,1,0,0;-1/1:494:-1,0,0,0,1,0,0;1/1:556:-2,0,0,0,0,0,0;1/1:562:-2,0,0,0,0,0,0;1/1:562:0,0,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:583:0,0,0,0,0,0,0;1/1:586:-2,0,0,0,0,0,0;1/1:592:0,0,0,0,0,0,0;1/1:598:-2,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:614:-1,0,0,0,1,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:626:-1,0,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;1/1:634:0,0,0,0,0,0,0;-1/1:638:-1,0,0,0,1,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:656:-1,0,0,0,1,0,0;-1/1:664:-1,0,0,0,1,0,0;1/1:664:0,0,0,0,0,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;-1/1:696:-2,0,0,0,0,0,0;2/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;-1/1:708:-2,0,0,0,0,0,0;1/1:712:-2,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:-1,0,0,0,1,0,0;1/1:718:0,0,0,0,0,0,0;1/1:724:0,0,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:734:-1,0,0,0,1,0,0;-1/1:739:0,0,0,0,0,0,0;1/1:748:0,0,0,0,0,0,0;1/1:754:0,0,0,0,0,0,0;-1/1:764:-1,0,0,0,1,0,0;1/1:772:-2,0,0,0,0,0,0;1/1:772:0,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;-1/1:788:-1,0,0,0,1,0,0;-1/1:794:-1,0,0,0,1,0,0;1/1:796:-2,0,0,0,0,0,0;1/1:802:0,0,0,0,0,0,0;-1/1:806:-1,0,0,0,1,0,0;1/1:808:0,0,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:818:-1,0,0,0,1,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:824:-1,0,0,0,1,0,0;1/1:832:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:838:-2,0,0,0,0,0,0;1/1:838:0,0,0,0,0,0,0;1/1:844:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,-2,0,0,1,0,0;2/1:864:-1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:878:-2,0,0,0,0,0,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:878:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:884:0,0,0,0,0,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:892:-2,0,0,0,0,0,0;1/1:892:0,0,0,0,0,0,0;1/1:898:-2,0,0,0,0,0,0;1/1:916:-2,0,0,0,0,0,0;1/1:922:-2,0,0,0,0,0,0;1/1:922:0,0,0,0,0,0,0;1/1:928:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:934:0,0,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:943:0,0,0,0,0,0,0;1/1:946:-2,0,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;1/1:976:-2,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:986:-1,0,0,0,1,0,0;1/1:988:-2,0,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;-1/1:1003:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck192 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 192) = operation980BoundedValue192 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 192 8
    operation980BoundedValue192 operation980BoundedValue200 operation980BoundedCheck200
  decide +kernel

compact_certificate private def operation980BoundedValue184 : Poly := laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;1/1:58:-2,0,0,0,0,0,0;-1/1:58:-2,0,0,0,2,0,0;-1/1:68:-1,0,0,0,1,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:74:-1,0,0,0,1,0,0;1/1:76:-2,0,0,0,0,0,0;1/1:94:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;1/1:116:-3,0,0,0,1,0,0;-1/1:134:-1,0,0,0,1,0,0;1/1:136:-2,0,0,0,0,0,0;1/1:142:0,0,0,0,0,0,0;1/1:148:-2,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:158:-1,0,0,0,1,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;1/1:166:-2,0,0,0,0,0,0;-1/1:166:-2,0,0,0,2,0,0;-2/1:172:-4,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:174:0,0,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;1/1:186:-1,-2,0,0,1,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:188:-1,0,0,0,1,0,0;-1/1:192:-2,-2,0,0,0,0,0;1/1:202:-2,0,0,0,0,0,0;-1/1:218:-1,0,0,0,1,0,0;1/1:226:-2,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:244:0,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:-2,0,0,0,0,0,0;1/1:268:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-1/1:278:-1,0,0,0,1,0,0;-1/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:284:-1,0,0,0,1,0,0;-1/1:289:0,0,0,0,0,0,0;1/1:304:0,0,0,0,0,0,0;1/1:316:-2,0,0,0,0,0,0;1/1:328:-2,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:332:-3,0,0,0,1,0,0;1/1:348:-4,-2,0,0,0,0,0;1/1:348:-2,-2,0,0,0,0,0;1/1:348:-1,0,0,0,1,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;1/1:376:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:388:-2,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:398:-1,0,0,0,1,0,0;1/1:402:-2,-2,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:432:0,-2,0,0,0,0,0;-1/1:433:0,0,0,0,0,0,0;1/1:436:-2,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:446:-1,0,0,0,1,0,0;-1/1:457:0,0,0,0,0,0,0;-1/1:458:-1,0,0,0,1,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:488:-1,0,0,0,1,0,0;-1/1:494:-1,0,0,0,1,0,0;1/1:556:-2,0,0,0,0,0,0;1/1:562:0,0,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:583:0,0,0,0,0,0,0;1/1:592:0,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:614:-1,0,0,0,1,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:626:-1,0,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;1/1:634:0,0,0,0,0,0,0;-1/1:638:-1,0,0,0,1,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;1/1:664:0,0,0,0,0,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;-1/1:696:-2,0,0,0,0,0,0;2/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;-1/1:708:-2,0,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:712:-2,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;1/1:724:0,0,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;1/1:748:0,0,0,0,0,0,0;1/1:754:0,0,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0;1/1:772:0,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;-1/1:788:-1,0,0,0,1,0,0;1/1:796:-2,0,0,0,0,0,0;1/1:802:0,0,0,0,0,0,0;1/1:808:0,0,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;1/1:832:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:838:-2,0,0,0,0,0,0;1/1:838:0,0,0,0,0,0,0;1/1:844:0,0,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,-2,0,0,1,0,0;2/1:864:-1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:878:-2,0,0,0,0,0,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:878:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:892:-2,0,0,0,0,0,0;1/1:898:-2,0,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;1/1:916:-2,0,0,0,0,0,0;1/1:922:-2,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;1/1:946:-2,0,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;1/1:976:-2,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:986:-1,0,0,0,1,0,0;1/1:988:-2,0,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;-1/1:1003:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck184 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 184) = operation980BoundedValue184 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 184 8
    operation980BoundedValue184 operation980BoundedValue192 operation980BoundedCheck192
  decide +kernel

compact_certificate private def operation980BoundedValue176 : Poly := laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:68:-1,0,0,0,1,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:74:-1,0,0,0,1,0,0;1/1:76:-2,0,0,0,0,0,0;1/1:94:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:134:-1,0,0,0,1,0,0;1/1:136:-2,0,0,0,0,0,0;1/1:142:0,0,0,0,0,0,0;1/1:148:-2,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:158:-1,0,0,0,1,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-2/1:172:-4,0,0,0,0,0,0;1/1:172:0,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:174:0,0,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;1/1:186:-1,-2,0,0,1,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:188:-1,0,0,0,1,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:218:-1,0,0,0,1,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:-2,0,0,0,0,0,0;1/1:268:0,0,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-1/1:278:-1,0,0,0,1,0,0;-1/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:284:-1,0,0,0,1,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;1/1:316:-2,0,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;1/1:328:-2,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;1/1:348:-2,-2,0,0,0,0,0;1/1:348:-1,0,0,0,1,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;1/1:376:-2,0,0,0,0,0,0;-1/1:386:-1,0,0,0,1,0,0;1/1:388:-2,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:398:-1,0,0,0,1,0,0;1/1:402:-2,-2,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:432:0,-2,0,0,0,0,0;-1/1:433:0,0,0,0,0,0,0;1/1:436:-2,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:446:-1,0,0,0,1,0,0;-1/1:457:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;1/1:556:-2,0,0,0,0,0,0;1/1:562:0,0,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:583:0,0,0,0,0,0,0;1/1:592:0,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;1/1:634:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;1/1:664:0,0,0,0,0,0,0;1/1:688:-2,0,0,0,0,0,0;1/1:694:-1,0,0,0,1,0,0;-1/1:696:-2,0,0,0,0,0,0;2/1:696:-1,-2,0,0,1,0,0;1/1:702:-4,-2,0,0,0,0,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:702:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;1/1:706:-1,0,0,0,1,0,0;-1/1:708:-2,0,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:712:-2,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;1/1:718:0,0,0,0,0,0,0;1/1:724:0,0,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;1/1:748:0,0,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;1/1:772:-2,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;-1/1:788:-1,0,0,0,1,0,0;1/1:796:-2,0,0,0,0,0,0;1/1:808:0,0,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,-2,0,0,1,0,0;2/1:864:-1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:878:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:892:-2,0,0,0,0,0,0;1/1:898:-2,0,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;1/1:922:-2,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;1/1:946:-2,0,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:986:-1,0,0,0,1,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;-1/1:1003:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck176 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 176) = operation980BoundedValue176 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 176 8
    operation980BoundedValue176 operation980BoundedValue184 operation980BoundedCheck184
  decide +kernel

compact_certificate private def operation980BoundedValue168 : Poly := laurent_polynomial% "1/1:34:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:68:-1,0,0,0,1,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:74:-1,0,0,0,1,0,0;1/1:76:-2,0,0,0,0,0,0;1/1:94:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:134:-1,0,0,0,1,0,0;1/1:136:-2,0,0,0,0,0,0;1/1:148:-2,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:158:-1,0,0,0,1,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:177:0,0,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;1/1:186:-1,-2,0,0,1,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:188:-1,0,0,0,1,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:218:-1,0,0,0,1,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:-2,0,0,0,0,0,0;1/1:268:0,0,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-1/1:278:-1,0,0,0,1,0,0;-1/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:289:0,0,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;1/1:316:-2,0,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;1/1:328:-2,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;1/1:348:-2,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;1/1:376:-2,0,0,0,0,0,0;1/1:388:-2,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;1/1:402:-2,-2,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:432:0,-2,0,0,0,0,0;-1/1:433:0,0,0,0,0,0,0;1/1:436:-2,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:457:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;1/1:556:-2,0,0,0,0,0,0;1/1:562:0,0,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:583:0,0,0,0,0,0,0;1/1:592:0,0,0,0,0,0,0;1/1:604:0,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;1/1:622:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;1/1:634:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;1/1:664:0,0,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;2/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;1/1:699:0,0,0,0,0,0,0;1/1:702:-4,-2,0,0,0,0,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;-1/1:788:-1,0,0,0,1,0,0;1/1:808:0,0,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,-2,0,0,1,0,0;2/1:864:-1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:898:-2,0,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;1/1:922:-2,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;1/1:946:-2,0,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:986:-1,0,0,0,1,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;-1/1:1003:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck168 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 168) = operation980BoundedValue168 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 168 8
    operation980BoundedValue168 operation980BoundedValue176 operation980BoundedCheck176
  decide +kernel

compact_certificate private def operation980BoundedValue160 : Poly := laurent_polynomial% "-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:177:0,0,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;1/1:186:-1,-2,0,0,1,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:0,0,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-1/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:289:0,0,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;1/1:328:-2,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;1/1:348:-2,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;1/1:402:-2,-2,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:432:0,-2,0,0,0,0,0;-1/1:433:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:457:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:618:0,-2,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:667:0,0,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;1/1:699:0,0,0,0,0,0,0;1/1:702:-4,-2,0,0,0,0,0;1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;-1/1:788:-1,0,0,0,1,0,0;1/1:808:0,0,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,-2,0,0,1,0,0;2/1:864:-1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:898:-2,0,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;1/1:922:-2,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;1/1:946:-2,0,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:986:-1,0,0,0,1,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;-1/1:1003:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck160 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 160) = operation980BoundedValue160 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 160 8
    operation980BoundedValue160 operation980BoundedValue168 operation980BoundedCheck168
  decide +kernel

compact_certificate private def operation980BoundedValue152 : Poly := laurent_polynomial% "-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:177:0,0,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:0,0,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-1/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:289:0,0,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;1/1:328:-2,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;1/1:410:0,0,0,0,0,0,0;-1/1:426:-3,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:432:0,-2,0,0,0,0,0;-1/1:433:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:640:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;1/1:699:0,0,0,0,0,0,0;1/1:702:-4,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;-1/1:788:-1,0,0,0,1,0,0;-1/1:792:-2,-2,0,0,0,0,0;1/1:808:0,0,0,0,0,0,0;1/1:810:-2,-2,0,0,0,0,0;-1/1:810:-2,0,0,0,0,0,0;1/1:810:-1,-2,0,0,1,0,0;-1/1:810:0,-1,0,0,0,1,0;1/1:815:0,0,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:838:-2,0,0,0,0,0,0;1/1:845:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;-1/1:864:-3,0,0,0,1,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,-2,0,0,1,0,0;2/1:864:-1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:898:-2,0,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;1/1:922:-2,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:935:0,0,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;1/1:946:-2,0,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:986:-1,0,0,0,1,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;-1/1:1003:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck152 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 152) = operation980BoundedValue152 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 152 8
    operation980BoundedValue152 operation980BoundedValue160 operation980BoundedCheck160
  decide +kernel

compact_certificate private def operation980BoundedValue144 : Poly := laurent_polynomial% "-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:164:-3,0,0,0,1,0,0;-1/1:164:-1,0,0,0,1,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:177:0,0,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:0,0,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:289:0,0,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;1/1:328:-2,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;1/1:394:0,0,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;1/1:410:0,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:432:0,-2,0,0,0,0,0;-1/1:433:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:640:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;1/1:699:0,0,0,0,0,0,0;1/1:702:-4,-2,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;1/1:706:-2,0,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:788:-1,0,0,0,1,0,0;-1/1:792:-2,-2,0,0,0,0,0;1/1:808:0,0,0,0,0,0,0;1/1:810:-2,-2,0,0,0,0,0;1/1:810:-2,-1,0,0,0,1,0;1/1:810:-1,-2,0,0,1,0,0;-1/1:810:-1,0,0,0,1,0,0;-1/1:810:0,-2,0,0,0,0,0;-1/1:810:0,-1,0,0,0,1,0;1/1:815:0,0,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:838:-2,0,0,0,0,0,0;1/1:845:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,-2,0,0,1,0,0;1/1:864:-1,0,0,0,1,0,0;-1/1:876:-3,-2,0,0,1,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:878:-1,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:898:-2,0,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;1/1:922:-2,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;1/1:946:-2,0,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:974:-1,0,0,0,1,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:986:-1,0,0,0,1,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:998:-1,0,0,0,1,0,0;-1/1:1003:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck144 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 144) = operation980BoundedValue144 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 144 8
    operation980BoundedValue144 operation980BoundedValue152 operation980BoundedCheck152
  decide +kernel

compact_certificate private def operation980BoundedValue136 : Poly := laurent_polynomial% "-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:164:-3,0,0,0,1,0,0;-1/1:164:-1,0,0,0,1,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;-1/1:174:-3,-2,0,0,1,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:177:0,0,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:0,0,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:289:0,0,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;1/1:328:-2,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;1/1:348:-4,-2,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;1/1:388:0,0,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;1/1:410:0,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:640:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;1/1:678:-2,-2,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;1/1:699:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:702:-2,0,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:776:-1,0,0,0,1,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;1/1:808:0,0,0,0,0,0,0;1/1:810:-2,-2,0,0,0,0,0;1/1:810:-2,-1,0,0,0,1,0;1/1:810:-2,0,0,0,0,0,0;1/1:810:-1,-2,0,0,1,0,0;-1/1:810:-1,0,0,0,1,0,0;-1/1:810:0,-2,0,0,0,0,0;-1/1:810:0,-1,0,0,0,1,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:838:-2,0,0,0,0,0,0;1/1:845:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;1/1:876:-1,0,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck136 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 136) = operation980BoundedValue136 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 136 8
    operation980BoundedValue136 operation980BoundedValue144 operation980BoundedCheck144
  decide +kernel

compact_certificate private def operation980BoundedValue128 : Poly := laurent_polynomial% "-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:177:0,0,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:0,0,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:580:-2,0,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:640:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;1/1:699:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;1/1:810:-2,-2,0,0,0,0,0;1/1:810:-2,-1,0,0,0,1,0;1/1:810:-2,0,0,0,0,0,0;-1/1:810:-1,0,0,0,1,0,0;-1/1:810:0,-2,0,0,0,0,0;-1/1:810:0,-1,0,0,0,1,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:838:-2,0,0,0,0,0,0;1/1:845:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck128 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 128) = operation980BoundedValue128 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 128 8
    operation980BoundedValue128 operation980BoundedValue136 operation980BoundedCheck136
  decide +kernel

compact_certificate private def operation980BoundedValue120 : Poly := laurent_polynomial% "-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;1/1:160:-2,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:177:0,0,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;1/1:220:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:268:0,0,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;1/1:699:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:810:0,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;1/1:845:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;1/1:958:-2,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck120 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 120) = operation980BoundedValue120 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 120 8
    operation980BoundedValue120 operation980BoundedValue128 operation980BoundedCheck128
  decide +kernel

compact_certificate private def operation980BoundedValue112 : Poly := laurent_polynomial% "-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;1/1:76:-2,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;1/1:160:-2,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;1/1:220:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:262:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;1/1:699:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck112 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 112) = operation980BoundedValue112 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 112 8
    operation980BoundedValue112 operation980BoundedValue120 operation980BoundedCheck120
  decide +kernel

compact_certificate private def operation980BoundedValue104 : Poly := laurent_polynomial% "-1/1:19:0,0,0,0,0,0,0;-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:240:-2,-2,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:312:-2,-2,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:318:-2,-2,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:390:-2,-2,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:565:0,0,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;1/1:699:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:732:-2,-2,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:738:-2,-2,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:745:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:787:0,0,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck104 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 104) = operation980BoundedValue104 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 104 8
    operation980BoundedValue104 operation980BoundedValue112 operation980BoundedCheck112
  decide +kernel

compact_certificate private def operation980BoundedValue96 : Poly := laurent_polynomial% "-1/1:19:0,0,0,0,0,0,0;-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:133:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:240:-2,-2,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:312:-2,-2,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:318:-2,-2,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:325:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:349:0,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:390:-2,-2,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:565:0,0,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:637:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:732:-2,-2,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:738:-2,-2,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:745:0,0,0,0,0,0,0;-1/1:763:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:775:0,0,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:787:0,0,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:847:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:918:-2,-2,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck96 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 96) = operation980BoundedValue96 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 96 8
    operation980BoundedValue96 operation980BoundedValue104 operation980BoundedCheck104
  decide +kernel

compact_certificate private def operation980BoundedValue88 : Poly := laurent_polynomial% "-1/1:19:0,0,0,0,0,0,0;-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:133:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;-1/1:217:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:240:-2,-2,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:312:-2,-2,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:318:-2,-2,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:325:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:349:0,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:390:-2,-2,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;-1/1:469:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:475:0,0,0,0,0,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:523:0,0,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:565:0,0,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:582:-2,-2,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:637:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:732:-2,-2,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:738:-2,-2,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:745:0,0,0,0,0,0,0;-1/1:763:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:775:0,0,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:787:0,0,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:847:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:889:0,0,0,0,0,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:918:-2,-2,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:942:-2,-2,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:948:-2,-2,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck88 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 88) = operation980BoundedValue88 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 88 8
    operation980BoundedValue88 operation980BoundedValue96 operation980BoundedCheck96
  decide +kernel

compact_certificate private def operation980BoundedValue80 : Poly := laurent_polynomial% "-1/1:19:0,0,0,0,0,0,0;-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:108:-2,-2,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:133:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;-1/1:217:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:240:-2,-2,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:312:-2,-2,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:318:-2,-2,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:325:0,0,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:349:0,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:355:0,0,0,0,0,0,0;-1/1:360:-2,-2,0,0,0,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:390:-2,-2,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;-1/1:469:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:475:0,0,0,0,0,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:523:0,0,0,0,0,0,0;-1/1:558:-2,-2,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:565:0,0,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:582:-2,-2,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:625:0,0,0,0,0,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:637:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:679:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:732:-2,-2,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:738:-2,-2,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:745:0,0,0,0,0,0,0;-1/1:763:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:775:0,0,0,0,0,0,0;-1/1:780:-2,-2,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:787:0,0,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:847:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:889:0,0,0,0,0,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:918:-2,-2,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:942:-2,-2,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:948:-2,-2,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:996:-2,-2,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck80 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 80) = operation980BoundedValue80 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 80 8
    operation980BoundedValue80 operation980BoundedValue88 operation980BoundedCheck88
  decide +kernel

compact_certificate private def operation980BoundedValue72 : Poly := laurent_polynomial% "-1/1:19:0,0,0,0,0,0,0;-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:96:-2,-2,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:108:-2,-2,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:133:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;-1/1:217:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:240:-2,-2,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:270:-2,-2,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:312:-2,-2,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:318:-2,-2,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:325:0,0,0,0,0,0,0;-1/1:330:-2,-2,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:349:0,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:355:0,0,0,0,0,0,0;-1/1:360:-2,-2,0,0,0,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:390:-2,-2,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;-1/1:469:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:475:0,0,0,0,0,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:523:0,0,0,0,0,0,0;-1/1:553:0,0,0,0,0,0,0;-1/1:558:-2,-2,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:565:0,0,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:582:-2,-2,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:625:0,0,0,0,0,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:637:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:679:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:690:-2,-2,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:732:-2,-2,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:738:-2,-2,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:745:0,0,0,0,0,0,0;-1/1:750:-2,-2,0,0,0,0,0;-1/1:763:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:775:0,0,0,0,0,0,0;-1/1:780:-2,-2,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:787:0,0,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:847:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:889:0,0,0,0,0,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:900:-2,-2,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:918:-2,-2,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:942:-2,-2,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:948:-2,-2,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:973:0,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:996:-2,-2,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck72 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 72) = operation980BoundedValue72 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 72 8
    operation980BoundedValue72 operation980BoundedValue80 operation980BoundedCheck80
  decide +kernel

compact_certificate private def operation980BoundedValue64 : Poly := laurent_polynomial% "-1/1:19:0,0,0,0,0,0,0;-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:60:-2,-2,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:96:-2,-2,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:108:-2,-2,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:120:-2,-2,0,0,0,0,0;-1/1:133:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:180:-2,-2,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;-1/1:217:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:240:-2,-2,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:270:-2,-2,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:312:-2,-2,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:318:-2,-2,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:325:0,0,0,0,0,0,0;-1/1:330:-2,-2,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:349:0,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:355:0,0,0,0,0,0,0;-1/1:360:-2,-2,0,0,0,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:390:-2,-2,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;-1/1:469:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:475:0,0,0,0,0,0,0;-1/1:480:-2,-2,0,0,0,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:523:0,0,0,0,0,0,0;-1/1:553:0,0,0,0,0,0,0;-1/1:558:-2,-2,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:565:0,0,0,0,0,0,0;-1/1:570:-2,-2,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:582:-2,-2,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:595:0,0,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:625:0,0,0,0,0,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:637:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:679:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:690:-2,-2,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:732:-2,-2,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:738:-2,-2,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:745:0,0,0,0,0,0,0;-1/1:750:-2,-2,0,0,0,0,0;-1/1:763:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:775:0,0,0,0,0,0,0;-1/1:780:-2,-2,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:787:0,0,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:805:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:847:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:870:-2,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:889:0,0,0,0,0,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:900:-2,-2,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:918:-2,-2,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:942:-2,-2,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:948:-2,-2,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:973:0,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:996:-2,-2,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck64 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 64) = operation980BoundedValue64 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 64 8
    operation980BoundedValue64 operation980BoundedValue72 operation980BoundedCheck72
  decide +kernel

compact_certificate private def operation980BoundedValue56 : Poly := laurent_polynomial% "-1/1:19:0,0,0,0,0,0,0;-1/1:30:-2,-2,0,0,0,0,0;-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:60:-2,-2,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:96:-2,-2,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:108:-2,-2,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:120:-2,-2,0,0,0,0,0;-1/1:133:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:180:-2,-2,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;-1/1:217:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:240:-2,-2,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:270:-2,-2,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:312:-2,-2,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:318:-2,-2,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:325:0,0,0,0,0,0,0;-1/1:330:-2,-2,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:349:0,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:355:0,0,0,0,0,0,0;-1/1:360:-2,-2,0,0,0,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:385:0,0,0,0,0,0,0;-1/1:390:-2,-2,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:420:-2,-2,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;-1/1:469:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:475:0,0,0,0,0,0,0;-1/1:480:-2,-2,0,0,0,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:523:0,0,0,0,0,0,0;-1/1:535:0,0,0,0,0,0,0;-1/1:553:0,0,0,0,0,0,0;-1/1:558:-2,-2,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:565:0,0,0,0,0,0,0;-1/1:570:-2,-2,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:582:-2,-2,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:595:0,0,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:625:0,0,0,0,0,0,0;-1/1:630:-2,-2,0,0,0,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:637:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:679:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:690:-2,-2,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:732:-2,-2,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:738:-2,-2,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:745:0,0,0,0,0,0,0;-1/1:750:-2,-2,0,0,0,0,0;-1/1:763:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:775:0,0,0,0,0,0,0;-1/1:780:-2,-2,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:787:0,0,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:805:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:847:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:870:-2,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:889:0,0,0,0,0,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:900:-2,-2,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:918:-2,-2,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:942:-2,-2,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:948:-2,-2,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:973:0,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:990:-2,-2,0,0,0,0,0;-1/1:996:-2,-2,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1020:-2,-2,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0;-1/1:1045:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck56 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 56) = operation980BoundedValue56 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 56 8
    operation980BoundedValue56 operation980BoundedValue64 operation980BoundedCheck64
  decide +kernel

compact_certificate private def operation980BoundedValue48 : Poly := laurent_polynomial% "-1/1:19:0,0,0,0,0,0,0;-1/1:30:-2,-2,0,0,0,0,0;-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:60:-2,-2,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:96:-2,-2,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:108:-2,-2,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:120:-2,-2,0,0,0,0,0;-1/1:133:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:180:-2,-2,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;-1/1:217:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:240:-2,-2,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;-1/1:259:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:270:-2,-2,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:312:-2,-2,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:318:-2,-2,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:325:0,0,0,0,0,0,0;-1/1:330:-2,-2,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:343:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:349:0,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:355:0,0,0,0,0,0,0;-1/1:360:-2,-2,0,0,0,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:378:-2,-2,0,0,0,0,0;-1/1:385:0,0,0,0,0,0,0;-1/1:390:-2,-2,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:420:-2,-2,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-1/1:427:0,0,0,0,0,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;-1/1:469:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:475:0,0,0,0,0,0,0;-1/1:480:-2,-2,0,0,0,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:498:-2,-2,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:517:0,0,0,0,0,0,0;-1/1:523:0,0,0,0,0,0,0;-1/1:535:0,0,0,0,0,0,0;-1/1:553:0,0,0,0,0,0,0;-1/1:558:-2,-2,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:565:0,0,0,0,0,0,0;-1/1:570:-2,-2,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:582:-2,-2,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:595:0,0,0,0,0,0,0;-1/1:600:-2,-2,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:625:0,0,0,0,0,0,0;-1/1:630:-2,-2,0,0,0,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:637:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:679:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:690:-2,-2,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:732:-2,-2,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:738:-2,-2,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:745:0,0,0,0,0,0,0;-1/1:750:-2,-2,0,0,0,0,0;-1/1:763:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:775:0,0,0,0,0,0,0;-1/1:780:-2,-2,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:787:0,0,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:805:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:847:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:870:-2,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:889:0,0,0,0,0,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:900:-2,-2,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:918:-2,-2,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:942:-2,-2,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:948:-2,-2,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:973:0,0,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:990:-2,-2,0,0,0,0,0;-1/1:996:-2,-2,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1002:-2,-2,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1020:-2,-2,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0;-1/1:1045:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck48 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 48) = operation980BoundedValue48 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 48 8
    operation980BoundedValue48 operation980BoundedValue56 operation980BoundedCheck56
  decide +kernel

compact_certificate private def operation980BoundedValue40 : Poly := laurent_polynomial% "-1/1:19:0,0,0,0,0,0,0;-1/1:25:0,0,0,0,0,0,0;-1/1:30:-2,-2,0,0,0,0,0;-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:60:-2,-2,0,0,0,0,0;-1/1:66:-2,-2,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:96:-2,-2,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:108:-2,-2,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:120:-2,-2,0,0,0,0,0;-1/1:133:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:180:-2,-2,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;-1/1:217:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:240:-2,-2,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;-1/1:259:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:270:-2,-2,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:312:-2,-2,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:318:-2,-2,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:325:0,0,0,0,0,0,0;-1/1:330:-2,-2,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:336:-2,-2,0,0,0,0,0;-1/1:343:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:349:0,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:355:0,0,0,0,0,0,0;-1/1:360:-2,-2,0,0,0,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:378:-2,-2,0,0,0,0,0;-1/1:385:0,0,0,0,0,0,0;-1/1:390:-2,-2,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:420:-2,-2,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-1/1:427:0,0,0,0,0,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:450:-2,-2,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;-1/1:469:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:475:0,0,0,0,0,0,0;-1/1:480:-2,-2,0,0,0,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:498:-2,-2,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:517:0,0,0,0,0,0,0;-1/1:523:0,0,0,0,0,0,0;-1/1:529:0,0,0,0,0,0,0;-1/1:535:0,0,0,0,0,0,0;-1/1:553:0,0,0,0,0,0,0;-1/1:558:-2,-2,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:565:0,0,0,0,0,0,0;-1/1:570:-2,-2,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:582:-2,-2,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:595:0,0,0,0,0,0,0;-1/1:600:-2,-2,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:625:0,0,0,0,0,0,0;-1/1:630:-2,-2,0,0,0,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:637:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:672:-2,-2,0,0,0,0,0;-1/1:679:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:690:-2,-2,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:732:-2,-2,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:738:-2,-2,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:745:0,0,0,0,0,0,0;-1/1:750:-2,-2,0,0,0,0,0;-1/1:763:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:775:0,0,0,0,0,0,0;-1/1:780:-2,-2,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:787:0,0,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:805:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:847:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:870:-2,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:889:0,0,0,0,0,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:900:-2,-2,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:918:-2,-2,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:942:-2,-2,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:948:-2,-2,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:973:0,0,0,0,0,0,0;-1/1:978:-2,-2,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:990:-2,-2,0,0,0,0,0;-1/1:996:-2,-2,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1002:-2,-2,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1020:-2,-2,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0;-1/1:1039:0,0,0,0,0,0,0;-1/1:1045:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck40 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 40) = operation980BoundedValue40 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 40 8
    operation980BoundedValue40 operation980BoundedValue48 operation980BoundedCheck48
  decide +kernel

compact_certificate private def operation980BoundedValue32 : Poly := laurent_polynomial% "-1/1:19:0,0,0,0,0,0,0;-1/1:25:0,0,0,0,0,0,0;-1/1:30:-2,-2,0,0,0,0,0;-1/1:36:-2,-2,0,0,0,0,0;-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:60:-2,-2,0,0,0,0,0;-1/1:66:-2,-2,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:72:-2,-2,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:78:-2,-2,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:96:-2,-2,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:108:-2,-2,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:120:-2,-2,0,0,0,0,0;-1/1:133:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:156:-2,-2,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:175:0,0,0,0,0,0,0;-1/1:180:-2,-2,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;-1/1:217:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:240:-2,-2,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;-1/1:252:-2,-2,0,0,0,0,0;-1/1:259:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:270:-2,-2,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:312:-2,-2,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:318:-2,-2,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:325:0,0,0,0,0,0,0;-1/1:330:-2,-2,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:336:-2,-2,0,0,0,0,0;-1/1:343:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:349:0,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:355:0,0,0,0,0,0,0;-1/1:360:-2,-2,0,0,0,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:378:-2,-2,0,0,0,0,0;-1/1:385:0,0,0,0,0,0,0;-1/1:390:-2,-2,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:420:-2,-2,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-1/1:427:0,0,0,0,0,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:450:-2,-2,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;-1/1:469:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:475:0,0,0,0,0,0,0;-1/1:480:-2,-2,0,0,0,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:492:-2,-2,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:498:-2,-2,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:517:0,0,0,0,0,0,0;-1/1:523:0,0,0,0,0,0,0;-1/1:529:0,0,0,0,0,0,0;-1/1:535:0,0,0,0,0,0,0;-1/1:553:0,0,0,0,0,0,0;-1/1:558:-2,-2,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:565:0,0,0,0,0,0,0;-1/1:570:-2,-2,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:582:-2,-2,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:595:0,0,0,0,0,0,0;-1/1:600:-2,-2,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:625:0,0,0,0,0,0,0;-1/1:630:-2,-2,0,0,0,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:637:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:672:-2,-2,0,0,0,0,0;-1/1:679:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:690:-2,-2,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:732:-2,-2,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:738:-2,-2,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:745:0,0,0,0,0,0,0;-1/1:750:-2,-2,0,0,0,0,0;-1/1:763:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:775:0,0,0,0,0,0,0;-1/1:780:-2,-2,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:787:0,0,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:798:-2,-2,0,0,0,0,0;-1/1:805:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:847:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:870:-2,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:889:0,0,0,0,0,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:900:-2,-2,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:918:-2,-2,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:942:-2,-2,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:948:-2,-2,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:973:0,0,0,0,0,0,0;-1/1:978:-2,-2,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:990:-2,-2,0,0,0,0,0;-1/1:996:-2,-2,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1002:-2,-2,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1020:-2,-2,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0;-1/1:1039:0,0,0,0,0,0,0;-1/1:1045:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck32 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 32) = operation980BoundedValue32 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 32 8
    operation980BoundedValue32 operation980BoundedValue40 operation980BoundedCheck40
  decide +kernel

compact_certificate private def operation980BoundedValue24 : Poly := laurent_polynomial% "-1/1:13:0,0,0,0,0,0,0;-1/1:18:-2,-2,0,0,0,0,0;-1/1:19:0,0,0,0,0,0,0;-1/1:25:0,0,0,0,0,0,0;-1/1:30:-2,-2,0,0,0,0,0;-1/1:36:-2,-2,0,0,0,0,0;-1/1:37:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:60:-2,-2,0,0,0,0,0;-1/1:66:-2,-2,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:72:-2,-2,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:78:-2,-2,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:96:-2,-2,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:108:-2,-2,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:120:-2,-2,0,0,0,0,0;-1/1:126:-2,-2,0,0,0,0,0;-1/1:133:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:156:-2,-2,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:175:0,0,0,0,0,0,0;-1/1:180:-2,-2,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;-1/1:217:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:240:-2,-2,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;-1/1:252:-2,-2,0,0,0,0,0;-1/1:259:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:270:-2,-2,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:312:-2,-2,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:318:-2,-2,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:325:0,0,0,0,0,0,0;-1/1:330:-2,-2,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:336:-2,-2,0,0,0,0,0;-1/1:343:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:349:0,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:355:0,0,0,0,0,0,0;-1/1:360:-2,-2,0,0,0,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:378:-2,-2,0,0,0,0,0;-1/1:385:0,0,0,0,0,0,0;-1/1:390:-2,-2,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:420:-2,-2,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-1/1:427:0,0,0,0,0,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:450:-2,-2,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;-1/1:462:-2,-2,0,0,0,0,0;-1/1:469:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:475:0,0,0,0,0,0,0;-1/1:480:-2,-2,0,0,0,0,0;-1/1:486:-2,-2,0,0,0,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:492:-2,-2,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:498:-2,-2,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:516:-2,-2,0,0,0,0,0;-1/1:517:0,0,0,0,0,0,0;-1/1:523:0,0,0,0,0,0,0;-1/1:529:0,0,0,0,0,0,0;-1/1:535:0,0,0,0,0,0,0;-1/1:553:0,0,0,0,0,0,0;-1/1:558:-2,-2,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:565:0,0,0,0,0,0,0;-1/1:570:-2,-2,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:582:-2,-2,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:588:-2,-2,0,0,0,0,0;-1/1:595:0,0,0,0,0,0,0;-1/1:600:-2,-2,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:625:0,0,0,0,0,0,0;-1/1:630:-2,-2,0,0,0,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:637:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:672:-2,-2,0,0,0,0,0;-1/1:679:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:690:-2,-2,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:732:-2,-2,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:738:-2,-2,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:745:0,0,0,0,0,0,0;-1/1:750:-2,-2,0,0,0,0,0;-1/1:763:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:775:0,0,0,0,0,0,0;-1/1:780:-2,-2,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:787:0,0,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:798:-2,-2,0,0,0,0,0;-1/1:805:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:847:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:870:-2,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:889:0,0,0,0,0,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:900:-2,-2,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:918:-2,-2,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:942:-2,-2,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:948:-2,-2,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:973:0,0,0,0,0,0,0;-1/1:978:-2,-2,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:990:-2,-2,0,0,0,0,0;-1/1:996:-2,-2,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1002:-2,-2,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1020:-2,-2,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0;-1/1:1032:-2,-2,0,0,0,0,0;-1/1:1039:0,0,0,0,0,0,0;-1/1:1045:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck24 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 24) = operation980BoundedValue24 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 24 8
    operation980BoundedValue24 operation980BoundedValue32 operation980BoundedCheck32
  decide +kernel

compact_certificate private def operation980BoundedValue16 : Poly := laurent_polynomial% "-1/1:13:0,0,0,0,0,0,0;-1/1:18:-2,-2,0,0,0,0,0;-1/1:19:0,0,0,0,0,0,0;-1/1:25:0,0,0,0,0,0,0;-1/1:30:-2,-2,0,0,0,0,0;-1/1:36:-2,-2,0,0,0,0,0;-1/1:37:0,0,0,0,0,0,0;-1/1:49:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:60:-2,-2,0,0,0,0,0;-1/1:66:-2,-2,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:72:-2,-2,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:78:-2,-2,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:96:-2,-2,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:102:-2,-2,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:108:-2,-2,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:120:-2,-2,0,0,0,0,0;-1/1:126:-2,-2,0,0,0,0,0;-1/1:133:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:150:-2,-2,0,0,0,0,0;-1/1:156:-2,-2,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:168:-2,-2,0,0,0,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:175:0,0,0,0,0,0,0;-1/1:180:-2,-2,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;-1/1:217:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:240:-2,-2,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;-1/1:252:-2,-2,0,0,0,0,0;-1/1:259:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:270:-2,-2,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:312:-2,-2,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:318:-2,-2,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:325:0,0,0,0,0,0,0;-1/1:330:-2,-2,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:336:-2,-2,0,0,0,0,0;-1/1:343:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:349:0,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:355:0,0,0,0,0,0,0;-1/1:360:-2,-2,0,0,0,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:378:-2,-2,0,0,0,0,0;-1/1:385:0,0,0,0,0,0,0;-1/1:390:-2,-2,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:420:-2,-2,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-1/1:427:0,0,0,0,0,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:450:-2,-2,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;-1/1:462:-2,-2,0,0,0,0,0;-1/1:469:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:475:0,0,0,0,0,0,0;-1/1:480:-2,-2,0,0,0,0,0;-1/1:486:-2,-2,0,0,0,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:492:-2,-2,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:498:-2,-2,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:516:-2,-2,0,0,0,0,0;-1/1:517:0,0,0,0,0,0,0;-1/1:523:0,0,0,0,0,0,0;-1/1:529:0,0,0,0,0,0,0;-1/1:535:0,0,0,0,0,0,0;-1/1:553:0,0,0,0,0,0,0;-1/1:558:-2,-2,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:565:0,0,0,0,0,0,0;-1/1:570:-2,-2,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:582:-2,-2,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:588:-2,-2,0,0,0,0,0;-1/1:595:0,0,0,0,0,0,0;-1/1:600:-2,-2,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:625:0,0,0,0,0,0,0;-1/1:630:-2,-2,0,0,0,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:637:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:672:-2,-2,0,0,0,0,0;-1/1:679:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:690:-2,-2,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:732:-2,-2,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:738:-2,-2,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:745:0,0,0,0,0,0,0;-1/1:750:-2,-2,0,0,0,0,0;-1/1:756:-2,-2,0,0,0,0,0;-1/1:763:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:775:0,0,0,0,0,0,0;-1/1:780:-2,-2,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:787:0,0,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:798:-2,-2,0,0,0,0,0;-1/1:805:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:847:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:870:-2,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:882:-2,-2,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:889:0,0,0,0,0,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:900:-2,-2,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:918:-2,-2,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:942:-2,-2,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:948:-2,-2,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:973:0,0,0,0,0,0,0;-1/1:978:-2,-2,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:990:-2,-2,0,0,0,0,0;-1/1:996:-2,-2,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1002:-2,-2,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1020:-2,-2,0,0,0,0,0;-1/1:1026:-2,-2,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0;-1/1:1032:-2,-2,0,0,0,0,0;-1/1:1033:0,0,0,0,0,0,0;-1/1:1039:0,0,0,0,0,0,0;-1/1:1045:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck16 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 16) = operation980BoundedValue16 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 16 8
    operation980BoundedValue16 operation980BoundedValue24 operation980BoundedCheck24
  decide +kernel

compact_certificate private def operation980BoundedValue8 : Poly := laurent_polynomial% "-1/1:13:0,0,0,0,0,0,0;-1/1:18:-2,-2,0,0,0,0,0;-1/1:19:0,0,0,0,0,0,0;-1/1:25:0,0,0,0,0,0,0;-1/1:30:-2,-2,0,0,0,0,0;-1/1:36:-2,-2,0,0,0,0,0;-1/1:37:0,0,0,0,0,0,0;-1/1:49:0,0,0,0,0,0,0;1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;-1/1:55:0,0,0,0,0,0,0;-1/1:60:-2,-2,0,0,0,0,0;-1/1:66:-2,-2,0,0,0,0,0;-1/1:67:0,0,0,0,0,0,0;-1/1:72:-2,-2,0,0,0,0,0;-1/1:73:0,0,0,0,0,0,0;-1/1:78:-2,-2,0,0,0,0,0;-1/1:79:0,0,0,0,0,0,0;-1/1:96:-2,-2,0,0,0,0,0;-1/1:97:0,0,0,0,0,0,0;-1/1:102:-2,-2,0,0,0,0,0;-1/1:103:0,0,0,0,0,0,0;-1/1:108:-2,-2,0,0,0,0,0;-1/1:109:0,0,0,0,0,0,0;-1/1:115:0,0,0,0,0,0,0;-1/1:120:-2,-2,0,0,0,0,0;-1/1:126:-2,-2,0,0,0,0,0;-1/1:133:0,0,0,0,0,0,0;-1/1:138:-2,-2,0,0,0,0,0;-1/1:139:0,0,0,0,0,0,0;-1/1:145:0,0,0,0,0,0,0;-1/1:150:-2,-2,0,0,0,0,0;-1/1:156:-2,-2,0,0,0,0,0;-1/1:157:0,0,0,0,0,0,0;-1/1:162:-2,-2,0,0,0,0,0;-1/1:163:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:168:-2,-2,0,0,0,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;-1/1:175:0,0,0,0,0,0,0;-1/1:180:-2,-2,0,0,0,0,0;1/1:186:-3,0,0,0,1,0,0;-1/1:186:-2,-2,0,0,0,0,0;-1/1:187:0,0,0,0,0,0,0;-1/1:192:-2,-2,0,0,0,0,0;-1/1:193:0,0,0,0,0,0,0;-1/1:198:-2,-2,0,0,0,0,0;-1/1:199:0,0,0,0,0,0,0;-1/1:205:0,0,0,0,0,0,0;-1/1:210:-2,-2,0,0,0,0,0;-1/1:217:0,0,0,0,0,0,0;-1/1:222:-2,-2,0,0,0,0,0;-1/1:223:0,0,0,0,0,0,0;-1/1:228:-2,-2,0,0,0,0,0;-1/1:229:0,0,0,0,0,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:235:0,0,0,0,0,0,0;-1/1:240:-2,-2,0,0,0,0,0;-1/1:244:-1,0,0,0,1,0,0;-1/1:246:-2,-2,0,0,0,0,0;-1/1:247:0,0,0,0,0,0,0;-1/1:252:-2,-2,0,0,0,0,0;-1/1:259:0,0,0,0,0,0,0;1/1:264:-1,0,0,0,1,0,0;-1/1:265:0,0,0,0,0,0,0;-1/1:270:-2,-2,0,0,0,0,0;-1/1:276:-2,-2,0,0,0,0,0;-1/1:277:0,0,0,0,0,0,0;1/1:278:-2,0,0,0,0,0,0;-2/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:283:0,0,0,0,0,0,0;-1/1:288:-2,-2,0,0,0,0,0;-1/1:289:0,0,0,0,0,0,0;-1/1:306:-2,-2,0,0,0,0,0;-1/1:307:0,0,0,0,0,0,0;-1/1:312:-2,-2,0,0,0,0,0;-1/1:313:0,0,0,0,0,0,0;-1/1:318:-2,-2,0,0,0,0,0;-1/1:319:0,0,0,0,0,0,0;-1/1:325:0,0,0,0,0,0,0;-1/1:330:-2,-2,0,0,0,0,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:336:-2,-2,0,0,0,0,0;-1/1:343:0,0,0,0,0,0,0;-1/1:348:-2,-2,0,0,0,0,0;-1/1:349:0,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;-1/1:355:0,0,0,0,0,0,0;-1/1:360:-2,-2,0,0,0,0,0;-1/1:366:-2,-2,0,0,0,0,0;-1/1:367:0,0,0,0,0,0,0;-1/1:372:-2,-2,0,0,0,0,0;-1/1:373:0,0,0,0,0,0,0;-1/1:378:-2,-2,0,0,0,0,0;-1/1:385:0,0,0,0,0,0,0;-1/1:390:-2,-2,0,0,0,0,0;-1/1:396:-2,-2,0,0,0,0,0;-1/1:397:0,0,0,0,0,0,0;1/1:398:-2,0,0,0,0,0,0;-1/1:403:0,0,0,0,0,0,0;-1/1:408:-2,-2,0,0,0,0,0;-1/1:409:0,0,0,0,0,0,0;-1/1:415:0,0,0,0,0,0,0;-1/1:420:-2,-2,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-1/1:427:0,0,0,0,0,0,0;-2/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;-1/1:433:0,0,0,0,0,0,0;-1/1:438:-2,-2,0,0,0,0,0;-1/1:439:0,0,0,0,0,0,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;-1/1:445:0,0,0,0,0,0,0;-1/1:450:-2,-2,0,0,0,0,0;-1/1:456:-2,-2,0,0,0,0,0;-1/1:457:0,0,0,0,0,0,0;-1/1:462:-2,-2,0,0,0,0,0;-1/1:469:0,0,0,0,0,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:475:0,0,0,0,0,0,0;-1/1:480:-2,-2,0,0,0,0,0;-1/1:486:-2,-2,0,0,0,0,0;-1/1:487:0,0,0,0,0,0,0;-1/1:492:-2,-2,0,0,0,0,0;-1/1:493:0,0,0,0,0,0,0;-1/1:498:-2,-2,0,0,0,0,0;-1/1:499:0,0,0,0,0,0,0;-1/1:516:-2,-2,0,0,0,0,0;-1/1:517:0,0,0,0,0,0,0;-1/1:522:-2,-2,0,0,0,0,0;-1/1:523:0,0,0,0,0,0,0;-1/1:529:0,0,0,0,0,0,0;-1/1:535:0,0,0,0,0,0,0;-1/1:540:-2,-2,0,0,0,0,0;-1/1:553:0,0,0,0,0,0,0;-1/1:558:-2,-2,0,0,0,0,0;-1/1:559:0,0,0,0,0,0,0;-1/1:565:0,0,0,0,0,0,0;-1/1:570:-2,-2,0,0,0,0,0;-1/1:576:-2,-2,0,0,0,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;-1/1:582:-2,-2,0,0,0,0,0;-1/1:583:0,0,0,0,0,0,0;-1/1:588:-2,-2,0,0,0,0,0;-1/1:595:0,0,0,0,0,0,0;-1/1:600:-2,-2,0,0,0,0,0;-1/1:606:-2,-2,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:607:0,0,0,0,0,0,0;-1/1:612:-2,-2,0,0,0,0,0;-1/1:613:0,0,0,0,0,0,0;-1/1:618:-2,-2,0,0,0,0,0;-1/1:618:-2,0,0,0,0,0,0;-1/1:619:0,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;-1/1:625:0,0,0,0,0,0,0;-1/1:630:-2,-2,0,0,0,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:637:0,0,0,0,0,0,0;-2/1:642:-2,-2,0,0,0,0,0;-1/1:643:0,0,0,0,0,0,0;-1/1:648:-2,-2,0,0,0,0,0;-1/1:649:0,0,0,0,0,0,0;-1/1:655:0,0,0,0,0,0,0;-1/1:660:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;-1/1:666:-2,-2,0,0,0,0,0;-1/1:667:0,0,0,0,0,0,0;-1/1:672:-2,-2,0,0,0,0,0;-1/1:679:0,0,0,0,0,0,0;-1/1:685:0,0,0,0,0,0,0;-1/1:690:-2,-2,0,0,0,0,0;-1/1:696:-2,-2,0,0,0,0,0;1/1:696:-1,-2,0,0,1,0,0;-1/1:697:0,0,0,0,0,0,0;-1/1:702:-2,-2,0,0,0,0,0;-1/1:703:0,0,0,0,0,0,0;-1/1:708:-2,-2,0,0,0,0,0;-1/1:709:0,0,0,0,0,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:726:-2,-2,0,0,0,0,0;-1/1:727:0,0,0,0,0,0,0;-1/1:732:-2,-2,0,0,0,0,0;-1/1:733:0,0,0,0,0,0,0;-1/1:738:-2,-2,0,0,0,0,0;-1/1:739:0,0,0,0,0,0,0;-1/1:745:0,0,0,0,0,0,0;-1/1:750:-2,-2,0,0,0,0,0;-1/1:756:-2,-2,0,0,0,0,0;-1/1:763:0,0,0,0,0,0,0;-1/1:768:-2,-2,0,0,0,0,0;-1/1:769:0,0,0,0,0,0,0;-1/1:775:0,0,0,0,0,0,0;-1/1:780:-2,-2,0,0,0,0,0;-1/1:786:-2,-2,0,0,0,0,0;-1/1:787:0,0,0,0,0,0,0;-1/1:792:-2,-2,0,0,0,0,0;-1/1:793:0,0,0,0,0,0,0;-1/1:798:-2,-2,0,0,0,0,0;-1/1:805:0,0,0,0,0,0,0;-1/1:810:-2,-2,0,0,0,0,0;-1/1:816:-2,-2,0,0,0,0,0;-1/1:817:0,0,0,0,0,0,0;-1/1:822:-2,-2,0,0,0,0,0;-1/1:823:0,0,0,0,0,0,0;-1/1:828:-2,-2,0,0,0,0,0;-1/1:829:0,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:835:0,0,0,0,0,0,0;-1/1:838:-2,0,0,0,0,0,0;-1/1:840:-2,-2,0,0,0,0,0;-1/1:847:0,0,0,0,0,0,0;-1/1:852:-2,-2,0,0,0,0,0;-1/1:853:0,0,0,0,0,0,0;-1/1:858:-2,-2,0,0,0,0,0;-1/1:859:0,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:865:0,0,0,0,0,0,0;-1/1:870:-2,-2,0,0,0,0,0;-1/1:876:-2,-2,0,0,0,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:877:0,0,0,0,0,0,0;-1/1:882:-2,-2,0,0,0,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;-1/1:889:0,0,0,0,0,0,0;-1/1:895:0,0,0,0,0,0,0;-1/1:900:-2,-2,0,0,0,0,0;-1/1:906:-2,-2,0,0,0,0,0;-1/1:907:0,0,0,0,0,0,0;-1/1:912:-2,-2,0,0,0,0,0;-1/1:913:0,0,0,0,0,0,0;-1/1:918:-2,-2,0,0,0,0,0;-1/1:919:0,0,0,0,0,0,0;1/1:934:-1,0,0,0,1,0,0;-1/1:936:-2,-2,0,0,0,0,0;1/1:936:-1,-2,0,0,1,0,0;-1/1:937:0,0,0,0,0,0,0;-1/1:942:-2,-2,0,0,0,0,0;-1/1:943:0,0,0,0,0,0,0;-1/1:948:-2,-2,0,0,0,0,0;-1/1:949:0,0,0,0,0,0,0;-1/1:955:0,0,0,0,0,0,0;-1/1:960:-2,-2,0,0,0,0,0;-1/1:973:0,0,0,0,0,0,0;-1/1:978:-2,-2,0,0,0,0,0;-1/1:979:0,0,0,0,0,0,0;-1/1:985:0,0,0,0,0,0,0;-1/1:990:-2,-2,0,0,0,0,0;-1/1:996:-2,-2,0,0,0,0,0;-1/1:997:0,0,0,0,0,0,0;-1/1:1002:-2,-2,0,0,0,0,0;-1/1:1003:0,0,0,0,0,0,0;-1/1:1008:-2,-2,0,0,0,0,0;-1/1:1015:0,0,0,0,0,0,0;-1/1:1020:-2,-2,0,0,0,0,0;-1/1:1026:-2,-2,0,0,0,0,0;-1/1:1027:0,0,0,0,0,0,0;-1/1:1032:-2,-2,0,0,0,0,0;-1/1:1033:0,0,0,0,0,0,0;-1/1:1038:-2,-2,0,0,0,0,0;-1/1:1039:0,0,0,0,0,0,0;-1/1:1045:0,0,0,0,0,0,0"

compact_certificate private theorem operation980BoundedCheck8 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 8) = operation980BoundedValue8 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 8 8
    operation980BoundedValue8 operation980BoundedValue16 operation980BoundedCheck16
  decide +kernel

compact_certificate private def operation980BoundedValue0 : Poly := laurent_polynomial% "1/1:52:-4,0,0,0,0,0,0;1/1:52:0,0,0,0,0,0,0;1/1:166:-3,0,0,0,1,0,0;-1/1:172:-4,0,0,0,0,0,0;1/1:174:-1,0,0,0,1,0,0;1/1:186:-3,0,0,0,1,0,0;1/1:234:-2,-1,0,0,0,1,0;1/1:234:-1,0,0,0,1,0,0;-1/1:244:-1,0,0,0,1,0,0;1/1:264:-1,0,0,0,1,0,0;1/1:278:-2,0,0,0,0,0,0;-1/1:282:-2,-2,0,0,0,0,0;-1/1:282:-1,-1,0,0,1,1,0;-1/1:332:-4,0,0,0,0,0,0;-1/1:354:-1,0,0,0,1,0,0;1/1:398:-2,0,0,0,0,0,0;1/1:402:-2,-2,0,0,0,0,0;-1/1:426:-1,-2,0,0,1,0,0;-1/1:432:-2,-2,0,0,0,0,0;-1/1:432:-1,-1,0,0,1,1,0;1/1:444:-2,-1,0,0,0,1,0;1/1:444:-1,0,0,0,1,0,0;1/1:444:1,-2,0,0,1,0,0;1/1:474:-1,0,0,0,1,0,0;-1/1:576:-1,-2,0,0,1,0,0;1/1:576:0,-1,0,0,0,1,0;1/1:576:1,0,0,0,1,0,0;1/1:577:0,0,0,0,0,0,0;-1/1:606:-1,-2,0,0,1,0,0;-1/1:618:-2,0,0,0,0,0,0;1/1:624:-3,-2,0,0,1,0,0;1/1:634:-1,0,0,0,1,0,0;-1/1:642:-2,-2,0,0,0,0,0;-1/1:664:-1,0,0,0,1,0,0;1/1:696:-1,-2,0,0,1,0,0;1/1:718:-2,0,0,0,0,0,0;-1/1:834:-2,-1,0,0,0,1,0;-1/1:838:-2,0,0,0,0,0,0;1/1:864:-2,-1,0,0,0,1,0;1/1:864:-1,0,0,0,1,0,0;-1/1:876:-1,-2,0,0,1,0,0;-1/1:884:-1,0,0,0,1,0,0;-1/1:888:-2,0,0,0,0,0,0;-1/1:888:0,-2,0,0,2,0,0;1/1:934:-1,0,0,0,1,0,0;1/1:936:-1,-2,0,0,1,0,0"

compact_certificate private theorem operation980BoundedCheck0 :
    substituteCompute (fun j => if j<4600 then source j else normal (j-4600)) ((operations 980).drop 0) = operation980BoundedValue0 := by
  apply substituteCompute_stage (fun j => if j<4600 then source j else normal (j-4600)) (operations 980) 0 8
    operation980BoundedValue0 operation980BoundedValue8 operation980BoundedCheck8
  decide +kernel

compact_certificate theorem operations_checked_30_single20 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 980)=normal 980 := by
  simp only [← substituteCompute_eq]
  exact operation980BoundedCheck0

compact_certificate theorem operations_prior_30_single20 : ∀ t ∈ operations 980,
    t.2.1<4600+980 := by decide +kernel
#print axioms operations_checked_30_single20
#print axioms operations_prior_30_single20

compact_certificate theorem operations_checked_30_single21 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 981)=normal 981 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single21 : ∀ t ∈ operations 981,
    t.2.1<4600+981 := by decide +kernel
#print axioms operations_checked_30_single21
#print axioms operations_prior_30_single21
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentEliminationCheckFamilyV4 -/
section
-- Editor-info-based tactic linting is unavailable inside compact certificates.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-! Explicit certificate statements sharing their proof procedures. -/
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 0
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_facts [
  (operations_checked_0 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+0))=normal (i.val+0)),
  (operations_checked_1 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+32))=normal (i.val+32)),
  (operations_checked_2 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+64))=normal (i.val+64)),
  (operations_checked_3 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+96))=normal (i.val+96)),
  (operations_checked_4 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+128))=normal (i.val+128)),
  (operations_checked_5 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+160))=normal (i.val+160)),
  (operations_checked_6 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+192))=normal (i.val+192)),
  (operations_checked_7 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+224))=normal (i.val+224)),
  (operations_checked_8 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+256))=normal (i.val+256)),
  (operations_checked_9 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+288))=normal (i.val+288)),
  (operations_checked_10 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+320))=normal (i.val+320)),
  (operations_checked_11 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+352))=normal (i.val+352)),
  (operations_checked_12 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+384))=normal (i.val+384)),
  (operations_checked_13 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+416))=normal (i.val+416)),
  (operations_checked_14 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+448))=normal (i.val+448)),
  (operations_checked_15 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+480))=normal (i.val+480)),
  (operations_checked_16 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+512))=normal (i.val+512)),
  (operations_checked_17 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+544))=normal (i.val+544)),
  (operations_checked_18 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+576))=normal (i.val+576)),
  (operations_checked_19 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+608))=normal (i.val+608)),
  (operations_checked_20 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+640))=normal (i.val+640)),
  (operations_checked_21 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+672))=normal (i.val+672)),
  (operations_checked_22 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+704))=normal (i.val+704)),
  (operations_checked_23 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+736))=normal (i.val+736)),
  (operations_checked_24 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+768))=normal (i.val+768)),
  (operations_checked_25 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+800))=normal (i.val+800)),
  (operations_checked_26 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+832))=normal (i.val+832)),
  (operations_checked_27 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+864))=normal (i.val+864)),
  (operations_checked_28 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+896))=normal (i.val+896)),
  (operations_checked_29 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+928))=normal (i.val+928))
] by
  simp only [← substituteCompute_eq]
  decide +kernel

compact_facts [
  (operations_prior_0 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+0), t.2.1<4600+i.val+0),
  (operations_prior_1 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+32), t.2.1<4600+i.val+32),
  (operations_prior_2 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+64), t.2.1<4600+i.val+64),
  (operations_prior_3 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+96), t.2.1<4600+i.val+96),
  (operations_prior_4 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+128), t.2.1<4600+i.val+128),
  (operations_prior_5 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+160), t.2.1<4600+i.val+160),
  (operations_prior_6 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+192), t.2.1<4600+i.val+192),
  (operations_prior_7 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+224), t.2.1<4600+i.val+224),
  (operations_prior_8 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+256), t.2.1<4600+i.val+256),
  (operations_prior_9 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+288), t.2.1<4600+i.val+288),
  (operations_prior_10 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+320), t.2.1<4600+i.val+320),
  (operations_prior_11 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+352), t.2.1<4600+i.val+352),
  (operations_prior_12 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+384), t.2.1<4600+i.val+384),
  (operations_prior_13 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+416), t.2.1<4600+i.val+416),
  (operations_prior_14 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+448), t.2.1<4600+i.val+448),
  (operations_prior_15 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+480), t.2.1<4600+i.val+480),
  (operations_prior_16 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+512), t.2.1<4600+i.val+512),
  (operations_prior_17 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+544), t.2.1<4600+i.val+544),
  (operations_prior_18 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+576), t.2.1<4600+i.val+576),
  (operations_prior_19 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+608), t.2.1<4600+i.val+608),
  (operations_prior_20 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+640), t.2.1<4600+i.val+640),
  (operations_prior_21 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+672), t.2.1<4600+i.val+672),
  (operations_prior_22 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+704), t.2.1<4600+i.val+704),
  (operations_prior_23 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+736), t.2.1<4600+i.val+736),
  (operations_prior_24 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+768), t.2.1<4600+i.val+768),
  (operations_prior_25 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+800), t.2.1<4600+i.val+800),
  (operations_prior_26 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+832), t.2.1<4600+i.val+832),
  (operations_prior_27 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+864), t.2.1<4600+i.val+864),
  (operations_prior_28 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+896), t.2.1<4600+i.val+896),
  (operations_prior_29 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+928), t.2.1<4600+i.val+928)
] by
  decide +kernel

compact_certificate theorem operations_checked_30 : ∀ i : Fin 22, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+960))=normal (i.val+960) := by
  let P : ℕ → Prop := fun i => substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations i)=normal i
  have h : ∀ i<22, P (i+960) :=
    (finite_range% P 960 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single7),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single8),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single9),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single10),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single11),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single12),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single13),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single14),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single15),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single16),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single17),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single18),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single19),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single20),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single21)
  ])
  intro i
  simpa only [Nat.add_assoc] using h i.val i.isLt
#print axioms operations_checked_30

compact_certificate theorem operations_prior_30 : ∀ i : Fin 22, ∀ t ∈ operations (i.val+960), t.2.1<4600+i.val+960 := by
  let P : ℕ → Prop := fun i => ∀ t ∈ operations i, t.2.1<4600+i
  have h : ∀ i<22, P (i+960) :=
    (finite_range% P 960 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single7),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single8),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single9),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single10),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single11),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single12),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single13),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single14),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single15),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single16),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single17),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single18),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single19),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single20),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single21)
  ])
  intro i
  simpa only [Nat.add_assoc] using h i.val i.isLt
#print axioms operations_prior_30
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentKernelCoordinatesInverseBundleV4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem coordinate_position_part0 : ∀ i : Fin 32,
    coordinate (position (i.val+0))=i.val+0 := by decide +kernel
#print axioms coordinate_position_part0

compact_certificate theorem coordinate_position_part1 : ∀ i : Fin 32,
    coordinate (position (i.val+32))=i.val+32 := by decide +kernel
#print axioms coordinate_position_part1

compact_certificate theorem coordinate_position_part2 : ∀ i : Fin 32,
    coordinate (position (i.val+64))=i.val+64 := by decide +kernel
#print axioms coordinate_position_part2

compact_certificate theorem coordinate_position_part3 : ∀ i : Fin 32,
    coordinate (position (i.val+96))=i.val+96 := by decide +kernel
#print axioms coordinate_position_part3

compact_certificate theorem coordinate_position_part4 : ∀ i : Fin 32,
    coordinate (position (i.val+128))=i.val+128 := by decide +kernel
#print axioms coordinate_position_part4

compact_certificate theorem coordinate_position_part5 : ∀ i : Fin 32,
    coordinate (position (i.val+160))=i.val+160 := by decide +kernel
#print axioms coordinate_position_part5

compact_certificate theorem coordinate_position_part6 : ∀ i : Fin 32,
    coordinate (position (i.val+192))=i.val+192 := by decide +kernel
#print axioms coordinate_position_part6

compact_certificate theorem coordinate_position_part7 : ∀ i : Fin 32,
    coordinate (position (i.val+224))=i.val+224 := by decide +kernel
#print axioms coordinate_position_part7

compact_certificate theorem coordinate_position_part8 : ∀ i : Fin 32,
    coordinate (position (i.val+256))=i.val+256 := by decide +kernel
#print axioms coordinate_position_part8

compact_certificate theorem coordinate_position_part9 : ∀ i : Fin 32,
    coordinate (position (i.val+288))=i.val+288 := by decide +kernel
#print axioms coordinate_position_part9

compact_certificate theorem coordinate_position_part10 : ∀ i : Fin 32,
    coordinate (position (i.val+320))=i.val+320 := by decide +kernel
#print axioms coordinate_position_part10

compact_certificate theorem coordinate_position_part11 : ∀ i : Fin 32,
    coordinate (position (i.val+352))=i.val+352 := by decide +kernel
#print axioms coordinate_position_part11

compact_certificate theorem coordinate_position_part12 : ∀ i : Fin 32,
    coordinate (position (i.val+384))=i.val+384 := by decide +kernel
#print axioms coordinate_position_part12

compact_certificate theorem coordinate_position_part13 : ∀ i : Fin 32,
    coordinate (position (i.val+416))=i.val+416 := by decide +kernel
#print axioms coordinate_position_part13

compact_certificate theorem coordinate_position_part14 : ∀ i : Fin 32,
    coordinate (position (i.val+448))=i.val+448 := by decide +kernel
#print axioms coordinate_position_part14

compact_certificate theorem coordinate_position_part15 : ∀ i : Fin 32,
    coordinate (position (i.val+480))=i.val+480 := by decide +kernel
#print axioms coordinate_position_part15

compact_certificate theorem coordinate_position_part16 : ∀ i : Fin 32,
    coordinate (position (i.val+512))=i.val+512 := by decide +kernel
#print axioms coordinate_position_part16

compact_certificate theorem coordinate_position_part17 : ∀ i : Fin 32,
    coordinate (position (i.val+544))=i.val+544 := by decide +kernel
#print axioms coordinate_position_part17

compact_certificate theorem coordinate_position_part18 : ∀ i : Fin 32,
    coordinate (position (i.val+576))=i.val+576 := by decide +kernel
#print axioms coordinate_position_part18

compact_certificate theorem coordinate_position_part19 : ∀ i : Fin 32,
    coordinate (position (i.val+608))=i.val+608 := by decide +kernel
#print axioms coordinate_position_part19

compact_certificate theorem coordinate_position_part20 : ∀ i : Fin 32,
    coordinate (position (i.val+640))=i.val+640 := by decide +kernel
#print axioms coordinate_position_part20

compact_certificate theorem coordinate_position_part21 : ∀ i : Fin 32,
    coordinate (position (i.val+672))=i.val+672 := by decide +kernel
#print axioms coordinate_position_part21

compact_certificate theorem coordinate_position_part22 : ∀ i : Fin 32,
    coordinate (position (i.val+704))=i.val+704 := by decide +kernel
#print axioms coordinate_position_part22

compact_certificate theorem coordinate_position_part23 : ∀ i : Fin 32,
    coordinate (position (i.val+736))=i.val+736 := by decide +kernel
#print axioms coordinate_position_part23

compact_certificate theorem coordinate_position_part24 : ∀ i : Fin 32,
    coordinate (position (i.val+768))=i.val+768 := by decide +kernel
#print axioms coordinate_position_part24

compact_certificate theorem coordinate_position_part25 : ∀ i : Fin 32,
    coordinate (position (i.val+800))=i.val+800 := by decide +kernel
#print axioms coordinate_position_part25

compact_certificate theorem coordinate_position_part26 : ∀ i : Fin 32,
    coordinate (position (i.val+832))=i.val+832 := by decide +kernel
#print axioms coordinate_position_part26

compact_certificate theorem coordinate_position_part27 : ∀ i : Fin 32,
    coordinate (position (i.val+864))=i.val+864 := by decide +kernel
#print axioms coordinate_position_part27

compact_certificate theorem coordinate_position_part28 : ∀ i : Fin 32,
    coordinate (position (i.val+896))=i.val+896 := by decide +kernel
#print axioms coordinate_position_part28

compact_certificate theorem coordinate_position_part29 : ∀ i : Fin 32,
    coordinate (position (i.val+928))=i.val+928 := by decide +kernel
#print axioms coordinate_position_part29

compact_certificate theorem coordinate_position_part30 : ∀ i : Fin 32,
    coordinate (position (i.val+960))=i.val+960 := by decide +kernel
#print axioms coordinate_position_part30

compact_certificate theorem coordinate_position_part31 : ∀ i : Fin 32,
    coordinate (position (i.val+992))=i.val+992 := by decide +kernel
#print axioms coordinate_position_part31


}
certificate_batch {
compact_certificate theorem coordinate_position_part32 : ∀ i : Fin 26,
    coordinate (position (i.val+1024))=i.val+1024 := by decide +kernel
#print axioms coordinate_position_part32

end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentTriangularCheckFamilyV4 -/
section
/-! Explicit certificate statements sharing their proof procedures. -/
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 0
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_facts [
  (triangular_checked_0 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+0),(0,0,0,0,0,0,0))] (triTail (i.val+0))=normal (i.val+0)),
  (triangular_checked_1 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+32),(0,0,0,0,0,0,0))] (triTail (i.val+32))=normal (i.val+32)),
  (triangular_checked_2 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+64),(0,0,0,0,0,0,0))] (triTail (i.val+64))=normal (i.val+64)),
  (triangular_checked_3 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+96),(0,0,0,0,0,0,0))] (triTail (i.val+96))=normal (i.val+96)),
  (triangular_checked_4 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+128),(0,0,0,0,0,0,0))] (triTail (i.val+128))=normal (i.val+128)),
  (triangular_checked_5 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+160),(0,0,0,0,0,0,0))] (triTail (i.val+160))=normal (i.val+160)),
  (triangular_checked_6 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+192),(0,0,0,0,0,0,0))] (triTail (i.val+192))=normal (i.val+192)),
  (triangular_checked_7 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+224),(0,0,0,0,0,0,0))] (triTail (i.val+224))=normal (i.val+224)),
  (triangular_checked_8 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+256),(0,0,0,0,0,0,0))] (triTail (i.val+256))=normal (i.val+256)),
  (triangular_checked_9 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+288),(0,0,0,0,0,0,0))] (triTail (i.val+288))=normal (i.val+288)),
  (triangular_checked_10 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+320),(0,0,0,0,0,0,0))] (triTail (i.val+320))=normal (i.val+320)),
  (triangular_checked_11 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+352),(0,0,0,0,0,0,0))] (triTail (i.val+352))=normal (i.val+352)),
  (triangular_checked_12 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+384),(0,0,0,0,0,0,0))] (triTail (i.val+384))=normal (i.val+384)),
  (triangular_checked_13 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+416),(0,0,0,0,0,0,0))] (triTail (i.val+416))=normal (i.val+416)),
  (triangular_checked_14 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+448),(0,0,0,0,0,0,0))] (triTail (i.val+448))=normal (i.val+448)),
  (triangular_checked_15 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+480),(0,0,0,0,0,0,0))] (triTail (i.val+480))=normal (i.val+480)),
  (triangular_checked_16 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+512),(0,0,0,0,0,0,0))] (triTail (i.val+512))=normal (i.val+512)),
  (triangular_checked_17 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+544),(0,0,0,0,0,0,0))] (triTail (i.val+544))=normal (i.val+544)),
  (triangular_checked_18 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+576),(0,0,0,0,0,0,0))] (triTail (i.val+576))=normal (i.val+576)),
  (triangular_checked_19 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+608),(0,0,0,0,0,0,0))] (triTail (i.val+608))=normal (i.val+608)),
  (triangular_checked_20 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+640),(0,0,0,0,0,0,0))] (triTail (i.val+640))=normal (i.val+640)),
  (triangular_checked_21 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+672),(0,0,0,0,0,0,0))] (triTail (i.val+672))=normal (i.val+672)),
  (triangular_checked_22 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+704),(0,0,0,0,0,0,0))] (triTail (i.val+704))=normal (i.val+704)),
  (triangular_checked_23 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+736),(0,0,0,0,0,0,0))] (triTail (i.val+736))=normal (i.val+736)),
  (triangular_checked_24 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+768),(0,0,0,0,0,0,0))] (triTail (i.val+768))=normal (i.val+768)),
  (triangular_checked_25 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+800),(0,0,0,0,0,0,0))] (triTail (i.val+800))=normal (i.val+800)),
  (triangular_checked_26 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+832),(0,0,0,0,0,0,0))] (triTail (i.val+832))=normal (i.val+832)),
  (triangular_checked_27 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+864),(0,0,0,0,0,0,0))] (triTail (i.val+864))=normal (i.val+864)),
  (triangular_checked_28 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+896),(0,0,0,0,0,0,0))] (triTail (i.val+896))=normal (i.val+896)),
  (triangular_checked_29 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+928),(0,0,0,0,0,0,0))] (triTail (i.val+928))=normal (i.val+928)),
  (triangular_checked_30 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+960),(0,0,0,0,0,0,0))] (triTail (i.val+960))=normal (i.val+960)),
  (triangular_checked_31 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+992),(0,0,0,0,0,0,0))] (triTail (i.val+992))=normal (i.val+992)),
  (triangular_checked_32 : ∀ i : Fin 26, mergeFuel 20000 [(1,coordinate (i.val+1024),(0,0,0,0,0,0,0))] (triTail (i.val+1024))=normal (i.val+1024))
] by
  simp only [← mergeCompute_eq]
  decide +kernel

compact_facts [
  (triangular_prior_0 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+0), t.2.1<1050 ∧ i.val+0<position t.2.1),
  (triangular_prior_1 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+32), t.2.1<1050 ∧ i.val+32<position t.2.1),
  (triangular_prior_2 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+64), t.2.1<1050 ∧ i.val+64<position t.2.1),
  (triangular_prior_3 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+96), t.2.1<1050 ∧ i.val+96<position t.2.1),
  (triangular_prior_4 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+128), t.2.1<1050 ∧ i.val+128<position t.2.1),
  (triangular_prior_5 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+160), t.2.1<1050 ∧ i.val+160<position t.2.1),
  (triangular_prior_6 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+192), t.2.1<1050 ∧ i.val+192<position t.2.1),
  (triangular_prior_7 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+224), t.2.1<1050 ∧ i.val+224<position t.2.1),
  (triangular_prior_8 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+256), t.2.1<1050 ∧ i.val+256<position t.2.1),
  (triangular_prior_9 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+288), t.2.1<1050 ∧ i.val+288<position t.2.1),
  (triangular_prior_10 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+320), t.2.1<1050 ∧ i.val+320<position t.2.1),
  (triangular_prior_11 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+352), t.2.1<1050 ∧ i.val+352<position t.2.1),
  (triangular_prior_12 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+384), t.2.1<1050 ∧ i.val+384<position t.2.1),
  (triangular_prior_13 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+416), t.2.1<1050 ∧ i.val+416<position t.2.1),
  (triangular_prior_14 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+448), t.2.1<1050 ∧ i.val+448<position t.2.1),
  (triangular_prior_15 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+480), t.2.1<1050 ∧ i.val+480<position t.2.1),
  (triangular_prior_16 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+512), t.2.1<1050 ∧ i.val+512<position t.2.1),
  (triangular_prior_17 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+544), t.2.1<1050 ∧ i.val+544<position t.2.1),
  (triangular_prior_18 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+576), t.2.1<1050 ∧ i.val+576<position t.2.1),
  (triangular_prior_19 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+608), t.2.1<1050 ∧ i.val+608<position t.2.1),
  (triangular_prior_20 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+640), t.2.1<1050 ∧ i.val+640<position t.2.1),
  (triangular_prior_21 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+672), t.2.1<1050 ∧ i.val+672<position t.2.1),
  (triangular_prior_22 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+704), t.2.1<1050 ∧ i.val+704<position t.2.1),
  (triangular_prior_23 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+736), t.2.1<1050 ∧ i.val+736<position t.2.1),
  (triangular_prior_24 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+768), t.2.1<1050 ∧ i.val+768<position t.2.1),
  (triangular_prior_25 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+800), t.2.1<1050 ∧ i.val+800<position t.2.1),
  (triangular_prior_26 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+832), t.2.1<1050 ∧ i.val+832<position t.2.1),
  (triangular_prior_27 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+864), t.2.1<1050 ∧ i.val+864<position t.2.1),
  (triangular_prior_28 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+896), t.2.1<1050 ∧ i.val+896<position t.2.1),
  (triangular_prior_29 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+928), t.2.1<1050 ∧ i.val+928<position t.2.1),
  (triangular_prior_30 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+960), t.2.1<1050 ∧ i.val+960<position t.2.1),
  (triangular_prior_31 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+992), t.2.1<1050 ∧ i.val+992<position t.2.1),
  (triangular_prior_32 : ∀ i : Fin 26, ∀ t ∈ triTail (i.val+1024), t.2.1<1050 ∧ i.val+1024<position t.2.1)
] by
  decide +kernel
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentTheoryV4 -/
section
/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusActualRowsV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel

compact_certificate theorem all_actual_source (j : Fin 4600) :
    normalizedPoly (rawSourcePoly (-1) (actual j.val))=source j.val := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly (-1) (actual i))=source i
  have h : ∀ i<4600, P (i+0) := (finite_range% P 0 [
    384 => actual_source_chunk0,
    384 => actual_source_chunk1,
    384 => actual_source_chunk2,
    384 => actual_source_chunk3,
    384 => actual_source_chunk4,
    384 => actual_source_chunk5,
    384 => actual_source_chunk6,
    384 => actual_source_chunk7,
    384 => actual_source_chunk8,
    384 => actual_source_chunk9,
    384 => actual_source_chunk10,
    376 => actual_source_chunk11
  ])
  exact h j.val j.isLt
#print axioms all_actual_source
compact_certificate theorem all_actual_tail (j : Fin 4600) :
    normalizedPoly (rawTailPoly (actual j.val))=tail j.val := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h : ∀ i<4600, P (i+0) := (finite_range% P 0 [
    384 => actual_tail_chunk0,
    384 => actual_tail_chunk1,
    384 => actual_tail_chunk2,
    384 => actual_tail_chunk3,
    384 => actual_tail_chunk4,
    384 => actual_tail_chunk5,
    384 => actual_tail_chunk6,
    384 => actual_tail_chunk7,
    384 => actual_tail_chunk8,
    384 => actual_tail_chunk9,
    384 => actual_tail_chunk10,
    376 => actual_tail_chunk11
  ])
  exact h j.val j.isLt
#print axioms all_actual_tail
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentBasisCertificateV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows
compact_certificate theorem all_source_zero (i : Fin 4600) : substitute basis (source i.val)=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ j<4600, P (j+0) := (finite_range% P 0 [
    32 => (fun i hi => source_zero_0 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_1 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_2 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_3 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_4 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_5 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_6 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_7 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_8 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_9 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_10 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_11 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_12 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_13 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_14 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_15 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_16 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_17 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_18 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_19 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_20 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_21 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_22 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_23 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_24 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_25 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_26 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_27 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_28 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_29 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_30 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_31 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_32 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_33 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_34 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_35 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_36 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_37 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_38 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_39 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_40 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_41 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_42 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_43 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_44 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_45 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_46 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_47 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_48 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_49 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_50 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_51 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_52 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_53 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_54 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_55 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_56 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_57 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_58 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_59 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_60 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_61 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_62 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_63 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_64 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_65 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_66 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_67 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_68 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_69 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_70 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_71 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_72 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_73 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_74 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_75 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_76 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_77 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_78 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_79 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_80 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_81 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_82 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_83 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_84 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_85 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_86 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_87 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_88 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_89 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_90 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_91 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_92 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_93 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_94 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_95 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_96 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_97 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_98 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_99 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_100 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_101 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_102 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_103 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_104 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_105 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_106 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_107 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_108 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_109 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_110 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_111 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_112 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_113 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_114 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_115 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_116 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_117 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_118 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_119 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_120 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_121 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_122 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_123 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_124 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_125 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_126 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_127 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_128 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_129 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_130 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_131 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_132 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_133 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_134 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_135 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_136 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_137 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_138 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_139 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_140 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_141 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_142 ⟨i,hi⟩),
    24 => (fun i hi => source_zero_143 ⟨i,hi⟩)
  ])
  simpa only [Nat.add_zero] using h i.val i.isLt

compact_certificate theorem eval_source_zero (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (i : Fin 4600) :
    eval x y z w a b c (fun j => eval x y z w a b c v (basis j)) (source i.val)=0 :=
  substitution_zero x y z w a b c v hx hy hz hw basis (source i.val) (all_source_zero i)
#print axioms all_source_zero
#print axioms eval_source_zero
compact_certificate theorem all_tail_zero (i : Fin 4600) : substitute basis (tail i.val)=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ j<4600, P (j+0) := (finite_range% P 0 [
    32 => (fun i hi => tail_zero_0 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_1 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_2 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_3 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_4 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_5 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_6 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_7 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_8 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_9 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_10 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_11 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_12 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_13 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_14 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_15 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_16 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_17 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_18 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_19 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_20 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_21 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_22 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_23 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_24 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_25 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_26 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_27 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_28 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_29 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_30 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_31 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_32 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_33 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_34 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_35 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_36 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_37 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_38 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_39 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_40 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_41 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_42 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_43 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_44 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_45 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_46 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_47 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_48 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_49 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_50 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_51 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_52 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_53 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_54 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_55 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_56 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_57 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_58 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_59 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_60 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_61 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_62 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_63 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_64 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_65 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_66 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_67 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_68 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_69 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_70 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_71 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_72 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_73 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_74 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_75 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_76 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_77 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_78 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_79 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_80 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_81 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_82 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_83 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_84 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_85 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_86 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_87 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_88 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_89 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_90 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_91 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_92 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_93 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_94 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_95 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_96 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_97 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_98 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_99 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_100 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_101 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_102 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_103 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_104 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_105 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_106 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_107 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_108 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_109 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_110 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_111 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_112 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_113 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_114 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_115 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_116 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_117 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_118 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_119 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_120 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_121 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_122 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_123 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_124 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_125 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_126 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_127 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_128 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_129 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_130 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_131 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_132 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_133 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_134 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_135 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_136 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_137 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_138 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_139 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_140 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_141 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_142 ⟨i,hi⟩),
    24 => (fun i hi => tail_zero_143 ⟨i,hi⟩)
  ])
  simpa only [Nat.add_zero] using h i.val i.isLt

compact_certificate theorem eval_tail_zero (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (i : Fin 4600) :
    eval x y z w a b c (fun j => eval x y z w a b c v (basis j)) (tail i.val)=0 :=
  substitution_zero x y z w a b c v hx hy hz hw basis (tail i.val) (all_tail_zero i)
#print axioms all_tail_zero
#print axioms eval_tail_zero
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentKernelOperationsV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem all_operations_checked : ∀ i<982, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations i)=normal i := by
  let P : ℕ → Prop := fun i => substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations i)=normal i
  have h : ∀ i<982, P (i+0) :=
    (finite_range% P 0 [
    32 => (fun i hi => operations_checked_0 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_1 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_2 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_3 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_4 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_5 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_6 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_7 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_8 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_9 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_10 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_11 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_12 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_13 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_14 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_15 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_16 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_17 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_18 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_19 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_20 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_21 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_22 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_23 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_24 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_25 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_26 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_27 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_28 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_29 ⟨i,hi⟩),
    22 => (fun i hi => operations_checked_30 ⟨i,hi⟩)
  ])
  simpa only [Nat.add_zero] using h


#print axioms all_operations_checked
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentKernelPriorV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem all_operations_prior : ∀ i<982, ∀ t ∈ operations i, t.2.1<4600+i := by
  let P : ℕ → Prop := fun i => ∀ t ∈ operations i, t.2.1<4600+i
  have h : ∀ i<982, P (i+0) :=
    (finite_range% P 0 [
    32 => (fun i hi => operations_prior_0 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_1 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_2 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_3 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_4 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_5 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_6 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_7 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_8 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_9 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_10 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_11 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_12 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_13 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_14 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_15 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_16 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_17 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_18 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_19 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_20 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_21 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_22 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_23 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_24 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_25 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_26 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_27 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_28 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_29 ⟨i,hi⟩),
    22 => (fun i hi => operations_prior_30 ⟨i,hi⟩)
  ])
  simpa only [Nat.add_zero] using h


#print axioms all_operations_prior
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentKernelTriangularV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem all_triangular_checked : ∀ i<1050, mergeFuel 20000 [(1,coordinate i,(0,0,0,0,0,0,0))] (triTail i)=normal i := by
  let P : ℕ → Prop := fun i => mergeFuel 20000 [(1,coordinate i,(0,0,0,0,0,0,0))] (triTail i)=normal i
  have h : ∀ i<1050, P (i+0) :=
    (finite_range% P 0 [
    32 => (fun i hi => triangular_checked_0 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_1 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_2 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_3 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_4 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_5 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_6 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_7 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_8 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_9 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_10 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_11 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_12 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_13 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_14 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_15 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_16 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_17 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_18 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_19 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_20 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_21 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_22 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_23 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_24 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_25 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_26 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_27 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_28 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_29 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_30 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_31 ⟨i,hi⟩),
    26 => (fun i hi => triangular_checked_32 ⟨i,hi⟩)
  ])
  simpa only [Nat.add_zero] using h


#print axioms all_triangular_checked
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentKernelTriangularPriorV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem all_triangular_prior : ∀ i<1050, ∀ t ∈ triTail i, t.2.1<1050 ∧ i<position t.2.1 := by
  let P : ℕ → Prop := fun i => ∀ t ∈ triTail i, t.2.1<1050 ∧ i<position t.2.1
  have h : ∀ i<1050, P (i+0) :=
    (finite_range% P 0 [
    32 => (fun i hi => triangular_prior_0 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_1 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_2 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_3 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_4 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_5 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_6 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_7 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_8 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_9 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_10 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_11 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_12 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_13 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_14 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_15 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_16 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_17 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_18 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_19 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_20 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_21 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_22 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_23 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_24 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_25 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_26 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_27 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_28 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_29 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_30 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_31 ⟨i,hi⟩),
    26 => (fun i hi => triangular_prior_32 ⟨i,hi⟩)
  ])
  simpa only [Nat.add_zero] using h


#print axioms all_triangular_prior
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentKernelCoordinatesBoundV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem coordinate_bound : ∀ i : Fin 1050, coordinate i.val<1050 := by
  have h : ∀ x∈coordinates, x<1050 := by decide +kernel
  intro i
  exact QuantitativeArithmeticListBounds.getD_of_forall (fun x : ℕ => x<1050) 0
    (by decide) coordinates h i.val

#print axioms coordinate_bound
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentKernelPositionsBoundV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem position_bound : ∀ i : Fin 1050, position i.val<1050 := by
  have h : ∀ x∈positions, x<1050 := by decide +kernel
  intro i
  exact QuantitativeArithmeticListBounds.getD_of_forall (fun x : ℕ => x<1050) 0
    (by decide) positions h i.val

#print axioms position_bound
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentKernelCoordinatesInverseV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem coordinate_position : ∀ i : Fin 1050, coordinate (position i.val)=i.val := by
  let P : ℕ → Prop := fun i => coordinate (position i)=i
  have h : ∀ i<1050, P (i+0) := (finite_range% P 0 [
    32 => (fun i hi => coordinate_position_part0 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part1 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part2 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part3 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part4 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part5 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part6 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part7 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part8 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part9 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part10 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part11 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part12 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part13 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part14 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part15 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part16 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part17 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part18 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part19 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part20 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part21 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part22 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part23 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part24 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part25 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part26 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part27 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part28 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part29 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part30 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part31 ⟨i,hi⟩),
    26 => (fun i hi => coordinate_position_part32 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms coordinate_position
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentKernelFreeRowsV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem free_rows : ∀ i : Fin 68,
    normal (i.val+982)=[(1,coordinate (i.val+982),(0,0,0,0,0,0,0))] := by decide +kernel


#print axioms free_rows
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentKernelCertificateV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem augmented_kernel (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (hs : ∀ j<4600, eval x y z w a b c v (source j)=0)
    (hf : ∀ j : Fin 68, v (coordinate (j.val+982))=0) :
    ∀ j<1050, v j=0 := by
  have hn := forward_elimination x y z w a b c v hx hy hz hw 4600 982
    source normal operations all_operations_checked all_operations_prior hs
  have hnormal : ∀ i<1050, eval x y z w a b c v (normal i)=0 := by
    intro i hi
    by_cases h : i<982
    · exact hn i h
    · have he : i-982+982=i := by omega
      have hh := free_rows ⟨i-982,by omega⟩
      dsimp only at hh
      rw [he] at hh
      rw [hh]
      simpa [eval,monomial,he] using hf ⟨i-982,by omega⟩
  have ht : ∀ i : Fin 1050, v (coordinate i.val)+eval x y z w a b c v (triTail i.val)=0 := by
    intro i
    have hh := hnormal i.val i.isLt
    rw [← all_triangular_checked i.val i.isLt,eval_mergeFuel] at hh
    simpa [eval,monomial] using hh
  have hzall := triangular_kernel x y z w a b c v 1050
    (fun i => coordinate i.val) (fun i => triTail i.val) ht (by
      intro i t ht
      obtain ⟨hbound,higher⟩ := all_triangular_prior i.val i.isLt t ht
      refine ⟨⟨position t.2.1,position_bound ⟨t.2.1,hbound⟩⟩,higher,?_⟩
      exact (coordinate_position ⟨t.2.1,hbound⟩).symm)
  intro j hj
  have hh := hzall ⟨position j,position_bound ⟨j,hj⟩⟩
  simpa only [coordinate_position ⟨j,hj⟩] using hh
#print axioms augmented_kernel
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentGaugeCoordinatesV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem basis_free_coordinate : ∀ i : Fin 68,
    basis (coordinate (i.val+982))=[(1,i.val,(0,0,0,0,0,0,0))] := by decide +kernel

compact_certificate theorem basis_old_coordinate : ∀ i : Fin 150, basis (7*i.val)=[] := by decide +kernel

#print axioms basis_free_coordinate
#print axioms basis_old_coordinate
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
open Complex QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid

compact_certificate def freeCoordinate (j : Fin 68) : Fin 1050 :=
  ⟨coordinate (j.val+982),coordinate_bound ⟨j.val+982,by omega⟩⟩

compact_certificate theorem actual_augmented_kernel {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε s : ℂ) (hχ : ε*I^(2*m)=(-1)) (v : Fin 1050 → ℂ)
    (hs : ∀ i : Fin 4600, sourceLeading (actual i.val) m f ε s v=0)
    (hfree : ∀ j : Fin 68, v (freeCoordinate j)=0) : v=0 := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p m s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  have phase : ε*I^(2*m)=(((-1):ℚ):ℂ) := by simpa using hχ
  have hk := augmented_kernel (primeParameter 2 m s) (primeParameter 3 m s)
    (primeParameter 5 m s) (primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7)
    (periodicVector v) (hp 2 (by decide)) (hp 3 (by decide)) (hp 5 (by decide)) (hp 7 (by decide))
    (by
      intro i hi
      have he := eval_rawSourcePoly (actual i) hf ε s ((-1):ℚ) phase v
      rw [← eval_normalizedPoly _ _ _ _ _ _ _ _ (hp 2 (by decide)) (hp 3 (by decide))
        (hp 5 (by decide)) (hp 7 (by decide)),all_actual_source ⟨i,hi⟩] at he
      exact he.trans (hs ⟨i,hi⟩))
    (by
      intro j
      change periodicVector v (freeCoordinate j).val=0
      rw [periodicVector_fin]
      exact hfree j)
  funext j
  simpa only [periodicVector_fin, Pi.zero_apply] using hk j.val j.isLt

/- Auxiliary continuation from the original Euler/Fricke input and the
already continued 150-grid; the free auxiliary twists are not continued. -/
compact_certificate theorem original_auxiliary_continuation {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=(-1))
    (BG : ℝ) (G0 : ℂ → Fin 150 → ℂ)
    (hG0 : ∀ j z, MeromorphicAt (fun w => G0 w j) z)
    (hG0F : ∀ z, BG<z.re → G0 z=QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords.gridVector (2*m) f z) :
    ∃ (B : ℝ) (G : ℂ → Fin 1050 → ℂ),
      (∀ j z, MeromorphicNFAt (fun w => G w j) z) ∧
      (∀ z, B<z.re → G z=physicalGauge basis freeCoordinate m f z (gridVector 1050 (2*m) f z)) ∧
      ∀ z, B<z.re → ∀ j : Fin 150, G z ⟨7*j.val,by omega⟩=
        QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords.gridVector (2*m) f z j := by
  apply quotient_continuation_of_certificates (fun i : Fin 4600 => actual i.val)
    freeCoordinate basis (fun i => source i.val) (fun i => tail i.val) ((-1):ℚ)
    basis_periodic (fun j => basis_free_coordinate j) basis_old_coordinate
    all_actual_source all_actual_tail all_source_zero all_tail_zero
    hm hf ε hε hlaw (by simpa using hχ)
    (fun s v hs hfree => actual_augmented_kernel hf ε s hχ v hs hfree)
    BG G0 hG0 hG0F

#print axioms actual_augmented_kernel
#print axioms original_auxiliary_continuation
end QuantitativeArithmeticSmallLevelTwentyFive.AuxMinusLaurent
end
end
end

}
