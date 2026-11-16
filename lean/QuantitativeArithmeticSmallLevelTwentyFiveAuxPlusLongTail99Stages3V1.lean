module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusRow99Stages0V1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusRow99Stages1V1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusRow99Stages2V1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusRow99Stages3V1
public meta import SmallLevelCertificateBatchCommandV1
public meta import SmallLevelLaurentPolynomialLiteralV1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusActualAssemblyChapterV1

public import QuantitativeArithmeticFiniteRangeCertificatesV1
public import QuantitativeArithmeticListBoundsV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridDataTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModelTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxSymbolicRowsV1
public meta import QuantitativeArithmeticCompactCommandsV1
public meta import QuantitativeArithmeticCompactFactCommandsV1
public meta import QuantitativeArithmeticFiniteRangeCommandsV4

-- These editor-information linters are incompatible with compact_certificate.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent. Original declarations and local scopes are retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows
certificate_batch {
compact_certificate private theorem boundedLongTail3199Check120 : substituteCompute basis ((tail 3199).drop 120)=[] := by
  decide +kernel

compact_certificate private def boundedLongTail3199Value112 : Poly := laurent_polynomial% ""

compact_certificate private theorem boundedLongTail3199Check112 : substituteCompute basis ((tail 3199).drop 112)=boundedLongTail3199Value112 := by
  apply substituteCompute_stage basis (tail 3199) 112 8 boundedLongTail3199Value112 [] boundedLongTail3199Check120
  decide +kernel

compact_certificate private def boundedLongTail3199Value104 : Poly := laurent_polynomial% ""

compact_certificate private theorem boundedLongTail3199Check104 : substituteCompute basis ((tail 3199).drop 104)=boundedLongTail3199Value104 := by
  apply substituteCompute_stage basis (tail 3199) 104 8 boundedLongTail3199Value104 boundedLongTail3199Value112 boundedLongTail3199Check112
  decide +kernel

compact_certificate private def boundedLongTail3199Value96 : Poly := laurent_polynomial% "-1/1:5:0,0,0,0,0,0,0;1/1:8:-3,0,0,0,1,0,0;-1/1:8:-1,0,0,0,1,0,0;-1/1:9:-1,0,0,0,1,0,0;-1/1:14:-2,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;-1/1:16:-2,0,0,0,0,0,0;1/1:16:0,0,0,0,0,0,0;-1/1:17:-4,0,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;1/1:17:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;-1/1:45:-2,0,0,0,0,0,0;1/1:45:0,0,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;-1/1:50:-2,0,0,0,0,0,0;1/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;-1/1:59:-1,0,0,0,1,0,0;1/1:61:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3199Check96 : substituteCompute basis ((tail 3199).drop 96)=boundedLongTail3199Value96 := by
  apply substituteCompute_stage basis (tail 3199) 96 8 boundedLongTail3199Value96 boundedLongTail3199Value104 boundedLongTail3199Check104
  decide +kernel

compact_certificate private def boundedLongTail3199Value88 : Poly := laurent_polynomial% "-1/1:5:-2,0,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;-1/1:5:1,0,0,0,1,0,0;1/1:8:-3,0,0,0,1,0,0;-2/1:8:-1,0,0,0,1,0,0;-1/1:8:0,0,0,0,0,0,0;-2/1:9:-1,0,0,0,1,0,0;1/1:11:0,0,0,0,0,0,0;-1/1:14:-2,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;-1/1:16:-2,0,0,0,0,0,0;2/1:16:0,0,0,0,0,0,0;-1/1:17:-4,0,0,0,0,0,0;2/1:17:-2,0,0,0,0,0,0;2/1:17:0,0,0,0,0,0,0;-1/1:18:0,0,0,0,0,0,0;-1/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;1/1:26:0,0,0,0,0,0,0;-1/1:27:0,0,0,0,0,0,0;1/1:29:2,0,0,0,0,0,0;1/1:32:2,0,0,0,0,0,0;-1/1:33:0,0,0,0,0,0,0;1/1:36:0,0,0,0,0,0,0;1/1:38:0,0,0,0,0,0,0;-1/1:45:-2,0,0,0,0,0,0;1/1:45:0,0,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;-2/1:50:-2,0,0,0,0,0,0;2/1:50:0,0,0,0,0,0,0;1/1:54:0,0,0,0,0,0,0;2/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;-1/1:59:-1,0,0,0,1,0,0;1/1:61:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3199Check88 : substituteCompute basis ((tail 3199).drop 88)=boundedLongTail3199Value88 := by
  apply substituteCompute_stage basis (tail 3199) 88 8 boundedLongTail3199Value88 boundedLongTail3199Value96 boundedLongTail3199Check96
  decide +kernel

compact_certificate private def boundedLongTail3199Value80 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;-2/1:8:-1,0,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-1/1:8:0,0,0,0,0,0,0;1/1:9:-1,0,0,0,1,0,0;-1/1:11:0,-1,0,0,0,1,0;1/1:11:0,0,0,0,0,0,0;1/1:12:0,0,0,0,0,0,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:16:0,0,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;2/1:17:-2,0,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-1/1:18:0,0,0,0,0,0,0;-1/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:26:0,0,0,0,0,0,0;1/1:27:0,-1,0,0,0,1,0;-1/1:27:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;2/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;1/1:36:0,0,0,0,0,0,0;1/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;2/1:45:0,0,0,0,0,0,0;1/1:50:-2,0,0,0,0,0,0;2/1:50:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;3/1:58:0,0,0,0,0,0,0;1/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3199Check80 : substituteCompute basis ((tail 3199).drop 80)=boundedLongTail3199Value80 := by
  apply substituteCompute_stage basis (tail 3199) 80 8 boundedLongTail3199Value80 boundedLongTail3199Value88 boundedLongTail3199Check88
  decide +kernel

compact_certificate private def boundedLongTail3199Value72 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;-1/1:8:-1,0,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-1/1:8:0,0,0,0,0,0,0;1/1:9:-1,0,0,0,1,0,0;-1/1:11:0,-1,0,0,0,1,0;1/1:12:0,0,0,0,0,0,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;-1/1:14:0,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-1/1:18:0,0,0,0,0,0,0;-1/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:27:0,-1,0,0,0,1,0;-1/1:27:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;2/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;1/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;1/1:45:0,0,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;-1/1:46:0,0,0,0,0,0,0;1/1:50:-2,0,0,0,0,0,0;2/1:50:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;2/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3199Check72 : substituteCompute basis ((tail 3199).drop 72)=boundedLongTail3199Value72 := by
  apply substituteCompute_stage basis (tail 3199) 72 8 boundedLongTail3199Value72 boundedLongTail3199Value80 boundedLongTail3199Check80
  decide +kernel

compact_certificate private def boundedLongTail3199Value64 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;1/1:5:-2,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;2/1:9:-1,0,0,0,1,0,0;-1/1:11:0,-1,0,0,0,1,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;-1/1:14:0,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-1/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;-1/1:26:0,0,0,0,0,0,0;1/1:27:0,-1,0,0,0,1,0;-2/1:27:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-1/1:33:0,0,0,0,0,0,0;1/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;1/1:45:0,0,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;-1/1:46:0,0,0,0,0,0,0;2/1:50:-2,0,0,0,0,0,0;2/1:50:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:54:0,0,0,0,0,0,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3199Check64 : substituteCompute basis ((tail 3199).drop 64)=boundedLongTail3199Value64 := by
  apply substituteCompute_stage basis (tail 3199) 64 8 boundedLongTail3199Value64 boundedLongTail3199Value72 boundedLongTail3199Check72
  decide +kernel

compact_certificate private def boundedLongTail3199Value56 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;1/1:5:-2,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;2/1:9:-1,0,0,0,1,0,0;-1/1:11:0,-1,0,0,0,1,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;-1/1:14:0,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-1/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;-1/1:26:0,0,0,0,0,0,0;1/1:27:0,-1,0,0,0,1,0;-2/1:27:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-1/1:33:0,0,0,0,0,0,0;1/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;1/1:45:0,0,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;-1/1:46:0,0,0,0,0,0,0;2/1:50:-2,0,0,0,0,0,0;2/1:50:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:54:0,0,0,0,0,0,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3199Check56 : substituteCompute basis ((tail 3199).drop 56)=boundedLongTail3199Value56 := by
  apply substituteCompute_stage basis (tail 3199) 56 8 boundedLongTail3199Value56 boundedLongTail3199Value64 boundedLongTail3199Check64
  decide +kernel

compact_certificate private def boundedLongTail3199Value48 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-2/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;2/1:9:-1,0,0,0,1,0,0;-1/1:11:0,-1,0,0,0,1,0;-1/1:13:0,0,0,0,0,0,0;2/1:14:-2,0,0,0,0,0,0;-1/1:14:0,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;2/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;2/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-1/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:27:0,-1,0,0,0,1,0;-2/1:27:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-1/1:33:0,0,0,0,0,0,0;1/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;2/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;1/1:45:0,0,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;-1/1:46:0,0,0,0,0,0,0;2/1:50:-2,0,0,0,0,0,0;2/1:50:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:54:0,0,0,0,0,0,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;2/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3199Check48 : substituteCompute basis ((tail 3199).drop 48)=boundedLongTail3199Value48 := by
  apply substituteCompute_stage basis (tail 3199) 48 8 boundedLongTail3199Value48 boundedLongTail3199Value56 boundedLongTail3199Check56
  decide +kernel

compact_certificate private def boundedLongTail3199Value40 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-2/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;2/1:9:-1,0,0,0,1,0,0;-1/1:11:0,-1,0,0,0,1,0;-1/1:11:0,0,0,0,0,0,0;1/1:12:0,0,0,0,0,0,0;-1/1:13:0,0,0,0,0,0,0;2/1:14:-2,0,0,0,0,0,0;-1/1:14:0,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;2/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;2/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;1/1:18:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:27:0,-1,0,0,0,1,0;-1/1:27:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;2/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;1/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;2/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;1/1:45:0,0,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;-1/1:46:0,0,0,0,0,0,0;2/1:50:-2,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;-1/1:54:0,0,0,0,0,0,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;2/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3199Check40 : substituteCompute basis ((tail 3199).drop 40)=boundedLongTail3199Value40 := by
  apply substituteCompute_stage basis (tail 3199) 40 8 boundedLongTail3199Value40 boundedLongTail3199Value48 boundedLongTail3199Check48
  decide +kernel

compact_certificate private def boundedLongTail3199Value32 : Poly := laurent_polynomial% "-1/1:5:-2,0,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;-1/1:5:1,0,0,0,1,0,0;-2/1:8:0,0,0,0,0,0,0;-1/1:9:-1,0,0,0,1,0,0;-1/1:11:0,0,0,0,0,0,0;1/1:12:0,0,0,0,0,0,0;-1/1:14:0,0,0,0,0,0,0;2/1:14:2,0,0,0,0,0,0;1/1:16:0,0,0,0,0,0,0;2/1:17:0,0,0,0,0,0,0;1/1:18:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;-1/1:27:0,0,0,0,0,0,0;2/1:29:2,0,0,0,0,0,0;1/1:32:2,0,0,0,0,0,0;-2/1:33:0,0,0,0,0,0,0;1/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;2/1:45:2,0,0,0,0,0,0;-1/1:46:0,0,0,0,0,0,0;-1/1:50:-2,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;-1/1:54:0,0,0,0,0,0,0;1/1:58:0,0,0,0,0,0,0;2/1:58:1,0,0,0,1,0,0;1/1:61:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3199Check32 : substituteCompute basis ((tail 3199).drop 32)=boundedLongTail3199Value32 := by
  apply substituteCompute_stage basis (tail 3199) 32 8 boundedLongTail3199Value32 boundedLongTail3199Value40 boundedLongTail3199Check40
  decide +kernel

compact_certificate private def boundedLongTail3199Value24 : Poly := laurent_polynomial% "-1/1:5:0,0,0,0,0,0,0;-1/1:5:1,0,0,0,1,0,0;-2/1:8:0,0,0,0,0,0,0;1/1:12:0,0,0,0,0,0,0;1/1:16:0,0,0,0,0,0,0;1/1:17:0,0,0,0,0,0,0;1/1:18:0,0,0,0,0,0,0;-1/1:27:0,0,0,0,0,0,0;2/1:29:2,0,0,0,0,0,0;1/1:32:2,0,0,0,0,0,0;-2/1:33:0,0,0,0,0,0,0;1/1:36:0,0,0,0,0,0,0;1/1:38:0,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;-1/1:54:0,0,0,0,0,0,0;1/1:58:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3199Check24 : substituteCompute basis ((tail 3199).drop 24)=boundedLongTail3199Value24 := by
  apply substituteCompute_stage basis (tail 3199) 24 8 boundedLongTail3199Value24 boundedLongTail3199Value32 boundedLongTail3199Check32
  decide +kernel

compact_certificate private def boundedLongTail3199Value16 : Poly := laurent_polynomial% "1/1:12:0,0,0,0,0,0,0;1/1:29:2,0,0,0,0,0,0;-1/1:33:0,0,0,0,0,0,0;-1/1:54:0,0,0,0,0,0,0;1/1:58:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3199Check16 : substituteCompute basis ((tail 3199).drop 16)=boundedLongTail3199Value16 := by
  apply substituteCompute_stage basis (tail 3199) 16 8 boundedLongTail3199Value16 boundedLongTail3199Value24 boundedLongTail3199Check24
  decide +kernel

compact_certificate private def boundedLongTail3199Value8 : Poly := laurent_polynomial% ""

compact_certificate private theorem boundedLongTail3199Check8 : substituteCompute basis ((tail 3199).drop 8)=boundedLongTail3199Value8 := by
  apply substituteCompute_stage basis (tail 3199) 8 8 boundedLongTail3199Value8 boundedLongTail3199Value16 boundedLongTail3199Check16
  decide +kernel

compact_certificate private def boundedLongTail3199Value0 : Poly := laurent_polynomial% ""

compact_certificate private theorem boundedLongTail3199Check0 : substituteCompute basis ((tail 3199).drop 0)=boundedLongTail3199Value0 := by
  apply substituteCompute_stage basis (tail 3199) 0 8 boundedLongTail3199Value0 boundedLongTail3199Value8 boundedLongTail3199Check8
  decide +kernel

compact_certificate theorem boundedLongTail3199Done : substitute basis (tail 3199)=[] := by
  simpa only [← substituteCompute_eq, List.drop_zero, boundedLongTail3199Value0] using boundedLongTail3199Check0
}
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
