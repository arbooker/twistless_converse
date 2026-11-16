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
compact_certificate private theorem boundedLongTail3173Check120 : substituteCompute basis ((tail 3173).drop 120)=[] := by
  decide +kernel

compact_certificate private def boundedLongTail3173Value112 : Poly := laurent_polynomial% ""

compact_certificate private theorem boundedLongTail3173Check112 : substituteCompute basis ((tail 3173).drop 112)=boundedLongTail3173Value112 := by
  apply substituteCompute_stage basis (tail 3173) 112 8 boundedLongTail3173Value112 [] boundedLongTail3173Check120
  decide +kernel

compact_certificate private def boundedLongTail3173Value104 : Poly := laurent_polynomial% "-1/1:5:0,0,0,0,0,0,0;-1/1:8:-1,0,0,0,1,0,0;-1/1:9:0,0,0,0,0,0,0;1/1:10:0,0,0,0,0,0,0;1/1:16:0,0,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;1/1:25:0,0,0,0,0,0,0;-1/1:27:2,0,0,0,0,0,0;1/1:45:0,0,0,0,0,0,0;-1/1:49:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3173Check104 : substituteCompute basis ((tail 3173).drop 104)=boundedLongTail3173Value104 := by
  apply substituteCompute_stage basis (tail 3173) 104 8 boundedLongTail3173Value104 boundedLongTail3173Value112 boundedLongTail3173Check112
  decide +kernel

compact_certificate private def boundedLongTail3173Value96 : Poly := laurent_polynomial% "-2/1:5:0,0,0,0,0,0,0;1/1:8:-3,0,0,0,1,0,0;-2/1:8:-1,0,0,0,1,0,0;-1/1:9:-1,0,0,0,1,0,0;-1/1:9:0,0,0,0,0,0,0;1/1:10:0,0,0,0,0,0,0;-1/1:14:-2,0,0,0,0,0,0;1/1:14:0,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;-1/1:16:-2,0,0,0,0,0,0;2/1:16:0,0,0,0,0,0,0;-1/1:17:-4,0,0,0,0,0,0;2/1:17:-2,0,0,0,0,0,0;1/1:17:0,0,0,0,0,0,0;-1/1:22:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;2/1:25:0,0,0,0,0,0,0;-1/1:26:2,0,0,0,0,0,0;-1/1:27:2,0,0,0,0,0,0;1/1:29:0,0,0,0,0,0,0;-1/1:41:0,0,0,0,0,0,0;-1/1:45:-2,0,0,0,0,0,0;2/1:45:0,0,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;-1/1:49:0,0,0,0,0,0,0;-1/1:50:-2,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;-1/1:59:-1,0,0,0,1,0,0;2/1:59:0,0,0,0,0,0,0;1/1:61:1,0,0,0,1,0,0"

compact_certificate private theorem boundedLongTail3173Check96 : substituteCompute basis ((tail 3173).drop 96)=boundedLongTail3173Value96 := by
  apply substituteCompute_stage basis (tail 3173) 96 8 boundedLongTail3173Value96 boundedLongTail3173Value104 boundedLongTail3173Check104
  decide +kernel

compact_certificate private def boundedLongTail3173Value88 : Poly := laurent_polynomial% "-1/1:5:-2,0,0,0,0,0,0;-2/1:5:0,0,0,0,0,0,0;1/1:8:-3,0,0,0,1,0,0;-3/1:8:-1,0,0,0,1,0,0;-2/1:9:-1,0,0,0,1,0,0;-2/1:9:0,0,0,0,0,0,0;1/1:10:0,0,0,0,0,0,0;-1/1:14:-2,0,0,0,0,0,0;1/1:14:0,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;-1/1:16:-2,0,0,0,0,0,0;3/1:16:0,0,0,0,0,0,0;-1/1:17:-4,0,0,0,0,0,0;3/1:17:-2,0,0,0,0,0,0;2/1:17:0,0,0,0,0,0,0;-1/1:21:0,0,0,0,0,0,0;-2/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;2/1:25:0,0,0,0,0,0,0;-1/1:26:2,0,0,0,0,0,0;-1/1:27:2,0,0,0,0,0,0;1/1:29:0,0,0,0,0,0,0;-1/1:32:0,0,0,0,0,0,0;1/1:36:0,0,0,0,0,0,0;1/1:38:0,0,0,0,0,0,0;-1/1:41:0,0,0,0,0,0,0;-1/1:45:-2,0,0,0,0,0,0;2/1:45:0,0,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;1/1:46:0,0,0,0,0,0,0;-2/1:50:-2,0,0,0,0,0,0;2/1:50:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;-1/1:59:-1,0,0,0,1,0,0;2/1:59:0,0,0,0,0,0,0;1/1:61:1,0,0,0,1,0,0"

compact_certificate private theorem boundedLongTail3173Check88 : substituteCompute basis ((tail 3173).drop 88)=boundedLongTail3173Value88 := by
  apply substituteCompute_stage basis (tail 3173) 88 8 boundedLongTail3173Value88 boundedLongTail3173Value96 boundedLongTail3173Check96
  decide +kernel

compact_certificate private def boundedLongTail3173Value80 : Poly := laurent_polynomial% "-2/1:1:-2,0,0,0,0,0,0;-2/1:2:0,0,0,0,0,0,0;2/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;2/1:7:-2,0,0,0,0,0,0;-2/1:8:-3,0,0,0,1,0,0;2/1:8:-1,-2,0,0,1,0,0;-2/1:8:-1,0,0,0,1,0,0;2/1:8:0,-1,0,0,0,1,0;2/1:9:-1,0,0,0,1,0,0;-2/1:9:0,0,0,0,0,0,0;1/1:10:0,0,0,0,0,0,0;-2/1:11:0,-1,0,0,0,1,0;-2/1:13:0,0,0,0,0,0,0;2/1:14:-2,0,0,0,0,0,0;-1/1:14:2,0,0,0,0,0,0;2/1:16:-2,0,0,0,0,0,0;-4/1:16:0,-2,0,0,0,0,0;2/1:16:0,0,0,0,0,0,0;2/1:17:-4,0,0,0,0,0,0;-2/1:17:-2,-2,0,0,0,0,0;2/1:17:-2,0,0,0,0,0,0;-3/1:17:0,0,0,0,0,0,0;-1/1:21:0,0,0,0,0,0,0;-2/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;2/1:25:0,0,0,0,0,0,0;-2/1:26:0,-1,0,0,0,1,0;-2/1:26:2,0,0,0,0,0,0;2/1:27:0,-1,0,0,0,1,0;-1/1:27:2,0,0,0,0,0,0;1/1:29:0,0,0,0,0,0,0;-2/1:29:2,-1,0,0,0,1,0;-1/1:32:0,0,0,0,0,0,0;2/1:33:0,-1,0,0,0,1,0;1/1:36:0,0,0,0,0,0,0;1/1:38:0,0,0,0,0,0,0;-1/1:41:0,0,0,0,0,0,0;-2/1:43:0,0,0,0,0,0,0;2/1:45:-2,0,0,0,0,0,0;-2/1:45:0,-2,0,0,0,0,0;2/1:45:0,0,0,0,0,0,0;-1/1:45:2,0,0,0,0,0,0;1/1:46:0,0,0,0,0,0,0;2/1:50:-2,0,0,0,0,0,0;2/1:50:0,0,0,0,0,0,0;2/1:54:0,-1,0,0,0,1,0;2/1:55:0,0,0,0,0,0,0;2/1:57:0,0,0,0,0,0,0;-2/1:58:0,-1,0,0,0,1,0;-1/1:58:1,0,0,0,1,0,0;2/1:59:-1,0,0,0,1,0,0;2/1:59:0,0,0,0,0,0,0;-2/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;2/1:61:1,0,0,0,1,0,0;2/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3173Check80 : substituteCompute basis ((tail 3173).drop 80)=boundedLongTail3173Value80 := by
  apply substituteCompute_stage basis (tail 3173) 80 8 boundedLongTail3173Value80 boundedLongTail3173Value88 boundedLongTail3173Check88
  decide +kernel

compact_certificate private def boundedLongTail3173Value72 : Poly := laurent_polynomial% "-2/1:1:-2,0,0,0,0,0,0;-2/1:2:0,0,0,0,0,0,0;2/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;2/1:7:-2,0,0,0,0,0,0;-2/1:8:-3,0,0,0,1,0,0;2/1:8:-1,-2,0,0,1,0,0;-2/1:8:-1,0,0,0,1,0,0;2/1:8:0,-1,0,0,0,1,0;2/1:9:-1,0,0,0,1,0,0;-1/1:9:0,0,0,0,0,0,0;-2/1:11:0,-1,0,0,0,1,0;-2/1:13:0,0,0,0,0,0,0;2/1:14:-2,0,0,0,0,0,0;-1/1:14:2,0,0,0,0,0,0;2/1:16:-2,0,0,0,0,0,0;-4/1:16:0,-2,0,0,0,0,0;2/1:16:0,0,0,0,0,0,0;2/1:17:-4,0,0,0,0,0,0;-2/1:17:-2,-2,0,0,0,0,0;2/1:17:-2,0,0,0,0,0,0;-3/1:17:0,0,0,0,0,0,0;-2/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;2/1:25:0,0,0,0,0,0,0;-2/1:26:0,-1,0,0,0,1,0;-2/1:26:2,0,0,0,0,0,0;2/1:27:0,-1,0,0,0,1,0;-1/1:27:2,0,0,0,0,0,0;2/1:29:0,0,0,0,0,0,0;-2/1:29:2,-1,0,0,0,1,0;2/1:33:0,-1,0,0,0,1,0;2/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-2/1:43:0,0,0,0,0,0,0;2/1:45:-2,0,0,0,0,0,0;-2/1:45:0,-2,0,0,0,0,0;2/1:45:0,0,0,0,0,0,0;-1/1:45:2,0,0,0,0,0,0;1/1:49:0,0,0,0,0,0,0;2/1:50:-2,0,0,0,0,0,0;2/1:50:0,0,0,0,0,0,0;2/1:54:0,-1,0,0,0,1,0;2/1:55:0,0,0,0,0,0,0;2/1:57:0,0,0,0,0,0,0;-2/1:58:0,-1,0,0,0,1,0;-1/1:58:1,0,0,0,1,0,0;2/1:59:-1,0,0,0,1,0,0;2/1:59:0,0,0,0,0,0,0;-2/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;2/1:61:1,0,0,0,1,0,0;2/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3173Check72 : substituteCompute basis ((tail 3173).drop 72)=boundedLongTail3173Value72 := by
  apply substituteCompute_stage basis (tail 3173) 72 8 boundedLongTail3173Value72 boundedLongTail3173Value80 boundedLongTail3173Check80
  decide +kernel

compact_certificate private def boundedLongTail3173Value64 : Poly := laurent_polynomial% "-2/1:1:-2,0,0,0,0,0,0;-2/1:2:0,0,0,0,0,0,0;1/1:5:-2,0,0,0,0,0,0;2/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;2/1:7:-2,0,0,0,0,0,0;-2/1:8:-3,0,0,0,1,0,0;2/1:8:-1,-2,0,0,1,0,0;-1/1:8:-1,0,0,0,1,0,0;2/1:8:0,-1,0,0,0,1,0;3/1:9:-1,0,0,0,1,0,0;-1/1:9:0,0,0,0,0,0,0;-2/1:11:0,-1,0,0,0,1,0;-2/1:13:0,0,0,0,0,0,0;2/1:14:-2,0,0,0,0,0,0;-1/1:14:2,0,0,0,0,0,0;2/1:16:-2,0,0,0,0,0,0;-4/1:16:0,-2,0,0,0,0,0;2/1:16:0,0,0,0,0,0,0;2/1:17:-4,0,0,0,0,0,0;-2/1:17:-2,-2,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;-3/1:17:0,0,0,0,0,0,0;-2/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;2/1:25:0,0,0,0,0,0,0;-2/1:26:0,-1,0,0,0,1,0;-2/1:26:2,0,0,0,0,0,0;2/1:27:0,-1,0,0,0,1,0;-1/1:27:2,0,0,0,0,0,0;3/1:29:0,0,0,0,0,0,0;-2/1:29:2,-1,0,0,0,1,0;1/1:32:0,0,0,0,0,0,0;2/1:33:0,-1,0,0,0,1,0;2/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-2/1:43:0,0,0,0,0,0,0;2/1:45:-2,0,0,0,0,0,0;-2/1:45:0,-2,0,0,0,0,0;2/1:45:0,0,0,0,0,0,0;-1/1:45:2,0,0,0,0,0,0;1/1:49:0,0,0,0,0,0,0;3/1:50:-2,0,0,0,0,0,0;2/1:50:0,0,0,0,0,0,0;2/1:54:0,-1,0,0,0,1,0;2/1:55:0,0,0,0,0,0,0;2/1:57:0,0,0,0,0,0,0;-2/1:58:0,-1,0,0,0,1,0;-1/1:58:1,0,0,0,1,0,0;2/1:59:-1,0,0,0,1,0,0;2/1:59:0,0,0,0,0,0,0;-2/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;2/1:61:1,0,0,0,1,0,0;2/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3173Check64 : substituteCompute basis ((tail 3173).drop 64)=boundedLongTail3173Value64 := by
  apply substituteCompute_stage basis (tail 3173) 64 8 boundedLongTail3173Value64 boundedLongTail3173Value72 boundedLongTail3173Check72
  decide +kernel

compact_certificate private def boundedLongTail3173Value56 : Poly := laurent_polynomial% "-2/1:1:-2,0,0,0,0,0,0;-2/1:2:0,0,0,0,0,0,0;1/1:5:-2,0,0,0,0,0,0;2/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;2/1:7:-2,0,0,0,0,0,0;-2/1:8:-3,0,0,0,1,0,0;2/1:8:-1,-2,0,0,1,0,0;-1/1:8:-1,0,0,0,1,0,0;2/1:8:0,-1,0,0,0,1,0;3/1:9:-1,0,0,0,1,0,0;-1/1:9:0,0,0,0,0,0,0;-2/1:11:0,-1,0,0,0,1,0;-2/1:13:0,0,0,0,0,0,0;2/1:14:-2,0,0,0,0,0,0;-1/1:14:2,0,0,0,0,0,0;2/1:16:-2,0,0,0,0,0,0;-4/1:16:0,-2,0,0,0,0,0;2/1:16:0,0,0,0,0,0,0;2/1:17:-4,0,0,0,0,0,0;-2/1:17:-2,-2,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;-3/1:17:0,0,0,0,0,0,0;-2/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;2/1:25:0,0,0,0,0,0,0;-2/1:26:0,-1,0,0,0,1,0;-2/1:26:2,0,0,0,0,0,0;2/1:27:0,-1,0,0,0,1,0;-1/1:27:2,0,0,0,0,0,0;3/1:29:0,0,0,0,0,0,0;-2/1:29:2,-1,0,0,0,1,0;1/1:32:0,0,0,0,0,0,0;2/1:33:0,-1,0,0,0,1,0;2/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-2/1:43:0,0,0,0,0,0,0;2/1:45:-2,0,0,0,0,0,0;-2/1:45:0,-2,0,0,0,0,0;2/1:45:0,0,0,0,0,0,0;-1/1:45:2,0,0,0,0,0,0;1/1:49:0,0,0,0,0,0,0;3/1:50:-2,0,0,0,0,0,0;2/1:50:0,0,0,0,0,0,0;2/1:54:0,-1,0,0,0,1,0;2/1:55:0,0,0,0,0,0,0;2/1:57:0,0,0,0,0,0,0;-2/1:58:0,-1,0,0,0,1,0;-1/1:58:1,0,0,0,1,0,0;2/1:59:-1,0,0,0,1,0,0;2/1:59:0,0,0,0,0,0,0;-2/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;2/1:61:1,0,0,0,1,0,0;2/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3173Check56 : substituteCompute basis ((tail 3173).drop 56)=boundedLongTail3173Value56 := by
  apply substituteCompute_stage basis (tail 3173) 56 8 boundedLongTail3173Value56 boundedLongTail3173Value64 boundedLongTail3173Check64
  decide +kernel

compact_certificate private def boundedLongTail3173Value48 : Poly := laurent_polynomial% "-2/1:1:-2,0,0,0,0,0,0;-2/1:2:0,0,0,0,0,0,0;2/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;2/1:7:-2,0,0,0,0,0,0;-3/1:8:-3,0,0,0,1,0,0;2/1:8:-1,-2,0,0,1,0,0;-1/1:8:-1,0,0,0,1,0,0;2/1:8:0,-1,0,0,0,1,0;3/1:9:-1,0,0,0,1,0,0;-2/1:9:0,0,0,0,0,0,0;1/1:10:0,0,0,0,0,0,0;-2/1:11:0,-1,0,0,0,1,0;-2/1:13:0,0,0,0,0,0,0;3/1:14:-2,0,0,0,0,0,0;-1/1:14:0,0,0,0,0,0,0;-1/1:14:2,0,0,0,0,0,0;3/1:16:-2,0,0,0,0,0,0;-4/1:16:0,-2,0,0,0,0,0;2/1:16:0,0,0,0,0,0,0;3/1:17:-4,0,0,0,0,0,0;-2/1:17:-2,-2,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;-3/1:17:0,0,0,0,0,0,0;-2/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;2/1:25:0,0,0,0,0,0,0;-2/1:26:0,-1,0,0,0,1,0;-2/1:26:2,0,0,0,0,0,0;2/1:27:0,-1,0,0,0,1,0;-2/1:27:2,0,0,0,0,0,0;2/1:29:0,0,0,0,0,0,0;-2/1:29:2,-1,0,0,0,1,0;2/1:33:0,-1,0,0,0,1,0;2/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;1/1:41:0,0,0,0,0,0,0;-2/1:43:0,0,0,0,0,0,0;3/1:45:-2,0,0,0,0,0,0;-2/1:45:0,-2,0,0,0,0,0;1/1:45:0,0,0,0,0,0,0;-1/1:45:2,0,0,0,0,0,0;3/1:50:-2,0,0,0,0,0,0;2/1:50:0,0,0,0,0,0,0;2/1:54:0,-1,0,0,0,1,0;2/1:55:0,0,0,0,0,0,0;2/1:57:0,0,0,0,0,0,0;-2/1:58:0,-1,0,0,0,1,0;-1/1:58:1,0,0,0,1,0,0;3/1:59:-1,0,0,0,1,0,0;1/1:59:0,0,0,0,0,0,0;-2/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;2/1:61:1,0,0,0,1,0,0;2/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3173Check48 : substituteCompute basis ((tail 3173).drop 48)=boundedLongTail3173Value48 := by
  apply substituteCompute_stage basis (tail 3173) 48 8 boundedLongTail3173Value48 boundedLongTail3173Value56 boundedLongTail3173Check56
  decide +kernel

compact_certificate private def boundedLongTail3173Value40 : Poly := laurent_polynomial% "-2/1:1:-2,0,0,0,0,0,0;-2/1:2:0,0,0,0,0,0,0;2/1:5:0,-2,0,0,0,0,0;-2/1:5:0,0,0,0,0,0,0;2/1:7:-2,0,0,0,0,0,0;-3/1:8:-3,0,0,0,1,0,0;2/1:8:-1,-2,0,0,1,0,0;-1/1:8:-1,0,0,0,1,0,0;2/1:8:0,-1,0,0,0,1,0;3/1:9:-1,0,0,0,1,0,0;-2/1:9:0,0,0,0,0,0,0;1/1:10:0,0,0,0,0,0,0;-2/1:11:0,-1,0,0,0,1,0;-2/1:13:0,0,0,0,0,0,0;3/1:14:-2,0,0,0,0,0,0;-1/1:14:0,0,0,0,0,0,0;-1/1:14:2,0,0,0,0,0,0;3/1:16:-2,0,0,0,0,0,0;-4/1:16:0,-2,0,0,0,0,0;2/1:16:0,0,0,0,0,0,0;3/1:17:-4,0,0,0,0,0,0;-2/1:17:-2,-2,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;-3/1:17:0,0,0,0,0,0,0;1/1:21:0,0,0,0,0,0,0;-1/1:22:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;2/1:25:0,0,0,0,0,0,0;-2/1:26:0,-1,0,0,0,1,0;-2/1:26:2,0,0,0,0,0,0;2/1:27:0,-1,0,0,0,1,0;-2/1:27:2,0,0,0,0,0,0;1/1:29:0,0,0,0,0,0,0;-2/1:29:2,-1,0,0,0,1,0;2/1:33:0,-1,0,0,0,1,0;2/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;1/1:41:0,0,0,0,0,0,0;-2/1:43:0,0,0,0,0,0,0;3/1:45:-2,0,0,0,0,0,0;-2/1:45:0,-2,0,0,0,0,0;1/1:45:0,0,0,0,0,0,0;-1/1:45:2,0,0,0,0,0,0;-1/1:46:0,0,0,0,0,0,0;-1/1:49:0,0,0,0,0,0,0;3/1:50:-2,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;2/1:54:0,-1,0,0,0,1,0;2/1:55:0,0,0,0,0,0,0;2/1:57:0,0,0,0,0,0,0;-2/1:58:0,-1,0,0,0,1,0;-1/1:58:1,0,0,0,1,0,0;3/1:59:-1,0,0,0,1,0,0;1/1:59:0,0,0,0,0,0,0;-2/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;2/1:61:1,0,0,0,1,0,0;2/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3173Check40 : substituteCompute basis ((tail 3173).drop 40)=boundedLongTail3173Value40 := by
  apply substituteCompute_stage basis (tail 3173) 40 8 boundedLongTail3173Value40 boundedLongTail3173Value48 boundedLongTail3173Check48
  decide +kernel

compact_certificate private def boundedLongTail3173Value32 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;-1/1:5:-2,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-2/1:5:0,0,0,0,0,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;-1/1:8:-1,0,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-1/1:9:0,0,0,0,0,0,0;-1/1:11:0,-1,0,0,0,1,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;2/1:16:0,0,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;1/1:17:0,0,0,0,0,0,0;1/1:21:0,0,0,0,0,0,0;-1/1:22:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;1/1:25:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;-1/1:26:2,0,0,0,0,0,0;1/1:27:0,-1,0,0,0,1,0;-1/1:27:2,0,0,0,0,0,0;1/1:29:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;1/1:33:0,-1,0,0,0,1,0;2/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;1/1:41:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;-1/1:46:0,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:59:-1,0,0,0,1,0,0;1/1:59:0,0,0,0,0,0,0;-1/1:60:0,0,0,0,0,0,0;1/1:61:0,0,0,0,0,0,0;1/1:61:1,0,0,0,1,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3173Check32 : substituteCompute basis ((tail 3173).drop 32)=boundedLongTail3173Value32 := by
  apply substituteCompute_stage basis (tail 3173) 32 8 boundedLongTail3173Value32 boundedLongTail3173Value40 boundedLongTail3173Check40
  decide +kernel

compact_certificate private def boundedLongTail3173Value24 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;1/1:9:-1,0,0,0,1,0,0;-1/1:9:0,0,0,0,0,0,0;-1/1:11:0,-1,0,0,0,1,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;-1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:16:0,0,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:27:0,-1,0,0,0,1,0;-1/1:29:2,-1,0,0,0,1,0;1/1:33:0,-1,0,0,0,1,0;1/1:36:0,0,0,0,0,0,0;1/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;-1/1:45:2,0,0,0,0,0,0;1/1:50:-2,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;-1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;1/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3173Check24 : substituteCompute basis ((tail 3173).drop 24)=boundedLongTail3173Value24 := by
  apply substituteCompute_stage basis (tail 3173) 24 8 boundedLongTail3173Value24 boundedLongTail3173Value32 boundedLongTail3173Check32
  decide +kernel

compact_certificate private def boundedLongTail3173Value16 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;1/1:9:-1,0,0,0,1,0,0;-1/1:11:0,-1,0,0,0,1,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;-1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:27:0,-1,0,0,0,1,0;-1/1:29:2,-1,0,0,0,1,0;1/1:33:0,-1,0,0,0,1,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;-1/1:45:2,0,0,0,0,0,0;1/1:50:-2,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;-1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;1/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3173Check16 : substituteCompute basis ((tail 3173).drop 16)=boundedLongTail3173Value16 := by
  apply substituteCompute_stage basis (tail 3173) 16 8 boundedLongTail3173Value16 boundedLongTail3173Value24 boundedLongTail3173Check24
  decide +kernel

compact_certificate private def boundedLongTail3173Value8 : Poly := laurent_polynomial% ""

compact_certificate private theorem boundedLongTail3173Check8 : substituteCompute basis ((tail 3173).drop 8)=boundedLongTail3173Value8 := by
  apply substituteCompute_stage basis (tail 3173) 8 8 boundedLongTail3173Value8 boundedLongTail3173Value16 boundedLongTail3173Check16
  decide +kernel

compact_certificate private def boundedLongTail3173Value0 : Poly := laurent_polynomial% ""

compact_certificate private theorem boundedLongTail3173Check0 : substituteCompute basis ((tail 3173).drop 0)=boundedLongTail3173Value0 := by
  apply substituteCompute_stage basis (tail 3173) 0 8 boundedLongTail3173Value0 boundedLongTail3173Value8 boundedLongTail3173Check8
  decide +kernel

compact_certificate theorem boundedLongTail3173Done : substitute basis (tail 3173)=[] := by
  simpa only [← substituteCompute_eq, List.drop_zero, boundedLongTail3173Value0] using boundedLongTail3173Check0

compact_certificate private theorem boundedLongTail3174Check120 : substituteCompute basis ((tail 3174).drop 120)=[] := by
  decide +kernel

compact_certificate private def boundedLongTail3174Value112 : Poly := laurent_polynomial% ""

compact_certificate private theorem boundedLongTail3174Check112 : substituteCompute basis ((tail 3174).drop 112)=boundedLongTail3174Value112 := by
  apply substituteCompute_stage basis (tail 3174) 112 8 boundedLongTail3174Value112 [] boundedLongTail3174Check120
  decide +kernel

compact_certificate private def boundedLongTail3174Value104 : Poly := laurent_polynomial% "-1/1:5:0,0,0,0,0,0,0;-1/1:8:-1,0,0,0,1,0,0;1/1:16:0,0,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;1/1:45:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3174Check104 : substituteCompute basis ((tail 3174).drop 104)=boundedLongTail3174Value104 := by
  apply substituteCompute_stage basis (tail 3174) 104 8 boundedLongTail3174Value104 boundedLongTail3174Value112 boundedLongTail3174Check112
  decide +kernel

compact_certificate private def boundedLongTail3174Value96 : Poly := laurent_polynomial% "-2/1:5:0,0,0,0,0,0,0;1/1:8:-3,0,0,0,1,0,0;-2/1:8:-1,0,0,0,1,0,0;-1/1:9:-1,0,0,0,1,0,0;-1/1:14:-2,0,0,0,0,0,0;1/1:14:0,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;-1/1:16:-2,0,0,0,0,0,0;2/1:16:0,0,0,0,0,0,0;-1/1:17:-4,0,0,0,0,0,0;2/1:17:-2,0,0,0,0,0,0;1/1:17:0,0,0,0,0,0,0;-1/1:22:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;-1/1:45:-2,0,0,0,0,0,0;2/1:45:0,0,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;-1/1:50:-2,0,0,0,0,0,0;1/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;-1/1:59:-1,0,0,0,1,0,0;1/1:61:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3174Check96 : substituteCompute basis ((tail 3174).drop 96)=boundedLongTail3174Value96 := by
  apply substituteCompute_stage basis (tail 3174) 96 8 boundedLongTail3174Value96 boundedLongTail3174Value104 boundedLongTail3174Check104
  decide +kernel

compact_certificate private def boundedLongTail3174Value88 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;-1/1:5:-2,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-2/1:5:0,0,0,0,0,0,0;-1/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;1/1:8:-1,-2,0,0,1,0,0;-3/1:8:-1,0,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-1/1:8:0,0,0,0,0,0,0;-1/1:9:-1,0,0,0,1,0,0;-1/1:11:0,-1,0,0,0,1,0;1/1:11:0,0,0,0,0,0,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:0,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;3/1:16:0,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;3/1:17:-2,0,0,0,0,0,0;-1/1:18:0,0,0,0,0,0,0;-2/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:26:0,0,0,0,0,0,0;1/1:27:0,-1,0,0,0,1,0;-1/1:27:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;1/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-1/1:33:0,0,0,0,0,0,0;1/1:36:0,0,0,0,0,0,0;1/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;2/1:45:0,0,0,0,0,0,0;1/1:46:0,0,0,0,0,0,0;-1/1:50:-2,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;2/1:58:0,0,0,0,0,0,0;-1/1:60:0,0,0,0,0,0,0;2/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3174Check88 : substituteCompute basis ((tail 3174).drop 88)=boundedLongTail3174Value88 := by
  apply substituteCompute_stage basis (tail 3174) 88 8 boundedLongTail3174Value88 boundedLongTail3174Value96 boundedLongTail3174Check96
  decide +kernel

compact_certificate private def boundedLongTail3174Value80 : Poly := laurent_polynomial% "-2/1:1:-2,0,0,0,0,0,0;-2/1:2:0,0,0,0,0,0,0;2/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;2/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;2/1:8:-1,-2,0,0,1,0,0;-2/1:8:-1,0,0,0,1,0,0;2/1:8:0,-1,0,0,0,1,0;-1/1:8:0,0,0,0,0,0,0;1/1:9:-1,0,0,0,1,0,0;-2/1:11:0,-1,0,0,0,1,0;1/1:11:0,0,0,0,0,0,0;1/1:12:0,0,0,0,0,0,0;-2/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;-1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-4/1:16:0,-2,0,0,0,0,0;1/1:16:0,0,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-2/1:17:-2,-2,0,0,0,0,0;2/1:17:-2,0,0,0,0,0,0;-2/1:17:0,0,0,0,0,0,0;-1/1:18:0,0,0,0,0,0,0;-2/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-2/1:26:0,-1,0,0,0,1,0;1/1:26:0,0,0,0,0,0,0;2/1:27:0,-1,0,0,0,1,0;-1/1:27:0,0,0,0,0,0,0;-2/1:29:2,-1,0,0,0,1,0;2/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;2/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;1/1:36:0,0,0,0,0,0,0;1/1:38:0,0,0,0,0,0,0;-2/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-2/1:45:0,-2,0,0,0,0,0;2/1:45:0,0,0,0,0,0,0;-1/1:45:2,0,0,0,0,0,0;1/1:46:0,0,0,0,0,0,0;1/1:50:-2,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;2/1:54:0,-1,0,0,0,1,0;-1/1:54:0,0,0,0,0,0,0;2/1:55:0,0,0,0,0,0,0;2/1:57:0,0,0,0,0,0,0;-2/1:58:0,-1,0,0,0,1,0;3/1:58:0,0,0,0,0,0,0;-1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;-2/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;2/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3174Check80 : substituteCompute basis ((tail 3174).drop 80)=boundedLongTail3174Value80 := by
  apply substituteCompute_stage basis (tail 3174) 80 8 boundedLongTail3174Value80 boundedLongTail3174Value88 boundedLongTail3174Check88
  decide +kernel

compact_certificate private def boundedLongTail3174Value72 : Poly := laurent_polynomial% "-2/1:1:-2,0,0,0,0,0,0;-2/1:2:0,0,0,0,0,0,0;2/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;2/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;2/1:8:-1,-2,0,0,1,0,0;-2/1:8:-1,0,0,0,1,0,0;2/1:8:0,-1,0,0,0,1,0;-1/1:8:0,0,0,0,0,0,0;1/1:9:-1,0,0,0,1,0,0;-2/1:11:0,-1,0,0,0,1,0;-2/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-4/1:16:0,-2,0,0,0,0,0;1/1:16:0,0,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-2/1:17:-2,-2,0,0,0,0,0;2/1:17:-2,0,0,0,0,0,0;-2/1:17:0,0,0,0,0,0,0;-1/1:18:0,0,0,0,0,0,0;-2/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-2/1:26:0,-1,0,0,0,1,0;2/1:27:0,-1,0,0,0,1,0;-2/1:27:0,0,0,0,0,0,0;-2/1:29:2,-1,0,0,0,1,0;2/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;2/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;2/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-2/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-2/1:45:0,-2,0,0,0,0,0;2/1:45:0,0,0,0,0,0,0;1/1:50:-2,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;2/1:54:0,-1,0,0,0,1,0;-1/1:54:0,0,0,0,0,0,0;2/1:55:0,0,0,0,0,0,0;2/1:57:0,0,0,0,0,0,0;-2/1:58:0,-1,0,0,0,1,0;2/1:58:0,0,0,0,0,0,0;1/1:59:-1,0,0,0,1,0,0;-2/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;2/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3174Check72 : substituteCompute basis ((tail 3174).drop 72)=boundedLongTail3174Value72 := by
  apply substituteCompute_stage basis (tail 3174) 72 8 boundedLongTail3174Value72 boundedLongTail3174Value80 boundedLongTail3174Check80
  decide +kernel

compact_certificate private def boundedLongTail3174Value64 : Poly := laurent_polynomial% "-2/1:1:-2,0,0,0,0,0,0;-2/1:2:0,0,0,0,0,0,0;1/1:5:-2,0,0,0,0,0,0;2/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;2/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;2/1:8:-1,-2,0,0,1,0,0;-1/1:8:-1,0,0,0,1,0,0;2/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;2/1:9:-1,0,0,0,1,0,0;-2/1:11:0,-1,0,0,0,1,0;-1/1:12:0,0,0,0,0,0,0;-2/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-4/1:16:0,-2,0,0,0,0,0;1/1:16:0,0,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-2/1:17:-2,-2,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;-2/1:17:0,0,0,0,0,0,0;-2/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-2/1:26:0,-1,0,0,0,1,0;-1/1:26:0,0,0,0,0,0,0;2/1:27:0,-1,0,0,0,1,0;-3/1:27:0,0,0,0,0,0,0;-2/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;2/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;2/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-2/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-2/1:45:0,-2,0,0,0,0,0;2/1:45:0,0,0,0,0,0,0;2/1:50:-2,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;2/1:54:0,-1,0,0,0,1,0;2/1:55:0,0,0,0,0,0,0;2/1:57:0,0,0,0,0,0,0;-2/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;1/1:59:-1,0,0,0,1,0,0;-2/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;2/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3174Check64 : substituteCompute basis ((tail 3174).drop 64)=boundedLongTail3174Value64 := by
  apply substituteCompute_stage basis (tail 3174) 64 8 boundedLongTail3174Value64 boundedLongTail3174Value72 boundedLongTail3174Check72
  decide +kernel

compact_certificate private def boundedLongTail3174Value56 : Poly := laurent_polynomial% "-2/1:1:-2,0,0,0,0,0,0;-2/1:2:0,0,0,0,0,0,0;1/1:5:-2,0,0,0,0,0,0;2/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;2/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;2/1:8:-1,-2,0,0,1,0,0;-1/1:8:-1,0,0,0,1,0,0;2/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;2/1:9:-1,0,0,0,1,0,0;-2/1:11:0,-1,0,0,0,1,0;-1/1:12:0,0,0,0,0,0,0;-2/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-4/1:16:0,-2,0,0,0,0,0;1/1:16:0,0,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-2/1:17:-2,-2,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;-2/1:17:0,0,0,0,0,0,0;-2/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-2/1:26:0,-1,0,0,0,1,0;-1/1:26:0,0,0,0,0,0,0;2/1:27:0,-1,0,0,0,1,0;-3/1:27:0,0,0,0,0,0,0;-2/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;2/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;2/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-2/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-2/1:45:0,-2,0,0,0,0,0;2/1:45:0,0,0,0,0,0,0;2/1:50:-2,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;2/1:54:0,-1,0,0,0,1,0;2/1:55:0,0,0,0,0,0,0;2/1:57:0,0,0,0,0,0,0;-2/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;1/1:59:-1,0,0,0,1,0,0;-2/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;2/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3174Check56 : substituteCompute basis ((tail 3174).drop 56)=boundedLongTail3174Value56 := by
  apply substituteCompute_stage basis (tail 3174) 56 8 boundedLongTail3174Value56 boundedLongTail3174Value64 boundedLongTail3174Check64
  decide +kernel

compact_certificate private def boundedLongTail3174Value48 : Poly := laurent_polynomial% "-2/1:1:-2,0,0,0,0,0,0;-2/1:2:0,0,0,0,0,0,0;2/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;2/1:7:-2,0,0,0,0,0,0;-2/1:8:-3,0,0,0,1,0,0;2/1:8:-1,-2,0,0,1,0,0;-1/1:8:-1,0,0,0,1,0,0;2/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;2/1:9:-1,0,0,0,1,0,0;-2/1:11:0,-1,0,0,0,1,0;-1/1:12:0,0,0,0,0,0,0;-2/1:13:0,0,0,0,0,0,0;2/1:14:-2,0,0,0,0,0,0;-1/1:14:0,0,0,0,0,0,0;2/1:16:-2,0,0,0,0,0,0;-4/1:16:0,-2,0,0,0,0,0;1/1:16:0,0,0,0,0,0,0;2/1:17:-4,0,0,0,0,0,0;-2/1:17:-2,-2,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;-2/1:17:0,0,0,0,0,0,0;-2/1:22:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-2/1:26:0,-1,0,0,0,1,0;2/1:27:0,-1,0,0,0,1,0;-2/1:27:0,0,0,0,0,0,0;-2/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;2/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;2/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-2/1:43:0,0,0,0,0,0,0;2/1:45:-2,0,0,0,0,0,0;-2/1:45:0,-2,0,0,0,0,0;1/1:45:0,0,0,0,0,0,0;2/1:50:-2,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;2/1:54:0,-1,0,0,0,1,0;2/1:55:0,0,0,0,0,0,0;2/1:57:0,0,0,0,0,0,0;-2/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;2/1:59:-1,0,0,0,1,0,0;-2/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;2/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3174Check48 : substituteCompute basis ((tail 3174).drop 48)=boundedLongTail3174Value48 := by
  apply substituteCompute_stage basis (tail 3174) 48 8 boundedLongTail3174Value48 boundedLongTail3174Value56 boundedLongTail3174Check56
  decide +kernel

compact_certificate private def boundedLongTail3174Value40 : Poly := laurent_polynomial% "-2/1:1:-2,0,0,0,0,0,0;-2/1:2:0,0,0,0,0,0,0;2/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;2/1:7:-2,0,0,0,0,0,0;-2/1:8:-3,0,0,0,1,0,0;2/1:8:-1,-2,0,0,1,0,0;-1/1:8:-1,0,0,0,1,0,0;2/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;2/1:9:-1,0,0,0,1,0,0;-2/1:11:0,-1,0,0,0,1,0;-1/1:11:0,0,0,0,0,0,0;-2/1:13:0,0,0,0,0,0,0;2/1:14:-2,0,0,0,0,0,0;-1/1:14:0,0,0,0,0,0,0;2/1:16:-2,0,0,0,0,0,0;-4/1:16:0,-2,0,0,0,0,0;1/1:16:0,0,0,0,0,0,0;2/1:17:-4,0,0,0,0,0,0;-2/1:17:-2,-2,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;1/1:18:0,0,0,0,0,0,0;-1/1:22:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;-2/1:26:0,-1,0,0,0,1,0;2/1:27:0,-1,0,0,0,1,0;-1/1:27:0,0,0,0,0,0,0;-2/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;2/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;2/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-2/1:43:0,0,0,0,0,0,0;2/1:45:-2,0,0,0,0,0,0;-2/1:45:0,-2,0,0,0,0,0;1/1:45:0,0,0,0,0,0,0;-1/1:46:0,0,0,0,0,0,0;2/1:50:-2,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;2/1:54:0,-1,0,0,0,1,0;-1/1:54:0,0,0,0,0,0,0;2/1:55:0,0,0,0,0,0,0;2/1:57:0,0,0,0,0,0,0;-2/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;2/1:59:-1,0,0,0,1,0,0;-2/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;2/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3174Check40 : substituteCompute basis ((tail 3174).drop 40)=boundedLongTail3174Value40 := by
  apply substituteCompute_stage basis (tail 3174) 40 8 boundedLongTail3174Value40 boundedLongTail3174Value48 boundedLongTail3174Check48
  decide +kernel

compact_certificate private def boundedLongTail3174Value32 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;-1/1:5:-2,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-1/1:5:0,0,0,0,0,0,0;-1/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;-1/1:8:-1,0,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;-1/1:11:0,-1,0,0,0,1,0;-1/1:11:0,0,0,0,0,0,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;2/1:16:0,0,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;1/1:17:-2,0,0,0,0,0,0;1/1:17:0,0,0,0,0,0,0;1/1:18:0,0,0,0,0,0,0;-1/1:22:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:27:0,-1,0,0,0,1,0;-1/1:27:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;1/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;2/1:36:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;-1/1:46:0,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;-1/1:54:0,0,0,0,0,0,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;2/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3174Check32 : substituteCompute basis ((tail 3174).drop 32)=boundedLongTail3174Value32 := by
  apply substituteCompute_stage basis (tail 3174) 32 8 boundedLongTail3174Value32 boundedLongTail3174Value40 boundedLongTail3174Check40
  decide +kernel

compact_certificate private def boundedLongTail3174Value24 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-1/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;1/1:9:-1,0,0,0,1,0,0;-1/1:11:0,-1,0,0,0,1,0;1/1:12:0,0,0,0,0,0,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;-1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:16:0,0,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;1/1:18:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:27:0,-1,0,0,0,1,0;-1/1:27:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;1/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;1/1:36:0,0,0,0,0,0,0;1/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;-1/1:45:2,0,0,0,0,0,0;1/1:50:-2,0,0,0,0,0,0;1/1:50:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;-1/1:54:0,0,0,0,0,0,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;-1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;1/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3174Check24 : substituteCompute basis ((tail 3174).drop 24)=boundedLongTail3174Value24 := by
  apply substituteCompute_stage basis (tail 3174) 24 8 boundedLongTail3174Value24 boundedLongTail3174Value32 boundedLongTail3174Check32
  decide +kernel

compact_certificate private def boundedLongTail3174Value16 : Poly := laurent_polynomial% "1/1:12:0,0,0,0,0,0,0;1/1:29:2,0,0,0,0,0,0;-1/1:33:0,0,0,0,0,0,0;-1/1:54:0,0,0,0,0,0,0;1/1:58:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3174Check16 : substituteCompute basis ((tail 3174).drop 16)=boundedLongTail3174Value16 := by
  apply substituteCompute_stage basis (tail 3174) 16 8 boundedLongTail3174Value16 boundedLongTail3174Value24 boundedLongTail3174Check24
  decide +kernel

compact_certificate private def boundedLongTail3174Value8 : Poly := laurent_polynomial% ""

compact_certificate private theorem boundedLongTail3174Check8 : substituteCompute basis ((tail 3174).drop 8)=boundedLongTail3174Value8 := by
  apply substituteCompute_stage basis (tail 3174) 8 8 boundedLongTail3174Value8 boundedLongTail3174Value16 boundedLongTail3174Check16
  decide +kernel

compact_certificate private def boundedLongTail3174Value0 : Poly := laurent_polynomial% ""

compact_certificate private theorem boundedLongTail3174Check0 : substituteCompute basis ((tail 3174).drop 0)=boundedLongTail3174Value0 := by
  apply substituteCompute_stage basis (tail 3174) 0 8 boundedLongTail3174Value0 boundedLongTail3174Value8 boundedLongTail3174Check8
  decide +kernel

compact_certificate theorem boundedLongTail3174Done : substitute basis (tail 3174)=[] := by
  simpa only [← substituteCompute_eq, List.drop_zero, boundedLongTail3174Value0] using boundedLongTail3174Check0

compact_certificate private theorem boundedLongTail3175Check120 : substituteCompute basis ((tail 3175).drop 120)=[] := by
  decide +kernel

compact_certificate private def boundedLongTail3175Value112 : Poly := laurent_polynomial% ""

compact_certificate private theorem boundedLongTail3175Check112 : substituteCompute basis ((tail 3175).drop 112)=boundedLongTail3175Value112 := by
  apply substituteCompute_stage basis (tail 3175) 112 8 boundedLongTail3175Value112 [] boundedLongTail3175Check120
  decide +kernel

compact_certificate private def boundedLongTail3175Value104 : Poly := laurent_polynomial% "-1/1:9:0,0,0,0,0,0,0;1/1:10:0,0,0,0,0,0,0;1/1:25:0,0,0,0,0,0,0;-1/1:27:2,0,0,0,0,0,0;-1/1:49:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3175Check104 : substituteCompute basis ((tail 3175).drop 104)=boundedLongTail3175Value104 := by
  apply substituteCompute_stage basis (tail 3175) 104 8 boundedLongTail3175Value104 boundedLongTail3175Value112 boundedLongTail3175Check112
  decide +kernel

compact_certificate private def boundedLongTail3175Value96 : Poly := laurent_polynomial% "1/1:8:-3,0,0,0,1,0,0;-1/1:9:-1,0,0,0,1,0,0;-1/1:9:0,0,0,0,0,0,0;1/1:10:0,0,0,0,0,0,0;-1/1:14:-2,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;-1/1:16:-2,0,0,0,0,0,0;-1/1:17:-4,0,0,0,0,0,0;1/1:17:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;1/1:25:0,0,0,0,0,0,0;-2/1:27:2,0,0,0,0,0,0;-1/1:45:-2,0,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;-1/1:49:0,0,0,0,0,0,0;-1/1:50:-2,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;-1/1:59:-1,0,0,0,1,0,0;1/1:59:0,0,0,0,0,0,0;1/1:61:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3175Check96 : substituteCompute basis ((tail 3175).drop 96)=boundedLongTail3175Value96 := by
  apply substituteCompute_stage basis (tail 3175) 96 8 boundedLongTail3175Value96 boundedLongTail3175Value104 boundedLongTail3175Check104
  decide +kernel

compact_certificate private def boundedLongTail3175Value88 : Poly := laurent_polynomial% "-1/1:5:-2,0,0,0,0,0,0;-1/1:5:1,0,0,0,1,0,0;1/1:8:-3,0,0,0,1,0,0;-1/1:8:0,0,0,0,0,0,0;-2/1:9:-1,0,0,0,1,0,0;-2/1:9:0,0,0,0,0,0,0;1/1:10:0,0,0,0,0,0,0;1/1:11:0,0,0,0,0,0,0;-1/1:14:-2,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;-1/1:16:-2,0,0,0,0,0,0;-1/1:17:-4,0,0,0,0,0,0;2/1:17:0,0,0,0,0,0,0;-1/1:18:0,0,0,0,0,0,0;-1/1:21:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;1/1:25:0,0,0,0,0,0,0;1/1:26:0,0,0,0,0,0,0;-1/1:27:0,0,0,0,0,0,0;-2/1:27:2,0,0,0,0,0,0;1/1:29:2,0,0,0,0,0,0;-1/1:32:0,0,0,0,0,0,0;1/1:32:2,0,0,0,0,0,0;-1/1:33:0,0,0,0,0,0,0;1/1:38:0,0,0,0,0,0,0;-1/1:45:-2,0,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;1/1:46:0,0,0,0,0,0,0;-2/1:50:-2,0,0,0,0,0,0;1/1:54:0,0,0,0,0,0,0;1/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;-1/1:59:-1,0,0,0,1,0,0;1/1:59:0,0,0,0,0,0,0;1/1:61:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3175Check88 : substituteCompute basis ((tail 3175).drop 88)=boundedLongTail3175Value88 := by
  apply substituteCompute_stage basis (tail 3175) 88 8 boundedLongTail3175Value88 boundedLongTail3175Value96 boundedLongTail3175Check96
  decide +kernel

compact_certificate private def boundedLongTail3175Value80 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;-1/1:5:-2,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-1/1:8:0,0,0,0,0,0,0;-2/1:9:0,0,0,0,0,0,0;1/1:10:0,0,0,0,0,0,0;-1/1:11:0,-1,0,0,0,1,0;1/1:11:0,0,0,0,0,0,0;1/1:12:0,0,0,0,0,0,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-1/1:18:0,0,0,0,0,0,0;-1/1:21:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;1/1:25:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:26:0,0,0,0,0,0,0;-1/1:26:2,0,0,0,0,0,0;1/1:27:0,-1,0,0,0,1,0;-1/1:27:0,0,0,0,0,0,0;-2/1:27:2,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;2/1:29:2,0,0,0,0,0,0;-1/1:32:0,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;1/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;1/1:46:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;2/1:58:0,0,0,0,0,0,0;1/1:59:-1,0,0,0,1,0,0;1/1:59:0,0,0,0,0,0,0;-1/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;1/1:61:1,0,0,0,1,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3175Check80 : substituteCompute basis ((tail 3175).drop 80)=boundedLongTail3175Value80 := by
  apply substituteCompute_stage basis (tail 3175) 80 8 boundedLongTail3175Value80 boundedLongTail3175Value88 boundedLongTail3175Check88
  decide +kernel

compact_certificate private def boundedLongTail3175Value72 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;-1/1:5:-2,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-1/1:8:0,0,0,0,0,0,0;-1/1:9:0,0,0,0,0,0,0;-1/1:10:0,0,0,0,0,0,0;-1/1:11:0,-1,0,0,0,1,0;1/1:11:0,0,0,0,0,0,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-1/1:18:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:26:0,0,0,0,0,0,0;-1/1:26:2,0,0,0,0,0,0;1/1:27:0,-1,0,0,0,1,0;-2/1:27:0,0,0,0,0,0,0;-1/1:27:2,0,0,0,0,0,0;1/1:29:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;2/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;1/1:49:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;2/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;1/1:59:0,0,0,0,0,0,0;-1/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;1/1:61:1,0,0,0,1,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3175Check72 : substituteCompute basis ((tail 3175).drop 72)=boundedLongTail3175Value72 := by
  apply substituteCompute_stage basis (tail 3175) 72 8 boundedLongTail3175Value72 boundedLongTail3175Value80 boundedLongTail3175Check80
  decide +kernel

compact_certificate private def boundedLongTail3175Value64 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;1/1:9:-1,0,0,0,1,0,0;-1/1:9:0,0,0,0,0,0,0;-1/1:10:0,0,0,0,0,0,0;-1/1:11:0,-1,0,0,0,1,0;1/1:11:0,0,0,0,0,0,0;-1/1:12:0,0,0,0,0,0,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;-1/1:26:2,0,0,0,0,0,0;1/1:27:0,-1,0,0,0,1,0;-3/1:27:0,0,0,0,0,0,0;-1/1:27:2,0,0,0,0,0,0;2/1:29:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;1/1:32:0,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-1/1:33:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;1/1:49:0,0,0,0,0,0,0;1/1:50:-2,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:54:0,0,0,0,0,0,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;1/1:59:0,0,0,0,0,0,0;-1/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;1/1:61:1,0,0,0,1,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3175Check64 : substituteCompute basis ((tail 3175).drop 64)=boundedLongTail3175Value64 := by
  apply substituteCompute_stage basis (tail 3175) 64 8 boundedLongTail3175Value64 boundedLongTail3175Value72 boundedLongTail3175Check72
  decide +kernel

compact_certificate private def boundedLongTail3175Value56 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;1/1:9:-1,0,0,0,1,0,0;-1/1:9:0,0,0,0,0,0,0;-1/1:10:0,0,0,0,0,0,0;-1/1:11:0,-1,0,0,0,1,0;1/1:11:0,0,0,0,0,0,0;-1/1:12:0,0,0,0,0,0,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;-1/1:26:2,0,0,0,0,0,0;1/1:27:0,-1,0,0,0,1,0;-3/1:27:0,0,0,0,0,0,0;-1/1:27:2,0,0,0,0,0,0;2/1:29:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;1/1:32:0,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-1/1:33:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;1/1:49:0,0,0,0,0,0,0;1/1:50:-2,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:54:0,0,0,0,0,0,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;1/1:59:0,0,0,0,0,0,0;-1/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;1/1:61:1,0,0,0,1,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3175Check56 : substituteCompute basis ((tail 3175).drop 56)=boundedLongTail3175Value56 := by
  apply substituteCompute_stage basis (tail 3175) 56 8 boundedLongTail3175Value56 boundedLongTail3175Value64 boundedLongTail3175Check64
  decide +kernel

compact_certificate private def boundedLongTail3175Value48 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;-1/1:5:-2,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-2/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;1/1:9:-1,0,0,0,1,0,0;-2/1:9:0,0,0,0,0,0,0;-1/1:11:0,-1,0,0,0,1,0;1/1:11:0,0,0,0,0,0,0;-1/1:12:0,0,0,0,0,0,0;-1/1:13:0,0,0,0,0,0,0;2/1:14:-2,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;2/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;2/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-2/1:23:0,0,0,0,0,0,0;1/1:25:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;-1/1:26:2,0,0,0,0,0,0;1/1:27:0,-1,0,0,0,1,0;-2/1:27:0,0,0,0,0,0,0;-2/1:27:2,0,0,0,0,0,0;1/1:29:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-1/1:33:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;1/1:41:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;2/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;1/1:50:-2,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;1/1:54:0,0,0,0,0,0,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;2/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;1/1:61:1,0,0,0,1,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3175Check48 : substituteCompute basis ((tail 3175).drop 48)=boundedLongTail3175Value48 := by
  apply substituteCompute_stage basis (tail 3175) 48 8 boundedLongTail3175Value48 boundedLongTail3175Value56 boundedLongTail3175Check56
  decide +kernel

compact_certificate private def boundedLongTail3175Value40 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;-1/1:5:-2,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-2/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-2/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;1/1:9:-1,0,0,0,1,0,0;-2/1:9:0,0,0,0,0,0,0;-1/1:11:0,-1,0,0,0,1,0;-1/1:13:0,0,0,0,0,0,0;2/1:14:-2,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;2/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;2/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;1/1:18:0,0,0,0,0,0,0;1/1:21:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;1/1:25:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;-1/1:26:2,0,0,0,0,0,0;1/1:27:0,-1,0,0,0,1,0;-1/1:27:0,0,0,0,0,0,0;-2/1:27:2,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;2/1:29:2,0,0,0,0,0,0;2/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;1/1:41:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;2/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;-1/1:46:0,0,0,0,0,0,0;-1/1:49:0,0,0,0,0,0,0;1/1:50:-2,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;-1/1:54:0,0,0,0,0,0,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;2/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;3/1:61:0,0,0,0,0,0,0;1/1:61:1,0,0,0,1,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3175Check40 : substituteCompute basis ((tail 3175).drop 40)=boundedLongTail3175Value40 := by
  apply substituteCompute_stage basis (tail 3175) 40 8 boundedLongTail3175Value40 boundedLongTail3175Value48 boundedLongTail3175Check48
  decide +kernel

compact_certificate private def boundedLongTail3175Value32 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;-1/1:5:-2,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-1/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;-1/1:9:0,0,0,0,0,0,0;-1/1:10:0,0,0,0,0,0,0;-1/1:11:0,-1,0,0,0,1,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;1/1:17:0,0,0,0,0,0,0;1/1:18:0,0,0,0,0,0,0;1/1:21:0,0,0,0,0,0,0;-1/1:23:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:27:0,-1,0,0,0,1,0;-1/1:27:0,0,0,0,0,0,0;-1/1:27:2,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;2/1:29:2,0,0,0,0,0,0;1/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;2/1:38:0,0,0,0,0,0,0;1/1:41:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;1/1:45:2,0,0,0,0,0,0;-1/1:46:0,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;-1/1:54:0,0,0,0,0,0,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;2/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3175Check32 : substituteCompute basis ((tail 3175).drop 32)=boundedLongTail3175Value32 := by
  apply substituteCompute_stage basis (tail 3175) 32 8 boundedLongTail3175Value32 boundedLongTail3175Value40 boundedLongTail3175Check40
  decide +kernel

compact_certificate private def boundedLongTail3175Value24 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;-1/1:5:1,0,0,0,1,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;-2/1:8:0,0,0,0,0,0,0;1/1:9:-1,0,0,0,1,0,0;-1/1:9:0,0,0,0,0,0,0;-1/1:11:0,-1,0,0,0,1,0;1/1:12:0,0,0,0,0,0,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;-1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;1/1:18:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:27:0,-1,0,0,0,1,0;-1/1:27:0,0,0,0,0,0,0;-1/1:29:2,-1,0,0,0,1,0;2/1:29:2,0,0,0,0,0,0;1/1:32:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-2/1:33:0,0,0,0,0,0,0;1/1:38:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;-1/1:45:2,0,0,0,0,0,0;1/1:50:-2,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;-1/1:54:0,0,0,0,0,0,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;-1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;1/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3175Check24 : substituteCompute basis ((tail 3175).drop 24)=boundedLongTail3175Value24 := by
  apply substituteCompute_stage basis (tail 3175) 24 8 boundedLongTail3175Value24 boundedLongTail3175Value32 boundedLongTail3175Check32
  decide +kernel

compact_certificate private def boundedLongTail3175Value16 : Poly := laurent_polynomial% "-1/1:1:-2,0,0,0,0,0,0;-1/1:2:0,0,0,0,0,0,0;1/1:5:0,-2,0,0,0,0,0;1/1:7:-2,0,0,0,0,0,0;-1/1:8:-3,0,0,0,1,0,0;1/1:8:-1,-2,0,0,1,0,0;1/1:8:0,-1,0,0,0,1,0;1/1:9:-1,0,0,0,1,0,0;-1/1:11:0,-1,0,0,0,1,0;1/1:12:0,0,0,0,0,0,0;-1/1:13:0,0,0,0,0,0,0;1/1:14:-2,0,0,0,0,0,0;-1/1:14:2,0,0,0,0,0,0;1/1:16:-2,0,0,0,0,0,0;-2/1:16:0,-2,0,0,0,0,0;1/1:17:-4,0,0,0,0,0,0;-1/1:17:-2,-2,0,0,0,0,0;-1/1:17:0,0,0,0,0,0,0;-1/1:26:0,-1,0,0,0,1,0;1/1:27:0,-1,0,0,0,1,0;-1/1:29:2,-1,0,0,0,1,0;1/1:29:2,0,0,0,0,0,0;1/1:33:0,-1,0,0,0,1,0;-1/1:33:0,0,0,0,0,0,0;-1/1:43:0,0,0,0,0,0,0;1/1:45:-2,0,0,0,0,0,0;-1/1:45:0,-2,0,0,0,0,0;-1/1:45:2,0,0,0,0,0,0;1/1:50:-2,0,0,0,0,0,0;1/1:54:0,-1,0,0,0,1,0;-1/1:54:0,0,0,0,0,0,0;1/1:55:0,0,0,0,0,0,0;1/1:57:0,0,0,0,0,0,0;-1/1:58:0,-1,0,0,0,1,0;1/1:58:0,0,0,0,0,0,0;-1/1:58:1,0,0,0,1,0,0;1/1:59:-1,0,0,0,1,0,0;-1/1:60:0,0,0,0,0,0,0;1/1:61:0,0,0,0,0,0,0;1/1:66:0,0,0,0,0,0,0"

compact_certificate private theorem boundedLongTail3175Check16 : substituteCompute basis ((tail 3175).drop 16)=boundedLongTail3175Value16 := by
  apply substituteCompute_stage basis (tail 3175) 16 8 boundedLongTail3175Value16 boundedLongTail3175Value24 boundedLongTail3175Check24
  decide +kernel

compact_certificate private def boundedLongTail3175Value8 : Poly := laurent_polynomial% ""

compact_certificate private theorem boundedLongTail3175Check8 : substituteCompute basis ((tail 3175).drop 8)=boundedLongTail3175Value8 := by
  apply substituteCompute_stage basis (tail 3175) 8 8 boundedLongTail3175Value8 boundedLongTail3175Value16 boundedLongTail3175Check16
  decide +kernel

compact_certificate private def boundedLongTail3175Value0 : Poly := laurent_polynomial% ""

compact_certificate private theorem boundedLongTail3175Check0 : substituteCompute basis ((tail 3175).drop 0)=boundedLongTail3175Value0 := by
  apply substituteCompute_stage basis (tail 3175) 0 8 boundedLongTail3175Value0 boundedLongTail3175Value8 boundedLongTail3175Check8
  decide +kernel

compact_certificate theorem boundedLongTail3175Done : substitute basis (tail 3175)=[] := by
  simpa only [← substituteCompute_eq, List.drop_zero, boundedLongTail3175Value0] using boundedLongTail3175Check0
}
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
