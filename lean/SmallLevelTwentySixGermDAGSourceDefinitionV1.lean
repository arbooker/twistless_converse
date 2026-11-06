module
public import SmallLevelTwentySixGermCoordinateDataV4
public import SmallLevelTwentySixGermSourcesTheoryV4
public import SmallLevelTwentySixGermDAGSourceRowsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGermSources FinitenessRamanujanSum QuantitativeArithmeticSevenLaurentRows

def replayJetRow (n : ℕ) (X Y Z W a b : ℂ) (v : ℕ→ℂ) (i : Fin 397) : ℂ :=
  laurentJetRow n X Y Z W (-1) (-1) (-1) a b
    (fun h j => v (sourceCoordinate h j)) (selectedSource i)

end SmallLevelTwentySixGermDAG
