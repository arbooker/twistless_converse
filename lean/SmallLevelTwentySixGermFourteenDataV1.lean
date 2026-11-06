module
public import SmallLevelTwentySixGermFullFirstChartV1
public import SmallLevelTwentySixIntegerRowIndexTransposeSourcesSeriesV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermFourteen
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGermDAG SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)

def rows : Fin 14→Poly :=
  ![SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row01.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row05.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row07.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row08.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row09.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row29.primitiveData,
    SmallLevelIntegerLaurentGerm.toRat SmallLevelTwentySixIntegerRow87Transpose.outputData,
    SmallLevelIntegerLaurentGerm.toRat SmallLevelTwentySixIntegerRow88Transpose.outputData,
    SmallLevelIntegerLaurentGerm.toRat SmallLevelTwentySixIntegerRow89Transpose.outputData]

theorem rows_support : ∀ i : Fin 14,∀ t∈rows i,t.2.1=0 ∨ t.2.1=1 := by
  decide +kernel

theorem first_eight (i : Fin 8) : rows ⟨i.val,by omega⟩=SmallLevelTwentySixGermFirstEight.rows i := by
  fin_cases i <;> rfl

theorem eval_replay_top (m : ℕ) (G : ℂ→Fin 320→ℂ) (z X Y Z W A B : ℂ)
    (i : Fin 14) :
    eval X Y Z W A B 1 (replayVector m G z) (rows i)=
      eval X Y Z W A B 1 (fun j => if j=0 then G z (topIndex 0) else G z (topIndex 1))
        (rows i) := by
  rw [SmallLevelLaurentTwoCoordinateGerms.eval_two_coordinates X Y Z W A B 1 _ _ (rows_support i)]
  rw [SmallLevelLaurentTwoCoordinateGerms.eval_two_coordinates X Y Z W A B 1 _ _ (rows_support i)]
  have h0 : replayVector m G z 0=G z (topIndex 0) := by
    simpa using replayVector_top m G z (0 : Fin 2)
  have h1 : replayVector m G z 1=G z (topIndex 1) := by
    simpa using replayVector_top m G z (1 : Fin 2)
  rw [h0,h1]
  simp


#print axioms rows_support
#print axioms eval_replay_top
end SmallLevelTwentySixGermFourteen
