module
public import QuantitativeArithmeticSmallLevelTwentySevenEntireSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenShiftSampleV1
public import QuantitativeArithmeticSmallLevelTwentySevenSignedSourceV1
public import QuantitativeArithmeticSmallLevelTwentySevenHeckeSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenKnownWordsTheoryV4
@[expose] public noncomputable section
/- Source-row certificates grouped by their shared mathematical context. -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 2048
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace QuantitativeArithmeticSmallLevelTwentySevenFourthSource
open QuantitativeArithmeticSevenLaurentRows FinitenessRamanujanSum
open QuantitativeArithmeticSmallLevelTwentySevenKnownWords
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
def raw0Poly : Poly := [((1/1:ℚ),0,(0,0,0,0,0,0,0)),((-1/1:ℚ),1,(0,0,0,0,0,0,0))]
def raw0Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨0,sourceWord49,0,1,(-1),0,0,0,0⟩
theorem raw0Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw0Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw0Spec]
  decide +kernel
theorem raw0Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw0Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw0Spec x y z w v := by
  norm_num [eval,monomial,raw0Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw0Spec] <;> ring
def raw0Observation : Fin 553 := ⟨52,by decide⟩
theorem raw0Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw0Observation)=v raw0Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw0Observation=[(1,raw0Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw0Observed
#print axioms raw0Valid
#print axioms raw0Row

def raw1Poly : Poly := [((1/1:ℚ),2,(0,0,0,0,0,0,0)),((-1/1:ℚ),3,(2,0,0,0,0,0,0))]
def raw1Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1,sourceWord144,2,3,2,2,0,0,0⟩
theorem raw1Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1Spec]
  decide +kernel
theorem raw1Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1Spec x y z w v := by
  norm_num [eval,monomial,raw1Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1Spec] <;> ring
def raw1Observation : Fin 553 := ⟨27,by decide⟩
theorem raw1Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1Observation)=v raw1Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1Observation=[(1,raw1Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1Observed
#print axioms raw1Valid
#print axioms raw1Row

def raw3Poly : Poly := [((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),7,(0,0,2,0,0,0,0))]
def raw3Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨3,sourceWord144,6,7,2,0,0,2,0⟩
theorem raw3Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw3Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw3Spec]
  decide +kernel
theorem raw3Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw3Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw3Spec x y z w v := by
  norm_num [eval,monomial,raw3Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw3Spec] <;> ring
def raw3Observation : Fin 553 := ⟨55,by decide⟩
theorem raw3Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw3Observation)=v raw3Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw3Observation=[(1,raw3Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw3Observed
#print axioms raw3Valid
#print axioms raw3Row

def raw9Poly : Poly := [((-1/1:ℚ),6,(0,0,0,0,0,0,0)),((1/1:ℚ),16,(0,0,0,0,0,0,0))]
def raw9Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨9,sourceWord101,16,6,1,0,0,0,0⟩
theorem raw9Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw9Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw9Spec]
  decide +kernel
theorem raw9Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw9Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw9Spec x y z w v := by
  norm_num [eval,monomial,raw9Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw9Spec] <;> ring
def raw9Observation : Fin 553 := ⟨6,by decide⟩
theorem raw9Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw9Observation)=v raw9Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw9Observation=[(1,raw9Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw9Observed
#print axioms raw9Valid
#print axioms raw9Row

def raw10Poly : Poly := [((1/1:ℚ),17,(0,0,0,0,0,0,0)),((-1/1:ℚ),18,((-2),0,0,0,0,0,0))]
def raw10Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨10,sourceWord101,17,18,1,(-2),0,0,0⟩
theorem raw10Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw10Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw10Spec]
  decide +kernel
theorem raw10Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw10Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw10Spec x y z w v := by
  norm_num [eval,monomial,raw10Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw10Spec] <;> ring
def raw10Observation : Fin 553 := ⟨8,by decide⟩
theorem raw10Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw10Observation)=v raw10Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw10Observation=[(1,raw10Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw10Observed
#print axioms raw10Valid
#print axioms raw10Row

def raw11Poly : Poly := [((1/1:ℚ),19,(0,0,0,0,0,0,0)),((-1/1:ℚ),20,(2,0,(-2),0,0,0,0))]
def raw11Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨11,sourceWord101,19,20,1,2,0,(-2),0⟩
theorem raw11Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw11Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw11Spec]
  decide +kernel
theorem raw11Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw11Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw11Spec x y z w v := by
  norm_num [eval,monomial,raw11Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw11Spec] <;> ring
def raw11Observation : Fin 553 := ⟨9,by decide⟩
theorem raw11Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw11Observation)=v raw11Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw11Observation=[(1,raw11Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw11Observed
#print axioms raw11Valid
#print axioms raw11Row

def raw16Poly : Poly := [((1/1:ℚ),27,(0,0,0,0,0,0,0)),((-1/1:ℚ),28,(0,0,(-2),0,0,0,0))]
def raw16Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨16,sourceWord101,27,28,0,0,0,(-2),0⟩
theorem raw16Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw16Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw16Spec]
  decide +kernel
theorem raw16Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw16Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw16Spec x y z w v := by
  norm_num [eval,monomial,raw16Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw16Spec] <;> ring
def raw16Observation : Fin 553 := ⟨48,by decide⟩
theorem raw16Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw16Observation)=v raw16Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw16Observation=[(1,raw16Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw16Observed
#print axioms raw16Valid
#print axioms raw16Row

def raw18Poly : Poly := [((-1/1:ℚ),2,((-2),0,0,0,0,0,0)),((1/1:ℚ),3,(0,0,0,0,0,0,0))]
def raw18Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨18,sourceWord101,3,2,1,(-2),0,0,0⟩
theorem raw18Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw18Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw18Spec]
  decide +kernel
theorem raw18Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw18Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw18Spec x y z w v := by
  norm_num [eval,monomial,raw18Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw18Spec] <;> ring
def raw18Observation : Fin 553 := ⟨0,by decide⟩
theorem raw18Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw18Observation)=v raw18Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw18Observation=[(1,raw18Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw18Observed
#print axioms raw18Valid
#print axioms raw18Row

def raw19Poly : Poly := [((1/1:ℚ),31,(0,0,0,0,0,0,0)),((-1/1:ℚ),32,(0,0,0,0,0,0,0))]
def raw19Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨19,sourceWord101,31,32,1,0,0,0,0⟩
theorem raw19Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw19Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw19Spec]
  decide +kernel
theorem raw19Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw19Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw19Spec x y z w v := by
  norm_num [eval,monomial,raw19Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw19Spec] <;> ring
def raw19Observation : Fin 553 := ⟨2,by decide⟩
theorem raw19Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw19Observation)=v raw19Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw19Observation=[(1,raw19Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw19Observed
#print axioms raw19Valid
#print axioms raw19Row

def raw20Poly : Poly := [((1/1:ℚ),33,(0,0,0,0,0,0,0)),((-1/1:ℚ),34,(2,0,0,0,0,0,0))]
def raw20Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨20,sourceWord101,33,34,1,2,0,0,0⟩
theorem raw20Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw20Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw20Spec]
  decide +kernel
theorem raw20Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw20Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw20Spec x y z w v := by
  norm_num [eval,monomial,raw20Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw20Spec] <;> ring
def raw20Observation : Fin 553 := ⟨3,by decide⟩
theorem raw20Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw20Observation)=v raw20Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw20Observation=[(1,raw20Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw20Observed
#print axioms raw20Valid
#print axioms raw20Row

def raw22Poly : Poly := [((1/1:ℚ),37,(0,0,0,0,0,0,0)),((-1/1:ℚ),38,(0,0,2,0,0,0,0))]
def raw22Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨22,sourceWord101,37,38,1,0,0,2,0⟩
theorem raw22Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw22Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw22Spec]
  decide +kernel
theorem raw22Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw22Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw22Spec x y z w v := by
  norm_num [eval,monomial,raw22Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw22Spec] <;> ring
def raw22Observation : Fin 553 := ⟨61,by decide⟩
theorem raw22Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw22Observation)=v raw22Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw22Observation=[(1,raw22Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw22Observed
#print axioms raw22Valid
#print axioms raw22Row

def raw24Poly : Poly := [((-1/1:ℚ),1,(0,0,0,0,0,0,0)),((1/1:ℚ),31,(0,0,0,0,0,0,0))]
def raw24Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨24,sourceWord66,31,1,(-1),0,0,0,0⟩
theorem raw24Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw24Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw24Spec]
  decide +kernel
theorem raw24Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw24Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw24Spec x y z w v := by
  norm_num [eval,monomial,raw24Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw24Spec] <;> ring
def raw24Observation : Fin 553 := ⟨52,by decide⟩
theorem raw24Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw24Observation)=v raw24Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw24Observation=[(1,raw24Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw24Observed
#print axioms raw24Valid
#print axioms raw24Row

def raw26Poly : Poly := [((-1/1:ℚ),7,((-2),0,2,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0))]
def raw26Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨26,sourceWord117,42,7,0,(-2),0,2,0⟩
theorem raw26Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw26Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw26Spec]
  decide +kernel
theorem raw26Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw26Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw26Spec x y z w v := by
  norm_num [eval,monomial,raw26Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw26Spec] <;> ring
def raw26Observation : Fin 553 := ⟨55,by decide⟩
theorem raw26Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw26Observation)=v raw26Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw26Observation=[(1,raw26Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw26Observed
#print axioms raw26Valid
#print axioms raw26Row

def raw27Poly : Poly := [((1/1:ℚ),1,(0,0,0,0,0,0,0)),((-1/1:ℚ),31,(0,0,0,0,0,0,0))]
def raw27Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨27,sourceWord117,1,31,0,0,0,0,0⟩
theorem raw27Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw27Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw27Spec]
  decide +kernel
theorem raw27Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw27Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw27Spec x y z w v := by
  norm_num [eval,monomial,raw27Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw27Spec] <;> ring
def raw27Observation : Fin 553 := ⟨28,by decide⟩
theorem raw27Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw27Observation)=v raw27Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw27Observation=[(1,raw27Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw27Observed
#print axioms raw27Valid
#print axioms raw27Row

def raw30Poly : Poly := [((-1/1:ℚ),16,(0,0,(-2),0,0,0,0)),((1/1:ℚ),47,(0,0,0,0,0,0,0))]
def raw30Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨30,sourceWord117,47,16,0,0,0,(-2),0⟩
theorem raw30Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw30Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw30Spec]
  decide +kernel
theorem raw30Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw30Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw30Spec x y z w v := by
  norm_num [eval,monomial,raw30Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw30Spec] <;> ring
def raw30Observation : Fin 553 := ⟨24,by decide⟩
theorem raw30Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw30Observation)=v raw30Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw30Observation=[(1,raw30Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw30Observed
#print axioms raw30Valid
#print axioms raw30Row

def raw31Poly : Poly := [((-1/1:ℚ),24,((-2),0,0,0,0,0,0)),((1/1:ℚ),30,(0,0,0,0,0,0,0))]
def raw31Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨31,sourceWord117,30,24,0,(-2),0,0,0⟩
theorem raw31Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw31Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw31Spec]
  decide +kernel
theorem raw31Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw31Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw31Spec x y z w v := by
  norm_num [eval,monomial,raw31Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw31Spec] <;> ring
def raw31Observation : Fin 553 := ⟨26,by decide⟩
theorem raw31Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw31Observation)=v raw31Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw31Observation=[(1,raw31Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw31Observed
#print axioms raw31Valid
#print axioms raw31Row

def raw38Poly : Poly := [((1/1:ℚ),55,(0,0,0,0,0,0,0)),((-1/1:ℚ),56,((-2),0,2,0,0,0,0))]
def raw38Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨38,sourceWord50,55,56,0,(-2),0,2,0⟩
theorem raw38Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw38Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw38Spec]
  decide +kernel
theorem raw38Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw38Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw38Spec x y z w v := by
  norm_num [eval,monomial,raw38Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw38Spec] <;> ring
def raw38Observation : Fin 553 := ⟨69,by decide⟩
theorem raw38Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw38Observation)=v raw38Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw38Observation=[(1,raw38Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw38Observed
#print axioms raw38Valid
#print axioms raw38Row

def raw40Poly : Poly := [((1/1:ℚ),28,(0,0,0,0,0,0,0)),((-1/1:ℚ),33,(0,0,0,0,0,0,0))]
def raw40Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨40,sourceWord50,28,33,0,0,0,0,0⟩
theorem raw40Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw40Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw40Spec]
  decide +kernel
theorem raw40Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw40Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw40Spec x y z w v := by
  norm_num [eval,monomial,raw40Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw40Spec] <;> ring
def raw40Observation : Fin 553 := ⟨30,by decide⟩
theorem raw40Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw40Observation)=v raw40Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw40Observation=[(1,raw40Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw40Observed
#print axioms raw40Valid
#print axioms raw40Row

def raw41Poly : Poly := [((1/1:ℚ),57,(0,0,0,0,0,0,0)),((-1/1:ℚ),58,((-2),0,0,0,0,0,0))]
def raw41Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨41,sourceWord50,57,58,0,(-2),0,0,0⟩
theorem raw41Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw41Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw41Spec]
  decide +kernel
theorem raw41Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw41Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw41Spec x y z w v := by
  norm_num [eval,monomial,raw41Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw41Spec] <;> ring
def raw41Observation : Fin 553 := ⟨32,by decide⟩
theorem raw41Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw41Observation)=v raw41Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw41Observation=[(1,raw41Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw41Observed
#print axioms raw41Valid
#print axioms raw41Row

def raw42Poly : Poly := [((1/1:ℚ),59,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(2,0,(-2),0,0,0,0))]
def raw42Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨42,sourceWord50,59,60,0,2,0,(-2),0⟩
theorem raw42Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw42Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw42Spec]
  decide +kernel
theorem raw42Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw42Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw42Spec x y z w v := by
  norm_num [eval,monomial,raw42Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw42Spec] <;> ring
def raw42Observation : Fin 553 := ⟨33,by decide⟩
theorem raw42Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw42Observation)=v raw42Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw42Observation=[(1,raw42Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw42Observed
#print axioms raw42Valid
#print axioms raw42Row

def raw47Poly : Poly := [((-1/1:ℚ),50,(0,0,(-2),0,0,0,0)),((1/1:ℚ),64,(0,0,0,0,0,0,0))]
def raw47Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨47,sourceWord50,64,50,0,0,0,(-2),0⟩
theorem raw47Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw47Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw47Spec]
  decide +kernel
theorem raw47Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw47Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw47Spec x y z w v := by
  norm_num [eval,monomial,raw47Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw47Spec] <;> ring
def raw47Observation : Fin 553 := ⟨18,by decide⟩
theorem raw47Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw47Observation)=v raw47Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw47Observation=[(1,raw47Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw47Observed
#print axioms raw47Valid
#print axioms raw47Row

def raw49Poly : Poly := [((-1/1:ℚ),16,((-2),0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0))]
def raw49Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨49,sourceWord50,42,16,0,(-2),0,0,0⟩
theorem raw49Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw49Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw49Spec]
  decide +kernel
theorem raw49Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw49Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw49Spec x y z w v := by
  norm_num [eval,monomial,raw49Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw49Spec] <;> ring
def raw49Observation : Fin 553 := ⟨24,by decide⟩
theorem raw49Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw49Observation)=v raw49Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw49Observation=[(1,raw49Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw49Observed
#print axioms raw49Valid
#print axioms raw49Row

def raw50Poly : Poly := [((1/1:ℚ),1,(0,0,0,0,0,0,0)),((-1/1:ℚ),24,(0,0,0,0,0,0,0))]
def raw50Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨50,sourceWord50,1,24,0,0,0,0,0⟩
theorem raw50Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw50Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw50Spec]
  decide +kernel
theorem raw50Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw50Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw50Spec x y z w v := by
  norm_num [eval,monomial,raw50Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw50Spec] <;> ring
def raw50Observation : Fin 553 := ⟨26,by decide⟩
theorem raw50Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw50Observation)=v raw50Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw50Observation=[(1,raw50Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw50Observed
#print axioms raw50Valid
#print axioms raw50Row

def raw51Poly : Poly := [((-1/1:ℚ),0,(0,0,0,0,0,0,0)),((1/1:ℚ),31,(0,0,0,0,0,0,0))]
def raw51Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨51,sourceWord179,31,0,(-2),0,0,0,0⟩
theorem raw51Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw51Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw51Spec]
  decide +kernel
theorem raw51Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw51Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw51Spec x y z w v := by
  norm_num [eval,monomial,raw51Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw51Spec] <;> ring
def raw51Observation : Fin 553 := ⟨50,by decide⟩
theorem raw51Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw51Observation)=v raw51Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw51Observation=[(1,raw51Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw51Observed
#print axioms raw51Valid
#print axioms raw51Row

def raw52Poly : Poly := [((-1/1:ℚ),31,(0,0,0,0,0,0,0)),((1/1:ℚ),32,(0,0,0,0,0,0,0))]
def raw52Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨52,sourceWord172,32,31,0,0,0,0,0⟩
theorem raw52Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw52Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw52Spec]
  decide +kernel
theorem raw52Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw52Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw52Spec x y z w v := by
  norm_num [eval,monomial,raw52Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw52Spec] <;> ring
def raw52Observation : Fin 553 := ⟨28,by decide⟩
theorem raw52Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw52Observation)=v raw52Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw52Observation=[(1,raw52Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw52Observed
#print axioms raw52Valid
#print axioms raw52Row

def raw68Poly : Poly := [((1/1:ℚ),4,(0,0,0,0,0,0,0)),((-1/1:ℚ),32,((-2),0,0,0,0,0,0))]
def raw68Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨68,sourceWord130,4,32,2,(-2),0,0,0⟩
theorem raw68Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw68Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw68Spec]
  decide +kernel
theorem raw68Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw68Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw68Spec x y z w v := by
  norm_num [eval,monomial,raw68Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw68Spec] <;> ring
def raw68Observation : Fin 553 := ⟨2,by decide⟩
theorem raw68Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw68Observation)=v raw68Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw68Observation=[(1,raw68Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw68Observed
#print axioms raw68Valid
#print axioms raw68Row

def raw69Poly : Poly := [((-1/1:ℚ),34,(2,0,(-2),0,0,0,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0))]
def raw69Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨69,sourceWord130,48,34,2,2,0,(-2),0⟩
theorem raw69Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw69Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw69Spec]
  decide +kernel
theorem raw69Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw69Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw69Spec x y z w v := by
  norm_num [eval,monomial,raw69Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw69Spec] <;> ring
def raw69Observation : Fin 553 := ⟨3,by decide⟩
theorem raw69Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw69Observation)=v raw69Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw69Observation=[(1,raw69Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw69Observed
#print axioms raw69Valid
#print axioms raw69Row

def raw70Poly : Poly := [((-1/1:ℚ),18,(0,0,(-2),0,0,0,0)),((1/1:ℚ),49,(0,0,0,0,0,0,0))]
def raw70Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨70,sourceWord130,49,18,2,0,0,(-2),0⟩
theorem raw70Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw70Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw70Spec]
  decide +kernel
theorem raw70Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw70Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw70Spec x y z w v := by
  norm_num [eval,monomial,raw70Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw70Spec] <;> ring
def raw70Observation : Fin 553 := ⟨8,by decide⟩
theorem raw70Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw70Observation)=v raw70Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw70Observation=[(1,raw70Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw70Observed
#print axioms raw70Valid
#print axioms raw70Row

def raw71Poly : Poly := [((-1/1:ℚ),50,((-2),0,(-2),0,0,0,0)),((1/1:ℚ),51,(0,0,0,0,0,0,0))]
def raw71Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨71,sourceWord130,51,50,2,(-2),0,(-2),0⟩
theorem raw71Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw71Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw71Spec]
  decide +kernel
theorem raw71Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw71Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw71Spec x y z w v := by
  norm_num [eval,monomial,raw71Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw71Spec] <;> ring
def raw71Observation : Fin 553 := ⟨18,by decide⟩
theorem raw71Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw71Observation)=v raw71Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw71Observation=[(1,raw71Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw71Observed
#print axioms raw71Valid
#print axioms raw71Row

def raw73Poly : Poly := [((-1/1:ℚ),58,((-2),0,(-2),0,0,0,0)),((1/1:ℚ),67,(0,0,0,0,0,0,0))]
def raw73Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨73,sourceWord130,67,58,1,(-2),0,(-2),0⟩
theorem raw73Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw73Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw73Spec]
  decide +kernel
theorem raw73Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw73Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw73Spec x y z w v := by
  norm_num [eval,monomial,raw73Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw73Spec] <;> ring
def raw73Observation : Fin 553 := ⟨32,by decide⟩
theorem raw73Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw73Observation)=v raw73Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw73Observation=[(1,raw73Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw73Observed
#print axioms raw73Valid
#print axioms raw73Row

def raw74Poly : Poly := [((1/1:ℚ),68,(0,0,0,0,0,0,0)),((-1/1:ℚ),69,(0,0,(-2),0,0,0,0))]
def raw74Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨74,sourceWord130,68,69,1,0,0,(-2),0⟩
theorem raw74Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw74Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw74Spec]
  decide +kernel
theorem raw74Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw74Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw74Spec x y z w v := by
  norm_num [eval,monomial,raw74Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw74Spec] <;> ring
def raw74Observation : Fin 553 := ⟨42,by decide⟩
theorem raw74Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw74Observation)=v raw74Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw74Observation=[(1,raw74Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw74Observed
#print axioms raw74Valid
#print axioms raw74Row

def raw76Poly : Poly := [((-1/1:ℚ),28,((-2),0,0,0,0,0,0)),((1/1:ℚ),34,(0,0,0,0,0,0,0))]
def raw76Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨76,sourceWord130,34,28,1,(-2),0,0,0⟩
theorem raw76Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw76Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw76Spec]
  decide +kernel
theorem raw76Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw76Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw76Spec x y z w v := by
  norm_num [eval,monomial,raw76Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw76Spec] <;> ring
def raw76Observation : Fin 553 := ⟨48,by decide⟩
theorem raw76Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw76Observation)=v raw76Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw76Observation=[(1,raw76Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw76Observed
#print axioms raw76Valid
#print axioms raw76Row

def raw77Poly : Poly := [((-1/1:ℚ),0,(0,0,0,0,0,0,0)),((1/1:ℚ),72,(0,0,0,0,0,0,0))]
def raw77Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨77,sourceWord130,72,0,1,0,0,0,0⟩
theorem raw77Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw77Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw77Spec]
  decide +kernel
theorem raw77Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw77Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw77Spec x y z w v := by
  norm_num [eval,monomial,raw77Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw77Spec] <;> ring
def raw77Observation : Fin 553 := ⟨50,by decide⟩
theorem raw77Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw77Observation)=v raw77Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw77Observation=[(1,raw77Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw77Observed
#print axioms raw77Valid
#print axioms raw77Row

def raw78Poly : Poly := [((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),42,(2,0,0,0,0,0,0))]
def raw78Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨78,sourceWord130,6,42,1,2,0,0,0⟩
theorem raw78Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw78Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw78Spec]
  decide +kernel
theorem raw78Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw78Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw78Spec x y z w v := by
  norm_num [eval,monomial,raw78Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw78Spec] <;> ring
def raw78Observation : Fin 553 := ⟨51,by decide⟩
theorem raw78Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw78Observation)=v raw78Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw78Observation=[(1,raw78Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw78Observed
#print axioms raw78Valid
#print axioms raw78Row

def raw82Poly : Poly := [((1/1:ℚ),0,(0,0,0,0,0,0,0)),((-1/1:ℚ),31,(0,0,0,0,0,0,0))]
def raw82Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨82,sourceWord156,0,31,0,0,0,0,0⟩
theorem raw82Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw82Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw82Spec]
  decide +kernel
theorem raw82Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw82Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw82Spec x y z w v := by
  norm_num [eval,monomial,raw82Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw82Spec] <;> ring
def raw82Observation : Fin 553 := ⟨28,by decide⟩
theorem raw82Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw82Observation)=v raw82Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw82Observation=[(1,raw82Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw82Observed
#print axioms raw82Valid
#print axioms raw82Row

def raw83Poly : Poly := [((-1/1:ℚ),72,(0,0,(-2),0,0,0,0)),((1/1:ℚ),78,(0,0,0,0,0,0,0))]
def raw83Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨83,sourceWord10,78,72,0,0,0,(-2),0⟩
theorem raw83Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw83Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw83Spec]
  decide +kernel
theorem raw83Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw83Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw83Spec x y z w v := by
  norm_num [eval,monomial,raw83Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw83Spec] <;> ring
def raw83Observation : Fin 553 := ⟨4,by decide⟩
theorem raw83Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw83Observation)=v raw83Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw83Observation=[(1,raw83Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw83Observed
#print axioms raw83Valid
#print axioms raw83Row

def raw85Poly : Poly := [((-1/1:ℚ),28,(0,0,(-2),0,0,0,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0))]
def raw85Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨85,sourceWord10,48,28,(-1),0,0,(-2),0⟩
theorem raw85Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw85Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw85Spec]
  decide +kernel
theorem raw85Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw85Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw85Spec x y z w v := by
  norm_num [eval,monomial,raw85Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw85Spec] <;> ring
def raw85Observation : Fin 553 := ⟨48,by decide⟩
theorem raw85Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw85Observation)=v raw85Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw85Observation=[(1,raw85Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw85Observed
#print axioms raw85Valid
#print axioms raw85Row

def raw86Poly : Poly := [((-1/1:ℚ),1,(0,0,0,0,0,0,0)),((1/1:ℚ),32,(0,0,0,0,0,0,0))]
def raw86Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨86,sourceWord10,32,1,(-1),0,0,0,0⟩
theorem raw86Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw86Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw86Spec]
  decide +kernel
theorem raw86Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw86Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw86Spec x y z w v := by
  norm_num [eval,monomial,raw86Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw86Spec] <;> ring
def raw86Observation : Fin 553 := ⟨52,by decide⟩
theorem raw86Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw86Observation)=v raw86Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw86Observation=[(1,raw86Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw86Observed
#print axioms raw86Valid
#print axioms raw86Row

def raw105Poly : Poly := [((1/1:ℚ),28,(0,0,0,0,0,0,0)),((-1/1:ℚ),34,(2,0,0,0,0,0,0))]
def raw105Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨105,sourceWord77,28,34,(-1),2,0,0,0⟩
theorem raw105Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw105Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw105Spec]
  decide +kernel
theorem raw105Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw105Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw105Spec x y z w v := by
  norm_num [eval,monomial,raw105Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw105Spec] <;> ring
def raw105Observation : Fin 553 := ⟨3,by decide⟩
theorem raw105Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw105Observation)=v raw105Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw105Observation=[(1,raw105Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw105Observed
#print axioms raw105Valid
#print axioms raw105Row

def raw106Poly : Poly := [((1/1:ℚ),0,(0,0,0,0,0,0,0)),((-1/1:ℚ),72,(0,0,0,0,0,0,0))]
def raw106Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨106,sourceWord77,0,72,(-1),0,0,0,0⟩
theorem raw106Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw106Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw106Spec]
  decide +kernel
theorem raw106Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw106Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw106Spec x y z w v := by
  norm_num [eval,monomial,raw106Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw106Spec] <;> ring
def raw106Observation : Fin 553 := ⟨4,by decide⟩
theorem raw106Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw106Observation)=v raw106Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw106Observation=[(1,raw106Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw106Observed
#print axioms raw106Valid
#print axioms raw106Row

def raw107Poly : Poly := [((-1/1:ℚ),6,((-2),0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0))]
def raw107Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨107,sourceWord77,42,6,(-1),(-2),0,0,0⟩
theorem raw107Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw107Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw107Spec]
  decide +kernel
theorem raw107Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw107Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw107Spec x y z w v := by
  norm_num [eval,monomial,raw107Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw107Spec] <;> ring
def raw107Observation : Fin 553 := ⟨6,by decide⟩
theorem raw107Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw107Observation)=v raw107Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw107Observation=[(1,raw107Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw107Observed
#print axioms raw107Valid
#print axioms raw107Row

def raw108Poly : Poly := [((-1/1:ℚ),73,(2,0,(-2),0,0,0,0)),((1/1:ℚ),74,(0,0,0,0,0,0,0))]
def raw108Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨108,sourceWord77,74,73,(-1),2,0,(-2),0⟩
theorem raw108Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw108Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw108Spec]
  decide +kernel
theorem raw108Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw108Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw108Spec x y z w v := by
  norm_num [eval,monomial,raw108Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw108Spec] <;> ring
def raw108Observation : Fin 553 := ⟨7,by decide⟩
theorem raw108Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw108Observation)=v raw108Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw108Observation=[(1,raw108Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw108Observed
#print axioms raw108Valid
#print axioms raw108Row

def raw109Poly : Poly := [((-1/1:ℚ),75,(0,0,(-2),0,0,0,0)),((1/1:ℚ),76,(0,0,0,0,0,0,0))]
def raw109Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨109,sourceWord77,76,75,(-1),0,0,(-2),0⟩
theorem raw109Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw109Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw109Spec]
  decide +kernel
theorem raw109Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw109Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw109Spec x y z w v := by
  norm_num [eval,monomial,raw109Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw109Spec] <;> ring
def raw109Observation : Fin 553 := ⟨12,by decide⟩
theorem raw109Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw109Observation)=v raw109Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw109Observation=[(1,raw109Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw109Observed
#print axioms raw109Valid
#print axioms raw109Row

def raw112Poly : Poly := [((-1/1:ℚ),37,((-2),0,(-2),0,0,0,0)),((1/1:ℚ),79,(0,0,0,0,0,0,0))]
def raw112Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨112,sourceWord77,79,37,(-2),(-2),0,(-2),0⟩
theorem raw112Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw112Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw112Spec]
  decide +kernel
theorem raw112Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw112Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw112Spec x y z w v := by
  norm_num [eval,monomial,raw112Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw112Spec] <;> ring
def raw112Observation : Fin 553 := ⟨36,by decide⟩
theorem raw112Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw112Observation)=v raw112Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw112Observation=[(1,raw112Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw112Observed
#print axioms raw112Valid
#print axioms raw112Row

def raw114Poly : Poly := [((-1/1:ℚ),42,(2,0,(-2),0,0,0,0)),((1/1:ℚ),47,(0,0,0,0,0,0,0))]
def raw114Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨114,sourceWord77,47,42,(-2),2,0,(-2),0⟩
theorem raw114Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw114Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw114Spec]
  decide +kernel
theorem raw114Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw114Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw114Spec x y z w v := by
  norm_num [eval,monomial,raw114Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw114Spec] <;> ring
def raw114Observation : Fin 553 := ⟨51,by decide⟩
theorem raw114Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw114Observation)=v raw114Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw114Observation=[(1,raw114Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw114Observed
#print axioms raw114Valid
#print axioms raw114Row

def raw115Poly : Poly := [((-1/1:ℚ),1,((-2),0,0,0,0,0,0)),((1/1:ℚ),30,(0,0,0,0,0,0,0))]
def raw115Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨115,sourceWord77,30,1,(-2),(-2),0,0,0⟩
theorem raw115Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw115Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw115Spec]
  decide +kernel
theorem raw115Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw115Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw115Spec x y z w v := by
  norm_num [eval,monomial,raw115Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw115Spec] <;> ring
def raw115Observation : Fin 553 := ⟨52,by decide⟩
theorem raw115Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw115Observation)=v raw115Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw115Observation=[(1,raw115Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw115Observed
#print axioms raw115Valid
#print axioms raw115Row

def raw118Poly : Poly := [((1/1:ℚ),24,(0,0,0,0,0,0,0)),((-1/1:ℚ),32,(0,0,0,0,0,0,0))]
def raw118Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨118,sourceWord33,24,32,0,0,0,0,0⟩
theorem raw118Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw118Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw118Spec]
  decide +kernel
theorem raw118Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw118Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw118Spec x y z w v := by
  norm_num [eval,monomial,raw118Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw118Spec] <;> ring
def raw118Observation : Fin 553 := ⟨2,by decide⟩
theorem raw118Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw118Observation)=v raw118Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw118Observation=[(1,raw118Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw118Observed
#print axioms raw118Valid
#print axioms raw118Row

def raw122Poly : Poly := [((-1/1:ℚ),2,((-2),0,0,0,0,0,0)),((1/1:ℚ),3,(0,0,0,0,0,0,0))]
def raw122Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨122,sourceWord33,3,2,0,(-2),0,0,0⟩
theorem raw122Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw122Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw122Spec]
  decide +kernel
theorem raw122Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw122Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw122Spec x y z w v := by
  norm_num [eval,monomial,raw122Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw122Spec] <;> ring
def raw122Observation : Fin 553 := ⟨0,by decide⟩
theorem raw122Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw122Observation)=v raw122Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw122Observation=[(1,raw122Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw122Observed
#print axioms raw122Valid
#print axioms raw122Row

def raw145Poly : Poly := [((-1/1:ℚ),6,((-2),0,(-2),0,0,0,0)),((1/1:ℚ),84,(0,0,0,0,0,0,0))]
def raw145Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨145,sourceWord9,84,6,0,(-2),0,(-2),0⟩
theorem raw145Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw145Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw145Spec]
  decide +kernel
theorem raw145Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw145Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw145Spec x y z w v := by
  norm_num [eval,monomial,raw145Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw145Spec] <;> ring
def raw145Observation : Fin 553 := ⟨6,by decide⟩
theorem raw145Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw145Observation)=v raw145Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw145Observation=[(1,raw145Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw145Observed
#print axioms raw145Valid
#print axioms raw145Row

def raw146Poly : Poly := [((-1/1:ℚ),0,(0,0,(-2),0,0,0,0)),((1/1:ℚ),78,(0,0,0,0,0,0,0))]
def raw146Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨146,sourceWord9,78,0,(-1),0,0,(-2),0⟩
theorem raw146Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw146Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw146Spec]
  decide +kernel
theorem raw146Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw146Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw146Spec x y z w v := by
  norm_num [eval,monomial,raw146Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw146Spec] <;> ring
def raw146Observation : Fin 553 := ⟨50,by decide⟩
theorem raw146Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw146Observation)=v raw146Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw146Observation=[(1,raw146Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw146Observed
#print axioms raw146Valid
#print axioms raw146Row

def raw147Poly : Poly := [((-1/1:ℚ),1,((-2),0,0,0,0,0,0)),((1/1:ℚ),4,(0,0,0,0,0,0,0))]
def raw147Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨147,sourceWord9,4,1,(-1),(-2),0,0,0⟩
theorem raw147Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw147Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw147Spec]
  decide +kernel
theorem raw147Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw147Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw147Spec x y z w v := by
  norm_num [eval,monomial,raw147Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw147Spec] <;> ring
def raw147Observation : Fin 553 := ⟨52,by decide⟩
theorem raw147Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw147Observation)=v raw147Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw147Observation=[(1,raw147Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw147Observed
#print axioms raw147Valid
#print axioms raw147Row

def raw151Poly : Poly := [((1/1:ℚ),50,(0,0,0,0,0,0,0)),((-1/1:ℚ),64,(0,0,2,0,0,0,0))]
def raw151Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨151,sourceWord99,50,64,(-2),0,0,2,0⟩
theorem raw151Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw151Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw151Spec]
  decide +kernel
theorem raw151Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw151Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw151Spec x y z w v := by
  norm_num [eval,monomial,raw151Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw151Spec] <;> ring
def raw151Observation : Fin 553 := ⟨80,by decide⟩
theorem raw151Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw151Observation)=v raw151Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw151Observation=[(1,raw151Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw151Observed
#print axioms raw151Valid
#print axioms raw151Row

def raw153Poly : Poly := [((1/1:ℚ),16,(0,0,0,0,0,0,0)),((-1/1:ℚ),42,(2,0,0,0,0,0,0))]
def raw153Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨153,sourceWord99,16,42,(-2),2,0,0,0⟩
theorem raw153Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw153Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw153Spec]
  decide +kernel
theorem raw153Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw153Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw153Spec x y z w v := by
  norm_num [eval,monomial,raw153Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw153Spec] <;> ring
def raw153Observation : Fin 553 := ⟨51,by decide⟩
theorem raw153Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw153Observation)=v raw153Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw153Observation=[(1,raw153Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw153Observed
#print axioms raw153Valid
#print axioms raw153Row

def raw155Poly : Poly := [((-1/1:ℚ),2,((-2),0,0,0,0,0,0)),((1/1:ℚ),3,(0,0,0,0,0,0,0))]
def raw155Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨155,sourceWord99,3,2,(-1),(-2),0,0,0⟩
theorem raw155Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw155Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw155Spec]
  decide +kernel
theorem raw155Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw155Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw155Spec x y z w v := by
  norm_num [eval,monomial,raw155Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw155Spec] <;> ring
def raw155Observation : Fin 553 := ⟨0,by decide⟩
theorem raw155Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw155Observation)=v raw155Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw155Observation=[(1,raw155Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw155Observed
#print axioms raw155Valid
#print axioms raw155Row

def raw157Poly : Poly := [((-1/1:ℚ),6,(0,0,(-2),0,0,0,0)),((1/1:ℚ),7,(0,0,0,0,0,0,0))]
def raw157Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨157,sourceWord99,7,6,(-1),0,0,(-2),0⟩
theorem raw157Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw157Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw157Spec]
  decide +kernel
theorem raw157Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw157Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw157Spec x y z w v := by
  norm_num [eval,monomial,raw157Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw157Spec] <;> ring
def raw157Observation : Fin 553 := ⟨6,by decide⟩
theorem raw157Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw157Observation)=v raw157Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw157Observation=[(1,raw157Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw157Observed
#print axioms raw157Valid
#print axioms raw157Row

def raw160Poly : Poly := [((-1/1:ℚ),33,((-2),0,(-2),0,0,0,0)),((1/1:ℚ),52,(0,0,0,0,0,0,0))]
def raw160Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨160,sourceWord99,52,33,(-2),(-2),0,(-2),0⟩
theorem raw160Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw160Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw160Spec]
  decide +kernel
theorem raw160Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw160Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw160Spec x y z w v := by
  norm_num [eval,monomial,raw160Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw160Spec] <;> ring
def raw160Observation : Fin 553 := ⟨30,by decide⟩
theorem raw160Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw160Observation)=v raw160Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw160Observation=[(1,raw160Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw160Observed
#print axioms raw160Valid
#print axioms raw160Row

def raw162Poly : Poly := [((-1/1:ℚ),55,(2,0,(-2),0,0,0,0)),((1/1:ℚ),56,(0,0,0,0,0,0,0))]
def raw162Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨162,sourceWord99,56,55,(-2),2,0,(-2),0⟩
theorem raw162Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw162Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw162Spec]
  decide +kernel
theorem raw162Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw162Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw162Spec x y z w v := by
  norm_num [eval,monomial,raw162Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw162Spec] <;> ring
def raw162Observation : Fin 553 := ⟨45,by decide⟩
theorem raw162Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw162Observation)=v raw162Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw162Observation=[(1,raw162Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw162Observed
#print axioms raw162Valid
#print axioms raw162Row

def raw163Poly : Poly := [((-1/1:ℚ),39,((-2),0,0,0,0,0,0)),((1/1:ℚ),44,(0,0,0,0,0,0,0))]
def raw163Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨163,sourceWord99,44,39,(-2),(-2),0,0,0⟩
theorem raw163Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw163Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw163Spec]
  decide +kernel
theorem raw163Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw163Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw163Spec x y z w v := by
  norm_num [eval,monomial,raw163Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw163Spec] <;> ring
def raw163Observation : Fin 553 := ⟨46,by decide⟩
theorem raw163Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw163Observation)=v raw163Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw163Observation=[(1,raw163Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw163Observed
#print axioms raw163Valid
#print axioms raw163Row

def raw164Poly : Poly := [((-1/1:ℚ),28,(0,0,0,0,0,0,0)),((1/1:ℚ),33,(0,0,0,0,0,0,0))]
def raw164Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨164,sourceWord99,33,28,(-2),0,0,0,0⟩
theorem raw164Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw164Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw164Spec]
  decide +kernel
theorem raw164Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw164Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw164Spec x y z w v := by
  norm_num [eval,monomial,raw164Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw164Spec] <;> ring
def raw164Observation : Fin 553 := ⟨48,by decide⟩
theorem raw164Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw164Observation)=v raw164Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw164Observation=[(1,raw164Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw164Observed
#print axioms raw164Valid
#print axioms raw164Row

def raw165Poly : Poly := [((-1/1:ℚ),57,(2,0,0,0,0,0,0)),((1/1:ℚ),58,(0,0,0,0,0,0,0))]
def raw165Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨165,sourceWord99,58,57,(-2),2,0,0,0⟩
theorem raw165Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw165Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw165Spec]
  decide +kernel
theorem raw165Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw165Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw165Spec x y z w v := by
  norm_num [eval,monomial,raw165Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw165Spec] <;> ring
def raw165Observation : Fin 553 := ⟨49,by decide⟩
theorem raw165Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw165Observation)=v raw165Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw165Observation=[(1,raw165Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw165Observed
#print axioms raw165Valid
#print axioms raw165Row

def raw177Poly : Poly := [((-1/1:ℚ),39,((-2),0,(-2),0,0,0,0)),((1/1:ℚ),41,(0,0,0,0,0,0,0))]
def raw177Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨177,sourceWord145,41,39,0,(-2),0,(-2),0⟩
theorem raw177Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw177Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw177Spec]
  decide +kernel
theorem raw177Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw177Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw177Spec x y z w v := by
  norm_num [eval,monomial,raw177Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw177Spec] <;> ring
def raw177Observation : Fin 553 := ⟨46,by decide⟩
theorem raw177Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw177Observation)=v raw177Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw177Observation=[(1,raw177Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw177Observed
#print axioms raw177Valid
#print axioms raw177Row

def raw186Poly : Poly := [((-1/1:ℚ),0,((-2),0,0,0,0,0,0)),((1/1:ℚ),4,(0,0,0,0,0,0,0))]
def raw186Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨186,sourceWord142,4,0,(-1),(-2),0,0,0⟩
theorem raw186Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw186Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw186Spec]
  decide +kernel
theorem raw186Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw186Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw186Spec x y z w v := by
  norm_num [eval,monomial,raw186Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw186Spec] <;> ring
def raw186Observation : Fin 553 := ⟨50,by decide⟩
theorem raw186Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw186Observation)=v raw186Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw186Observation=[(1,raw186Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw186Observed
#print axioms raw186Valid
#print axioms raw186Row

def raw187Poly : Poly := [((1/1:ℚ),2,(0,0,0,0,0,0,0)),((-1/1:ℚ),3,(2,0,0,0,0,0,0))]
def raw187Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨187,sourceWord151,2,3,1,2,0,0,0⟩
theorem raw187Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw187Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw187Spec]
  decide +kernel
theorem raw187Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw187Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw187Spec x y z w v := by
  norm_num [eval,monomial,raw187Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw187Spec] <;> ring
def raw187Observation : Fin 553 := ⟨27,by decide⟩
theorem raw187Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw187Observation)=v raw187Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw187Observation=[(1,raw187Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw187Observed
#print axioms raw187Valid
#print axioms raw187Row

def raw189Poly : Poly := [((1/1:ℚ),2,(0,0,0,0,0,0,0)),((-1/1:ℚ),3,(2,0,0,0,0,0,0))]
def raw189Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨189,sourceWord114,2,3,0,2,0,0,0⟩
theorem raw189Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw189Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw189Spec]
  decide +kernel
theorem raw189Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw189Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw189Spec x y z w v := by
  norm_num [eval,monomial,raw189Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw189Spec] <;> ring
def raw189Observation : Fin 553 := ⟨27,by decide⟩
theorem raw189Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw189Observation)=v raw189Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw189Observation=[(1,raw189Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw189Observed
#print axioms raw189Valid
#print axioms raw189Row

def raw191Poly : Poly := [((-1/1:ℚ),33,(0,0,(-2),0,0,0,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0))]
def raw191Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨191,sourceWord114,48,33,0,0,0,(-2),0⟩
theorem raw191Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw191Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw191Spec]
  decide +kernel
theorem raw191Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw191Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw191Spec x y z w v := by
  norm_num [eval,monomial,raw191Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw191Spec] <;> ring
def raw191Observation : Fin 553 := ⟨30,by decide⟩
theorem raw191Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw191Observation)=v raw191Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw191Observation=[(1,raw191Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw191Observed
#print axioms raw191Valid
#print axioms raw191Row

def raw192Poly : Poly := [((-1/1:ℚ),80,((-2),0,(-2),0,0,0,0)),((1/1:ℚ),81,(0,0,0,0,0,0,0))]
def raw192Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨192,sourceWord114,81,80,0,(-2),0,(-2),0⟩
theorem raw192Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw192Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw192Spec]
  decide +kernel
theorem raw192Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw192Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw192Spec x y z w v := by
  norm_num [eval,monomial,raw192Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw192Spec] <;> ring
def raw192Observation : Fin 553 := ⟨20,by decide⟩
theorem raw192Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw192Observation)=v raw192Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw192Observation=[(1,raw192Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw192Observed
#print axioms raw192Valid
#print axioms raw192Row

def raw194Poly : Poly := [((-1/1:ℚ),24,(0,0,0,0,0,0,0)),((1/1:ℚ),32,(0,0,0,0,0,0,0))]
def raw194Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨194,sourceWord114,32,24,0,0,0,0,0⟩
theorem raw194Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw194Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw194Spec]
  decide +kernel
theorem raw194Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw194Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw194Spec x y z w v := by
  norm_num [eval,monomial,raw194Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw194Spec] <;> ring
def raw194Observation : Fin 553 := ⟨26,by decide⟩
theorem raw194Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw194Observation)=v raw194Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw194Observation=[(1,raw194Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw194Observed
#print axioms raw194Valid
#print axioms raw194Row

def raw212Poly : Poly := [((-1/1:ℚ),7,((-2),0,0,0,0,0,0)),((1/1:ℚ),10,(0,0,0,0,0,0,0))]
def raw212Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨212,sourceWord154,10,7,0,(-2),0,0,0⟩
theorem raw212Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw212Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw212Spec]
  decide +kernel
theorem raw212Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw212Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw212Spec x y z w v := by
  norm_num [eval,monomial,raw212Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw212Spec] <;> ring
def raw212Observation : Fin 553 := ⟨55,by decide⟩
theorem raw212Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw212Observation)=v raw212Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw212Observation=[(1,raw212Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw212Observed
#print axioms raw212Valid
#print axioms raw212Row

def raw234Poly : Poly := [((-1/1:ℚ),32,(0,0,0,0,0,0,0)),((1/1:ℚ),72,(0,0,0,0,0,0,0))]
def raw234Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨234,sourceWord42,72,32,0,0,0,0,0⟩
theorem raw234Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw234Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw234Spec]
  decide +kernel
theorem raw234Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw234Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw234Spec x y z w v := by
  norm_num [eval,monomial,raw234Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw234Spec] <;> ring
def raw234Observation : Fin 553 := ⟨2,by decide⟩
theorem raw234Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw234Observation)=v raw234Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw234Observation=[(1,raw234Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw234Observed
#print axioms raw234Valid
#print axioms raw234Row

def raw249Poly : Poly := [((1/1:ℚ),32,(0,0,0,0,0,0,0)),((-1/1:ℚ),72,(0,0,0,0,0,0,0))]
def raw249Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨249,sourceWord104,32,72,0,0,0,0,0⟩
theorem raw249Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw249Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw249Spec]
  decide +kernel
theorem raw249Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw249Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw249Spec x y z w v := by
  norm_num [eval,monomial,raw249Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw249Spec] <;> ring
def raw249Observation : Fin 553 := ⟨4,by decide⟩
theorem raw249Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw249Observation)=v raw249Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw249Observation=[(1,raw249Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw249Observed
#print axioms raw249Valid
#print axioms raw249Row

def raw307Poly : Poly := [((1/1:ℚ),2,(0,0,0,0,0,0,0)),((-1/1:ℚ),3,(2,0,0,0,0,0,0))]
def raw307Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨307,sourceWord41,2,3,0,2,0,0,0⟩
theorem raw307Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw307Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw307Spec]
  decide +kernel
theorem raw307Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw307Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw307Spec x y z w v := by
  norm_num [eval,monomial,raw307Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw307Spec] <;> ring
def raw307Observation : Fin 553 := ⟨27,by decide⟩
theorem raw307Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw307Observation)=v raw307Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw307Observation=[(1,raw307Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw307Observed
#print axioms raw307Valid
#print axioms raw307Row

def raw309Poly : Poly := [((-1/1:ℚ),33,((-2),0,0,0,0,0,0)),((1/1:ℚ),34,(0,0,0,0,0,0,0))]
def raw309Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨309,sourceWord41,34,33,0,(-2),0,0,0⟩
theorem raw309Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw309Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw309Spec]
  decide +kernel
theorem raw309Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw309Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw309Spec x y z w v := by
  norm_num [eval,monomial,raw309Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw309Spec] <;> ring
def raw309Observation : Fin 553 := ⟨30,by decide⟩
theorem raw309Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw309Observation)=v raw309Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw309Observation=[(1,raw309Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw309Observed
#print axioms raw309Valid
#print axioms raw309Row

def raw311Poly : Poly := [((-1/1:ℚ),37,(0,0,(-2),0,0,0,0)),((1/1:ℚ),38,(0,0,0,0,0,0,0))]
def raw311Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨311,sourceWord41,38,37,0,0,0,(-2),0⟩
theorem raw311Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw311Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw311Spec]
  decide +kernel
theorem raw311Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw311Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw311Spec x y z w v := by
  norm_num [eval,monomial,raw311Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw311Spec] <;> ring
def raw311Observation : Fin 553 := ⟨36,by decide⟩
theorem raw311Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw311Observation)=v raw311Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw311Observation=[(1,raw311Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw311Observed
#print axioms raw311Valid
#print axioms raw311Row

def raw316Poly : Poly := [((-1/1:ℚ),12,(2,0,(-2),0,0,0,0)),((1/1:ℚ),13,(0,0,0,0,0,0,0))]
def raw316Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨316,sourceWord41,13,12,0,2,0,(-2),0⟩
theorem raw316Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw316Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw316Spec]
  decide +kernel
theorem raw316Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw316Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw316Spec x y z w v := by
  norm_num [eval,monomial,raw316Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw316Spec] <;> ring
def raw316Observation : Fin 553 := ⟨21,by decide⟩
theorem raw316Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw316Observation)=v raw316Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw316Observation=[(1,raw316Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw316Observed
#print axioms raw316Valid
#print axioms raw316Row

def raw317Poly : Poly := [((-1/1:ℚ),14,((-2),0,0,0,0,0,0)),((1/1:ℚ),15,(0,0,0,0,0,0,0))]
def raw317Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨317,sourceWord41,15,14,0,(-2),0,0,0⟩
theorem raw317Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw317Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw317Spec]
  decide +kernel
theorem raw317Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw317Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw317Spec x y z w v := by
  norm_num [eval,monomial,raw317Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw317Spec] <;> ring
def raw317Observation : Fin 553 := ⟨22,by decide⟩
theorem raw317Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw317Observation)=v raw317Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw317Observation=[(1,raw317Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw317Observed
#print axioms raw317Valid
#print axioms raw317Row

def raw318Poly : Poly := [((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),16,(0,0,0,0,0,0,0))]
def raw318Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨318,sourceWord41,6,16,0,0,0,0,0⟩
theorem raw318Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw318Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw318Spec]
  decide +kernel
theorem raw318Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw318Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw318Spec x y z w v := by
  norm_num [eval,monomial,raw318Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw318Spec] <;> ring
def raw318Observation : Fin 553 := ⟨24,by decide⟩
theorem raw318Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw318Observation)=v raw318Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw318Observation=[(1,raw318Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw318Observed
#print axioms raw318Valid
#print axioms raw318Row

def raw320Poly : Poly := [((-1/1:ℚ),19,((-2),0,2,0,0,0,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0))]
def raw320Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨320,sourceWord41,20,19,0,(-2),0,2,0⟩
theorem raw320Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw320Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw320Spec]
  decide +kernel
theorem raw320Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw320Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw320Spec x y z w v := by
  norm_num [eval,monomial,raw320Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw320Spec] <;> ring
def raw320Observation : Fin 553 := ⟨94,by decide⟩
theorem raw320Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw320Observation)=v raw320Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw320Observation=[(1,raw320Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw320Observed
#print axioms raw320Valid
#print axioms raw320Row

def raw367Poly : Poly := [((-1/1:ℚ),6,(0,0,(-2),0,0,0,0)),((1/1:ℚ),47,(0,0,0,0,0,0,0))]
def raw367Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨367,sourceWord8,47,6,0,0,0,(-2),0⟩
theorem raw367Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw367Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw367Spec]
  decide +kernel
theorem raw367Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw367Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw367Spec x y z w v := by
  norm_num [eval,monomial,raw367Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw367Spec] <;> ring
def raw367Observation : Fin 553 := ⟨6,by decide⟩
theorem raw367Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw367Observation)=v raw367Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw367Observation=[(1,raw367Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw367Observed
#print axioms raw367Valid
#print axioms raw367Row

def raw404Poly : Poly := [((-1/1:ℚ),57,(0,0,(-2),0,0,0,0)),((1/1:ℚ),67,(0,0,0,0,0,0,0))]
def raw404Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨404,sourceWord70,67,57,(-1),0,0,(-2),0⟩
theorem raw404Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw404Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw404Spec]
  decide +kernel
theorem raw404Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw404Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw404Spec x y z w v := by
  norm_num [eval,monomial,raw404Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw404Spec] <;> ring
def raw404Observation : Fin 553 := ⟨49,by decide⟩
theorem raw404Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw404Observation)=v raw404Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw404Observation=[(1,raw404Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw404Observed
#print axioms raw404Valid
#print axioms raw404Row

def raw509Poly : Poly := [((-1/1:ℚ),7,(0,0,2,0,0,0,0)),((1/1:ℚ),16,(0,0,0,0,0,0,0))]
def raw509Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨509,sourceWord135,16,7,0,0,0,2,0⟩
theorem raw509Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw509Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw509Spec]
  decide +kernel
theorem raw509Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw509Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw509Spec x y z w v := by
  norm_num [eval,monomial,raw509Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw509Spec] <;> ring
def raw509Observation : Fin 553 := ⟨55,by decide⟩
theorem raw509Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw509Observation)=v raw509Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw509Observation=[(1,raw509Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw509Observed
#print axioms raw509Valid
#print axioms raw509Row

def raw569Poly : Poly := [((-1/1:ℚ),2,((-2),(-3),(-2),0,0,0,0)),((1/1:ℚ),88,(0,0,0,0,0,0,0))]
def raw569Left : ℕ→ℕ
  | 0 => 88
  | _ => 0
def raw569Right : ℕ→ℕ
  | 0 => 2
  | _ => 0
def raw569Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨569,270,1,1,(-2700),raw569Left,raw569Right,(-2),(-3),(-2),0⟩
theorem raw569Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw569Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw569Spec]
  decide +kernel
theorem raw569Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw569Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw569Spec x y z w 1 v := by
  norm_num [eval,monomial,raw569Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw569Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw569Left,raw569Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw569Observation : Fin 553 := ⟨0,by decide⟩
def raw569Units : List ℕ := [0]
theorem raw569Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw569Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw569Spec.q raw569Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw569Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw569Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw569Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw569Units raw569Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw569Units raw569Right (by decide +kernel) (by decide +kernel)]
#print axioms raw569Observed
#print axioms raw569Valid
#print axioms raw569Row

def raw571Poly : Poly := [((-1/1:ℚ),2,(0,(-3),(-2),0,0,0,0)),((1/1:ℚ),83,(0,0,0,0,0,0,0))]
def raw571Left : ℕ→ℕ
  | 0 => 83
  | _ => 0
def raw571Right : ℕ→ℕ
  | 0 => 2
  | _ => 0
def raw571Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨571,270,1,2,(-1350),raw571Left,raw571Right,0,(-3),(-2),0⟩
theorem raw571Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw571Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw571Spec]
  decide +kernel
theorem raw571Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw571Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw571Spec x y z w 1 v := by
  norm_num [eval,monomial,raw571Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw571Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw571Left,raw571Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw571Observation : Fin 553 := ⟨0,by decide⟩
def raw571Units : List ℕ := [0]
theorem raw571Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw571Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw571Spec.q raw571Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw571Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw571Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw571Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw571Units raw571Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw571Units raw571Right (by decide +kernel) (by decide +kernel)]
#print axioms raw571Observed
#print axioms raw571Valid
#print axioms raw571Row

def raw579Poly : Poly := [((1/1:ℚ),48,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,(0,(-1),(-2),0,0,0,0))]
def raw579Left : ℕ→ℕ
  | 0 => 48
  | _ => 0
def raw579Right : ℕ→ℕ
  | 0 => 50
  | _ => 0
def raw579Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨579,270,1,6,(-450),raw579Left,raw579Right,0,(-1),(-2),0⟩
theorem raw579Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw579Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw579Spec]
  decide +kernel
theorem raw579Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw579Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw579Spec x y z w 1 v := by
  norm_num [eval,monomial,raw579Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw579Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw579Left,raw579Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw579Observation : Fin 553 := ⟨18,by decide⟩
def raw579Units : List ℕ := [0]
theorem raw579Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw579Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw579Spec.q raw579Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw579Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw579Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw579Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw579Units raw579Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw579Units raw579Right (by decide +kernel) (by decide +kernel)]
#print axioms raw579Observed
#print axioms raw579Valid
#print axioms raw579Row

def raw580Poly : Poly := [((-1/1:ℚ),37,(0,(-1),(-2),0,0,0,0)),((1/1:ℚ),47,(0,0,0,0,0,0,0))]
def raw580Left : ℕ→ℕ
  | 0 => 47
  | _ => 0
def raw580Right : ℕ→ℕ
  | 0 => 37
  | _ => 0
def raw580Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨580,270,1,(-6),450,raw580Left,raw580Right,0,(-1),(-2),0⟩
theorem raw580Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw580Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw580Spec]
  decide +kernel
theorem raw580Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw580Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw580Spec x y z w 1 v := by
  norm_num [eval,monomial,raw580Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw580Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw580Left,raw580Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw580Observation : Fin 553 := ⟨36,by decide⟩
def raw580Units : List ℕ := [0]
theorem raw580Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw580Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw580Spec.q raw580Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw580Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw580Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw580Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw580Units raw580Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw580Units raw580Right (by decide +kernel) (by decide +kernel)]
#print axioms raw580Observed
#print axioms raw580Valid
#print axioms raw580Row

def raw582Poly : Poly := [((-1/1:ℚ),6,((-2),1,(-2),0,0,0,0)),((1/1:ℚ),79,(0,0,0,0,0,0,0))]
def raw582Left : ℕ→ℕ
  | 0 => 79
  | _ => 0
def raw582Right : ℕ→ℕ
  | 0 => 6
  | _ => 0
def raw582Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨582,270,1,(-9),300,raw582Left,raw582Right,(-2),1,(-2),0⟩
theorem raw582Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw582Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw582Spec]
  decide +kernel
theorem raw582Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw582Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw582Spec x y z w 1 v := by
  norm_num [eval,monomial,raw582Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw582Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw582Left,raw582Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw582Observation : Fin 553 := ⟨6,by decide⟩
def raw582Units : List ℕ := [0]
theorem raw582Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw582Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw582Spec.q raw582Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw582Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw582Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw582Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw582Units raw582Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw582Units raw582Right (by decide +kernel) (by decide +kernel)]
#print axioms raw582Observed
#print axioms raw582Valid
#print axioms raw582Row

def raw585Poly : Poly := [((-1/1:ℚ),20,(2,(-1),(-2),0,0,0,0)),((1/1:ℚ),68,(0,0,0,0,0,0,0))]
def raw585Left : ℕ→ℕ
  | 0 => 68
  | _ => 0
def raw585Right : ℕ→ℕ
  | 0 => 20
  | _ => 0
def raw585Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨585,270,1,12,(-225),raw585Left,raw585Right,2,(-1),(-2),0⟩
theorem raw585Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw585Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw585Spec]
  decide +kernel
theorem raw585Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw585Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw585Spec x y z w 1 v := by
  norm_num [eval,monomial,raw585Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw585Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw585Left,raw585Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw585Observation : Fin 553 := ⟨9,by decide⟩
def raw585Units : List ℕ := [0]
theorem raw585Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw585Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw585Spec.q raw585Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw585Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw585Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw585Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw585Units raw585Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw585Units raw585Right (by decide +kernel) (by decide +kernel)]
#print axioms raw585Observed
#print axioms raw585Valid
#print axioms raw585Row

def raw586Poly : Poly := [((-1/1:ℚ),55,(2,(-1),(-2),0,0,0,0)),((1/1:ℚ),76,(0,0,0,0,0,0,0))]
def raw586Left : ℕ→ℕ
  | 0 => 76
  | _ => 0
def raw586Right : ℕ→ℕ
  | 0 => 55
  | _ => 0
def raw586Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨586,270,1,(-12),225,raw586Left,raw586Right,2,(-1),(-2),0⟩
theorem raw586Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw586Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw586Spec]
  decide +kernel
theorem raw586Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw586Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw586Spec x y z w 1 v := by
  norm_num [eval,monomial,raw586Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw586Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw586Left,raw586Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw586Observation : Fin 553 := ⟨45,by decide⟩
def raw586Units : List ℕ := [0]
theorem raw586Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw586Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw586Spec.q raw586Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw586Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw586Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw586Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw586Units raw586Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw586Units raw586Right (by decide +kernel) (by decide +kernel)]
#print axioms raw586Observed
#print axioms raw586Valid
#print axioms raw586Row

def raw587Poly : Poly := [((1/1:ℚ),34,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,((-2),(-1),0,0,0,0,0))]
def raw587Left : ℕ→ℕ
  | 0 => 34
  | _ => 0
def raw587Right : ℕ→ℕ
  | 0 => 50
  | _ => 0
def raw587Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨587,270,1,15,(-180),raw587Left,raw587Right,(-2),(-1),0,0⟩
theorem raw587Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw587Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw587Spec]
  decide +kernel
theorem raw587Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw587Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw587Spec x y z w 1 v := by
  norm_num [eval,monomial,raw587Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw587Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw587Left,raw587Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw587Observation : Fin 553 := ⟨18,by decide⟩
def raw587Units : List ℕ := [0]
theorem raw587Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw587Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw587Spec.q raw587Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw587Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw587Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw587Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw587Units raw587Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw587Units raw587Right (by decide +kernel) (by decide +kernel)]
#print axioms raw587Observed
#print axioms raw587Valid
#print axioms raw587Row

def raw590Poly : Poly := [((-1/1:ℚ),33,(0,1,(-2),0,0,0,0)),((1/1:ℚ),64,(0,0,0,0,0,0,0))]
def raw590Left : ℕ→ℕ
  | 0 => 64
  | _ => 0
def raw590Right : ℕ→ℕ
  | 0 => 33
  | _ => 0
def raw590Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨590,270,1,(-18),150,raw590Left,raw590Right,0,1,(-2),0⟩
theorem raw590Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw590Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw590Spec]
  decide +kernel
theorem raw590Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw590Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw590Spec x y z w 1 v := by
  norm_num [eval,monomial,raw590Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw590Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw590Left,raw590Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw590Observation : Fin 553 := ⟨30,by decide⟩
def raw590Units : List ℕ := [0]
theorem raw590Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw590Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw590Spec.q raw590Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw590Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw590Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw590Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw590Units raw590Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw590Units raw590Right (by decide +kernel) (by decide +kernel)]
#print axioms raw590Observed
#print axioms raw590Valid
#print axioms raw590Row

def raw593Poly : Poly := [((1/1:ℚ),15,(0,0,0,0,0,0,0)),((-1/1:ℚ),90,((-2),(-3),2,0,0,0,0))]
def raw593Left : ℕ→ℕ
  | 0 => 15
  | _ => 0
def raw593Right : ℕ→ℕ
  | 0 => 90
  | _ => 0
def raw593Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨593,270,1,25,(-108),raw593Left,raw593Right,(-2),(-3),2,0⟩
theorem raw593Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw593Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw593Spec]
  decide +kernel
theorem raw593Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw593Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw593Spec x y z w 1 v := by
  norm_num [eval,monomial,raw593Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw593Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw593Left,raw593Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw593Observation : Fin 553 := ⟨100,by decide⟩
def raw593Units : List ℕ := [0]
theorem raw593Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw593Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw593Spec.q raw593Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw593Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw593Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw593Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw593Units raw593Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw593Units raw593Right (by decide +kernel) (by decide +kernel)]
#print axioms raw593Observed
#print axioms raw593Valid
#print axioms raw593Row

def raw594Poly : Poly := [((1/1:ℚ),57,(0,0,0,0,0,0,0)),((-1/1:ℚ),91,((-2),(-3),2,0,0,0,0))]
def raw594Left : ℕ→ℕ
  | 0 => 57
  | _ => 0
def raw594Right : ℕ→ℕ
  | 0 => 91
  | _ => 0
def raw594Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨594,270,1,(-25),108,raw594Left,raw594Right,(-2),(-3),2,0⟩
theorem raw594Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw594Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw594Spec]
  decide +kernel
theorem raw594Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw594Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw594Spec x y z w 1 v := by
  norm_num [eval,monomial,raw594Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw594Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw594Left,raw594Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw594Observation : Fin 553 := ⟨101,by decide⟩
def raw594Units : List ℕ := [0]
theorem raw594Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw594Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw594Spec.q raw594Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw594Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw594Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw594Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw594Units raw594Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw594Units raw594Right (by decide +kernel) (by decide +kernel)]
#print axioms raw594Observed
#print axioms raw594Valid
#print axioms raw594Row

def raw595Poly : Poly := [((-1/1:ℚ),46,((-2),3,(-2),0,0,0,0)),((1/1:ℚ),92,(0,0,0,0,0,0,0))]
def raw595Left : ℕ→ℕ
  | 0 => 92
  | _ => 0
def raw595Right : ℕ→ℕ
  | 0 => 46
  | _ => 0
def raw595Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨595,270,1,27,(-100),raw595Left,raw595Right,(-2),3,(-2),0⟩
theorem raw595Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw595Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw595Spec]
  decide +kernel
theorem raw595Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw595Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw595Spec x y z w 1 v := by
  norm_num [eval,monomial,raw595Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw595Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw595Left,raw595Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw595Observation : Fin 553 := ⟨34,by decide⟩
def raw595Units : List ℕ := [0]
theorem raw595Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw595Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw595Spec.q raw595Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw595Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw595Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw595Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw595Units raw595Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw595Units raw595Right (by decide +kernel) (by decide +kernel)]
#print axioms raw595Observed
#print axioms raw595Valid
#print axioms raw595Row

def raw596Poly : Poly := [((-1/1:ℚ),80,((-2),3,(-2),0,0,0,0)),((1/1:ℚ),93,(0,0,0,0,0,0,0))]
def raw596Left : ℕ→ℕ
  | 0 => 93
  | _ => 0
def raw596Right : ℕ→ℕ
  | 0 => 80
  | _ => 0
def raw596Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨596,270,1,(-27),100,raw596Left,raw596Right,(-2),3,(-2),0⟩
theorem raw596Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw596Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw596Spec]
  decide +kernel
theorem raw596Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw596Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw596Spec x y z w 1 v := by
  norm_num [eval,monomial,raw596Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw596Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw596Left,raw596Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw596Observation : Fin 553 := ⟨20,by decide⟩
def raw596Units : List ℕ := [0]
theorem raw596Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw596Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw596Spec.q raw596Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw596Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw596Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw596Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw596Units raw596Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw596Units raw596Right (by decide +kernel) (by decide +kernel)]
#print axioms raw596Observed
#print axioms raw596Valid
#print axioms raw596Row

def raw598Poly : Poly := [((1/1:ℚ),28,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,(0,(-1),0,0,0,0,0))]
def raw598Left : ℕ→ℕ
  | 0 => 28
  | _ => 0
def raw598Right : ℕ→ℕ
  | 0 => 50
  | _ => 0
def raw598Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨598,270,1,(-30),90,raw598Left,raw598Right,0,(-1),0,0⟩
theorem raw598Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw598Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw598Spec]
  decide +kernel
theorem raw598Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw598Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw598Spec x y z w 1 v := by
  norm_num [eval,monomial,raw598Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw598Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw598Left,raw598Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw598Observation : Fin 553 := ⟨18,by decide⟩
def raw598Units : List ℕ := [0]
theorem raw598Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw598Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw598Spec.q raw598Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw598Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw598Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw598Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw598Units raw598Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw598Units raw598Right (by decide +kernel) (by decide +kernel)]
#print axioms raw598Observed
#print axioms raw598Valid
#print axioms raw598Row

def raw599Poly : Poly := [((1/1:ℚ),94,(0,0,0,0,0,0,0)),((-1/1:ℚ),95,(2,1,(-2),0,0,0,0))]
def raw599Left : ℕ→ℕ
  | 0 => 94
  | _ => 0
def raw599Right : ℕ→ℕ
  | 0 => 95
  | _ => 0
def raw599Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨599,270,1,36,(-75),raw599Left,raw599Right,2,1,(-2),0⟩
theorem raw599Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw599Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw599Spec]
  decide +kernel
theorem raw599Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw599Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw599Spec x y z w 1 v := by
  norm_num [eval,monomial,raw599Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw599Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw599Left,raw599Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw599Observation : Fin 553 := ⟨39,by decide⟩
def raw599Units : List ℕ := [0]
theorem raw599Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw599Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw599Spec.q raw599Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw599Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw599Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw599Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw599Units raw599Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw599Units raw599Right (by decide +kernel) (by decide +kernel)]
#print axioms raw599Observed
#print axioms raw599Valid
#print axioms raw599Row

def raw600Poly : Poly := [((1/1:ℚ),96,(0,0,0,0,0,0,0)),((-1/1:ℚ),97,(2,1,(-2),0,0,0,0))]
def raw600Left : ℕ→ℕ
  | 0 => 96
  | _ => 0
def raw600Right : ℕ→ℕ
  | 0 => 97
  | _ => 0
def raw600Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨600,270,1,(-36),75,raw600Left,raw600Right,2,1,(-2),0⟩
theorem raw600Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw600Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw600Spec]
  decide +kernel
theorem raw600Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw600Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw600Spec x y z w 1 v := by
  norm_num [eval,monomial,raw600Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw600Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw600Left,raw600Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw600Observation : Fin 553 := ⟨15,by decide⟩
def raw600Units : List ℕ := [0]
theorem raw600Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw600Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw600Spec.q raw600Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw600Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw600Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw600Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw600Units raw600Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw600Units raw600Right (by decide +kernel) (by decide +kernel)]
#print axioms raw600Observed
#print axioms raw600Valid
#print axioms raw600Row

def raw601Poly : Poly := [((1/1:ℚ),20,(0,0,0,0,0,0,0)),((-1/1:ℚ),69,((-2),1,0,0,0,0,0))]
def raw601Left : ℕ→ℕ
  | 0 => 20
  | _ => 0
def raw601Right : ℕ→ℕ
  | 0 => 69
  | _ => 0
def raw601Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨601,270,1,45,(-60),raw601Left,raw601Right,(-2),1,0,0⟩
theorem raw601Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw601Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw601Spec]
  decide +kernel
theorem raw601Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw601Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw601Spec x y z w 1 v := by
  norm_num [eval,monomial,raw601Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw601Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw601Left,raw601Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw601Observation : Fin 553 := ⟨42,by decide⟩
def raw601Units : List ℕ := [0]
theorem raw601Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw601Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw601Spec.q raw601Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw601Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw601Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw601Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw601Units raw601Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw601Units raw601Right (by decide +kernel) (by decide +kernel)]
#print axioms raw601Observed
#print axioms raw601Valid
#print axioms raw601Row

def raw602Poly : Poly := [((1/1:ℚ),55,(0,0,0,0,0,0,0)),((-1/1:ℚ),75,((-2),1,0,0,0,0,0))]
def raw602Left : ℕ→ℕ
  | 0 => 55
  | _ => 0
def raw602Right : ℕ→ℕ
  | 0 => 75
  | _ => 0
def raw602Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨602,270,1,(-45),60,raw602Left,raw602Right,(-2),1,0,0⟩
theorem raw602Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw602Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw602Spec]
  decide +kernel
theorem raw602Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw602Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw602Spec x y z w 1 v := by
  norm_num [eval,monomial,raw602Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw602Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw602Left,raw602Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw602Observation : Fin 553 := ⟨12,by decide⟩
def raw602Units : List ℕ := [0]
theorem raw602Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw602Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw602Spec.q raw602Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw602Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw602Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw602Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw602Units raw602Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw602Units raw602Right (by decide +kernel) (by decide +kernel)]
#print axioms raw602Observed
#print axioms raw602Valid
#print axioms raw602Row

def raw603Poly : Poly := [((1/1:ℚ),98,(0,0,0,0,0,0,0)),((-1/1:ℚ),99,(0,(-3),2,0,0,0,0))]
def raw603Left : ℕ→ℕ
  | 0 => 98
  | _ => 0
def raw603Right : ℕ→ℕ
  | 0 => 99
  | _ => 0
def raw603Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨603,270,1,50,(-54),raw603Left,raw603Right,0,(-3),2,0⟩
theorem raw603Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw603Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw603Spec]
  decide +kernel
theorem raw603Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw603Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw603Spec x y z w 1 v := by
  norm_num [eval,monomial,raw603Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw603Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw603Left,raw603Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw603Observation : Fin 553 := ⟨102,by decide⟩
def raw603Units : List ℕ := [0]
theorem raw603Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw603Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw603Spec.q raw603Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw603Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw603Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw603Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw603Units raw603Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw603Units raw603Right (by decide +kernel) (by decide +kernel)]
#print axioms raw603Observed
#print axioms raw603Valid
#print axioms raw603Row

def raw604Poly : Poly := [((1/1:ℚ),100,(0,0,0,0,0,0,0)),((-1/1:ℚ),101,(0,(-3),2,0,0,0,0))]
def raw604Left : ℕ→ℕ
  | 0 => 100
  | _ => 0
def raw604Right : ℕ→ℕ
  | 0 => 101
  | _ => 0
def raw604Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨604,270,1,(-50),54,raw604Left,raw604Right,0,(-3),2,0⟩
theorem raw604Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw604Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw604Spec]
  decide +kernel
theorem raw604Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw604Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw604Spec x y z w 1 v := by
  norm_num [eval,monomial,raw604Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw604Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw604Left,raw604Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw604Observation : Fin 553 := ⟨103,by decide⟩
def raw604Units : List ℕ := [0]
theorem raw604Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw604Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw604Spec.q raw604Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw604Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw604Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw604Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw604Units raw604Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw604Units raw604Right (by decide +kernel) (by decide +kernel)]
#print axioms raw604Observed
#print axioms raw604Valid
#print axioms raw604Row

def raw605Poly : Poly := [((-1/1:ℚ),100,(0,3,(-2),0,0,0,0)),((1/1:ℚ),101,(0,0,0,0,0,0,0))]
def raw605Left : ℕ→ℕ
  | 0 => 101
  | _ => 0
def raw605Right : ℕ→ℕ
  | 0 => 100
  | _ => 0
def raw605Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨605,270,1,54,(-50),raw605Left,raw605Right,0,3,(-2),0⟩
theorem raw605Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw605Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw605Spec]
  decide +kernel
theorem raw605Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw605Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw605Spec x y z w 1 v := by
  norm_num [eval,monomial,raw605Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw605Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw605Left,raw605Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw605Observation : Fin 553 := ⟨44,by decide⟩
def raw605Units : List ℕ := [0]
theorem raw605Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw605Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw605Spec.q raw605Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw605Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw605Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw605Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw605Units raw605Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw605Units raw605Right (by decide +kernel) (by decide +kernel)]
#print axioms raw605Observed
#print axioms raw605Valid
#print axioms raw605Row

def raw606Poly : Poly := [((-1/1:ℚ),98,(0,3,(-2),0,0,0,0)),((1/1:ℚ),99,(0,0,0,0,0,0,0))]
def raw606Left : ℕ→ℕ
  | 0 => 99
  | _ => 0
def raw606Right : ℕ→ℕ
  | 0 => 98
  | _ => 0
def raw606Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨606,270,1,(-54),50,raw606Left,raw606Right,0,3,(-2),0⟩
theorem raw606Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw606Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw606Spec]
  decide +kernel
theorem raw606Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw606Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw606Spec x y z w 1 v := by
  norm_num [eval,monomial,raw606Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw606Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw606Left,raw606Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw606Observation : Fin 553 := ⟨10,by decide⟩
def raw606Units : List ℕ := [0]
theorem raw606Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw606Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw606Spec.q raw606Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw606Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw606Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw606Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw606Units raw606Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw606Units raw606Right (by decide +kernel) (by decide +kernel)]
#print axioms raw606Observed
#print axioms raw606Valid
#print axioms raw606Row

def raw607Poly : Poly := [((-1/1:ℚ),55,(2,(-1),0,0,0,0,0)),((1/1:ℚ),75,(0,0,0,0,0,0,0))]
def raw607Left : ℕ→ℕ
  | 0 => 75
  | _ => 0
def raw607Right : ℕ→ℕ
  | 0 => 55
  | _ => 0
def raw607Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨607,270,1,60,(-45),raw607Left,raw607Right,2,(-1),0,0⟩
theorem raw607Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw607Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw607Spec]
  decide +kernel
theorem raw607Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw607Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw607Spec x y z w 1 v := by
  norm_num [eval,monomial,raw607Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw607Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw607Left,raw607Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw607Observation : Fin 553 := ⟨45,by decide⟩
def raw607Units : List ℕ := [0]
theorem raw607Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw607Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw607Spec.q raw607Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw607Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw607Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw607Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw607Units raw607Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw607Units raw607Right (by decide +kernel) (by decide +kernel)]
#print axioms raw607Observed
#print axioms raw607Valid
#print axioms raw607Row

def raw608Poly : Poly := [((-1/1:ℚ),20,(2,(-1),0,0,0,0,0)),((1/1:ℚ),69,(0,0,0,0,0,0,0))]
def raw608Left : ℕ→ℕ
  | 0 => 69
  | _ => 0
def raw608Right : ℕ→ℕ
  | 0 => 20
  | _ => 0
def raw608Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨608,270,1,(-60),45,raw608Left,raw608Right,2,(-1),0,0⟩
theorem raw608Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw608Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw608Spec]
  decide +kernel
theorem raw608Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw608Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw608Spec x y z w 1 v := by
  norm_num [eval,monomial,raw608Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw608Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw608Left,raw608Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw608Observation : Fin 553 := ⟨9,by decide⟩
def raw608Units : List ℕ := [0]
theorem raw608Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw608Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw608Spec.q raw608Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw608Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw608Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw608Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw608Units raw608Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw608Units raw608Right (by decide +kernel) (by decide +kernel)]
#print axioms raw608Observed
#print axioms raw608Valid
#print axioms raw608Row

def raw609Poly : Poly := [((-1/1:ℚ),96,((-2),(-1),2,0,0,0,0)),((1/1:ℚ),97,(0,0,0,0,0,0,0))]
def raw609Left : ℕ→ℕ
  | 0 => 97
  | _ => 0
def raw609Right : ℕ→ℕ
  | 0 => 96
  | _ => 0
def raw609Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨609,270,1,75,(-36),raw609Left,raw609Right,(-2),(-1),2,0⟩
theorem raw609Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw609Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw609Spec]
  decide +kernel
theorem raw609Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw609Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw609Spec x y z w 1 v := by
  norm_num [eval,monomial,raw609Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw609Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw609Left,raw609Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw609Observation : Fin 553 := ⟨104,by decide⟩
def raw609Units : List ℕ := [0]
theorem raw609Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw609Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw609Spec.q raw609Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw609Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw609Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw609Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw609Units raw609Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw609Units raw609Right (by decide +kernel) (by decide +kernel)]
#print axioms raw609Observed
#print axioms raw609Valid
#print axioms raw609Row

def raw610Poly : Poly := [((-1/1:ℚ),94,((-2),(-1),2,0,0,0,0)),((1/1:ℚ),95,(0,0,0,0,0,0,0))]
def raw610Left : ℕ→ℕ
  | 0 => 95
  | _ => 0
def raw610Right : ℕ→ℕ
  | 0 => 94
  | _ => 0
def raw610Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨610,270,1,(-75),36,raw610Left,raw610Right,(-2),(-1),2,0⟩
theorem raw610Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw610Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw610Spec]
  decide +kernel
theorem raw610Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw610Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw610Spec x y z w 1 v := by
  norm_num [eval,monomial,raw610Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw610Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw610Left,raw610Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw610Observation : Fin 553 := ⟨105,by decide⟩
def raw610Units : List ℕ := [0]
theorem raw610Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw610Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw610Spec.q raw610Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw610Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw610Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw610Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw610Units raw610Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw610Units raw610Right (by decide +kernel) (by decide +kernel)]
#print axioms raw610Observed
#print axioms raw610Valid
#print axioms raw610Row

def raw615Poly : Poly := [((-1/1:ℚ),57,(2,3,(-2),0,0,0,0)),((1/1:ℚ),91,(0,0,0,0,0,0,0))]
def raw615Left : ℕ→ℕ
  | 0 => 91
  | _ => 0
def raw615Right : ℕ→ℕ
  | 0 => 57
  | _ => 0
def raw615Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨615,270,1,108,(-25),raw615Left,raw615Right,2,3,(-2),0⟩
theorem raw615Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw615Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw615Spec]
  decide +kernel
theorem raw615Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw615Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw615Spec x y z w 1 v := by
  norm_num [eval,monomial,raw615Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw615Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw615Left,raw615Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw615Observation : Fin 553 := ⟨49,by decide⟩
def raw615Units : List ℕ := [0]
theorem raw615Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw615Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw615Spec.q raw615Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw615Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw615Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw615Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw615Units raw615Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw615Units raw615Right (by decide +kernel) (by decide +kernel)]
#print axioms raw615Observed
#print axioms raw615Valid
#print axioms raw615Row

def raw619Poly : Poly := [((1/1:ℚ),33,(0,0,0,0,0,0,0)),((-1/1:ℚ),64,(0,(-1),2,0,0,0,0))]
def raw619Left : ℕ→ℕ
  | 0 => 33
  | _ => 0
def raw619Right : ℕ→ℕ
  | 0 => 64
  | _ => 0
def raw619Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨619,270,1,150,(-18),raw619Left,raw619Right,0,(-1),2,0⟩
theorem raw619Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw619Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw619Spec]
  decide +kernel
theorem raw619Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw619Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw619Spec x y z w 1 v := by
  norm_num [eval,monomial,raw619Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw619Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw619Left,raw619Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw619Observation : Fin 553 := ⟨80,by decide⟩
def raw619Units : List ℕ := [0]
theorem raw619Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw619Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw619Spec.q raw619Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw619Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw619Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw619Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw619Units raw619Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw619Units raw619Right (by decide +kernel) (by decide +kernel)]
#print axioms raw619Observed
#print axioms raw619Valid
#print axioms raw619Row

def raw620Poly : Poly := [((1/1:ℚ),16,(0,0,0,0,0,0,0)),((-1/1:ℚ),38,(0,(-1),2,0,0,0,0))]
def raw620Left : ℕ→ℕ
  | 0 => 16
  | _ => 0
def raw620Right : ℕ→ℕ
  | 0 => 38
  | _ => 0
def raw620Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨620,270,1,(-150),18,raw620Left,raw620Right,0,(-1),2,0⟩
theorem raw620Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw620Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw620Spec]
  decide +kernel
theorem raw620Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw620Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw620Spec x y z w 1 v := by
  norm_num [eval,monomial,raw620Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw620Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw620Left,raw620Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw620Observation : Fin 553 := ⟨61,by decide⟩
def raw620Units : List ℕ := [0]
theorem raw620Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw620Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw620Spec.q raw620Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw620Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw620Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw620Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw620Units raw620Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw620Units raw620Right (by decide +kernel) (by decide +kernel)]
#print axioms raw620Observed
#print axioms raw620Valid
#print axioms raw620Row

def raw648Poly : Poly := [((1/1:ℚ),56,(0,0,0,0,0,0,0)),((-1/1:ℚ),75,(0,1,(-2),0,0,0,0))]
def raw648Left : ℕ→ℕ
  | 1 => 56
  | _ => 0
def raw648Right : ℕ→ℕ
  | 1 => 75
  | _ => 0
def raw648Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨648,270,2,9,(-75),raw648Left,raw648Right,0,1,(-2),0⟩
theorem raw648Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw648Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw648Spec]
  decide +kernel
theorem raw648Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw648Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw648Spec x y z w 1 v := by
  norm_num [eval,monomial,raw648Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw648Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw648Left,raw648Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw648Observation : Fin 553 := ⟨12,by decide⟩
def raw648Units : List ℕ := [1]
theorem raw648Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw648Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw648Spec.q raw648Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw648Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 2 raw648Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw648Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw648Units raw648Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=2) v raw648Units raw648Right (by decide +kernel) (by decide +kernel)]
#print axioms raw648Observed
#print axioms raw648Valid
#print axioms raw648Row

def raw649Poly : Poly := [((1/1:ℚ),19,(0,0,0,0,0,0,0)),((-1/1:ℚ),69,(0,1,(-2),0,0,0,0))]
def raw649Left : ℕ→ℕ
  | 1 => 19
  | _ => 0
def raw649Right : ℕ→ℕ
  | 1 => 69
  | _ => 0
def raw649Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨649,270,2,(-9),75,raw649Left,raw649Right,0,1,(-2),0⟩
theorem raw649Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw649Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw649Spec]
  decide +kernel
theorem raw649Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw649Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw649Spec x y z w 1 v := by
  norm_num [eval,monomial,raw649Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw649Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw649Left,raw649Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw649Observation : Fin 553 := ⟨42,by decide⟩
def raw649Units : List ℕ := [1]
theorem raw649Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw649Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw649Spec.q raw649Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw649Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 2 raw649Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw649Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw649Units raw649Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=2) v raw649Units raw649Right (by decide +kernel) (by decide +kernel)]
#print axioms raw649Observed
#print axioms raw649Valid
#print axioms raw649Row

def raw652Poly : Poly := [((1/1:ℚ),58,(0,0,0,0,0,0,0)),((-1/1:ℚ),91,(0,(-3),2,0,0,0,0))]
def raw652Left : ℕ→ℕ
  | 1 => 58
  | _ => 0
def raw652Right : ℕ→ℕ
  | 1 => 91
  | _ => 0
def raw652Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨652,270,2,25,(-27),raw652Left,raw652Right,0,(-3),2,0⟩
theorem raw652Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw652Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw652Spec]
  decide +kernel
theorem raw652Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw652Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw652Spec x y z w 1 v := by
  norm_num [eval,monomial,raw652Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw652Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw652Left,raw652Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw652Observation : Fin 553 := ⟨101,by decide⟩
def raw652Units : List ℕ := [1]
theorem raw652Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw652Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw652Spec.q raw652Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw652Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 2 raw652Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw652Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw652Units raw652Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=2) v raw652Units raw652Right (by decide +kernel) (by decide +kernel)]
#print axioms raw652Observed
#print axioms raw652Valid
#print axioms raw652Row

def raw653Poly : Poly := [((1/1:ℚ),14,(0,0,0,0,0,0,0)),((-1/1:ℚ),90,(0,(-3),2,0,0,0,0))]
def raw653Left : ℕ→ℕ
  | 1 => 14
  | _ => 0
def raw653Right : ℕ→ℕ
  | 1 => 90
  | _ => 0
def raw653Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨653,270,2,(-25),27,raw653Left,raw653Right,0,(-3),2,0⟩
theorem raw653Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw653Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw653Spec]
  decide +kernel
theorem raw653Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw653Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw653Spec x y z w 1 v := by
  norm_num [eval,monomial,raw653Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw653Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw653Left,raw653Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw653Observation : Fin 553 := ⟨100,by decide⟩
def raw653Units : List ℕ := [1]
theorem raw653Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw653Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw653Spec.q raw653Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw653Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 2 raw653Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw653Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw653Units raw653Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=2) v raw653Units raw653Right (by decide +kernel) (by decide +kernel)]
#print axioms raw653Observed
#print axioms raw653Valid
#print axioms raw653Row

def raw654Poly : Poly := [((-1/1:ℚ),14,(0,3,(-2),0,0,0,0)),((1/1:ℚ),90,(0,0,0,0,0,0,0))]
def raw654Left : ℕ→ℕ
  | 1 => 90
  | _ => 0
def raw654Right : ℕ→ℕ
  | 1 => 14
  | _ => 0
def raw654Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨654,270,2,27,(-25),raw654Left,raw654Right,0,3,(-2),0⟩
theorem raw654Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw654Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw654Spec]
  decide +kernel
theorem raw654Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw654Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw654Spec x y z w 1 v := by
  norm_num [eval,monomial,raw654Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw654Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw654Left,raw654Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw654Observation : Fin 553 := ⟨22,by decide⟩
def raw654Units : List ℕ := [1]
theorem raw654Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw654Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw654Spec.q raw654Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw654Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 2 raw654Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw654Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw654Units raw654Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=2) v raw654Units raw654Right (by decide +kernel) (by decide +kernel)]
#print axioms raw654Observed
#print axioms raw654Valid
#print axioms raw654Row

def raw655Poly : Poly := [((-1/1:ℚ),58,(0,3,(-2),0,0,0,0)),((1/1:ℚ),91,(0,0,0,0,0,0,0))]
def raw655Left : ℕ→ℕ
  | 1 => 91
  | _ => 0
def raw655Right : ℕ→ℕ
  | 1 => 58
  | _ => 0
def raw655Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨655,270,2,(-27),25,raw655Left,raw655Right,0,3,(-2),0⟩
theorem raw655Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw655Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw655Spec]
  decide +kernel
theorem raw655Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw655Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw655Spec x y z w 1 v := by
  norm_num [eval,monomial,raw655Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw655Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw655Left,raw655Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw655Observation : Fin 553 := ⟨32,by decide⟩
def raw655Units : List ℕ := [1]
theorem raw655Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw655Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw655Spec.q raw655Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw655Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 2 raw655Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw655Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw655Units raw655Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=2) v raw655Units raw655Right (by decide +kernel) (by decide +kernel)]
#print axioms raw655Observed
#print axioms raw655Valid
#print axioms raw655Row

def raw677Poly : Poly := [((-1/1:ℚ),2,(0,(-1),(-2),0,0,0,0)),((-1/1:ℚ),37,(0,(-1),(-2),0,0,0,0)),((1/1:ℚ),122,(0,0,0,0,0,0,0)),((1/1:ℚ),123,(0,0,0,0,0,0,0))]
def raw677Left : ℕ→ℕ
  | 1 => 122
  | 2 => 123
  | _ => 0
def raw677Right : ℕ→ℕ
  | 1 => 37
  | 2 => 2
  | _ => 0
def raw677Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨677,270,3,6,(-450),raw677Left,raw677Right,0,(-1),(-2),0⟩
theorem raw677Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw677Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw677Spec]
  decide +kernel
theorem raw677Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw677Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw677Spec x y z w 1 v := by
  norm_num [eval,monomial,raw677Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw677Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw677Left,raw677Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw677Observation : Fin 553 := ⟨112,by decide⟩
def raw677Units : List ℕ := [2, 1]
theorem raw677Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw677Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw677Spec.q raw677Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw677Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw677Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw677Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw677Units raw677Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw677Units raw677Right (by decide +kernel) (by decide +kernel)]
#print axioms raw677Observed
#print axioms raw677Valid
#print axioms raw677Row

def raw678Poly : Poly := [((-1/1:ℚ),2,(0,(-1),(-2),0,0,0,0)),((-1/1:ℚ),50,(0,(-1),(-2),0,0,0,0)),((1/1:ℚ),124,(0,0,0,0,0,0,0)),((1/1:ℚ),125,(0,0,0,0,0,0,0))]
def raw678Left : ℕ→ℕ
  | 1 => 124
  | 2 => 125
  | _ => 0
def raw678Right : ℕ→ℕ
  | 1 => 2
  | 2 => 50
  | _ => 0
def raw678Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨678,270,3,(-6),450,raw678Left,raw678Right,0,(-1),(-2),0⟩
theorem raw678Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw678Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw678Spec]
  decide +kernel
theorem raw678Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw678Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw678Spec x y z w 1 v := by
  norm_num [eval,monomial,raw678Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw678Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw678Left,raw678Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw678Observation : Fin 553 := ⟨111,by decide⟩
def raw678Units : List ℕ := [1, 2]
theorem raw678Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw678Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw678Spec.q raw678Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw678Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw678Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw678Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw678Units raw678Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw678Units raw678Right (by decide +kernel) (by decide +kernel)]
#print axioms raw678Observed
#print axioms raw678Valid
#print axioms raw678Row

def raw679Poly : Poly := [((-1/1:ℚ),33,((-2),1,(-2),0,0,0,0)),((-1/1:ℚ),75,((-2),1,(-2),0,0,0,0)),((1/1:ℚ),126,(0,0,0,0,0,0,0)),((1/1:ℚ),127,(0,0,0,0,0,0,0))]
def raw679Left : ℕ→ℕ
  | 1 => 126
  | 2 => 127
  | _ => 0
def raw679Right : ℕ→ℕ
  | 1 => 75
  | 2 => 33
  | _ => 0
def raw679Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨679,270,3,9,(-300),raw679Left,raw679Right,(-2),1,(-2),0⟩
theorem raw679Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw679Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw679Spec]
  decide +kernel
theorem raw679Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw679Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw679Spec x y z w 1 v := by
  norm_num [eval,monomial,raw679Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw679Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw679Left,raw679Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw679Observation : Fin 553 := ⟨114,by decide⟩
def raw679Units : List ℕ := [2, 1]
theorem raw679Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw679Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw679Spec.q raw679Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw679Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw679Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw679Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw679Units raw679Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw679Units raw679Right (by decide +kernel) (by decide +kernel)]
#print axioms raw679Observed
#print axioms raw679Valid
#print axioms raw679Row

def raw680Poly : Poly := [((-1/1:ℚ),16,((-2),1,(-2),0,0,0,0)),((-1/1:ℚ),69,((-2),1,(-2),0,0,0,0)),((1/1:ℚ),128,(0,0,0,0,0,0,0)),((1/1:ℚ),129,(0,0,0,0,0,0,0))]
def raw680Left : ℕ→ℕ
  | 1 => 128
  | 2 => 129
  | _ => 0
def raw680Right : ℕ→ℕ
  | 1 => 16
  | 2 => 69
  | _ => 0
def raw680Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨680,270,3,(-9),300,raw680Left,raw680Right,(-2),1,(-2),0⟩
theorem raw680Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw680Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw680Spec]
  decide +kernel
theorem raw680Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw680Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw680Spec x y z w 1 v := by
  norm_num [eval,monomial,raw680Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw680Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw680Left,raw680Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw680Observation : Fin 553 := ⟨115,by decide⟩
def raw680Units : List ℕ := [1, 2]
theorem raw680Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw680Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw680Spec.q raw680Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw680Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw680Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw680Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw680Units raw680Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw680Units raw680Right (by decide +kernel) (by decide +kernel)]
#print axioms raw680Observed
#print axioms raw680Valid
#print axioms raw680Row

def raw681Poly : Poly := [((1/1:ℚ),26,(0,0,0,0,0,0,0)),((-1/1:ℚ),37,(0,(-3),0,0,0,0,0)),((-1/1:ℚ),50,(0,(-3),0,0,0,0,0)),((1/1:ℚ),80,(0,0,0,0,0,0,0))]
def raw681Left : ℕ→ℕ
  | 1 => 80
  | 2 => 26
  | _ => 0
def raw681Right : ℕ→ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
def raw681Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨681,270,3,10,(-270),raw681Left,raw681Right,0,(-3),0,0⟩
theorem raw681Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw681Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw681Spec]
  decide +kernel
theorem raw681Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw681Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw681Spec x y z w 1 v := by
  norm_num [eval,monomial,raw681Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw681Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw681Left,raw681Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw681Observation : Fin 553 := ⟨110,by decide⟩
def raw681Units : List ℕ := [2, 1]
theorem raw681Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw681Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw681Spec.q raw681Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw681Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw681Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw681Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw681Units raw681Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw681Units raw681Right (by decide +kernel) (by decide +kernel)]
#print axioms raw681Observed
#print axioms raw681Valid
#print axioms raw681Row

def raw682Poly : Poly := [((1/1:ℚ),8,(0,0,0,0,0,0,0)),((-1/1:ℚ),37,(0,(-3),0,0,0,0,0)),((1/1:ℚ),46,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,(0,(-3),0,0,0,0,0))]
def raw682Left : ℕ→ℕ
  | 1 => 8
  | 2 => 46
  | _ => 0
def raw682Right : ℕ→ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
def raw682Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨682,270,3,(-10),270,raw682Left,raw682Right,0,(-3),0,0⟩
theorem raw682Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw682Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw682Spec]
  decide +kernel
theorem raw682Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw682Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw682Spec x y z w 1 v := by
  norm_num [eval,monomial,raw682Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw682Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw682Left,raw682Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw682Observation : Fin 553 := ⟨110,by decide⟩
def raw682Units : List ℕ := [2, 1]
theorem raw682Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw682Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw682Spec.q raw682Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw682Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw682Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw682Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw682Units raw682Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw682Units raw682Right (by decide +kernel) (by decide +kernel)]
#print axioms raw682Observed
#print axioms raw682Valid
#print axioms raw682Row

def raw683Poly : Poly := [((-1/1:ℚ),3,(2,(-1),(-2),0,0,0,0)),((-1/1:ℚ),55,(2,(-1),(-2),0,0,0,0)),((1/1:ℚ),130,(0,0,0,0,0,0,0)),((1/1:ℚ),131,(0,0,0,0,0,0,0))]
def raw683Left : ℕ→ℕ
  | 1 => 130
  | 2 => 131
  | _ => 0
def raw683Right : ℕ→ℕ
  | 1 => 3
  | 2 => 55
  | _ => 0
def raw683Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨683,270,3,12,(-225),raw683Left,raw683Right,2,(-1),(-2),0⟩
theorem raw683Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw683Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw683Spec]
  decide +kernel
theorem raw683Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw683Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw683Spec x y z w 1 v := by
  norm_num [eval,monomial,raw683Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw683Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw683Left,raw683Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw683Observation : Fin 553 := ⟨116,by decide⟩
def raw683Units : List ℕ := [1, 2]
theorem raw683Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw683Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw683Spec.q raw683Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw683Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw683Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw683Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw683Units raw683Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw683Units raw683Right (by decide +kernel) (by decide +kernel)]
#print axioms raw683Observed
#print axioms raw683Valid
#print axioms raw683Row

def raw684Poly : Poly := [((-1/1:ℚ),3,(2,(-1),(-2),0,0,0,0)),((-1/1:ℚ),20,(2,(-1),(-2),0,0,0,0)),((1/1:ℚ),132,(0,0,0,0,0,0,0)),((1/1:ℚ),133,(0,0,0,0,0,0,0))]
def raw684Left : ℕ→ℕ
  | 1 => 132
  | 2 => 133
  | _ => 0
def raw684Right : ℕ→ℕ
  | 1 => 20
  | 2 => 3
  | _ => 0
def raw684Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨684,270,3,(-12),225,raw684Left,raw684Right,2,(-1),(-2),0⟩
theorem raw684Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw684Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw684Spec]
  decide +kernel
theorem raw684Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw684Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw684Spec x y z w 1 v := by
  norm_num [eval,monomial,raw684Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw684Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw684Left,raw684Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw684Observation : Fin 553 := ⟨117,by decide⟩
def raw684Units : List ℕ := [2, 1]
theorem raw684Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw684Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw684Spec.q raw684Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw684Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw684Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw684Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw684Units raw684Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw684Units raw684Right (by decide +kernel) (by decide +kernel)]
#print axioms raw684Observed
#print axioms raw684Valid
#print axioms raw684Row

def raw685Poly : Poly := [((-1/1:ℚ),2,((-2),(-1),0,0,0,0,0)),((1/1:ℚ),12,(0,0,0,0,0,0,0)),((-1/1:ℚ),37,((-2),(-1),0,0,0,0,0)),((1/1:ℚ),95,(0,0,0,0,0,0,0))]
def raw685Left : ℕ→ℕ
  | 1 => 12
  | 2 => 95
  | _ => 0
def raw685Right : ℕ→ℕ
  | 1 => 37
  | 2 => 2
  | _ => 0
def raw685Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨685,270,3,15,(-180),raw685Left,raw685Right,(-2),(-1),0,0⟩
theorem raw685Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw685Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw685Spec]
  decide +kernel
theorem raw685Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw685Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw685Spec x y z w 1 v := by
  norm_num [eval,monomial,raw685Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw685Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw685Left,raw685Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw685Observation : Fin 553 := ⟨112,by decide⟩
def raw685Units : List ℕ := [2, 1]
theorem raw685Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw685Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw685Spec.q raw685Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw685Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw685Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw685Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw685Units raw685Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw685Units raw685Right (by decide +kernel) (by decide +kernel)]
#print axioms raw685Observed
#print axioms raw685Valid
#print axioms raw685Row

def raw686Poly : Poly := [((-1/1:ℚ),2,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),50,((-2),(-1),0,0,0,0,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0)),((1/1:ℚ),97,(0,0,0,0,0,0,0))]
def raw686Left : ℕ→ℕ
  | 1 => 97
  | 2 => 60
  | _ => 0
def raw686Right : ℕ→ℕ
  | 1 => 2
  | 2 => 50
  | _ => 0
def raw686Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨686,270,3,(-15),180,raw686Left,raw686Right,(-2),(-1),0,0⟩
theorem raw686Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw686Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw686Spec]
  decide +kernel
theorem raw686Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw686Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw686Spec x y z w 1 v := by
  norm_num [eval,monomial,raw686Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw686Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw686Left,raw686Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw686Observation : Fin 553 := ⟨111,by decide⟩
def raw686Units : List ℕ := [1, 2]
theorem raw686Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw686Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw686Spec.q raw686Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw686Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw686Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw686Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw686Units raw686Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw686Units raw686Right (by decide +kernel) (by decide +kernel)]
#print axioms raw686Observed
#print axioms raw686Valid
#print axioms raw686Row

def raw687Poly : Poly := [((-1/1:ℚ),6,(0,1,(-2),0,0,0,0)),((-1/1:ℚ),69,(0,1,(-2),0,0,0,0)),((1/1:ℚ),91,(0,0,0,0,0,0,0)),((1/1:ℚ),134,(0,0,0,0,0,0,0))]
def raw687Left : ℕ→ℕ
  | 1 => 91
  | 2 => 134
  | _ => 0
def raw687Right : ℕ→ℕ
  | 1 => 69
  | 2 => 6
  | _ => 0
def raw687Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨687,270,3,18,(-150),raw687Left,raw687Right,0,1,(-2),0⟩
theorem raw687Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw687Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw687Spec]
  decide +kernel
theorem raw687Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw687Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw687Spec x y z w 1 v := by
  norm_num [eval,monomial,raw687Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw687Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw687Left,raw687Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw687Observation : Fin 553 := ⟨118,by decide⟩
def raw687Units : List ℕ := [2, 1]
theorem raw687Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw687Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw687Spec.q raw687Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw687Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw687Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw687Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw687Units raw687Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw687Units raw687Right (by decide +kernel) (by decide +kernel)]
#print axioms raw687Observed
#print axioms raw687Valid
#print axioms raw687Row

def raw688Poly : Poly := [((-1/1:ℚ),28,(0,1,(-2),0,0,0,0)),((-1/1:ℚ),75,(0,1,(-2),0,0,0,0)),((1/1:ℚ),90,(0,0,0,0,0,0,0)),((1/1:ℚ),135,(0,0,0,0,0,0,0))]
def raw688Left : ℕ→ℕ
  | 1 => 135
  | 2 => 90
  | _ => 0
def raw688Right : ℕ→ℕ
  | 1 => 28
  | 2 => 75
  | _ => 0
def raw688Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨688,270,3,(-18),150,raw688Left,raw688Right,0,1,(-2),0⟩
theorem raw688Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw688Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw688Spec]
  decide +kernel
theorem raw688Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw688Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw688Spec x y z w 1 v := by
  norm_num [eval,monomial,raw688Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw688Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw688Left,raw688Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw688Observation : Fin 553 := ⟨119,by decide⟩
def raw688Units : List ℕ := [1, 2]
theorem raw688Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw688Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw688Spec.q raw688Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw688Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw688Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw688Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw688Units raw688Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw688Units raw688Right (by decide +kernel) (by decide +kernel)]
#print axioms raw688Observed
#print axioms raw688Valid
#print axioms raw688Row

def raw689Poly : Poly := [((1/1:ℚ),14,(0,0,0,0,0,0,0)),((-1/1:ℚ),20,(2,(-3),0,0,0,0,0)),((1/1:ℚ),53,(0,0,0,0,0,0,0)),((-1/1:ℚ),55,(2,(-3),0,0,0,0,0))]
def raw689Left : ℕ→ℕ
  | 1 => 14
  | 2 => 53
  | _ => 0
def raw689Right : ℕ→ℕ
  | 1 => 55
  | 2 => 20
  | _ => 0
def raw689Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨689,270,3,20,(-135),raw689Left,raw689Right,2,(-3),0,0⟩
theorem raw689Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw689Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw689Spec]
  decide +kernel
theorem raw689Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw689Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw689Spec x y z w 1 v := by
  norm_num [eval,monomial,raw689Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw689Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw689Left,raw689Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw689Observation : Fin 553 := ⟨113,by decide⟩
def raw689Units : List ℕ := [2, 1]
theorem raw689Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw689Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw689Spec.q raw689Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw689Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw689Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw689Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw689Units raw689Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw689Units raw689Right (by decide +kernel) (by decide +kernel)]
#print axioms raw689Observed
#print axioms raw689Valid
#print axioms raw689Row

def raw690Poly : Poly := [((-1/1:ℚ),20,(2,(-3),0,0,0,0,0)),((1/1:ℚ),22,(0,0,0,0,0,0,0)),((-1/1:ℚ),55,(2,(-3),0,0,0,0,0)),((1/1:ℚ),58,(0,0,0,0,0,0,0))]
def raw690Left : ℕ→ℕ
  | 1 => 22
  | 2 => 58
  | _ => 0
def raw690Right : ℕ→ℕ
  | 1 => 55
  | 2 => 20
  | _ => 0
def raw690Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨690,270,3,(-20),135,raw690Left,raw690Right,2,(-3),0,0⟩
theorem raw690Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw690Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw690Spec]
  decide +kernel
theorem raw690Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw690Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw690Spec x y z w 1 v := by
  norm_num [eval,monomial,raw690Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw690Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw690Left,raw690Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw690Observation : Fin 553 := ⟨113,by decide⟩
def raw690Units : List ℕ := [2, 1]
theorem raw690Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw690Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw690Spec.q raw690Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw690Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw690Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw690Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw690Units raw690Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw690Units raw690Right (by decide +kernel) (by decide +kernel)]
#print axioms raw690Observed
#print axioms raw690Valid
#print axioms raw690Row

def raw691Poly : Poly := [((-1/1:ℚ),64,((-2),(-3),2,0,0,0,0)),((1/1:ℚ),66,(0,0,0,0,0,0,0)),((-1/1:ℚ),135,((-2),(-3),2,0,0,0,0)),((1/1:ℚ),136,(0,0,0,0,0,0,0))]
def raw691Left : ℕ→ℕ
  | 1 => 66
  | 2 => 136
  | _ => 0
def raw691Right : ℕ→ℕ
  | 1 => 64
  | 2 => 135
  | _ => 0
def raw691Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨691,270,3,25,(-108),raw691Left,raw691Right,(-2),(-3),2,0⟩
theorem raw691Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw691Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw691Spec]
  decide +kernel
theorem raw691Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw691Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw691Spec x y z w 1 v := by
  norm_num [eval,monomial,raw691Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw691Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw691Left,raw691Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw691Observation : Fin 553 := ⟨120,by decide⟩
def raw691Units : List ℕ := [1, 2]
theorem raw691Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw691Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw691Spec.q raw691Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw691Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw691Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw691Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw691Units raw691Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw691Units raw691Right (by decide +kernel) (by decide +kernel)]
#print axioms raw691Observed
#print axioms raw691Valid
#print axioms raw691Row

def raw692Poly : Poly := [((1/1:ℚ),35,(0,0,0,0,0,0,0)),((-1/1:ℚ),38,((-2),(-3),2,0,0,0,0)),((-1/1:ℚ),134,((-2),(-3),2,0,0,0,0)),((1/1:ℚ),137,(0,0,0,0,0,0,0))]
def raw692Left : ℕ→ℕ
  | 1 => 137
  | 2 => 35
  | _ => 0
def raw692Right : ℕ→ℕ
  | 1 => 134
  | 2 => 38
  | _ => 0
def raw692Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨692,270,3,(-25),108,raw692Left,raw692Right,(-2),(-3),2,0⟩
theorem raw692Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw692Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw692Spec]
  decide +kernel
theorem raw692Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw692Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw692Spec x y z w 1 v := by
  norm_num [eval,monomial,raw692Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw692Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw692Left,raw692Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw692Observation : Fin 553 := ⟨121,by decide⟩
def raw692Units : List ℕ := [2, 1]
theorem raw692Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw692Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw692Spec.q raw692Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw692Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw692Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw692Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw692Units raw692Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw692Units raw692Right (by decide +kernel) (by decide +kernel)]
#print axioms raw692Observed
#print axioms raw692Valid
#print axioms raw692Row

def raw693Poly : Poly := [((-1/1:ℚ),1,((-2),3,(-2),0,0,0,0)),((-1/1:ℚ),8,((-2),3,(-2),0,0,0,0)),((1/1:ℚ),138,(0,0,0,0,0,0,0)),((1/1:ℚ),139,(0,0,0,0,0,0,0))]
def raw693Left : ℕ→ℕ
  | 1 => 138
  | 2 => 139
  | _ => 0
def raw693Right : ℕ→ℕ
  | 1 => 1
  | 2 => 8
  | _ => 0
def raw693Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨693,270,3,27,(-100),raw693Left,raw693Right,(-2),3,(-2),0⟩
theorem raw693Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw693Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw693Spec]
  decide +kernel
theorem raw693Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw693Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw693Spec x y z w 1 v := by
  norm_num [eval,monomial,raw693Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw693Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw693Left,raw693Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw693Observation : Fin 553 := ⟨122,by decide⟩
def raw693Units : List ℕ := [1, 2]
theorem raw693Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw693Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw693Spec.q raw693Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw693Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw693Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw693Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw693Units raw693Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw693Units raw693Right (by decide +kernel) (by decide +kernel)]
#print axioms raw693Observed
#print axioms raw693Valid
#print axioms raw693Row

def raw695Poly : Poly := [((-1/1:ℚ),2,(0,(-1),0,0,0,0,0)),((1/1:ℚ),16,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,(0,(-1),0,0,0,0,0)),((1/1:ℚ),69,(0,0,0,0,0,0,0))]
def raw695Left : ℕ→ℕ
  | 1 => 16
  | 2 => 69
  | _ => 0
def raw695Right : ℕ→ℕ
  | 1 => 2
  | 2 => 50
  | _ => 0
def raw695Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨695,270,3,30,(-90),raw695Left,raw695Right,0,(-1),0,0⟩
theorem raw695Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw695Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw695Spec]
  decide +kernel
theorem raw695Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw695Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw695Spec x y z w 1 v := by
  norm_num [eval,monomial,raw695Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw695Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw695Left,raw695Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw695Observation : Fin 553 := ⟨111,by decide⟩
def raw695Units : List ℕ := [1, 2]
theorem raw695Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw695Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw695Spec.q raw695Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw695Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw695Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw695Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw695Units raw695Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw695Units raw695Right (by decide +kernel) (by decide +kernel)]
#print axioms raw695Observed
#print axioms raw695Valid
#print axioms raw695Row

def raw696Poly : Poly := [((-1/1:ℚ),2,(0,(-1),0,0,0,0,0)),((1/1:ℚ),33,(0,0,0,0,0,0,0)),((-1/1:ℚ),37,(0,(-1),0,0,0,0,0)),((1/1:ℚ),75,(0,0,0,0,0,0,0))]
def raw696Left : ℕ→ℕ
  | 1 => 75
  | 2 => 33
  | _ => 0
def raw696Right : ℕ→ℕ
  | 1 => 37
  | 2 => 2
  | _ => 0
def raw696Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨696,270,3,(-30),90,raw696Left,raw696Right,0,(-1),0,0⟩
theorem raw696Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw696Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw696Spec]
  decide +kernel
theorem raw696Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw696Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw696Spec x y z w 1 v := by
  norm_num [eval,monomial,raw696Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw696Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw696Left,raw696Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw696Observation : Fin 553 := ⟨112,by decide⟩
def raw696Units : List ℕ := [2, 1]
theorem raw696Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw696Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw696Spec.q raw696Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw696Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw696Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw696Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw696Units raw696Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw696Units raw696Right (by decide +kernel) (by decide +kernel)]
#print axioms raw696Observed
#print axioms raw696Valid
#print axioms raw696Row

def raw697Poly : Poly := [((-1/1:ℚ),12,(2,1,(-2),0,0,0,0)),((1/1:ℚ),19,(0,0,0,0,0,0,0)),((-1/1:ℚ),34,(2,1,(-2),0,0,0,0)),((1/1:ℚ),99,(0,0,0,0,0,0,0))]
def raw697Left : ℕ→ℕ
  | 1 => 19
  | 2 => 99
  | _ => 0
def raw697Right : ℕ→ℕ
  | 1 => 34
  | 2 => 12
  | _ => 0
def raw697Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨697,270,3,36,(-75),raw697Left,raw697Right,2,1,(-2),0⟩
theorem raw697Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw697Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw697Spec]
  decide +kernel
theorem raw697Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw697Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw697Spec x y z w 1 v := by
  norm_num [eval,monomial,raw697Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw697Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw697Left,raw697Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw697Observation : Fin 553 := ⟨124,by decide⟩
def raw697Units : List ℕ := [2, 1]
theorem raw697Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw697Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw697Spec.q raw697Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw697Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw697Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw697Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw697Units raw697Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw697Units raw697Right (by decide +kernel) (by decide +kernel)]
#print axioms raw697Observed
#print axioms raw697Valid
#print axioms raw697Row

def raw698Poly : Poly := [((-1/1:ℚ),42,(2,1,(-2),0,0,0,0)),((1/1:ℚ),56,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(2,1,(-2),0,0,0,0)),((1/1:ℚ),101,(0,0,0,0,0,0,0))]
def raw698Left : ℕ→ℕ
  | 1 => 101
  | 2 => 56
  | _ => 0
def raw698Right : ℕ→ℕ
  | 1 => 60
  | 2 => 42
  | _ => 0
def raw698Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨698,270,3,(-36),75,raw698Left,raw698Right,2,1,(-2),0⟩
theorem raw698Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw698Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw698Spec]
  decide +kernel
theorem raw698Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw698Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw698Spec x y z w 1 v := by
  norm_num [eval,monomial,raw698Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw698Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw698Left,raw698Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw698Observation : Fin 553 := ⟨125,by decide⟩
def raw698Units : List ℕ := [2, 1]
theorem raw698Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw698Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw698Spec.q raw698Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw698Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw698Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw698Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw698Units raw698Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw698Units raw698Right (by decide +kernel) (by decide +kernel)]
#print axioms raw698Observed
#print axioms raw698Valid
#print axioms raw698Row

def raw699Poly : Poly := [((1/1:ℚ),3,(0,0,0,0,0,0,0)),((-1/1:ℚ),6,((-2),1,0,0,0,0,0)),((-1/1:ℚ),16,((-2),1,0,0,0,0,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0))]
def raw699Left : ℕ→ℕ
  | 1 => 3
  | 2 => 55
  | _ => 0
def raw699Right : ℕ→ℕ
  | 1 => 6
  | 2 => 16
  | _ => 0
def raw699Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨699,270,3,45,(-60),raw699Left,raw699Right,(-2),1,0,0⟩
theorem raw699Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw699Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw699Spec]
  decide +kernel
theorem raw699Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw699Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw699Spec x y z w 1 v := by
  norm_num [eval,monomial,raw699Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw699Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw699Left,raw699Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw699Observation : Fin 553 := ⟨126,by decide⟩
def raw699Units : List ℕ := [1, 2]
theorem raw699Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw699Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw699Spec.q raw699Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw699Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw699Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw699Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw699Units raw699Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw699Units raw699Right (by decide +kernel) (by decide +kernel)]
#print axioms raw699Observed
#print axioms raw699Valid
#print axioms raw699Row

def raw700Poly : Poly := [((1/1:ℚ),3,(0,0,0,0,0,0,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((-1/1:ℚ),28,((-2),1,0,0,0,0,0)),((-1/1:ℚ),33,((-2),1,0,0,0,0,0))]
def raw700Left : ℕ→ℕ
  | 1 => 20
  | 2 => 3
  | _ => 0
def raw700Right : ℕ→ℕ
  | 1 => 33
  | 2 => 28
  | _ => 0
def raw700Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨700,270,3,(-45),60,raw700Left,raw700Right,(-2),1,0,0⟩
theorem raw700Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw700Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw700Spec]
  decide +kernel
theorem raw700Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw700Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw700Spec x y z w 1 v := by
  norm_num [eval,monomial,raw700Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw700Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw700Left,raw700Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw700Observation : Fin 553 := ⟨127,by decide⟩
def raw700Units : List ℕ := [2, 1]
theorem raw700Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw700Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw700Spec.q raw700Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw700Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw700Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw700Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw700Units raw700Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw700Units raw700Right (by decide +kernel) (by decide +kernel)]
#print axioms raw700Observed
#print axioms raw700Valid
#print axioms raw700Row

def raw701Poly : Poly := [((-1/1:ℚ),19,(0,(-3),2,0,0,0,0)),((1/1:ℚ),31,(0,0,0,0,0,0,0)),((1/1:ℚ),39,(0,0,0,0,0,0,0)),((-1/1:ℚ),94,(0,(-3),2,0,0,0,0))]
def raw701Left : ℕ→ℕ
  | 1 => 31
  | 2 => 39
  | _ => 0
def raw701Right : ℕ→ℕ
  | 1 => 94
  | 2 => 19
  | _ => 0
def raw701Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨701,270,3,50,(-54),raw701Left,raw701Right,0,(-3),2,0⟩
theorem raw701Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw701Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw701Spec]
  decide +kernel
theorem raw701Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw701Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw701Spec x y z w 1 v := by
  norm_num [eval,monomial,raw701Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw701Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw701Left,raw701Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw701Observation : Fin 553 := ⟨128,by decide⟩
def raw701Units : List ℕ := [2, 1]
theorem raw701Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw701Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw701Spec.q raw701Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw701Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw701Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw701Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw701Units raw701Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw701Units raw701Right (by decide +kernel) (by decide +kernel)]
#print axioms raw701Observed
#print axioms raw701Valid
#print axioms raw701Row

def raw702Poly : Poly := [((1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,0,0,0,0,0,0)),((-1/1:ℚ),56,(0,(-3),2,0,0,0,0)),((-1/1:ℚ),96,(0,(-3),2,0,0,0,0))]
def raw702Left : ℕ→ℕ
  | 1 => 18
  | 2 => 24
  | _ => 0
def raw702Right : ℕ→ℕ
  | 1 => 56
  | 2 => 96
  | _ => 0
def raw702Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨702,270,3,(-50),54,raw702Left,raw702Right,0,(-3),2,0⟩
theorem raw702Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw702Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw702Spec]
  decide +kernel
theorem raw702Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw702Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw702Spec x y z w 1 v := by
  norm_num [eval,monomial,raw702Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw702Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw702Left,raw702Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw702Observation : Fin 553 := ⟨129,by decide⟩
def raw702Units : List ℕ := [1, 2]
theorem raw702Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw702Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw702Spec.q raw702Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw702Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw702Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw702Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw702Units raw702Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw702Units raw702Right (by decide +kernel) (by decide +kernel)]
#print axioms raw702Observed
#print axioms raw702Valid
#print axioms raw702Row

def raw703Poly : Poly := [((-1/1:ℚ),18,(0,3,(-2),0,0,0,0)),((-1/1:ℚ),24,(0,3,(-2),0,0,0,0)),((1/1:ℚ),56,(0,0,0,0,0,0,0)),((1/1:ℚ),96,(0,0,0,0,0,0,0))]
def raw703Left : ℕ→ℕ
  | 1 => 56
  | 2 => 96
  | _ => 0
def raw703Right : ℕ→ℕ
  | 1 => 18
  | 2 => 24
  | _ => 0
def raw703Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨703,270,3,54,(-50),raw703Left,raw703Right,0,3,(-2),0⟩
theorem raw703Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw703Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw703Spec]
  decide +kernel
theorem raw703Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw703Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw703Spec x y z w 1 v := by
  norm_num [eval,monomial,raw703Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw703Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw703Left,raw703Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw703Observation : Fin 553 := ⟨130,by decide⟩
def raw703Units : List ℕ := [1, 2]
theorem raw703Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw703Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw703Spec.q raw703Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw703Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw703Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw703Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw703Units raw703Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw703Units raw703Right (by decide +kernel) (by decide +kernel)]
#print axioms raw703Observed
#print axioms raw703Valid
#print axioms raw703Row

def raw704Poly : Poly := [((1/1:ℚ),19,(0,0,0,0,0,0,0)),((-1/1:ℚ),31,(0,3,(-2),0,0,0,0)),((-1/1:ℚ),39,(0,3,(-2),0,0,0,0)),((1/1:ℚ),94,(0,0,0,0,0,0,0))]
def raw704Left : ℕ→ℕ
  | 1 => 94
  | 2 => 19
  | _ => 0
def raw704Right : ℕ→ℕ
  | 1 => 31
  | 2 => 39
  | _ => 0
def raw704Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨704,270,3,(-54),50,raw704Left,raw704Right,0,3,(-2),0⟩
theorem raw704Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw704Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw704Spec]
  decide +kernel
theorem raw704Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw704Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw704Spec x y z w 1 v := by
  norm_num [eval,monomial,raw704Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw704Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw704Left,raw704Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw704Observation : Fin 553 := ⟨131,by decide⟩
def raw704Units : List ℕ := [1, 2]
theorem raw704Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw704Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw704Spec.q raw704Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw704Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw704Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw704Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw704Units raw704Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw704Units raw704Right (by decide +kernel) (by decide +kernel)]
#print axioms raw704Observed
#print axioms raw704Valid
#print axioms raw704Row

def raw705Poly : Poly := [((-1/1:ℚ),3,(2,(-1),0,0,0,0,0)),((-1/1:ℚ),20,(2,(-1),0,0,0,0,0)),((1/1:ℚ),28,(0,0,0,0,0,0,0)),((1/1:ℚ),33,(0,0,0,0,0,0,0))]
def raw705Left : ℕ→ℕ
  | 1 => 33
  | 2 => 28
  | _ => 0
def raw705Right : ℕ→ℕ
  | 1 => 20
  | 2 => 3
  | _ => 0
def raw705Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨705,270,3,60,(-45),raw705Left,raw705Right,2,(-1),0,0⟩
theorem raw705Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw705Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw705Spec]
  decide +kernel
theorem raw705Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw705Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw705Spec x y z w 1 v := by
  norm_num [eval,monomial,raw705Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw705Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw705Left,raw705Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw705Observation : Fin 553 := ⟨117,by decide⟩
def raw705Units : List ℕ := [2, 1]
theorem raw705Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw705Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw705Spec.q raw705Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw705Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw705Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw705Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw705Units raw705Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw705Units raw705Right (by decide +kernel) (by decide +kernel)]
#print axioms raw705Observed
#print axioms raw705Valid
#print axioms raw705Row

def raw706Poly : Poly := [((-1/1:ℚ),3,(2,(-1),0,0,0,0,0)),((1/1:ℚ),6,(0,0,0,0,0,0,0)),((1/1:ℚ),16,(0,0,0,0,0,0,0)),((-1/1:ℚ),55,(2,(-1),0,0,0,0,0))]
def raw706Left : ℕ→ℕ
  | 1 => 6
  | 2 => 16
  | _ => 0
def raw706Right : ℕ→ℕ
  | 1 => 3
  | 2 => 55
  | _ => 0
def raw706Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨706,270,3,(-60),45,raw706Left,raw706Right,2,(-1),0,0⟩
theorem raw706Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw706Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw706Spec]
  decide +kernel
theorem raw706Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw706Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw706Spec x y z w 1 v := by
  norm_num [eval,monomial,raw706Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw706Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw706Left,raw706Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw706Observation : Fin 553 := ⟨116,by decide⟩
def raw706Units : List ℕ := [1, 2]
theorem raw706Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw706Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw706Spec.q raw706Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw706Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw706Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw706Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw706Units raw706Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw706Units raw706Right (by decide +kernel) (by decide +kernel)]
#print axioms raw706Observed
#print axioms raw706Valid
#print axioms raw706Row

def raw707Poly : Poly := [((1/1:ℚ),42,(0,0,0,0,0,0,0)),((-1/1:ℚ),56,((-2),(-1),2,0,0,0,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0)),((-1/1:ℚ),101,((-2),(-1),2,0,0,0,0))]
def raw707Left : ℕ→ℕ
  | 1 => 60
  | 2 => 42
  | _ => 0
def raw707Right : ℕ→ℕ
  | 1 => 101
  | 2 => 56
  | _ => 0
def raw707Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨707,270,3,75,(-36),raw707Left,raw707Right,(-2),(-1),2,0⟩
theorem raw707Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw707Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw707Spec]
  decide +kernel
theorem raw707Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw707Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw707Spec x y z w 1 v := by
  norm_num [eval,monomial,raw707Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw707Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw707Left,raw707Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw707Observation : Fin 553 := ⟨132,by decide⟩
def raw707Units : List ℕ := [2, 1]
theorem raw707Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw707Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw707Spec.q raw707Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw707Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw707Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw707Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw707Units raw707Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw707Units raw707Right (by decide +kernel) (by decide +kernel)]
#print axioms raw707Observed
#print axioms raw707Valid
#print axioms raw707Row

def raw708Poly : Poly := [((1/1:ℚ),12,(0,0,0,0,0,0,0)),((-1/1:ℚ),19,((-2),(-1),2,0,0,0,0)),((1/1:ℚ),34,(0,0,0,0,0,0,0)),((-1/1:ℚ),99,((-2),(-1),2,0,0,0,0))]
def raw708Left : ℕ→ℕ
  | 1 => 34
  | 2 => 12
  | _ => 0
def raw708Right : ℕ→ℕ
  | 1 => 19
  | 2 => 99
  | _ => 0
def raw708Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨708,270,3,(-75),36,raw708Left,raw708Right,(-2),(-1),2,0⟩
theorem raw708Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw708Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw708Spec]
  decide +kernel
theorem raw708Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw708Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw708Spec x y z w 1 v := by
  norm_num [eval,monomial,raw708Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw708Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw708Left,raw708Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw708Observation : Fin 553 := ⟨133,by decide⟩
def raw708Units : List ℕ := [1, 2]
theorem raw708Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw708Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw708Spec.q raw708Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw708Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw708Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw708Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw708Units raw708Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw708Units raw708Right (by decide +kernel) (by decide +kernel)]
#print axioms raw708Observed
#print axioms raw708Valid
#print axioms raw708Row

def raw709Poly : Poly := [((1/1:ℚ),2,(0,0,0,0,0,0,0)),((-1/1:ℚ),33,(0,1,0,0,0,0,0)),((1/1:ℚ),37,(0,0,0,0,0,0,0)),((-1/1:ℚ),75,(0,1,0,0,0,0,0))]
def raw709Left : ℕ→ℕ
  | 1 => 37
  | 2 => 2
  | _ => 0
def raw709Right : ℕ→ℕ
  | 1 => 75
  | 2 => 33
  | _ => 0
def raw709Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨709,270,3,90,(-30),raw709Left,raw709Right,0,1,0,0⟩
theorem raw709Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw709Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw709Spec]
  decide +kernel
theorem raw709Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw709Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw709Spec x y z w 1 v := by
  norm_num [eval,monomial,raw709Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw709Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw709Left,raw709Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw709Observation : Fin 553 := ⟨114,by decide⟩
def raw709Units : List ℕ := [2, 1]
theorem raw709Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw709Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw709Spec.q raw709Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw709Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw709Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw709Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw709Units raw709Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw709Units raw709Right (by decide +kernel) (by decide +kernel)]
#print axioms raw709Observed
#print axioms raw709Valid
#print axioms raw709Row

def raw710Poly : Poly := [((1/1:ℚ),2,(0,0,0,0,0,0,0)),((-1/1:ℚ),16,(0,1,0,0,0,0,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0)),((-1/1:ℚ),69,(0,1,0,0,0,0,0))]
def raw710Left : ℕ→ℕ
  | 1 => 2
  | 2 => 50
  | _ => 0
def raw710Right : ℕ→ℕ
  | 1 => 16
  | 2 => 69
  | _ => 0
def raw710Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨710,270,3,(-90),30,raw710Left,raw710Right,0,1,0,0⟩
theorem raw710Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw710Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw710Spec]
  decide +kernel
theorem raw710Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw710Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw710Spec x y z w 1 v := by
  norm_num [eval,monomial,raw710Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw710Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw710Left,raw710Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw710Observation : Fin 553 := ⟨115,by decide⟩
def raw710Units : List ℕ := [1, 2]
theorem raw710Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw710Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw710Spec.q raw710Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw710Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw710Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw710Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw710Units raw710Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw710Units raw710Right (by decide +kernel) (by decide +kernel)]
#print axioms raw710Observed
#print axioms raw710Valid
#print axioms raw710Row

def raw715Poly : Poly := [((1/1:ℚ),20,(0,0,0,0,0,0,0)),((-1/1:ℚ),22,((-2),3,0,0,0,0,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0)),((-1/1:ℚ),58,((-2),3,0,0,0,0,0))]
def raw715Left : ℕ→ℕ
  | 1 => 55
  | 2 => 20
  | _ => 0
def raw715Right : ℕ→ℕ
  | 1 => 22
  | 2 => 58
  | _ => 0
def raw715Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨715,270,3,135,(-20),raw715Left,raw715Right,(-2),3,0,0⟩
theorem raw715Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw715Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw715Spec]
  decide +kernel
theorem raw715Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw715Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw715Spec x y z w 1 v := by
  norm_num [eval,monomial,raw715Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw715Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw715Left,raw715Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw715Observation : Fin 553 := ⟨138,by decide⟩
def raw715Units : List ℕ := [1, 2]
theorem raw715Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw715Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw715Spec.q raw715Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw715Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw715Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw715Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw715Units raw715Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw715Units raw715Right (by decide +kernel) (by decide +kernel)]
#print axioms raw715Observed
#print axioms raw715Valid
#print axioms raw715Row

def raw716Poly : Poly := [((-1/1:ℚ),14,((-2),3,0,0,0,0,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((-1/1:ℚ),53,((-2),3,0,0,0,0,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0))]
def raw716Left : ℕ→ℕ
  | 1 => 55
  | 2 => 20
  | _ => 0
def raw716Right : ℕ→ℕ
  | 1 => 14
  | 2 => 53
  | _ => 0
def raw716Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨716,270,3,(-135),20,raw716Left,raw716Right,(-2),3,0,0⟩
theorem raw716Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw716Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw716Spec]
  decide +kernel
theorem raw716Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw716Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw716Spec x y z w 1 v := by
  norm_num [eval,monomial,raw716Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw716Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw716Left,raw716Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw716Observation : Fin 553 := ⟨139,by decide⟩
def raw716Units : List ℕ := [1, 2]
theorem raw716Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw716Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw716Spec.q raw716Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw716Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw716Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw716Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw716Units raw716Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw716Units raw716Right (by decide +kernel) (by decide +kernel)]
#print axioms raw716Observed
#print axioms raw716Valid
#print axioms raw716Row

def raw717Poly : Poly := [((1/1:ℚ),28,(0,0,0,0,0,0,0)),((1/1:ℚ),75,(0,0,0,0,0,0,0)),((-1/1:ℚ),90,(0,(-1),2,0,0,0,0)),((-1/1:ℚ),135,(0,(-1),2,0,0,0,0))]
def raw717Left : ℕ→ℕ
  | 1 => 28
  | 2 => 75
  | _ => 0
def raw717Right : ℕ→ℕ
  | 1 => 135
  | 2 => 90
  | _ => 0
def raw717Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨717,270,3,150,(-18),raw717Left,raw717Right,0,(-1),2,0⟩
theorem raw717Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw717Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw717Spec]
  decide +kernel
theorem raw717Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw717Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw717Spec x y z w 1 v := by
  norm_num [eval,monomial,raw717Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw717Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw717Left,raw717Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw717Observation : Fin 553 := ⟨140,by decide⟩
def raw717Units : List ℕ := [2, 1]
theorem raw717Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw717Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw717Spec.q raw717Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw717Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw717Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw717Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw717Units raw717Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw717Units raw717Right (by decide +kernel) (by decide +kernel)]
#print axioms raw717Observed
#print axioms raw717Valid
#print axioms raw717Row

def raw718Poly : Poly := [((1/1:ℚ),6,(0,0,0,0,0,0,0)),((1/1:ℚ),69,(0,0,0,0,0,0,0)),((-1/1:ℚ),91,(0,(-1),2,0,0,0,0)),((-1/1:ℚ),134,(0,(-1),2,0,0,0,0))]
def raw718Left : ℕ→ℕ
  | 1 => 69
  | 2 => 6
  | _ => 0
def raw718Right : ℕ→ℕ
  | 1 => 91
  | 2 => 134
  | _ => 0
def raw718Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨718,270,3,(-150),18,raw718Left,raw718Right,0,(-1),2,0⟩
theorem raw718Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw718Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw718Spec]
  decide +kernel
theorem raw718Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw718Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw718Spec x y z w 1 v := by
  norm_num [eval,monomial,raw718Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw718Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw718Left,raw718Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw718Observation : Fin 553 := ⟨141,by decide⟩
def raw718Units : List ℕ := [1, 2]
theorem raw718Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw718Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw718Spec.q raw718Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw718Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw718Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw718Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw718Units raw718Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw718Units raw718Right (by decide +kernel) (by decide +kernel)]
#print axioms raw718Observed
#print axioms raw718Valid
#print axioms raw718Row

def raw719Poly : Poly := [((1/1:ℚ),2,(0,0,0,0,0,0,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(2,1,0,0,0,0,0)),((-1/1:ℚ),97,(2,1,0,0,0,0,0))]
def raw719Left : ℕ→ℕ
  | 1 => 2
  | 2 => 50
  | _ => 0
def raw719Right : ℕ→ℕ
  | 1 => 97
  | 2 => 60
  | _ => 0
def raw719Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨719,270,3,180,(-15),raw719Left,raw719Right,2,1,0,0⟩
theorem raw719Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw719Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw719Spec]
  decide +kernel
theorem raw719Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw719Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw719Spec x y z w 1 v := by
  norm_num [eval,monomial,raw719Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw719Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw719Left,raw719Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw719Observation : Fin 553 := ⟨142,by decide⟩
def raw719Units : List ℕ := [2, 1]
theorem raw719Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw719Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw719Spec.q raw719Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw719Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw719Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw719Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw719Units raw719Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw719Units raw719Right (by decide +kernel) (by decide +kernel)]
#print axioms raw719Observed
#print axioms raw719Valid
#print axioms raw719Row

def raw720Poly : Poly := [((1/1:ℚ),2,(0,0,0,0,0,0,0)),((-1/1:ℚ),12,(2,1,0,0,0,0,0)),((1/1:ℚ),37,(0,0,0,0,0,0,0)),((-1/1:ℚ),95,(2,1,0,0,0,0,0))]
def raw720Left : ℕ→ℕ
  | 1 => 37
  | 2 => 2
  | _ => 0
def raw720Right : ℕ→ℕ
  | 1 => 12
  | 2 => 95
  | _ => 0
def raw720Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨720,270,3,(-180),15,raw720Left,raw720Right,2,1,0,0⟩
theorem raw720Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw720Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw720Spec]
  decide +kernel
theorem raw720Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw720Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw720Spec x y z w 1 v := by
  norm_num [eval,monomial,raw720Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw720Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw720Left,raw720Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw720Observation : Fin 553 := ⟨143,by decide⟩
def raw720Units : List ℕ := [1, 2]
theorem raw720Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw720Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw720Spec.q raw720Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw720Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw720Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw720Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw720Units raw720Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw720Units raw720Right (by decide +kernel) (by decide +kernel)]
#print axioms raw720Observed
#print axioms raw720Valid
#print axioms raw720Row

def raw723Poly : Poly := [((-1/1:ℚ),8,(0,3,0,0,0,0,0)),((1/1:ℚ),37,(0,0,0,0,0,0,0)),((-1/1:ℚ),46,(0,3,0,0,0,0,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0))]
def raw723Left : ℕ→ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
def raw723Right : ℕ→ℕ
  | 1 => 8
  | 2 => 46
  | _ => 0
def raw723Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨723,270,3,270,(-10),raw723Left,raw723Right,0,3,0,0⟩
theorem raw723Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw723Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw723Spec]
  decide +kernel
theorem raw723Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw723Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw723Spec x y z w 1 v := by
  norm_num [eval,monomial,raw723Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw723Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw723Left,raw723Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw723Observation : Fin 553 := ⟨146,by decide⟩
def raw723Units : List ℕ := [1, 2]
theorem raw723Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw723Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw723Spec.q raw723Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw723Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw723Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw723Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw723Units raw723Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw723Units raw723Right (by decide +kernel) (by decide +kernel)]
#print axioms raw723Observed
#print axioms raw723Valid
#print axioms raw723Row

def raw740Poly : Poly := [((-1/1:ℚ),2,((-2),(-3),0,0,0,0,0)),((-1/1:ℚ),91,((-2),(-3),0,0,0,0,0)),((-1/1:ℚ),99,((-2),(-3),0,0,0,0,0)),((-1/1:ℚ),101,((-2),(-3),0,0,0,0,0)),((1/1:ℚ),142,(0,0,0,0,0,0,0)),((1/1:ℚ),143,(0,0,0,0,0,0,0)),((1/1:ℚ),144,(0,0,0,0,0,0,0)),((1/1:ℚ),145,(0,0,0,0,0,0,0))]
def raw740Left : ℕ→ℕ
  | 1 => 142
  | 2 => 143
  | 3 => 144
  | 4 => 145
  | _ => 0
def raw740Right : ℕ→ℕ
  | 1 => 99
  | 2 => 2
  | 3 => 101
  | 4 => 91
  | _ => 0
def raw740Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨740,270,5,1,(-108),raw740Left,raw740Right,(-2),(-3),0,0⟩
theorem raw740Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw740Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw740Spec]
  decide +kernel
theorem raw740Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw740Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw740Spec x y z w 1 v := by
  norm_num [eval,monomial,raw740Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw740Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw740Left,raw740Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw740Observation : Fin 553 := ⟨162,by decide⟩
def raw740Units : List ℕ := [2, 4, 1, 3]
theorem raw740Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw740Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw740Spec.q raw740Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw740Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 5 raw740Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw740Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw740Units raw740Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=5) v raw740Units raw740Right (by decide +kernel) (by decide +kernel)]
#print axioms raw740Observed
#print axioms raw740Valid
#print axioms raw740Row

def raw742Poly : Poly := [((-1/1:ℚ),2,(0,(-3),0,0,0,0,0)),((1/1:ℚ),14,(0,0,0,0,0,0,0)),((-1/1:ℚ),90,(0,(-3),0,0,0,0,0)),((-1/1:ℚ),91,(0,(-3),0,0,0,0,0)),((-1/1:ℚ),101,(0,(-3),0,0,0,0,0)),((1/1:ℚ),150,(0,0,0,0,0,0,0)),((1/1:ℚ),151,(0,0,0,0,0,0,0)),((1/1:ℚ),152,(0,0,0,0,0,0,0))]
def raw742Left : ℕ→ℕ
  | 1 => 150
  | 2 => 14
  | 3 => 151
  | 4 => 152
  | _ => 0
def raw742Right : ℕ→ℕ
  | 1 => 2
  | 2 => 101
  | 3 => 91
  | 4 => 90
  | _ => 0
def raw742Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨742,270,5,2,(-54),raw742Left,raw742Right,0,(-3),0,0⟩
theorem raw742Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw742Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw742Spec]
  decide +kernel
theorem raw742Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw742Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw742Spec x y z w 1 v := by
  norm_num [eval,monomial,raw742Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw742Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw742Left,raw742Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw742Observation : Fin 553 := ⟨164,by decide⟩
def raw742Units : List ℕ := [1, 4, 3, 2]
theorem raw742Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw742Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw742Spec.q raw742Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw742Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 5 raw742Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw742Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw742Units raw742Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=5) v raw742Units raw742Right (by decide +kernel) (by decide +kernel)]
#print axioms raw742Observed
#print axioms raw742Valid
#print axioms raw742Row

def raw744Poly : Poly := [((-1/1:ℚ),19,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),37,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),38,((-2),(-1),0,0,0,0,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0)),((-1/1:ℚ),135,((-2),(-1),0,0,0,0,0)),((1/1:ℚ),156,(0,0,0,0,0,0,0)),((1/1:ℚ),157,(0,0,0,0,0,0,0)),((1/1:ℚ),158,(0,0,0,0,0,0,0))]
def raw744Left : ℕ→ℕ
  | 1 => 156
  | 2 => 157
  | 3 => 60
  | 4 => 158
  | _ => 0
def raw744Right : ℕ→ℕ
  | 1 => 38
  | 2 => 135
  | 3 => 19
  | 4 => 37
  | _ => 0
def raw744Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨744,270,5,3,(-36),raw744Left,raw744Right,(-2),(-1),0,0⟩
theorem raw744Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw744Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw744Spec]
  decide +kernel
theorem raw744Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw744Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw744Spec x y z w 1 v := by
  norm_num [eval,monomial,raw744Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw744Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw744Left,raw744Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw744Observation : Fin 553 := ⟨166,by decide⟩
def raw744Units : List ℕ := [3, 4, 1, 2]
theorem raw744Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw744Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw744Spec.q raw744Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw744Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 5 raw744Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw744Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw744Units raw744Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=5) v raw744Units raw744Right (by decide +kernel) (by decide +kernel)]
#print axioms raw744Observed
#print axioms raw744Valid
#print axioms raw744Row

def raw745Poly : Poly := [((1/1:ℚ),12,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),56,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),64,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),134,((-2),(-1),0,0,0,0,0)),((1/1:ℚ),159,(0,0,0,0,0,0,0)),((1/1:ℚ),160,(0,0,0,0,0,0,0)),((1/1:ℚ),161,(0,0,0,0,0,0,0))]
def raw745Left : ℕ→ℕ
  | 1 => 159
  | 2 => 12
  | 3 => 160
  | 4 => 161
  | _ => 0
def raw745Right : ℕ→ℕ
  | 1 => 50
  | 2 => 56
  | 3 => 134
  | 4 => 64
  | _ => 0
def raw745Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨745,270,5,(-3),36,raw745Left,raw745Right,(-2),(-1),0,0⟩
theorem raw745Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw745Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw745Spec]
  decide +kernel
theorem raw745Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw745Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw745Spec x y z w 1 v := by
  norm_num [eval,monomial,raw745Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw745Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw745Left,raw745Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw745Observation : Fin 553 := ⟨167,by decide⟩
def raw745Units : List ℕ := [1, 2, 4, 3]
theorem raw745Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw745Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw745Spec.q raw745Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw745Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 5 raw745Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw745Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw745Units raw745Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=5) v raw745Units raw745Right (by decide +kernel) (by decide +kernel)]
#print axioms raw745Observed
#print axioms raw745Valid
#print axioms raw745Row

def raw748Poly : Poly := [((-1/1:ℚ),50,(0,(-1),0,0,0,0,0)),((-1/1:ℚ),56,(0,(-1),0,0,0,0,0)),((1/1:ℚ),75,(0,0,0,0,0,0,0)),((-1/1:ℚ),94,(0,(-1),0,0,0,0,0)),((1/1:ℚ),133,(0,0,0,0,0,0,0)),((-1/1:ℚ),134,(0,(-1),0,0,0,0,0)),((1/1:ℚ),168,(0,0,0,0,0,0,0)),((1/1:ℚ),169,(0,0,0,0,0,0,0))]
def raw748Left : ℕ→ℕ
  | 1 => 75
  | 2 => 168
  | 3 => 133
  | 4 => 169
  | _ => 0
def raw748Right : ℕ→ℕ
  | 1 => 94
  | 2 => 50
  | 3 => 56
  | 4 => 134
  | _ => 0
def raw748Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨748,270,5,6,(-18),raw748Left,raw748Right,0,(-1),0,0⟩
theorem raw748Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw748Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw748Spec]
  decide +kernel
theorem raw748Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw748Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw748Spec x y z w 1 v := by
  norm_num [eval,monomial,raw748Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw748Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw748Left,raw748Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw748Observation : Fin 553 := ⟨170,by decide⟩
def raw748Units : List ℕ := [2, 3, 1, 4]
theorem raw748Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw748Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw748Spec.q raw748Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw748Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 5 raw748Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw748Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw748Units raw748Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=5) v raw748Units raw748Right (by decide +kernel) (by decide +kernel)]
#print axioms raw748Observed
#print axioms raw748Valid
#print axioms raw748Row

def raw749Poly : Poly := [((-1/1:ℚ),19,(0,(-1),0,0,0,0,0)),((-1/1:ℚ),37,(0,(-1),0,0,0,0,0)),((1/1:ℚ),69,(0,0,0,0,0,0,0)),((-1/1:ℚ),96,(0,(-1),0,0,0,0,0)),((1/1:ℚ),130,(0,0,0,0,0,0,0)),((-1/1:ℚ),135,(0,(-1),0,0,0,0,0)),((1/1:ℚ),170,(0,0,0,0,0,0,0)),((1/1:ℚ),171,(0,0,0,0,0,0,0))]
def raw749Left : ℕ→ℕ
  | 1 => 170
  | 2 => 130
  | 3 => 171
  | 4 => 69
  | _ => 0
def raw749Right : ℕ→ℕ
  | 1 => 135
  | 2 => 19
  | 3 => 37
  | 4 => 96
  | _ => 0
def raw749Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨749,270,5,(-6),18,raw749Left,raw749Right,0,(-1),0,0⟩
theorem raw749Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw749Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw749Spec]
  decide +kernel
theorem raw749Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw749Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw749Spec x y z w 1 v := by
  norm_num [eval,monomial,raw749Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw749Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw749Left,raw749Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw749Observation : Fin 553 := ⟨171,by decide⟩
def raw749Units : List ℕ := [2, 3, 4, 1]
theorem raw749Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw749Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw749Spec.q raw749Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw749Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 5 raw749Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw749Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw749Units raw749Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=5) v raw749Units raw749Right (by decide +kernel) (by decide +kernel)]
#print axioms raw749Observed
#print axioms raw749Valid
#print axioms raw749Row

def raw767Poly : Poly := [((-1/1:ℚ),2,(0,(-1),(-2),0,0,0,0)),((-1/1:ℚ),50,(0,(-1),(-2),0,0,0,0)),((1/1:ℚ),170,(0,0,0,0,0,0,0)),((1/1:ℚ),175,(0,0,0,0,0,0,0))]
def raw767Left : ℕ→ℕ
  | 1 => 170
  | 5 => 175
  | _ => 0
def raw767Right : ℕ→ℕ
  | 1 => 50
  | 5 => 2
  | _ => 0
def raw767Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨767,270,6,3,(-225),raw767Left,raw767Right,0,(-1),(-2),0⟩
theorem raw767Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw767Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw767Spec]
  decide +kernel
theorem raw767Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw767Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw767Spec x y z w 1 v := by
  norm_num [eval,monomial,raw767Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw767Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw767Left,raw767Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw767Observation : Fin 553 := ⟨111,by decide⟩
def raw767Units : List ℕ := [5, 1]
theorem raw767Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw767Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw767Spec.q raw767Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw767Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw767Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw767Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw767Units raw767Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw767Units raw767Right (by decide +kernel) (by decide +kernel)]
#print axioms raw767Observed
#print axioms raw767Valid
#print axioms raw767Row

def raw768Poly : Poly := [((-1/1:ℚ),2,(0,(-1),(-2),0,0,0,0)),((-1/1:ℚ),37,(0,(-1),(-2),0,0,0,0)),((1/1:ℚ),169,(0,0,0,0,0,0,0)),((1/1:ℚ),172,(0,0,0,0,0,0,0))]
def raw768Left : ℕ→ℕ
  | 1 => 172
  | 5 => 169
  | _ => 0
def raw768Right : ℕ→ℕ
  | 1 => 2
  | 5 => 37
  | _ => 0
def raw768Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨768,270,6,(-3),225,raw768Left,raw768Right,0,(-1),(-2),0⟩
theorem raw768Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw768Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw768Spec]
  decide +kernel
theorem raw768Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw768Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw768Spec x y z w 1 v := by
  norm_num [eval,monomial,raw768Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw768Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw768Left,raw768Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw768Observation : Fin 553 := ⟨112,by decide⟩
def raw768Units : List ℕ := [1, 5]
theorem raw768Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw768Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw768Spec.q raw768Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw768Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw768Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw768Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw768Units raw768Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw768Units raw768Right (by decide +kernel) (by decide +kernel)]
#print axioms raw768Observed
#print axioms raw768Valid
#print axioms raw768Row

def raw769Poly : Poly := [((-1/1:ℚ),37,(0,(-3),0,0,0,0,0)),((1/1:ℚ),39,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,(0,(-3),0,0,0,0,0)),((1/1:ℚ),98,(0,0,0,0,0,0,0))]
def raw769Left : ℕ→ℕ
  | 1 => 98
  | 5 => 39
  | _ => 0
def raw769Right : ℕ→ℕ
  | 1 => 37
  | 5 => 50
  | _ => 0
def raw769Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨769,270,6,5,(-135),raw769Left,raw769Right,0,(-3),0,0⟩
theorem raw769Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw769Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw769Spec]
  decide +kernel
theorem raw769Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw769Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw769Spec x y z w 1 v := by
  norm_num [eval,monomial,raw769Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw769Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw769Left,raw769Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw769Observation : Fin 553 := ⟨110,by decide⟩
def raw769Units : List ℕ := [1, 5]
theorem raw769Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw769Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw769Spec.q raw769Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw769Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw769Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw769Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw769Units raw769Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw769Units raw769Right (by decide +kernel) (by decide +kernel)]
#print axioms raw769Observed
#print axioms raw769Valid
#print axioms raw769Row

def raw770Poly : Poly := [((1/1:ℚ),18,(0,0,0,0,0,0,0)),((-1/1:ℚ),37,(0,(-3),0,0,0,0,0)),((-1/1:ℚ),50,(0,(-3),0,0,0,0,0)),((1/1:ℚ),100,(0,0,0,0,0,0,0))]
def raw770Left : ℕ→ℕ
  | 1 => 18
  | 5 => 100
  | _ => 0
def raw770Right : ℕ→ℕ
  | 1 => 37
  | 5 => 50
  | _ => 0
def raw770Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨770,270,6,(-5),135,raw770Left,raw770Right,0,(-3),0,0⟩
theorem raw770Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw770Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw770Spec]
  decide +kernel
theorem raw770Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw770Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw770Spec x y z w 1 v := by
  norm_num [eval,monomial,raw770Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw770Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw770Left,raw770Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw770Observation : Fin 553 := ⟨110,by decide⟩
def raw770Units : List ℕ := [1, 5]
theorem raw770Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw770Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw770Spec.q raw770Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw770Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw770Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw770Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw770Units raw770Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw770Units raw770Right (by decide +kernel) (by decide +kernel)]
#print axioms raw770Observed
#print axioms raw770Valid
#print axioms raw770Row

def raw771Poly : Poly := [((-1/1:ℚ),28,(0,1,(-2),0,0,0,0)),((-1/1:ℚ),33,(0,1,(-2),0,0,0,0)),((1/1:ℚ),96,(0,0,0,0,0,0,0)),((1/1:ℚ),101,(0,0,0,0,0,0,0))]
def raw771Left : ℕ→ℕ
  | 1 => 101
  | 5 => 96
  | _ => 0
def raw771Right : ℕ→ℕ
  | 1 => 28
  | 5 => 33
  | _ => 0
def raw771Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨771,270,6,9,(-75),raw771Left,raw771Right,0,1,(-2),0⟩
theorem raw771Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw771Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw771Spec]
  decide +kernel
theorem raw771Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw771Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw771Spec x y z w 1 v := by
  norm_num [eval,monomial,raw771Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw771Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw771Left,raw771Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw771Observation : Fin 553 := ⟨127,by decide⟩
def raw771Units : List ℕ := [1, 5]
theorem raw771Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw771Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw771Spec.q raw771Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw771Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw771Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw771Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw771Units raw771Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw771Units raw771Right (by decide +kernel) (by decide +kernel)]
#print axioms raw771Observed
#print axioms raw771Valid
#print axioms raw771Row

def raw772Poly : Poly := [((-1/1:ℚ),6,(0,1,(-2),0,0,0,0)),((-1/1:ℚ),16,(0,1,(-2),0,0,0,0)),((1/1:ℚ),94,(0,0,0,0,0,0,0)),((1/1:ℚ),99,(0,0,0,0,0,0,0))]
def raw772Left : ℕ→ℕ
  | 1 => 94
  | 5 => 99
  | _ => 0
def raw772Right : ℕ→ℕ
  | 1 => 16
  | 5 => 6
  | _ => 0
def raw772Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨772,270,6,(-9),75,raw772Left,raw772Right,0,1,(-2),0⟩
theorem raw772Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw772Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw772Spec]
  decide +kernel
theorem raw772Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw772Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw772Spec x y z w 1 v := by
  norm_num [eval,monomial,raw772Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw772Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw772Left,raw772Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw772Observation : Fin 553 := ⟨126,by decide⟩
def raw772Units : List ℕ := [5, 1]
theorem raw772Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw772Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw772Spec.q raw772Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw772Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw772Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw772Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw772Units raw772Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw772Units raw772Right (by decide +kernel) (by decide +kernel)]
#print axioms raw772Observed
#print axioms raw772Valid
#print axioms raw772Row

def raw773Poly : Poly := [((-1/1:ℚ),2,(0,(-1),0,0,0,0,0)),((1/1:ℚ),28,(0,0,0,0,0,0,0)),((-1/1:ℚ),37,(0,(-1),0,0,0,0,0)),((1/1:ℚ),75,(0,0,0,0,0,0,0))]
def raw773Left : ℕ→ℕ
  | 1 => 75
  | 5 => 28
  | _ => 0
def raw773Right : ℕ→ℕ
  | 1 => 2
  | 5 => 37
  | _ => 0
def raw773Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨773,270,6,15,(-45),raw773Left,raw773Right,0,(-1),0,0⟩
theorem raw773Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw773Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw773Spec]
  decide +kernel
theorem raw773Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw773Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw773Spec x y z w 1 v := by
  norm_num [eval,monomial,raw773Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw773Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw773Left,raw773Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw773Observation : Fin 553 := ⟨112,by decide⟩
def raw773Units : List ℕ := [1, 5]
theorem raw773Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw773Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw773Spec.q raw773Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw773Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw773Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw773Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw773Units raw773Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw773Units raw773Right (by decide +kernel) (by decide +kernel)]
#print axioms raw773Observed
#print axioms raw773Valid
#print axioms raw773Row

def raw774Poly : Poly := [((-1/1:ℚ),2,(0,(-1),0,0,0,0,0)),((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,(0,(-1),0,0,0,0,0)),((1/1:ℚ),69,(0,0,0,0,0,0,0))]
def raw774Left : ℕ→ℕ
  | 1 => 6
  | 5 => 69
  | _ => 0
def raw774Right : ℕ→ℕ
  | 1 => 50
  | 5 => 2
  | _ => 0
def raw774Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨774,270,6,(-15),45,raw774Left,raw774Right,0,(-1),0,0⟩
theorem raw774Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw774Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw774Spec]
  decide +kernel
theorem raw774Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw774Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw774Spec x y z w 1 v := by
  norm_num [eval,monomial,raw774Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw774Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw774Left,raw774Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw774Observation : Fin 553 := ⟨111,by decide⟩
def raw774Units : List ℕ := [5, 1]
theorem raw774Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw774Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw774Spec.q raw774Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw774Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw774Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw774Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw774Units raw774Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw774Units raw774Right (by decide +kernel) (by decide +kernel)]
#print axioms raw774Observed
#print axioms raw774Valid
#print axioms raw774Row

def raw775Poly : Poly := [((1/1:ℚ),0,(0,0,0,0,0,0,0)),((1/1:ℚ),22,(0,0,0,0,0,0,0)),((-1/1:ℚ),38,(0,(-3),2,0,0,0,0)),((-1/1:ℚ),134,(0,(-3),2,0,0,0,0))]
def raw775Left : ℕ→ℕ
  | 1 => 22
  | 5 => 0
  | _ => 0
def raw775Right : ℕ→ℕ
  | 1 => 38
  | 5 => 134
  | _ => 0
def raw775Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨775,270,6,25,(-27),raw775Left,raw775Right,0,(-3),2,0⟩
theorem raw775Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw775Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw775Spec]
  decide +kernel
theorem raw775Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw775Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw775Spec x y z w 1 v := by
  norm_num [eval,monomial,raw775Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw775Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw775Left,raw775Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw775Observation : Fin 553 := ⟨121,by decide⟩
def raw775Units : List ℕ := [1, 5]
theorem raw775Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw775Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw775Spec.q raw775Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw775Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw775Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw775Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw775Units raw775Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw775Units raw775Right (by decide +kernel) (by decide +kernel)]
#print axioms raw775Observed
#print axioms raw775Valid
#print axioms raw775Row

def raw776Poly : Poly := [((1/1:ℚ),53,(0,0,0,0,0,0,0)),((-1/1:ℚ),64,(0,(-3),2,0,0,0,0)),((1/1:ℚ),72,(0,0,0,0,0,0,0)),((-1/1:ℚ),135,(0,(-3),2,0,0,0,0))]
def raw776Left : ℕ→ℕ
  | 1 => 72
  | 5 => 53
  | _ => 0
def raw776Right : ℕ→ℕ
  | 1 => 135
  | 5 => 64
  | _ => 0
def raw776Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨776,270,6,(-25),27,raw776Left,raw776Right,0,(-3),2,0⟩
theorem raw776Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw776Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw776Spec]
  decide +kernel
theorem raw776Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw776Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw776Spec x y z w 1 v := by
  norm_num [eval,monomial,raw776Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw776Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw776Left,raw776Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw776Observation : Fin 553 := ⟨120,by decide⟩
def raw776Units : List ℕ := [5, 1]
theorem raw776Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw776Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw776Spec.q raw776Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw776Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw776Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw776Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw776Units raw776Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw776Units raw776Right (by decide +kernel) (by decide +kernel)]
#print axioms raw776Observed
#print axioms raw776Valid
#print axioms raw776Row

def raw777Poly : Poly := [((-1/1:ℚ),53,(0,3,(-2),0,0,0,0)),((1/1:ℚ),64,(0,0,0,0,0,0,0)),((-1/1:ℚ),72,(0,3,(-2),0,0,0,0)),((1/1:ℚ),135,(0,0,0,0,0,0,0))]
def raw777Left : ℕ→ℕ
  | 1 => 135
  | 5 => 64
  | _ => 0
def raw777Right : ℕ→ℕ
  | 1 => 72
  | 5 => 53
  | _ => 0
def raw777Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨777,270,6,27,(-25),raw777Left,raw777Right,0,3,(-2),0⟩
theorem raw777Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw777Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw777Spec]
  decide +kernel
theorem raw777Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw777Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw777Spec x y z w 1 v := by
  norm_num [eval,monomial,raw777Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw777Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw777Left,raw777Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw777Observation : Fin 553 := ⟨186,by decide⟩
def raw777Units : List ℕ := [5, 1]
theorem raw777Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw777Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw777Spec.q raw777Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw777Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw777Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw777Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw777Units raw777Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw777Units raw777Right (by decide +kernel) (by decide +kernel)]
#print axioms raw777Observed
#print axioms raw777Valid
#print axioms raw777Row

def raw778Poly : Poly := [((-1/1:ℚ),0,(0,3,(-2),0,0,0,0)),((-1/1:ℚ),22,(0,3,(-2),0,0,0,0)),((1/1:ℚ),38,(0,0,0,0,0,0,0)),((1/1:ℚ),134,(0,0,0,0,0,0,0))]
def raw778Left : ℕ→ℕ
  | 1 => 38
  | 5 => 134
  | _ => 0
def raw778Right : ℕ→ℕ
  | 1 => 22
  | 5 => 0
  | _ => 0
def raw778Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨778,270,6,(-27),25,raw778Left,raw778Right,0,3,(-2),0⟩
theorem raw778Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw778Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw778Spec]
  decide +kernel
theorem raw778Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw778Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw778Spec x y z w 1 v := by
  norm_num [eval,monomial,raw778Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw778Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw778Left,raw778Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw778Observation : Fin 553 := ⟨187,by decide⟩
def raw778Units : List ℕ := [5, 1]
theorem raw778Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw778Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw778Spec.q raw778Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw778Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw778Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw778Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw778Units raw778Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw778Units raw778Right (by decide +kernel) (by decide +kernel)]
#print axioms raw778Observed
#print axioms raw778Valid
#print axioms raw778Row

def raw781Poly : Poly := [((1/1:ℚ),6,(0,0,0,0,0,0,0)),((1/1:ℚ),16,(0,0,0,0,0,0,0)),((-1/1:ℚ),94,(0,(-1),2,0,0,0,0)),((-1/1:ℚ),99,(0,(-1),2,0,0,0,0))]
def raw781Left : ℕ→ℕ
  | 1 => 16
  | 5 => 6
  | _ => 0
def raw781Right : ℕ→ℕ
  | 1 => 94
  | 5 => 99
  | _ => 0
def raw781Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨781,270,6,75,(-9),raw781Left,raw781Right,0,(-1),2,0⟩
theorem raw781Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw781Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw781Spec]
  decide +kernel
theorem raw781Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw781Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw781Spec x y z w 1 v := by
  norm_num [eval,monomial,raw781Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw781Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw781Left,raw781Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw781Observation : Fin 553 := ⟨188,by decide⟩
def raw781Units : List ℕ := [1, 5]
theorem raw781Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw781Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw781Spec.q raw781Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw781Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw781Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw781Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw781Units raw781Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw781Units raw781Right (by decide +kernel) (by decide +kernel)]
#print axioms raw781Observed
#print axioms raw781Valid
#print axioms raw781Row

def raw782Poly : Poly := [((1/1:ℚ),28,(0,0,0,0,0,0,0)),((1/1:ℚ),33,(0,0,0,0,0,0,0)),((-1/1:ℚ),96,(0,(-1),2,0,0,0,0)),((-1/1:ℚ),101,(0,(-1),2,0,0,0,0))]
def raw782Left : ℕ→ℕ
  | 1 => 28
  | 5 => 33
  | _ => 0
def raw782Right : ℕ→ℕ
  | 1 => 101
  | 5 => 96
  | _ => 0
def raw782Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨782,270,6,(-75),9,raw782Left,raw782Right,0,(-1),2,0⟩
theorem raw782Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw782Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw782Spec]
  decide +kernel
theorem raw782Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw782Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw782Spec x y z w 1 v := by
  norm_num [eval,monomial,raw782Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw782Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw782Left,raw782Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw782Observation : Fin 553 := ⟨189,by decide⟩
def raw782Units : List ℕ := [5, 1]
theorem raw782Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw782Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw782Spec.q raw782Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw782Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw782Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw782Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw782Units raw782Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw782Units raw782Right (by decide +kernel) (by decide +kernel)]
#print axioms raw782Observed
#print axioms raw782Valid
#print axioms raw782Row

def raw783Poly : Poly := [((-1/1:ℚ),18,(0,3,0,0,0,0,0)),((1/1:ℚ),37,(0,0,0,0,0,0,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0)),((-1/1:ℚ),100,(0,3,0,0,0,0,0))]
def raw783Left : ℕ→ℕ
  | 1 => 37
  | 5 => 50
  | _ => 0
def raw783Right : ℕ→ℕ
  | 1 => 18
  | 5 => 100
  | _ => 0
def raw783Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨783,270,6,135,(-5),raw783Left,raw783Right,0,3,0,0⟩
theorem raw783Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw783Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw783Spec]
  decide +kernel
theorem raw783Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw783Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw783Spec x y z w 1 v := by
  norm_num [eval,monomial,raw783Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw783Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw783Left,raw783Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw783Observation : Fin 553 := ⟨190,by decide⟩
def raw783Units : List ℕ := [1, 5]
theorem raw783Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw783Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw783Spec.q raw783Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw783Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw783Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw783Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw783Units raw783Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw783Units raw783Right (by decide +kernel) (by decide +kernel)]
#print axioms raw783Observed
#print axioms raw783Valid
#print axioms raw783Row

def raw784Poly : Poly := [((1/1:ℚ),37,(0,0,0,0,0,0,0)),((-1/1:ℚ),39,(0,3,0,0,0,0,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0)),((-1/1:ℚ),98,(0,3,0,0,0,0,0))]
def raw784Left : ℕ→ℕ
  | 1 => 37
  | 5 => 50
  | _ => 0
def raw784Right : ℕ→ℕ
  | 1 => 98
  | 5 => 39
  | _ => 0
def raw784Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨784,270,6,(-135),5,raw784Left,raw784Right,0,3,0,0⟩
theorem raw784Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw784Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw784Spec]
  decide +kernel
theorem raw784Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw784Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw784Spec x y z w 1 v := by
  norm_num [eval,monomial,raw784Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw784Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw784Left,raw784Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw784Observation : Fin 553 := ⟨191,by decide⟩
def raw784Units : List ℕ := [5, 1]
theorem raw784Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw784Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw784Spec.q raw784Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw784Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw784Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw784Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw784Units raw784Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw784Units raw784Right (by decide +kernel) (by decide +kernel)]
#print axioms raw784Observed
#print axioms raw784Valid
#print axioms raw784Row

def raw798Poly : Poly := [((-1/1:ℚ),6,((-2),(-2),0,0,0,0,0)),((-1/1:ℚ),16,((-2),(-2),0,0,0,0,0)),((1/1:ℚ),17,(0,0,0,0,0,0,0)),((-1/1:ℚ),28,((-2),(-2),0,0,0,0,0)),((-1/1:ℚ),33,((-2),(-2),0,0,0,0,0)),((1/1:ℚ),35,(0,0,0,0,0,0,0)),((1/1:ℚ),57,(0,0,0,0,0,0,0)),((-1/1:ℚ),69,((-2),(-2),0,0,0,0,0)),((1/1:ℚ),73,(0,0,0,0,0,0,0)),((-1/1:ℚ),75,((-2),(-2),0,0,0,0,0)),((1/1:ℚ),137,(0,0,0,0,0,0,0)),((1/1:ℚ),149,(0,0,0,0,0,0,0))]
def raw798Left : ℕ→ℕ
  | 1 => 73
  | 2 => 137
  | 4 => 17
  | 5 => 35
  | 7 => 149
  | 8 => 57
  | _ => 0
def raw798Right : ℕ→ℕ
  | 1 => 16
  | 2 => 33
  | 4 => 69
  | 5 => 28
  | 7 => 6
  | 8 => 75
  | _ => 0
def raw798Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨798,270,9,5,(-180),raw798Left,raw798Right,(-2),(-2),0,0⟩
theorem raw798Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw798Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw798Spec]
  decide +kernel
theorem raw798Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw798Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw798Spec x y z w 1 v := by
  norm_num [eval,monomial,raw798Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw798Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw798Left,raw798Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw798Observation : Fin 553 := ⟨196,by decide⟩
def raw798Units : List ℕ := [7, 1, 5, 2, 4, 8]
theorem raw798Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw798Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw798Spec.q raw798Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw798Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 9 raw798Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw798Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw798Units raw798Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=9) v raw798Units raw798Right (by decide +kernel) (by decide +kernel)]
#print axioms raw798Observed
#print axioms raw798Valid
#print axioms raw798Row

def raw799Poly : Poly := [((-1/1:ℚ),6,((-2),(-2),0,0,0,0,0)),((1/1:ℚ),15,(0,0,0,0,0,0,0)),((-1/1:ℚ),16,((-2),(-2),0,0,0,0,0)),((-1/1:ℚ),28,((-2),(-2),0,0,0,0,0)),((-1/1:ℚ),33,((-2),(-2),0,0,0,0,0)),((1/1:ℚ),44,(0,0,0,0,0,0,0)),((1/1:ℚ),66,(0,0,0,0,0,0,0)),((-1/1:ℚ),69,((-2),(-2),0,0,0,0,0)),((1/1:ℚ),71,(0,0,0,0,0,0,0)),((-1/1:ℚ),75,((-2),(-2),0,0,0,0,0)),((1/1:ℚ),136,(0,0,0,0,0,0,0)),((1/1:ℚ),142,(0,0,0,0,0,0,0))]
def raw799Left : ℕ→ℕ
  | 1 => 15
  | 2 => 142
  | 4 => 66
  | 5 => 44
  | 7 => 136
  | 8 => 71
  | _ => 0
def raw799Right : ℕ→ℕ
  | 1 => 69
  | 2 => 28
  | 4 => 6
  | 5 => 75
  | 7 => 16
  | 8 => 33
  | _ => 0
def raw799Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨799,270,9,(-5),180,raw799Left,raw799Right,(-2),(-2),0,0⟩
theorem raw799Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw799Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw799Spec]
  decide +kernel
theorem raw799Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw799Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw799Spec x y z w 1 v := by
  norm_num [eval,monomial,raw799Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw799Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw799Left,raw799Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw799Observation : Fin 553 := ⟨196,by decide⟩
def raw799Units : List ℕ := [4, 7, 2, 8, 1, 5]
theorem raw799Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw799Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw799Spec.q raw799Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw799Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 9 raw799Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw799Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw799Units raw799Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=9) v raw799Units raw799Right (by decide +kernel) (by decide +kernel)]
#print axioms raw799Observed
#print axioms raw799Valid
#print axioms raw799Row

def raw800Poly : Poly := [((-1/1:ℚ),2,(0,0,(-2),0,0,0,0)),((1/1:ℚ),19,(0,0,0,0,0,0,0)),((-1/1:ℚ),28,(0,0,(-2),0,0,0,0)),((-1/1:ℚ),33,(0,0,(-2),0,0,0,0)),((-1/1:ℚ),37,(0,0,(-2),0,0,0,0)),((-1/1:ℚ),50,(0,0,(-2),0,0,0,0)),((1/1:ℚ),59,(0,0,0,0,0,0,0)),((-1/1:ℚ),75,(0,0,(-2),0,0,0,0)),((1/1:ℚ),94,(0,0,0,0,0,0,0)),((1/1:ℚ),99,(0,0,0,0,0,0,0)),((1/1:ℚ),171,(0,0,0,0,0,0,0)),((1/1:ℚ),174,(0,0,0,0,0,0,0))]
def raw800Left : ℕ→ℕ
  | 1 => 94
  | 2 => 174
  | 4 => 19
  | 5 => 171
  | 7 => 99
  | 8 => 59
  | _ => 0
def raw800Right : ℕ→ℕ
  | 1 => 33
  | 2 => 37
  | 4 => 28
  | 5 => 2
  | 7 => 75
  | 8 => 50
  | _ => 0
def raw800Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨800,270,9,6,(-150),raw800Left,raw800Right,0,0,(-2),0⟩
theorem raw800Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw800Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw800Spec]
  decide +kernel
theorem raw800Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw800Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw800Spec x y z w 1 v := by
  norm_num [eval,monomial,raw800Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw800Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw800Left,raw800Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw800Observation : Fin 553 := ⟨198,by decide⟩
def raw800Units : List ℕ := [5, 4, 1, 2, 8, 7]
theorem raw800Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw800Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw800Spec.q raw800Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw800Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 9 raw800Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw800Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw800Units raw800Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=9) v raw800Units raw800Right (by decide +kernel) (by decide +kernel)]
#print axioms raw800Observed
#print axioms raw800Valid
#print axioms raw800Row

def raw801Poly : Poly := [((-1/1:ℚ),2,(0,0,(-2),0,0,0,0)),((-1/1:ℚ),6,(0,0,(-2),0,0,0,0)),((1/1:ℚ),13,(0,0,0,0,0,0,0)),((-1/1:ℚ),16,(0,0,(-2),0,0,0,0)),((-1/1:ℚ),37,(0,0,(-2),0,0,0,0)),((-1/1:ℚ),50,(0,0,(-2),0,0,0,0)),((1/1:ℚ),56,(0,0,0,0,0,0,0)),((-1/1:ℚ),69,(0,0,(-2),0,0,0,0)),((1/1:ℚ),96,(0,0,0,0,0,0,0)),((1/1:ℚ),101,(0,0,0,0,0,0,0)),((1/1:ℚ),168,(0,0,0,0,0,0,0)),((1/1:ℚ),173,(0,0,0,0,0,0,0))]
def raw801Left : ℕ→ℕ
  | 1 => 13
  | 2 => 101
  | 4 => 168
  | 5 => 56
  | 7 => 173
  | 8 => 96
  | _ => 0
def raw801Right : ℕ→ℕ
  | 1 => 37
  | 2 => 69
  | 4 => 2
  | 5 => 6
  | 7 => 50
  | 8 => 16
  | _ => 0
def raw801Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨801,270,9,(-6),150,raw801Left,raw801Right,0,0,(-2),0⟩
theorem raw801Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw801Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw801Spec]
  decide +kernel
theorem raw801Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw801Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw801Spec x y z w 1 v := by
  norm_num [eval,monomial,raw801Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw801Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw801Left,raw801Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw801Observation : Fin 553 := ⟨197,by decide⟩
def raw801Units : List ℕ := [4, 5, 8, 1, 7, 2]
theorem raw801Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw801Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw801Spec.q raw801Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw801Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 9 raw801Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw801Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw801Units raw801Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=9) v raw801Units raw801Right (by decide +kernel) (by decide +kernel)]
#print axioms raw801Observed
#print axioms raw801Valid
#print axioms raw801Row

def raw803Poly : Poly := [((-1/1:ℚ),0,((-2),2,(-2),0,0,0,0)),((1/1:ℚ),10,(0,0,0,0,0,0,0)),((-1/1:ℚ),18,((-2),2,(-2),0,0,0,0)),((-1/1:ℚ),22,((-2),2,(-2),0,0,0,0)),((-1/1:ℚ),24,((-2),2,(-2),0,0,0,0)),((1/1:ℚ),52,(0,0,0,0,0,0,0)),((-1/1:ℚ),58,((-2),2,(-2),0,0,0,0)),((-1/1:ℚ),100,((-2),2,(-2),0,0,0,0)),((1/1:ℚ),157,(0,0,0,0,0,0,0)),((1/1:ℚ),159,(0,0,0,0,0,0,0)),((1/1:ℚ),218,(0,0,0,0,0,0,0)),((1/1:ℚ),219,(0,0,0,0,0,0,0))]
def raw803Left : ℕ→ℕ
  | 1 => 10
  | 2 => 159
  | 4 => 157
  | 5 => 52
  | 7 => 218
  | 8 => 219
  | _ => 0
def raw803Right : ℕ→ℕ
  | 1 => 24
  | 2 => 58
  | 4 => 100
  | 5 => 0
  | 7 => 18
  | 8 => 22
  | _ => 0
def raw803Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨803,270,9,(-9),100,raw803Left,raw803Right,(-2),2,(-2),0⟩
theorem raw803Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw803Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw803Spec]
  decide +kernel
theorem raw803Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw803Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw803Spec x y z w 1 v := by
  norm_num [eval,monomial,raw803Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw803Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw803Left,raw803Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw803Observation : Fin 553 := ⟨201,by decide⟩
def raw803Units : List ℕ := [5, 7, 8, 1, 2, 4]
theorem raw803Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw803Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw803Spec.q raw803Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw803Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 9 raw803Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw803Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw803Units raw803Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=9) v raw803Units raw803Right (by decide +kernel) (by decide +kernel)]
#print axioms raw803Observed
#print axioms raw803Valid
#print axioms raw803Row

def raw806Poly : Poly := [((-1/1:ℚ),3,(2,0,(-2),0,0,0,0)),((-1/1:ℚ),20,(2,0,(-2),0,0,0,0)),((1/1:ℚ),27,(0,0,0,0,0,0,0)),((-1/1:ℚ),42,(2,0,(-2),0,0,0,0)),((-1/1:ℚ),55,(2,0,(-2),0,0,0,0)),((-1/1:ℚ),60,(2,0,(-2),0,0,0,0)),((1/1:ℚ),64,(0,0,0,0,0,0,0)),((1/1:ℚ),90,(0,0,0,0,0,0,0)),((-1/1:ℚ),97,(2,0,(-2),0,0,0,0)),((1/1:ℚ),135,(0,0,0,0,0,0,0)),((1/1:ℚ),169,(0,0,0,0,0,0,0)),((1/1:ℚ),172,(0,0,0,0,0,0,0))]
def raw806Left : ℕ→ℕ
  | 1 => 172
  | 2 => 135
  | 4 => 27
  | 5 => 90
  | 7 => 169
  | 8 => 64
  | _ => 0
def raw806Right : ℕ→ℕ
  | 1 => 55
  | 2 => 42
  | 4 => 20
  | 5 => 97
  | 7 => 3
  | 8 => 60
  | _ => 0
def raw806Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨806,270,9,12,(-75),raw806Left,raw806Right,2,0,(-2),0⟩
theorem raw806Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw806Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw806Spec]
  decide +kernel
theorem raw806Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw806Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw806Spec x y z w 1 v := by
  norm_num [eval,monomial,raw806Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw806Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw806Left,raw806Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw806Observation : Fin 553 := ⟨202,by decide⟩
def raw806Units : List ℕ := [7, 4, 2, 1, 8, 5]
theorem raw806Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw806Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw806Spec.q raw806Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw806Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 9 raw806Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw806Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw806Units raw806Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=9) v raw806Units raw806Right (by decide +kernel) (by decide +kernel)]
#print axioms raw806Observed
#print axioms raw806Valid
#print axioms raw806Row

def raw807Poly : Poly := [((-1/1:ℚ),3,(2,0,(-2),0,0,0,0)),((1/1:ℚ),7,(0,0,0,0,0,0,0)),((-1/1:ℚ),12,(2,0,(-2),0,0,0,0)),((-1/1:ℚ),20,(2,0,(-2),0,0,0,0)),((-1/1:ℚ),34,(2,0,(-2),0,0,0,0)),((1/1:ℚ),38,(0,0,0,0,0,0,0)),((-1/1:ℚ),55,(2,0,(-2),0,0,0,0)),((1/1:ℚ),91,(0,0,0,0,0,0,0)),((-1/1:ℚ),95,(2,0,(-2),0,0,0,0)),((1/1:ℚ),134,(0,0,0,0,0,0,0)),((1/1:ℚ),170,(0,0,0,0,0,0,0)),((1/1:ℚ),175,(0,0,0,0,0,0,0))]
def raw807Left : ℕ→ℕ
  | 1 => 38
  | 2 => 170
  | 4 => 91
  | 5 => 7
  | 7 => 134
  | 8 => 175
  | _ => 0
def raw807Right : ℕ→ℕ
  | 1 => 12
  | 2 => 3
  | 4 => 95
  | 5 => 55
  | 7 => 34
  | 8 => 20
  | _ => 0
def raw807Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨807,270,9,(-12),75,raw807Left,raw807Right,2,0,(-2),0⟩
theorem raw807Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw807Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw807Spec]
  decide +kernel
theorem raw807Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw807Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw807Spec x y z w 1 v := by
  norm_num [eval,monomial,raw807Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw807Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw807Left,raw807Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw807Observation : Fin 553 := ⟨203,by decide⟩
def raw807Units : List ℕ := [2, 1, 8, 7, 5, 4]
theorem raw807Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw807Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw807Spec.q raw807Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw807Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 9 raw807Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw807Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw807Units raw807Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=9) v raw807Units raw807Right (by decide +kernel) (by decide +kernel)]
#print axioms raw807Observed
#print axioms raw807Valid
#print axioms raw807Row

def raw811Poly : Poly := [((-1/1:ℚ),1,(0,2,(-2),0,0,0,0)),((-1/1:ℚ),8,(0,2,(-2),0,0,0,0)),((-1/1:ℚ),14,(0,2,(-2),0,0,0,0)),((1/1:ℚ),27,(0,0,0,0,0,0,0)),((-1/1:ℚ),46,(0,2,(-2),0,0,0,0)),((-1/1:ℚ),53,(0,2,(-2),0,0,0,0)),((1/1:ℚ),68,(0,0,0,0,0,0,0)),((-1/1:ℚ),72,(0,2,(-2),0,0,0,0)),((1/1:ℚ),130,(0,0,0,0,0,0,0)),((1/1:ℚ),131,(0,0,0,0,0,0,0)),((1/1:ℚ),169,(0,0,0,0,0,0,0)),((1/1:ℚ),172,(0,0,0,0,0,0,0))]
def raw811Left : ℕ→ℕ
  | 1 => 68
  | 2 => 172
  | 4 => 130
  | 5 => 27
  | 7 => 131
  | 8 => 169
  | _ => 0
def raw811Right : ℕ→ℕ
  | 1 => 8
  | 2 => 14
  | 4 => 46
  | 5 => 53
  | 7 => 1
  | 8 => 72
  | _ => 0
def raw811Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨811,270,9,(-18),50,raw811Left,raw811Right,0,2,(-2),0⟩
theorem raw811Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw811Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw811Spec]
  decide +kernel
theorem raw811Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw811Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw811Spec x y z w 1 v := by
  norm_num [eval,monomial,raw811Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw811Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw811Left,raw811Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw811Observation : Fin 553 := ⟨205,by decide⟩
def raw811Units : List ℕ := [7, 1, 2, 4, 5, 8]
theorem raw811Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw811Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw811Spec.q raw811Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw811Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 9 raw811Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw811Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw811Units raw811Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=9) v raw811Units raw811Right (by decide +kernel) (by decide +kernel)]
#print axioms raw811Observed
#print axioms raw811Valid
#print axioms raw811Row

def raw845Poly : Poly := [((-1/1:ℚ),2,(0,(-3),0,0,0,0,0)),((1/1:ℚ),26,(0,0,0,0,0,0,0)),((-1/1:ℚ),90,(0,(-3),0,0,0,0,0)),((-1/1:ℚ),99,(0,(-3),0,0,0,0,0)),((-1/1:ℚ),101,(0,(-3),0,0,0,0,0)),((1/1:ℚ),197,(0,0,0,0,0,0,0)),((1/1:ℚ),210,(0,0,0,0,0,0,0)),((1/1:ℚ),220,(0,0,0,0,0,0,0))]
def raw845Left : ℕ→ℕ
  | 1 => 197
  | 3 => 220
  | 7 => 26
  | 9 => 210
  | _ => 0
def raw845Right : ℕ→ℕ
  | 1 => 2
  | 3 => 101
  | 7 => 90
  | 9 => 99
  | _ => 0
def raw845Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨845,270,10,1,(-27),raw845Left,raw845Right,0,(-3),0,0⟩
theorem raw845Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw845Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw845Spec]
  decide +kernel
theorem raw845Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw845Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw845Spec x y z w 1 v := by
  norm_num [eval,monomial,raw845Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw845Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw845Left,raw845Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw845Observation : Fin 553 := ⟨163,by decide⟩
def raw845Units : List ℕ := [1, 7, 9, 3]
theorem raw845Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw845Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw845Spec.q raw845Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw845Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 10 raw845Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw845Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw845Units raw845Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=10) v raw845Units raw845Right (by decide +kernel) (by decide +kernel)]
#print axioms raw845Observed
#print axioms raw845Valid
#print axioms raw845Row

def raw848Poly : Poly := [((1/1:ℚ),13,(0,0,0,0,0,0,0)),((1/1:ℚ),28,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,(0,(-1),0,0,0,0,0)),((-1/1:ℚ),64,(0,(-1),0,0,0,0,0)),((-1/1:ℚ),94,(0,(-1),0,0,0,0,0)),((1/1:ℚ),123,(0,0,0,0,0,0,0)),((1/1:ℚ),132,(0,0,0,0,0,0,0)),((-1/1:ℚ),134,(0,(-1),0,0,0,0,0))]
def raw848Left : ℕ→ℕ
  | 1 => 13
  | 3 => 132
  | 7 => 123
  | 9 => 28
  | _ => 0
def raw848Right : ℕ→ℕ
  | 1 => 94
  | 3 => 50
  | 7 => 134
  | 9 => 64
  | _ => 0
def raw848Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨848,270,10,(-3),9,raw848Left,raw848Right,0,(-1),0,0⟩
theorem raw848Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw848Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw848Spec]
  decide +kernel
theorem raw848Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw848Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw848Spec x y z w 1 v := by
  norm_num [eval,monomial,raw848Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw848Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw848Left,raw848Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw848Observation : Fin 553 := ⟨231,by decide⟩
def raw848Units : List ℕ := [3, 9, 1, 7]
theorem raw848Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw848Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw848Spec.q raw848Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw848Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 10 raw848Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw848Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw848Units raw848Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=10) v raw848Units raw848Right (by decide +kernel) (by decide +kernel)]
#print axioms raw848Observed
#print axioms raw848Valid
#print axioms raw848Row

def raw862Poly : Poly := [((-1/1:ℚ),2,(0,(-1),0,0,0,0,0)),((1/1:ℚ),13,(0,0,0,0,0,0,0)),((-1/1:ℚ),19,(0,(-1),0,0,0,0,0)),((1/1:ℚ),27,(0,0,0,0,0,0,0)),((1/1:ℚ),28,(0,0,0,0,0,0,0)),((1/1:ℚ),33,(0,0,0,0,0,0,0)),((-1/1:ℚ),37,(0,(-1),0,0,0,0,0)),((-1/1:ℚ),38,(0,(-1),0,0,0,0,0)),((1/1:ℚ),76,(0,0,0,0,0,0,0)),((-1/1:ℚ),91,(0,(-1),0,0,0,0,0)),((-1/1:ℚ),96,(0,(-1),0,0,0,0,0)),((-1/1:ℚ),99,(0,(-1),0,0,0,0,0)),((-1/1:ℚ),101,(0,(-1),0,0,0,0,0)),((1/1:ℚ),132,(0,0,0,0,0,0,0)),((1/1:ℚ),172,(0,0,0,0,0,0,0)),((1/1:ℚ),173,(0,0,0,0,0,0,0))]
def raw862Left : ℕ→ℕ
  | 1 => 13
  | 2 => 172
  | 4 => 132
  | 7 => 27
  | 8 => 33
  | 11 => 173
  | 13 => 28
  | 14 => 76
  | _ => 0
def raw862Right : ℕ→ℕ
  | 1 => 2
  | 2 => 38
  | 4 => 101
  | 7 => 91
  | 8 => 19
  | 11 => 37
  | 13 => 99
  | 14 => 96
  | _ => 0
def raw862Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨862,270,15,6,(-18),raw862Left,raw862Right,0,(-1),0,0⟩
theorem raw862Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw862Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw862Spec]
  decide +kernel
theorem raw862Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw862Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw862Spec x y z w 1 v := by
  norm_num [eval,monomial,raw862Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw862Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw862Left,raw862Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw862Observation : Fin 553 := ⟨244,by decide⟩
def raw862Units : List ℕ := [1, 8, 11, 2, 7, 14, 13, 4]
theorem raw862Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw862Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw862Spec.q raw862Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw862Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 15 raw862Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw862Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw862Units raw862Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=15) v raw862Units raw862Right (by decide +kernel) (by decide +kernel)]
#print axioms raw862Observed
#print axioms raw862Valid
#print axioms raw862Row

def raw970Poly : Poly := [((1/1:ℚ),41,(0,0,0,0,0,0,0)),((1/1:ℚ),49,((-2),0,0,0,0,0,0)),((-1/1:ℚ),78,((-1),0,0,0,1,0,0)),((1/1:ℚ),83,(0,0,0,0,0,0,0))]
def raw970Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨970,270,2,2,![83,41],78,49⟩
theorem raw970Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw970Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw970Spec]
  decide +kernel
theorem raw970Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw970Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw970Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw970Spec]
  norm_num [eval,monomial,raw970Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw970Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw970Valid
#print axioms raw970Row

def raw971Poly : Poly := [((1/1:ℚ),7,(0,0,0,0,0,0,0)),((-1/1:ℚ),48,((-1),0,0,0,1,0,0)),((1/1:ℚ),68,((-2),0,0,0,0,0,0)),((1/1:ℚ),84,(0,0,0,0,0,0,0))]
def raw971Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨971,270,2,3,![84,7],48,68⟩
theorem raw971Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw971Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw971Spec]
  decide +kernel
theorem raw971Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw971Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw971Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw971Spec]
  norm_num [eval,monomial,raw971Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw971Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw971Valid
#print axioms raw971Row

def raw974Poly : Poly := [((1/1:ℚ),13,((-2),0,0,0,0,0,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0)),((1/1:ℚ),52,(0,0,0,0,0,0,0)),((-1/1:ℚ),68,((-1),0,0,0,1,0,0))]
def raw974Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨974,270,2,6,![48,52],68,13⟩
theorem raw974Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw974Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw974Spec]
  decide +kernel
theorem raw974Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw974Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw974Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw974Spec]
  norm_num [eval,monomial,raw974Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw974Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw974Valid
#print axioms raw974Row

def raw975Poly : Poly := [((1/1:ℚ),54,(0,0,0,0,0,0,0)),((-1/1:ℚ),70,((-1),0,0,0,1,0,0)),((1/1:ℚ),81,(0,0,0,0,0,0,0)),((1/1:ℚ),197,((-2),0,0,0,0,0,0))]
def raw975Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨975,270,2,7,![81,54],70,197⟩
theorem raw975Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw975Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw975Spec]
  decide +kernel
theorem raw975Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw975Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw975Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw975Spec]
  norm_num [eval,monomial,raw975Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw975Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw975Valid
#print axioms raw975Row

def raw977Poly : Poly := [((-1/1:ℚ),38,((-1),0,0,0,1,0,0)),((1/1:ℚ),51,(0,0,0,0,0,0,0)),((1/1:ℚ),56,(0,0,0,0,0,0,0)),((1/1:ℚ),94,((-2),0,0,0,0,0,0))]
def raw977Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨977,270,2,9,![51,56],38,94⟩
theorem raw977Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw977Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw977Spec]
  decide +kernel
theorem raw977Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw977Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw977Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw977Spec]
  norm_num [eval,monomial,raw977Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw977Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw977Valid
#print axioms raw977Row

def raw978Poly : Poly := [((1/1:ℚ),18,((-2),0,0,0,0,0,0)),((1/1:ℚ),32,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(0,0,0,0,0,0,0)),((-1/1:ℚ),72,((-1),0,0,0,1,0,0))]
def raw978Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨978,270,2,10,![32,44],72,18⟩
theorem raw978Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw978Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw978Spec]
  decide +kernel
theorem raw978Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw978Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw978Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw978Spec]
  norm_num [eval,monomial,raw978Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw978Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw978Valid
#print axioms raw978Row

def raw983Poly : Poly := [((-1/1:ℚ),6,((-1),0,0,0,1,0,0)),((1/1:ℚ),33,(0,0,0,0,0,0,0)),((1/1:ℚ),34,(0,0,0,0,0,0,0)),((1/1:ℚ),75,((-2),0,0,0,0,0,0))]
def raw983Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨983,270,2,15,![34,33],6,75⟩
theorem raw983Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw983Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw983Spec]
  decide +kernel
theorem raw983Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw983Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw983Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw983Spec]
  norm_num [eval,monomial,raw983Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw983Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw983Valid
#print axioms raw983Row

def raw986Poly : Poly := [((1/1:ℚ),38,(0,0,0,0,0,0,0)),((-1/1:ℚ),94,((-1),0,0,0,1,0,0)),((1/1:ℚ),135,((-2),0,0,0,0,0,0)),((1/1:ℚ),141,(0,0,0,0,0,0,0))]
def raw986Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨986,270,2,18,![38,141],94,135⟩
theorem raw986Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw986Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw986Spec]
  decide +kernel
theorem raw986Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw986Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw986Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw986Spec]
  norm_num [eval,monomial,raw986Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw986Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw986Valid
#print axioms raw986Row

def raw988Poly : Poly := [((1/1:ℚ),8,((-2),0,0,0,0,0,0)),((-1/1:ℚ),18,((-1),0,0,0,1,0,0)),((1/1:ℚ),35,(0,0,0,0,0,0,0)),((1/1:ℚ),72,(0,0,0,0,0,0,0))]
def raw988Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨988,270,2,20,![72,35],18,8⟩
theorem raw988Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw988Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw988Spec]
  decide +kernel
theorem raw988Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw988Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw988Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw988Spec]
  norm_num [eval,monomial,raw988Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw988Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw988Valid
#print axioms raw988Row

def raw989Poly : Poly := [((1/1:ℚ),10,(0,0,0,0,0,0,0)),((1/1:ℚ),124,((-2),0,0,0,0,0,0)),((1/1:ℚ),171,(0,0,0,0,0,0,0)),((-1/1:ℚ),172,((-1),0,0,0,1,0,0))]
def raw989Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨989,270,2,21,![10,171],172,124⟩
theorem raw989Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw989Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw989Spec]
  decide +kernel
theorem raw989Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw989Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw989Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw989Spec]
  norm_num [eval,monomial,raw989Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw989Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw989Valid
#print axioms raw989Row

def raw992Poly : Poly := [((1/1:ℚ),13,(0,0,0,0,0,0,0)),((1/1:ℚ),122,((-2),0,0,0,0,0,0)),((1/1:ℚ),160,(0,0,0,0,0,0,0)),((-1/1:ℚ),170,((-1),0,0,0,1,0,0))]
def raw992Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨992,270,2,24,![13,160],170,122⟩
theorem raw992Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw992Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw992Spec]
  decide +kernel
theorem raw992Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw992Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw992Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw992Spec]
  norm_num [eval,monomial,raw992Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw992Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw992Valid
#print axioms raw992Row

def raw993Poly : Poly := [((1/1:ℚ),15,(0,0,0,0,0,0,0)),((1/1:ℚ),58,(0,0,0,0,0,0,0)),((1/1:ℚ),80,((-2),0,0,0,0,0,0)),((-1/1:ℚ),98,((-1),0,0,0,1,0,0))]
def raw993Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨993,270,2,25,![15,58],98,80⟩
theorem raw993Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw993Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw993Spec]
  decide +kernel
theorem raw993Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw993Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw993Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw993Spec]
  norm_num [eval,monomial,raw993Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw993Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw993Valid
#print axioms raw993Row

def raw995Poly : Poly := [((1/1:ℚ),90,(0,0,0,0,0,0,0)),((1/1:ℚ),91,((-2),0,0,0,0,0,0)),((1/1:ℚ),92,(0,0,0,0,0,0,0)),((-1/1:ℚ),101,((-1),0,0,0,1,0,0))]
def raw995Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨995,270,2,27,![92,90],101,91⟩
theorem raw995Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw995Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw995Spec]
  decide +kernel
theorem raw995Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw995Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw995Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw995Spec]
  norm_num [eval,monomial,raw995Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw995Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw995Valid
#print axioms raw995Row

def raw996Poly : Poly := [((1/1:ℚ),144,(0,0,0,0,0,0,0)),((-1/1:ℚ),150,((-1),0,0,0,1,0,0)),((1/1:ℚ),163,((-2),0,0,0,0,0,0)),((1/1:ℚ),197,(0,0,0,0,0,0,0))]
def raw996Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨996,270,2,28,![197,144],150,163⟩
theorem raw996Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw996Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw996Spec]
  decide +kernel
theorem raw996Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw996Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw996Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw996Spec]
  norm_num [eval,monomial,raw996Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw996Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw996Valid
#print axioms raw996Row

def raw998Poly : Poly := [((1/1:ℚ),6,(0,0,0,0,0,0,0)),((1/1:ℚ),16,((-2),0,0,0,0,0,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0)),((-1/1:ℚ),75,((-1),0,0,0,1,0,0))]
def raw998Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨998,270,2,30,![6,60],75,16⟩
theorem raw998Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw998Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw998Spec]
  decide +kernel
theorem raw998Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw998Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw998Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw998Spec]
  norm_num [eval,monomial,raw998Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw998Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw998Valid
#print axioms raw998Row

def raw1003Poly : Poly := [((-1/1:ℚ),22,((-1),0,0,0,1,0,0)),((1/1:ℚ),31,((-2),0,0,0,0,0,0)),((1/1:ℚ),46,(0,0,0,0,0,0,0)),((1/1:ℚ),73,(0,0,0,0,0,0,0))]
def raw1003Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1003,270,2,35,![73,46],22,31⟩
theorem raw1003Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1003Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1003Spec]
  decide +kernel
theorem raw1003Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1003Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1003Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1003Spec]
  norm_num [eval,monomial,raw1003Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1003Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1003Valid
#print axioms raw1003Row

def raw1004Poly : Poly := [((1/1:ℚ),56,((-2),0,0,0,0,0,0)),((1/1:ℚ),94,(0,0,0,0,0,0,0)),((1/1:ℚ),129,(0,0,0,0,0,0,0)),((-1/1:ℚ),135,((-1),0,0,0,1,0,0))]
def raw1004Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1004,270,2,36,![94,129],135,56⟩
theorem raw1004Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1004Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1004Spec]
  decide +kernel
theorem raw1004Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1004Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1004Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1004Spec]
  norm_num [eval,monomial,raw1004Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1004Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1004Valid
#print axioms raw1004Row

def raw1013Poly : Poly := [((1/1:ℚ),20,(0,0,0,0,0,0,0)),((1/1:ℚ),37,((-2),0,0,0,0,0,0)),((1/1:ℚ),37,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,((-1),0,0,0,1,0,0))]
def raw1013Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1013,270,2,45,![20,37],50,37⟩
theorem raw1013Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1013Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1013Spec]
  decide +kernel
theorem raw1013Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1013Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1013Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1013Spec]
  norm_num [eval,monomial,raw1013Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1013Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1013Valid
#print axioms raw1013Row

def raw1019Poly : Poly := [((1/1:ℚ),123,(0,0,0,0,0,0,0)),((-1/1:ℚ),130,((-1),0,0,0,1,0,0)),((1/1:ℚ),159,(0,0,0,0,0,0,0)),((1/1:ℚ),173,((-2),0,0,0,0,0,0))]
def raw1019Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1019,270,2,51,![159,123],130,173⟩
theorem raw1019Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1019Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1019Spec]
  decide +kernel
theorem raw1019Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1019Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1019Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1019Spec]
  norm_num [eval,monomial,raw1019Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1019Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1019Valid
#print axioms raw1019Row

def raw1022Poly : Poly := [((-1/1:ℚ),91,((-1),0,0,0,1,0,0)),((1/1:ℚ),99,((-2),0,0,0,0,0,0)),((1/1:ℚ),101,(0,0,0,0,0,0,0)),((1/1:ℚ),127,(0,0,0,0,0,0,0))]
def raw1022Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1022,270,2,54,![101,127],91,99⟩
theorem raw1022Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1022Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1022Spec]
  decide +kernel
theorem raw1022Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1022Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1022Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1022Spec]
  norm_num [eval,monomial,raw1022Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1022Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1022Valid
#print axioms raw1022Row

def raw1023Poly : Poly := [((-1/1:ℚ),14,((-1),0,0,0,1,0,0)),((1/1:ℚ),26,(0,0,0,0,0,0,0)),((1/1:ℚ),100,((-2),0,0,0,0,0,0)),((1/1:ℚ),142,(0,0,0,0,0,0,0))]
def raw1023Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1023,270,2,55,![142,26],14,100⟩
theorem raw1023Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1023Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1023Spec]
  decide +kernel
theorem raw1023Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1023Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1023Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1023Spec]
  norm_num [eval,monomial,raw1023Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1023Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1023Valid
#print axioms raw1023Row

def raw1025Poly : Poly := [((1/1:ℚ),131,(0,0,0,0,0,0,0)),((1/1:ℚ),156,(0,0,0,0,0,0,0)),((-1/1:ℚ),168,((-1),0,0,0,1,0,0)),((1/1:ℚ),175,((-2),0,0,0,0,0,0))]
def raw1025Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1025,270,2,57,![156,131],168,175⟩
theorem raw1025Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1025Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1025Spec]
  decide +kernel
theorem raw1025Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1025Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1025Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1025Spec]
  norm_num [eval,monomial,raw1025Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1025Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1025Valid
#print axioms raw1025Row

def raw1028Poly : Poly := [((-1/1:ℚ),16,((-1),0,0,0,1,0,0)),((1/1:ℚ),28,((-2),0,0,0,0,0,0)),((1/1:ℚ),75,(0,0,0,0,0,0,0)),((1/1:ℚ),95,(0,0,0,0,0,0,0))]
def raw1028Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1028,270,2,60,![75,95],16,28⟩
theorem raw1028Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1028Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1028Spec]
  decide +kernel
theorem raw1028Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1028Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1028Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1028Spec]
  norm_num [eval,monomial,raw1028Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1028Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1028Valid
#print axioms raw1028Row

def raw1031Poly : Poly := [((-1/1:ℚ),19,((-1),0,0,0,1,0,0)),((1/1:ℚ),64,((-2),0,0,0,0,0,0)),((1/1:ℚ),134,(0,0,0,0,0,0,0)),((1/1:ℚ),140,(0,0,0,0,0,0,0))]
def raw1031Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1031,270,2,63,![140,134],19,64⟩
theorem raw1031Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1031Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1031Spec]
  decide +kernel
theorem raw1031Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1031Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1031Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1031Spec]
  norm_num [eval,monomial,raw1031Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1031Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1031Valid
#print axioms raw1031Row

def raw1033Poly : Poly := [((1/1:ℚ),1,((-2),0,0,0,0,0,0)),((-1/1:ℚ),24,((-1),0,0,0,1,0,0)),((1/1:ℚ),53,(0,0,0,0,0,0,0)),((1/1:ℚ),137,(0,0,0,0,0,0,0))]
def raw1033Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1033,270,2,65,![137,53],24,1⟩
theorem raw1033Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1033Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1033Spec]
  decide +kernel
theorem raw1033Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1033Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1033Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1033Spec]
  norm_num [eval,monomial,raw1033Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1033Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1033Valid
#print axioms raw1033Row

def raw1034Poly : Poly := [((-1/1:ℚ),27,((-1),0,0,0,1,0,0)),((1/1:ℚ),47,((-2),0,0,0,0,0,0)),((1/1:ℚ),174,(0,0,0,0,0,0,0)),((1/1:ℚ),218,(0,0,0,0,0,0,0))]
def raw1034Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1034,270,2,66,![174,218],27,47⟩
theorem raw1034Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1034Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1034Spec]
  decide +kernel
theorem raw1034Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1034Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1034Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1034Spec]
  norm_num [eval,monomial,raw1034Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1034Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1034Valid
#print axioms raw1034Row

def raw1040Poly : Poly := [((1/1:ℚ),38,((-2),0,0,0,0,0,0)),((-1/1:ℚ),56,((-1),0,0,0,1,0,0)),((1/1:ℚ),135,(0,0,0,0,0,0,0)),((1/1:ℚ),139,(0,0,0,0,0,0,0))]
def raw1040Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1040,270,2,72,![135,139],56,38⟩
theorem raw1040Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1040Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1040Spec]
  decide +kernel
theorem raw1040Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1040Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1040Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1040Spec]
  norm_num [eval,monomial,raw1040Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1040Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1040Valid
#print axioms raw1040Row

def raw1043Poly : Poly := [((1/1:ℚ),6,((-2),0,0,0,0,0,0)),((-1/1:ℚ),33,((-1),0,0,0,1,0,0)),((1/1:ℚ),69,(0,0,0,0,0,0,0)),((1/1:ℚ),97,(0,0,0,0,0,0,0))]
def raw1043Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1043,270,2,75,![97,69],33,6⟩
theorem raw1043Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1043Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1043Spec]
  decide +kernel
theorem raw1043Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1043Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1043Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1043Spec]
  norm_num [eval,monomial,raw1043Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1043Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1043Valid
#print axioms raw1043Row

def raw1046Poly : Poly := [((1/1:ℚ),132,(0,0,0,0,0,0,0)),((1/1:ℚ),161,(0,0,0,0,0,0,0)),((-1/1:ℚ),171,((-1),0,0,0,1,0,0)),((1/1:ℚ),172,((-2),0,0,0,0,0,0))]
def raw1046Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1046,270,2,78,![132,161],171,172⟩
theorem raw1046Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1046Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1046Spec]
  decide +kernel
theorem raw1046Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1046Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1046Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1046Spec]
  norm_num [eval,monomial,raw1046Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1046Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1046Valid
#print axioms raw1046Row

def raw1048Poly : Poly := [((1/1:ℚ),8,(0,0,0,0,0,0,0)),((-1/1:ℚ),58,((-1),0,0,0,1,0,0)),((1/1:ℚ),98,((-2),0,0,0,0,0,0)),((1/1:ℚ),149,(0,0,0,0,0,0,0))]
def raw1048Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1048,270,2,80,![8,149],58,98⟩
theorem raw1048Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1048Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1048Spec]
  decide +kernel
theorem raw1048Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1048Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1048Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1048Spec]
  norm_num [eval,monomial,raw1048Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1048Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1048Valid
#print axioms raw1048Row

def raw1049Poly : Poly := [((-1/1:ℚ),90,((-1),0,0,0,1,0,0)),((1/1:ℚ),99,(0,0,0,0,0,0,0)),((1/1:ℚ),101,((-2),0,0,0,0,0,0)),((1/1:ℚ),128,(0,0,0,0,0,0,0))]
def raw1049Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1049,270,2,81,![128,99],90,101⟩
theorem raw1049Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1049Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1049Spec]
  decide +kernel
theorem raw1049Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1049Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1049Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1049Spec]
  norm_num [eval,monomial,raw1049Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1049Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1049Valid
#print axioms raw1049Row

def raw1050Poly : Poly := [((1/1:ℚ),145,(0,0,0,0,0,0,0)),((-1/1:ℚ),151,((-1),0,0,0,1,0,0)),((1/1:ℚ),162,((-2),0,0,0,0,0,0)),((1/1:ℚ),220,(0,0,0,0,0,0,0))]
def raw1050Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1050,270,2,82,![220,145],151,162⟩
theorem raw1050Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1050Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1050Spec]
  decide +kernel
theorem raw1050Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1050Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1050Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1050Spec]
  norm_num [eval,monomial,raw1050Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1050Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1050Valid
#print axioms raw1050Row

def raw1052Poly : Poly := [((1/1:ℚ),124,(0,0,0,0,0,0,0)),((-1/1:ℚ),133,((-1),0,0,0,1,0,0)),((1/1:ℚ),158,(0,0,0,0,0,0,0)),((1/1:ℚ),174,((-2),0,0,0,0,0,0))]
def raw1052Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1052,270,2,84,![124,158],133,174⟩
theorem raw1052Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1052Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1052Spec]
  decide +kernel
theorem raw1052Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1052Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1052Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1052Spec]
  norm_num [eval,monomial,raw1052Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1052Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1052Valid
#print axioms raw1052Row

def raw1064Poly : Poly := [((1/1:ℚ),122,(0,0,0,0,0,0,0)),((-1/1:ℚ),131,((-1),0,0,0,1,0,0)),((1/1:ℚ),168,((-2),0,0,0,0,0,0)),((1/1:ℚ),219,(0,0,0,0,0,0,0))]
def raw1064Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1064,270,2,96,![122,219],131,168⟩
theorem raw1064Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1064Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1064Spec]
  decide +kernel
theorem raw1064Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1064Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1064Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1064Spec]
  norm_num [eval,monomial,raw1064Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1064Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1064Valid
#print axioms raw1064Row

def raw1068Poly : Poly := [((1/1:ℚ),24,((-2),0,0,0,0,0,0)),((-1/1:ℚ),53,((-1),0,0,0,1,0,0)),((1/1:ℚ),71,(0,0,0,0,0,0,0)),((1/1:ℚ),80,(0,0,0,0,0,0,0))]
def raw1068Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1068,270,2,100,![80,71],53,24⟩
theorem raw1068Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1068Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1068Spec]
  decide +kernel
theorem raw1068Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1068Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1068Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1068Spec]
  norm_num [eval,monomial,raw1068Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1068Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1068Valid
#print axioms raw1068Row

def raw1077Poly : Poly := [((1/1:ℚ),143,(0,0,0,0,0,0,0)),((-1/1:ℚ),152,((-1),0,0,0,1,0,0)),((1/1:ℚ),164,((-2),0,0,0,0,0,0)),((1/1:ℚ),210,(0,0,0,0,0,0,0))]
def raw1077Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1077,270,2,109,![143,210],152,164⟩
theorem raw1077Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1077Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1077Spec]
  decide +kernel
theorem raw1077Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1077Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1077Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1077Spec]
  norm_num [eval,monomial,raw1077Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1077Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1077Valid
#print axioms raw1077Row

def raw1078Poly : Poly := [((1/1:ℚ),14,(0,0,0,0,0,0,0)),((1/1:ℚ),46,((-2),0,0,0,0,0,0)),((1/1:ℚ),57,(0,0,0,0,0,0,0)),((-1/1:ℚ),100,((-1),0,0,0,1,0,0))]
def raw1078Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1078,270,2,110,![14,57],100,46⟩
theorem raw1078Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1078Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1078Spec]
  decide +kernel
theorem raw1078Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1078Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1078Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1078Spec]
  norm_num [eval,monomial,raw1078Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1078Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1078Valid
#print axioms raw1078Row

def raw1194Poly : Poly := [((-1/1:ℚ),4,(0,0,(-1),0,0,1,0)),((1/1:ℚ),15,(0,0,(-2),0,0,0,0)),((1/1:ℚ),88,(0,0,0,0,0,0,0)),((1/1:ℚ),142,(0,0,0,0,0,0,0)),((1/1:ℚ),143,(0,0,0,0,0,0,0)),((1/1:ℚ),144,(0,0,0,0,0,0,0)),((1/1:ℚ),145,(0,0,0,0,0,0,0))]
def raw1194Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1194,270,5,1,![88,142,143,144,145],4,15⟩
theorem raw1194Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1194Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1194Spec]
  decide +kernel
theorem raw1194Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1194Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1194Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1194Spec]
  norm_num [eval,monomial,raw1194Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1194Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1194Valid
#print axioms raw1194Row

def raw1195Poly : Poly := [((1/1:ℚ),14,(0,0,0,0,0,0,0)),((-1/1:ℚ),32,(0,0,(-1),0,0,1,0)),((1/1:ℚ),83,(0,0,0,0,0,0,0)),((1/1:ℚ),98,(0,0,(-2),0,0,0,0)),((1/1:ℚ),150,(0,0,0,0,0,0,0)),((1/1:ℚ),151,(0,0,0,0,0,0,0)),((1/1:ℚ),152,(0,0,0,0,0,0,0))]
def raw1195Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1195,270,5,2,![83,150,14,151,152],32,98⟩
theorem raw1195Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1195Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1195Spec]
  decide +kernel
theorem raw1195Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1195Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1195Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1195Spec]
  norm_num [eval,monomial,raw1195Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1195Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1195Valid
#print axioms raw1195Row

def raw1196Poly : Poly := [((-1/1:ℚ),34,(0,0,(-1),0,0,1,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0)),((1/1:ℚ),84,(0,0,0,0,0,0,0)),((1/1:ℚ),97,(0,0,(-2),0,0,0,0)),((1/1:ℚ),156,(0,0,0,0,0,0,0)),((1/1:ℚ),157,(0,0,0,0,0,0,0)),((1/1:ℚ),158,(0,0,0,0,0,0,0))]
def raw1196Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1196,270,5,3,![84,156,157,60,158],34,97⟩
theorem raw1196Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1196Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1196Spec]
  decide +kernel
theorem raw1196Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1196Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1196Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1196Spec]
  norm_num [eval,monomial,raw1196Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1196Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1196Valid
#print axioms raw1196Row

def raw1197Poly : Poly := [((-1/1:ℚ),72,(0,0,(-1),0,0,1,0)),((1/1:ℚ),78,(0,0,0,0,0,0,0)),((1/1:ℚ),80,(0,0,(-2),0,0,0,0)),((1/1:ℚ),100,(0,0,0,0,0,0,0)),((1/1:ℚ),162,(0,0,0,0,0,0,0)),((1/1:ℚ),163,(0,0,0,0,0,0,0)),((1/1:ℚ),164,(0,0,0,0,0,0,0))]
def raw1197Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1197,270,5,4,![78,162,163,164,100],72,80⟩
theorem raw1197Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1197Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1197Spec]
  decide +kernel
theorem raw1197Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1197Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1197Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1197Spec]
  norm_num [eval,monomial,raw1197Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1197Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1197Valid
#print axioms raw1197Row

def raw1199Poly : Poly := [((-1/1:ℚ),6,(0,0,(-1),0,0,1,0)),((1/1:ℚ),33,(0,0,(-2),0,0,0,0)),((1/1:ℚ),48,(0,0,0,0,0,0,0)),((1/1:ℚ),75,(0,0,0,0,0,0,0)),((1/1:ℚ),133,(0,0,0,0,0,0,0)),((1/1:ℚ),168,(0,0,0,0,0,0,0)),((1/1:ℚ),169,(0,0,0,0,0,0,0))]
def raw1199Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1199,270,5,6,![48,75,168,133,169],6,33⟩
theorem raw1199Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1199Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1199Spec]
  decide +kernel
theorem raw1199Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1199Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1199Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1199Spec]
  norm_num [eval,monomial,raw1199Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1199Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1199Valid
#print axioms raw1199Row

def raw1205Poly : Poly := [((1/1:ℚ),6,(0,0,(-2),0,0,0,0)),((1/1:ℚ),16,(0,0,0,0,0,0,0)),((1/1:ℚ),68,(0,0,0,0,0,0,0)),((-1/1:ℚ),75,(0,0,(-1),0,0,1,0)),((1/1:ℚ),125,(0,0,0,0,0,0,0)),((1/1:ℚ),174,(0,0,0,0,0,0,0)),((1/1:ℚ),175,(0,0,0,0,0,0,0))]
def raw1205Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1205,270,5,12,![68,174,16,125,175],75,6⟩
theorem raw1205Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1205Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1205Spec]
  decide +kernel
theorem raw1205Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1205Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1205Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1205Spec]
  norm_num [eval,monomial,raw1205Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1205Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1205Valid
#print axioms raw1205Row

def raw1261Poly : Poly := [((-1/1:ℚ),50,(0,0,0,(-2),0,0,0)),((1/1:ℚ),279,(0,0,0,0,0,0,0))]
def raw1261Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1261,sourceWord101,279,50,1,0,0,0,(-2)⟩
theorem raw1261Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1261Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1261Spec]
  decide +kernel
theorem raw1261Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1261Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1261Spec x y z w v := by
  norm_num [eval,monomial,raw1261Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1261Spec] <;> ring
def raw1261Observation : Fin 553 := ⟨18,by decide⟩
theorem raw1261Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1261Observation)=v raw1261Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1261Observation=[(1,raw1261Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1261Observed
#print axioms raw1261Valid
#print axioms raw1261Row

def raw1284Poly : Poly := [((1/1:ℚ),37,(0,0,0,0,0,0,0)),((-1/1:ℚ),293,(0,0,0,2,0,0,0))]
def raw1284Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1284,sourceWord50,37,293,0,0,0,0,2⟩
theorem raw1284Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1284Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1284Spec]
  decide +kernel
theorem raw1284Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1284Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1284Spec x y z w v := by
  norm_num [eval,monomial,raw1284Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1284Spec] <;> ring
def raw1284Observation : Fin 553 := ⟨325,by decide⟩
theorem raw1284Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1284Observation)=v raw1284Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1284Observation=[(1,raw1284Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1284Observed
#print axioms raw1284Valid
#print axioms raw1284Row

def raw1299Poly : Poly := [((-1/1:ℚ),42,(0,0,0,(-2),0,0,0)),((1/1:ℚ),275,(0,0,0,0,0,0,0))]
def raw1299Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1299,sourceWord179,275,42,(-2),0,0,0,(-2)⟩
theorem raw1299Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1299Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1299Spec]
  decide +kernel
theorem raw1299Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1299Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1299Spec x y z w v := by
  norm_num [eval,monomial,raw1299Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1299Spec] <;> ring
def raw1299Observation : Fin 553 := ⟨51,by decide⟩
theorem raw1299Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1299Observation)=v raw1299Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1299Observation=[(1,raw1299Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1299Observed
#print axioms raw1299Valid
#print axioms raw1299Row

def raw1321Poly : Poly := [((-1/1:ℚ),75,(0,0,0,(-2),0,0,0)),((1/1:ℚ),290,(0,0,0,0,0,0,0))]
def raw1321Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1321,sourceWord130,290,75,2,0,0,0,(-2)⟩
theorem raw1321Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1321Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1321Spec]
  decide +kernel
theorem raw1321Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1321Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1321Spec x y z w v := by
  norm_num [eval,monomial,raw1321Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1321Spec] <;> ring
def raw1321Observation : Fin 553 := ⟨12,by decide⟩
theorem raw1321Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1321Observation)=v raw1321Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1321Observation=[(1,raw1321Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1321Observed
#print axioms raw1321Valid
#print axioms raw1321Row

def raw1324Poly : Poly := [((-1/1:ℚ),16,((-2),0,0,(-2),0,0,0)),((1/1:ℚ),299,(0,0,0,0,0,0,0))]
def raw1324Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1324,sourceWord130,299,16,1,(-2),0,0,(-2)⟩
theorem raw1324Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1324Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1324Spec]
  decide +kernel
theorem raw1324Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1324Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1324Spec x y z w v := by
  norm_num [eval,monomial,raw1324Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1324Spec] <;> ring
def raw1324Observation : Fin 553 := ⟨24,by decide⟩
theorem raw1324Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1324Observation)=v raw1324Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1324Observation=[(1,raw1324Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1324Observed
#print axioms raw1324Valid
#print axioms raw1324Row

def raw1326Poly : Poly := [((-1/1:ℚ),55,(2,0,0,(-2),0,0,0)),((1/1:ℚ),301,(0,0,0,0,0,0,0))]
def raw1326Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1326,sourceWord130,301,55,1,2,0,0,(-2)⟩
theorem raw1326Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1326Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1326Spec]
  decide +kernel
theorem raw1326Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1326Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1326Spec x y z w v := by
  norm_num [eval,monomial,raw1326Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1326Spec] <;> ring
def raw1326Observation : Fin 553 := ⟨45,by decide⟩
theorem raw1326Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1326Observation)=v raw1326Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1326Observation=[(1,raw1326Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1326Observed
#print axioms raw1326Valid
#print axioms raw1326Row

def raw1336Poly : Poly := [((-1/1:ℚ),6,(0,0,0,(-2),0,0,0)),((1/1:ℚ),304,(0,0,0,0,0,0,0))]
def raw1336Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1336,sourceWord10,304,6,0,0,0,0,(-2)⟩
theorem raw1336Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1336Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1336Spec]
  decide +kernel
theorem raw1336Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1336Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1336Spec x y z w v := by
  norm_num [eval,monomial,raw1336Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1336Spec] <;> ring
def raw1336Observation : Fin 553 := ⟨6,by decide⟩
theorem raw1336Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1336Observation)=v raw1336Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1336Observation=[(1,raw1336Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1336Observed
#print axioms raw1336Valid
#print axioms raw1336Row

def raw1338Poly : Poly := [((-1/1:ℚ),39,(0,0,0,(-2),0,0,0)),((1/1:ℚ),305,(0,0,0,0,0,0,0))]
def raw1338Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1338,sourceWord10,305,39,(-1),0,0,0,(-2)⟩
theorem raw1338Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1338Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1338Spec]
  decide +kernel
theorem raw1338Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1338Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1338Spec x y z w v := by
  norm_num [eval,monomial,raw1338Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1338Spec] <;> ring
def raw1338Observation : Fin 553 := ⟨46,by decide⟩
theorem raw1338Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1338Observation)=v raw1338Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1338Observation=[(1,raw1338Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1338Observed
#print axioms raw1338Valid
#print axioms raw1338Row

def raw1357Poly : Poly := [((1/1:ℚ),55,(0,0,0,0,0,0,0)),((-1/1:ℚ),301,((-2),0,0,2,0,0,0))]
def raw1357Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1357,sourceWord77,55,301,(-1),(-2),0,0,2⟩
theorem raw1357Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1357Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1357Spec]
  decide +kernel
theorem raw1357Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1357Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1357Spec x y z w v := by
  norm_num [eval,monomial,raw1357Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1357Spec] <;> ring
def raw1357Observation : Fin 553 := ⟨333,by decide⟩
theorem raw1357Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1357Observation)=v raw1357Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1357Observation=[(1,raw1357Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1357Observed
#print axioms raw1357Valid
#print axioms raw1357Row

def raw1395Poly : Poly := [((-1/1:ℚ),72,(0,0,0,(-2),0,0,0)),((1/1:ℚ),311,(0,0,0,0,0,0,0))]
def raw1395Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1395,sourceWord9,311,72,0,0,0,0,(-2)⟩
theorem raw1395Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1395Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1395Spec]
  decide +kernel
theorem raw1395Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1395Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1395Spec x y z w v := by
  norm_num [eval,monomial,raw1395Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1395Spec] <;> ring
def raw1395Observation : Fin 553 := ⟨4,by decide⟩
theorem raw1395Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1395Observation)=v raw1395Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1395Observation=[(1,raw1395Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1395Observed
#print axioms raw1395Valid
#print axioms raw1395Row

def raw1413Poly : Poly := [((-1/1:ℚ),37,(0,0,0,(-2),0,0,0)),((1/1:ℚ),293,(0,0,0,0,0,0,0))]
def raw1413Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1413,sourceWord99,293,37,(-2),0,0,0,(-2)⟩
theorem raw1413Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1413Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1413Spec]
  decide +kernel
theorem raw1413Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1413Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1413Spec x y z w v := by
  norm_num [eval,monomial,raw1413Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1413Spec] <;> ring
def raw1413Observation : Fin 553 := ⟨36,by decide⟩
theorem raw1413Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1413Observation)=v raw1413Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1413Observation=[(1,raw1413Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1413Observed
#print axioms raw1413Valid
#print axioms raw1413Row

def raw1429Poly : Poly := [((-1/1:ℚ),18,((-2),0,0,(-2),0,0,0)),((1/1:ℚ),316,(0,0,0,0,0,0,0))]
def raw1429Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1429,sourceWord145,316,18,1,(-2),0,0,(-2)⟩
theorem raw1429Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1429Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1429Spec]
  decide +kernel
theorem raw1429Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1429Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1429Spec x y z w v := by
  norm_num [eval,monomial,raw1429Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1429Spec] <;> ring
def raw1429Observation : Fin 553 := ⟨8,by decide⟩
theorem raw1429Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1429Observation)=v raw1429Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1429Observation=[(1,raw1429Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1429Observed
#print axioms raw1429Valid
#print axioms raw1429Row

def raw1446Poly : Poly := [((-1/1:ℚ),37,((-2),0,0,(-2),0,0,0)),((1/1:ℚ),310,(0,0,0,0,0,0,0))]
def raw1446Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1446,sourceWord114,310,37,0,(-2),0,0,(-2)⟩
theorem raw1446Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1446Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1446Spec]
  decide +kernel
theorem raw1446Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1446Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1446Spec x y z w v := by
  norm_num [eval,monomial,raw1446Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1446Spec] <;> ring
def raw1446Observation : Fin 553 := ⟨36,by decide⟩
theorem raw1446Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1446Observation)=v raw1446Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1446Observation=[(1,raw1446Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1446Observed
#print axioms raw1446Valid
#print axioms raw1446Row

def raw1447Poly : Poly := [((-1/1:ℚ),14,(0,0,0,(-2),0,0,0)),((1/1:ℚ),289,(0,0,0,0,0,0,0))]
def raw1447Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1447,sourceWord114,289,14,0,0,0,0,(-2)⟩
theorem raw1447Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1447Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1447Spec]
  decide +kernel
theorem raw1447Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1447Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1447Spec x y z w v := by
  norm_num [eval,monomial,raw1447Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1447Spec] <;> ring
def raw1447Observation : Fin 553 := ⟨22,by decide⟩
theorem raw1447Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1447Observation)=v raw1447Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1447Observation=[(1,raw1447Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1447Observed
#print axioms raw1447Valid
#print axioms raw1447Row

def raw1566Poly : Poly := [((-1/1:ℚ),60,(2,0,0,(-2),0,0,0)),((1/1:ℚ),284,(0,0,0,0,0,0,0))]
def raw1566Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1566,sourceWord41,284,60,0,2,0,0,(-2)⟩
theorem raw1566Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1566Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1566Spec]
  decide +kernel
theorem raw1566Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1566Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1566Spec x y z w v := by
  norm_num [eval,monomial,raw1566Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1566Spec] <;> ring
def raw1566Observation : Fin 553 := ⟨33,by decide⟩
theorem raw1566Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1566Observation)=v raw1566Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1566Observation=[(1,raw1566Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1566Observed
#print axioms raw1566Valid
#print axioms raw1566Row

def raw1568Poly : Poly := [((-1/1:ℚ),2,((-2),0,0,(-2),0,0,0)),((1/1:ℚ),318,(0,0,0,0,0,0,0))]
def raw1568Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1568,sourceWord41,318,2,1,(-2),0,0,(-2)⟩
theorem raw1568Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1568Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1568Spec]
  decide +kernel
theorem raw1568Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1568Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1568Spec x y z w v := by
  norm_num [eval,monomial,raw1568Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1568Spec] <;> ring
def raw1568Observation : Fin 553 := ⟨0,by decide⟩
theorem raw1568Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1568Observation)=v raw1568Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1568Observation=[(1,raw1568Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1568Observed
#print axioms raw1568Valid
#print axioms raw1568Row

def raw1833Poly : Poly := [((-1/1:ℚ),2,(0,(-3),0,(-2),0,0,0)),((1/1:ℚ),323,(0,0,0,0,0,0,0))]
def raw1833Left : ℕ→ℕ
  | 0 => 323
  | _ => 0
def raw1833Right : ℕ→ℕ
  | 0 => 2
  | _ => 0
def raw1833Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1833,378,1,2,(-2646),raw1833Left,raw1833Right,0,(-3),0,(-2)⟩
theorem raw1833Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1833Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1833Spec]
  decide +kernel
theorem raw1833Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1833Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1833Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1833Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1833Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1833Left,raw1833Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1833Observation : Fin 553 := ⟨0,by decide⟩
def raw1833Units : List ℕ := [0]
theorem raw1833Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1833Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1833Spec.q raw1833Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1833Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw1833Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1833Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1833Units raw1833Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw1833Units raw1833Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1833Observed
#print axioms raw1833Valid
#print axioms raw1833Row

def raw1835Poly : Poly := [((-1/1:ℚ),50,((-2),(-1),0,(-2),0,0,0)),((1/1:ℚ),325,(0,0,0,0,0,0,0))]
def raw1835Left : ℕ→ℕ
  | 0 => 325
  | _ => 0
def raw1835Right : ℕ→ℕ
  | 0 => 50
  | _ => 0
def raw1835Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1835,378,1,3,(-1764),raw1835Left,raw1835Right,(-2),(-1),0,(-2)⟩
theorem raw1835Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1835Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1835Spec]
  decide +kernel
theorem raw1835Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1835Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1835Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1835Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1835Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1835Left,raw1835Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1835Observation : Fin 553 := ⟨18,by decide⟩
def raw1835Units : List ℕ := [0]
theorem raw1835Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1835Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1835Spec.q raw1835Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1835Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw1835Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1835Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1835Units raw1835Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw1835Units raw1835Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1835Observed
#print axioms raw1835Valid
#print axioms raw1835Row

def raw1857Poly : Poly := [((-1/1:ℚ),60,(2,1,0,(-2),0,0,0)),((1/1:ℚ),328,(0,0,0,0,0,0,0))]
def raw1857Left : ℕ→ℕ
  | 0 => 328
  | _ => 0
def raw1857Right : ℕ→ℕ
  | 0 => 60
  | _ => 0
def raw1857Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1857,378,1,36,(-147),raw1857Left,raw1857Right,2,1,0,(-2)⟩
theorem raw1857Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1857Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1857Spec]
  decide +kernel
theorem raw1857Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1857Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1857Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1857Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1857Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1857Left,raw1857Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1857Observation : Fin 553 := ⟨33,by decide⟩
def raw1857Units : List ℕ := [0]
theorem raw1857Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1857Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1857Spec.q raw1857Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1857Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw1857Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1857Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1857Units raw1857Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw1857Units raw1857Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1857Observed
#print axioms raw1857Valid
#print axioms raw1857Row

def raw1858Poly : Poly := [((-1/1:ℚ),12,(2,1,0,(-2),0,0,0)),((1/1:ℚ),329,(0,0,0,0,0,0,0))]
def raw1858Left : ℕ→ℕ
  | 0 => 329
  | _ => 0
def raw1858Right : ℕ→ℕ
  | 0 => 12
  | _ => 0
def raw1858Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1858,378,1,(-36),147,raw1858Left,raw1858Right,2,1,0,(-2)⟩
theorem raw1858Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1858Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1858Spec]
  decide +kernel
theorem raw1858Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1858Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1858Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1858Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1858Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1858Left,raw1858Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1858Observation : Fin 553 := ⟨21,by decide⟩
def raw1858Units : List ℕ := [0]
theorem raw1858Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1858Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1858Spec.q raw1858Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1858Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw1858Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1858Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1858Units raw1858Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw1858Units raw1858Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1858Observed
#print axioms raw1858Valid
#print axioms raw1858Row

def raw1861Poly : Poly := [((1/1:ℚ),73,(0,0,0,0,0,0,0)),((-1/1:ℚ),330,((-2),(-3),0,2,0,0,0))]
def raw1861Left : ℕ→ℕ
  | 0 => 73
  | _ => 0
def raw1861Right : ℕ→ℕ
  | 0 => 330
  | _ => 0
def raw1861Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1861,378,1,49,(-108),raw1861Left,raw1861Right,(-2),(-3),0,2⟩
theorem raw1861Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1861Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1861Spec]
  decide +kernel
theorem raw1861Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1861Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1861Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1861Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1861Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1861Left,raw1861Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1861Observation : Fin 553 := ⟨360,by decide⟩
def raw1861Units : List ℕ := [0]
theorem raw1861Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1861Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1861Spec.q raw1861Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1861Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw1861Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1861Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1861Units raw1861Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw1861Units raw1861Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1861Observed
#print axioms raw1861Valid
#print axioms raw1861Row

def raw1863Poly : Poly := [((-1/1:ℚ),53,(0,3,0,(-2),0,0,0)),((1/1:ℚ),332,(0,0,0,0,0,0,0))]
def raw1863Left : ℕ→ℕ
  | 0 => 332
  | _ => 0
def raw1863Right : ℕ→ℕ
  | 0 => 53
  | _ => 0
def raw1863Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1863,378,1,54,(-98),raw1863Left,raw1863Right,0,3,0,(-2)⟩
theorem raw1863Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1863Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1863Spec]
  decide +kernel
theorem raw1863Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1863Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1863Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1863Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1863Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1863Left,raw1863Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1863Observation : Fin 553 := ⟨40,by decide⟩
def raw1863Units : List ℕ := [0]
theorem raw1863Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1863Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1863Spec.q raw1863Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1863Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw1863Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1863Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1863Units raw1863Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw1863Units raw1863Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1863Observed
#print axioms raw1863Valid
#print axioms raw1863Row

def raw1872Poly : Poly := [((-1/1:ℚ),73,(2,3,0,(-2),0,0,0)),((1/1:ℚ),330,(0,0,0,0,0,0,0))]
def raw1872Left : ℕ→ℕ
  | 0 => 330
  | _ => 0
def raw1872Right : ℕ→ℕ
  | 0 => 73
  | _ => 0
def raw1872Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1872,378,1,(-108),49,raw1872Left,raw1872Right,2,3,0,(-2)⟩
theorem raw1872Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1872Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1872Spec]
  decide +kernel
theorem raw1872Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1872Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1872Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1872Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1872Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1872Left,raw1872Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1872Observation : Fin 553 := ⟨7,by decide⟩
def raw1872Units : List ℕ := [0]
theorem raw1872Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1872Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1872Spec.q raw1872Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1872Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw1872Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1872Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1872Units raw1872Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw1872Units raw1872Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1872Observed
#print axioms raw1872Valid
#print axioms raw1872Row

def raw1875Poly : Poly := [((1/1:ℚ),12,(0,0,0,0,0,0,0)),((-1/1:ℚ),329,((-2),(-1),0,2,0,0,0))]
def raw1875Left : ℕ→ℕ
  | 0 => 12
  | _ => 0
def raw1875Right : ℕ→ℕ
  | 0 => 329
  | _ => 0
def raw1875Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1875,378,1,147,(-36),raw1875Left,raw1875Right,(-2),(-1),0,2⟩
theorem raw1875Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1875Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1875Spec]
  decide +kernel
theorem raw1875Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1875Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1875Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1875Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1875Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1875Left,raw1875Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1875Observation : Fin 553 := ⟨364,by decide⟩
def raw1875Units : List ℕ := [0]
theorem raw1875Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1875Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1875Spec.q raw1875Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1875Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw1875Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1875Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1875Units raw1875Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw1875Units raw1875Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1875Observed
#print axioms raw1875Valid
#print axioms raw1875Row

def raw1876Poly : Poly := [((1/1:ℚ),60,(0,0,0,0,0,0,0)),((-1/1:ℚ),328,((-2),(-1),0,2,0,0,0))]
def raw1876Left : ℕ→ℕ
  | 0 => 60
  | _ => 0
def raw1876Right : ℕ→ℕ
  | 0 => 328
  | _ => 0
def raw1876Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1876,378,1,(-147),36,raw1876Left,raw1876Right,(-2),(-1),0,2⟩
theorem raw1876Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1876Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1876Spec]
  decide +kernel
theorem raw1876Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1876Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1876Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1876Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1876Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1876Left,raw1876Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1876Observation : Fin 553 := ⟨365,by decide⟩
def raw1876Units : List ℕ := [0]
theorem raw1876Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1876Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1876Spec.q raw1876Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1876Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw1876Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1876Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1876Units raw1876Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw1876Units raw1876Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1876Observed
#print axioms raw1876Valid
#print axioms raw1876Row

def raw1884Poly : Poly := [((1/1:ℚ),75,(0,0,0,0,0,0,0)),((-1/1:ℚ),301,(0,(-1),0,2,0,0,0))]
def raw1884Left : ℕ→ℕ
  | 0 => 75
  | _ => 0
def raw1884Right : ℕ→ℕ
  | 0 => 301
  | _ => 0
def raw1884Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1884,378,1,(-294),18,raw1884Left,raw1884Right,0,(-1),0,2⟩
theorem raw1884Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1884Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1884Spec]
  decide +kernel
theorem raw1884Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1884Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1884Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1884Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1884Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1884Left,raw1884Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1884Observation : Fin 553 := ⟨333,by decide⟩
def raw1884Units : List ℕ := [0]
theorem raw1884Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1884Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1884Spec.q raw1884Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1884Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw1884Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1884Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1884Units raw1884Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw1884Units raw1884Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1884Observed
#print axioms raw1884Valid
#print axioms raw1884Row

def raw1914Poly : Poly := [((-1/1:ℚ),80,(0,3,0,(-2),0,0,0)),((1/1:ℚ),334,(0,0,0,0,0,0,0))]
def raw1914Left : ℕ→ℕ
  | 1 => 334
  | _ => 0
def raw1914Right : ℕ→ℕ
  | 1 => 80
  | _ => 0
def raw1914Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1914,378,2,27,(-49),raw1914Left,raw1914Right,0,3,0,(-2)⟩
theorem raw1914Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1914Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1914Spec]
  decide +kernel
theorem raw1914Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1914Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1914Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1914Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1914Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1914Left,raw1914Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1914Observation : Fin 553 := ⟨20,by decide⟩
def raw1914Units : List ℕ := [1]
theorem raw1914Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1914Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1914Spec.q raw1914Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1914Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 2 raw1914Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1914Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1914Units raw1914Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=2) v raw1914Units raw1914Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1914Observed
#print axioms raw1914Valid
#print axioms raw1914Row

def raw1915Poly : Poly := [((-1/1:ℚ),46,(0,3,0,(-2),0,0,0)),((1/1:ℚ),335,(0,0,0,0,0,0,0))]
def raw1915Left : ℕ→ℕ
  | 1 => 335
  | _ => 0
def raw1915Right : ℕ→ℕ
  | 1 => 46
  | _ => 0
def raw1915Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1915,378,2,(-27),49,raw1915Left,raw1915Right,0,3,0,(-2)⟩
theorem raw1915Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1915Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1915Spec]
  decide +kernel
theorem raw1915Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1915Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1915Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1915Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1915Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1915Left,raw1915Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1915Observation : Fin 553 := ⟨34,by decide⟩
def raw1915Units : List ℕ := [1]
theorem raw1915Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1915Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1915Spec.q raw1915Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1915Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 2 raw1915Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1915Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1915Units raw1915Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=2) v raw1915Units raw1915Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1915Observed
#print axioms raw1915Valid
#print axioms raw1915Row

def raw1916Poly : Poly := [((1/1:ℚ),46,(0,0,0,0,0,0,0)),((-1/1:ℚ),335,(0,(-3),0,2,0,0,0))]
def raw1916Left : ℕ→ℕ
  | 1 => 46
  | _ => 0
def raw1916Right : ℕ→ℕ
  | 1 => 335
  | _ => 0
def raw1916Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1916,378,2,49,(-27),raw1916Left,raw1916Right,0,(-3),0,2⟩
theorem raw1916Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1916Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1916Spec]
  decide +kernel
theorem raw1916Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1916Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1916Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1916Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1916Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1916Left,raw1916Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1916Observation : Fin 553 := ⟨373,by decide⟩
def raw1916Units : List ℕ := [1]
theorem raw1916Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1916Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1916Spec.q raw1916Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1916Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 2 raw1916Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1916Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1916Units raw1916Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=2) v raw1916Units raw1916Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1916Observed
#print axioms raw1916Valid
#print axioms raw1916Row

def raw1917Poly : Poly := [((1/1:ℚ),80,(0,0,0,0,0,0,0)),((-1/1:ℚ),334,(0,(-3),0,2,0,0,0))]
def raw1917Left : ℕ→ℕ
  | 1 => 80
  | _ => 0
def raw1917Right : ℕ→ℕ
  | 1 => 334
  | _ => 0
def raw1917Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1917,378,2,(-49),27,raw1917Left,raw1917Right,0,(-3),0,2⟩
theorem raw1917Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1917Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1917Spec]
  decide +kernel
theorem raw1917Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1917Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1917Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1917Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1917Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1917Left,raw1917Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1917Observation : Fin 553 := ⟨374,by decide⟩
def raw1917Units : List ℕ := [1]
theorem raw1917Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1917Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1917Spec.q raw1917Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1917Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 2 raw1917Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1917Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1917Units raw1917Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=2) v raw1917Units raw1917Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1917Observed
#print axioms raw1917Valid
#print axioms raw1917Row

def raw1921Poly : Poly := [((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),293,(0,(-1),0,2,0,0,0))]
def raw1921Left : ℕ→ℕ
  | 1 => 6
  | _ => 0
def raw1921Right : ℕ→ℕ
  | 1 => 293
  | _ => 0
def raw1921Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1921,378,2,(-147),9,raw1921Left,raw1921Right,0,(-1),0,2⟩
theorem raw1921Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1921Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1921Spec]
  decide +kernel
theorem raw1921Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1921Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1921Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1921Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1921Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1921Left,raw1921Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1921Observation : Fin 553 := ⟨325,by decide⟩
def raw1921Units : List ℕ := [1]
theorem raw1921Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1921Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1921Spec.q raw1921Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1921Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 2 raw1921Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1921Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1921Units raw1921Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=2) v raw1921Units raw1921Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1921Observed
#print axioms raw1921Valid
#print axioms raw1921Row

def raw1942Poly : Poly := [((-1/1:ℚ),28,((-2),1,0,(-2),0,0,0)),((-1/1:ℚ),75,((-2),1,0,(-2),0,0,0)),((1/1:ℚ),358,(0,0,0,0,0,0,0)),((1/1:ℚ),359,(0,0,0,0,0,0,0))]
def raw1942Left : ℕ→ℕ
  | 1 => 358
  | 2 => 359
  | _ => 0
def raw1942Right : ℕ→ℕ
  | 1 => 28
  | 2 => 75
  | _ => 0
def raw1942Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1942,378,3,(-9),588,raw1942Left,raw1942Right,(-2),1,0,(-2)⟩
theorem raw1942Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1942Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1942Spec]
  decide +kernel
theorem raw1942Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1942Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1942Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1942Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1942Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1942Left,raw1942Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1942Observation : Fin 553 := ⟨119,by decide⟩
def raw1942Units : List ℕ := [1, 2]
theorem raw1942Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1942Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1942Spec.q raw1942Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1942Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw1942Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1942Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1942Units raw1942Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw1942Units raw1942Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1942Observed
#print axioms raw1942Valid
#print axioms raw1942Row

def raw1947Poly : Poly := [((-1/1:ℚ),28,(0,1,0,(-2),0,0,0)),((-1/1:ℚ),33,(0,1,0,(-2),0,0,0)),((1/1:ℚ),330,(0,0,0,0,0,0,0)),((1/1:ℚ),364,(0,0,0,0,0,0,0))]
def raw1947Left : ℕ→ℕ
  | 1 => 364
  | 2 => 330
  | _ => 0
def raw1947Right : ℕ→ℕ
  | 1 => 33
  | 2 => 28
  | _ => 0
def raw1947Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1947,378,3,18,(-294),raw1947Left,raw1947Right,0,1,0,(-2)⟩
theorem raw1947Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1947Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1947Spec]
  decide +kernel
theorem raw1947Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1947Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1947Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1947Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1947Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1947Left,raw1947Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1947Observation : Fin 553 := ⟨127,by decide⟩
def raw1947Units : List ℕ := [2, 1]
theorem raw1947Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1947Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1947Spec.q raw1947Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1947Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw1947Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1947Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1947Units raw1947Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw1947Units raw1947Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1947Observed
#print axioms raw1947Valid
#print axioms raw1947Row

def raw1948Poly : Poly := [((-1/1:ℚ),6,(0,1,0,(-2),0,0,0)),((-1/1:ℚ),16,(0,1,0,(-2),0,0,0)),((1/1:ℚ),331,(0,0,0,0,0,0,0)),((1/1:ℚ),365,(0,0,0,0,0,0,0))]
def raw1948Left : ℕ→ℕ
  | 1 => 331
  | 2 => 365
  | _ => 0
def raw1948Right : ℕ→ℕ
  | 1 => 6
  | 2 => 16
  | _ => 0
def raw1948Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1948,378,3,(-18),294,raw1948Left,raw1948Right,0,1,0,(-2)⟩
theorem raw1948Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1948Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1948Spec]
  decide +kernel
theorem raw1948Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1948Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1948Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1948Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1948Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1948Left,raw1948Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1948Observation : Fin 553 := ⟨126,by decide⟩
def raw1948Units : List ℕ := [1, 2]
theorem raw1948Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1948Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1948Spec.q raw1948Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1948Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw1948Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1948Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1948Units raw1948Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw1948Units raw1948Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1948Observed
#print axioms raw1948Valid
#print axioms raw1948Row

def raw1952Poly : Poly := [((-1/1:ℚ),39,((-2),3,0,(-2),0,0,0)),((-1/1:ℚ),98,((-2),3,0,(-2),0,0,0)),((1/1:ℚ),368,(0,0,0,0,0,0,0)),((1/1:ℚ),369,(0,0,0,0,0,0,0))]
def raw1952Left : ℕ→ℕ
  | 1 => 368
  | 2 => 369
  | _ => 0
def raw1952Right : ℕ→ℕ
  | 1 => 39
  | 2 => 98
  | _ => 0
def raw1952Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1952,378,3,(-27),196,raw1952Left,raw1952Right,(-2),3,0,(-2)⟩
theorem raw1952Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1952Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1952Spec]
  decide +kernel
theorem raw1952Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1952Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1952Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1952Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1952Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1952Left,raw1952Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1952Observation : Fin 553 := ⟨191,by decide⟩
def raw1952Units : List ℕ := [1, 2]
theorem raw1952Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1952Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1952Spec.q raw1952Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1952Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw1952Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1952Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1952Units raw1952Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw1952Units raw1952Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1952Observed
#print axioms raw1952Valid
#print axioms raw1952Row

def raw1955Poly : Poly := [((-1/1:ℚ),42,(2,1,0,(-2),0,0,0)),((-1/1:ℚ),97,(2,1,0,(-2),0,0,0)),((1/1:ℚ),335,(0,0,0,0,0,0,0)),((1/1:ℚ),370,(0,0,0,0,0,0,0))]
def raw1955Left : ℕ→ℕ
  | 1 => 335
  | 2 => 370
  | _ => 0
def raw1955Right : ℕ→ℕ
  | 1 => 42
  | 2 => 97
  | _ => 0
def raw1955Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1955,378,3,36,(-147),raw1955Left,raw1955Right,2,1,0,(-2)⟩
theorem raw1955Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1955Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1955Spec]
  decide +kernel
theorem raw1955Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1955Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1955Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1955Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1955Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1955Left,raw1955Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1955Observation : Fin 553 := ⟨376,by decide⟩
def raw1955Units : List ℕ := [1, 2]
theorem raw1955Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1955Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1955Spec.q raw1955Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1955Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw1955Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1955Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1955Units raw1955Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw1955Units raw1955Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1955Observed
#print axioms raw1955Valid
#print axioms raw1955Row

def raw1956Poly : Poly := [((-1/1:ℚ),34,(2,1,0,(-2),0,0,0)),((-1/1:ℚ),95,(2,1,0,(-2),0,0,0)),((1/1:ℚ),334,(0,0,0,0,0,0,0)),((1/1:ℚ),371,(0,0,0,0,0,0,0))]
def raw1956Left : ℕ→ℕ
  | 1 => 371
  | 2 => 334
  | _ => 0
def raw1956Right : ℕ→ℕ
  | 1 => 95
  | 2 => 34
  | _ => 0
def raw1956Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1956,378,3,(-36),147,raw1956Left,raw1956Right,2,1,0,(-2)⟩
theorem raw1956Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1956Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1956Spec]
  decide +kernel
theorem raw1956Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1956Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1956Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1956Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1956Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1956Left,raw1956Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1956Observation : Fin 553 := ⟨377,by decide⟩
def raw1956Units : List ℕ := [2, 1]
theorem raw1956Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1956Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1956Spec.q raw1956Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1956Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw1956Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1956Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1956Units raw1956Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw1956Units raw1956Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1956Observed
#print axioms raw1956Valid
#print axioms raw1956Row

def raw1961Poly : Poly := [((-1/1:ℚ),14,(0,3,0,(-2),0,0,0)),((-1/1:ℚ),72,(0,3,0,(-2),0,0,0)),((1/1:ℚ),279,(0,0,0,0,0,0,0)),((1/1:ℚ),372,(0,0,0,0,0,0,0))]
def raw1961Left : ℕ→ℕ
  | 1 => 279
  | 2 => 372
  | _ => 0
def raw1961Right : ℕ→ℕ
  | 1 => 72
  | 2 => 14
  | _ => 0
def raw1961Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1961,378,3,54,(-98),raw1961Left,raw1961Right,0,3,0,(-2)⟩
theorem raw1961Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1961Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1961Spec]
  decide +kernel
theorem raw1961Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1961Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1961Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1961Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1961Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1961Left,raw1961Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1961Observation : Fin 553 := ⟨380,by decide⟩
def raw1961Units : List ℕ := [2, 1]
theorem raw1961Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1961Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1961Spec.q raw1961Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1961Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw1961Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1961Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1961Units raw1961Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw1961Units raw1961Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1961Observed
#print axioms raw1961Valid
#print axioms raw1961Row

def raw1962Poly : Poly := [((-1/1:ℚ),0,(0,3,0,(-2),0,0,0)),((-1/1:ℚ),58,(0,3,0,(-2),0,0,0)),((1/1:ℚ),293,(0,0,0,0,0,0,0)),((1/1:ℚ),373,(0,0,0,0,0,0,0))]
def raw1962Left : ℕ→ℕ
  | 1 => 373
  | 2 => 293
  | _ => 0
def raw1962Right : ℕ→ℕ
  | 1 => 58
  | 2 => 0
  | _ => 0
def raw1962Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1962,378,3,(-54),98,raw1962Left,raw1962Right,0,3,0,(-2)⟩
theorem raw1962Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1962Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1962Spec]
  decide +kernel
theorem raw1962Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1962Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1962Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1962Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1962Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1962Left,raw1962Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1962Observation : Fin 553 := ⟨381,by decide⟩
def raw1962Units : List ℕ := [2, 1]
theorem raw1962Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1962Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1962Spec.q raw1962Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1962Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw1962Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1962Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1962Units raw1962Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw1962Units raw1962Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1962Observed
#print axioms raw1962Valid
#print axioms raw1962Row

def raw1974Poly : Poly := [((1/1:ℚ),42,(0,0,0,0,0,0,0)),((1/1:ℚ),97,(0,0,0,0,0,0,0)),((-1/1:ℚ),335,((-2),(-1),0,2,0,0,0)),((-1/1:ℚ),370,((-2),(-1),0,2,0,0,0))]
def raw1974Left : ℕ→ℕ
  | 1 => 42
  | 2 => 97
  | _ => 0
def raw1974Right : ℕ→ℕ
  | 1 => 335
  | 2 => 370
  | _ => 0
def raw1974Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1974,378,3,(-147),36,raw1974Left,raw1974Right,(-2),(-1),0,2⟩
theorem raw1974Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1974Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1974Spec]
  decide +kernel
theorem raw1974Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1974Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1974Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1974Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1974Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1974Left,raw1974Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1974Observation : Fin 553 := ⟨387,by decide⟩
def raw1974Units : List ℕ := [1, 2]
theorem raw1974Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1974Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1974Spec.q raw1974Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1974Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw1974Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1974Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1974Units raw1974Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw1974Units raw1974Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1974Observed
#print axioms raw1974Valid
#print axioms raw1974Row

def raw2009Poly : Poly := [((-1/1:ℚ),33,(0,1,0,(-2),0,0,0)),((-1/1:ℚ),75,(0,1,0,(-2),0,0,0)),((1/1:ℚ),332,(0,0,0,0,0,0,0)),((1/1:ℚ),372,(0,0,0,0,0,0,0))]
def raw2009Left : ℕ→ℕ
  | 1 => 332
  | 5 => 372
  | _ => 0
def raw2009Right : ℕ→ℕ
  | 1 => 33
  | 5 => 75
  | _ => 0
def raw2009Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2009,378,6,(-9),147,raw2009Left,raw2009Right,0,1,0,(-2)⟩
theorem raw2009Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2009Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2009Spec]
  decide +kernel
theorem raw2009Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2009Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2009Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2009Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2009Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2009Left,raw2009Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2009Observation : Fin 553 := ⟨114,by decide⟩
def raw2009Units : List ℕ := [1, 5]
theorem raw2009Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2009Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2009Spec.q raw2009Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2009Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw2009Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2009Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2009Units raw2009Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw2009Units raw2009Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2009Observed
#print axioms raw2009Valid
#print axioms raw2009Row

def raw2013Poly : Poly := [((-1/1:ℚ),1,(0,3,0,(-2),0,0,0)),((-1/1:ℚ),8,(0,3,0,(-2),0,0,0)),((1/1:ℚ),328,(0,0,0,0,0,0,0)),((1/1:ℚ),370,(0,0,0,0,0,0,0))]
def raw2013Left : ℕ→ℕ
  | 1 => 328
  | 5 => 370
  | _ => 0
def raw2013Right : ℕ→ℕ
  | 1 => 8
  | 5 => 1
  | _ => 0
def raw2013Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2013,378,6,(-27),49,raw2013Left,raw2013Right,0,3,0,(-2)⟩
theorem raw2013Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2013Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2013Spec]
  decide +kernel
theorem raw2013Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2013Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2013Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2013Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2013Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2013Left,raw2013Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2013Observation : Fin 553 := ⟨122,by decide⟩
def raw2013Units : List ℕ := [5, 1]
theorem raw2013Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2013Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2013Spec.q raw2013Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2013Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw2013Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2013Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2013Units raw2013Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw2013Units raw2013Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2013Observed
#print axioms raw2013Valid
#print axioms raw2013Row

def raw2014Poly : Poly := [((1/1:ℚ),1,(0,0,0,0,0,0,0)),((1/1:ℚ),8,(0,0,0,0,0,0,0)),((-1/1:ℚ),328,(0,(-3),0,2,0,0,0)),((-1/1:ℚ),370,(0,(-3),0,2,0,0,0))]
def raw2014Left : ℕ→ℕ
  | 1 => 8
  | 5 => 1
  | _ => 0
def raw2014Right : ℕ→ℕ
  | 1 => 328
  | 5 => 370
  | _ => 0
def raw2014Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2014,378,6,49,(-27),raw2014Left,raw2014Right,0,(-3),0,2⟩
theorem raw2014Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2014Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2014Spec]
  decide +kernel
theorem raw2014Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2014Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2014Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2014Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2014Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2014Left,raw2014Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2014Observation : Fin 553 := ⟨406,by decide⟩
def raw2014Units : List ℕ := [1, 5]
theorem raw2014Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2014Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2014Spec.q raw2014Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2014Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw2014Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2014Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2014Units raw2014Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw2014Units raw2014Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2014Observed
#print axioms raw2014Valid
#print axioms raw2014Row

def raw2232Poly : Poly := [((1/1:ℚ),305,((-2),0,0,0,0,0,0)),((-1/1:ℚ),311,((-1),0,0,0,1,0,0)),((1/1:ℚ),316,(0,0,0,0,0,0,0)),((1/1:ℚ),323,(0,0,0,0,0,0,0))]
def raw2232Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2232,378,2,2,![323,316],311,305⟩
theorem raw2232Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2232Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2232Spec]
  decide +kernel
theorem raw2232Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2232Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2232Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2232Spec]
  norm_num [eval,monomial,raw2232Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2232Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2232Valid
#print axioms raw2232Row

def raw2236Poly : Poly := [((1/1:ℚ),275,(0,0,0,0,0,0,0)),((1/1:ℚ),284,((-2),0,0,0,0,0,0)),((-1/1:ℚ),290,((-1),0,0,0,1,0,0)),((1/1:ℚ),304,(0,0,0,0,0,0,0))]
def raw2236Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2236,378,2,6,![304,275],290,284⟩
theorem raw2236Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2236Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2236Spec]
  decide +kernel
theorem raw2236Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2236Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2236Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2236Spec]
  norm_num [eval,monomial,raw2236Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2236Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2236Valid
#print axioms raw2236Row

def raw2239Poly : Poly := [((1/1:ℚ),293,(0,0,0,0,0,0,0)),((-1/1:ℚ),301,((-1),0,0,0,1,0,0)),((1/1:ℚ),310,(0,0,0,0,0,0,0)),((1/1:ℚ),328,((-2),0,0,0,0,0,0))]
def raw2239Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2239,378,2,9,![310,293],301,328⟩
theorem raw2239Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2239Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2239Spec]
  decide +kernel
theorem raw2239Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2239Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2239Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2239Spec]
  norm_num [eval,monomial,raw2239Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2239Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2239Valid
#print axioms raw2239Row

def raw2245Poly : Poly := [((-1/1:ℚ),276,((-1),0,0,0,1,0,0)),((1/1:ℚ),299,(0,0,0,0,0,0,0)),((1/1:ℚ),380,((-2),0,0,0,0,0,0)),((1/1:ℚ),433,(0,0,0,0,0,0,0))]
def raw2245Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2245,378,2,15,![299,433],276,380⟩
theorem raw2245Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2245Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2245Spec]
  decide +kernel
theorem raw2245Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2245Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2245Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2245Spec]
  norm_num [eval,monomial,raw2245Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2245Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2245Valid
#print axioms raw2245Row

def raw2257Poly : Poly := [((1/1:ℚ),318,(0,0,0,0,0,0,0)),((1/1:ℚ),331,((-2),0,0,0,0,0,0)),((-1/1:ℚ),332,((-1),0,0,0,1,0,0)),((1/1:ℚ),334,(0,0,0,0,0,0,0))]
def raw2257Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2257,378,2,27,![318,334],332,331⟩
theorem raw2257Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2257Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2257Spec]
  decide +kernel
theorem raw2257Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2257Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2257Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2257Spec]
  norm_num [eval,monomial,raw2257Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2257Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2257Valid
#print axioms raw2257Row

def raw2266Poly : Poly := [((1/1:ℚ),328,(0,0,0,0,0,0,0)),((1/1:ℚ),364,((-2),0,0,0,0,0,0)),((1/1:ℚ),369,(0,0,0,0,0,0,0)),((-1/1:ℚ),373,((-1),0,0,0,1,0,0))]
def raw2266Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2266,378,2,36,![328,369],373,364⟩
theorem raw2266Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2266Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2266Spec]
  decide +kernel
theorem raw2266Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2266Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2266Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2266Spec]
  norm_num [eval,monomial,raw2266Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2266Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2266Valid
#print axioms raw2266Row

def raw2284Poly : Poly := [((-1/1:ℚ),331,((-1),0,0,0,1,0,0)),((1/1:ℚ),332,(0,0,0,0,0,0,0)),((1/1:ℚ),334,((-2),0,0,0,0,0,0)),((1/1:ℚ),359,(0,0,0,0,0,0,0))]
def raw2284Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2284,378,2,54,![332,359],331,334⟩
theorem raw2284Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2284Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2284Spec]
  decide +kernel
theorem raw2284Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2284Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2284Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2284Spec]
  norm_num [eval,monomial,raw2284Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2284Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2284Valid
#print axioms raw2284Row

def raw2329Poly : Poly := [((-1/1:ℚ),293,((-1),0,0,0,1,0,0)),((1/1:ℚ),301,((-2),0,0,0,0,0,0)),((1/1:ℚ),368,(0,0,0,0,0,0,0)),((1/1:ℚ),370,(0,0,0,0,0,0,0))]
def raw2329Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2329,378,2,99,![368,370],293,301⟩
theorem raw2329Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2329Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2329Spec]
  decide +kernel
theorem raw2329Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2329Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2329Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2329Spec]
  norm_num [eval,monomial,raw2329Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2329Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2329Valid
#print axioms raw2329Row

def raw2347Poly : Poly := [((1/1:ℚ),358,(0,0,0,0,0,0,0)),((-1/1:ℚ),365,((-1),0,0,0,1,0,0)),((1/1:ℚ),371,((-2),0,0,0,0,0,0)),((1/1:ℚ),372,(0,0,0,0,0,0,0))]
def raw2347Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2347,378,2,117,![358,372],365,371⟩
theorem raw2347Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2347Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2347Spec]
  decide +kernel
theorem raw2347Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2347Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2347Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2347Spec]
  norm_num [eval,monomial,raw2347Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2347Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2347Valid
#print axioms raw2347Row

def raw2637Poly : Poly := [((-1/1:ℚ),22,(0,0,(-2),(-2),0,0,0)),((1/1:ℚ),594,(0,0,0,0,0,0,0))]
def raw2637Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨2637,sourceWord130,594,22,3,0,0,(-2),(-2)⟩
theorem raw2637Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw2637Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw2637Spec]
  decide +kernel
theorem raw2637Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2637Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw2637Spec x y z w v := by
  norm_num [eval,monomial,raw2637Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw2637Spec] <;> ring
def raw2637Observation : Fin 553 := ⟨14,by decide⟩
theorem raw2637Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2637Observation)=v raw2637Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2637Observation=[(1,raw2637Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw2637Observed
#print axioms raw2637Valid
#print axioms raw2637Row

def raw2644Poly : Poly := [((-1/1:ℚ),46,(0,0,(-2),(-2),0,0,0)),((1/1:ℚ),595,(0,0,0,0,0,0,0))]
def raw2644Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨2644,sourceWord10,595,46,0,0,0,(-2),(-2)⟩
theorem raw2644Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw2644Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw2644Spec]
  decide +kernel
theorem raw2644Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2644Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw2644Spec x y z w v := by
  norm_num [eval,monomial,raw2644Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw2644Spec] <;> ring
def raw2644Observation : Fin 553 := ⟨34,by decide⟩
theorem raw2644Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2644Observation)=v raw2644Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2644Observation=[(1,raw2644Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw2644Observed
#print axioms raw2644Valid
#print axioms raw2644Row

def raw2651Poly : Poly := [((-1/1:ℚ),31,((-2),0,(-2),(-2),0,0,0)),((1/1:ℚ),597,(0,0,0,0,0,0,0))]
def raw2651Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨2651,sourceWord99,597,31,1,(-2),0,(-2),(-2)⟩
theorem raw2651Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw2651Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw2651Spec]
  decide +kernel
theorem raw2651Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2651Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw2651Spec x y z w v := by
  norm_num [eval,monomial,raw2651Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw2651Spec] <;> ring
def raw2651Observation : Fin 553 := ⟨28,by decide⟩
theorem raw2651Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2651Observation)=v raw2651Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2651Observation=[(1,raw2651Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw2651Observed
#print axioms raw2651Valid
#print axioms raw2651Row

def raw2654Poly : Poly := [((-1/1:ℚ),73,(2,0,(-2),(-2),0,0,0)),((1/1:ℚ),600,(0,0,0,0,0,0,0))]
def raw2654Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨2654,sourceWord41,600,73,1,2,0,(-2),(-2)⟩
theorem raw2654Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw2654Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw2654Spec]
  decide +kernel
theorem raw2654Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2654Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw2654Spec x y z w v := by
  norm_num [eval,monomial,raw2654Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw2654Spec] <;> ring
def raw2654Observation : Fin 553 := ⟨7,by decide⟩
theorem raw2654Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2654Observation)=v raw2654Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2654Observation=[(1,raw2654Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw2654Observed
#print axioms raw2654Valid
#print axioms raw2654Row

def raw2656Poly : Poly := [((-1/1:ℚ),37,((-2),(-1),(-2),(-2),0,0,0)),((1/1:ℚ),601,(0,0,0,0,0,0,0))]
def raw2656Left : ℕ→ℕ
  | 0 => 601
  | _ => 0
def raw2656Right : ℕ→ℕ
  | 0 => 37
  | _ => 0
def raw2656Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2656,1890,1,3,(-44100),raw2656Left,raw2656Right,(-2),(-1),(-2),(-2)⟩
theorem raw2656Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2656Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2656Spec]
  decide +kernel
theorem raw2656Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2656Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2656Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2656Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2656Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2656Left,raw2656Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2656Observation : Fin 553 := ⟨36,by decide⟩
def raw2656Units : List ℕ := [0]
theorem raw2656Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2656Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2656Spec.q raw2656Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2656Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw2656Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2656Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2656Units raw2656Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw2656Units raw2656Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2656Observed
#print axioms raw2656Valid
#print axioms raw2656Row

def raw2664Poly : Poly := [((1/1:ℚ),81,(0,0,0,0,0,0,0)),((-1/1:ℚ),334,((-2),(-3),(-2),2,0,0,0))]
def raw2664Left : ℕ→ℕ
  | 0 => 81
  | _ => 0
def raw2664Right : ℕ→ℕ
  | 0 => 334
  | _ => 0
def raw2664Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2664,1890,1,49,(-2700),raw2664Left,raw2664Right,(-2),(-3),(-2),2⟩
theorem raw2664Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2664Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2664Spec]
  decide +kernel
theorem raw2664Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2664Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2664Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2664Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2664Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2664Left,raw2664Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2664Observation : Fin 553 := ⟨374,by decide⟩
def raw2664Units : List ℕ := [0]
theorem raw2664Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2664Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2664Spec.q raw2664Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2664Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw2664Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2664Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2664Units raw2664Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw2664Units raw2664Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2664Observed
#print axioms raw2664Valid
#print axioms raw2664Row

def raw2666Poly : Poly := [((-1/1:ℚ),90,(0,(-3),2,(-2),0,0,0)),((1/1:ℚ),289,(0,0,0,0,0,0,0))]
def raw2666Left : ℕ→ℕ
  | 0 => 289
  | _ => 0
def raw2666Right : ℕ→ℕ
  | 0 => 90
  | _ => 0
def raw2666Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2666,1890,1,50,(-2646),raw2666Left,raw2666Right,0,(-3),2,(-2)⟩
theorem raw2666Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2666Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2666Spec]
  decide +kernel
theorem raw2666Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2666Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2666Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2666Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2666Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2666Left,raw2666Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2666Observation : Fin 553 := ⟨100,by decide⟩
def raw2666Units : List ℕ := [0]
theorem raw2666Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2666Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2666Spec.q raw2666Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2666Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw2666Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2666Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2666Units raw2666Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw2666Units raw2666Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2666Observed
#print axioms raw2666Valid
#print axioms raw2666Row

def raw2669Poly : Poly := [((1/1:ℚ),74,(0,0,0,0,0,0,0)),((-1/1:ℚ),330,(0,(-3),(-2),2,0,0,0))]
def raw2669Left : ℕ→ℕ
  | 0 => 74
  | _ => 0
def raw2669Right : ℕ→ℕ
  | 0 => 330
  | _ => 0
def raw2669Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2669,1890,1,(-98),1350,raw2669Left,raw2669Right,0,(-3),(-2),2⟩
theorem raw2669Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2669Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2669Spec]
  decide +kernel
theorem raw2669Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2669Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2669Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2669Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2669Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2669Left,raw2669Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2669Observation : Fin 553 := ⟨360,by decide⟩
def raw2669Units : List ℕ := [0]
theorem raw2669Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2669Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2669Spec.q raw2669Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2669Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw2669Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2669Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2669Units raw2669Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw2669Units raw2669Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2669Observed
#print axioms raw2669Valid
#print axioms raw2669Row

def raw2674Poly : Poly := [((1/1:ℚ),172,(0,0,0,0,0,0,0)),((-1/1:ℚ),370,(0,(-1),(-2),2,0,0,0))]
def raw2674Left : ℕ→ℕ
  | 0 => 172
  | _ => 0
def raw2674Right : ℕ→ℕ
  | 0 => 370
  | _ => 0
def raw2674Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2674,1890,1,294,(-450),raw2674Left,raw2674Right,0,(-1),(-2),2⟩
theorem raw2674Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2674Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2674Spec]
  decide +kernel
theorem raw2674Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2674Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2674Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2674Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2674Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2674Left,raw2674Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2674Observation : Fin 553 := ⟨546,by decide⟩
def raw2674Units : List ℕ := [0]
theorem raw2674Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2674Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2674Spec.q raw2674Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2674Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw2674Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2674Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2674Units raw2674Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=1) v raw2674Units raw2674Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2674Observed
#print axioms raw2674Valid
#print axioms raw2674Row

def raw2694Poly : Poly := [((1/1:ℚ),7,(0,0,0,0,0,0,0)),((1/1:ℚ),170,(0,0,0,0,0,0,0)),((-1/1:ℚ),329,(0,(-1),(-2),2,0,0,0)),((-1/1:ℚ),334,(0,(-1),(-2),2,0,0,0))]
def raw2694Left : ℕ→ℕ
  | 1 => 170
  | 2 => 7
  | _ => 0
def raw2694Right : ℕ→ℕ
  | 1 => 334
  | 2 => 329
  | _ => 0
def raw2694Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2694,1890,3,(-294),450,raw2694Left,raw2694Right,0,(-1),(-2),2⟩
theorem raw2694Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2694Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2694Spec]
  decide +kernel
theorem raw2694Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2694Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2694Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2694Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2694Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2694Left,raw2694Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2694Observation : Fin 553 := ⟨551,by decide⟩
def raw2694Units : List ℕ := [2, 1]
theorem raw2694Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2694Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2694Spec.q raw2694Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2694Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw2694Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2694Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2694Units raw2694Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw2694Units raw2694Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2694Observed
#print axioms raw2694Valid
#print axioms raw2694Row

def raw2698Poly : Poly := [((-1/1:ℚ),19,((-2),(-1),0,(-2),0,0,0)),((-1/1:ℚ),37,((-2),(-1),0,(-2),0,0,0)),((-1/1:ℚ),96,((-2),(-1),0,(-2),0,0,0)),((-1/1:ℚ),135,((-2),(-1),0,(-2),0,0,0)),((1/1:ℚ),480,(0,0,0,0,0,0,0)),((1/1:ℚ),604,(0,0,0,0,0,0,0)),((1/1:ℚ),605,(0,0,0,0,0,0,0)),((1/1:ℚ),606,(0,0,0,0,0,0,0))]
def raw2698Left : ℕ→ℕ
  | 1 => 604
  | 2 => 605
  | 3 => 606
  | 4 => 480
  | _ => 0
def raw2698Right : ℕ→ℕ
  | 1 => 135
  | 2 => 19
  | 3 => 37
  | 4 => 96
  | _ => 0
def raw2698Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2698,1890,5,3,(-1764),raw2698Left,raw2698Right,(-2),(-1),0,(-2)⟩
theorem raw2698Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2698Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2698Spec]
  decide +kernel
theorem raw2698Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2698Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2698Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2698Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2698Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2698Left,raw2698Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2698Observation : Fin 553 := ⟨171,by decide⟩
def raw2698Units : List ℕ := [2, 3, 4, 1]
theorem raw2698Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2698Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2698Spec.q raw2698Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2698Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 5 raw2698Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2698Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2698Units raw2698Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=5) v raw2698Units raw2698Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2698Observed
#print axioms raw2698Valid
#print axioms raw2698Row

def raw2701Poly : Poly := [((1/1:ℚ),59,(0,0,0,0,0,0,0)),((1/1:ℚ),174,(0,0,0,0,0,0,0)),((-1/1:ℚ),301,(0,(-1),(-2),2,0,0,0)),((-1/1:ℚ),330,(0,(-1),(-2),2,0,0,0))]
def raw2701Left : ℕ→ℕ
  | 1 => 174
  | 5 => 59
  | _ => 0
def raw2701Right : ℕ→ℕ
  | 1 => 301
  | 5 => 330
  | _ => 0
def raw2701Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2701,1890,6,147,(-225),raw2701Left,raw2701Right,0,(-1),(-2),2⟩
theorem raw2701Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2701Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2701Spec]
  decide +kernel
theorem raw2701Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2701Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2701Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2701Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2701Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2701Left,raw2701Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2701Observation : Fin 553 := ⟨552,by decide⟩
def raw2701Units : List ℕ := [1, 5]
theorem raw2701Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2701Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2701Spec.q raw2701Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2701Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw2701Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2701Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2701Units raw2701Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw2701Units raw2701Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2701Observed
#print axioms raw2701Valid
#print axioms raw2701Row

def raw2707Poly : Poly := [((-1/1:ℚ),594,((-1),0,0,0,1,0,0)),((1/1:ℚ),595,(0,0,0,0,0,0,0)),((1/1:ℚ),597,(0,0,0,0,0,0,0)),((1/1:ℚ),600,((-2),0,0,0,0,0,0))]
def raw2707Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2707,1890,2,34,![595,597],594,600⟩
theorem raw2707Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2707Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2707Spec]
  decide +kernel
theorem raw2707Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2707Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2707Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2707Spec]
  norm_num [eval,monomial,raw2707Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2707Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2707Valid
#print axioms raw2707Row

def raw2712Poly : Poly := [((1/1:ℚ),299,(0,0,(-2),0,0,0,0)),((-1/1:ℚ),325,(0,0,(-1),0,0,1,0)),((1/1:ℚ),480,(0,0,0,0,0,0,0)),((1/1:ℚ),601,(0,0,0,0,0,0,0)),((1/1:ℚ),604,(0,0,0,0,0,0,0)),((1/1:ℚ),605,(0,0,0,0,0,0,0)),((1/1:ℚ),606,(0,0,0,0,0,0,0))]
def raw2712Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2712,1890,5,3,![601,604,605,606,480],325,299⟩
theorem raw2712Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2712Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2712Spec]
  decide +kernel
theorem raw2712Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2712Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2712Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2712Spec]
  norm_num [eval,monomial,raw2712Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2712Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2712Valid
#print axioms raw2712Row

end QuantitativeArithmeticSmallLevelTwentySevenFourthSource
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 2048
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace QuantitativeArithmeticSmallLevelTwentySevenFourthSource
open QuantitativeArithmeticSevenLaurentRows FinitenessRamanujanSum
open QuantitativeArithmeticOriginalMatrixMellin
open QuantitativeArithmeticSmallLevelTwentySevenEntireSource
open QuantitativeArithmeticSmallLevelTwentySevenKnownWords
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
def raw14Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),24,(0,0,0,0,0,0,0))]
def raw14Word : Word := sourceWord101
def raw14Point : ℕ := 24
theorem raw14Infinity : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw14Word 1 0≠0 ∧
    (QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw14Word 1 0:ℚ)*point raw14Point+(QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw14Word 1 1:ℚ)=0 := by decide +kernel
theorem raw14Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw14Poly=v raw14Point := by
  norm_num [eval,monomial,raw14Poly,raw14Point]
theorem raw14Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw14Poly m f z=E z := by
  have hc : coordC raw14Word≠0 := by
    rw [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordC_cast]
    exact_mod_cast raw14Infinity.1
  have hp : coordC raw14Word*(point raw14Point:ℝ)+coordD raw14Word=0 := by
    rw [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordC_cast,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordD_cast]
    exact_mod_cast raw14Infinity.2
  have hE := word_infinity_entire m hm hf raw14Word (point raw14Point) hc hp
  obtain ⟨B,hB⟩ := SmallLevelAdditive.original_common_halfplane hf
  refine ⟨B,actualMellin (2*m) f (point raw14Point),hE,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw14Row]
  exact ((hB (point raw14Point) z hz).2).symm
#print axioms raw14Row
#print axioms raw14Original

def raw45Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),0,(0,0,0,0,0,0,0))]
def raw45Word : Word := sourceWord50
def raw45Point : ℕ := 0
theorem raw45Infinity : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw45Word 1 0≠0 ∧
    (QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw45Word 1 0:ℚ)*point raw45Point+(QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw45Word 1 1:ℚ)=0 := by decide +kernel
theorem raw45Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw45Poly=v raw45Point := by
  norm_num [eval,monomial,raw45Poly,raw45Point]
theorem raw45Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw45Poly m f z=E z := by
  have hc : coordC raw45Word≠0 := by
    rw [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordC_cast]
    exact_mod_cast raw45Infinity.1
  have hp : coordC raw45Word*(point raw45Point:ℝ)+coordD raw45Word=0 := by
    rw [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordC_cast,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordD_cast]
    exact_mod_cast raw45Infinity.2
  have hE := word_infinity_entire m hm hf raw45Word (point raw45Point) hc hp
  obtain ⟨B,hB⟩ := SmallLevelAdditive.original_common_halfplane hf
  refine ⟨B,actualMellin (2*m) f (point raw45Point),hE,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw45Row]
  exact ((hB (point raw45Point) z hz).2).symm
#print axioms raw45Row
#print axioms raw45Original

def raw72Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),32,(0,0,0,0,0,0,0))]
def raw72Word : Word := sourceWord130
def raw72Point : ℕ := 32
theorem raw72Infinity : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw72Word 1 0≠0 ∧
    (QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw72Word 1 0:ℚ)*point raw72Point+(QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw72Word 1 1:ℚ)=0 := by decide +kernel
theorem raw72Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw72Poly=v raw72Point := by
  norm_num [eval,monomial,raw72Poly,raw72Point]
theorem raw72Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw72Poly m f z=E z := by
  have hc : coordC raw72Word≠0 := by
    rw [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordC_cast]
    exact_mod_cast raw72Infinity.1
  have hp : coordC raw72Word*(point raw72Point:ℝ)+coordD raw72Word=0 := by
    rw [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordC_cast,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordD_cast]
    exact_mod_cast raw72Infinity.2
  have hE := word_infinity_entire m hm hf raw72Word (point raw72Point) hc hp
  obtain ⟨B,hB⟩ := SmallLevelAdditive.original_common_halfplane hf
  refine ⟨B,actualMellin (2*m) f (point raw72Point),hE,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw72Row]
  exact ((hB (point raw72Point) z hz).2).symm
#print axioms raw72Row
#print axioms raw72Original

def raw84Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),4,(0,0,0,0,0,0,0))]
def raw84Word : Word := sourceWord10
def raw84Point : ℕ := 4
theorem raw84Infinity : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw84Word 1 0≠0 ∧
    (QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw84Word 1 0:ℚ)*point raw84Point+(QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw84Word 1 1:ℚ)=0 := by decide +kernel
theorem raw84Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw84Poly=v raw84Point := by
  norm_num [eval,monomial,raw84Poly,raw84Point]
theorem raw84Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw84Poly m f z=E z := by
  have hc : coordC raw84Word≠0 := by
    rw [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordC_cast]
    exact_mod_cast raw84Infinity.1
  have hp : coordC raw84Word*(point raw84Point:ℝ)+coordD raw84Word=0 := by
    rw [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordC_cast,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordD_cast]
    exact_mod_cast raw84Infinity.2
  have hE := word_infinity_entire m hm hf raw84Word (point raw84Point) hc hp
  obtain ⟨B,hB⟩ := SmallLevelAdditive.original_common_halfplane hf
  refine ⟨B,actualMellin (2*m) f (point raw84Point),hE,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw84Row]
  exact ((hB (point raw84Point) z hz).2).symm
#print axioms raw84Row
#print axioms raw84Original

def raw111Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),1,(0,0,0,0,0,0,0))]
def raw111Word : Word := sourceWord77
def raw111Point : ℕ := 1
theorem raw111Infinity : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw111Word 1 0≠0 ∧
    (QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw111Word 1 0:ℚ)*point raw111Point+(QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry raw111Word 1 1:ℚ)=0 := by decide +kernel
theorem raw111Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw111Poly=v raw111Point := by
  norm_num [eval,monomial,raw111Poly,raw111Point]
theorem raw111Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw111Poly m f z=E z := by
  have hc : coordC raw111Word≠0 := by
    rw [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordC_cast]
    exact_mod_cast raw111Infinity.1
  have hp : coordC raw111Word*(point raw111Point:ℝ)+coordD raw111Word=0 := by
    rw [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordC_cast,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.coordD_cast]
    exact_mod_cast raw111Infinity.2
  have hE := word_infinity_entire m hm hf raw111Word (point raw111Point) hc hp
  obtain ⟨B,hB⟩ := SmallLevelAdditive.original_common_halfplane hf
  refine ⟨B,actualMellin (2*m) f (point raw111Point),hE,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw111Row]
  exact ((hB (point raw111Point) z hz).2).symm
#print axioms raw111Row
#print axioms raw111Original

def raw568Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),2,(0,0,0,0,0,0,0))]
def raw568Sample : ℕ→ℕ
  | 0 => 2
  | _ => 0
theorem raw568Point : ∀ a : Fin 1, a.val.Coprime 1 → point (raw568Sample a.val)=((((a.val:ℤ)*(270/1:ℕ))%(270:ℤ):ℤ):ℚ)/(270:ℚ) := by decide +kernel
theorem raw568Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw568Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw568Sample v := by
  norm_num [eval,monomial,raw568Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw568Sample,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem raw568Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw568Poly m f z=E z := by
  obtain ⟨hE,B,hB⟩ := SmallLevelTaylor.original_ramanujan_entire (by decide : 0<27) (by omega : 0<2*m) hf (by decide : 0<1)
  refine ⟨B,SmallLevelTaylor.ramanujanEntire 27 (2*m) f 1,fun z => (hE z).differentiableAt,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw568Row]
  have hs := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sample_original point (by decide : 0<270) (by decide : 0<1) (by decide : 1∣270) 0 raw568Sample (by simpa only [zero_add,Nat.cast_ofNat,Int.cast_ofNat] using raw568Point) m f z
  rw [show QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 1 raw568Sample (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) z)=SmallLevelTaylor.ramanujanAdditive (2*m) f 1 0 z by simpa using hs]
  exact (hB z hz).symm
#print axioms raw568Row
#print axioms raw568Original

def raw666Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),37,(0,0,0,0,0,0,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0))]
def raw666Sample : ℕ→ℕ
  | 1 => 50
  | 2 => 37
  | _ => 0
theorem raw666Point : ∀ a : Fin 3, a.val.Coprime 3 → point (raw666Sample a.val)=((((a.val:ℤ)*(270/3:ℕ))%(270:ℤ):ℤ):ℚ)/(270:ℚ) := by decide +kernel
theorem raw666Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw666Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw666Sample v := by
  norm_num [eval,monomial,raw666Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw666Sample,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem raw666Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw666Poly m f z=E z := by
  obtain ⟨hE,B,hB⟩ := SmallLevelTaylor.original_ramanujan_entire (by decide : 0<27) (by omega : 0<2*m) hf (by decide : 0<3)
  refine ⟨B,SmallLevelTaylor.ramanujanEntire 27 (2*m) f 3,fun z => (hE z).differentiableAt,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw666Row]
  have hs := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sample_original point (by decide : 0<270) (by decide : 0<3) (by decide : 3∣270) 0 raw666Sample (by simpa only [zero_add,Nat.cast_ofNat,Int.cast_ofNat] using raw666Point) m f z
  rw [show QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw666Sample (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) z)=SmallLevelTaylor.ramanujanAdditive (2*m) f 3 0 z by simpa using hs]
  exact (hB z hz).symm
#print axioms raw666Row
#print axioms raw666Original

def raw739Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),90,(0,0,0,0,0,0,0)),((1/1:ℚ),91,(0,0,0,0,0,0,0)),((1/1:ℚ),99,(0,0,0,0,0,0,0)),((1/1:ℚ),101,(0,0,0,0,0,0,0))]
def raw739Sample : ℕ→ℕ
  | 1 => 101
  | 2 => 91
  | 3 => 90
  | 4 => 99
  | _ => 0
theorem raw739Point : ∀ a : Fin 5, a.val.Coprime 5 → point (raw739Sample a.val)=((((a.val:ℤ)*(270/5:ℕ))%(270:ℤ):ℤ):ℚ)/(270:ℚ) := by decide +kernel
theorem raw739Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw739Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 5 raw739Sample v := by
  norm_num [eval,monomial,raw739Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw739Sample,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem raw739Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw739Poly m f z=E z := by
  obtain ⟨hE,B,hB⟩ := SmallLevelTaylor.original_ramanujan_entire (by decide : 0<27) (by omega : 0<2*m) hf (by decide : 0<5)
  refine ⟨B,SmallLevelTaylor.ramanujanEntire 27 (2*m) f 5,fun z => (hE z).differentiableAt,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw739Row]
  have hs := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sample_original point (by decide : 0<270) (by decide : 0<5) (by decide : 5∣270) 0 raw739Sample (by simpa only [zero_add,Nat.cast_ofNat,Int.cast_ofNat] using raw739Point) m f z
  rw [show QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 5 raw739Sample (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) z)=SmallLevelTaylor.ramanujanAdditive (2*m) f 5 0 z by simpa using hs]
  exact (hB z hz).symm
#print axioms raw739Row
#print axioms raw739Original

def raw764Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),20,(0,0,0,0,0,0,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0))]
def raw764Sample : ℕ→ℕ
  | 1 => 20
  | 5 => 55
  | _ => 0
theorem raw764Point : ∀ a : Fin 6, a.val.Coprime 6 → point (raw764Sample a.val)=((((a.val:ℤ)*(270/6:ℕ))%(270:ℤ):ℤ):ℚ)/(270:ℚ) := by decide +kernel
theorem raw764Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw764Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw764Sample v := by
  norm_num [eval,monomial,raw764Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw764Sample,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem raw764Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw764Poly m f z=E z := by
  obtain ⟨hE,B,hB⟩ := SmallLevelTaylor.original_ramanujan_entire (by decide : 0<27) (by omega : 0<2*m) hf (by decide : 0<6)
  refine ⟨B,SmallLevelTaylor.ramanujanEntire 27 (2*m) f 6,fun z => (hE z).differentiableAt,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw764Row]
  have hs := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sample_original point (by decide : 0<270) (by decide : 0<6) (by decide : 6∣270) 0 raw764Sample (by simpa only [zero_add,Nat.cast_ofNat,Int.cast_ofNat] using raw764Point) m f z
  rw [show QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw764Sample (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) z)=SmallLevelTaylor.ramanujanAdditive (2*m) f 6 0 z by simpa using hs]
  exact (hB z hz).symm
#print axioms raw764Row
#print axioms raw764Original

def raw844Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),92,(0,0,0,0,0,0,0)),((1/1:ℚ),93,(0,0,0,0,0,0,0)),((1/1:ℚ),127,(0,0,0,0,0,0,0)),((1/1:ℚ),128,(0,0,0,0,0,0,0))]
def raw844Sample : ℕ→ℕ
  | 1 => 92
  | 3 => 128
  | 7 => 127
  | 9 => 93
  | _ => 0
theorem raw844Point : ∀ a : Fin 10, a.val.Coprime 10 → point (raw844Sample a.val)=((((a.val:ℤ)*(270/10:ℕ))%(270:ℤ):ℤ):ℚ)/(270:ℚ) := by decide +kernel
theorem raw844Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw844Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 10 raw844Sample v := by
  norm_num [eval,monomial,raw844Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw844Sample,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem raw844Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw844Poly m f z=E z := by
  obtain ⟨hE,B,hB⟩ := SmallLevelTaylor.original_ramanujan_entire (by decide : 0<27) (by omega : 0<2*m) hf (by decide : 0<10)
  refine ⟨B,SmallLevelTaylor.ramanujanEntire 27 (2*m) f 10,fun z => (hE z).differentiableAt,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw844Row]
  have hs := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sample_original point (by decide : 0<270) (by decide : 0<10) (by decide : 10∣270) 0 raw844Sample (by simpa only [zero_add,Nat.cast_ofNat,Int.cast_ofNat] using raw844Point) m f z
  rw [show QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 10 raw844Sample (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) z)=SmallLevelTaylor.ramanujanAdditive (2*m) f 10 0 z by simpa using hs]
  exact (hB z hz).symm
#print axioms raw844Row
#print axioms raw844Original

def raw916Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),51,(0,0,0,0,0,0,0)),((1/1:ℚ),79,(0,0,0,0,0,0,0)),((1/1:ℚ),126,(0,0,0,0,0,0,0)),((1/1:ℚ),129,(0,0,0,0,0,0,0)),((1/1:ℚ),138,(0,0,0,0,0,0,0)),((1/1:ℚ),139,(0,0,0,0,0,0,0)),((1/1:ℚ),140,(0,0,0,0,0,0,0)),((1/1:ℚ),141,(0,0,0,0,0,0,0))]
def raw916Sample : ℕ→ℕ
  | 1 => 51
  | 7 => 140
  | 11 => 126
  | 13 => 138
  | 17 => 141
  | 19 => 129
  | 23 => 139
  | 29 => 79
  | _ => 0
theorem raw916Point : ∀ a : Fin 30, a.val.Coprime 30 → point (raw916Sample a.val)=((((a.val:ℤ)*(270/30:ℕ))%(270:ℤ):ℤ):ℚ)/(270:ℚ) := by decide +kernel
theorem raw916Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw916Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 30 raw916Sample v := by
  norm_num [eval,monomial,raw916Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw916Sample,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem raw916Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw916Poly m f z=E z := by
  obtain ⟨hE,B,hB⟩ := SmallLevelTaylor.original_ramanujan_entire (by decide : 0<27) (by omega : 0<2*m) hf (by decide : 0<30)
  refine ⟨B,SmallLevelTaylor.ramanujanEntire 27 (2*m) f 30,fun z => (hE z).differentiableAt,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw916Row]
  have hs := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sample_original point (by decide : 0<270) (by decide : 0<30) (by decide : 30∣270) 0 raw916Sample (by simpa only [zero_add,Nat.cast_ofNat,Int.cast_ofNat] using raw916Point) m f z
  rw [show QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 30 raw916Sample (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) z)=SmallLevelTaylor.ramanujanAdditive (2*m) f 30 0 z by simpa using hs]
  exact (hB z hz).symm
#print axioms raw916Row
#print axioms raw916Original

end QuantitativeArithmeticSmallLevelTwentySevenFourthSource
end
