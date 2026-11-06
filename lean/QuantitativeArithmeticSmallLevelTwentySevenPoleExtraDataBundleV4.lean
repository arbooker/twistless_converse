module
public import QuantitativeArithmeticSmallLevelTwentySevenEntireSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenShiftSampleV1
public import QuantitativeArithmeticSmallLevelTwentySevenSignedSourceV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentySevenPoleExtraSource
open QuantitativeArithmeticSevenLaurentRows FinitenessRamanujanSum
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)

def extraPoly0 : Poly := [((-1/1:ℚ),37,(0,-3,0,0,0,0,0)),((1/1:ℚ),39,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,(0,-3,0,0,0,0,0)),((1/1:ℚ),98,(0,0,0,0,0,0,0))]
def extraLeft0 : ℕ → ℕ
  | 1 => 98
  | 5 => 39
  | _ => 0
def extraRight0 : ℕ → ℕ
  | 1 => 37
  | 5 => 50
  | _ => 0
def extraSpec0 : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨0,270,6,5,-135,extraLeft0,extraRight0,0,-3,0,0⟩
theorem extraValid0 : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point extraSpec0 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,extraSpec0]
  decide +kernel
theorem extraRow0 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly0=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading extraSpec0 x y z w 1 v := by
  norm_num [eval,monomial,extraPoly0,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,extraSpec0,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,extraLeft0,extraRight0,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def extraObservation0 : Fin 553 := ⟨110,by decide⟩
def extraUnits0 : List ℕ := [1, 5]
theorem extraObserved0 (v : ℕ → ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation extraObservation0)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval extraSpec0.q extraSpec0.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation extraObservation0)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 extraRight0 v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation extraObservation0=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow extraUnits0 extraRight0 := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v extraUnits0 extraRight0 (by decide +kernel) (by decide +kernel)]
#print axioms extraRow0
#print axioms extraObserved0

def extraPoly1 : Poly := [((1/1:ℚ),18,(0,0,0,0,0,0,0)),((-1/1:ℚ),37,(0,-3,0,0,0,0,0)),((-1/1:ℚ),50,(0,-3,0,0,0,0,0)),((1/1:ℚ),100,(0,0,0,0,0,0,0))]
def extraLeft1 : ℕ → ℕ
  | 1 => 18
  | 5 => 100
  | _ => 0
def extraRight1 : ℕ → ℕ
  | 1 => 37
  | 5 => 50
  | _ => 0
def extraSpec1 : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1,270,6,-5,135,extraLeft1,extraRight1,0,-3,0,0⟩
theorem extraValid1 : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point extraSpec1 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,extraSpec1]
  decide +kernel
theorem extraRow1 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly1=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading extraSpec1 x y z w 1 v := by
  norm_num [eval,monomial,extraPoly1,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,extraSpec1,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,extraLeft1,extraRight1,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def extraObservation1 : Fin 553 := ⟨110,by decide⟩
def extraUnits1 : List ℕ := [1, 5]
theorem extraObserved1 (v : ℕ → ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation extraObservation1)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval extraSpec1.q extraSpec1.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation extraObservation1)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 extraRight1 v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation extraObservation1=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow extraUnits1 extraRight1 := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v extraUnits1 extraRight1 (by decide +kernel) (by decide +kernel)]
#print axioms extraRow1
#print axioms extraObserved1

def extraPoly2 : Poly := [((1/1:ℚ),19,(0,0,0,0,0,0,0)),((1/1:ℚ),38,(0,0,0,0,0,0,0)),((1/1:ℚ),56,(0,0,0,0,0,0,0)),((1/1:ℚ),64,(0,0,0,0,0,0,0)),((1/1:ℚ),94,(0,0,0,0,0,0,0)),((1/1:ℚ),96,(0,0,0,0,0,0,0)),((1/1:ℚ),134,(0,0,0,0,0,0,0)),((1/1:ℚ),135,(0,0,0,0,0,0,0))]
def extraSample2 : ℕ → ℕ
  | 1 => 38
  | 2 => 94
  | 4 => 135
  | 7 => 19
  | 8 => 56
  | 11 => 134
  | 13 => 96
  | 14 => 64
  | _ => 0
theorem extraPoint2 : ∀ a : Fin 15, a.val.Coprime 15 → point (extraSample2 a.val)=((((a.val:ℤ)*(270/15:ℕ))%(270:ℤ):ℤ):ℚ)/(270:ℚ) := by decide +kernel
theorem extraRow2 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly2=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 15 extraSample2 v := by
  norm_num [eval,monomial,extraPoly2,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,extraSample2,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem extraOriginal2 (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ → ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly2 m f z=E z := by
  obtain ⟨hE,B,hB⟩ := SmallLevelTaylor.original_ramanujan_entire (by decide : 0<27) (by omega : 0<2*m) hf (by decide : 0<15)
  refine ⟨B,SmallLevelTaylor.ramanujanEntire 27 (2*m) f 15,fun z => (hE z).differentiableAt,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow2]
  have hs := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sample_original point (by decide : 0<270) (by decide : 0<15) (by decide : 15∣270) 0 extraSample2 (by simpa only [zero_add,Nat.cast_ofNat,Int.cast_ofNat] using extraPoint2) m f z
  rw [show QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 15 extraSample2 (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) z)=SmallLevelTaylor.ramanujanAdditive (2*m) f 15 0 z by simpa using hs]
  exact (hB z hz).symm
#print axioms extraOriginal2

def extraPoly3 : Poly := [((1/1:ℚ),1,(-2,0,0,0,0,0,0)),((-1/1:ℚ),24,(-1,0,0,0,1,0,0)),((1/1:ℚ),53,(0,0,0,0,0,0,0)),((1/1:ℚ),137,(0,0,0,0,0,0,0))]
def extraSpec3 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨3,270,2,65,![137,53],24,1⟩
theorem extraValid3 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec3 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec3]
  decide +kernel
theorem extraRow3 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly3=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec3 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec3]
  norm_num [eval,monomial,extraPoly3,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec3,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal3 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly3 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec3 extraValid3 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow3,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec3 extraValid3.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal3

def extraPoly4 : Poly := [((1/1:ℚ),15,(0,0,0,0,0,0,0)),((1/1:ℚ),66,(0,0,0,0,0,0,0)),((1/1:ℚ),136,(0,0,0,0,0,0,0))]
def extraSpec4 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨4,270,3,25,![15,66,136],97,55⟩
theorem extraValid4 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec4 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec4]
  decide +kernel
theorem extraRow4 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly4=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec4 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec4]
  norm_num [eval,monomial,extraPoly4,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec4,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal4 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly4 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec4 extraValid4 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow4,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec4 extraValid4.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal4

def extraPoly5 : Poly := [((1/1:ℚ),35,(0,0,0,0,0,0,0)),((1/1:ℚ),57,(0,0,0,0,0,0,0)),((1/1:ℚ),137,(0,0,0,0,0,0,0))]
def extraSpec5 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨5,270,3,65,![137,35,57],95,20⟩
theorem extraValid5 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec5 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec5]
  decide +kernel
theorem extraRow5 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly5=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec5 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec5]
  norm_num [eval,monomial,extraPoly5,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec5,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal5 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly5 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec5 extraValid5 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow5,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec5 extraValid5.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal5

def extraPoly6 : Poly := [((1/1:ℚ),37,(0,0,0,-2,0,0,0)),((-1/1:ℚ),37,(0,0,0,-1,0,0,1)),((1/1:ℚ),37,(0,0,0,0,0,0,0)),((1/1:ℚ),293,(0,0,0,0,0,0,0)),((1/1:ℚ),302,(0,0,0,0,0,0,0)),((1/1:ℚ),328,(0,0,0,0,0,0,0)),((1/1:ℚ),364,(0,0,0,0,0,0,0)),((1/1:ℚ),371,(0,0,0,0,0,0,0)),((1/1:ℚ),372,(0,0,0,0,0,0,0))]
def extraSpec6 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨6,378,7,36,![328,371,364,293,37,372,302],37,37⟩
theorem extraValid6 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec6 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec6]
  decide +kernel
theorem extraRow6 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly6=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec6 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec6]
  norm_num [eval,monomial,extraPoly6,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec6,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal6 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly6 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec6 extraValid6 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow6,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec6 extraValid6.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal6

def extraPoly7 : Poly := [((1/1:ℚ),106,(-2,0,0,0,0,0,0)),((1/1:ℚ),166,(0,0,0,0,0,0,0)),((-1/1:ℚ),176,(-1,0,0,0,1,0,0)),((1/1:ℚ),260,(0,0,0,0,0,0,0))]
def extraSpec7 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨7,270,2,23,![260,166],176,106⟩
theorem extraValid7 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec7 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec7]
  decide +kernel
theorem extraRow7 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly7=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec7 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec7]
  norm_num [eval,monomial,extraPoly7,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec7,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal7 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly7 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec7 extraValid7 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow7,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec7 extraValid7.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal7

def extraPoly8 : Poly := [((1/1:ℚ),40,(0,0,0,0,0,0,0)),((1/1:ℚ),71,(0,0,0,0,0,0,0)),((1/1:ℚ),103,(0,0,0,0,0,0,0)),((-1/1:ℚ),118,(0,0,-1,0,0,1,0)),((1/1:ℚ),136,(0,0,-2,0,0,0,0)),((1/1:ℚ),223,(0,0,0,0,0,0,0)),((1/1:ℚ),224,(0,0,0,0,0,0,0))]
def extraSpec8 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨8,270,5,19,![40,223,224,103,71],118,136⟩
theorem extraValid8 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec8 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec8]
  decide +kernel
theorem extraRow8 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly8=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec8 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec8]
  norm_num [eval,monomial,extraPoly8,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec8,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal8 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly8 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec8 extraValid8 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow8,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec8 extraValid8.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal8

def extraPoly9 : Poly := [((1/1:ℚ),362,(0,0,0,0,0,0,0)),((-1/1:ℚ),438,(-1,0,0,0,1,0,0)),((1/1:ℚ),477,(-2,0,0,0,0,0,0)),((1/1:ℚ),480,(0,0,0,0,0,0,0))]
def extraSpec9 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨9,378,2,114,![362,480],438,477⟩
theorem extraValid9 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec9 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec9]
  decide +kernel
theorem extraRow9 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly9=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec9 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec9]
  norm_num [eval,monomial,extraPoly9,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec9,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal9 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly9 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec9 extraValid9 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow9,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec9 extraValid9.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal9

def extraPoly10 : Poly := [((-1/1:ℚ),2,(-2,0,0,0,0,0,0)),((1/1:ℚ),3,(0,0,0,0,0,0,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((-1/1:ℚ),28,(-2,0,0,0,0,0,0)),((-1/1:ℚ),33,(-2,0,0,0,0,0,0)),((-1/1:ℚ),37,(-2,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,(-2,0,0,0,0,0,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0)),((-1/1:ℚ),75,(-2,0,0,0,0,0,0)),((1/1:ℚ),97,(0,0,0,0,0,0,0)),((1/1:ℚ),271,(0,0,0,0,0,0,0)),((-1/1:ℚ),273,(-2,0,0,0,0,0,0)),((1/1:ℚ),275,(0,0,0,0,0,0,0)),((-1/1:ℚ),279,(-2,0,0,0,0,0,0)),((1/1:ℚ),287,(0,0,0,0,0,0,0)),((-1/1:ℚ),290,(-2,0,0,0,0,0,0)),((-1/1:ℚ),298,(-2,0,0,0,0,0,0)),((1/1:ℚ),299,(0,0,0,0,0,0,0)),((-1/1:ℚ),301,(-2,0,0,0,0,0,0)),((-1/1:ℚ),302,(-2,0,0,0,0,0,0)),((1/1:ℚ),310,(0,0,0,0,0,0,0)),((-1/1:ℚ),313,(-2,0,0,0,0,0,0)),((1/1:ℚ),318,(0,0,0,0,0,0,0)),((1/1:ℚ),326,(0,0,0,0,0,0,0)),((-1/1:ℚ),328,(-2,0,0,0,0,0,0)),((-1/1:ℚ),329,(-2,0,0,0,0,0,0)),((-1/1:ℚ),330,(-2,0,0,0,0,0,0)),((-1/1:ℚ),331,(-2,0,0,0,0,0,0)),((-1/1:ℚ),332,(-2,0,0,0,0,0,0)),((-1/1:ℚ),334,(-2,0,0,0,0,0,0)),((-1/1:ℚ),335,(-2,0,0,0,0,0,0)),((1/1:ℚ),346,(0,0,0,0,0,0,0)),((1/1:ℚ),347,(0,0,0,0,0,0,0)),((-1/1:ℚ),354,(-2,0,0,0,0,0,0)),((-1/1:ℚ),355,(-2,0,0,0,0,0,0)),((1/1:ℚ),356,(0,0,0,0,0,0,0)),((1/1:ℚ),357,(0,0,0,0,0,0,0)),((1/1:ℚ),358,(0,0,0,0,0,0,0)),((1/1:ℚ),359,(0,0,0,0,0,0,0)),((-1/1:ℚ),360,(-2,0,0,0,0,0,0)),((-1/1:ℚ),361,(-2,0,0,0,0,0,0)),((-1/1:ℚ),364,(-2,0,0,0,0,0,0)),((-1/1:ℚ),365,(-2,0,0,0,0,0,0)),((1/1:ℚ),366,(0,0,0,0,0,0,0)),((1/1:ℚ),367,(0,0,0,0,0,0,0)),((1/1:ℚ),368,(0,0,0,0,0,0,0)),((1/1:ℚ),369,(0,0,0,0,0,0,0)),((-1/1:ℚ),370,(-2,0,0,0,0,0,0)),((-1/1:ℚ),371,(-2,0,0,0,0,0,0)),((-1/1:ℚ),372,(-2,0,0,0,0,0,0)),((-1/1:ℚ),378,(-2,0,0,0,0,0,0)),((-1/1:ℚ),379,(-2,0,0,0,0,0,0)),((1/1:ℚ),407,(0,0,0,0,0,0,0)),((1/1:ℚ),408,(0,0,0,0,0,0,0)),((1/1:ℚ),410,(0,0,0,0,0,0,0)),((1/1:ℚ),411,(0,0,0,0,0,0,0)),((1/1:ℚ),413,(0,0,0,0,0,0,0)),((-1/1:ℚ),427,(-2,0,0,0,0,0,0)),((-1/1:ℚ),428,(-2,0,0,0,0,0,0)),((1/1:ℚ),434,(0,0,0,0,0,0,0)),((-1/1:ℚ),436,(-2,0,0,0,0,0,0)),((1/1:ℚ),437,(0,0,0,0,0,0,0)),((-1/1:ℚ),438,(-2,0,0,0,0,0,0)),((-1/1:ℚ),476,(-2,0,0,0,0,0,0)),((1/1:ℚ),479,(0,0,0,0,0,0,0)),((1/1:ℚ),480,(0,0,0,0,0,0,0)),((1/1:ℚ),482,(0,0,0,0,0,0,0)),((1/1:ℚ),485,(0,0,0,0,0,0,0)),((1/1:ℚ),526,(0,0,0,0,0,0,0)),((1/1:ℚ),527,(0,0,0,0,0,0,0))]
def extraLeft10 : ℕ → ℕ
  | 1 => 310
  | 2 => 299
  | 4 => 318
  | 5 => 482
  | 8 => 407
  | 10 => 20
  | 11 => 526
  | 13 => 413
  | 16 => 368
  | 17 => 97
  | 19 => 358
  | 20 => 346
  | 22 => 356
  | 23 => 527
  | 25 => 366
  | 26 => 408
  | 29 => 479
  | 31 => 3
  | 32 => 275
  | 34 => 437
  | 37 => 369
  | 38 => 60
  | 40 => 359
  | 41 => 347
  | 43 => 357
  | 44 => 410
  | 46 => 367
  | 47 => 485
  | 50 => 480
  | 52 => 55
  | 53 => 411
  | 55 => 434
  | 58 => 271
  | 59 => 42
  | 61 => 287
  | 62 => 326
  | _ => 0
def extraRight10 : ℕ → ℕ
  | 1 => 313
  | 2 => 2
  | 4 => 290
  | 5 => 301
  | 8 => 328
  | 10 => 427
  | 11 => 332
  | 13 => 378
  | 16 => 75
  | 17 => 371
  | 19 => 428
  | 20 => 331
  | 22 => 354
  | 23 => 50
  | 25 => 360
  | 26 => 364
  | 29 => 335
  | 31 => 436
  | 32 => 279
  | 34 => 273
  | 37 => 33
  | 38 => 334
  | 40 => 438
  | 41 => 365
  | 43 => 355
  | 44 => 37
  | 46 => 361
  | 47 => 330
  | 50 => 370
  | 52 => 476
  | 53 => 372
  | 55 => 379
  | 58 => 28
  | 59 => 329
  | 61 => 298
  | 62 => 302
  | _ => 0
def extraSpec10 : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨10,378,63,3,-12,extraLeft10,extraRight10,-2,0,0,0⟩
theorem extraValid10 : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point extraSpec10 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,extraSpec10]
  decide +kernel
theorem extraRow10 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly10=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading extraSpec10 x y z w 1 v := by
  norm_num [eval,monomial,extraPoly10,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,extraSpec10,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,extraLeft10,extraRight10,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def extraObservation10 : Fin 553 := ⟨516,by decide⟩
def extraUnits10 : List ℕ := [2, 58, 37, 44, 23, 16, 34, 32, 4, 61, 5, 62, 1, 8, 59, 47, 20, 11, 38, 29, 22, 43, 25, 46, 26, 41, 50, 17, 53, 13, 55, 10, 19, 31, 40, 52]
theorem extraObserved10 (v : ℕ → ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation extraObservation10)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval extraSpec10.q extraSpec10.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation extraObservation10)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 63 extraRight10 v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation extraObservation10=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow extraUnits10 extraRight10 := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=63) v extraUnits10 extraRight10 (by decide +kernel) (by decide +kernel)]
#print axioms extraRow10
#print axioms extraObserved10

def extraPoly11 : Poly := [((-1/1:ℚ),12,(2,-2,0,0,0,0,0)),((1/1:ℚ),14,(0,0,0,0,0,0,0)),((1/1:ℚ),31,(0,0,0,0,0,0,0)),((-1/1:ℚ),34,(2,-2,0,0,0,0,0)),((1/1:ℚ),39,(0,0,0,0,0,0,0)),((-1/1:ℚ),42,(2,-2,0,0,0,0,0)),((1/1:ℚ),53,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(2,-2,0,0,0,0,0)),((1/1:ℚ),72,(0,0,0,0,0,0,0)),((-1/1:ℚ),95,(2,-2,0,0,0,0,0)),((-1/1:ℚ),97,(2,-2,0,0,0,0,0)),((1/1:ℚ),98,(0,0,0,0,0,0,0)),((-1/1:ℚ),270,(2,-2,0,0,0,0,0)),((-1/1:ℚ),275,(2,-2,0,0,0,0,0)),((1/1:ℚ),278,(0,0,0,0,0,0,0)),((-1/1:ℚ),281,(2,-2,0,0,0,0,0)),((1/1:ℚ),288,(0,0,0,0,0,0,0)),((1/1:ℚ),289,(0,0,0,0,0,0,0)),((1/1:ℚ),297,(0,0,0,0,0,0,0)),((-1/1:ℚ),299,(2,-2,0,0,0,0,0)),((1/1:ℚ),300,(0,0,0,0,0,0,0)),((1/1:ℚ),315,(0,0,0,0,0,0,0)),((1/1:ℚ),324,(0,0,0,0,0,0,0)),((-1/1:ℚ),325,(2,-2,0,0,0,0,0)),((-1/1:ℚ),326,(2,-2,0,0,0,0,0)),((1/1:ℚ),342,(0,0,0,0,0,0,0)),((1/1:ℚ),343,(0,0,0,0,0,0,0)),((-1/1:ℚ),344,(2,-2,0,0,0,0,0)),((-1/1:ℚ),345,(2,-2,0,0,0,0,0)),((-1/1:ℚ),346,(2,-2,0,0,0,0,0)),((-1/1:ℚ),347,(2,-2,0,0,0,0,0)),((1/1:ℚ),374,(0,0,0,0,0,0,0)),((1/1:ℚ),375,(0,0,0,0,0,0,0)),((1/1:ℚ),397,(0,0,0,0,0,0,0)),((1/1:ℚ),398,(0,0,0,0,0,0,0)),((1/1:ℚ),399,(0,0,0,0,0,0,0)),((1/1:ℚ),401,(0,0,0,0,0,0,0)),((-1/1:ℚ),402,(2,-2,0,0,0,0,0)),((-1/1:ℚ),403,(2,-2,0,0,0,0,0)),((-1/1:ℚ),404,(2,-2,0,0,0,0,0)),((-1/1:ℚ),405,(2,-2,0,0,0,0,0)),((-1/1:ℚ),407,(2,-2,0,0,0,0,0)),((-1/1:ℚ),409,(2,-2,0,0,0,0,0)),((-1/1:ℚ),410,(2,-2,0,0,0,0,0)),((-1/1:ℚ),411,(2,-2,0,0,0,0,0)),((1/1:ℚ),458,(0,0,0,0,0,0,0)),((1/1:ℚ),459,(0,0,0,0,0,0,0)),((1/1:ℚ),461,(0,0,0,0,0,0,0)),((-1/1:ℚ),462,(2,-2,0,0,0,0,0)),((-1/1:ℚ),463,(2,-2,0,0,0,0,0)),((-1/1:ℚ),464,(2,-2,0,0,0,0,0)),((-1/1:ℚ),465,(2,-2,0,0,0,0,0)),((-1/1:ℚ),478,(2,-2,0,0,0,0,0)),((-1/1:ℚ),479,(2,-2,0,0,0,0,0)),((-1/1:ℚ),480,(2,-2,0,0,0,0,0)),((-1/1:ℚ),481,(2,-2,0,0,0,0,0)),((1/1:ℚ),486,(0,0,0,0,0,0,0)),((1/1:ℚ),487,(0,0,0,0,0,0,0)),((1/1:ℚ),492,(0,0,0,0,0,0,0)),((1/1:ℚ),493,(0,0,0,0,0,0,0)),((1/1:ℚ),520,(0,0,0,0,0,0,0)),((1/1:ℚ),521,(0,0,0,0,0,0,0)),((1/1:ℚ),522,(0,0,0,0,0,0,0)),((1/1:ℚ),523,(0,0,0,0,0,0,0)),((-1/1:ℚ),524,(2,-2,0,0,0,0,0)),((-1/1:ℚ),525,(2,-2,0,0,0,0,0)),((-1/1:ℚ),526,(2,-2,0,0,0,0,0)),((-1/1:ℚ),527,(2,-2,0,0,0,0,0)),((1/1:ℚ),544,(0,0,0,0,0,0,0)),((1/1:ℚ),545,(0,0,0,0,0,0,0)),((1/1:ℚ),549,(0,0,0,0,0,0,0)),((1/1:ℚ),550,(0,0,0,0,0,0,0))]
def extraLeft11 : ℕ → ℕ
  | 1 => 289
  | 2 => 300
  | 4 => 72
  | 5 => 520
  | 8 => 397
  | 10 => 374
  | 11 => 98
  | 13 => 458
  | 16 => 544
  | 17 => 398
  | 19 => 550
  | 20 => 342
  | 22 => 486
  | 23 => 521
  | 25 => 14
  | 26 => 399
  | 29 => 278
  | 31 => 315
  | 32 => 31
  | 34 => 459
  | 37 => 545
  | 38 => 492
  | 40 => 487
  | 41 => 343
  | 43 => 549
  | 44 => 401
  | 46 => 53
  | 47 => 522
  | 50 => 523
  | 52 => 375
  | 53 => 39
  | 55 => 461
  | 58 => 297
  | 59 => 493
  | 61 => 288
  | 62 => 324
  | _ => 0
def extraRight11 : ℕ → ℕ
  | 1 => 326
  | 2 => 325
  | 4 => 299
  | 5 => 34
  | 8 => 464
  | 10 => 407
  | 11 => 402
  | 13 => 526
  | 16 => 462
  | 17 => 478
  | 19 => 97
  | 20 => 403
  | 22 => 346
  | 23 => 344
  | 25 => 527
  | 26 => 12
  | 29 => 404
  | 31 => 479
  | 32 => 281
  | 34 => 275
  | 37 => 409
  | 38 => 405
  | 40 => 60
  | 41 => 524
  | 43 => 347
  | 44 => 345
  | 46 => 410
  | 47 => 95
  | 50 => 465
  | 52 => 480
  | 53 => 525
  | 55 => 411
  | 58 => 463
  | 59 => 481
  | 61 => 42
  | 62 => 270
  | _ => 0
def extraSpec11 : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨11,378,63,4,-9,extraLeft11,extraRight11,2,-2,0,0⟩
theorem extraValid11 : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point extraSpec11 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,extraSpec11]
  decide +kernel
theorem extraRow11 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly11=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading extraSpec11 x y z w 1 v := by
  norm_num [eval,monomial,extraPoly11,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,extraSpec11,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,extraLeft11,extraRight11,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def extraObservation11 : Fin 553 := ⟨518,by decide⟩
def extraUnits11 : List ℕ := [26, 5, 61, 40, 47, 19, 62, 34, 32, 4, 2, 1, 23, 44, 22, 43, 11, 20, 29, 38, 10, 37, 46, 55, 16, 58, 8, 50, 17, 31, 52, 59, 41, 53, 13, 25]
theorem extraObserved11 (v : ℕ → ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation extraObservation11)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval extraSpec11.q extraSpec11.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation extraObservation11)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 63 extraRight11 v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation extraObservation11=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow extraUnits11 extraRight11 := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=63) v extraUnits11 extraRight11 (by decide +kernel) (by decide +kernel)]
#print axioms extraRow11
#print axioms extraObserved11

def extraPoly12 : Poly := [((1/1:ℚ),390,(0,0,0,0,0,0,0)),((1/1:ℚ),507,(0,0,0,0,0,0,0)),((1/1:ℚ),510,(0,0,0,0,0,0,0))]
def extraSpec12 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨12,378,3,17,![507,510,390],407,366⟩
theorem extraValid12 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec12 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec12]
  decide +kernel
theorem extraRow12 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly12=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec12 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec12]
  norm_num [eval,monomial,extraPoly12,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec12,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal12 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly12 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec12 extraValid12 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow12,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec12 extraValid12.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal12

def extraPoly13 : Poly := [((1/1:ℚ),198,(0,0,0,0,0,0,0)),((-1/1:ℚ),215,(-1,0,0,0,1,0,0)),((1/1:ℚ),226,(0,0,0,0,0,0,0)),((1/1:ℚ),237,(-2,0,0,0,0,0,0))]
def extraSpec13 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨13,270,2,118,![198,226],215,237⟩
theorem extraValid13 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec13 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec13]
  decide +kernel
theorem extraRow13 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly13=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec13 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec13]
  norm_num [eval,monomial,extraPoly13,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec13,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal13 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly13 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec13 extraValid13 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow13,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec13 extraValid13.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal13

def extraPoly14 : Poly := [((1/1:ℚ),118,(0,0,0,0,0,0,0)),((-1/1:ℚ),136,(0,0,-1,0,0,1,0)),((1/1:ℚ),149,(0,0,-2,0,0,0,0)),((1/1:ℚ),189,(0,0,0,0,0,0,0)),((1/1:ℚ),240,(0,0,0,0,0,0,0)),((1/1:ℚ),267,(0,0,0,0,0,0,0)),((1/1:ℚ),269,(0,0,0,0,0,0,0))]
def extraSpec14 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨14,270,5,41,![240,118,189,267,269],136,149⟩
theorem extraValid14 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec14 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec14]
  decide +kernel
theorem extraRow14 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly14=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec14 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec14]
  norm_num [eval,monomial,extraPoly14,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec14,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal14 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly14 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec14 extraValid14 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow14,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec14 extraValid14.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal14

def extraPoly15 : Poly := [((1/1:ℚ),353,(0,0,0,0,0,0,0)),((-1/1:ℚ),360,(-1,0,0,0,1,0,0)),((1/1:ℚ),425,(-2,0,0,0,0,0,0)),((1/1:ℚ),526,(0,0,0,0,0,0,0))]
def extraSpec15 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨15,378,2,69,![526,353],360,425⟩
theorem extraValid15 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec15 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec15]
  decide +kernel
theorem extraRow15 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly15=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec15 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec15]
  norm_num [eval,monomial,extraPoly15,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec15,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal15 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly15 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec15 extraValid15 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow15,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec15 extraValid15.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal15

def extraPoly16 : Poly := [((1/1:ℚ),361,(0,0,0,0,0,0,0)),((-1/1:ℚ),432,(-1,0,0,0,1,0,0)),((1/1:ℚ),476,(-2,0,0,0,0,0,0)),((1/1:ℚ),483,(0,0,0,0,0,0,0))]
def extraSpec16 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨16,378,2,75,![483,361],432,476⟩
theorem extraValid16 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec16 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec16]
  decide +kernel
theorem extraRow16 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly16=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec16 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec16]
  norm_num [eval,monomial,extraPoly16,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec16,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal16 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly16 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec16 extraValid16 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow16,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec16 extraValid16.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal16

def extraPoly17 : Poly := [((1/1:ℚ),150,(0,0,0,0,0,0,0)),((-1/1:ℚ),163,(-1,0,0,0,1,0,0)),((1/1:ℚ),179,(-2,0,0,0,0,0,0)),((1/1:ℚ),242,(0,0,0,0,0,0,0))]
def extraSpec17 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨17,270,2,56,![150,242],163,179⟩
theorem extraValid17 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec17 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec17]
  decide +kernel
theorem extraRow17 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly17=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec17 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec17]
  norm_num [eval,monomial,extraPoly17,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec17,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal17 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly17 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec17 extraValid17 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow17,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec17 extraValid17.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal17

def extraPoly18 : Poly := [((1/1:ℚ),473,(0,0,0,0,0,0,0)),((1/1:ℚ),507,(0,0,0,0,0,0,0)),((-1/1:ℚ),520,(-1,0,0,0,1,0,0)),((1/1:ℚ),532,(-2,0,0,0,0,0,0))]
def extraSpec18 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨18,378,2,17,![507,473],520,532⟩
theorem extraValid18 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec18 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec18]
  decide +kernel
theorem extraRow18 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly18=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec18 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec18]
  norm_num [eval,monomial,extraPoly18,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec18,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal18 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly18 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec18 extraValid18 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow18,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec18 extraValid18.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal18

def extraPoly19 : Poly := [((1/1:ℚ),103,(0,0,0,0,0,0,0)),((-1/1:ℚ),106,(-1,0,0,0,1,0,0)),((1/1:ℚ),115,(-2,0,0,0,0,0,0)),((1/1:ℚ),176,(0,0,0,0,0,0,0))]
def extraSpec19 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨19,270,2,46,![176,103],106,115⟩
theorem extraValid19 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec19 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec19]
  decide +kernel
theorem extraRow19 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly19=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec19 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec19]
  norm_num [eval,monomial,extraPoly19,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec19,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal19 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly19 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec19 extraValid19 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow19,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec19 extraValid19.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal19

def extraPoly20 : Poly := [((1/1:ℚ),18,(0,0,0,-2,0,0,0)),((-1/1:ℚ),58,(0,0,0,-1,0,0,1)),((1/1:ℚ),80,(0,0,0,0,0,0,0)),((1/1:ℚ),274,(0,0,0,0,0,0,0)),((1/1:ℚ),277,(0,0,0,0,0,0,0)),((1/1:ℚ),351,(0,0,0,0,0,0,0)),((1/1:ℚ),453,(0,0,0,0,0,0,0)),((1/1:ℚ),497,(0,0,0,0,0,0,0)),((1/1:ℚ),535,(0,0,0,0,0,0,0))]
def extraSpec20 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨20,378,7,32,![277,453,80,274,351,535,497],58,18⟩
theorem extraValid20 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec20 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec20]
  decide +kernel
theorem extraRow20 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly20=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec20 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec20]
  norm_num [eval,monomial,extraPoly20,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec20,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal20 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly20 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec20 extraValid20 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow20,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec20 extraValid20.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal20

def extraPoly21 : Poly := [((1/1:ℚ),66,(0,0,0,-2,0,0,0)),((1/1:ℚ),120,(0,0,0,0,0,0,0)),((-1/1:ℚ),142,(0,0,0,-1,0,0,1)),((1/1:ℚ),451,(0,0,0,0,0,0,0)),((1/1:ℚ),539,(0,0,0,0,0,0,0)),((1/1:ℚ),573,(0,0,0,0,0,0,0)),((1/1:ℚ),577,(0,0,0,0,0,0,0)),((1/1:ℚ),583,(0,0,0,0,0,0,0)),((1/1:ℚ),585,(0,0,0,0,0,0,0))]
def extraSpec21 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨21,378,7,11,![573,577,120,583,585,539,451],142,66⟩
theorem extraValid21 : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point extraSpec21 := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,extraSpec21]
  decide +kernel
theorem extraRow21 (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v extraPoly21=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading extraSpec21 x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec21]
  norm_num [eval,monomial,extraPoly21,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,extraSpec21,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ]
  <;> ring
theorem extraOriginal21 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval extraPoly21 m f z=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.original_leading point extraSpec21 extraValid21 hm hf
  refine ⟨B,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [extraRow21,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.physical_formal extraSpec21 extraValid21.2.2.2.1 m f h3]
  exact hB z hz
#print axioms extraOriginal21

end QuantitativeArithmeticSmallLevelTwentySevenPoleExtraSource
