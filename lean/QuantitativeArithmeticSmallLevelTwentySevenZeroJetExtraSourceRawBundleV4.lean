module
public import QuantitativeArithmeticSmallLevelTwentySevenEntireSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenShiftSampleV1
public import QuantitativeArithmeticSmallLevelTwentySevenSignedSourceV1
public import QuantitativeArithmeticSmallLevelTwentySevenHeckeSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenKnownWordsTheoryV4
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
namespace QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource
open QuantitativeArithmeticSevenLaurentRows FinitenessRamanujanSum
open QuantitativeArithmeticSmallLevelTwentySevenKnownWords
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
open QuantitativeArithmeticOriginalMatrixMellin
open QuantitativeArithmeticSmallLevelTwentySevenEntireSource

def raw847Poly : Poly := [((1/1:ℚ),6,(0,0,0,0,0,0,0)),((-1/1:ℚ),37,(0,(-1),0,0,0,0,0)),((-1/1:ℚ),38,(0,(-1),0,0,0,0,0)),((1/1:ℚ),59,(0,0,0,0,0,0,0)),((-1/1:ℚ),96,(0,(-1),0,0,0,0,0)),((1/1:ℚ),124,(0,0,0,0,0,0,0)),((1/1:ℚ),131,(0,0,0,0,0,0,0)),((-1/1:ℚ),135,(0,(-1),0,0,0,0,0))]
def raw847Left : ℕ→ℕ
  | 1 => 6
  | 3 => 124
  | 7 => 131
  | 9 => 59
  | _ => 0
def raw847Right : ℕ→ℕ
  | 1 => 38
  | 3 => 135
  | 7 => 37
  | 9 => 96
  | _ => 0
def raw847Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨847,270,10,3,(-9),raw847Left,raw847Right,0,(-1),0,0⟩
theorem raw847Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw847Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw847Spec]
  decide +kernel
theorem raw847Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw847Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw847Spec x y z w 1 v := by
  norm_num [eval,monomial,raw847Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw847Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw847Left,raw847Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw847Observation : Fin 553 := ⟨230,by decide⟩
def raw847Units : List ℕ := [7, 1, 9, 3]
theorem raw847Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw847Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw847Spec.q raw847Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw847Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 10 raw847Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw847Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw847Units raw847Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=10) v raw847Units raw847Right (by decide +kernel) (by decide +kernel)]
#print axioms raw847Observed
#print axioms raw847Valid
#print axioms raw847Row

def raw853Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),19,(0,0,0,0,0,0,0)),((1/1:ℚ),38,(0,0,0,0,0,0,0)),((1/1:ℚ),56,(0,0,0,0,0,0,0)),((1/1:ℚ),64,(0,0,0,0,0,0,0)),((1/1:ℚ),94,(0,0,0,0,0,0,0)),((1/1:ℚ),96,(0,0,0,0,0,0,0)),((1/1:ℚ),134,(0,0,0,0,0,0,0)),((1/1:ℚ),135,(0,0,0,0,0,0,0))]
def raw853Sample : ℕ→ℕ
  | 1 => 38
  | 2 => 94
  | 4 => 135
  | 7 => 19
  | 8 => 56
  | 11 => 134
  | 13 => 96
  | 14 => 64
  | _ => 0
theorem raw853Point : ∀ a : Fin 15, a.val.Coprime 15 → point (raw853Sample a.val)=((((a.val:ℤ)*(270/15:ℕ))%(270:ℤ):ℤ):ℚ)/(270:ℚ) := by decide +kernel
theorem raw853Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw853Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 15 raw853Sample v := by
  norm_num [eval,monomial,raw853Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw853Sample,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem raw853Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw853Poly m f z=E z := by
  obtain ⟨hE,B,hB⟩ := SmallLevelTaylor.original_ramanujan_entire (by decide : 0<27) (by omega : 0<2*m) hf (by decide : 0<15)
  refine ⟨B,SmallLevelTaylor.ramanujanEntire 27 (2*m) f 15,fun z => (hE z).differentiableAt,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw853Row]
  have hs := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sample_original point (by decide : 0<270) (by decide : 0<15) (by decide : 15∣270) 0 raw853Sample (by simpa only [zero_add,Nat.cast_ofNat,Int.cast_ofNat] using raw853Point) m f z
  rw [show QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 15 raw853Sample (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) z)=SmallLevelTaylor.ramanujanAdditive (2*m) f 15 0 z by simpa using hs]
  exact (hB z hz).symm
#print axioms raw853Row
#print axioms raw853Original

def raw858Poly : Poly := [((-1/1:ℚ),2,((-2),(-1),0,0,0,0,0)),((1/1:ℚ),10,(0,0,0,0,0,0,0)),((1/1:ℚ),23,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),64,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),90,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),91,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),94,((-2),(-1),0,0,0,0,0)),((1/1:ℚ),97,(0,0,0,0,0,0,0)),((-1/1:ℚ),99,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),134,((-2),(-1),0,0,0,0,0)),((1/1:ℚ),204,(0,0,0,0,0,0,0)),((1/1:ℚ),205,(0,0,0,0,0,0,0)),((1/1:ℚ),216,(0,0,0,0,0,0,0)),((1/1:ℚ),218,(0,0,0,0,0,0,0))]
def raw858Left : ℕ→ℕ
  | 1 => 10
  | 2 => 216
  | 4 => 97
  | 7 => 23
  | 8 => 204
  | 11 => 218
  | 13 => 205
  | 14 => 42
  | _ => 0
def raw858Right : ℕ→ℕ
  | 1 => 64
  | 2 => 2
  | 4 => 94
  | 7 => 50
  | 8 => 91
  | 11 => 90
  | 13 => 134
  | 14 => 99
  | _ => 0
def raw858Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨858,270,15,3,(-36),raw858Left,raw858Right,(-2),(-1),0,0⟩
theorem raw858Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw858Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw858Spec]
  decide +kernel
theorem raw858Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw858Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw858Spec x y z w 1 v := by
  norm_num [eval,monomial,raw858Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw858Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw858Left,raw858Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw858Observation : Fin 553 := ⟨240,by decide⟩
def raw858Units : List ℕ := [2, 7, 1, 11, 8, 4, 14, 13]
theorem raw858Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw858Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw858Spec.q raw858Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw858Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 15 raw858Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw858Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw858Units raw858Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=15) v raw858Units raw858Right (by decide +kernel) (by decide +kernel)]
#print axioms raw858Observed
#print axioms raw858Valid
#print axioms raw858Row

def raw944Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),4,(0,0,0,0,0,0,0)),((1/1:ℚ),15,(0,0,0,0,0,0,0)),((1/1:ℚ),17,(0,0,0,0,0,0,0)),((1/1:ℚ),30,(0,0,0,0,0,0,0)),((1/1:ℚ),35,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(0,0,0,0,0,0,0)),((1/1:ℚ),57,(0,0,0,0,0,0,0)),((1/1:ℚ),66,(0,0,0,0,0,0,0)),((1/1:ℚ),71,(0,0,0,0,0,0,0)),((1/1:ℚ),73,(0,0,0,0,0,0,0)),((1/1:ℚ),118,(0,0,0,0,0,0,0)),((1/1:ℚ),119,(0,0,0,0,0,0,0)),((1/1:ℚ),120,(0,0,0,0,0,0,0)),((1/1:ℚ),121,(0,0,0,0,0,0,0)),((1/1:ℚ),136,(0,0,0,0,0,0,0)),((1/1:ℚ),137,(0,0,0,0,0,0,0)),((1/1:ℚ),142,(0,0,0,0,0,0,0)),((1/1:ℚ),149,(0,0,0,0,0,0,0))]
def raw944Sample : ℕ→ℕ
  | 1 => 4
  | 5 => 15
  | 7 => 73
  | 11 => 142
  | 13 => 137
  | 17 => 120
  | 19 => 118
  | 23 => 66
  | 25 => 17
  | 29 => 44
  | 31 => 35
  | 35 => 121
  | 37 => 119
  | 41 => 136
  | 43 => 149
  | 47 => 71
  | 49 => 57
  | 53 => 30
  | _ => 0
theorem raw944Point : ∀ a : Fin 54, a.val.Coprime 54 → point (raw944Sample a.val)=((((a.val:ℤ)*(270/54:ℕ))%(270:ℤ):ℤ):ℚ)/(270:ℚ) := by decide +kernel
theorem raw944Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw944Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 54 raw944Sample v := by
  norm_num [eval,monomial,raw944Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw944Sample,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem raw944Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw944Poly m f z=E z := by
  obtain ⟨hE,B,hB⟩ := SmallLevelTaylor.original_ramanujan_entire (by decide : 0<27) (by omega : 0<2*m) hf (by decide : 0<54)
  refine ⟨B,SmallLevelTaylor.ramanujanEntire 27 (2*m) f 54,fun z => (hE z).differentiableAt,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw944Row]
  have hs := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sample_original point (by decide : 0<270) (by decide : 0<54) (by decide : 54∣270) 0 raw944Sample (by simpa only [zero_add,Nat.cast_ofNat,Int.cast_ofNat] using raw944Point) m f z
  rw [show QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 54 raw944Sample (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) z)=SmallLevelTaylor.ramanujanAdditive (2*m) f 54 0 z by simpa using hs]
  exact (hB z hz).symm
#print axioms raw944Row
#print axioms raw944Original

def raw952Poly : Poly := [((1/1:ℚ),0,(0,0,0,0,0,0,0)),((-1/1:ℚ),6,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),7,(0,(-2),0,0,0,0,0)),((1/1:ℚ),11,(0,0,0,0,0,0,0)),((-1/1:ℚ),13,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),16,(0,(-2),0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),22,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,0,0,0,0,0,0)),((-1/1:ℚ),27,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),28,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),33,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),47,(0,(-2),0,0,0,0,0)),((1/1:ℚ),54,(0,0,0,0,0,0,0)),((1/1:ℚ),58,(0,0,0,0,0,0,0)),((-1/1:ℚ),68,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),69,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),75,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),76,(0,(-2),0,0,0,0,0)),((1/1:ℚ),78,(0,0,0,0,0,0,0)),((1/1:ℚ),87,(0,0,0,0,0,0,0)),((1/1:ℚ),100,(0,0,0,0,0,0,0)),((1/1:ℚ),108,(0,0,0,0,0,0,0)),((1/1:ℚ),109,(0,0,0,0,0,0,0)),((1/1:ℚ),114,(0,0,0,0,0,0,0)),((1/1:ℚ),115,(0,0,0,0,0,0,0)),((-1/1:ℚ),124,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),125,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),130,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),131,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),132,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),133,(0,(-2),0,0,0,0,0)),((1/1:ℚ),153,(0,0,0,0,0,0,0)),((1/1:ℚ),155,(0,0,0,0,0,0,0)),((1/1:ℚ),162,(0,0,0,0,0,0,0)),((1/1:ℚ),163,(0,0,0,0,0,0,0)),((-1/1:ℚ),168,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),169,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),170,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),172,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),173,(0,(-2),0,0,0,0,0)),((-1/1:ℚ),175,(0,(-2),0,0,0,0,0)),((1/1:ℚ),199,(0,0,0,0,0,0,0)),((1/1:ℚ),201,(0,0,0,0,0,0,0)),((1/1:ℚ),206,(0,0,0,0,0,0,0)),((1/1:ℚ),208,(0,0,0,0,0,0,0)),((1/1:ℚ),235,(0,0,0,0,0,0,0)),((1/1:ℚ),237,(0,0,0,0,0,0,0))]
def raw952Left : ℕ→ℕ
  | 1 => 78
  | 7 => 11
  | 11 => 206
  | 13 => 18
  | 17 => 153
  | 19 => 162
  | 23 => 22
  | 29 => 108
  | 31 => 114
  | 37 => 163
  | 41 => 208
  | 43 => 24
  | 47 => 54
  | 49 => 199
  | 53 => 58
  | 59 => 109
  | 61 => 115
  | 67 => 237
  | 71 => 155
  | 73 => 100
  | 77 => 235
  | 79 => 201
  | 83 => 0
  | 89 => 87
  | _ => 0
def raw952Right : ℕ→ℕ
  | 1 => 47
  | 7 => 68
  | 11 => 13
  | 13 => 6
  | 17 => 172
  | 19 => 170
  | 23 => 75
  | 29 => 132
  | 31 => 124
  | 37 => 130
  | 41 => 168
  | 43 => 16
  | 47 => 27
  | 49 => 7
  | 53 => 33
  | 59 => 133
  | 61 => 125
  | 67 => 131
  | 71 => 173
  | 73 => 69
  | 77 => 169
  | 79 => 175
  | 83 => 28
  | 89 => 76
  | _ => 0
def raw952Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨952,270,90,1,(-9),raw952Left,raw952Right,0,(-2),0,0⟩
theorem raw952Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw952Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw952Spec]
  decide +kernel
theorem raw952Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw952Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw952Spec x y z w 1 v := by
  norm_num [eval,monomial,raw952Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw952Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw952Left,raw952Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw952Observation : Fin 553 := ⟨281,by decide⟩
def raw952Units : List ℕ := [13, 49, 11, 43, 47, 83, 53, 1, 7, 73, 23, 89, 31, 61, 37, 67, 29, 59, 41, 77, 19, 17, 71, 79]
theorem raw952Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw952Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw952Spec.q raw952Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw952Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 90 raw952Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw952Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw952Units raw952Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=90) v raw952Units raw952Right (by decide +kernel) (by decide +kernel)]
#print axioms raw952Observed
#print axioms raw952Valid
#print axioms raw952Row

def raw985Poly : Poly := [((1/1:ℚ),195,(0,0,0,0,0,0,0)),((-1/1:ℚ),206,((-1),0,0,0,1,0,0)),((1/1:ℚ),227,(0,0,0,0,0,0,0)),((1/1:ℚ),238,((-2),0,0,0,0,0,0))]
def raw985Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨985,270,2,17,![227,195],206,238⟩
theorem raw985Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw985Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw985Spec]
  decide +kernel
theorem raw985Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw985Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw985Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw985Spec]
  norm_num [eval,monomial,raw985Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw985Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw985Valid
#print axioms raw985Row

def raw991Poly : Poly := [((1/1:ℚ),106,((-2),0,0,0,0,0,0)),((1/1:ℚ),166,(0,0,0,0,0,0,0)),((-1/1:ℚ),176,((-1),0,0,0,1,0,0)),((1/1:ℚ),260,(0,0,0,0,0,0,0))]
def raw991Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨991,270,2,23,![260,166],176,106⟩
theorem raw991Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw991Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw991Spec]
  decide +kernel
theorem raw991Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw991Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw991Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw991Spec]
  norm_num [eval,monomial,raw991Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw991Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw991Valid
#print axioms raw991Row

def raw999Poly : Poly := [((1/1:ℚ),164,(0,0,0,0,0,0,0)),((1/1:ℚ),180,(0,0,0,0,0,0,0)),((-1/1:ℚ),193,((-1),0,0,0,1,0,0)),((1/1:ℚ),208,((-2),0,0,0,0,0,0))]
def raw999Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨999,270,2,31,![180,164],193,208⟩
theorem raw999Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw999Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw999Spec]
  decide +kernel
theorem raw999Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw999Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw999Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw999Spec]
  norm_num [eval,monomial,raw999Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw999Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw999Valid
#print axioms raw999Row

def raw1005Poly : Poly := [((1/1:ℚ),199,((-2),0,0,0,0,0,0)),((1/1:ℚ),222,(0,0,0,0,0,0,0)),((-1/1:ℚ),233,((-1),0,0,0,1,0,0)),((1/1:ℚ),248,(0,0,0,0,0,0,0))]
def raw1005Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1005,270,2,37,![222,248],233,199⟩
theorem raw1005Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1005Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1005Spec]
  decide +kernel
theorem raw1005Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1005Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1005Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1005Spec]
  norm_num [eval,monomial,raw1005Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1005Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1005Valid
#print axioms raw1005Row

def raw1012Poly : Poly := [((1/1:ℚ),105,(0,0,0,0,0,0,0)),((-1/1:ℚ),108,((-1),0,0,0,1,0,0)),((1/1:ℚ),117,((-2),0,0,0,0,0,0)),((1/1:ℚ),178,(0,0,0,0,0,0,0))]
def raw1012Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1012,270,2,44,![178,105],108,117⟩
theorem raw1012Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1012Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1012Spec]
  decide +kernel
theorem raw1012Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1012Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1012Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1012Spec]
  norm_num [eval,monomial,raw1012Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1012Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1012Valid
#print axioms raw1012Row

def raw1014Poly : Poly := [((1/1:ℚ),103,(0,0,0,0,0,0,0)),((-1/1:ℚ),106,((-1),0,0,0,1,0,0)),((1/1:ℚ),115,((-2),0,0,0,0,0,0)),((1/1:ℚ),176,(0,0,0,0,0,0,0))]
def raw1014Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1014,270,2,46,![176,103],106,115⟩
theorem raw1014Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1014Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1014Spec]
  decide +kernel
theorem raw1014Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1014Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1014Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1014Spec]
  norm_num [eval,monomial,raw1014Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1014Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1014Valid
#print axioms raw1014Row

def raw1015Poly : Poly := [((1/1:ℚ),107,(0,0,0,0,0,0,0)),((-1/1:ℚ),114,((-1),0,0,0,1,0,0)),((1/1:ℚ),221,((-2),0,0,0,0,0,0)),((1/1:ℚ),261,(0,0,0,0,0,0,0))]
def raw1015Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1015,270,2,47,![261,107],114,221⟩
theorem raw1015Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1015Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1015Spec]
  decide +kernel
theorem raw1015Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1015Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1015Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1015Spec]
  norm_num [eval,monomial,raw1015Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1015Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1015Valid
#print axioms raw1015Row

def raw1020Poly : Poly := [((1/1:ℚ),153,(0,0,0,0,0,0,0)),((-1/1:ℚ),165,((-1),0,0,0,1,0,0)),((1/1:ℚ),200,((-2),0,0,0,0,0,0)),((1/1:ℚ),256,(0,0,0,0,0,0,0))]
def raw1020Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1020,270,2,52,![153,256],165,200⟩
theorem raw1020Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1020Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1020Spec]
  decide +kernel
theorem raw1020Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1020Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1020Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1020Spec]
  norm_num [eval,monomial,raw1020Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1020Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1020Valid
#print axioms raw1020Row

def raw1021Poly : Poly := [((1/1:ℚ),146,(0,0,0,0,0,0,0)),((-1/1:ℚ),154,((-1),0,0,0,1,0,0)),((1/1:ℚ),167,((-2),0,0,0,0,0,0)),((1/1:ℚ),221,(0,0,0,0,0,0,0))]
def raw1021Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1021,270,2,53,![146,221],154,167⟩
theorem raw1021Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1021Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1021Spec]
  decide +kernel
theorem raw1021Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1021Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1021Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1021Spec]
  norm_num [eval,monomial,raw1021Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1021Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1021Valid
#print axioms raw1021Row

def raw1024Poly : Poly := [((1/1:ℚ),150,(0,0,0,0,0,0,0)),((-1/1:ℚ),163,((-1),0,0,0,1,0,0)),((1/1:ℚ),179,((-2),0,0,0,0,0,0)),((1/1:ℚ),242,(0,0,0,0,0,0,0))]
def raw1024Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1024,270,2,56,![150,242],163,179⟩
theorem raw1024Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1024Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1024Spec]
  decide +kernel
theorem raw1024Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1024Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1024Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1024Spec]
  norm_num [eval,monomial,raw1024Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1024Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1024Valid
#print axioms raw1024Row

def raw1026Poly : Poly := [((1/1:ℚ),162,(0,0,0,0,0,0,0)),((-1/1:ℚ),212,((-1),0,0,0,1,0,0)),((1/1:ℚ),235,((-2),0,0,0,0,0,0)),((1/1:ℚ),257,(0,0,0,0,0,0,0))]
def raw1026Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1026,270,2,58,![162,257],212,235⟩
theorem raw1026Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1026Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1026Spec]
  decide +kernel
theorem raw1026Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1026Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1026Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1026Spec]
  norm_num [eval,monomial,raw1026Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1026Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1026Valid
#print axioms raw1026Row

def raw1029Poly : Poly := [((1/1:ℚ),181,(0,0,0,0,0,0,0)),((-1/1:ℚ),194,((-1),0,0,0,1,0,0)),((1/1:ℚ),210,((-2),0,0,0,0,0,0)),((1/1:ℚ),234,(0,0,0,0,0,0,0))]
def raw1029Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1029,270,2,61,![181,234],194,210⟩
theorem raw1029Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1029Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1029Spec]
  decide +kernel
theorem raw1029Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1029Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1029Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1029Spec]
  norm_num [eval,monomial,raw1029Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1029Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1029Valid
#print axioms raw1029Row

def raw1044Poly : Poly := [((1/1:ℚ),184,(0,0,0,0,0,0,0)),((-1/1:ℚ),195,((-1),0,0,0,1,0,0)),((1/1:ℚ),206,((-2),0,0,0,0,0,0)),((1/1:ℚ),236,(0,0,0,0,0,0,0))]
def raw1044Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1044,270,2,76,![236,184],195,206⟩
theorem raw1044Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1044Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1044Spec]
  decide +kernel
theorem raw1044Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1044Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1044Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1044Spec]
  norm_num [eval,monomial,raw1044Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1044Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1044Valid
#print axioms raw1044Row

def raw1045Poly : Poly := [((1/1:ℚ),167,(0,0,0,0,0,0,0)),((-1/1:ℚ),209,((-1),0,0,0,1,0,0)),((1/1:ℚ),232,((-2),0,0,0,0,0,0)),((1/1:ℚ),262,(0,0,0,0,0,0,0))]
def raw1045Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1045,270,2,77,![262,167],209,232⟩
theorem raw1045Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1045Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1045Spec]
  decide +kernel
theorem raw1045Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1045Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1045Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1045Spec]
  norm_num [eval,monomial,raw1045Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1045Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1045Valid
#print axioms raw1045Row

def raw1047Poly : Poly := [((1/1:ℚ),155,(0,0,0,0,0,0,0)),((-1/1:ℚ),166,((-1),0,0,0,1,0,0)),((1/1:ℚ),176,((-2),0,0,0,0,0,0)),((1/1:ℚ),245,(0,0,0,0,0,0,0))]
def raw1047Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1047,270,2,79,![245,155],166,176⟩
theorem raw1047Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1047Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1047Spec]
  decide +kernel
theorem raw1047Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1047Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1047Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1047Spec]
  norm_num [eval,monomial,raw1047Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1047Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1047Valid
#print axioms raw1047Row

def raw1051Poly : Poly := [((1/1:ℚ),152,(0,0,0,0,0,0,0)),((-1/1:ℚ),164,((-1),0,0,0,1,0,0)),((1/1:ℚ),193,((-2),0,0,0,0,0,0)),((1/1:ℚ),263,(0,0,0,0,0,0,0))]
def raw1051Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1051,270,2,83,![263,152],164,193⟩
theorem raw1051Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1051Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1051Spec]
  decide +kernel
theorem raw1051Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1051Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1051Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1051Spec]
  norm_num [eval,monomial,raw1051Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1051Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1051Valid
#print axioms raw1051Row

def raw1054Poly : Poly := [((1/1:ℚ),116,(0,0,0,0,0,0,0)),((1/1:ℚ),233,((-2),0,0,0,0,0,0)),((1/1:ℚ),243,(0,0,0,0,0,0,0)),((-1/1:ℚ),248,((-1),0,0,0,1,0,0))]
def raw1054Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1054,270,2,86,![116,243],248,233⟩
theorem raw1054Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1054Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1054Spec]
  decide +kernel
theorem raw1054Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1054Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1054Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1054Spec]
  norm_num [eval,monomial,raw1054Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1054Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1054Valid
#print axioms raw1054Row

def raw1062Poly : Poly := [((1/1:ℚ),114,(0,0,0,0,0,0,0)),((1/1:ℚ),154,((-2),0,0,0,0,0,0)),((-1/1:ℚ),221,((-1),0,0,0,1,0,0)),((1/1:ℚ),247,(0,0,0,0,0,0,0))]
def raw1062Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1062,270,2,94,![114,247],221,154⟩
theorem raw1062Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1062Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1062Spec]
  decide +kernel
theorem raw1062Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1062Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1062Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1062Spec]
  norm_num [eval,monomial,raw1062Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1062Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1062Valid
#print axioms raw1062Row

def raw1065Poly : Poly := [((1/1:ℚ),198,((-2),0,0,0,0,0,0)),((1/1:ℚ),235,(0,0,0,0,0,0,0)),((-1/1:ℚ),239,((-1),0,0,0,1,0,0)),((1/1:ℚ),253,(0,0,0,0,0,0,0))]
def raw1065Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1065,270,2,97,![253,235],239,198⟩
theorem raw1065Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1065Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1065Spec]
  decide +kernel
theorem raw1065Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1065Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1065Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1065Spec]
  norm_num [eval,monomial,raw1065Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1065Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1065Valid
#print axioms raw1065Row

def raw1069Poly : Poly := [((1/1:ℚ),29,((-2),0,0,0,0,0,0)),((1/1:ℚ),215,(0,0,0,0,0,0,0)),((-1/1:ℚ),237,((-1),0,0,0,1,0,0)),((1/1:ℚ),241,(0,0,0,0,0,0,0))]
def raw1069Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1069,270,2,101,![241,215],237,29⟩
theorem raw1069Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1069Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1069Spec]
  decide +kernel
theorem raw1069Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1069Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1069Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1069Spec]
  norm_num [eval,monomial,raw1069Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1069Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1069Valid
#print axioms raw1069Row

def raw1072Poly : Poly := [((1/1:ℚ),165,(0,0,0,0,0,0,0)),((1/1:ℚ),191,(0,0,0,0,0,0,0)),((-1/1:ℚ),200,((-1),0,0,0,1,0,0)),((1/1:ℚ),213,((-2),0,0,0,0,0,0))]
def raw1072Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1072,270,2,104,![165,191],200,213⟩
theorem raw1072Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1072Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1072Spec]
  decide +kernel
theorem raw1072Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1072Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1072Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1072Spec]
  norm_num [eval,monomial,raw1072Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1072Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1072Valid
#print axioms raw1072Row

def raw1080Poly : Poly := [((1/1:ℚ),109,((-2),0,0,0,0,0,0)),((1/1:ℚ),163,(0,0,0,0,0,0,0)),((-1/1:ℚ),179,((-1),0,0,0,1,0,0)),((1/1:ℚ),259,(0,0,0,0,0,0,0))]
def raw1080Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1080,270,2,112,![163,259],179,109⟩
theorem raw1080Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1080Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1080Spec]
  decide +kernel
theorem raw1080Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1080Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1080Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1080Spec]
  norm_num [eval,monomial,raw1080Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1080Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1080Valid
#print axioms raw1080Row

def raw1083Poly : Poly := [((1/1:ℚ),0,(0,0,0,0,0,0,0)),((1/1:ℚ),26,((-2),0,0,0,0,0,0)),((-1/1:ℚ),39,((-1),0,0,0,1,0,0)),((1/1:ℚ),66,(0,0,0,0,0,0,0))]
def raw1083Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1083,270,2,115,![66,0],39,26⟩
theorem raw1083Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1083Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1083Spec]
  decide +kernel
theorem raw1083Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1083Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1083Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1083Spec]
  norm_num [eval,monomial,raw1083Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1083Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1083Valid
#print axioms raw1083Row

def raw1084Poly : Poly := [((1/1:ℚ),63,(0,0,0,0,0,0,0)),((1/1:ℚ),212,(0,0,0,0,0,0,0)),((-1/1:ℚ),235,((-1),0,0,0,1,0,0)),((1/1:ℚ),239,((-2),0,0,0,0,0,0))]
def raw1084Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1084,270,2,116,![212,63],235,239⟩
theorem raw1084Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1084Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1084Spec]
  decide +kernel
theorem raw1084Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1084Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1084Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1084Spec]
  norm_num [eval,monomial,raw1084Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1084Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1084Valid
#print axioms raw1084Row

def raw1086Poly : Poly := [((1/1:ℚ),198,(0,0,0,0,0,0,0)),((-1/1:ℚ),215,((-1),0,0,0,1,0,0)),((1/1:ℚ),226,(0,0,0,0,0,0,0)),((1/1:ℚ),237,((-2),0,0,0,0,0,0))]
def raw1086Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1086,270,2,118,![198,226],215,237⟩
theorem raw1086Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1086Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1086Spec]
  decide +kernel
theorem raw1086Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1086Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1086Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1086Spec]
  norm_num [eval,monomial,raw1086Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1086Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1086Valid
#print axioms raw1086Row

def raw1090Poly : Poly := [((1/1:ℚ),152,((-2),0,0,0,0,0,0)),((1/1:ℚ),194,(0,0,0,0,0,0,0)),((-1/1:ℚ),210,((-1),0,0,0,1,0,0)),((1/1:ℚ),269,(0,0,0,0,0,0,0))]
def raw1090Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1090,270,2,122,![194,269],210,152⟩
theorem raw1090Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1090Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1090Spec]
  decide +kernel
theorem raw1090Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1090Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1090Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1090Spec]
  norm_num [eval,monomial,raw1090Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1090Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1090Valid
#print axioms raw1090Row

def raw1126Poly : Poly := [((1/1:ℚ),260,(0,0,0,0,0,0,0)),((1/1:ℚ),264,(0,0,0,0,0,0,0)),((1/1:ℚ),267,(0,0,0,0,0,0,0))]
def raw1126Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1126,270,3,23,![260,264,267],217,139⟩
theorem raw1126Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1126Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1126Spec]
  decide +kernel
theorem raw1126Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1126Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1126Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1126Spec]
  norm_num [eval,monomial,raw1126Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1126Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1126Valid
#print axioms raw1126Row

def raw1132Poly : Poly := [((1/1:ℚ),186,(0,0,0,0,0,0,0)),((1/1:ℚ),188,(0,0,0,0,0,0,0)),((1/1:ℚ),190,(0,0,0,0,0,0,0))]
def raw1132Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1132,270,3,29,![186,188,190],112,79⟩
theorem raw1132Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1132Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1132Spec]
  decide +kernel
theorem raw1132Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1132Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1132Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1132Spec]
  norm_num [eval,monomial,raw1132Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1132Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1132Valid
#print axioms raw1132Row

def raw1164Poly : Poly := [((1/1:ℚ),181,(0,0,0,0,0,0,0)),((1/1:ℚ),183,(0,0,0,0,0,0,0)),((1/1:ℚ),185,(0,0,0,0,0,0,0))]
def raw1164Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1164,270,3,61,![181,183,185],111,51⟩
theorem raw1164Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1164Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1164Spec]
  decide +kernel
theorem raw1164Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1164Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1164Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1164Spec]
  norm_num [eval,monomial,raw1164Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1164Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1164Valid
#print axioms raw1164Row

def raw1198Poly : Poly := [((1/1:ℚ),4,(0,0,0,0,0,0,0)),((-1/1:ℚ),15,(0,0,(-1),0,0,1,0)),((1/1:ℚ),17,(0,0,(-2),0,0,0,0)),((1/1:ℚ),187,(0,0,0,0,0,0,0)),((1/1:ℚ),243,(0,0,0,0,0,0,0)),((1/1:ℚ),264,(0,0,0,0,0,0,0)),((1/1:ℚ),265,(0,0,0,0,0,0,0))]
def raw1198Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1198,270,5,5,![4,187,264,265,243],15,17⟩
theorem raw1198Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1198Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1198Spec]
  decide +kernel
theorem raw1198Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1198Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1198Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1198Spec]
  norm_num [eval,monomial,raw1198Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1198Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1198Valid
#print axioms raw1198Row

def raw1206Poly : Poly := [((1/1:ℚ),121,(0,0,0,0,0,0,0)),((-1/1:ℚ),137,(0,0,(-1),0,0,1,0)),((1/1:ℚ),142,(0,0,(-2),0,0,0,0)),((1/1:ℚ),182,(0,0,0,0,0,0,0)),((1/1:ℚ),247,(0,0,0,0,0,0,0)),((1/1:ℚ),250,(0,0,0,0,0,0,0)),((1/1:ℚ),252,(0,0,0,0,0,0,0))]
def raw1206Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1206,270,5,13,![250,252,182,121,247],137,142⟩
theorem raw1206Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1206Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1206Spec]
  decide +kernel
theorem raw1206Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1206Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1206Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1206Spec]
  norm_num [eval,monomial,raw1206Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1206Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1206Valid
#print axioms raw1206Row

def raw1212Poly : Poly := [((1/1:ℚ),40,(0,0,0,0,0,0,0)),((1/1:ℚ),71,(0,0,0,0,0,0,0)),((1/1:ℚ),103,(0,0,0,0,0,0,0)),((-1/1:ℚ),118,(0,0,(-1),0,0,1,0)),((1/1:ℚ),136,(0,0,(-2),0,0,0,0)),((1/1:ℚ),223,(0,0,0,0,0,0,0)),((1/1:ℚ),224,(0,0,0,0,0,0,0))]
def raw1212Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1212,270,5,19,![40,223,224,103,71],118,136⟩
theorem raw1212Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1212Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1212Spec]
  decide +kernel
theorem raw1212Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1212Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1212Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1212Spec]
  norm_num [eval,monomial,raw1212Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1212Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1212Valid
#print axioms raw1212Row

def raw1240Poly : Poly := [((1/1:ℚ),35,(0,0,0,0,0,0,0)),((1/1:ℚ),45,(0,0,0,0,0,0,0)),((-1/1:ℚ),71,(0,0,(-1),0,0,1,0)),((1/1:ℚ),118,(0,0,(-2),0,0,0,0)),((1/1:ℚ),190,(0,0,0,0,0,0,0)),((1/1:ℚ),241,(0,0,0,0,0,0,0)),((1/1:ℚ),261,(0,0,0,0,0,0,0))]
def raw1240Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨1240,270,5,47,![261,241,35,190,45],71,118⟩
theorem raw1240Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw1240Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw1240Spec]
  decide +kernel
theorem raw1240Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1240Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw1240Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1240Spec]
  norm_num [eval,monomial,raw1240Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw1240Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw1240Valid
#print axioms raw1240Row

def raw1361Poly : Poly := [((-1/1:ℚ),20,(2,0,0,(-2),0,0,0)),((1/1:ℚ),302,(0,0,0,0,0,0,0))]
def raw1361Spec : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec := ⟨1361,sourceWord77,302,20,(-1),2,0,0,(-2)⟩
theorem raw1361Valid : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid point raw1361Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Valid,raw1361Spec]
  decide +kernel
theorem raw1361Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1361Poly=QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading raw1361Spec x y z w v := by
  norm_num [eval,monomial,raw1361Poly,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,raw1361Spec] <;> ring
def raw1361Observation : Fin 553 := ⟨9,by decide⟩
theorem raw1361Observed (v : ℕ→ℂ) : QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1361Observation)=v raw1361Spec.right := by
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1361Observation=[(1,raw1361Spec.right)] := by decide +kernel
  rw [h]
  simp
#print axioms raw1361Observed
#print axioms raw1361Valid
#print axioms raw1361Row

def raw1986Poly : Poly := [((1/1:ℚ),3,(0,0,0,0,0,0,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((-1/1:ℚ),360,((-2),1,0,2,0,0,0)),((-1/1:ℚ),361,((-2),1,0,2,0,0,0))]
def raw1986Left : ℕ→ℕ
  | 1 => 20
  | 2 => 3
  | _ => 0
def raw1986Right : ℕ→ℕ
  | 1 => 360
  | 2 => 361
  | _ => 0
def raw1986Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1986,378,3,(-441),12,raw1986Left,raw1986Right,(-2),1,0,2⟩
theorem raw1986Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1986Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1986Spec]
  decide +kernel
theorem raw1986Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1986Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1986Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1986Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1986Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1986Left,raw1986Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1986Observation : Fin 553 := ⟨393,by decide⟩
def raw1986Units : List ℕ := [1, 2]
theorem raw1986Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1986Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1986Spec.q raw1986Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1986Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw1986Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1986Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1986Units raw1986Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw1986Units raw1986Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1986Observed
#print axioms raw1986Valid
#print axioms raw1986Row

def raw1991Poly : Poly := [((1/1:ℚ),2,(0,0,0,0,0,0,0)),((1/1:ℚ),37,(0,0,0,0,0,0,0)),((-1/1:ℚ),354,(0,1,0,2,0,0,0)),((-1/1:ℚ),355,(0,1,0,2,0,0,0))]
def raw1991Left : ℕ→ℕ
  | 1 => 37
  | 2 => 2
  | _ => 0
def raw1991Right : ℕ→ℕ
  | 1 => 354
  | 2 => 355
  | _ => 0
def raw1991Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1991,378,3,882,(-6),raw1991Left,raw1991Right,0,1,0,2⟩
theorem raw1991Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1991Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1991Spec]
  decide +kernel
theorem raw1991Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1991Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1991Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1991Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1991Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1991Left,raw1991Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1991Observation : Fin 553 := ⟨396,by decide⟩
def raw1991Units : List ℕ := [1, 2]
theorem raw1991Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1991Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1991Spec.q raw1991Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1991Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw1991Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1991Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1991Units raw1991Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw1991Units raw1991Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1991Observed
#print axioms raw1991Valid
#print axioms raw1991Row

def raw1992Poly : Poly := [((1/1:ℚ),2,(0,0,0,0,0,0,0)),((1/1:ℚ),50,(0,0,0,0,0,0,0)),((-1/1:ℚ),352,(0,1,0,2,0,0,0)),((-1/1:ℚ),353,(0,1,0,2,0,0,0))]
def raw1992Left : ℕ→ℕ
  | 1 => 2
  | 2 => 50
  | _ => 0
def raw1992Right : ℕ→ℕ
  | 1 => 352
  | 2 => 353
  | _ => 0
def raw1992Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨1992,378,3,(-882),6,raw1992Left,raw1992Right,0,1,0,2⟩
theorem raw1992Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw1992Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw1992Spec]
  decide +kernel
theorem raw1992Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw1992Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw1992Spec x y z w 1 v := by
  norm_num [eval,monomial,raw1992Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw1992Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw1992Left,raw1992Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw1992Observation : Fin 553 := ⟨397,by decide⟩
def raw1992Units : List ℕ := [1, 2]
theorem raw1992Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1992Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw1992Spec.q raw1992Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1992Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 3 raw1992Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw1992Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw1992Units raw1992Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=3) v raw1992Units raw1992Right (by decide +kernel) (by decide +kernel)]
#print axioms raw1992Observed
#print axioms raw1992Valid
#print axioms raw1992Row

def raw2023Poly : Poly := [((1/1:ℚ),2,(0,0,0,0,0,0,0)),((1/1:ℚ),37,(0,0,0,0,0,0,0)),((-1/1:ℚ),378,(0,1,0,2,0,0,0)),((-1/1:ℚ),379,(0,1,0,2,0,0,0))]
def raw2023Left : ℕ→ℕ
  | 1 => 2
  | 5 => 37
  | _ => 0
def raw2023Right : ℕ→ℕ
  | 1 => 378
  | 5 => 379
  | _ => 0
def raw2023Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2023,378,6,(-441),3,raw2023Left,raw2023Right,0,1,0,2⟩
theorem raw2023Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2023Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2023Spec]
  decide +kernel
theorem raw2023Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2023Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2023Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2023Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2023Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2023Left,raw2023Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2023Observation : Fin 553 := ⟨411,by decide⟩
def raw2023Units : List ℕ := [1, 5]
theorem raw2023Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2023Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2023Spec.q raw2023Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2023Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 6 raw2023Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2023Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2023Units raw2023Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=6) v raw2023Units raw2023Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2023Observed
#print axioms raw2023Valid
#print axioms raw2023Row

def raw2026Poly : QuantitativeArithmeticSevenLaurentRows.Poly := [((1/1:ℚ),330,(0,0,0,0,0,0,0)),((1/1:ℚ),331,(0,0,0,0,0,0,0)),((1/1:ℚ),332,(0,0,0,0,0,0,0)),((1/1:ℚ),333,(0,0,0,0,0,0,0)),((1/1:ℚ),334,(0,0,0,0,0,0,0)),((1/1:ℚ),335,(0,0,0,0,0,0,0))]
def raw2026Sample : ℕ→ℕ
  | 1 => 332
  | 2 => 331
  | 3 => 335
  | 4 => 334
  | 5 => 330
  | 6 => 333
  | _ => 0
theorem raw2026Point : ∀ a : Fin 7, a.val.Coprime 7 → point (raw2026Sample a.val)=((((a.val:ℤ)*(378/7:ℕ))%(378:ℤ):ℤ):ℚ)/(378:ℚ) := by decide +kernel
theorem raw2026Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2026Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 7 raw2026Sample v := by
  norm_num [eval,monomial,raw2026Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2026Sample,Finset.sum_filter,Finset.sum_range_succ] <;> ring
theorem raw2026Original (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (B : ℝ) (E : ℂ→ℂ), Differentiable ℂ E ∧
      ∀ z : ℂ, B<z.re → QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval raw2026Poly m f z=E z := by
  obtain ⟨hE,B,hB⟩ := SmallLevelTaylor.original_ramanujan_entire (by decide : 0<27) (by omega : 0<2*m) hf (by decide : 0<7)
  refine ⟨B,SmallLevelTaylor.ramanujanEntire 27 (2*m) f 7,fun z => (hE z).differentiableAt,?_⟩
  intro z hz
  unfold QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.physicalEval
  rw [raw2026Row]
  have hs := QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sample_original point (by decide : 0<378) (by decide : 0<7) (by decide : 7∣378) 0 raw2026Sample (by simpa only [zero_add,Nat.cast_ofNat,Int.cast_ofNat] using raw2026Point) m f z
  rw [show QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 7 raw2026Sample (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) z)=SmallLevelTaylor.ramanujanAdditive (2*m) f 7 0 z by simpa using hs]
  exact (hB z hz).symm
#print axioms raw2026Row
#print axioms raw2026Original

def raw2087Poly : Poly := [((1/1:ℚ),1,(0,0,0,0,0,0,0)),((1/1:ℚ),8,(0,0,0,0,0,0,0)),((1/1:ℚ),31,(0,0,0,0,0,0,0)),((1/1:ℚ),39,(0,0,0,0,0,0,0)),((1/1:ℚ),46,(0,0,0,0,0,0,0)),((1/1:ℚ),98,(0,0,0,0,0,0,0)),((-1/1:ℚ),283,(0,(-2),0,2,0,0,0)),((-1/1:ℚ),298,(0,(-2),0,2,0,0,0)),((-1/1:ℚ),380,(0,(-2),0,2,0,0,0)),((-1/1:ℚ),381,(0,(-2),0,2,0,0,0)),((-1/1:ℚ),428,(0,(-2),0,2,0,0,0)),((-1/1:ℚ),438,(0,(-2),0,2,0,0,0))]
def raw2087Left : ℕ→ℕ
  | 1 => 39
  | 2 => 1
  | 4 => 98
  | 5 => 8
  | 7 => 31
  | 8 => 46
  | _ => 0
def raw2087Right : ℕ→ℕ
  | 1 => 380
  | 2 => 428
  | 4 => 283
  | 5 => 438
  | 7 => 381
  | 8 => 298
  | _ => 0
def raw2087Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2087,378,9,(-98),18,raw2087Left,raw2087Right,0,(-2),0,2⟩
theorem raw2087Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2087Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2087Spec]
  decide +kernel
theorem raw2087Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2087Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2087Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2087Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2087Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2087Left,raw2087Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2087Observation : Fin 553 := ⟨443,by decide⟩
def raw2087Units : List ℕ := [4, 8, 1, 7, 2, 5]
theorem raw2087Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2087Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2087Spec.q raw2087Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2087Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 9 raw2087Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2087Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2087Units raw2087Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=9) v raw2087Units raw2087Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2087Observed
#print axioms raw2087Valid
#print axioms raw2087Row

def raw2090Poly : Poly := [((1/1:ℚ),3,(0,0,0,0,0,0,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0)),((1/1:ℚ),97,(0,0,0,0,0,0,0)),((-1/1:ℚ),276,((-2),0,0,2,0,0,0)),((-1/1:ℚ),293,((-2),0,0,2,0,0,0)),((-1/1:ℚ),333,((-2),0,0,2,0,0,0)),((-1/1:ℚ),373,((-2),0,0,2,0,0,0)),((-1/1:ℚ),429,((-2),0,0,2,0,0,0)),((-1/1:ℚ),439,((-2),0,0,2,0,0,0))]
def raw2090Left : ℕ→ℕ
  | 1 => 3
  | 2 => 60
  | 4 => 55
  | 5 => 42
  | 7 => 20
  | 8 => 97
  | _ => 0
def raw2090Right : ℕ→ℕ
  | 1 => 276
  | 2 => 373
  | 4 => 429
  | 5 => 293
  | 7 => 439
  | 8 => 333
  | _ => 0
def raw2090Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2090,378,9,147,(-12),raw2090Left,raw2090Right,(-2),0,0,2⟩
theorem raw2090Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2090Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2090Spec]
  decide +kernel
theorem raw2090Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2090Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2090Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2090Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2090Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2090Left,raw2090Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2090Observation : Fin 553 := ⟨444,by decide⟩
def raw2090Units : List ℕ := [1, 5, 8, 2, 4, 7]
theorem raw2090Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2090Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2090Spec.q raw2090Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2090Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 9 raw2090Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2090Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2090Units raw2090Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=9) v raw2090Units raw2090Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2090Observed
#print axioms raw2090Valid
#print axioms raw2090Row

def raw2109Poly : Poly := [((-1/1:ℚ),50,(0,(-1),0,0,0,0,0)),((1/1:ℚ),75,(0,0,0,0,0,0,0)),((1/1:ℚ),276,(0,0,0,0,0,0,0)),((1/1:ℚ),298,(0,0,0,0,0,0,0)),((-1/1:ℚ),301,(0,(-1),0,0,0,0,0)),((-1/1:ℚ),329,(0,(-1),0,0,0,0,0)),((1/1:ℚ),355,(0,0,0,0,0,0,0)),((1/1:ℚ),360,(0,0,0,0,0,0,0)),((-1/1:ℚ),365,(0,(-1),0,0,0,0,0)),((-1/1:ℚ),370,(0,(-1),0,0,0,0,0)),((-1/1:ℚ),373,(0,(-1),0,0,0,0,0)),((1/1:ℚ),476,(0,0,0,0,0,0,0))]
def raw2109Left : ℕ→ℕ
  | 1 => 276
  | 3 => 75
  | 5 => 360
  | 9 => 355
  | 11 => 476
  | 13 => 298
  | _ => 0
def raw2109Right : ℕ→ℕ
  | 1 => 301
  | 3 => 373
  | 5 => 50
  | 9 => 365
  | 11 => 370
  | 13 => 329
  | _ => 0
def raw2109Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2109,378,14,3,(-9),raw2109Left,raw2109Right,0,(-1),0,0⟩
theorem raw2109Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2109Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2109Spec]
  decide +kernel
theorem raw2109Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2109Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2109Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2109Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2109Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2109Left,raw2109Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2109Observation : Fin 553 := ⟨460,by decide⟩
def raw2109Units : List ℕ := [5, 1, 13, 9, 11, 3]
theorem raw2109Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2109Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2109Spec.q raw2109Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2109Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 14 raw2109Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2109Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2109Units raw2109Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=14) v raw2109Units raw2109Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2109Observed
#print axioms raw2109Valid
#print axioms raw2109Row

def raw2136Poly : Poly := [((1/1:ℚ),15,(0,0,0,0,0,0,0)),((-1/1:ℚ),37,((-2),(-3),0,0,0,0,0)),((-1/1:ℚ),50,((-2),(-3),0,0,0,0,0)),((1/1:ℚ),136,(0,0,0,0,0,0,0)),((-1/1:ℚ),279,((-2),(-3),0,0,0,0,0)),((1/1:ℚ),292,(0,0,0,0,0,0,0)),((-1/1:ℚ),293,((-2),(-3),0,0,0,0,0)),((-1/1:ℚ),301,((-2),(-3),0,0,0,0,0)),((-1/1:ℚ),328,((-2),(-3),0,0,0,0,0)),((-1/1:ℚ),329,((-2),(-3),0,0,0,0,0)),((-1/1:ℚ),364,((-2),(-3),0,0,0,0,0)),((-1/1:ℚ),370,((-2),(-3),0,0,0,0,0)),((-1/1:ℚ),371,((-2),(-3),0,0,0,0,0)),((-1/1:ℚ),372,((-2),(-3),0,0,0,0,0)),((-1/1:ℚ),373,((-2),(-3),0,0,0,0,0)),((1/1:ℚ),507,(0,0,0,0,0,0,0)),((1/1:ℚ),508,(0,0,0,0,0,0,0)),((1/1:ℚ),509,(0,0,0,0,0,0,0)),((1/1:ℚ),510,(0,0,0,0,0,0,0)),((1/1:ℚ),511,(0,0,0,0,0,0,0)),((1/1:ℚ),512,(0,0,0,0,0,0,0)),((1/1:ℚ),513,(0,0,0,0,0,0,0)),((1/1:ℚ),514,(0,0,0,0,0,0,0)),((1/1:ℚ),515,(0,0,0,0,0,0,0))]
def raw2136Left : ℕ→ℕ
  | 1 => 507
  | 2 => 15
  | 4 => 508
  | 5 => 509
  | 8 => 510
  | 10 => 511
  | 11 => 292
  | 13 => 512
  | 16 => 136
  | 17 => 513
  | 19 => 514
  | 20 => 515
  | _ => 0
def raw2136Right : ℕ→ℕ
  | 1 => 50
  | 2 => 364
  | 4 => 279
  | 5 => 293
  | 8 => 37
  | 10 => 370
  | 11 => 372
  | 13 => 329
  | 16 => 301
  | 17 => 328
  | 19 => 373
  | 20 => 371
  | _ => 0
def raw2136Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2136,378,21,(-1),108,raw2136Left,raw2136Right,(-2),(-3),0,0⟩
theorem raw2136Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2136Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2136Spec]
  decide +kernel
theorem raw2136Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2136Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2136Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2136Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2136Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2136Left,raw2136Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2136Observation : Fin 553 := ⟨473,by decide⟩
def raw2136Units : List ℕ := [8, 1, 4, 5, 16, 17, 13, 2, 10, 20, 11, 19]
theorem raw2136Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2136Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2136Spec.q raw2136Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2136Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 21 raw2136Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2136Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2136Units raw2136Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=21) v raw2136Units raw2136Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2136Observed
#print axioms raw2136Valid
#print axioms raw2136Row

def raw2140Poly : Poly := [((-1/1:ℚ),2,((-2),(-1),0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,((-2),(-1),0,0,0,0,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0)),((1/1:ℚ),275,(0,0,0,0,0,0,0)),((-1/1:ℚ),279,((-2),(-1),0,0,0,0,0)),((1/1:ℚ),299,(0,0,0,0,0,0,0)),((-1/1:ℚ),301,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),329,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),330,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),331,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),332,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),333,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),334,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),365,((-2),(-1),0,0,0,0,0)),((-1/1:ℚ),373,((-2),(-1),0,0,0,0,0)),((1/1:ℚ),462,(0,0,0,0,0,0,0)),((1/1:ℚ),463,(0,0,0,0,0,0,0)),((1/1:ℚ),479,(0,0,0,0,0,0,0)),((1/1:ℚ),480,(0,0,0,0,0,0,0)),((1/1:ℚ),482,(0,0,0,0,0,0,0)),((1/1:ℚ),485,(0,0,0,0,0,0,0)),((1/1:ℚ),526,(0,0,0,0,0,0,0)),((1/1:ℚ),527,(0,0,0,0,0,0,0))]
def raw2140Left : ℕ→ℕ
  | 1 => 299
  | 2 => 482
  | 4 => 526
  | 5 => 462
  | 8 => 527
  | 10 => 479
  | 11 => 275
  | 13 => 60
  | 16 => 485
  | 17 => 480
  | 19 => 463
  | 20 => 42
  | _ => 0
def raw2140Right : ℕ→ℕ
  | 1 => 332
  | 2 => 373
  | 4 => 331
  | 5 => 50
  | 8 => 279
  | 10 => 334
  | 11 => 365
  | 13 => 330
  | 16 => 333
  | 17 => 329
  | 19 => 2
  | 20 => 301
  | _ => 0
def raw2140Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2140,378,21,(-3),36,raw2140Left,raw2140Right,(-2),(-1),0,0⟩
theorem raw2140Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2140Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2140Spec]
  decide +kernel
theorem raw2140Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2140Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2140Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2140Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2140Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2140Left,raw2140Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2140Observation : Fin 553 := ⟨477,by decide⟩
def raw2140Units : List ℕ := [19, 5, 8, 20, 17, 13, 4, 1, 16, 10, 11, 2]
theorem raw2140Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2140Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2140Spec.q raw2140Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2140Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 21 raw2140Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2140Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2140Units raw2140Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=21) v raw2140Units raw2140Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2140Observed
#print axioms raw2140Valid
#print axioms raw2140Row

def raw2199Poly : Poly := [((-1/1:ℚ),2,((-2),0,0,0,0,0,0)),((1/1:ℚ),3,(0,0,0,0,0,0,0)),((1/1:ℚ),20,(0,0,0,0,0,0,0)),((-1/1:ℚ),28,((-2),0,0,0,0,0,0)),((-1/1:ℚ),33,((-2),0,0,0,0,0,0)),((-1/1:ℚ),37,((-2),0,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((-1/1:ℚ),50,((-2),0,0,0,0,0,0)),((1/1:ℚ),55,(0,0,0,0,0,0,0)),((1/1:ℚ),60,(0,0,0,0,0,0,0)),((-1/1:ℚ),75,((-2),0,0,0,0,0,0)),((1/1:ℚ),97,(0,0,0,0,0,0,0)),((1/1:ℚ),271,(0,0,0,0,0,0,0)),((-1/1:ℚ),273,((-2),0,0,0,0,0,0)),((1/1:ℚ),275,(0,0,0,0,0,0,0)),((-1/1:ℚ),279,((-2),0,0,0,0,0,0)),((1/1:ℚ),287,(0,0,0,0,0,0,0)),((-1/1:ℚ),290,((-2),0,0,0,0,0,0)),((-1/1:ℚ),298,((-2),0,0,0,0,0,0)),((1/1:ℚ),299,(0,0,0,0,0,0,0)),((-1/1:ℚ),301,((-2),0,0,0,0,0,0)),((-1/1:ℚ),302,((-2),0,0,0,0,0,0)),((1/1:ℚ),310,(0,0,0,0,0,0,0)),((-1/1:ℚ),313,((-2),0,0,0,0,0,0)),((1/1:ℚ),318,(0,0,0,0,0,0,0)),((1/1:ℚ),326,(0,0,0,0,0,0,0)),((-1/1:ℚ),328,((-2),0,0,0,0,0,0)),((-1/1:ℚ),329,((-2),0,0,0,0,0,0)),((-1/1:ℚ),330,((-2),0,0,0,0,0,0)),((-1/1:ℚ),331,((-2),0,0,0,0,0,0)),((-1/1:ℚ),332,((-2),0,0,0,0,0,0)),((-1/1:ℚ),334,((-2),0,0,0,0,0,0)),((-1/1:ℚ),335,((-2),0,0,0,0,0,0)),((1/1:ℚ),346,(0,0,0,0,0,0,0)),((1/1:ℚ),347,(0,0,0,0,0,0,0)),((-1/1:ℚ),354,((-2),0,0,0,0,0,0)),((-1/1:ℚ),355,((-2),0,0,0,0,0,0)),((1/1:ℚ),356,(0,0,0,0,0,0,0)),((1/1:ℚ),357,(0,0,0,0,0,0,0)),((1/1:ℚ),358,(0,0,0,0,0,0,0)),((1/1:ℚ),359,(0,0,0,0,0,0,0)),((-1/1:ℚ),360,((-2),0,0,0,0,0,0)),((-1/1:ℚ),361,((-2),0,0,0,0,0,0)),((-1/1:ℚ),364,((-2),0,0,0,0,0,0)),((-1/1:ℚ),365,((-2),0,0,0,0,0,0)),((1/1:ℚ),366,(0,0,0,0,0,0,0)),((1/1:ℚ),367,(0,0,0,0,0,0,0)),((1/1:ℚ),368,(0,0,0,0,0,0,0)),((1/1:ℚ),369,(0,0,0,0,0,0,0)),((-1/1:ℚ),370,((-2),0,0,0,0,0,0)),((-1/1:ℚ),371,((-2),0,0,0,0,0,0)),((-1/1:ℚ),372,((-2),0,0,0,0,0,0)),((-1/1:ℚ),378,((-2),0,0,0,0,0,0)),((-1/1:ℚ),379,((-2),0,0,0,0,0,0)),((1/1:ℚ),407,(0,0,0,0,0,0,0)),((1/1:ℚ),408,(0,0,0,0,0,0,0)),((1/1:ℚ),410,(0,0,0,0,0,0,0)),((1/1:ℚ),411,(0,0,0,0,0,0,0)),((1/1:ℚ),413,(0,0,0,0,0,0,0)),((-1/1:ℚ),427,((-2),0,0,0,0,0,0)),((-1/1:ℚ),428,((-2),0,0,0,0,0,0)),((1/1:ℚ),434,(0,0,0,0,0,0,0)),((-1/1:ℚ),436,((-2),0,0,0,0,0,0)),((1/1:ℚ),437,(0,0,0,0,0,0,0)),((-1/1:ℚ),438,((-2),0,0,0,0,0,0)),((-1/1:ℚ),476,((-2),0,0,0,0,0,0)),((1/1:ℚ),479,(0,0,0,0,0,0,0)),((1/1:ℚ),480,(0,0,0,0,0,0,0)),((1/1:ℚ),482,(0,0,0,0,0,0,0)),((1/1:ℚ),485,(0,0,0,0,0,0,0)),((1/1:ℚ),526,(0,0,0,0,0,0,0)),((1/1:ℚ),527,(0,0,0,0,0,0,0))]
def raw2199Left : ℕ→ℕ
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
def raw2199Right : ℕ→ℕ
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
def raw2199Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2199,378,63,3,(-12),raw2199Left,raw2199Right,(-2),0,0,0⟩
theorem raw2199Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2199Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2199Spec]
  decide +kernel
theorem raw2199Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2199Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2199Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2199Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2199Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2199Left,raw2199Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2199Observation : Fin 553 := ⟨516,by decide⟩
def raw2199Units : List ℕ := [2, 58, 37, 44, 23, 16, 34, 32, 4, 61, 5, 62, 1, 8, 59, 47, 20, 11, 38, 29, 22, 43, 25, 46, 26, 41, 50, 17, 53, 13, 55, 10, 19, 31, 40, 52]
theorem raw2199Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2199Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2199Spec.q raw2199Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2199Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 63 raw2199Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2199Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2199Units raw2199Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=63) v raw2199Units raw2199Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2199Observed
#print axioms raw2199Valid
#print axioms raw2199Row

def raw2201Poly : Poly := [((-1/1:ℚ),12,(2,(-2),0,0,0,0,0)),((1/1:ℚ),14,(0,0,0,0,0,0,0)),((1/1:ℚ),31,(0,0,0,0,0,0,0)),((-1/1:ℚ),34,(2,(-2),0,0,0,0,0)),((1/1:ℚ),39,(0,0,0,0,0,0,0)),((-1/1:ℚ),42,(2,(-2),0,0,0,0,0)),((1/1:ℚ),53,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(2,(-2),0,0,0,0,0)),((1/1:ℚ),72,(0,0,0,0,0,0,0)),((-1/1:ℚ),95,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),97,(2,(-2),0,0,0,0,0)),((1/1:ℚ),98,(0,0,0,0,0,0,0)),((-1/1:ℚ),270,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),275,(2,(-2),0,0,0,0,0)),((1/1:ℚ),278,(0,0,0,0,0,0,0)),((-1/1:ℚ),281,(2,(-2),0,0,0,0,0)),((1/1:ℚ),288,(0,0,0,0,0,0,0)),((1/1:ℚ),289,(0,0,0,0,0,0,0)),((1/1:ℚ),297,(0,0,0,0,0,0,0)),((-1/1:ℚ),299,(2,(-2),0,0,0,0,0)),((1/1:ℚ),300,(0,0,0,0,0,0,0)),((1/1:ℚ),315,(0,0,0,0,0,0,0)),((1/1:ℚ),324,(0,0,0,0,0,0,0)),((-1/1:ℚ),325,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),326,(2,(-2),0,0,0,0,0)),((1/1:ℚ),342,(0,0,0,0,0,0,0)),((1/1:ℚ),343,(0,0,0,0,0,0,0)),((-1/1:ℚ),344,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),345,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),346,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),347,(2,(-2),0,0,0,0,0)),((1/1:ℚ),374,(0,0,0,0,0,0,0)),((1/1:ℚ),375,(0,0,0,0,0,0,0)),((1/1:ℚ),397,(0,0,0,0,0,0,0)),((1/1:ℚ),398,(0,0,0,0,0,0,0)),((1/1:ℚ),399,(0,0,0,0,0,0,0)),((1/1:ℚ),401,(0,0,0,0,0,0,0)),((-1/1:ℚ),402,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),403,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),404,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),405,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),407,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),409,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),410,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),411,(2,(-2),0,0,0,0,0)),((1/1:ℚ),458,(0,0,0,0,0,0,0)),((1/1:ℚ),459,(0,0,0,0,0,0,0)),((1/1:ℚ),461,(0,0,0,0,0,0,0)),((-1/1:ℚ),462,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),463,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),464,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),465,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),478,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),479,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),480,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),481,(2,(-2),0,0,0,0,0)),((1/1:ℚ),486,(0,0,0,0,0,0,0)),((1/1:ℚ),487,(0,0,0,0,0,0,0)),((1/1:ℚ),492,(0,0,0,0,0,0,0)),((1/1:ℚ),493,(0,0,0,0,0,0,0)),((1/1:ℚ),520,(0,0,0,0,0,0,0)),((1/1:ℚ),521,(0,0,0,0,0,0,0)),((1/1:ℚ),522,(0,0,0,0,0,0,0)),((1/1:ℚ),523,(0,0,0,0,0,0,0)),((-1/1:ℚ),524,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),525,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),526,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),527,(2,(-2),0,0,0,0,0)),((1/1:ℚ),544,(0,0,0,0,0,0,0)),((1/1:ℚ),545,(0,0,0,0,0,0,0)),((1/1:ℚ),549,(0,0,0,0,0,0,0)),((1/1:ℚ),550,(0,0,0,0,0,0,0))]
def raw2201Left : ℕ→ℕ
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
def raw2201Right : ℕ→ℕ
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
def raw2201Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2201,378,63,4,(-9),raw2201Left,raw2201Right,2,(-2),0,0⟩
theorem raw2201Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2201Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2201Spec]
  decide +kernel
theorem raw2201Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2201Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2201Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2201Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2201Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2201Left,raw2201Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2201Observation : Fin 553 := ⟨518,by decide⟩
def raw2201Units : List ℕ := [26, 5, 61, 40, 47, 19, 62, 34, 32, 4, 2, 1, 23, 44, 22, 43, 11, 20, 29, 38, 10, 37, 46, 55, 16, 58, 8, 50, 17, 31, 52, 59, 41, 53, 13, 25]
theorem raw2201Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2201Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2201Spec.q raw2201Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2201Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 63 raw2201Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2201Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2201Units raw2201Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=63) v raw2201Units raw2201Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2201Observed
#print axioms raw2201Valid
#print axioms raw2201Row

def raw2202Poly : Poly := [((1/1:ℚ),0,(0,0,0,0,0,0,0)),((-1/1:ℚ),12,(2,(-2),0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),22,(0,0,0,0,0,0,0)),((1/1:ℚ),24,(0,0,0,0,0,0,0)),((-1/1:ℚ),34,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),42,(2,(-2),0,0,0,0,0)),((1/1:ℚ),58,(0,0,0,0,0,0,0)),((-1/1:ℚ),60,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),95,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),97,(2,(-2),0,0,0,0,0)),((1/1:ℚ),100,(0,0,0,0,0,0,0)),((-1/1:ℚ),270,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),275,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),281,(2,(-2),0,0,0,0,0)),((1/1:ℚ),285,(0,0,0,0,0,0,0)),((1/1:ℚ),286,(0,0,0,0,0,0,0)),((1/1:ℚ),294,(0,0,0,0,0,0,0)),((-1/1:ℚ),299,(2,(-2),0,0,0,0,0)),((1/1:ℚ),303,(0,0,0,0,0,0,0)),((1/1:ℚ),305,(0,0,0,0,0,0,0)),((1/1:ℚ),309,(0,0,0,0,0,0,0)),((1/1:ℚ),323,(0,0,0,0,0,0,0)),((-1/1:ℚ),325,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),326,(2,(-2),0,0,0,0,0)),((1/1:ℚ),340,(0,0,0,0,0,0,0)),((1/1:ℚ),341,(0,0,0,0,0,0,0)),((-1/1:ℚ),344,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),345,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),346,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),347,(2,(-2),0,0,0,0,0)),((1/1:ℚ),376,(0,0,0,0,0,0,0)),((1/1:ℚ),377,(0,0,0,0,0,0,0)),((1/1:ℚ),392,(0,0,0,0,0,0,0)),((1/1:ℚ),394,(0,0,0,0,0,0,0)),((1/1:ℚ),395,(0,0,0,0,0,0,0)),((1/1:ℚ),396,(0,0,0,0,0,0,0)),((-1/1:ℚ),402,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),403,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),404,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),406,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),408,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),409,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),410,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),411,(2,(-2),0,0,0,0,0)),((1/1:ℚ),452,(0,0,0,0,0,0,0)),((1/1:ℚ),454,(0,0,0,0,0,0,0)),((1/1:ℚ),455,(0,0,0,0,0,0,0)),((-1/1:ℚ),462,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),463,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),464,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),465,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),482,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),483,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),484,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),485,(2,(-2),0,0,0,0,0)),((1/1:ℚ),488,(0,0,0,0,0,0,0)),((1/1:ℚ),489,(0,0,0,0,0,0,0)),((1/1:ℚ),494,(0,0,0,0,0,0,0)),((1/1:ℚ),495,(0,0,0,0,0,0,0)),((1/1:ℚ),516,(0,0,0,0,0,0,0)),((1/1:ℚ),517,(0,0,0,0,0,0,0)),((1/1:ℚ),518,(0,0,0,0,0,0,0)),((1/1:ℚ),519,(0,0,0,0,0,0,0)),((-1/1:ℚ),524,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),525,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),526,(2,(-2),0,0,0,0,0)),((-1/1:ℚ),527,(2,(-2),0,0,0,0,0)),((1/1:ℚ),546,(0,0,0,0,0,0,0)),((1/1:ℚ),547,(0,0,0,0,0,0,0)),((1/1:ℚ),548,(0,0,0,0,0,0,0)),((1/1:ℚ),551,(0,0,0,0,0,0,0))]
def raw2202Left : ℕ→ℕ
  | 1 => 323
  | 2 => 305
  | 4 => 494
  | 5 => 285
  | 8 => 452
  | 10 => 18
  | 11 => 376
  | 13 => 516
  | 16 => 517
  | 17 => 22
  | 19 => 392
  | 20 => 548
  | 22 => 340
  | 23 => 488
  | 25 => 495
  | 26 => 546
  | 29 => 454
  | 31 => 24
  | 32 => 309
  | 34 => 294
  | 37 => 394
  | 38 => 58
  | 40 => 518
  | 41 => 489
  | 43 => 341
  | 44 => 551
  | 46 => 395
  | 47 => 547
  | 50 => 455
  | 52 => 100
  | 53 => 377
  | 55 => 396
  | 58 => 519
  | 59 => 0
  | 61 => 303
  | 62 => 286
  | _ => 0
def raw2202Right : ℕ→ℕ
  | 1 => 299
  | 2 => 34
  | 4 => 482
  | 5 => 464
  | 8 => 402
  | 10 => 526
  | 11 => 483
  | 13 => 462
  | 16 => 97
  | 17 => 403
  | 19 => 346
  | 20 => 344
  | 22 => 527
  | 23 => 12
  | 25 => 408
  | 26 => 404
  | 29 => 281
  | 31 => 275
  | 32 => 484
  | 34 => 409
  | 37 => 60
  | 38 => 524
  | 40 => 347
  | 41 => 345
  | 43 => 410
  | 44 => 95
  | 46 => 485
  | 47 => 465
  | 50 => 525
  | 52 => 411
  | 53 => 406
  | 55 => 463
  | 58 => 42
  | 59 => 270
  | 61 => 326
  | 62 => 325
  | _ => 0
def raw2202Spec : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec := ⟨2202,378,63,(-4),9,raw2202Left,raw2202Right,2,(-2),0,0⟩
theorem raw2202Valid : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid point raw2202Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Valid,raw2202Spec]
  decide +kernel
theorem raw2202Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2202Poly=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading raw2202Spec x y z w 1 v := by
  norm_num [eval,monomial,raw2202Poly,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,raw2202Spec,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,residues,raw2202Left,raw2202Right,Finset.sum_filter,Finset.sum_range_succ] <;> ring
def raw2202Observation : Fin 553 := ⟨519,by decide⟩
def raw2202Units : List ℕ := [23, 2, 58, 37, 44, 16, 59, 31, 29, 1, 62, 61, 20, 41, 19, 40, 8, 17, 26, 53, 25, 34, 43, 52, 13, 55, 5, 47, 4, 11, 32, 46, 38, 50, 10, 22]
theorem raw2202Observed (v : ℕ→ℂ) :
    QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2202Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval raw2202Spec.q raw2202Spec.right v := by
  change QuantitativeArithmeticRationalRows.eval v (QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2202Observation)=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval 63 raw2202Right v
  have h : QuantitativeArithmeticSmallLevelTwentySevenObservation.observation raw2202Observation=QuantitativeArithmeticSmallLevelTwentySevenShiftSource.sampleRow raw2202Units raw2202Right := by decide +kernel
  rw [h,QuantitativeArithmeticSmallLevelTwentySevenShiftSource.eval_sampleRow (q:=63) v raw2202Units raw2202Right (by decide +kernel) (by decide +kernel)]
#print axioms raw2202Observed
#print axioms raw2202Valid
#print axioms raw2202Row

def raw2247Poly : Poly := [((1/1:ℚ),473,(0,0,0,0,0,0,0)),((1/1:ℚ),507,(0,0,0,0,0,0,0)),((-1/1:ℚ),520,((-1),0,0,0,1,0,0)),((1/1:ℚ),532,((-2),0,0,0,0,0,0))]
def raw2247Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2247,378,2,17,![507,473],520,532⟩
theorem raw2247Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2247Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2247Spec]
  decide +kernel
theorem raw2247Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2247Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2247Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2247Spec]
  norm_num [eval,monomial,raw2247Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2247Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2247Valid
#print axioms raw2247Row

def raw2249Poly : Poly := [((1/1:ℚ),459,(0,0,0,0,0,0,0)),((-1/1:ℚ),471,((-1),0,0,0,1,0,0)),((1/1:ℚ),498,(0,0,0,0,0,0,0)),((1/1:ℚ),528,((-2),0,0,0,0,0,0))]
def raw2249Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2249,378,2,19,![498,459],471,528⟩
theorem raw2249Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2249Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2249Spec]
  decide +kernel
theorem raw2249Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2249Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2249Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2249Spec]
  norm_num [eval,monomial,raw2249Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2249Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2249Valid
#print axioms raw2249Row

def raw2274Poly : Poly := [((1/1:ℚ),452,(0,0,0,0,0,0,0)),((-1/1:ℚ),467,((-1),0,0,0,1,0,0)),((1/1:ℚ),512,(0,0,0,0,0,0,0)),((1/1:ℚ),533,((-2),0,0,0,0,0,0))]
def raw2274Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2274,378,2,44,![452,512],467,533⟩
theorem raw2274Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2274Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2274Spec]
  decide +kernel
theorem raw2274Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2274Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2274Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2274Spec]
  norm_num [eval,monomial,raw2274Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2274Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2274Valid
#print axioms raw2274Row

def raw2299Poly : Poly := [((1/1:ℚ),353,(0,0,0,0,0,0,0)),((-1/1:ℚ),360,((-1),0,0,0,1,0,0)),((1/1:ℚ),425,((-2),0,0,0,0,0,0)),((1/1:ℚ),526,(0,0,0,0,0,0,0))]
def raw2299Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2299,378,2,69,![526,353],360,425⟩
theorem raw2299Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2299Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2299Spec]
  decide +kernel
theorem raw2299Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2299Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2299Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2299Spec]
  norm_num [eval,monomial,raw2299Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2299Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2299Valid
#print axioms raw2299Row

def raw2304Poly : Poly := [((1/1:ℚ),455,((-2),0,0,0,0,0,0)),((-1/1:ℚ),491,((-1),0,0,0,1,0,0)),((1/1:ℚ),516,(0,0,0,0,0,0,0)),((1/1:ℚ),587,(0,0,0,0,0,0,0))]
def raw2304Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2304,378,2,74,![516,587],491,455⟩
theorem raw2304Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2304Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2304Spec]
  decide +kernel
theorem raw2304Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2304Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2304Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2304Spec]
  norm_num [eval,monomial,raw2304Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2304Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2304Valid
#print axioms raw2304Row

def raw2305Poly : Poly := [((1/1:ℚ),361,(0,0,0,0,0,0,0)),((-1/1:ℚ),432,((-1),0,0,0,1,0,0)),((1/1:ℚ),476,((-2),0,0,0,0,0,0)),((1/1:ℚ),483,(0,0,0,0,0,0,0))]
def raw2305Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2305,378,2,75,![483,361],432,476⟩
theorem raw2305Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2305Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2305Spec]
  decide +kernel
theorem raw2305Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2305Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2305Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2305Spec]
  norm_num [eval,monomial,raw2305Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2305Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2305Valid
#print axioms raw2305Row

def raw2312Poly : Poly := [((1/1:ℚ),385,(0,0,0,0,0,0,0)),((-1/1:ℚ),393,((-1),0,0,0,1,0,0)),((1/1:ℚ),417,((-2),0,0,0,0,0,0)),((1/1:ℚ),458,(0,0,0,0,0,0,0))]
def raw2312Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2312,378,2,82,![458,385],393,417⟩
theorem raw2312Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2312Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2312Spec]
  decide +kernel
theorem raw2312Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2312Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2312Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2312Spec]
  norm_num [eval,monomial,raw2312Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2312Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2312Valid
#print axioms raw2312Row

def raw2316Poly : Poly := [((1/1:ℚ),453,(0,0,0,0,0,0,0)),((-1/1:ℚ),468,((-1),0,0,0,1,0,0)),((1/1:ℚ),519,((-2),0,0,0,0,0,0)),((1/1:ℚ),588,(0,0,0,0,0,0,0))]
def raw2316Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2316,378,2,86,![453,588],468,519⟩
theorem raw2316Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2316Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2316Spec]
  decide +kernel
theorem raw2316Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2316Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2316Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2316Spec]
  norm_num [eval,monomial,raw2316Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2316Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2316Valid
#print axioms raw2316Row

def raw2334Poly : Poly := [((1/1:ℚ),420,(0,0,0,0,0,0,0)),((1/1:ℚ),450,(0,0,0,0,0,0,0)),((-1/1:ℚ),459,((-1),0,0,0,1,0,0)),((1/1:ℚ),471,((-2),0,0,0,0,0,0))]
def raw2334Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2334,378,2,104,![420,450],459,471⟩
theorem raw2334Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2334Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2334Spec]
  decide +kernel
theorem raw2334Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2334Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2334Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2334Spec]
  norm_num [eval,monomial,raw2334Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2334Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2334Valid
#print axioms raw2334Row

def raw2336Poly : Poly := [((1/1:ℚ),398,(0,0,0,0,0,0,0)),((-1/1:ℚ),422,((-1),0,0,0,1,0,0)),((1/1:ℚ),444,(0,0,0,0,0,0,0)),((1/1:ℚ),466,((-2),0,0,0,0,0,0))]
def raw2336Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2336,378,2,106,![398,444],422,466⟩
theorem raw2336Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2336Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2336Spec]
  decide +kernel
theorem raw2336Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2336Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2336Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2336Spec]
  norm_num [eval,monomial,raw2336Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2336Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2336Valid
#print axioms raw2336Row

def raw2337Poly : Poly := [((1/1:ℚ),388,(0,0,0,0,0,0,0)),((-1/1:ℚ),400,((-1),0,0,0,1,0,0)),((1/1:ℚ),419,((-2),0,0,0,0,0,0)),((1/1:ℚ),455,(0,0,0,0,0,0,0))]
def raw2337Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2337,378,2,107,![388,455],400,419⟩
theorem raw2337Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2337Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2337Spec]
  decide +kernel
theorem raw2337Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2337Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2337Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2337Spec]
  norm_num [eval,monomial,raw2337Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2337Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2337Valid
#print axioms raw2337Row

def raw2344Poly : Poly := [((1/1:ℚ),362,(0,0,0,0,0,0,0)),((-1/1:ℚ),438,((-1),0,0,0,1,0,0)),((1/1:ℚ),477,((-2),0,0,0,0,0,0)),((1/1:ℚ),480,(0,0,0,0,0,0,0))]
def raw2344Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2344,378,2,114,![362,480],438,477⟩
theorem raw2344Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2344Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2344Spec]
  decide +kernel
theorem raw2344Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2344Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2344Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2344Spec]
  norm_num [eval,monomial,raw2344Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2344Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2344Valid
#print axioms raw2344Row

def raw2345Poly : Poly := [((1/1:ℚ),458,((-2),0,0,0,0,0,0)),((-1/1:ℚ),496,((-1),0,0,0,1,0,0)),((1/1:ℚ),523,(0,0,0,0,0,0,0)),((1/1:ℚ),558,(0,0,0,0,0,0,0))]
def raw2345Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2345,378,2,115,![558,523],496,458⟩
theorem raw2345Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2345Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2345Spec]
  decide +kernel
theorem raw2345Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2345Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2345Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2345Spec]
  norm_num [eval,monomial,raw2345Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2345Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2345Valid
#print axioms raw2345Row

def raw2346Poly : Poly := [((1/1:ℚ),453,((-2),0,0,0,0,0,0)),((-1/1:ℚ),492,((-1),0,0,0,1,0,0)),((1/1:ℚ),513,(0,0,0,0,0,0,0)),((1/1:ℚ),548,(0,0,0,0,0,0,0))]
def raw2346Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2346,378,2,116,![548,513],492,453⟩
theorem raw2346Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2346Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2346Spec]
  decide +kernel
theorem raw2346Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2346Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2346Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2346Spec]
  norm_num [eval,monomial,raw2346Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2346Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2346Valid
#print axioms raw2346Row

def raw2348Poly : Poly := [((1/1:ℚ),505,(0,0,0,0,0,0,0)),((-1/1:ℚ),518,((-1),0,0,0,1,0,0)),((1/1:ℚ),529,((-2),0,0,0,0,0,0)),((1/1:ℚ),550,(0,0,0,0,0,0,0))]
def raw2348Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2348,378,2,118,![550,505],518,529⟩
theorem raw2348Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2348Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2348Spec]
  decide +kernel
theorem raw2348Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2348Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2348Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2348Spec]
  norm_num [eval,monomial,raw2348Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2348Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2348Valid
#print axioms raw2348Row

def raw2351Poly : Poly := [((1/1:ℚ),398,((-2),0,0,0,0,0,0)),((-1/1:ℚ),489,((-1),0,0,0,1,0,0)),((1/1:ℚ),531,(0,0,0,0,0,0,0)),((1/1:ℚ),559,(0,0,0,0,0,0,0))]
def raw2351Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2351,378,2,121,![559,531],489,398⟩
theorem raw2351Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2351Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2351Spec]
  decide +kernel
theorem raw2351Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2351Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2351Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2351Spec]
  norm_num [eval,monomial,raw2351Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2351Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2351Valid
#print axioms raw2351Row

def raw2352Poly : Poly := [((1/1:ℚ),350,(0,0,0,0,0,0,0)),((1/1:ℚ),392,((-2),0,0,0,0,0,0)),((-1/1:ℚ),487,((-1),0,0,0,1,0,0)),((1/1:ℚ),590,(0,0,0,0,0,0,0))]
def raw2352Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2352,378,2,122,![350,590],487,392⟩
theorem raw2352Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2352Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2352Spec]
  decide +kernel
theorem raw2352Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2352Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2352Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2352Spec]
  norm_num [eval,monomial,raw2352Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2352Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2352Valid
#print axioms raw2352Row

def raw2360Poly : Poly := [((1/1:ℚ),348,(0,0,0,0,0,0,0)),((1/1:ℚ),521,((-2),0,0,0,0,0,0)),((-1/1:ℚ),551,((-1),0,0,0,1,0,0)),((1/1:ℚ),569,(0,0,0,0,0,0,0))]
def raw2360Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2360,378,2,130,![348,569],551,521⟩
theorem raw2360Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2360Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2360Spec]
  decide +kernel
theorem raw2360Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2360Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2360Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2360Spec]
  norm_num [eval,monomial,raw2360Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2360Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2360Valid
#print axioms raw2360Row

def raw2361Poly : Poly := [((1/1:ℚ),423,(0,0,0,0,0,0,0)),((1/1:ℚ),495,((-2),0,0,0,0,0,0)),((-1/1:ℚ),549,((-1),0,0,0,1,0,0)),((1/1:ℚ),580,(0,0,0,0,0,0,0))]
def raw2361Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2361,378,2,131,![580,423],549,495⟩
theorem raw2361Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2361Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2361Spec]
  decide +kernel
theorem raw2361Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2361Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2361Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2361Spec]
  norm_num [eval,monomial,raw2361Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2361Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2361Valid
#print axioms raw2361Row

def raw2362Poly : Poly := [((1/1:ℚ),352,(0,0,0,0,0,0,0)),((-1/1:ℚ),361,((-1),0,0,0,1,0,0)),((1/1:ℚ),411,(0,0,0,0,0,0,0)),((1/1:ℚ),432,((-2),0,0,0,0,0,0))]
def raw2362Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2362,378,2,132,![352,411],361,432⟩
theorem raw2362Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2362Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2362Spec]
  decide +kernel
theorem raw2362Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2362Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2362Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2362Spec]
  norm_num [eval,monomial,raw2362Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2362Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2362Valid
#print axioms raw2362Row

def raw2364Poly : Poly := [((1/1:ℚ),391,(0,0,0,0,0,0,0)),((-1/1:ℚ),401,((-1),0,0,0,1,0,0)),((1/1:ℚ),421,((-2),0,0,0,0,0,0)),((1/1:ℚ),488,(0,0,0,0,0,0,0))]
def raw2364Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2364,378,2,134,![488,391],401,421⟩
theorem raw2364Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2364Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2364Spec]
  decide +kernel
theorem raw2364Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2364Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2364Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2364Spec]
  norm_num [eval,monomial,raw2364Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2364Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2364Valid
#print axioms raw2364Row

def raw2366Poly : Poly := [((1/1:ℚ),386,(0,0,0,0,0,0,0)),((-1/1:ℚ),395,((-1),0,0,0,1,0,0)),((1/1:ℚ),414,((-2),0,0,0,0,0,0)),((1/1:ℚ),486,(0,0,0,0,0,0,0))]
def raw2366Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2366,378,2,136,![486,386],395,414⟩
theorem raw2366Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2366Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2366Spec]
  decide +kernel
theorem raw2366Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2366Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2366Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2366Spec]
  norm_num [eval,monomial,raw2366Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2366Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2366Valid
#print axioms raw2366Row

def raw2368Poly : Poly := [((1/1:ℚ),360,(0,0,0,0,0,0,0)),((1/1:ℚ),406,(0,0,0,0,0,0,0)),((-1/1:ℚ),425,((-1),0,0,0,1,0,0)),((1/1:ℚ),436,((-2),0,0,0,0,0,0))]
def raw2368Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2368,378,2,138,![360,406],425,436⟩
theorem raw2368Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2368Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2368Spec]
  decide +kernel
theorem raw2368Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2368Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2368Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2368Spec]
  norm_num [eval,monomial,raw2368Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2368Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2368Valid
#print axioms raw2368Row

def raw2371Poly : Poly := [((1/1:ℚ),283,((-2),0,0,0,0,0,0)),((1/1:ℚ),426,(0,0,0,0,0,0,0)),((-1/1:ℚ),439,((-1),0,0,0,1,0,0)),((1/1:ℚ),527,(0,0,0,0,0,0,0))]
def raw2371Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2371,378,2,141,![527,426],439,283⟩
theorem raw2371Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2371Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2371Spec]
  decide +kernel
theorem raw2371Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2371Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2371Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2371Spec]
  norm_num [eval,monomial,raw2371Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2371Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2371Valid
#print axioms raw2371Row

def raw2376Poly : Poly := [((1/1:ℚ),451,(0,0,0,0,0,0,0)),((-1/1:ℚ),460,((-1),0,0,0,1,0,0)),((1/1:ℚ),473,((-2),0,0,0,0,0,0)),((1/1:ℚ),495,(0,0,0,0,0,0,0))]
def raw2376Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2376,378,2,146,![495,451],460,473⟩
theorem raw2376Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2376Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2376Spec]
  decide +kernel
theorem raw2376Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2376Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2376Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2376Spec]
  norm_num [eval,monomial,raw2376Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2376Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2376Valid
#print axioms raw2376Row

def raw2378Poly : Poly := [((1/1:ℚ),400,((-2),0,0,0,0,0,0)),((1/1:ℚ),445,(0,0,0,0,0,0,0)),((-1/1:ℚ),455,((-1),0,0,0,1,0,0)),((1/1:ℚ),491,(0,0,0,0,0,0,0))]
def raw2378Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2378,378,2,148,![491,445],455,400⟩
theorem raw2378Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2378Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2378Spec]
  decide +kernel
theorem raw2378Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2378Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2378Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2378Spec]
  norm_num [eval,monomial,raw2378Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2378Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2378Valid
#print axioms raw2378Row

def raw2381Poly : Poly := [((1/1:ℚ),470,(0,0,0,0,0,0,0)),((-1/1:ℚ),535,((-1),0,0,0,1,0,0)),((1/1:ℚ),545,((-2),0,0,0,0,0,0)),((1/1:ℚ),560,(0,0,0,0,0,0,0))]
def raw2381Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2381,378,2,151,![560,470],535,545⟩
theorem raw2381Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2381Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2381Spec]
  decide +kernel
theorem raw2381Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2381Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2381Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2381Spec]
  norm_num [eval,monomial,raw2381Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2381Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2381Valid
#print axioms raw2381Row

def raw2389Poly : Poly := [((1/1:ℚ),296,(0,0,0,0,0,0,0)),((1/1:ℚ),353,((-2),0,0,0,0,0,0)),((-1/1:ℚ),379,((-1),0,0,0,1,0,0)),((1/1:ℚ),408,(0,0,0,0,0,0,0))]
def raw2389Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2389,378,2,159,![408,296],379,353⟩
theorem raw2389Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2389Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2389Spec]
  decide +kernel
theorem raw2389Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2389Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2389Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2389Spec]
  norm_num [eval,monomial,raw2389Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2389Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2389Valid
#print axioms raw2389Row

def raw2390Poly : Poly := [((1/1:ℚ),272,(0,0,0,0,0,0,0)),((1/1:ℚ),399,(0,0,0,0,0,0,0)),((-1/1:ℚ),423,((-1),0,0,0,1,0,0)),((1/1:ℚ),549,((-2),0,0,0,0,0,0))]
def raw2390Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2390,378,2,160,![399,272],423,549⟩
theorem raw2390Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2390Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2390Spec]
  decide +kernel
theorem raw2390Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2390Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2390Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2390Spec]
  norm_num [eval,monomial,raw2390Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2390Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2390Valid
#print axioms raw2390Row

def raw2394Poly : Poly := [((1/1:ℚ),393,(0,0,0,0,0,0,0)),((-1/1:ℚ),417,((-1),0,0,0,1,0,0)),((1/1:ℚ),547,((-2),0,0,0,0,0,0)),((1/1:ℚ),593,(0,0,0,0,0,0,0))]
def raw2394Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2394,378,2,164,![393,593],417,547⟩
theorem raw2394Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2394Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2394Spec]
  decide +kernel
theorem raw2394Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2394Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2394Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2394Spec]
  norm_num [eval,monomial,raw2394Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2394Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2394Valid
#print axioms raw2394Row

def raw2395Poly : Poly := [((1/1:ℚ),298,(0,0,0,0,0,0,0)),((1/1:ℚ),404,(0,0,0,0,0,0,0)),((-1/1:ℚ),426,((-1),0,0,0,1,0,0)),((1/1:ℚ),439,((-2),0,0,0,0,0,0))]
def raw2395Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2395,378,2,165,![404,298],426,439⟩
theorem raw2395Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2395Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2395Spec]
  decide +kernel
theorem raw2395Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2395Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2395Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2395Spec]
  norm_num [eval,monomial,raw2395Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2395Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2395Valid
#print axioms raw2395Row

def raw2396Poly : Poly := [((1/1:ℚ),414,(0,0,0,0,0,0,0)),((-1/1:ℚ),475,((-1),0,0,0,1,0,0)),((1/1:ℚ),522,((-2),0,0,0,0,0,0)),((1/1:ℚ),571,(0,0,0,0,0,0,0))]
def raw2396Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2396,378,2,166,![414,571],475,522⟩
theorem raw2396Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2396Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2396Spec]
  decide +kernel
theorem raw2396Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2396Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2396Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2396Spec]
  norm_num [eval,monomial,raw2396Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2396Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2396Valid
#print axioms raw2396Row

def raw2402Poly : Poly := [((1/1:ℚ),468,(0,0,0,0,0,0,0)),((1/1:ℚ),506,(0,0,0,0,0,0,0)),((-1/1:ℚ),519,((-1),0,0,0,1,0,0)),((1/1:ℚ),531,((-2),0,0,0,0,0,0))]
def raw2402Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2402,378,2,172,![468,506],519,531⟩
theorem raw2402Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2402Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2402Spec]
  decide +kernel
theorem raw2402Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2402Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2402Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2402Spec]
  norm_num [eval,monomial,raw2402Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2402Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2402Valid
#print axioms raw2402Row

def raw2436Poly : Poly := [((1/1:ℚ),390,(0,0,0,0,0,0,0)),((1/1:ℚ),507,(0,0,0,0,0,0,0)),((1/1:ℚ),510,(0,0,0,0,0,0,0))]
def raw2436Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2436,378,3,17,![507,510,390],407,366⟩
theorem raw2436Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2436Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2436Spec]
  decide +kernel
theorem raw2436Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2436Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2436Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2436Spec]
  norm_num [eval,monomial,raw2436Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2436Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2436Valid
#print axioms raw2436Row

def raw2441Poly : Poly := [((1/1:ℚ),416,(0,0,0,0,0,0,0)),((1/1:ℚ),490,(0,0,0,0,0,0,0)),((1/1:ℚ),491,(0,0,0,0,0,0,0))]
def raw2441Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2441,378,3,22,![490,491,416],378,293⟩
theorem raw2441Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2441Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2441Spec]
  decide +kernel
theorem raw2441Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2441Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2441Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2441Spec]
  norm_num [eval,monomial,raw2441Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2441Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2441Valid
#print axioms raw2441Row

def raw2450Poly : Poly := [((1/1:ℚ),553,(0,0,0,0,0,0,0)),((1/1:ℚ),561,(0,0,0,0,0,0,0)),((1/1:ℚ),567,(0,0,0,0,0,0,0))]
def raw2450Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2450,378,3,31,![553,561,567],478,367⟩
theorem raw2450Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2450Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2450Spec]
  decide +kernel
theorem raw2450Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2450Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2450Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2450Spec]
  norm_num [eval,monomial,raw2450Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2450Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2450Valid
#print axioms raw2450Row

def raw2456Poly : Poly := [((1/1:ℚ),384,(0,0,0,0,0,0,0)),((1/1:ℚ),499,(0,0,0,0,0,0,0)),((1/1:ℚ),504,(0,0,0,0,0,0,0))]
def raw2456Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2456,378,3,37,![499,384,504],403,434⟩
theorem raw2456Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2456Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2456Spec]
  decide +kernel
theorem raw2456Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2456Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2456Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2456Spec]
  norm_num [eval,monomial,raw2456Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2456Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2456Valid
#print axioms raw2456Row

def raw2463Poly : Poly := [((1/1:ℚ),452,(0,0,0,0,0,0,0)),((1/1:ℚ),454,(0,0,0,0,0,0,0)),((1/1:ℚ),455,(0,0,0,0,0,0,0))]
def raw2463Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2463,378,3,44,![452,454,455],352,301⟩
theorem raw2463Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2463Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2463Spec]
  decide +kernel
theorem raw2463Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2463Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2463Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2463Spec]
  norm_num [eval,monomial,raw2463Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2463Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2463Valid
#print axioms raw2463Row

def raw2508Poly : Poly := [((1/1:ℚ),389,(0,0,0,0,0,0,0)),((1/1:ℚ),509,(0,0,0,0,0,0,0)),((1/1:ℚ),514,(0,0,0,0,0,0,0))]
def raw2508Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2508,378,3,89,![509,389,514],410,435⟩
theorem raw2508Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2508Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2508Spec]
  decide +kernel
theorem raw2508Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2508Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2508Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2508Spec]
  norm_num [eval,monomial,raw2508Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2508Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2508Valid
#print axioms raw2508Row

def raw2532Poly : Poly := [((1/1:ℚ),306,(0,0,0,0,0,0,0)),((1/1:ℚ),536,(0,0,0,0,0,0,0)),((1/1:ℚ),538,(0,0,0,0,0,0,0))]
def raw2532Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2532,378,3,113,![536,538,306],463,357⟩
theorem raw2532Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2532Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2532Spec]
  decide +kernel
theorem raw2532Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2532Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2532Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2532Spec]
  norm_num [eval,monomial,raw2532Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2532Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2532Valid
#print axioms raw2532Row

def raw2550Poly : Poly := [((-1/1:ℚ),15,(0,0,0,(-1),0,0,1)),((1/1:ℚ),71,(0,0,0,0,0,0,0)),((1/1:ℚ),121,(0,0,0,(-2),0,0,0)),((1/1:ℚ),312,(0,0,0,0,0,0,0)),((1/1:ℚ),448,(0,0,0,0,0,0,0)),((1/1:ℚ),536,(0,0,0,0,0,0,0)),((1/1:ℚ),576,(0,0,0,0,0,0,0)),((1/1:ℚ),584,(0,0,0,0,0,0,0)),((1/1:ℚ),588,(0,0,0,0,0,0,0))]
def raw2550Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2550,378,7,5,![312,576,536,448,584,588,71],15,121⟩
theorem raw2550Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2550Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2550Spec]
  decide +kernel
theorem raw2550Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2550Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2550Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2550Spec]
  norm_num [eval,monomial,raw2550Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2550Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2550Valid
#print axioms raw2550Row

def raw2558Poly : Poly := [((1/1:ℚ),17,(0,0,0,0,0,0,0)),((1/1:ℚ),119,(0,0,0,(-2),0,0,0)),((-1/1:ℚ),137,(0,0,0,(-1),0,0,1)),((1/1:ℚ),291,(0,0,0,0,0,0,0)),((1/1:ℚ),445,(0,0,0,0,0,0,0)),((1/1:ℚ),555,(0,0,0,0,0,0,0)),((1/1:ℚ),559,(0,0,0,0,0,0,0)),((1/1:ℚ),563,(0,0,0,0,0,0,0)),((1/1:ℚ),567,(0,0,0,0,0,0,0))]
def raw2558Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2558,378,7,13,![291,555,559,17,563,567,445],137,119⟩
theorem raw2558Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2558Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2558Spec]
  decide +kernel
theorem raw2558Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2558Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2558Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2558Spec]
  norm_num [eval,monomial,raw2558Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2558Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2558Valid
#print axioms raw2558Row

def raw2564Poly : Poly := [((1/1:ℚ),17,(0,0,0,(-2),0,0,0)),((1/1:ℚ),57,(0,0,0,0,0,0,0)),((-1/1:ℚ),118,(0,0,0,(-1),0,0,1)),((1/1:ℚ),280,(0,0,0,0,0,0,0)),((1/1:ℚ),336,(0,0,0,0,0,0,0)),((1/1:ℚ),498,(0,0,0,0,0,0,0)),((1/1:ℚ),500,(0,0,0,0,0,0,0)),((1/1:ℚ),503,(0,0,0,0,0,0,0)),((1/1:ℚ),504,(0,0,0,0,0,0,0))]
def raw2564Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2564,378,7,19,![498,500,336,280,503,504,57],118,17⟩
theorem raw2564Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2564Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2564Spec]
  decide +kernel
theorem raw2564Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2564Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2564Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2564Spec]
  norm_num [eval,monomial,raw2564Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2564Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2564Valid
#print axioms raw2564Row

def raw2583Poly : Poly := [((1/1:ℚ),0,(0,0,0,(-2),0,0,0)),((-1/1:ℚ),26,(0,0,0,(-1),0,0,1)),((1/1:ℚ),100,(0,0,0,0,0,0,0)),((1/1:ℚ),294,(0,0,0,0,0,0,0)),((1/1:ℚ),303,(0,0,0,0,0,0,0)),((1/1:ℚ),341,(0,0,0,0,0,0,0)),((1/1:ℚ),471,(0,0,0,0,0,0,0)),((1/1:ℚ),495,(0,0,0,0,0,0,0)),((1/1:ℚ),517,(0,0,0,0,0,0,0))]
def raw2583Spec : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec := ⟨2583,378,7,38,![471,517,495,294,341,100,303],26,0⟩
theorem raw2583Valid : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid point raw2583Spec := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Valid,raw2583Spec]
  decide +kernel
theorem raw2583Row (x y z w a b c : ℂ) (v : ℕ→ℂ) : eval x y z w a b c v raw2583Poly=QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading raw2583Spec x y z w a b c v := by
  dsimp only [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2583Spec]
  norm_num [eval,monomial,raw2583Poly,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,raw2583Spec,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,Fin.sum_univ_succ] <;> ring
#print axioms raw2583Valid
#print axioms raw2583Row

end QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource
