module
public import QuantitativeArithmeticSmallLevelNineteenTenthFrickeV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteen
open Matrix ModularGroup UpperHalfPlane SmallLevelNormalized SmallLevelGenerators SmallLevelOriginal
open scoped MatrixGroups ModularForm

/-- Actual invariant matrices used by all eight114-grid algebra certificates.
Their membership follows from T, lower19 and the known odd-prime matrix. -/
def continuationMatrix0 : SL(2,ℤ) := ⟨!![1,-1;-38,39],by decide⟩
theorem original_continuation_matrix0 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix0=
      fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  have hmat : continuationMatrix0=(((1)*((lower 19)⁻¹))*((lower 19)⁻¹))*((T)⁻¹) := by decide
  change continuationMatrix0∈K
  rw [hmat]
  exact (K.mul_mem (K.mul_mem (K.mul_mem K.one_mem (K.inv_mem hu)) (K.inv_mem hu)) (K.inv_mem ht))

def continuationMatrix1 : SL(2,ℤ) := ⟨!![1,-1;38,-37],by decide⟩
theorem original_continuation_matrix1 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix1=
      fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  have hmat : continuationMatrix1=(((1)*(lower 19))*(lower 19))*((T)⁻¹) := by decide
  change continuationMatrix1∈K
  rw [hmat]
  exact (K.mul_mem (K.mul_mem (K.mul_mem K.one_mem hu) hu) (K.inv_mem ht))

def continuationMatrix2 : SL(2,ℤ) := ⟨!![1,0;57,1],by decide⟩
theorem original_continuation_matrix2 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix2=
      fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  have hmat : continuationMatrix2=(((1)*(lower 19))*(lower 19))*(lower 19) := by decide
  change continuationMatrix2∈K
  rw [hmat]
  exact (K.mul_mem (K.mul_mem (K.mul_mem K.one_mem hu) hu) hu)

def continuationMatrix3 : SL(2,ℤ) := ⟨!![2,-1;-19,10],by decide⟩
theorem original_continuation_matrix3 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix3=
      fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  have hmat : continuationMatrix3=(1)*(tenthMinus) := by decide
  change continuationMatrix3∈K
  rw [hmat]
  exact (K.mul_mem K.one_mem he)

def continuationMatrix4 : SL(2,ℤ) := ⟨!![9,1;-19,-2],by decide⟩
theorem original_continuation_matrix4 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix4=
      fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  have hz : -1∈K := SmallLevelThirtySix.slash_neg_one_even _ m
  have hmat : continuationMatrix4=(-1)*(((1)*((T)⁻¹))*((tenthMinus)⁻¹)) := by decide
  change continuationMatrix4∈K
  rw [hmat]
  exact (K.mul_mem hz (K.mul_mem (K.mul_mem K.one_mem (K.inv_mem ht)) (K.inv_mem he)))

def continuationMatrix5 : SL(2,ℤ) := ⟨!![10,-9;-171,154],by decide⟩
theorem original_continuation_matrix5 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix5=
      fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  have hmat : continuationMatrix5=(((1)*((lower 19)⁻¹))*((tenthMinus)⁻¹))*((T)⁻¹) := by decide
  change continuationMatrix5∈K
  rw [hmat]
  exact (K.mul_mem (K.mul_mem (K.mul_mem K.one_mem (K.inv_mem hu)) (K.inv_mem he)) (K.inv_mem ht))

def continuationMatrix6 : SL(2,ℤ) := ⟨!![17,-1;-152,9],by decide⟩
theorem original_continuation_matrix6 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix6=
      fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  have hz : -1∈K := SmallLevelThirtySix.slash_neg_one_even _ m
  have hmat : continuationMatrix6=(-1)*((((1)*(tenthMinus))*(T))*((lower 19)⁻¹)) := by decide
  change continuationMatrix6∈K
  rw [hmat]
  exact (K.mul_mem hz (K.mul_mem (K.mul_mem (K.mul_mem K.one_mem he) ht) (K.inv_mem hu)))

def continuationMatrix7 : SL(2,ℤ) := ⟨!![20,-21;-19,20],by decide⟩
theorem original_continuation_matrix7 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix7=
      fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  have hmat : continuationMatrix7=(((1)*((T)⁻¹))*((lower 19)⁻¹))*((T)⁻¹) := by decide
  change continuationMatrix7∈K
  rw [hmat]
  exact (K.mul_mem (K.mul_mem (K.mul_mem K.one_mem (K.inv_mem ht)) (K.inv_mem hu)) (K.inv_mem ht))

def continuationMatrix8 : SL(2,ℤ) := ⟨!![20,-1;-19,1],by decide⟩
theorem original_continuation_matrix8 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix8=
      fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  have hmat : continuationMatrix8=((1)*((T)⁻¹))*((lower 19)⁻¹) := by decide
  change continuationMatrix8∈K
  rw [hmat]
  exact (K.mul_mem (K.mul_mem K.one_mem (K.inv_mem ht)) (K.inv_mem hu))

def continuationMatrix9 : SL(2,ℤ) := ⟨!![21,-10;19,-9],by decide⟩
theorem original_continuation_matrix9 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix9=
      fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  have hmat : continuationMatrix9=(((1)*(T))*(lower 19))*(tenthMinus) := by decide
  change continuationMatrix9∈K
  rw [hmat]
  exact (K.mul_mem (K.mul_mem (K.mul_mem K.one_mem ht) hu) he)

def continuationMatrix10 : SL(2,ℤ) := ⟨!![28,-1;57,-2],by decide⟩
theorem original_continuation_matrix10 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix10=
      fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  have hz : -1∈K := SmallLevelThirtySix.slash_neg_one_even _ m
  have hmat : continuationMatrix10=(-1)*((((1)*((tenthMinus)⁻¹))*((lower 19)⁻¹))*((lower 19)⁻¹)) := by decide
  change continuationMatrix10∈K
  rw [hmat]
  exact (K.mul_mem hz (K.mul_mem (K.mul_mem (K.mul_mem K.one_mem (K.inv_mem he)) (K.inv_mem hu)) (K.inv_mem hu)))

def continuationMatrix11 : SL(2,ℤ) := ⟨!![199,-11;380,-21],by decide⟩
theorem original_continuation_matrix11 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix11=
      fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  have hz : -1∈K := SmallLevelThirtySix.slash_neg_one_even _ m
  have hmat : continuationMatrix11=(-1)*((((1)*((tenthMinus)⁻¹))*(T))*((lower 19)⁻¹)) := by decide
  change continuationMatrix11∈K
  rw [hmat]
  exact (K.mul_mem hz (K.mul_mem (K.mul_mem (K.mul_mem K.one_mem (K.inv_mem he)) ht) (K.inv_mem hu)))

def continuationMatrix12 : SL(2,ℤ) := ⟨!![251,-131;-228,119],by decide⟩
theorem original_continuation_matrix12 (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix12=
      fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  have hmat : continuationMatrix12=(((1)*((T)⁻¹))*(tenthMinus))*(tenthMinus) := by decide
  change continuationMatrix12∈K
  rw [hmat]
  exact (K.mul_mem (K.mul_mem (K.mul_mem K.one_mem (K.inv_mem ht)) he) he)

#print axioms original_continuation_matrix0
#print axioms original_continuation_matrix1
#print axioms original_continuation_matrix2
#print axioms original_continuation_matrix3
#print axioms original_continuation_matrix4
#print axioms original_continuation_matrix5
#print axioms original_continuation_matrix6
#print axioms original_continuation_matrix7
#print axioms original_continuation_matrix8
#print axioms original_continuation_matrix9
#print axioms original_continuation_matrix10
#print axioms original_continuation_matrix11
#print axioms original_continuation_matrix12
end QuantitativeArithmeticSmallLevelNineteen
