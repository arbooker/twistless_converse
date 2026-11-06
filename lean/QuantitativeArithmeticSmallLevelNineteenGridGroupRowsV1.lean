module
public import QuantitativeArithmeticSmallLevelNineteenGridInvariantMatricesV1
public import QuantitativeArithmeticTwoSequenceTaylorTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteen
open Matrix ModularGroup UpperHalfPlane SmallLevelOriginal SmallLevelAdditive
open FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

/-- The thirteen actual known group transformations used in the grid. -/
def continuationMatrix : Fin 13 → SL(2,ℤ) :=
  ![continuationMatrix0,continuationMatrix1,continuationMatrix2,continuationMatrix3,continuationMatrix4,continuationMatrix5,continuationMatrix6,continuationMatrix7,continuationMatrix8,continuationMatrix9,continuationMatrix10,continuationMatrix11,continuationMatrix12]

theorem original_continuation_matrices (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) (i : Fin 13) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] continuationMatrix i=
      fourierFunction (2*m) f := by
  fin_cases i
  · exact original_continuation_matrix0 m hf
  · exact original_continuation_matrix1 m hf
  · exact original_continuation_matrix2 m hf
  · exact original_continuation_matrix3 m hf
  · exact original_continuation_matrix4 m hf
  · exact original_continuation_matrix5 m hf
  · exact original_continuation_matrix6 m hf
  · exact original_continuation_matrix7 m hf
  · exact original_continuation_matrix8 m hf
  · exact original_continuation_matrix9 m hf
  · exact original_continuation_matrix10 m hf
  · exact original_continuation_matrix11 m hf
  · exact original_continuation_matrix12 m hf

/-- Literal matrix Fourier law; its only transformation premise is the
already separately proved slash invariance. -/
theorem invariant_matrix_fourier (k : ℕ) (f : ℕ → ℂ) (γ : SL(2,ℤ))
    (hγ : fourierFunction k f ∣[(k:ℤ)] γ=fourierFunction k f)
    (z : ℂ) (hz : 0<z.im) :
    fourier (fullCoefficients f k) z=
      1/(((γ.val 1 0:ℤ):ℂ)*z+((γ.val 1 1:ℤ):ℂ))^k*
        fourier (fullCoefficients f k)
          ((((γ.val 0 0:ℤ):ℂ)*z+((γ.val 0 1:ℤ):ℂ))/
            (((γ.val 1 0:ℤ):ℂ)*z+((γ.val 1 1:ℤ):ℂ))) := by
  have h := congrFun hγ ⟨z,hz⟩
  rw [ModularForm.SL_slash_apply] at h
  simp only [fourierFunction,coe_specialLinearGroup_apply,zpow_neg,zpow_natCast] at h
  norm_num [denom,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe] at h
  simpa only [one_div,mul_comm] using h.symm

theorem continuationMatrix_lower_ne_zero (i : Fin 13) :
    ((continuationMatrix i).val 1 0:ℝ)≠0 := by
  fin_cases i <;> norm_num [continuationMatrix,continuationMatrix0,continuationMatrix1,continuationMatrix2,continuationMatrix3,continuationMatrix4,continuationMatrix5,continuationMatrix6,continuationMatrix7,continuationMatrix8,continuationMatrix9,continuationMatrix10,continuationMatrix11,continuationMatrix12]

/-- All-order actual matrix Taylor rows, before reduction to the finite grid.
This theorem introduces no continuation assumption on any additive twist. -/
theorem original_continuation_matrix_rows (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) (i : Fin 13)
    (j : ℝ) (hj : ((continuationMatrix i).val 1 0:ℝ)*j+
      ((continuationMatrix i).val 1 1:ℝ)≠0) :
    let A : ℝ := (continuationMatrix i).val 0 0
    let B : ℝ := (continuationMatrix i).val 0 1
    let C : ℝ := (continuationMatrix i).val 1 0
    let D : ℝ := (continuationMatrix i).val 1 1
    ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        transform (fullCoefficients f (2*m)) j s-
          (((C*j+D)^2:ℝ):ℂ)^(s-(m:ℂ))*
          (∑ n∈Finset.range M, (Complex.I*((C*(C*j+D):ℝ):ℂ))^n*
            Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
            transform (fullCoefficients f (2*m)) ((A*j+B)/(C*j+D))
              (s+(n:ℂ)))=error M s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hdetZ : (continuationMatrix i).val 0 0*(continuationMatrix i).val 1 1-
      (continuationMatrix i).val 0 1*(continuationMatrix i).val 1 0=1 := by
    simpa only [Matrix.det_fin_two] using (continuationMatrix i).property
  have hdet : ((continuationMatrix i).val 0 0:ℝ)*((continuationMatrix i).val 1 1:ℝ)-
      ((continuationMatrix i).val 0 1:ℝ)*((continuationMatrix i).val 1 0:ℝ)=1 := by
    exact_mod_cast hdetZ
  have hF := invariant_matrix_fourier (2*m) f (continuationMatrix i)
    (original_continuation_matrices m hf i)
  have he := QuantitativeArithmeticTwoSequenceTaylor.matrix_even_rows
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m)) m
    ((continuationMatrix i).val 0 0:ℝ) ((continuationMatrix i).val 0 1:ℝ)
    ((continuationMatrix i).val 1 0:ℝ) ((continuationMatrix i).val 1 1:ℝ) j
    (continuationMatrix_lower_ne_zero i) (by rw [hdet]; norm_num) hj 1
    (by simpa only [hdet,Complex.ofReal_one,one_pow,mul_one,Complex.ofReal_intCast] using hF)
  simpa only [hdet,div_one,one_mul] using he

#print axioms original_continuation_matrices
#print axioms invariant_matrix_fourier
#print axioms original_continuation_matrix_rows
end QuantitativeArithmeticSmallLevelNineteen
