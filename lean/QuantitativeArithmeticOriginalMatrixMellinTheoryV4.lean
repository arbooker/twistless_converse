module

public import QuantitativeArithmeticMatrixInfinityMellinTheoryV4
public import QuantitativeArithmeticTwoSequenceStripRowsV1
public import SmallLevelNormalizedFrickeV1
public import SmallLevelOriginalV1

/-! Consolidated chapter: QuantitativeArithmeticOriginalMatrixMellin. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticOriginalMatrixMellinV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticOriginalMatrixMellin
open Matrix UpperHalfPlane SmallLevelOriginal SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open SmallLevelAdditive Complex Set MeasureTheory
open scoped MatrixGroups ModularForm

def actualMellin (k : ℕ) (f : ℕ→ℂ) (r : ℝ) : ℂ→ℂ :=
  mellin (fun y : ℝ => fourier (fullCoefficients f k) ((r:ℂ)+(y:ℂ)*Complex.I))

theorem matrix_fourier {k : ℕ} (f : ℕ→ℂ) (g : GL (Fin 2) ℝ)
    (hg : (GeneralLinearGroup.det g:ℝ)=1) (χ : ℂ) (hχ : χ=1 ∨ χ= -1)
    (hslash : fourierFunction k f ∣[(k:ℤ)] g=χ • fourierFunction k f)
    (z : ℂ) (hz : 0<z.im) :
    fourier (fullCoefficients f k) z=
      χ/(((g.val 1 0:ℂ)*z+(g.val 1 1:ℂ))^k)*
        fourier (fullCoefficients f k)
          (((g.val 0 0:ℂ)*z+(g.val 0 1:ℂ))/((g.val 1 0:ℂ)*z+(g.val 1 1:ℂ))) := by
  have hback : fourierFunction k f=χ • (fourierFunction k f ∣[(k:ℤ)] g) := by
    rcases hχ with h|h
    · simpa only [h,one_smul] using hslash.symm
    · simpa only [h,neg_one_smul,neg_neg] using congrArg Neg.neg hslash.symm
  have hh := congrFun hback ⟨z,hz⟩
  rw [Pi.smul_apply,smul_eq_mul,det_one_slash _ hg,zpow_neg,zpow_natCast] at hh
  simp only [fourierFunction] at hh
  rw [coe_smul_of_det_pos (by rw [hg]; norm_num)] at hh
  simpa only [num,denom,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

theorem source_entire {N k : ℕ} (hk : 0<k) {f : ℕ→ℂ} (hf : IsSolution N k f)
    (g : GL (Fin 2) ℝ) (hg : (GeneralLinearGroup.det g:ℝ)=1)
    (χ : ℂ) (hχ : χ=1 ∨ χ= -1)
    (hslash : fourierFunction k f ∣[(k:ℤ)] g=χ • fourierFunction k f)
    (r : ℝ) (hC : g.val 1 0≠0) (hr : g.val 1 0*r+g.val 1 1=0) :
    Differentiable ℂ (actualMellin k f r) := by
  obtain ⟨τ,_,hbound⟩ := hf.growth
  have hd : g.val 0 0*g.val 1 1-g.val 0 1*g.val 1 0=(1:ℝ) := by
    change g.val.det=1 at hg
    simpa only [Matrix.det_fin_two] using hg
  have hn : χ≠0 := by rcases hχ with h|h <;> simp [h]
  exact QuantitativeArithmeticMatrixInfinityMellin.matrix_source_entire
    (polynomial_bound hf.zero hbound k) (fullCoefficients_zero hf.zero k)
    k hk (g.val 0 0) (g.val 0 1) (g.val 1 0) (g.val 1 1) r hC
    (by rw [hd]; norm_num) hr χ hn (matrix_fourier f g hg χ hχ hslash)

#print axioms matrix_fourier
#print axioms source_entire
end QuantitativeArithmeticOriginalMatrixMellin
end
end

/-! ## QuantitativeArithmeticOriginalMatrixConvergentV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticOriginalMatrixMellin
open Matrix UpperHalfPlane SmallLevelOriginal SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open SmallLevelAdditive Complex Set MeasureTheory
open scoped MatrixGroups ModularForm
theorem source_convergent {N k : ℕ} (hk : 0<k) {f : ℕ→ℂ} (hf : IsSolution N k f)
    (g : GL (Fin 2) ℝ) (hg : (GeneralLinearGroup.det g:ℝ)=1)
    (χ : ℂ) (hχ : χ=1 ∨ χ= -1)
    (hslash : fourierFunction k f ∣[(k:ℤ)] g=χ • fourierFunction k f)
    (r : ℝ) (hC : g.val 1 0≠0) (hr : g.val 1 0*r+g.val 1 1=0) :
    ∀ s : ℂ, MellinConvergent
      (fun t : ℝ => fourier (fullCoefficients f k) ((r:ℂ)+(t:ℂ)*Complex.I)) s := by
  obtain ⟨τ,_,hbound⟩ := hf.growth
  have hd : g.val 0 0*g.val 1 1-g.val 0 1*g.val 1 0=(1:ℝ) := by
    change g.val.det=1 at hg
    simpa only [Matrix.det_fin_two] using hg
  have hn : χ≠0 := by rcases hχ with h|h <;> simp [h]
  exact QuantitativeArithmeticMatrixInfinityMellin.matrix_source_convergent
    (polynomial_bound hf.zero hbound k) (fullCoefficients_zero hf.zero k)
    k hk (g.val 0 0) (g.val 0 1) (g.val 1 0) (g.val 1 1) r hC
    (by rw [hd]; norm_num) hr χ hn (matrix_fourier f g hg χ hχ hslash)


#print axioms source_convergent
end QuantitativeArithmeticOriginalMatrixMellin
end
end
