module
public import SmallLevelThirtyFourGridCoherentFrickeV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGrid
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct SmallLevelAdditive Complex Set
open SmallLevelThirtyFourGroup (W)
open scoped MatrixGroups ModularForm

def wordRate (w : List (Fin 5×Bool)) (r : ℝ) : ℝ :=
  ((gridWord w).val 1 0*r+(gridWord w).val 1 1)^2

def wordDerivative (w : List (Fin 5×Bool)) (r : ℝ) : ℝ :=
  (gridWord w).val 1 0*((gridWord w).val 1 0*r+(gridWord w).val 1 1)

def wordPartner (w : List (Fin 5×Bool)) (r : ℝ) : ℝ :=
  ((gridWord w).val 0 0*r+(gridWord w).val 0 1)/
    ((gridWord w).val 1 0*r+(gridWord w).val 1 1)

/-- Every non-affine original word supplies all Taylor orders, with a
single error bound and the same Fricke sign as the Ramanujan rows. -/
theorem word_taylor_of_fricke (m : ℕ) (hm : 0<m) {f : ℕ→ℂ} (hf : IsSolution 34 (2*m) f)
    {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=η • fourierFunction (2*m) f)
    (w : List (Fin 5×Bool)) (hw : (gridWord w).val 1 0≠0)
    (r : ℝ) (hr : (gridWord w).val 1 0*r+(gridWord w).val 1 1≠0) :
    ∃ (bound : ℝ) (error : ℕ→ℂ→ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        original (2*m) f r s-gridWordSign (root 34 f 2) η w*
          (wordRate w r:ℂ)^(s-(m:ℂ))*
          (∑ n∈Finset.range M, (Complex.I*(wordDerivative w r:ℂ))^n*
            Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
            original (2*m) f (wordPartner w r) (s+(n:ℂ)))=error M s := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  have hF:=grid_word_fourier
    (gridWordSign_unit (root_unit hf.toEulerData 2) hη w)
    (grid_words_of_fricke m hm hf hη hW w)
  have hd : (gridWord w).val 0 0*(gridWord w).val 1 1-
      (gridWord w).val 0 1*(gridWord w).val 1 0=(1:ℝ) := by
    have h:=gridWord_det w
    change (gridWord w).val.det=1 at h
    simpa only [det_fin_two] using h
  have hh:=QuantitativeArithmeticTwoSequenceTaylor.matrix_even_rows
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m)) m
    ((gridWord w).val 0 0) ((gridWord w).val 0 1)
    ((gridWord w).val 1 0) ((gridWord w).val 1 1) r hw (by rw [hd]; norm_num) hr
    (gridWordSign (root 34 f 2) η w) (by
      intro z hz
      simpa only [hd,Complex.ofReal_one,one_pow,mul_one] using hF z hz)
  simpa only [hd,div_one,wordRate,wordDerivative,wordPartner,original] using hh

#print axioms word_taylor_of_fricke
end SmallLevelThirtyFourGrid
