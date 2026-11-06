module

public import SmallLevelTwentyEightGridSourcesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightGrid
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct
open scoped MatrixGroups ModularForm

private theorem scale_mobius (A B C D z t : ℂ) (ht : t≠0) :
    (t*A*z+t*B)/(t*C*z+t*D)=(A*z+B)/(C*z+D) := by
  rw [show t*A*z+t*B=t*(A*z+B) by ring,
    show t*C*z+t*D=t*(C*z+D) by ring]
  exact mul_div_mul_left _ _ ht

private theorem scale_factor (m : ℕ) (χ C D z s d : ℂ) (hs : s^2=d) :
    χ/((1/s)*C*z+(1/s)*D)^(2*m)=χ*d^m/(C*z+D)^(2*m) := by
  rw [show (1/s)*C*z+(1/s)*D=(1/s)*(C*z+D) by ring,
    mul_pow,one_div,inv_pow,div_mul_eq_div_div,div_inv_eq_mul,pow_mul,hs]

/-- The literal raw-matrix Fourier law, with determinant to the half-wten.
This verifies the normalization of the ten concrete source matrices. -/
theorem grid_source_fourier {m : ℕ} {f : ℕ→ℂ} {i : Fin 10}
    {χ : ℂ} (hχ : χ=1 ∨ χ= -1)
    (h : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] gridWord (gridSourceWord i)=
      χ • SmallLevelOriginal.fourierFunction (2*m) f)
    (z : ℂ) (hz : 0<z.im) :
    fourier (fullCoefficients f (2*m)) z=
      (χ*(gridSourceDet i:ℂ)^m)/
        (((gridSourceRaw i) 1 0:ℂ)*z+((gridSourceRaw i) 1 1:ℂ))^(2*m)*
        fourier (fullCoefficients f (2*m))
          ((((gridSourceRaw i) 0 0:ℂ)*z+((gridSourceRaw i) 0 1:ℂ))/
            (((gridSourceRaw i) 1 0:ℂ)*z+((gridSourceRaw i) 1 1:ℂ))) := by
  have hh:=grid_word_fourier hχ h z hz
  rw [gridSource_coordinates] at hh
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.map_apply,Int.coe_castRingHom,
    Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_intCast] at hh
  have hs : (Real.sqrt (gridSourceDet i):ℂ)^2=(gridSourceDet i:ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (gridSourceDet i): (0:ℝ)≤_)
  have hn : (Real.sqrt (gridSourceDet i):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast gridSourceDet_pos i)).ne'
  rw [scale_mobius _ _ _ _ _ _ (one_div_ne_zero hn),scale_factor m _ _ _ _ _ _ hs] at hh
  exact hh

/-- Coherently signed literal Fourier laws for the selected ten matrices. -/
theorem original_grid_sources (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 28 (2*m) f) :
    ∃ η : ℂ, (η=1 ∨ η= -1) ∧ ∀ i : Fin 10, ∀ z : ℂ, 0<z.im →
      fourier (fullCoefficients f (2*m)) z=
        (gridSourceSign η i*
            (gridSourceDet i:ℂ)^m)/
          (((gridSourceRaw i) 1 0:ℂ)*z+((gridSourceRaw i) 1 1:ℂ))^(2*m)*
          fourier (fullCoefficients f (2*m))
            ((((gridSourceRaw i) 0 0:ℂ)*z+((gridSourceRaw i) 0 1:ℂ))/
              (((gridSourceRaw i) 1 0:ℂ)*z+((gridSourceRaw i) 1 1:ℂ))) := by
  obtain ⟨η,hη,hw⟩:=original_grid_words m hf
  refine ⟨η,hη,?_⟩
  intro i z hz
  have hh:=grid_source_fourier
    (gridWordSign_unit hη (gridSourceWord i))
    (hw (gridSourceWord i)) z hz
  simpa only [gridSource_sign] using hh

#print axioms grid_source_fourier
#print axioms original_grid_sources
end SmallLevelTwentyEightGrid
