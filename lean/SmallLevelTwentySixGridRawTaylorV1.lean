module
public import SmallLevelTwentySixGridWordTaylorV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct SmallLevelAdditive Complex Set
open SmallLevelTwentySixTwelfth (W)
open scoped MatrixGroups ModularForm

private theorem scale_mobius (A B C D z t : ℂ) (ht : t≠0) :
    (t*A*z+t*B)/(t*C*z+t*D)=(A*z+B)/(C*z+D) := by
  rw [show t*A*z+t*B=t*(A*z+B) by ring,
    show t*C*z+t*D=t*(C*z+D) by ring]
  exact mul_div_mul_left _ _ ht

private theorem scale_factor (m : ℕ) (χ C D z t d : ℂ) (h : t^2*d=1) :
    χ/(t*C*z+t*D)^(2*m)=χ*d^m/(C*z+D)^(2*m) := by
  have hi : ((t^2)^m)⁻¹=d^m := by
    apply inv_eq_of_mul_eq_one_right
    rw [←mul_pow,h,one_pow]
  rw [show t*C*z+t*D=t*(C*z+D) by ring,mul_pow,pow_mul,
    div_eq_mul_inv,_root_.mul_inv_rev,hi]
  rw [div_eq_mul_inv]
  ring

/-- Projective normalization may have either sign. Its square is fixed
by the determinant, so both choices give the same even-weight law. -/
theorem raw_word_fourier {m : ℕ} {f : ℕ→ℂ} {w : List (Fin 4×Bool)}
    {χ : ℂ} (hχ : χ=1 ∨ χ= -1)
    (h : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] gridWord w=χ • fourierFunction (2*m) f)
    (A B C D t : ℝ) (hc : (gridWord w).val=t • !![A,B;C,D])
    (z : ℂ) (hz : 0<z.im) :
    fourier (fullCoefficients f (2*m)) z=
      (χ*((A*D-B*C:ℝ):ℂ)^m)/((C:ℂ)*z+(D:ℂ))^(2*m)*
        fourier (fullCoefficients f (2*m)) (((A:ℂ)*z+(B:ℂ))/((C:ℂ)*z+(D:ℂ))) := by
  have hd : t^2*(A*D-B*C)=1 := by
    have hg:=gridWord_det w
    change (gridWord w).val.det=1 at hg
    rw [hc,det_fin_two] at hg
    change t*A*(t*D)-t*B*(t*C)=1 at hg
    linear_combination hg
  have ht : t≠0 := by intro ht; simp [ht] at hd
  have hd' : (t:ℂ)^2*((A*D-B*C:ℝ):ℂ)=1 := by exact_mod_cast hd
  have hh:=grid_word_fourier hχ h z hz
  rw [hc] at hh
  norm_num only [Matrix.smul_apply,smul_eq_mul,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,Complex.ofReal_mul] at hh
  rw [scale_mobius _ _ _ _ _ _ (by exact_mod_cast ht),scale_factor m _ _ _ _ _ _ hd'] at hh
  exact hh

/-- Original-input Taylor rows in rational/raw matrix coordinates. The
matrix certificate is a finite identity, not an additional analytic law. -/
theorem raw_word_taylor_of_fricke (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 26 (2*m) f)
    {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=η • fourierFunction (2*m) f)
    (w : List (Fin 4×Bool)) (A B C D t r : ℝ)
    (hc : (gridWord w).val=t • !![A,B;C,D])
    (hC : C≠0) (hd : 0<A*D-B*C) (hr : C*r+D≠0) :
    ∃ (bound : ℝ) (error : ℕ→ℂ→ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        original (2*m) f r s-gridWordSign (root 26 f 2) η w*
          (((C*r+D)^2/(A*D-B*C):ℝ):ℂ)^(s-(m:ℂ))*
          (∑ n∈Finset.range M, (Complex.I*((C*(C*r+D)/(A*D-B*C):ℝ):ℂ))^n*
            Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
            original (2*m) f ((A*r+B)/(C*r+D)) (s+(n:ℂ)))=error M s := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  have hF:=raw_word_fourier
    (gridWordSign_unit (root_unit hf.toEulerData 2) hη w)
    (grid_words_of_fricke m hf hη hW w) A B C D t hc
  exact QuantitativeArithmeticTwoSequenceTaylor.matrix_even_rows
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m))
    m A B C D r hC hd hr (gridWordSign (root 26 f 2) η w) hF

#print axioms raw_word_fourier
#print axioms raw_word_taylor_of_fricke
end SmallLevelTwentySixGrid
