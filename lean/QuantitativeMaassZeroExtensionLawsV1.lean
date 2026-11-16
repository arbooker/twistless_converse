module

public import QuantitativeMaassSimplePowerReflectionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane AsymptoticOrbitDecode AsymptoticFreshMatrices

namespace QuantitativeMaass

/-- Extension by zero below the real axis permits purely algebraic
finite-sum identities to be applied to actual upper-half-plane functions. -/
def upperZeroExtension (f : ℍ → ℂ) (z : ℂ) : ℂ :=
  if hz : 0<z.im then f ⟨z,hz⟩ else 0

theorem upperZeroExtension_apply (f : ℍ → ℂ) (z : ℍ) : upperZeroExtension f z=f z := by
  unfold upperZeroExtension
  split_ifs with h
  · rfl
  · exact (h z.im_pos).elim

theorem ramified_label_coe (p : ℕ) (hp : 0<p) (a : Fin p) (z : ℍ) :
    ((ramifiedLabel p hp a • z : ℍ):ℂ)=((z:ℂ)+(a.val:ℂ))/(p:ℂ) := by
  rw [ramifiedLabel,AsymptoticRationalBranches.ofMatrix_action,
    AsymptoticRegularObservationRows.ramified,
    AsymptoticRegularObservationRows.realMatrix_ramified]
  simpa using AsymptoticRamifiedBranch.branch_action
    (show (0:ℝ)<p by exact_mod_cast hp) (a.val:ℝ) z

/-- A genuine pointwise U_p equation on the upper half-plane implies
the global algebraic averaging equation for its zero extension. -/
theorem upperZeroExtension_ramified (p : ℕ) (hp : 0<p) (f : ℍ → ℂ) (δ : ℂ)
    (hU : ∀ z : ℍ,∑ a : Fin p,f (ramifiedLabel p hp a • z)=δ*f z)
    (z : ℂ) : ramifiedAverage p (upperZeroExtension f) z=δ*upperZeroExtension f z := by
  by_cases hz : 0<z.im
  · have he := hU ⟨z,hz⟩
    have ht (a : Fin p) : upperZeroExtension f ((z+(a.val:ℂ))/(p:ℂ))=
        f (ramifiedLabel p hp a • (⟨z,hz⟩ : ℍ)) := by
      rw [←ramified_label_coe p hp a (⟨z,hz⟩ : ℍ),upperZeroExtension_apply]
    unfold ramifiedAverage
    simp_rw [ht]
    simpa only [upperZeroExtension,dite_eq_left hz] using he
  · have hpR : (0:ℝ)<p := by exact_mod_cast hp
    have ht (a : Fin p) : upperZeroExtension f ((z+(a.val:ℂ))/(p:ℂ))=0 := by
      apply dite_eq_right
      have hi : ((z+(a.val:ℂ))/(p:ℂ)).im=z.im/(p:ℝ) := by
        simp [←Complex.ofReal_natCast]
      rw [hi]
      exact not_lt.mpr (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hz) hpR.le)
    unfold ramifiedAverage
    simp_rw [ht]
    simp only [Finset.sum_const_zero,upperZeroExtension,dite_eq_right hz,mul_zero]

/-- Fricke also preserves the zero extension, since it preserves both
open half-planes and maps the real axis into itself. -/
theorem upperZeroExtension_fricke (N : ℕ) (hN : 0<N) (f : ℍ → ℂ) (w : ℂ)
    (hW : ∀ z : ℍ,w*f (frickeLabel N hN • z)=f z)
    (z : ℂ) : w*upperZeroExtension f (-1/((N:ℂ)*z))=upperZeroExtension f z := by
  by_cases hz : 0<z.im
  · have he := hW ⟨z,hz⟩
    have ht : upperZeroExtension f (-1/((N:ℂ)*z))=
        f (frickeLabel N hN • (⟨z,hz⟩ : ℍ)) := by
      rw [←fricke_label_coe N hN (⟨z,hz⟩ : ℍ),upperZeroExtension_apply]
    rw [ht]
    simpa only [upperZeroExtension,dite_eq_left hz] using he
  · have hy : ¬0<(-1/((N:ℂ)*z)).im := by
      apply not_lt.mpr
      simp only [neg_div,one_div,Complex.neg_im,Complex.inv_im,neg_div,neg_neg,
        Complex.mul_im,Complex.natCast_re,Complex.natCast_im,zero_mul,add_zero]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hz)) (Complex.normSq_nonneg _)
    simp only [upperZeroExtension,dite_eq_right hz,dite_eq_right hy,mul_zero]

#print axioms upperZeroExtension_apply
#print axioms ramified_label_coe
#print axioms upperZeroExtension_ramified
#print axioms upperZeroExtension_fricke

end QuantitativeMaass
