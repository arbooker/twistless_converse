module

public import QuantitativeMaassNewPrimePowerLawsV1
public import QuantitativeMaassTwistDilationV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane AsymptoticFreshMatrices AsymptoticCongruenceStrip
open AsymptoticClassicalPetersson AsymptoticIntegralSubgroup

namespace QuantitativeMaass

theorem upperZeroExtension_periodic (N : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    Function.Periodic (upperZeroExtension f.val) 1 := by
  intro z
  have hi : (z+1).im=z.im := by simp
  by_cases hz : 0<z.im
  · have ht : ((translationLabel (1:ℚ) • (⟨z,hz⟩:ℍ) : ℍ):ℂ)=z+1 := by
      rw [AsymptoticCompactTranslation.label_action,AsymptoticMobiusFold.translation_action]
      simp
    rw [←ht,upperZeroExtension_apply]
    have he := f.property.2.1 ⟨translationLabel (1:ℚ),translation_mem N 1⟩ (⟨z,hz⟩:ℍ)
    simpa only [upperZeroExtension,dite_eq_left hz] using he
  · simp only [upperZeroExtension,hi,dite_eq_right hz]

theorem upperZeroExtension_twist_zero (f : ℍ → ℂ) (q : ℕ) (z : ℂ)
    (hz : z.im≤0) : FinitenessAnalyticReconstruction.twist (upperZeroExtension f) q z=0 := by
  classical
  unfold FinitenessAnalyticReconstruction.twist
  apply Finset.sum_eq_zero
  intro a _
  apply dite_eq_right
  have hi : (z+(a:ℂ)/q).im=z.im := by simp [←Complex.ofReal_natCast]
  rw [hi]
  exact not_lt.mpr hz

/-- The coprime-modulus reflection law holds on the whole plane for
the canonical zero extension of an actual modular function. -/
theorem upperZeroExtension_coprime_law (N q : ℕ) (hN : 0<N) (hq : 0<q)
    (hc : N.Coprime q)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (w : ℂ) (hW : ∀ z,w*f.val (frickeLabel N hN • z)=f.val z) (z : ℂ) :
    w*FinitenessAnalyticReconstruction.twist (upperZeroExtension f.val) q
      (-1/((Nat.lcm N (q^2):ℂ)*z))=
      FinitenessAnalyticReconstruction.twist (upperZeroExtension f.val) q z := by
  by_cases hz : 0<z.im
  · apply (coprime_analytic_law_of_modular N q hN hq hc (upperZeroExtension f.val)
      (fun a y => by simpa only [upperZeroExtension_apply] using f.property.2.1 a y)
      w (fun y => upperZeroExtension_fricke N hN f.val w hW y) z hz).symm
  · have hy : (-1/((Nat.lcm N (q^2):ℂ)*z)).im≤0 := by
      simp only [neg_div,one_div,Complex.neg_im,Complex.inv_im,neg_div,neg_neg,
        Complex.mul_im,Complex.natCast_re,Complex.natCast_im,zero_mul,add_zero]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hz)) (Complex.normSq_nonneg _)
    rw [upperZeroExtension_twist_zero _ _ _ hy,
      upperZeroExtension_twist_zero _ _ _ (le_of_not_gt hz),mul_zero]

#print axioms upperZeroExtension_periodic
#print axioms upperZeroExtension_twist_zero
#print axioms upperZeroExtension_coprime_law

end QuantitativeMaass
