module

public import QuantitativeMaassSineBoundaryFluxV1
public import QuantitativeMaassAbelCutoffMassV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem coshTimeTest_deriv_zero (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) :
    deriv (coshTimeTest F) 0=0 := by
  have h := ((hF.differentiable (by simp)) (Real.cosh 0)).hasDerivAt.scomp 0
    (Real.hasDerivAt_cosh 0)
  have hz : HasDerivAt (coshTimeTest F) 0 0 := by
    convert! h using 1
    simp only [Real.sinh_zero,zero_smul]
  exact hz.deriv

namespace Wave
open QuantitativeArithmeticMaassWave

/-- The cosine family has zero boundary defect for the literal q-tests in
the Abel equation: both the test derivative and wave velocity vanish at zero. -/
theorem shiftedQuotientWave_coshTest_boundary (N : ℕ) {v w : AutomorphicSpace N}
    (hvw : FriedrichsGraph N v w) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∫ t in Ioi (0:ℝ),coshTimeOperator F (Real.cosh t) • shiftedQuotientWave N t v-
      coshTimeTest F t • ((1/4:ℂ) • shiftedQuotientWave N t v-shiftedQuotientWave N t w))=0 := by
  have hc : HasCompactSupport (coshTimeTest F) :=
    (isCompact_Icc : IsCompact (Icc (-R) R)).of_isClosed_subset isClosed_closure
      (closure_minimal (coshTimeTest_support F R hR hs) isClosed_Icc)
  have h := compactTest_second_boundary (coshTimeTest F) (hF.comp Real.contDiff_cosh) hc
    (fun t => shiftedQuotientWave N t v) (quotientWaveVelocity N v w)
    (fun t => (1/4:ℂ) • shiftedQuotientWave N t v-shiftedQuotientWave N t w)
    (quotientWave_hasDerivAt N hvw) (quotientWaveVelocity_hasDerivAt N v w)
    (((shiftedQuotientWave_stronglyContinuous N v).const_smul (1/4:ℂ)).sub
      (shiftedQuotientWave_stronglyContinuous N w))
  simpa only [coshTimeTest_second F hF,coshTimeTest_deriv_zero F hF,
    quotientWaveVelocity_zero,smul_zero,zero_smul,sub_self] using h

/-- One explicit admissible compact q-test detects every nonzero sine
initial vector. This is an unconditional boundary computation, separate
from the still-needed representation of a general Abel-wave difference. -/
theorem quotientSine_cutoff_boundary (N : ℕ) {v w : AutomorphicSpace N}
    (hvw : FriedrichsGraph N v w) :
    (∫ t in Ioi (0:ℝ),coshTimeOperator (abelCutoff (Real.cosh 1-1)) (Real.cosh t) • quotientSine N t v-
      coshTimeTest (abelCutoff (Real.cosh 1-1)) t •
        ((1/4:ℂ) • quotientSine N t v-quotientSine N t w))=v := by
  have h := quotientSine_coshTest_boundary N hvw (abelCutoff (Real.cosh 1-1))
    (abelCutoff_smooth _) 1 (by norm_num) (abelCutoff_radius_support 1 (by norm_num))
  simpa only [abelCutoff,abelCutoffReal_one,Complex.ofReal_one,one_smul] using h

#print axioms coshTimeTest_deriv_zero
#print axioms shiftedQuotientWave_coshTest_boundary
#print axioms quotientSine_cutoff_boundary

end Wave
end QuantitativeMaass
