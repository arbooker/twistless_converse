module

public import QuantitativeMaassWaveOperatorV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set
open scoped InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Real operator spectrum with the real scalar structure fixed by the
complex Hilbert structure, as in the continuous functional calculus. -/
def inverseSpectrum (A : H →L[ℂ] H) : Set ℝ := spectrum ℝ A

theorem positiveContraction_spectrum_bound (A : H →L[ℂ] H)
    (hp : A.IsPositive) (hn : ‖A‖≤1) {s : ℝ} (hs : s∈inverseSpectrum A) : 0≤s ∧ s≤1 := by
  refine ⟨spectrum_nonneg_of_nonneg (ContinuousLinearMap.nonneg_iff_isPositive.mpr hp) hs,?_⟩
  have h := IsometricContinuousFunctionalCalculus.norm_spectrum_le A hs hp.isSelfAdjoint
  exact (le_abs_self s).trans (h.trans hn)

theorem friedrichsResolvent_isPositive (N : ℕ) : (friedrichsResolvent N).IsPositive := by
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (friedrichsResolvent_isSelfAdjoint N),?_⟩
  intro v
  exact (sq_nonneg ‖friedrichsResolvent N v‖).trans (friedrichsResolvent_lower N v)

theorem friedrichsResolvent_spectrum_bound (N : ℕ) {s : ℝ}
    (hs : s∈inverseSpectrum (friedrichsResolvent N)) : 0≤s ∧ s≤1 :=
  positiveContraction_spectrum_bound _ (friedrichsResolvent_isPositive N)
    (friedrichsResolvent_opNorm_le N) hs

#print axioms friedrichsResolvent_spectrum_bound

end QuantitativeMaass.Wave
