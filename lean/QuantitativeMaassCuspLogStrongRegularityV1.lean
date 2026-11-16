module

public import QuantitativeMaassCuspLogEquationCheckV1
public import QuantitativeArithmeticMaassWavePDEV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff MatrixGroups InnerProductSpace

namespace QuantitativeMaass.Wave
open QuantitativeArithmeticMaassWave

/-- Strong C2 evolution on the actual Friedrichs domain, derived from the
constructed spectral wave and its strong derivative formulas. -/
theorem quotientWave_contDiff_two (N : ℕ) {f g : AutomorphicSpace N}
    (hfg : FriedrichsGraph N f g) :
    ContDiff ℝ 2 (fun t => shiftedQuotientWave N t f) := by
  have hsecond := quotientWave_second_derivative N hfg
  have he : deriv (deriv (fun t => shiftedQuotientWave N t f))=
      fun t => (1/4:ℂ) • shiftedQuotientWave N t f-shiftedQuotientWave N t g :=
    funext (fun t => (hsecond t).deriv)
  rw [show (2:ℕ∞ω)=1+1 by rfl,contDiff_succ_iff_deriv]
  refine ⟨fun t => (quotientWave_hasDerivAt N hfg t).differentiableAt,by simp,?_⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hsecond t).differentiableAt,?_⟩
  rw [he]
  exact ((shiftedQuotientWave_stronglyContinuous N f).const_smul (1/4:ℂ)).sub
    (shiftedQuotientWave_stronglyContinuous N g)

/-- The actual local cusp half-density is C2 as an L2-valued curve for
Friedrichs-domain initial data, without choosing a smooth representative. -/
theorem cuspLogConstant_wave_contDiff_two (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) {f g : AutomorphicSpace N} (hfg : FriedrichsGraph N f g) :
    ContDiff ℝ 2 (fun t => cuspLogConstant N hN s A B (shiftedQuotientWave N t f)) :=
  (cuspLogConstant N hN s A B).contDiff.comp (quotientWave_contDiff_two N hfg)

theorem cuspLogConstant_wave_hasDerivAt (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) {f g : AutomorphicSpace N} (hfg : FriedrichsGraph N f g) (t : ℝ) :
    HasDerivAt (fun r => cuspLogConstant N hN s A B (shiftedQuotientWave N r f))
      (cuspLogConstant N hN s A B (quotientWaveVelocity N f g t)) t :=
  (cuspLogConstant N hN s A B).hasFDerivAt.comp_hasDerivAt t (quotientWave_hasDerivAt N hfg t)

theorem cuspLogConstant_wave_initial_velocity (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B : ℝ) {f g : AutomorphicSpace N} (hfg : FriedrichsGraph N f g) :
    deriv (fun t => cuspLogConstant N hN s A B (shiftedQuotientWave N t f)) 0=0 := by
  rw [(cuspLogConstant_wave_hasDerivAt N hN s A B hfg 0).deriv,
    quotientWaveVelocity_zero,map_zero]

#print axioms quotientWave_contDiff_two
#print axioms cuspLogConstant_wave_contDiff_two
#print axioms cuspLogConstant_wave_initial_velocity

end QuantitativeMaass.Wave
