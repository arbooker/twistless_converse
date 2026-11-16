module

public import QuantitativeMaassRawBoundedIterationV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointTerminalAlgebra QuantitativeEulerEndpointExponentialParameters

/-- The existing next-block sharpening already gives a geometric final
idempotency defect; no extra arithmetic block is needed for metric transport. -/
theorem valid_final_defect {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
    (n : ℕ) (b : ℕ→Block A P e)
    (hc : 0<(b n).cutoff)
    (hu : QuantitativeEulerEndpointBlockNormalization.factor
      (b n).bound ((b n).primes.length+1)*(b n).cutoff≤1)
    (F : Algebra A P) (hv : Valid A P e n b n F) :
    tr A P (F-F^2)≤1/(4:ℝ)^n := by
  let area := (AsymptoticReconstructedCount.parameters A P).ε⁻¹
  let E := effortAt A P e n b n
  have ha : 0≤area := inv_nonneg.mpr (AsymptoticReconstructedCount.parameters A P).epsilon_pos.le
  have hlog := RawBoundedTerminal.logCost_nonneg (b n).primes (b n).bound hc hu
  have hE : 0<E := QuantitativeEulerEndpointLocalEffort.effort_pos n n hlog
  have hlo : (4:ℝ)^n≤E := by
    dsimp only [E,effortAt,RawBoundedTerminal.effort,QuantitativeEulerEndpointLocalEffort.effort]
    simp only [Nat.sub_self,pow_zero,mul_one]
    exact le_add_of_nonneg_right hlog
  have hs := sharpness_error ha hE (le_refl area)
  have hterm : 0≤4*area/(sharpness area E:ℝ) := by positivity
  have hp : 0≤(power E:ℝ) := Nat.cast_nonneg _
  have hfirst : 4*area/(sharpness area E:ℝ)≤1/E := by nlinarith
  exact hv.defect.trans (hfirst.trans (one_div_le_one_div_of_le (by positivity) hlo))

#print axioms valid_final_defect
end QuantitativeMaass.RawBoundedIteration
