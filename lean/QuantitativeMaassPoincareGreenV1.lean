module

public import QuantitativeMaassGreenUpperV1
public import QuantitativeMaassPoincareLaplacianV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff ENNReal

namespace QuantitativeMaass
open MaassDifferential

/-- Exact conjugate-slot unfolding for the actual normalized projective
congruence quotient. Integrability is supplied by the proved local L²
pairing theorem. -/
theorem congruence_poincare_pairing_left (N : ℕ) (f : ℍ → ℂ)
    (hf : Measurable f) (hinv : ∀ g : gamma N, ∀ z, f (g•z)=f z)
    (hL : MemLp f 2 (quotientMeasure N))
    (φ : ℍ → ℂ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    (∫ z, star (poincareSum (G := gamma N) φ z)*f z ∂quotientMeasure N)=
      ∫ z : ℍ, star (φ z)*f z := by
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun g => AsymptoticRationalBranches.action_continuous g.val⟩
  have h := (integral_poincare_pairing volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    f hf hinv hL φ hφ hc).2.2
  have h' := congrArg star h
  simp only [← starRingEnd_apply,← integral_conj] at h'
  convert h' using 1 <;> congr 1 <;> funext z <;> simp [mul_comm]

/-- The literal Poincaré Laplacian is symmetric in the actual quotient
Hilbert inner product. All quotient normalization, local finiteness,
Laplacian intertwining and integration by parts are established inputs.
This is a statement on representatives; it is not a graph-core assertion. -/
theorem poincare_green_symmetric (N : ℕ) {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hcu : HasCompactSupport (upperFunction u))
    (hcv : HasCompactSupport (upperFunction v)) :
    (∫ z, star (poincareSum (G := gamma N) (upperFunction u) z)*
      upperLaplacian (congruencePoincareCartesian N v) z ∂quotientMeasure N)=
    ∫ z, star (upperLaplacian (congruencePoincareCartesian N u) z)*
      poincareSum (G := gamma N) (upperFunction v) z ∂quotientMeasure N := by
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun g => AsymptoticRationalBranches.action_continuous g.val⟩
  rw [upperLaplacian_congruencePoincareCartesian N hu hcu,
    upperLaplacian_congruencePoincareCartesian N hv hcv]
  have hvΔ := upperLaplacian_continuous hv
  have hcvΔ := upperLaplacian_compact v hcv
  have hvP := poincareSum_continuous (G := gamma N) (upperFunction v) hcv
    (upperFunction_continuous hv)
  have hvΔP := poincareSum_continuous (G := gamma N) (upperLaplacian v) hcvΔ hvΔ
  have hLp (φ : ℍ → ℂ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :=
    poincareSum_memLp volume
      (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
      (density N) (density_measurable N) (density_orbit_sum N) φ hφ hc
  rw [congruence_poincare_pairing_left N _ hvΔP.measurable
      (fun g z => poincareSum_invariant _ g z) (hLp _ hvΔ hcvΔ)
      _ (upperFunction_continuous hu) hcu,
    congruence_poincare_pairing_left N _ hvP.measurable
      (fun g z => poincareSum_invariant _ g z)
      (hLp _ (upperFunction_continuous hv) hcv)
      _ (upperLaplacian_continuous hu) (upperLaplacian_compact u hcu)]
  have h := upper_green_symmetric hu (congruencePoincareCartesian_smooth N hv hcv) hcu
  simpa only [upperLaplacian_congruencePoincareCartesian N hv hcv,
    congruencePoincareCartesian_represents] using h

#print axioms poincare_green_symmetric

end QuantitativeMaass
