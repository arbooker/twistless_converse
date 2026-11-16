module

public import QuantitativeMaassCylinderHilbertV1
public import QuantitativeMaassEulerWeightedL2V1
public import AsymptoticZeroExtensionV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticMassTransport

namespace QuantitativeMaass

theorem cylinderStripIdentity_preserving :
    MeasurePreserving (id : ℍ → ℍ) (volume.restrict strip) (quotientMeasure 0) := by
  rw [translation_quotient_measure]
  exact MeasurePreserving.id _

/-- Exact zero extension from the hyperbolic translation cylinder to the
physical ambient L2 space used by the Euler reconstruction. -/
def cylinderZeroExtension :
    Lp ℂ 2 (quotientMeasure 0) →ₗᵢ[ℂ] AsymptoticHyperbolicSlash.Space :=
  (AsymptoticZeroExtension.isometry volume strip strip_measurable).comp
    (Lp.compMeasurePreservingₗᵢ ℂ id cylinderStripIdentity_preserving)

theorem cylinderZeroExtension_coeFn (f : Lp ℂ 2 (quotientMeasure 0)) :
    cylinderZeroExtension f=ᵐ[volume] strip.indicator f := by
  have he := (ae_eq_restrict_iff_indicator_ae_eq strip_measurable).mp
    (Lp.coeFn_compMeasurePreserving f cylinderStripIdentity_preserving)
  have hz := AsymptoticZeroExtension.isometry_coeFn volume strip strip_measurable
    (Lp.compMeasurePreservingₗᵢ ℂ id cylinderStripIdentity_preserving f)
  exact hz.trans (by simpa only [Function.comp_def,id_eq] using! he)

theorem cylinderZeroExtension_coeFn_of_ae (f : Lp ℂ 2 (quotientMeasure 0))
    (φ : ℍ → ℂ) (hφ : f=ᵐ[quotientMeasure 0] φ) :
    cylinderZeroExtension f=ᵐ[volume] strip.indicator φ := by
  have hp := cylinderStripIdentity_preserving.quasiMeasurePreserving.ae hφ
  have he := (ae_eq_restrict_iff_indicator_ae_eq strip_measurable).mp hp
  exact (cylinderZeroExtension_coeFn f).trans (by simpa only [id_eq] using he)

theorem cylinderZeroExtension_norm (f : Lp ℂ 2 (quotientMeasure 0)) :
    ‖cylinderZeroExtension f‖=‖f‖ := cylinderZeroExtension.norm_map f

/-- The original capped Euler wave is an actual cylinder L2 function, with
the same certificate-controlled exponent as the physical reconstruction. -/
theorem principalEulerCylinder_memLp {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    MemLp (AsymptoticWeightedBranches.weighted P.ε (P.s+3) 0
      (principalEulerPhysical b r σ)) 2 (quotientMeasure 0) := by
  rw [translation_quotient_measure]
  exact (memLp_indicator_iff_restrict strip_measurable).mp
    (principalEulerPhysical_weighted_memLp hN A P r σ hb)

def principalEulerCylinderLp {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) : Lp ℂ 2 (quotientMeasure 0) :=
  (principalEulerCylinder_memLp hN A P r σ hb).toLp _

theorem principalEulerCylinderLp_coeFn {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    principalEulerCylinderLp hN A P r σ hb=ᵐ[quotientMeasure 0]
      AsymptoticWeightedBranches.weighted P.ε (P.s+3) 0 (principalEulerPhysical b r σ) :=
  MemLp.coeFn_toLp _

/-- Exact identification with the already checked original reconstruction;
no replacement of the original Euler solution set is made. -/
theorem principalEulerCylinderLp_physical {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    cylinderZeroExtension (principalEulerCylinderLp hN A P r σ hb)=
      principalEulerWeightedLp hN A P r σ hb := by
  apply Lp.ext
  exact (cylinderZeroExtension_coeFn_of_ae _ _
    (principalEulerCylinderLp_coeFn hN A P r σ hb)).trans
    (principalEulerWeightedLp_coeFn hN A P r σ hb).symm

#print axioms cylinderZeroExtension_coeFn
#print axioms cylinderZeroExtension_norm
#print axioms principalEulerCylinder_memLp
#print axioms principalEulerCylinderLp_coeFn
#print axioms principalEulerCylinderLp_physical

end QuantitativeMaass
