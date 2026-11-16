module

public import QuantitativeMaassPhysicalExpressionV1
public import QuantitativeMaassReflectionOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

open MeasureTheory UpperHalfPlane AsymptoticFiniteBranch ContinuousLinearMap
open scoped InnerProductSpace
namespace QuantitativeMaass

/-- Geometric reflection on the full hyperbolic L2 space. -/
def physicalReflection : AsymptoticHyperbolicSlash.Space →ₗᵢ[ℂ] AsymptoticHyperbolicSlash.Space :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z : ℍ => J•z) (measurePreserving_smul J volume)

theorem physicalReflection_representative (f : AsymptoticHyperbolicSlash.Space)
    (φ : ℍ→ℂ) (hf : (f : ℍ→ℂ) =ᵐ[volume] φ) :
    (physicalReflection f : ℍ→ℂ) =ᵐ[volume] (fun z => φ (J•z)) := by
  have hp := (measurePreserving_smul J volume).quasiMeasurePreserving.ae hf
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_smul J volume),hp]
    with z hz hpz
  exact hz.trans hpz

theorem physicalReflection_involutive : Function.Involutive physicalReflection := by
  intro f
  apply Lp.ext
  have h := physicalReflection_representative f f Filter.EventuallyEq.rfl
  have hh := physicalReflection_representative (physicalReflection f) (fun z => f (J•z)) h
  filter_upwards [hh] with z hz
  simpa only [reflection_involutive] using hz

theorem physicalReflection_selfAdjoint :
    IsSelfAdjoint physicalReflection.toContinuousLinearMap := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hh := physicalReflection.inner_map_map x (physicalReflection y)
  rw [physicalReflection_involutive] at hh
  exact hh

/-- The physical reflected expression has the literal reflected pullback
pairing, for arbitrary almost-everywhere representatives. -/
theorem physical_reflected_expression_pairing (E : Expression)
    (f g : AsymptoticHyperbolicSlash.Space) (φ ψ : ℍ→ℂ)
    (hf : (f : ℍ→ℂ) =ᵐ[volume] φ) (hg : (g : ℍ→ℂ) =ᵐ[volume] ψ) :
    inner ℂ f (physicalReflection (holomorphicSum E 0 g)) =
      ∫ z : ℍ, star (φ z)*expressionFunction E ψ (J•z) := by
  rw [L2.inner_def]
  have hh := physicalReflection_representative (holomorphicSum E 0 g)
    (expressionFunction E ψ) (physical_expression_representative E g ψ hg)
  apply integral_congr_ae
  filter_upwards [hf,hh] with z hfz hgz
  rw [hfz,hgz]
  simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]

#print axioms physicalReflection_representative
#print axioms physicalReflection_involutive
#print axioms physicalReflection_selfAdjoint
#print axioms physical_reflected_expression_pairing

end QuantitativeMaass
