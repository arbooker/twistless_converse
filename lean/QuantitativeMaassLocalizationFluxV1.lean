module

public import QuantitativeMaassGradientProductV1
public import QuantitativeArithmeticMaassGradientFormV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass

open MaassDifferential QuantitativeArithmeticMaassGradient

def cutoffGradientOperator (N : ℕ) (i : Bool) (b : Point → ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2}) {C : ℝ}
    (hg : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) :
    Lp ℂ 2 (quotientMeasure N) →L[ℂ] Lp ℂ 2 (quotientMeasure N) :=
  AsymptoticL2Multiplier.operator (cutoffGradient i b)
    (cutoffGradient_continuous i b hb).aestronglyMeasurable
    (Eventually.of_forall (cutoffGradient_norm_le i b hg))

/-- The exact form commutator is the first-order cutoff flux. This holds on
the completed form domain, with literal quotient gradient and multiplier maps. -/
theorem quotientClosedEnergy_localization_flux (N : ℕ) (b : Point → ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    (hr : ∀ Z, star (b Z)=b Z)
    {B C : ℝ} (hB : 0≤B) (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hg : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) (u v : QuotientEnergySpace N) :
    quotientClosedEnergy N u (energyLocalization N b hb v)-
      quotientClosedEnergy N (energyLocalization N b hb u) v=
      (inner ℂ (quotientGradient N true u)
          (cutoffGradientOperator N true b hb hg (energyInclusion N v).val)-
        inner ℂ (cutoffGradientOperator N true b hb hg (energyInclusion N u).val)
          (quotientGradient N true v))+
      (inner ℂ (quotientGradient N false u)
          (cutoffGradientOperator N false b hb hg (energyInclusion N v).val)-
        inner ℂ (cutoffGradientOperator N false b hb hg (energyInclusion N u).val)
          (quotientGradient N false v)) := by
  let M : Lp ℂ 2 (quotientMeasure N) →L[ℂ] Lp ℂ 2 (quotientMeasure N) :=
    AsymptoticL2Multiplier.operator (upperFunction b)
      (upperFunction_continuous hb).aestronglyMeasurable (Eventually.of_forall hbound)
  have hM : M.adjoint=M := AsymptoticL2Multiplier.operator_adjoint _ _ _
    (Eventually.of_forall (fun z => hr (z.re,z.im)))
  have hs (a d : Lp ℂ 2 (quotientMeasure N)) : inner ℂ (M a) d=inner ℂ a (M d) := by
    simpa only [hM] using M.adjoint_inner_left d a
  rw [quotientGradient_form,quotientGradient_form,
    quotientGradient_localized N true b hb hi hB hbound hg,
    quotientGradient_localized N false b hb hi hB hbound hg,
    quotientGradient_localized N true b hb hi hB hbound hg,
    quotientGradient_localized N false b hb hi hB hbound hg]
  change (inner ℂ (quotientGradient N true u)
      (M (quotientGradient N true v)+cutoffGradientOperator N true b hb hg (energyInclusion N v).val)+
    inner ℂ (quotientGradient N false u)
      (M (quotientGradient N false v)+cutoffGradientOperator N false b hb hg (energyInclusion N v).val))-
    (inner ℂ (M (quotientGradient N true u)+cutoffGradientOperator N true b hb hg (energyInclusion N u).val)
      (quotientGradient N true v)+
    inner ℂ (M (quotientGradient N false u)+cutoffGradientOperator N false b hb hg (energyInclusion N u).val)
      (quotientGradient N false v))=_
  simp only [inner_add_left,inner_add_right,hs]
  ring

#print axioms quotientClosedEnergy_localization_flux

end QuantitativeMaass
