module

public import QuantitativeMaassCrossReflectedPhysicalV1
public import QuantitativeMaassCrossCylinderProjectionV1
public import QuantitativeMaassCompactReflectedTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticFiniteBranch AsymptoticMassTransport
open scoped SchwartzMap
namespace QuantitativeMaass

/-- The reflected compact-transfer trace is the literal reflected kernel
trace of its finite localized expression, retaining both cutoffs. -/
theorem crossQuotientLocalization_reflected_kernel_trace {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (N : ℕ) (a b : ℝ) (ha : 0<a) (u : SmoothUpperSeed)
    (hu : tsupport (upperFunction u.toFun) ⊆ upperRectangle 0 1 a b)
    (hstrip : Function.support (upperFunction u.toFun) ⊆ strip)
    (B : ℝ) (hB : 0≤B)
    (hbound : ∀ z∈upperRectangle 0 1 a b,‖upperFunction u.toFun z‖≤B)
    (E : Expression) (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hA : QuotientRealizes N E A) :
    let S := upperRectangle 0 1 a b
    let hS := upperRectangle_compact 0 1 a b ha
    let v := upperFunction u.toFun
    let hv := (upperFunction_continuous u.smooth).measurable
    let hb := CrossCompactBranch.cutoff_global_bound v S hu B hB hbound
    let E' := reflectedLocalExpression N S S hS hS v v hv hv B B hB hB hb hb E
    let T := crossQuotientLocalization N 0 S hS u hbound
    columnLinearTrace (quotientMeasure 0)
      (fun z => T (cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z)))
      ((reflectionIsometry N).toContinuousLinearMap.comp A) =
      ((compactInputExpression S hS.measurableSet E').map
        (fun q => ∫ x in S,(cylinderInputBranchCoefficient q (J•x)*radialPoincareKernel 0
          (abelProfile (evenCoshLift (timeConvolution f f))) x (q.label • (J•x))).re)).sum := by
  intro S hS v hv hb E' T
  let P := AsymptoticRegionL2.projection (quotientMeasure 0) S hS.measurableSet
  let Z := cylinderZeroExtension.toContinuousLinearMap
  let J₀ := Z.comp (AutomorphicSpace 0).subtypeL
  have hsand := crossQuotientLocalization_reflected_physical_sandwich N S S hS hS u u
    hstrip hstrip B B hB hB hbound hbound hu hu E A hA
  change T.adjoint.comp ((reflectionIsometry N).toContinuousLinearMap.comp (A.comp T)) =
    J₀.adjoint.comp (physicalReflection.toContinuousLinearMap.comp ((holomorphicSum E' 0).comp J₀)) at hsand
  rw [←compact_input_reflected_expression_kernel_trace basis f hc he hr R hR hs ha b E']
  unfold columnLinearTrace
  apply integral_congr_ae
  filter_upwards with z
  let c := cylinderTimeColumn f hc he R hR hs z
  have hp := crossQuotientLocalization_cylinder_project N a b ha u hbound c
  change T (cylinderAutomorphic (P c))=T (cylinderAutomorphic c) at hp
  change (inner ℂ (reflectionIsometry N (A (T (cylinderAutomorphic c)))) (T (cylinderAutomorphic c))).re =
    (inner ℂ (Z.adjoint (physicalReflection (holomorphicSum E' 0 (Z (P c))))) (P c)).re
  rw [←hp]
  have hh := congrArg (fun U : AutomorphicSpace 0 →L[ℂ] AutomorphicSpace 0 =>
    inner ℂ (cylinderAutomorphic (P c)) (U (cylinderAutomorphic (P c)))) hsand
  simp only [comp_apply,T.adjoint_inner_right,J₀.adjoint_inner_right] at hh
  change inner ℂ (T (cylinderAutomorphic (P c)))
      (reflectionIsometry N (A (T (cylinderAutomorphic (P c))))) =
    inner ℂ (Z (P c)) (physicalReflection (holomorphicSum E' 0 (Z (P c)))) at hh
  rw [Z.adjoint_inner_left]
  exact (inner_re_symm (𝕜 := ℂ) _ _).trans
    ((congrArg Complex.re hh).trans (inner_re_symm (𝕜 := ℂ) _ _))

#print axioms crossQuotientLocalization_reflected_kernel_trace

end QuantitativeMaass
