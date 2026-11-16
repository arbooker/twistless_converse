module

public import QuantitativeMaassCylinderCompactPhysicalV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticFiniteBranch
open scoped SchwartzMap
namespace QuantitativeMaass

/-- Compact input restriction is an actual identity branch of the same
finite expression in physical and regular representations. -/
def compactInputExpression (S : Set ℍ) (hS : MeasurableSet S) (E : Expression) : Expression :=
  composeExpression E [corner S hS]

theorem compactInputExpression_physical (S : Set ℍ) (hS : MeasurableSet S) (E : Expression) :
    holomorphicSum (compactInputExpression S hS E) 0=
      (holomorphicSum E 0).comp (AsymptoticRegionL2.projection volume S hS) := by
  rw [compactInputExpression,holomorphicSum_compose]
  simp only [holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,holomorphic_corner]

/-- Exact finite-branch kernel formula for the full-output compact-input
column trace obtained from the original excess. This is the cyclicity and
localization bridge; it does not identify the two differently ordered cutoffs
without proof. -/
theorem compact_input_expression_kernel_trace {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    {a : ℝ} (ha : 0<a) (b : ℝ) (E : Expression) :
    let S := upperRectangle 0 1 a b
    let hS := upperRectangle_compact 0 1 a b ha
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) S hS.measurableSet
    let Z := cylinderZeroExtension.toContinuousLinearMap
    columnLinearTrace (quotientMeasure 0)
      (fun z => P (cylinderTimeColumn f hc he R hR hs z))
      (Z.adjoint.comp ((holomorphicSum E 0).comp Z))=
      ((compactInputExpression S hS.measurableSet E).map
        (fun q => ∫ x in S,(cylinderInputBranchCoefficient q x*radialPoincareKernel 0
          (abelProfile (evenCoshLift (timeConvolution f f))) x (q.label • x)).re)).sum := by
  intro S hS P Z
  rw [compact_input_column_trace_cyclic f hc he hr R hR hs basis ha b]
  rw [←concrete_expression_packet_trace f hc he hr R hR hs basis S hS
    (compactInputExpression S hS.measurableSet E)]
  apply tsum_congr
  intro i
  let v := cylinderTimePacket f (f.smooth ⊤) hc (basis i)
  let A := AsymptoticRegionL2.projection volume S hS.measurableSet
  have hp : A (Z v)=Z (P v) :=
    DFunLike.congr_fun (cylinderZeroExtension_projection S hS.measurableSet) v
  have hfix : A (Z (P v))=Z (P v) := by
    rw [←hp]
    exact AsymptoticRegionL2.projection_idempotent volume S hS.measurableSet (Z v)
  rw [compact_column_zeroExtension f hc he hr R hR hs ha b (basis i),
    compactInputExpression_physical]
  change (inner ℂ (P v) (Z.adjoint (holomorphicSum E 0 (Z (P v))))).re=
    (inner ℂ (Z (P v)) (A (holomorphicSum E 0 (A (Z v))))).re
  rw [Z.adjoint_inner_right,hp]
  have haA : A.adjoint=A := AsymptoticRegionL2.projection_adjoint _ _ _
  rw [←haA, A.adjoint_inner_right,hfix]

#print axioms compactInputExpression_physical
#print axioms compact_input_expression_kernel_trace
end QuantitativeMaass
