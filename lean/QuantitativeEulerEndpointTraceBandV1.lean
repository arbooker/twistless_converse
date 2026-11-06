module

public import QuantitativeEulerEndpointTraceMassV1
public import QuantitativeEulerEndpointPhysicalGramV1
public import QuantitativeHolomorphicMatrixExpressionV1
public import AsymptoticCylinderTerminalLiftV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTraceMass
open MeasureTheory UpperHalfPlane AsymptoticUnweightedKernel AsymptoticFiniteBranch
open AsymptoticRegularTrace QuantitativeHolomorphic AsymptoticHyperbolicArea
open QuantitativeEulerEndpointBandExpression
open scoped Classical

/-- A slightly larger retained band contains the original strict terminal band
pointwise, avoiding any boundary modification of the constructed operators. -/
theorem band_subset_retained {ε H : ℝ} (hε : 0<ε) (_hH : 0<H) :
    terminal ε\terminal H⊆retainedRegion (ε/2) (2*H) := by
  intro z hz
  have hlow : ε<z.im := hz.1.2
  have hhigh : z.im≤H := by
    by_contra hh
    exact hz.2 ⟨hz.1.1,lt_of_not_ge hh⟩
  exact ⟨hz.1.1,by linarith,by linarith⟩

theorem sandwich_of_supported {A : Type*} [Ring A] (P Q a : A)
    (hQP : Q*P=P) (hPQ : P*Q=P) (hPa : P*a=a) (haP : a*P=a) : Q*(a*Q)=a := by
  have hQa : Q*a=a := calc
    Q*a=Q*(P*a) := congrArg (fun x => Q*x) hPa.symm
    _=(Q*P)*a := (mul_assoc _ _ _).symm
    _=a := by rw [hQP,hPa]
  have haQ : a*Q=a := calc
    a*Q=(a*P)*Q := congrArg (fun x => x*Q) haP.symm
    _=a*(P*Q) := mul_assoc _ _ _
    _=a := by rw [hPQ,haP]
  rw [haQ,hQa]

theorem band_retained_physical {ε H : ℝ} (hε : 0<ε) (hH : 0<H) (e : Expression) (m : ℕ)
    (hl : holomorphicSum (unitExpression ε H) m*holomorphicSum e m=holomorphicSum e m)
    (hr : holomorphicSum e m*holomorphicSum (unitExpression ε H) m=holomorphicSum e m) :
    holomorphicSum (retainedExpression (ε/2) (2*H) e) m=holomorphicSum e m := by
  let P := holomorphicSum (unitExpression ε H) m
  let Q := holomorphic (corner (retainedRegion (ε/2) (2*H)) (retainedRegion_measurable _ _)) m
  have hPQ : P*Q=P := by
    dsimp only [P,Q]
    rw [unit_holomorphic,holomorphic_corner]
    exact AsymptoticRegionL2.projection_comp_of_subset volume _ _ _ _ (band_subset_retained hε hH)
  have hQP : Q*P=P := by
    have hh := congrArg star hPQ
    have hp : star P=P := (QuantitativeEulerEndpointPhysicalGram.unit_isStarProjection ε H m).isSelfAdjoint.star_eq
    have hq : star Q=Q := by
      dsimp only [Q]
      rw [holomorphic_corner]
      exact AsymptoticRegionL2.projection_adjoint _ _ _
    simpa only [star_mul,hp,hq] using hh
  rw [holomorphicSum_retainedExpression]
  exact sandwich_of_supported P Q (holomorphicSum e m) hQP hPQ hl hr

theorem band_retained_regular {ε H : ℝ} (hε : 0<ε) (hH : 0<H) (e : Expression)
    (x : ℍ)
    (hl : regularSum (unitExpression ε H) x*regularSum e x=regularSum e x)
    (hr : regularSum e x*regularSum (unitExpression ε H) x=regularSum e x) :
    regularSum (retainedExpression (ε/2) (2*H) e) x=regularSum e x := by
  rw [regularSum_retainedExpression]
  rw [unit_regular] at hl hr
  exact sandwich_of_supported _ _ (regularSum e x)
    (QuantitativeEulerEndpointBandCorner.corner_mul_of_subset (band_subset_retained hε hH) x)
    (QuantitativeEulerEndpointBandCorner.corner_mul_reverse_of_subset (band_subset_retained hε hH) x) hl hr

/-- The actual supported expression has a finite-weight trace comparison with
only coefficient mass and integer matrix height, and no expression-length cost. -/
theorem band_expression_trace_bound (e : Expression) {ε H B : ℝ}
    (hε : 0<ε) (hH : 0<H) (hB : 0≤B) (hm : ExpressionMatrixBound e B)
    (h : ℕ) (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*(B*(2*H+2))≤1) (S : Finset ℤ)
    (hfar : ∀ j : ℤ,j∉S → 2*compactBaseBound (ε/2) (2*H) 1≤1+|(j:ℝ)|)
    (hreg : ∀ x,regularSum (unitExpression ε H) x*regularSum e x=regularSum e x ∧
      regularSum e x*regularSum (unitExpression ε H) x=regularSum e x)
    (hphys : holomorphicSum (unitExpression ε H) (h+1)*holomorphicSum e (h+1)=holomorphicSum e (h+1) ∧
      holomorphicSum e (h+1)*holomorphicSum (unitExpression ε H) (h+1)=holomorphicSum e (h+1)) :
    |liftedTrace h hε (holomorphicSum e (h+1))/(2*h+2:ℕ)-
      signedTrace volume (regularSum e)/(4*Real.pi)|≤
      expressionBound e*uniformRetainedTraceError (B*(2*H+2)) (ε/2) (2*H) h S.card := by
  have hh := retained_expression_mass_uniform_trace_bound e hε (by positivity)
    (by positivity) (by positivity) h hsmall S hfar
    (fun b hb hne => hm.geometry hB (ε/2) (2*H) S b hb hne)
  have he : regularSum (retainedExpression (ε/2) (2*H) e)=regularSum e :=
    funext (fun x => band_retained_regular hε hH e x (hreg x).1 (hreg x).2)
  rwa [band_retained_physical hε hH e (h+1) hphys.1 hphys.2,he] at hh

#print axioms band_retained_physical
#print axioms band_retained_regular
#print axioms band_expression_trace_bound
end QuantitativeEulerEndpointTraceMass
