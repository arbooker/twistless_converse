module

public import QuantitativeMaassFullExcessColumnV1
public import QuantitativeMaassFullFilterExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap MeasureTheory AsymptoticSectorSigns AsymptoticFiniteBranch
namespace QuantitativeMaass

/-- Isometric physical realization preserves the actual linear column trace. -/
theorem columnLinearTrace_isometry {α H E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (c : α→H) (U : H→ₗᵢ[ℂ]E) (T : H→L[ℂ]H) :
    columnLinearTrace μ (fun x => U (c x))
      (U.toContinuousLinearMap.comp (T.comp U.toContinuousLinearMap.adjoint))=
      columnLinearTrace μ c T := by
  have hu (x : H) : U.toContinuousLinearMap.adjoint (U x)=x :=
    DFunLike.congr_fun U.adjoint_comp_self x
  apply integral_congr_ae
  filter_upwards with x
  simp only [comp_apply,LinearIsometry.coe_toContinuousLinearMap,hu,U.inner_map_map]

namespace EulerHilbert.FullTerminal
variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

theorem commonResidualFilter_square (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) :
    commonResidualFilter A hN P e hs qs d*commonResidualFilter A hN P e hs qs d=
      commonResidualFilter A hN P e hs qs (2*d) := by
  unfold commonResidualFilter
  rw [two_mul,pow_add]

/-- The actual finite expression approximates the squared filter appearing
in the excess trace. Subtracting the same exact target adds no error. -/
theorem fullExcessExpression_ambient_error (e : Sector N) {s : Set UpperHalfPlane}
    (hs : IsCompact s) (qs : Finset ℕ+) (n j J d : ℕ) (hJ : 0<J)
    (M : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε→L[ℂ]
      AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) :
    let U := (physicalIsometry A hN P e).toContinuousLinearMap
    let F := commonResidualFilter A hN P e hs qs d
    ‖(holomorphicSum (fullFilterExpression A hN P e hs qs n j J (2*d)) 0-
      U.comp (M.comp U.adjoint))-U.comp ((F*F-M).comp U.adjoint)‖≤
      (2*(2*d)+2 : ℝ)*
        (QuantitativeHolomorphic.countReconstructionError A P j J*(1+3*(3^n:ℕ))*(7:ℝ)^(4^n)+
          (1-QuantitativeHolomorphic.countGramLower A P)^(2^n)/
            Real.sqrt (QuantitativeHolomorphic.countGramLower A P)) := by
  intro U F
  rw [sub_comp,comp_sub,sub_sub_sub_cancel_right]
  simpa only [←commonResidualFilter_square A hN P e hs qs d,Nat.cast_mul,Nat.cast_ofNat] using
    fullFilterExpression_ambient_error A hN P e hs qs n j J (2*d) hJ

#print axioms commonResidualFilter_square
#print axioms fullExcessExpression_ambient_error
end EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- The cylinder realization used in the column count is exactly the
physical realization used in the finite branch expression. -/
theorem fullTerminalTranslation_physical (e : Sector N) :
    cylinderZeroExtension.toContinuousLinearMap.comp
      (fullTerminalTranslationIsometry A hN P e).toContinuousLinearMap=
      (EulerHilbert.FullTerminal.physicalIsometry A hN P e).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  exact productCylinderToTranslation_lift (EulerHilbert.normalized A hN P e x)

#print axioms columnLinearTrace_isometry
#print axioms fullTerminalTranslation_physical
end QuantitativeMaass
