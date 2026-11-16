module

public import QuantitativeMaassFullExcessExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap MeasureTheory AsymptoticSectorSigns AsymptoticFiniteBranch
open AsymptoticClassicalPetersson
namespace QuantitativeMaass

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- The actual cylinder excess trace equals the physical trace of the same
centered capped columns after zero extension. No replacement packet is used. -/
theorem fullTerminal_excess_physical_trace {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α→Lp ℂ 2 (quotientMeasure 0)) (e : Sector N)
    (T : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε→L[ℂ]
      AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) :
    let U := (fullTerminalTranslationIsometry A hN P e).toContinuousLinearMap
    let V := (EulerHilbert.FullTerminal.physicalIsometry A hN P e).toContinuousLinearMap
    columnLinearTrace μ (fun x => cylinderZeroExtension (c x)) (V.comp (T.comp V.adjoint))=
      columnLinearTrace μ c (U.comp (T.comp U.adjoint)) := by
  intro U V
  have hh := columnLinearTrace_isometry μ c cylinderZeroExtension (U.comp (T.comp U.adjoint))
  have hp : cylinderZeroExtension.toContinuousLinearMap.comp U=V :=
    fullTerminalTranslation_physical A hN P e
  have he : cylinderZeroExtension.toContinuousLinearMap.comp
      ((U.comp (T.comp U.adjoint)).comp cylinderZeroExtension.toContinuousLinearMap.adjoint)=
      V.comp (T.comp V.adjoint) := by
    rw [←hp,adjoint_comp]
    simp only [comp_assoc]
  rw [he] at hh
  exact hh

namespace EulerHilbert.FullTerminal

/-- The explicit finite-branch approximation controls the linear trace of
any actual square-integrable physical column, including the zero-extended
centered capped columns in the original count. -/
theorem fullExcessExpression_column_error {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α→AsymptoticHyperbolicSlash.Space) (hc : MemLp c 2 μ)
    (e : Sector N) {s : Set UpperHalfPlane} (hs : IsCompact s) (qs : Finset ℕ+)
    (n j J d : ℕ) (hJ : 0<J)
    (M : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε→L[ℂ]
      AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) :
    let U := (physicalIsometry A hN P e).toContinuousLinearMap
    let F := commonResidualFilter A hN P e hs qs d
    |columnLinearTrace μ c (holomorphicSum (fullFilterExpression A hN P e hs qs n j J (2*d)) 0-
        U.comp (M.comp U.adjoint))-
      columnLinearTrace μ c (U.comp ((F*F-M).comp U.adjoint))|≤
      ((2*(2*d)+2 : ℝ)*
        (QuantitativeHolomorphic.countReconstructionError A P j J*(1+3*(3^n:ℕ))*(7:ℝ)^(4^n)+
          (1-QuantitativeHolomorphic.countGramLower A P)^(2^n)/
            Real.sqrt (QuantitativeHolomorphic.countGramLower A P)))*(∫ x,‖c x‖^2 ∂μ) := by
  intro U F
  exact columnLinearTrace_approx μ c hc _ _
    (fullExcessExpression_ambient_error A hN P e hs qs n j J d hJ M)

#print axioms fullExcessExpression_column_error
end EulerHilbert.FullTerminal
#print axioms fullTerminal_excess_physical_trace
end QuantitativeMaass
