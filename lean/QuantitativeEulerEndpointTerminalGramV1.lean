module

public import QuantitativeEulerEndpointTerminalAlgebraV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointTerminalAlgebra
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointRegularBase QuantitativeHolomorphic
open AsymptoticRegularTrace AsymptoticRegularReconstruction AsymptoticFiniteBranch
open AsymptoticOrbitDiagonal MeasureTheory

theorem extension_right {G H K : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (S : G →L[ℂ] H) (U : G →L[ℂ] K) (hS : S.adjoint.comp S=1) :
    (U.comp S.adjoint).comp (S.comp S.adjoint)=U.comp S.adjoint := by
  rw [comp_assoc,←comp_assoc S.adjoint S,hS]
  simp only [one_def,id_comp]

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (hN : 0<N) (P : Parameters A) (e : Sector N)

theorem normalized_right_terminal (z : UpperHalfPlane) :
    (normalizedRegularAmbientCountReconstruction A hN P e z).comp
      (corner (terminalRegion A P) z)=normalizedRegularAmbientCountReconstruction A hN P e z := by
  let S := (TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z).subtypeL
  let U := normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)
  have hS : S.adjoint.comp S=1 := AsymptoticOrbitRegion.adjoint_comp_subtype _ z
  have hc : corner (terminalRegion A P) z=S.comp S.adjoint :=
    (AsymptoticOrbitRegion.subtype_comp_adjoint _ z).symm
  change (U.comp S.adjoint).comp (corner (terminalRegion A P) z)=U.comp S.adjoint
  exact (congrArg (fun T => (U.comp S.adjoint).comp T) hc).trans (extension_right S U hS)

variable (B : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace)

def normalizedRow (z : Base) : RegularSpace →L[ℂ] RegularSpace :=
  (B z).comp (normalizedRegularAmbientCountReconstruction A hN P e z)

theorem normalized_row_source (z : Base) :
    normalizedRow A hN P e B z * corner (terminalRegion A P) z=normalizedRow A hN P e B z := by
  change ((B z).comp _).comp _=(B z).comp _
  rw [comp_assoc,normalized_right_terminal]

variable (hm : ∀ g k,Measurable (fun z => matrix (B z) g k)) (hc : Covariant B)
  (C : ℝ) (hn : ∀ z,‖B z‖≤C)

include hm in
theorem normalized_row_measurable :
    ∀ g k,Measurable (fun z => matrix (normalizedRow A hN P e B z) g k) :=
  matrix_comp_measurable _ _ hm (normalizedRegularCountReconstruction_regular A hN P e).1

include hc in
theorem normalized_row_covariant : Covariant (normalizedRow A hN P e B) :=
  covariant_comp _ _ hc (normalizedRegularCountReconstruction_regular A hN P e).2

include hn in
theorem normalized_row_norm (z : Base) : ‖normalizedRow A hN P e B z‖≤C := by
  apply (opNorm_comp_le _ _).trans
  exact ((mul_le_mul_of_nonneg_left
    (normalizedRegularAmbientCountReconstruction_norm_le A hN P e z) (norm_nonneg (B z))).trans_eq
      (mul_one _)).trans (hn z)

/-- Each original observation, applied after exact normalized reconstruction,
has a Gram element in the finite algebra of the full terminal strip. -/
def normalizedGram : Algebra A P :=
  QuantitativeSpectralSourceGram.gramElement action_measurable (terminalRegion A P) (terminal_measurable A P)
    (normalizedRow A hN P e B) (normalized_row_measurable A hN P e B hm)
    (normalized_row_covariant A hN P e B hc) C (normalized_row_norm A hN P e B C hn)
    (normalized_row_source A hN P e B)

theorem rep_normalizedGram (z : Base) : rep A P (normalizedGram A hN P e B hm hc C hn) z=
    (normalizedRow A hN P e B z).adjoint.comp (normalizedRow A hN P e B z) := rfl

theorem normalizedGram_nonneg : 0≤normalizedGram A hN P e B hm hc C hn :=
  QuantitativeSpectralSourceGram.gramElement_nonneg _ _ _ _ _ _ _ _ _

theorem normalizedGram_norm : ‖normalizedGram A hN P e B hm hc C hn‖≤C^2 :=
  QuantitativeSpectralSourceGram.gramElement_norm_le _ _ _ _ _ _ _ _ _

#print axioms normalized_right_terminal
#print axioms normalized_row_source
#print axioms rep_normalizedGram
#print axioms normalizedGram_nonneg
#print axioms normalizedGram_norm
end QuantitativeEulerEndpointTerminalAlgebra
