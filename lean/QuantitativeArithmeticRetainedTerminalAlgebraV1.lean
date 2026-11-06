module

public import QuantitativeEulerEndpointRegularBaseV1
public import QuantitativeSpectralSourceGramV1
public import QuantitativeArithmeticRetainedRegularExtensionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedTerminalAlgebra
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeEulerEndpointRegularBase AsymptoticCertificateOperators
open QuantitativeSpectralRegularAlgebra MeasureTheory
open scoped ENNReal

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q}
    (A : Certificate N S Q hQ) (P : Parameters A)

def terminalRegion : Set Base := region (highStrip P.ε)

theorem terminal_measurable : MeasurableSet (terminalRegion A P) := highStrip_measurable _

theorem terminal_area : measure (terminalRegion A P)=
    ENNReal.ofReal P.ε⁻¹ :=
  AsymptoticHyperbolicArea.closed_terminal_area P.epsilon_pos

theorem terminal_finite : measure (terminalRegion A P)<∞ := by
  rw [terminal_area]
  exact ENNReal.ofReal_lt_top

/-- The entire terminal strip has finite area, so its regular algebra carries a finite trace. -/
abbrev Algebra := FiniteCorner AsymptoticRationalGroup.Group Base
  action_measurable (terminalRegion A P) (terminal_measurable A P)

def rep : Algebra A P →ₗ[ℝ] (Base → AsymptoticFiniteBranch.RegularSpace →L[ℂ] AsymptoticFiniteBranch.RegularSpace) :=
  representation _ _ action_measurable (terminalRegion A P) (terminal_measurable A P)

def tr : Algebra A P →L[ℝ] ℝ :=
  QuantitativeSpectralFiniteCornerTrace.rootedTrace measure action_measurable
    (terminalRegion A P) (terminal_measurable A P) (terminal_finite A P)

theorem tr_one : tr A P 1=P.ε⁻¹ := by
  rw [tr,QuantitativeSpectralFiniteCornerDistribution.rootedTrace_one,terminal_area,
    ENNReal.toReal_ofReal (inv_nonneg.mpr P.epsilon_pos.le)]

theorem tr_mono : Monotone (tr A P) :=
  QuantitativeSpectralFiniteCornerDistribution.rootedTrace_mono _ _ _ _ _

theorem tr_cyclic (a b : Algebra A P) : tr A P (a*b)=tr A P (b*a) :=
  QuantitativeSpectralFiniteCornerTrace.rootedTrace_cyclic _ _ _ _ _ action_preserving a b

theorem rep_one (z : Base) : rep A P 1 z=
    (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P z).starProjection := by
  change AsymptoticOrbitDiagonal.corner (terminalRegion A P) z=_
  exact (QuantitativeSpectralExceptionalRows.region_projection _ z).symm

#print axioms terminal_area
#print axioms tr_one
#print axioms tr_mono
#print axioms tr_cyclic
#print axioms rep_one
end QuantitativeArithmeticRetainedTerminalAlgebra
