module

public import QuantitativeEulerEndpointTerminalHalfV1
public import QuantitativeEulerEndpointCutDefectV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass
open QuantitativeEulerEndpointTerminalAlgebra QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointUnitSubcorner FinitenessCertificate FinitenessGlobalHeight

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

theorem terminal_half_defect_bounds (F : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1) :
    F-(4:ℝ) • (F-F^2)≤halfProjection A P F (IsSelfAdjoint.of_nonneg hF0) ∧
      halfProjection A P F (IsSelfAdjoint.of_nonneg hF0)≤F+(4:ℝ) • (F-F^2) := by
  let s := terminalRegion A P
  let hs := terminal_measurable A P
  have h := QuantitativeEulerEndpointCornerCut.half_cut_defect_bounds action_measurable s hs
    1 (unitProjection action_measurable s hs) (terminalSpace A P) (terminal_space_projection A P)
    (lift action_measurable s hs F) (lift_nonneg action_measurable s hs F hF0)
    (lift_le_one action_measurable s hs F hF1)
  let v := value action_measurable s hs
  have hv : Monotone v := fun a b hab => (value_le_iff action_measurable s hs a b).mpr hab
  have hl := hv h.1
  have hu := hv h.2
  have hmul (a b : UnitCorner action_measurable s hs) : v (a*b)=v a*v b := rfl
  have hp : v ((lift action_measurable s hs F)^2)=F^2 := by
    rw [pow_two,hmul]
    change F*F=F^2
    exact (pow_two F).symm
  have hval : v (lift action_measurable s hs F)=F := rfl
  rw [map_sub,map_smul,map_sub,hval,hp] at hl
  rw [map_add,map_smul,map_sub,hval,hp] at hu
  exact ⟨hl,hu⟩

#print axioms terminal_half_defect_bounds
end QuantitativeMaass
