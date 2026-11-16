module

public import MaassSecondCurveV1
public import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 20000

@[expose] public section

namespace MaassDifferential

/-- The ordered cross terms cancel without any symmetry of the bilinear map. -/
theorem bilinear_rotation (H : Point →L[ℝ] Point →L[ℝ] ℂ) (A B : ℝ) :
    H (A,-B) (A,-B)+H (B,A) (B,A) =
      (A^2+B^2) • (H e₁ e₁+H e₂ e₂) := by
  have h1 : (A,-B)=A•e₁+(-B)•e₂ := by ext <;> simp [e₁,e₂]
  have h2 : (B,A)=B•e₁+A•e₂ := by ext <;> simp [e₁,e₂]
  rw [h1,h2]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_add,smul_smul]
  simp only [Complex.real_smul]
  push_cast
  ring

#print axioms bilinear_rotation

end MaassDifferential
