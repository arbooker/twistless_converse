module

public import AsymptoticClassicalDegeneracyV1
public import AsymptoticClassicalDiscriminantAffineV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalDiscriminant

open UpperHalfPlane Matrix AsymptoticClassicalCusp AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups

/-- The dilation action is the positive affine map with zero translation. -/
theorem dilation_action (N : ℕ) (hN : 0 < N) (z : ℍ) :
    dilationReal N hN • z = affine (N : ℝ) (by exact_mod_cast hN) 0 z := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by rw [dilationReal_det]; exact_mod_cast hN), dilationReal_denom]
  simp [num, dilationReal, dilationGL, GeneralLinearGroup.map,
    GeneralLinearGroup.mkOfDetNeZero, affine]

/-- The discriminant evaluated at N*z, as a genuine level-N cusp form. -/
def atLevel (N : ℕ) (hN : 0 < N) : CuspForm (level N) 12 :=
  let f := degeneracy 1 N hN 12 (restrict 12 (level_le_SL 1) CuspForm.discriminant)
  f.copy (fun z => ModularForm.discriminant (dilationReal N hN • z))
    (by
      funext z
      exact (degeneracy_apply 1 N hN 12
        (restrict 12 (level_le_SL 1) CuspForm.discriminant) z).symm)
    (by simp only [Nat.mul_one])

@[simp] theorem atLevel_apply (N : ℕ) (hN : 0 < N) (z : ℍ) :
    atLevel N hN z = ModularForm.discriminant (affine (N : ℝ) (by exact_mod_cast hN) 0 z) := by
  change ModularForm.discriminant (dilationReal N hN • z) = _
  rw [dilation_action]

theorem atLevel_ne_zero (N : ℕ) (hN : 0 < N) (z : ℍ) : atLevel N hN z ≠ 0 :=
  ModularForm.discriminant_ne_zero _

/-- The expected congruence subgroup is contained in the slash stabilizer. -/
theorem atLevel_slash_eq (N : ℕ) (hN : 0 < N) (A : SL(2, ℤ))
    (hA : A ∈ CongruenceSubgroup.Gamma0 N) :
    (atLevel N hN : ℍ → ℂ) ∣[(12 : ℤ)] A = atLevel N hN := by
  change (atLevel N hN : ℍ → ℂ) ∣[(12 : ℤ)] SpecialLinearGroup.mapGL ℝ A = _
  exact (atLevel N hN).slash_action_eq' _ ⟨A, hA, rfl⟩

/-- The actual level-N discriminant has decay slope N. -/
theorem atLevel_log_decay (N : ℕ) (hN : 0 < N) :
    Filter.Tendsto (fun z : ℍ => Real.log ‖atLevel N hN z‖ / z.im)
      atImInfty (nhds ((-2 * Real.pi) * N)) := by
  simpa only [atLevel_apply] using log_affine_div_im_tendsto (N : ℝ) (by exact_mod_cast hN) 0

#print axioms dilation_action
#print axioms atLevel_ne_zero
#print axioms atLevel_slash_eq
#print axioms atLevel_log_decay

end AsymptoticClassicalDiscriminant
