module

public import AsymptoticClassicalLocalAtkinMatrixV1
public import AsymptoticClassicalHeckeSwapV1
public import AsymptoticClassicalBadHeckeLowerV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace AsymptoticClassicalCusp
open UpperHalfPlane Matrix ConjAct AsymptoticAtkinLehner
open scoped ModularForm MatrixGroups Pointwise
variable (M p : ℕ) (hp : 0 < p) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)

/-- The unscaled local slash operator, bundled on the actual cusp space. -/
def localAtkinOperator (k : ℤ) :
    CuspForm (level (p * M)) k →ₗ[ℂ] CuspForm (level (p * M)) k := by
  let C : CuspForm (toConjAct (localAtkinReal M p hp A B hAB)⁻¹ • level (p * M)) k →ₗ[ℂ]
      CuspForm (level (p * M)) k := {
    toFun := fun f => CuspForm.mcast rfl f (localAtkinReal_normalizes M p hp A B hAB).symm
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact C.comp (translateLinear (level (p * M)) k (localAtkinReal M p hp A B hAB)
    (by rw [localAtkinReal_det]; exact_mod_cast hp))

@[simp] theorem localAtkinOperator_coe (k : ℤ) (f : CuspForm (level (p * M)) k) :
    (localAtkinOperator M p hp A B hAB k f : ℍ → ℂ) =
      (f : ℍ → ℂ) ∣[k] localAtkinReal M p hp A B hAB := rfl

theorem scalar_eq_positiveScalarReal :
    GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) (by exact_mod_cast hp.ne')) =
      positiveScalarReal p hp := by
  apply Units.ext
  change Matrix.diagonal (fun _ : Fin 2 => (p : ℝ)) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positiveScalarReal, AsymptoticClassicalDiscriminant.triangularGL,
      GeneralLinearGroup.mkOfDetNeZero, Matrix.diagonal]

theorem localAtkinOperator_square (k : ℤ) (f : CuspForm (level (p * M)) k) :
    localAtkinOperator M p hp A B hAB k (localAtkinOperator M p hp A B hAB k f) =
      (p : ℂ) ^ (k - 2) • f := by
  apply DFunLike.coe_injective
  simp only [localAtkinOperator_coe]
  rw [← SlashAction.slash_mul, localAtkinReal_square, scalar_eq_positiveScalarReal p hp,
    SlashAction.slash_mul]
  have hi : (f : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ (localSquare M p A B hAB) = f :=
    f.slash_action_eq' _ ⟨_, localSquare_mem M p A B hAB, rfl⟩
  rw [hi, slash_positiveScalarReal]
  rfl

/-- Local Atkin interchanges the two old overgroups. -/
theorem localAtkinReal_oldGroup :
    toConjAct (localAtkinReal M p hp A B hAB) • level M = dilationLevel M p hp := by
  have hu : SpecialLinearGroup.mapGL ℝ (heckeSL M p A B hAB) ∈ level M :=
    ⟨_, heckeSL_mem M p A B hAB, rfl⟩
  have hu' : toConjAct (SpecialLinearGroup.mapGL ℝ (heckeSL M p A B hAB)) • level M = level M :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hu)
  rw [localAtkinReal, map_mul, mul_smul, hu']
  have hh := upper_translate_dilationLevel M p hp
  calc
    _ = toConjAct (upperDilationReal p hp) •
        (toConjAct (upperDilationReal p hp)⁻¹ • dilationLevel M p hp) := congrArg _ hh.symm
    _ = _ := by rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]

theorem localAtkinReal_oldGroup_back :
    toConjAct (localAtkinReal M p hp A B hAB)⁻¹ • dilationLevel M p hp = level M := by
  rw [← localAtkinReal_oldGroup M p hp A B hAB, ← mul_smul, ← map_mul,
    inv_mul_cancel, map_one, one_smul]

#print axioms localAtkinOperator_coe
#print axioms scalar_eq_positiveScalarReal
#print axioms localAtkinOperator_square
#print axioms localAtkinReal_oldGroup
#print axioms localAtkinReal_oldGroup_back
end AsymptoticClassicalCusp
