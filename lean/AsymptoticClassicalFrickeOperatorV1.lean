module

public import AsymptoticClassicalEigenFrickeSlashV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane ConjAct AsymptoticClassicalLSeries
open scoped ModularForm Pointwise

theorem fricke_inverse_normalizes (N : ℕ) (hN : 0 < N) :
    toConjAct (frickeReal N hN)⁻¹ • level N = level N := by
  have he : toConjAct (frickeReal N hN) • level N = level N :=
    frickeOldLevel_self N hN
  calc
    _ = toConjAct (frickeReal N hN)⁻¹ • (toConjAct (frickeReal N hN) • level N) :=
      congrArg (fun G => toConjAct (frickeReal N hN)⁻¹ • G) he.symm
    _ = _ := by
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

/-- Global Fricke, with determinant-half-weight normalization, is an
actual complex linear endomorphism of the classical cusp space. -/
def frickeOperator (N : ℕ) (hN : 0 < N) (k : ℤ) :
    CuspForm (level N) k →ₗ[ℂ] CuspForm (level N) k := by
  let C : CuspForm (toConjAct (frickeReal N hN)⁻¹ • level N) k →ₗ[ℂ]
      CuspForm (level N) k := {
    toFun := fun f => CuspForm.mcast rfl f (fricke_inverse_normalizes N hN).symm
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact (N : ℂ)^(1-(k : ℂ)/2) • C.comp
    (translateLinear (level N) k (frickeReal N hN)
      (by rw [frickeReal_det]; exact_mod_cast hN))

@[simp] theorem frickeOperator_coe (N : ℕ) (hN : 0 < N) (k : ℤ)
    (f : CuspForm (level N) k) :
    (frickeOperator N hN k f : ℍ → ℂ) = normalizedFricke N hN k f := by
  rw [normalizedFricke_eq_slash]
  rfl

@[simp] theorem frickeOperator_apply (N : ℕ) (hN : 0 < N) (k : ℤ)
    (f : CuspForm (level N) k) (z : ℍ) :
    frickeOperator N hN k f z = (N : ℂ)^(-(k : ℂ)/2) *
      (z : ℂ)^(-k) * f (frickeReal N hN • z) := by
  exact congrFun (frickeOperator_coe N hN k f) z

#print axioms fricke_inverse_normalizes
#print axioms frickeOperator
#print axioms frickeOperator_coe
#print axioms frickeOperator_apply

end AsymptoticClassicalCusp
