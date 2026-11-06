module

public import AsymptoticClassicalLocalFrickeMatrixV1
public import AsymptoticClassicalLocalAtkinOperatorV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace AsymptoticClassicalCusp
open UpperHalfPlane AsymptoticClassicalLSeries
open scoped ModularForm

/-- Global Fricke commutes with the literal local Atkin--Lehner slash
operator. Their matrix commutator belongs to the original congruence group. -/
theorem localAtkin_fricke_commute (M p : ℕ) (hM : 0 < M) (hp : 0 < p)
    (A B : ℤ) (hAB : (p : ℤ)*A+(M : ℤ)*B=1) (k : ℤ) :
    Function.Commute (localAtkinOperator M p hp A B hAB k)
      (frickeOperator (p*M) (Nat.mul_pos hp hM) k) := by
  intro f
  apply DFunLike.coe_injective
  rw [localAtkinOperator_coe, frickeOperator_coe, normalizedFricke_eq_slash,
    ModularForm.smul_slash, ← SlashAction.slash_mul,
    localAtkin_fricke_intertwine M p hp A B hAB hM,
    SlashAction.slash_mul, SlashAction.slash_mul]
  have hi : (f : ℍ → ℂ) ∣[k]
      Matrix.SpecialLinearGroup.mapGL ℝ (localFrickeCommutator M p A B hAB) = f :=
    f.slash_action_eq' _ ⟨_, localFrickeCommutator_mem M p A B hAB, rfl⟩
  rw [hi, frickeOperator_coe, normalizedFricke_eq_slash, localAtkinOperator_coe]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  simp only [σ, localAtkinReal_det, hpR, ite_true, ContinuousAlgEquiv.refl_apply]

#print axioms localAtkin_fricke_commute
end AsymptoticClassicalCusp
