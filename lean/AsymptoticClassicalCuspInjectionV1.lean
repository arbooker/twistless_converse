module

public import AsymptoticClassicalDiscriminantFamilyV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalDiscriminant

open UpperHalfPlane AsymptoticClassicalCusp
open scoped ModularForm MatrixGroups Manifold

/-- Multiply the common-weight discriminant family by arbitrary
 level-one forms of one weight and add the results. -/
def familyMap (N : ℕ) (hN : 0 < N) (n : ℕ) (w : ℤ) :
    (Fin n → ModularForm 𝒮ℒ w) →ₗ[ℂ] CuspForm (level N) (12 * (n : ℤ) + w) where
  toFun g := ∑ j, (family N hN n j).mulModularForm (restrictModular w (level_le_SL N) (g j))
  map_add' g h := by
    ext z
    simp only [sum_apply, CuspForm.coe_mulModularForm, Pi.mul_apply,
      restrictModular_apply, Pi.add_apply, add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' c g := by
    ext z
    simp only [sum_apply, CuspForm.coe_mulModularForm, Pi.mul_apply,
      restrictModular_apply, Pi.smul_apply, smul_apply,
      RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

@[simp] theorem familyMap_apply (N : ℕ) (hN : 0 < N) (n : ℕ) (w : ℤ)
    (g : Fin n → ModularForm 𝒮ℒ w) (z : ℍ) :
    familyMap N hN n w g z = ∑ j, family N hN n j z * g j z := by
  simp only [familyMap, LinearMap.coe_mk, AddHom.coe_mk, sum_apply,
    CuspForm.coe_mulModularForm, Pi.mul_apply, restrictModular_apply]

theorem levelOne_slash (w : ℤ) (g : ModularForm 𝒮ℒ w) (A : SL(2, ℤ)) :
    (g : ℍ → ℂ) ∣[w] A = g :=
  g.slash_action_eq' (Matrix.SpecialLinearGroup.mapGL ℝ A) ⟨A, rfl⟩

theorem familyMap_slash (N : ℕ) (hN : 0 < N) (n : ℕ) (w : ℤ)
    (g : Fin n → ModularForm 𝒮ℒ w) (A : SL(2, ℤ)) :
    (familyMap N hN n w g : ℍ → ℂ) ∣[12 * (n : ℤ) + w] A =
      ∑ j, (ModularForm.discriminant * ((atLevel N hN : ℍ → ℂ) ∣[(12 : ℤ)] A) ^ j.val *
        ModularForm.discriminant ^ j.rev.val) * (g j : ℍ → ℂ) := by
  have hf : (familyMap N hN n w g : ℍ → ℂ) =
      ∑ j, (family N hN n j : ℍ → ℂ) * (g j : ℍ → ℂ) := by
    funext z
    simp only [familyMap_apply, Finset.sum_apply, Pi.mul_apply]
  rw [hf, SlashAction.sum_slash]
  apply Finset.sum_congr rfl
  intro j _
  rw [ModularForm.mul_slash_SL2, family_slash, levelOne_slash]

/-- The coset orbit makes the discriminant family independent even with
 coefficients in the space of level-one modular forms. -/
theorem familyMap_injective (N : ℕ) (hN : 0 < N) (n : ℕ) (w : ℤ)
    (e : Fin n ≃ SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    Function.Injective (familyMap N hN n w) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro g hg
  let v : Fin n → ℍ → ℂ := fun j z =>
    ModularForm.discriminant z * ModularForm.discriminant z ^ j.rev.val * g j z
  have hv : ∀ j, MDiff (v j) := fun j =>
    (CuspForm.discriminant.holo'.mul (CuspForm.discriminant.holo'.pow j.rev.val)).mul (g j).holo'
  have he : ∀ z i, ∑ j : Fin n, orbit N hN (e i) z ^ j.val * v j z = 0 := by
    intro z i
    let A : SL(2, ℤ) := (e i).out⁻¹
    have ho : orbit N hN (e i) = (atLevel N hN : ℍ → ℂ) ∣[(12 : ℤ)] A := by
      have hh := congrArg (orbit N hN) (Quotient.out_eq (e i))
      exact hh.symm
    have hs := familyMap_slash N hN n w g A
    rw [hg] at hs
    have hz := congrFun hs z
    simp only [FunLike.coe_zero, SlashAction.zero_slash, Pi.zero_apply,
      Finset.sum_apply, Pi.mul_apply, Pi.pow_apply] at hz
    rw [ho]
    convert hz.symm using 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp [v]
    ring
  have hz := coefficients_eq_zero (fun i => orbit N hN (e i)) v
    (fun i => orbit_holomorphic N hN (e i)) hv
    ((orbit_injective N hN).comp e.injective) he
  funext j
  apply ModularForm.ext
  intro z
  have hh := congrFun (hz j) z
  change ModularForm.discriminant z * ModularForm.discriminant z ^ j.rev.val * g j z = 0 at hh
  exact (mul_eq_zero.mp hh).resolve_left
    (mul_ne_zero (ModularForm.discriminant_ne_zero z)
      (pow_ne_zero _ (ModularForm.discriminant_ne_zero z)))

#print axioms familyMap_apply
#print axioms familyMap_slash
#print axioms familyMap_injective

end AsymptoticClassicalDiscriminant
