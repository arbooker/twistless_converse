module

public import AsymptoticClassicalSturmV1
public import AsymptoticClassicalNewCuspV1
public import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalNorm

open UpperHalfPlane
open scoped ModularForm MatrixGroups

variable {G : Subgroup (GL (Fin 2) ℝ)} [G.HasDetOne] [G.IsArithmetic]
  (hper : (1 : ℝ) ∈ G.strictPeriods) (k : ℤ)

/-- A finite Fourier jet at infinity, with length supplied by the norm bound. -/
def fourierJet : ModularForm G k →ₗ[ℂ]
    (Fin ((k * Nat.card (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)).toNat / 12 + 1) → ℂ) where
  toFun f n := (qExpansion 1 f).coeff n.val
  map_add' f g := by
    ext n
    simp only [FunLike.coe_add, ModularForm.qExpansion_add zero_lt_one hper,
      map_add, Pi.add_apply]
  map_smul' c f := by
    ext n
    simp only [FunLike.coe_smul, ModularForm.qExpansion_smul zero_lt_one hper,
      PowerSeries.coeff_smul, Pi.smul_apply, RingHom.id_apply]

variable (hG : G ≤ 𝒮ℒ)

include hG hper

theorem fourierJet_injective : Function.Injective (fourierJet hper k) := by
  intro f g he
  apply sub_eq_zero.mp
  apply eq_zero_of_coefficients hG hper (f - g)
  intro n hn
  have hh := congrFun he (⟨n, by omega⟩ :
    Fin ((k * Nat.card (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)).toNat / 12 + 1))
  change (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n at hh
  simp only [FunLike.coe_sub, ModularForm.qExpansion_sub zero_lt_one hper, map_sub]
  exact sub_eq_zero.mpr hh

/-- Finite dimensionality is derived from the finite Fourier jet, rather
 than supplied as a hypothesis. -/
theorem finiteDimensional : Module.Finite ℂ (ModularForm G k) :=
  Module.Finite.of_injective (fourierJet hper k) (fourierJet_injective hper k hG)

#print axioms fourierJet_injective
#print axioms finiteDimensional

end AsymptoticClassicalNorm

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm MatrixGroups

theorem level_le_SL (N : ℕ) : level N ≤ 𝒮ℒ := by
  rintro g ⟨A, _, rfl⟩
  exact ⟨A, rfl⟩

theorem level_one_period (N : ℕ) : (1 : ℝ) ∈ (level N).strictPeriods := by
  simp [level]

instance modular_finite (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Finite ℂ (ModularForm (level N) k) :=
  AsymptoticClassicalNorm.finiteDimensional (level_one_period N) k (level_le_SL N)

instance cusp_finite (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Finite ℂ (CuspForm (level N) k) :=
  Module.Finite.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

/-- The concrete joint trace kernel is now a finite dimensional cusp space. -/
instance newSpace_finite (N : ℕ) (hN : 0 < N) (k : ℤ) :
    Module.Finite ℂ (newSpace N hN k) := by
  let : NeZero N := ⟨hN.ne'⟩
  infer_instance

#print axioms level_le_SL
#print axioms level_one_period
#print axioms modular_finite
#print axioms cusp_finite
#print axioms newSpace_finite

end AsymptoticClassicalCusp
