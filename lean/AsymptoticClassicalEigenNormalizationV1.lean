module

public import AsymptoticClassicalEigenbasisV1
public import Mathlib.Data.Set.Card

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalEigenbasis

open Module

variable {E ι : Type*} [AddCommGroup E] [Module ℂ E]

/-- First-coefficient extraction from each operator and separation by all
coefficients force the first coefficient of a nonzero joint eigenvector
 to be nonzero. -/
theorem first_ne_zero (T : ι → E →ₗ[ℂ] E) (first : E →ₗ[ℂ] ℂ)
    (coeff : ι → E →ₗ[ℂ] ℂ)
    (hcoeff : ∀ i v, first (T i v) = coeff i v)
    (hsep : ∀ v, (∀ i, coeff i v = 0) → v = 0)
    {v : E} (hv : v ≠ 0) {χ : ι → ℂ}
    (heigen : ∀ i, T i v = χ i • v) : first v ≠ 0 := by
  intro hzero
  apply hv
  apply hsep
  intro i
  rw [← hcoeff, heigen, map_smul, hzero, smul_zero]

/-- Normalize a vector by its first coefficient. -/
def normalizedVector (first : E →ₗ[ℂ] ℂ) (v : E) : E :=
  (first v)⁻¹ • v

@[simp] theorem first_normalizedVector (first : E →ₗ[ℂ] ℂ) {v : E}
    (hv : first v ≠ 0) : first (normalizedVector first v) = 1 := by
  simp [normalizedVector, hv]

theorem normalizedVector_eigen (T : ι → E →ₗ[ℂ] E) (first : E →ₗ[ℂ] ℂ)
    {v : E} {χ : ι → ℂ} (heigen : ∀ i, T i v = χ i • v) (i : ι) :
    T i (normalizedVector first v) = χ i • normalizedVector first v := by
  unfold normalizedVector
  rw [map_smul, heigen i]
  exact smul_comm _ _ _

/-- The complete coefficient sequence of a normalized joint eigenvector
is its operator eigenvalue sequence. -/
theorem coeff_normalizedVector (T : ι → E →ₗ[ℂ] E) (first : E →ₗ[ℂ] ℂ)
    (coeff : ι → E →ₗ[ℂ] ℂ)
    (hcoeff : ∀ i v, first (T i v) = coeff i v)
    {v : E} (hv : first v ≠ 0) {χ : ι → ℂ}
    (heigen : ∀ i, T i v = χ i • v) (i : ι) :
    coeff i (normalizedVector first v) = χ i := by
  rw [← hcoeff, normalizedVector_eigen T first heigen, map_smul,
    first_normalizedVector first hv, smul_eq_mul, mul_one]

/-- Normalizing independent nonzero vectors does not identify two of them. -/
theorem normalizedVector_injective {J : Type*} {b : J → E}
    (hb : LinearIndependent ℂ b) (first : E →ₗ[ℂ] ℂ)
    (hfirst : ∀ j, first (b j) ≠ 0) :
    Function.Injective (fun j => normalizedVector first (b j)) := by
  intro i j hij
  exact hb.eq_of_smul_apply_eq_smul_apply _ _ i j (inv_ne_zero (hfirst i)) hij

/-- Equality of every coefficient determines the vector. -/
theorem coefficient_injective (coeff : ι → E →ₗ[ℂ] ℂ)
    (hsep : ∀ v, (∀ i, coeff i v = 0) → v = 0) :
    Function.Injective (fun v i => coeff i v) := by
  intro v w hvw
  apply sub_eq_zero.mp
  apply hsep
  intro i
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun hvw i)

/-- Joint eigenspaces have dimension at most one when first-coefficient
extraction and coefficient separation hold. This is the multiplicity-one
step, independent of the construction of the operators. -/
theorem joint_vectors_proportional (T : ι → E →ₗ[ℂ] E) (first : E →ₗ[ℂ] ℂ)
    (coeff : ι → E →ₗ[ℂ] ℂ)
    (hcoeff : ∀ i v, first (T i v) = coeff i v)
    (hsep : ∀ v, (∀ i, coeff i v = 0) → v = 0)
    {v w : E} {χ : ι → ℂ}
    (hv : ∀ i, T i v = χ i • v) (hw : ∀ i, T i w = χ i • w) :
    first w • v = first v • w := by
  apply coefficient_injective coeff hsep
  funext i
  simp only [map_smul, ← hcoeff, hv, hw, smul_eq_mul]
  ring

#print axioms first_ne_zero
#print axioms first_normalizedVector
#print axioms normalizedVector_eigen
#print axioms coeff_normalizedVector
#print axioms normalizedVector_injective
#print axioms coefficient_injective
#print axioms joint_vectors_proportional

end AsymptoticClassicalEigenbasis
