module

public import AsymptoticClassicalFiniteDimensionV1
public import AsymptoticClassicalEigenNormalizationV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane

/-- The actual Fourier coefficient at infinity, as a linear functional on
 the classical cusp space. -/
def cuspCoefficient (N : ℕ) (k : ℤ) (n : ℕ) : CuspForm (level N) k →ₗ[ℂ] ℂ where
  toFun f := (qExpansion 1 f).coeff n
  map_add' f g := by
    change (qExpansion 1 ((CuspForm.toModularFormₗ f) + (CuspForm.toModularFormₗ g))).coeff n = _
    rw [ModularForm.qExpansion_add zero_lt_one (level_one_period N), map_add]
    rfl
  map_smul' c f := by
    change (qExpansion 1 (c • (CuspForm.toModularFormₗ f))).coeff n = _
    rw [ModularForm.qExpansion_smul zero_lt_one (level_one_period N), PowerSeries.coeff_smul]
    rfl

@[simp] theorem cuspCoefficient_apply (N : ℕ) (k : ℤ) (n : ℕ)
    (f : CuspForm (level N) k) : cuspCoefficient N k n f = (qExpansion 1 f).coeff n := rfl

/-- Separation by Fourier coefficients is proved for the actual cusp
 space, using injectivity of the analytic q-expansion. -/
theorem cuspCoefficient_separates (N : ℕ) (k : ℤ) (f : CuspForm (level N) k)
    (hf : ∀ n, cuspCoefficient N k n f = 0) : f = 0 := by
  apply CuspForm.toModularFormₗ_injective
  apply ModularForm.qExpansion_injective zero_lt_one (level_one_period N)
  ext n
  change (qExpansion 1 f).coeff n = (qExpansion 1 (0 : ℍ → ℂ)).coeff n
  rw [qExpansion_zero, map_zero]
  exact hf n

/-- Fourier coefficients restricted to the concrete newspace. -/
def newCoefficient (N : ℕ) (hN : 0 < N) (k : ℤ) (n : ℕ) :
    newSpace N hN k →ₗ[ℂ] ℂ :=
  (cuspCoefficient N k n).comp (newSpace N hN k).subtype

@[simp] theorem newCoefficient_apply (N : ℕ) (hN : 0 < N) (k : ℤ) (n : ℕ)
    (f : newSpace N hN k) : newCoefficient N hN k n f = (qExpansion 1 f.val).coeff n := rfl

theorem newCoefficient_separates (N : ℕ) (hN : 0 < N) (k : ℤ)
    (f : newSpace N hN k) (hf : ∀ n, newCoefficient N hN k n f = 0) : f = 0 := by
  apply Subtype.val_injective
  exact cuspCoefficient_separates N k f.val hf

#print axioms cuspCoefficient
#print axioms cuspCoefficient_separates
#print axioms newCoefficient
#print axioms newCoefficient_separates

end AsymptoticClassicalCusp
