module

public import AsymptoticClassicalNormFactorV1
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalNorm

open UpperHalfPlane
open scoped ModularForm MatrixGroups

variable {G : Subgroup (GL (Fin 2) ℝ)} [G.HasDetOne] [G.IsArithmetic]
  (hG : G ≤ 𝒮ℒ) (hper : (1 : ℝ) ∈ G.strictPeriods) {k : ℤ}

include hG hper

/-- The identity-coset factor cannot have larger Fourier vanishing order
 than the level-one norm. -/
theorem order_le_norm (f : ModularForm G k) :
    (qExpansion 1 f).order ≤ (qExpansion 1 (ModularForm.norm 𝒮ℒ f)).order := by
  rw [norm_eq_mul_remainder hG f,
    ModularForm.qExpansion_mul_coe zero_lt_one hper,
    PowerSeries.order_mul]
  exact le_add_of_nonneg_right (by positivity)

/-- A Sturm bound at any arithmetic level containing the unit translation,
 obtained from the actual norm and the classical level-one bound. -/
theorem sturm_bound (f : ModularForm G k)
    (hv : (((k * Nat.card (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)).toNat / 12 : ℕ) : ℕ∞) <
      (qExpansion 1 f).order) : f = 0 := by
  have hn : ModularForm.norm 𝒮ℒ f = 0 :=
    ModularForm.sturm_bound_levelOne (hv.trans_le (order_le_norm hG hper f))
  exact DFunLike.coe_injective ((ModularForm.norm_eq_zero_iff 𝒮ℒ f).mp hn)

/-- Finitely many Fourier coefficients determine an arithmetic modular
 form; the bound includes the constant coefficient. -/
theorem eq_zero_of_coefficients (f : ModularForm G k)
    (hv : ∀ n ≤ (k * Nat.card (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)).toNat / 12,
      (qExpansion 1 f).coeff n = 0) : f = 0 := by
  apply sturm_bound hG hper f
  apply lt_of_lt_of_le _ (PowerSeries.nat_le_order _
    ((k * Nat.card (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ)).toNat / 12 + 1)
    (fun n hn => hv n (by omega)))
  exact_mod_cast Nat.lt_succ_self _

#print axioms order_le_norm
#print axioms sturm_bound
#print axioms eq_zero_of_coefficients

end AsymptoticClassicalNorm
