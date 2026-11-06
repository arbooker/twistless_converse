module

public import QuantitativeEulerOldProjectionHolomorphicCoverV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionHolomorphic

open UpperHalfPlane MeasureTheory AsymptoticClassicalCusp AsymptoticClassicalPetersson
open AsymptoticCongruenceStrip AsymptoticClassicalCosets

variable (N M : ℕ) [NeZero N] [NeZero M] (k : ℤ) (hMN : M ∣ N)

local instance : (level N).IsFiniteRelIndex (level M) :=
  ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
    (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1

local instance : Fintype (level M ⧸ (level N).subgroupOf (level M)) := Fintype.ofFinite _
local instance : Fintype (gamma M ⧸ (gamma N).subgroupOf (gamma M)) := Fintype.ofFinite _

/-- The actual Hilbert-adjoint trace has the literal finite-coset slash
formula in the weighted quotient realization. Each weight-k slash phase
is retained in quotientFunc; there is no scalar pullback substitution. -/
theorem trace_coeFn (f : CuspForm (level N) k) :
    ((trace N k M hMN (realization N k f) : space M k) : Lp ℂ 2 (quotientMeasure M))
      =ᵐ[quotientMeasure M] fun z : ℍ =>
        ∑ q : gamma M ⧸ (gamma N).subgroupOf (gamma M),
          weighted k (SlashInvariantForm.quotientFunc f ((traceEquiv N M).symm q)) z := by
  rw [trace_realization]
  filter_upwards [realization_coeFn M k (arithmeticTrace (level N) (level M) k f)] with z hz
  rw [hz]
  have ht : (arithmeticTrace (level N) (level M) k f : ℍ → ℂ) =
      ∑ q : level M ⧸ (level N).subgroupOf (level M), SlashInvariantForm.quotientFunc f q := rfl
  rw [ht]
  unfold weighted
  rw [Finset.sum_apply, Finset.mul_sum]
  exact ((traceEquiv N M).symm.sum_comp
    (fun q => (Real.sqrt (z.im ^ k) : ℂ) * SlashInvariantForm.quotientFunc f q z)).symm

#print axioms trace_coeFn
end QuantitativeEulerOldProjectionHolomorphic
