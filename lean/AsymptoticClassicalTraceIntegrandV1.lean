module

public import AsymptoticClassicalCosetBridgeV1
public import AsymptoticLowerLevelOldSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalPetersson

open UpperHalfPlane Matrix AsymptoticClassicalCusp AsymptoticClassicalCosets
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups ComplexConjugate

variable (N M : ℕ) (k : ℤ)

/-- The Petersson integrand of one classical trace summand is the
 inverse translate by the corresponding projective representative. -/
theorem quotient_integrand_mk (f : CuspForm (level N) k) (g : CuspForm (level M) k)
    (a : gamma M) (z : ℍ) :
    petersson k (SlashInvariantForm.quotientFunc f
      ((traceEquiv N M).symm (QuotientGroup.mk a))) g z =
      petersson k f g (a.val⁻¹ • z) := by
  obtain ⟨A, hA, he⟩ := a.property
  let b : CongruenceSubgroup.Gamma0 M := ⟨A, hA⟩
  have ha : integralLabel.subgroupMap (CongruenceSubgroup.Gamma0 M) b = a :=
    Subtype.ext he
  have hq : (traceEquiv N M).symm (QuotientGroup.mk a) =
      QuotientGroup.mk ((SpecialLinearGroup.mapGL ℝ).subgroupMap _ b) := by
    apply (traceEquiv N M).injective
    rw [Equiv.apply_symm_apply, traceEquiv_mk, ha]
    rfl
  rw [hq, SlashInvariantForm.quotientFunc_mk]
  have hg : (g : ℍ → ℂ) ∣[k] A⁻¹ = g := by
    rw [ModularForm.SL_slash]
    exact g.slash_action_eq' _ ⟨A⁻¹, (CongruenceSubgroup.Gamma0 M).inv_mem hA, rfl⟩
  have hs := petersson_slash_SL k f g A⁻¹ z
  rw [hg] at hs
  have hm : ((SpecialLinearGroup.mapGL ℝ).subgroupMap _ b).val⁻¹ =
      SpecialLinearGroup.mapGL ℝ A⁻¹ := (map_inv (SpecialLinearGroup.mapGL ℝ) A).symm
  rw [hm]
  change petersson k ((f : ℍ → ℂ) ∣[k] A⁻¹) g z = _
  rw [← he, ← map_inv, integralLabel_action]
  exact hs

theorem quotient_integrand (f : CuspForm (level N) k) (g : CuspForm (level M) k)
    (q : gamma M ⧸ (gamma N).subgroupOf (gamma M)) (z : ℍ) :
    petersson k (SlashInvariantForm.quotientFunc f ((traceEquiv N M).symm q)) g z =
      petersson k f g (q.out.val⁻¹ • z) := by
  have hh := quotient_integrand_mk N M k f g q.out z
  simpa only [QuotientGroup.out_eq'] using hh

variable [NeZero N] [NeZero M]

/-- The actual classical trace has the projective coset-sum integrand
 required for quotient unfolding. -/
theorem trace_integrand (f : CuspForm (level N) k) (g : CuspForm (level M) k) (z : ℍ) :
    petersson k (arithmeticTrace (level N) (level M) k f) g z =
      ∑' q : gamma M ⧸ (gamma N).subgroupOf (gamma M),
        petersson k f g (q.out.val⁻¹ • z) := by
  classical
  let : (level N).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let := Fintype.ofFinite (level M ⧸ (level N).subgroupOf (level M))
  let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
  have ht : (arithmeticTrace (level N) (level M) k f : ℍ → ℂ) =
      ∑ q : level M ⧸ (level N).subgroupOf (level M), SlashInvariantForm.quotientFunc f q := rfl
  rw [ht, tsum_fintype]
  have he : petersson k
      (∑ q : level M ⧸ (level N).subgroupOf (level M), SlashInvariantForm.quotientFunc f q) g z =
      ∑ q : level M ⧸ (level N).subgroupOf (level M),
        petersson k (SlashInvariantForm.quotientFunc f q) g z := by
    simp only [petersson, Finset.sum_apply, map_sum, Finset.sum_mul]
  rw [he, ← (traceEquiv N M).symm.sum_comp
    (fun q => petersson k (SlashInvariantForm.quotientFunc f q) g z)]
  exact Finset.sum_congr rfl (fun q _ => quotient_integrand N M k f g q z)

#print axioms quotient_integrand_mk
#print axioms quotient_integrand
#print axioms trace_integrand

end AsymptoticClassicalPetersson
