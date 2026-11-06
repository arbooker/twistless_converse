module

public import AsymptoticClassicalFrickeSquareV1
public import AsymptoticClassicalFrickeCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix AsymptoticClassicalCosets AsymptoticClassicalLSeries
open scoped ModularForm MatrixGroups

/-- Conjugate coset representatives intertwine Fricke with the individual
summands of the ordinary and Fricke-conjugated traces. -/
theorem fricke_quotient_swap (N M : ℕ) (hN : 0 < N) (k : ℤ)
    (f : CuspForm (level N) k)
    (q : CongruenceSubgroup.Gamma0 M ⧸
      (CongruenceSubgroup.Gamma0 N).subgroupOf (CongruenceSubgroup.Gamma0 M)) :
    SlashInvariantForm.quotientFunc (frickeOperator N hN k f) (matrixEquiv N M q) =
      (N : ℂ)^(1-(k : ℂ)/2) •
        ((SlashInvariantForm.quotientFunc f (frickeMatrixEquiv N M hN q)) ∣[k] frickeReal N hN) := by
  induction q using Quotient.inductionOn with
  | h a =>
    have hm : matrixEquiv N M (QuotientGroup.mk a) =
        QuotientGroup.mk ((SpecialLinearGroup.mapGL ℝ).subgroupMap _ a) := rfl
    have hf : frickeMatrixEquiv N M hN (QuotientGroup.mk a) =
        QuotientGroup.mk (frickeMatrixRepresentative N M hN a) := imageEquivOfEq_mk ..
    rw [hm, hf, SlashInvariantForm.quotientFunc_mk, SlashInvariantForm.quotientFunc_mk]
    rw [frickeOperator_coe, normalizedFricke_eq_slash, ModularForm.smul_slash]
    have hd : (((SpecialLinearGroup.mapGL ℝ).subgroupMap
        (CongruenceSubgroup.Gamma0 M) a).val⁻¹).det.val = 1 := by simp
    simp only [σ, hd, zero_lt_one, ite_true, ContinuousAlgEquiv.refl_apply]
    rw [← SlashAction.slash_mul, ← SlashAction.slash_mul]
    congr 2
    change frickeReal N hN * (SpecialLinearGroup.mapGL ℝ a.val)⁻¹ =
      (frickeReal N hN * SpecialLinearGroup.mapGL ℝ a.val * (frickeReal N hN)⁻¹)⁻¹ *
        frickeReal N hN
    simp only [_root_.mul_inv_rev, inv_inv]
    group

/-- The ordinary trace of Fricke is the Fricke translate of the
conjugated old trace. This identity is proved with the actual coset sums. -/
theorem fricke_trace_swap (N M : ℕ) [NeZero N] [NeZero M] (hN : 0 < N) (k : ℤ)
    (f : CuspForm (level N) k) :
    (arithmeticTrace (level N) (level M) k (frickeOperator N hN k f) : ℍ → ℂ) =
      (N : ℂ)^(1-(k : ℂ)/2) •
        ((arithmeticTrace (level N) (frickeOldLevel N M hN) k f : ℍ → ℂ)
          ∣[k] frickeReal N hN) := by
  classical
  let : (level N).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let : (level N).IsFiniteRelIndex (frickeOldLevel N M hN) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := frickeOldLevel N M hN)).symm).1
  let Q := CongruenceSubgroup.Gamma0 M ⧸
    (CongruenceSubgroup.Gamma0 N).subgroupOf (CongruenceSubgroup.Gamma0 M)
  let := Fintype.ofFinite Q
  let := Fintype.ofFinite (level M ⧸ (level N).subgroupOf (level M))
  let := Fintype.ofFinite (frickeOldLevel N M hN ⧸
    (level N).subgroupOf (frickeOldLevel N M hN))
  change (∑ q : level M ⧸ (level N).subgroupOf (level M),
      SlashInvariantForm.quotientFunc (frickeOperator N hN k f) q) =
    (N : ℂ)^(1-(k : ℂ)/2) •
      ((∑ q : frickeOldLevel N M hN ⧸ (level N).subgroupOf (frickeOldLevel N M hN),
        SlashInvariantForm.quotientFunc f q) ∣[k] frickeReal N hN)
  rw [← (matrixEquiv N M).sum_comp,
    ← (frickeMatrixEquiv N M hN).sum_comp,
    SlashAction.sum_slash, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun q _ => fricke_quotient_swap N M hN k f q)

#print axioms fricke_quotient_swap
#print axioms fricke_trace_swap

end AsymptoticClassicalCusp
