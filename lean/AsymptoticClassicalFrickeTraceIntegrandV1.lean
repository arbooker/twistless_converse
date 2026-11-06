module

public import AsymptoticClassicalFrickeCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalPetersson

open UpperHalfPlane Matrix AsymptoticClassicalCusp AsymptoticClassicalCosets
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups ComplexConjugate

variable (N M : ℕ) (hN : 0 < N) (k : ℤ)

theorem fricke_quotient_integrand_mk (f : CuspForm (level N) k)
    (g : CuspForm (frickeOldLevel N M hN) k) (a : frickeOldGroup N M hN) (z : ℍ) :
    petersson k (SlashInvariantForm.quotientFunc f
      ((frickeTraceEquiv N M hN).symm (QuotientGroup.mk a))) g z =
      petersson k f g (a.val⁻¹ • z) := by
  have ha' : a.val ∈ (CongruenceSubgroup.Gamma0 M).map (frickeProjectiveLabel N hN) :=
    (frickeProjectiveLabel_image N M hN).symm ▸ a.property
  obtain ⟨A, hA, he⟩ := ha'
  let b : CongruenceSubgroup.Gamma0 M := ⟨A, hA⟩
  have ha : frickeProjectiveRepresentative N M hN b = a := Subtype.ext he
  have hq : (frickeTraceEquiv N M hN).symm (QuotientGroup.mk a) =
      QuotientGroup.mk (frickeMatrixRepresentative N M hN b) := by
    apply (frickeTraceEquiv N M hN).injective
    rw [Equiv.apply_symm_apply, frickeTraceEquiv_mk, ha]
  let r := frickeMatrixRepresentative N M hN b
  have hg : (g : ℍ → ℂ) ∣[k] r.val⁻¹ = g :=
    g.slash_action_eq' _ ((frickeOldLevel N M hN).inv_mem r.property)
  have hd : (r.val⁻¹).det = 1 :=
    Subgroup.HasDetOne.det_eq ((frickeOldLevel N M hN).inv_mem r.property)
  have hs := petersson_slash k f g r.val⁻¹ z
  rw [hg] at hs
  have heact : a.val⁻¹ • z = r.val⁻¹ • z := by
    rw [← he, ← map_inv, fricke_label_action, map_inv]
    rfl
  rw [hq, SlashInvariantForm.quotientFunc_mk, heact]
  simpa only [σ, hd, Units.val_one, abs_one, Complex.ofReal_one, _root_.one_zpow,
    one_mul, zero_lt_one, ite_true, ContinuousAlgEquiv.refl_apply] using hs

theorem fricke_quotient_integrand (f : CuspForm (level N) k)
    (g : CuspForm (frickeOldLevel N M hN) k)
    (q : frickeOldGroup N M hN ⧸ (gamma N).subgroupOf (frickeOldGroup N M hN)) (z : ℍ) :
    petersson k (SlashInvariantForm.quotientFunc f ((frickeTraceEquiv N M hN).symm q)) g z =
      petersson k f g (q.out.val⁻¹ • z) := by
  have hh := fricke_quotient_integrand_mk N M hN k f g q.out z
  simpa only [QuotientGroup.out_eq'] using hh

variable [NeZero N] [NeZero M]

/-- The actual trace to the Fricke-conjugated old level, expressed in
 the projective cosets used by quotient integration. -/
theorem fricke_trace_integrand (f : CuspForm (level N) k)
    (g : CuspForm (frickeOldLevel N M hN) k) (z : ℍ) :
    petersson k (arithmeticTrace (level N) (frickeOldLevel N M hN) k f) g z =
      ∑' q : frickeOldGroup N M hN ⧸ (gamma N).subgroupOf (frickeOldGroup N M hN),
        petersson k f g (q.out.val⁻¹ • z) := by
  classical
  let : (level N).IsFiniteRelIndex (frickeOldLevel N M hN) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := frickeOldLevel N M hN)).symm).1
  let := Fintype.ofFinite (frickeOldLevel N M hN ⧸ (level N).subgroupOf (frickeOldLevel N M hN))
  let := Fintype.ofFinite (frickeOldGroup N M hN ⧸ (gamma N).subgroupOf (frickeOldGroup N M hN))
  have ht : (arithmeticTrace (level N) (frickeOldLevel N M hN) k f : ℍ → ℂ) =
      ∑ q : frickeOldLevel N M hN ⧸ (level N).subgroupOf (frickeOldLevel N M hN),
        SlashInvariantForm.quotientFunc f q := rfl
  rw [ht, tsum_fintype]
  have he : petersson k
      (∑ q : frickeOldLevel N M hN ⧸ (level N).subgroupOf (frickeOldLevel N M hN),
        SlashInvariantForm.quotientFunc f q) g z =
      ∑ q : frickeOldLevel N M hN ⧸ (level N).subgroupOf (frickeOldLevel N M hN),
        petersson k (SlashInvariantForm.quotientFunc f q) g z := by
    simp only [petersson, Finset.sum_apply, map_sum, Finset.sum_mul]
  rw [he, ← (frickeTraceEquiv N M hN).symm.sum_comp
    (fun q => petersson k (SlashInvariantForm.quotientFunc f q) g z)]
  exact Finset.sum_congr rfl (fun q _ => fricke_quotient_integrand N M hN k f g q z)

#print axioms fricke_quotient_integrand_mk
#print axioms fricke_quotient_integrand
#print axioms fricke_trace_integrand

end AsymptoticClassicalPetersson
