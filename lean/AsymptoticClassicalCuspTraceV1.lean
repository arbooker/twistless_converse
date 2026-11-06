module

public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

variable {G H : Subgroup (GL (Fin 2) ℝ)} [G.HasDetOne] [H.HasDetOne] (k : ℤ)

/-- Inclusion of classical cusp forms on an overgroup into the smaller level. -/
def restrict (h : G ≤ H) : CuspForm H k →ₗ[ℂ] CuspForm G k where
  toFun f := {
    toFun := f
    slash_action_eq' := fun g hg => f.slash_action_eq' g (h hg)
    holo' := f.holo'
    zero_at_cusps' := fun hc => f.zero_at_cusps' (hc.mono h) }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrict_apply (h : G ≤ H) (f : CuspForm H k) (z : ℍ) :
    restrict k h f z = f z := rfl

theorem restrict_injective (h : G ≤ H) : Function.Injective (restrict k h) := by
  intro f g he
  exact CuspForm.ext (fun z => congrArg (fun u : CuspForm G k => u z) he)

variable [G.IsFiniteRelIndex H]

/-- The classical coset trace, as a complex linear map. All matrices of the
 target have determinant one, so the GL slash action is complex linear. -/
def trace : CuspForm G k →ₗ[ℂ] CuspForm H k where
  toFun := fun f : CuspForm G k => CuspForm.trace H f
  map_add' f g := by
    classical
    apply CuspForm.ext
    intro z
    simp only [CuspForm.coe_trace, Finset.sum_apply, add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    induction q using Quotient.inductionOn with
    | h r => simp [SlashInvariantForm.quotientFunc_mk]
  map_smul' c f := by
    change CuspForm.trace H (c • f) = c • CuspForm.trace H f
    classical
    apply CuspForm.ext
    intro z
    simp only [CuspForm.coe_trace, Finset.sum_apply, smul_apply,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro q _
    induction q using Quotient.inductionOn with
    | h r =>
      simp [SlashInvariantForm.quotientFunc_mk,
        ModularForm.smul_slash, σ, Subgroup.HasDetOne.det_eq (H.inv_mem r.property)]

@[simp] theorem trace_apply (f : CuspForm G k) :
    trace k f = CuspForm.trace H f := rfl

/-- On an old form the unnormalised trace is multiplication by the index. -/
theorem trace_restrict (h : G ≤ H) (f : CuspForm H k) :
    trace k (restrict k h f) = (Nat.card (H ⧸ G.subgroupOf H) : ℂ) • f := by
  classical
  let := Fintype.ofFinite (H ⧸ G.subgroupOf H)
  apply CuspForm.ext
  intro z
  change (∑ q : H ⧸ G.subgroupOf H,
    SlashInvariantForm.quotientFunc (restrict k h f) q) z = _
  have hq (q : H ⧸ G.subgroupOf H) :
      SlashInvariantForm.quotientFunc (restrict k h f) q = (f : ℍ → ℂ) := by
    induction q using Quotient.inductionOn with
    | h r =>
      change (f : ℍ → ℂ) ∣[k] r.val⁻¹ = _
      exact f.slash_action_eq' _ (H.inv_mem r.property)
  simp [hq, Nat.card_eq_fintype_card]

#print axioms restrict_injective
#print axioms trace_restrict

end AsymptoticClassicalCusp
