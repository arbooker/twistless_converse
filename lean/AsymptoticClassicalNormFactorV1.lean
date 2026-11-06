module

public import AsymptoticClassicalCuspTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace AsymptoticClassicalNorm

open UpperHalfPlane SlashInvariantForm
open scoped ModularForm MatrixGroups

variable {G H : Subgroup (GL (Fin 2) ℝ)} [G.HasDetOne] [H.HasDetOne]
  [G.IsFiniteRelIndex H] (hGH : G ≤ H) {k : ℤ} (f : ModularForm G k)

local notation "Q" => H ⧸ G.subgroupOf H

/-- Delete the identity coset from the product defining the relative norm. -/
def remainder : ModularForm G (k * ((Nat.card Q - 1 : ℕ) : ℤ)) := by
  classical
  let := Fintype.ofFinite Q
  let q₀ : Q := ⟦(1 : H)⟧
  let s : Finset Q := Finset.univ.erase q₀
  have hs : s.card = Nat.card Q - 1 := by simp [s, Nat.card_eq_fintype_card]
  refine {
    toFun := ∏ q ∈ s, quotientFunc f q
    slash_action_eq' := ?_
    holo' := ?_
    bdd_at_cusps' := ?_ }
  · intro g hg
    rw [← hs, ModularForm.prod_slash]
    have hd : g.det.val = 1 := congrArg Units.val (Subgroup.HasDetOne.det_eq hg)
    simp only [hd, abs_one, one_zpow, one_smul]
    simp_rw [quotientFunc_smul f (hGH hg)]
    let e : Q ≃ Q := MulAction.toPerm (⟨g, hGH hg⟩ : H)⁻¹
    have he : e q₀ = q₀ := by
      change (⟦(⟨g, hGH hg⟩ : H)⁻¹ * 1⟧ : Q) = ⟦(1 : H)⟧
      rw [QuotientGroup.eq]
      change (g⁻¹ * 1)⁻¹ * 1 ∈ G
      simpa using hg
    apply Finset.prod_equiv e
    · intro q
      simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]
      exact not_congr ((e.injective.eq_iff).symm.trans (by rw [he]))
    · intro q _
      rfl
  · exact MDifferentiable.prod (Quotient.forall.mpr fun ⟨r, hr⟩ _ =>
      (ModularForm.translate f r⁻¹).holo')
  · intro c hc γ hγ
    subst c
    simp only [← hs, ModularForm.prod_slash,
      IsBoundedAtImInfty, Filter.BoundedAtFilter]
    apply Asymptotics.IsBigO.const_smul_left
    rw [show (1 : ℍ → ℝ) = fun z => ∏ q ∈ s, (1 : ℝ) by ext; simp,
      Finset.prod_fn]
    apply Asymptotics.IsBigO.finsetProd
    exact Quotient.forall.mpr fun ⟨r, hr⟩ _ =>
      (ModularForm.translate f r⁻¹).bdd_at_cusps'
        ((hc.mono hGH).of_isFiniteRelIndex_conj hr) γ rfl

/-- The norm contains the original form as the identity-coset factor. -/
theorem norm_eq_mul_remainder :
    (ModularForm.norm H f : ℍ → ℂ) = f * remainder hGH f := by
  classical
  let := Fintype.ofFinite Q
  change (∏ q : Q, quotientFunc f q) =
    (f : ℍ → ℂ) * ∏ q ∈ Finset.univ.erase (⟦(1 : H)⟧ : Q), quotientFunc f q
  have hq : quotientFunc f (⟦(1 : H)⟧ : Q) = (f : ℍ → ℂ) := by simp
  rw [← hq]
  exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ _)).symm

#print axioms norm_eq_mul_remainder

end AsymptoticClassicalNorm
