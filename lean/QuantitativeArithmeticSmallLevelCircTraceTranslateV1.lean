module

public import QuantitativeArithmeticSmallLevelCircModularTraceV1
public import AsymptoticClassicalTraceTranslateV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane ConjAct AsymptoticClassicalCusp AsymptoticClassicalCosets
open scoped ModularForm Pointwise

variable (G H : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℝ) (k : ℤ)

/-- Translation covariance of each literal coset summand, for full modular forms. -/
theorem quotientFunc_translate (f : ModularForm G k) (q : H ⧸ G.subgroupOf H) :
    SlashInvariantForm.quotientFunc (ModularForm.translate f g) (conjugateTraceEquiv G H g q) =
      (SlashInvariantForm.quotientFunc f q) ∣[k] g := by
  induction q using Quotient.inductionOn with
  | h a =>
    have he : conjugateTraceEquiv G H g (QuotientGroup.mk a) =
        QuotientGroup.mk (imageRepresentative (conjugationHom g) H
          (toConjAct g⁻¹ • H) rfl a) := imageEquivOfEq_mk ..
    rw [he, SlashInvariantForm.quotientFunc_mk, SlashInvariantForm.quotientFunc_mk]
    change ((f : ℍ → ℂ) ∣[k] g) ∣[k] (g⁻¹ * a.val * g)⁻¹ =
      ((f : ℍ → ℂ) ∣[k] a.val⁻¹) ∣[k] g
    rw [← SlashAction.slash_mul, ← SlashAction.slash_mul]
    congr 1
    group

/-- Exact covariance of the genuine modular trace. This includes Eisenstein
series and uses no Petersson pairing or vanishing assumption. -/
theorem trace_translate [G.IsFiniteRelIndex H] (f : ModularForm G k) :
    let := conjugate_finiteRelIndex G H g
    (ModularForm.trace (toConjAct g⁻¹ • H) (ModularForm.translate f g) : ℍ → ℂ) =
      ((ModularForm.trace H f : ℍ → ℂ) ∣[k] g) := by
  classical
  let := conjugate_finiteRelIndex G H g
  let := Fintype.ofFinite (H ⧸ G.subgroupOf H)
  let := Fintype.ofFinite
    (↥(toConjAct g⁻¹ • H) ⧸ (toConjAct g⁻¹ • G).subgroupOf (toConjAct g⁻¹ • H))
  change (∑ q : ↥(toConjAct g⁻¹ • H) ⧸
      (toConjAct g⁻¹ • G).subgroupOf (toConjAct g⁻¹ • H),
      SlashInvariantForm.quotientFunc (ModularForm.translate f g) q) =
    ((∑ q : H ⧸ G.subgroupOf H, SlashInvariantForm.quotientFunc f q) ∣[k] g)
  rw [← (conjugateTraceEquiv G H g).sum_comp, SlashAction.sum_slash]
  exact Finset.sum_congr rfl (fun q _ => quotientFunc_translate G H g k f q)

/-- Vanishing of a trace is preserved and reflected by translation. -/
theorem trace_translate_zero_iff [G.IsFiniteRelIndex H] (f : ModularForm G k) :
    let := conjugate_finiteRelIndex G H g
    ModularForm.trace (toConjAct g⁻¹ • H) (ModularForm.translate f g) = 0 ↔
      ModularForm.trace H f = 0 := by
  let := conjugate_finiteRelIndex G H g
  constructor
  · intro h
    apply DFunLike.coe_injective
    apply (SlashAction.slash_eq_zero_iff k g _).mp
    rw [← trace_translate G H g k f, h, FunLike.coe_zero]
  · intro h
    apply DFunLike.coe_injective
    rw [trace_translate G H g k f, h, FunLike.coe_zero, SlashAction.zero_slash]
    rfl

#print axioms quotientFunc_translate
#print axioms trace_translate
#print axioms trace_translate_zero_iff
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
