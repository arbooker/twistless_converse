module

public import AsymptoticClassicalFrickeCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane ConjAct AsymptoticClassicalCosets
open scoped ModularForm Pointwise

variable (G H : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℝ)

def conjugationHom : GL (Fin 2) ℝ →* GL (Fin 2) ℝ :=
  MulDistribMulAction.toMonoidEnd (ConjAct (GL (Fin 2) ℝ)) (GL (Fin 2) ℝ) (toConjAct g⁻¹)

@[simp] theorem conjugationHom_apply (a : GL (Fin 2) ℝ) :
    conjugationHom g a = g⁻¹*a*g := rfl

/-- Relative cosets are transported by conjugation, with the actual
matrix representatives retained. -/
def conjugateTraceEquiv : H ⧸ G.subgroupOf H ≃
    ↥(toConjAct g⁻¹ • H) ⧸ (toConjAct g⁻¹ • G).subgroupOf (toConjAct g⁻¹ • H) :=
  imageEquivOfEq (conjugationHom g) G H _ _ (by
    intro a ha
    have hi : Function.Injective (conjugationHom g) :=
      (MulAction.bijective (toConjAct g⁻¹)).injective
    have he : a = 1 := hi (ha.trans (map_one (conjugationHom g)).symm)
    rw [he]
    exact G.one_mem) rfl rfl

/-- Finite relative index is preserved by conjugating both groups. -/
theorem conjugate_finiteRelIndex [G.IsFiniteRelIndex H] :
    (toConjAct g⁻¹ • G).IsFiniteRelIndex (toConjAct g⁻¹ • H) :=
  Subgroup.IsFiniteRelIndex.map (conjugationHom g) (inferInstance : G.IsFiniteRelIndex H)

variable (k : ℤ)

theorem quotientFunc_translate (f : CuspForm G k) (q : H ⧸ G.subgroupOf H) :
    SlashInvariantForm.quotientFunc (CuspForm.translate f g) (conjugateTraceEquiv G H g q) =
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

/-- Exact translation covariance of the classical coset trace. This
holds before imposing any level, arithmetic, or determinant-sign restriction
on the translating matrix. -/
theorem trace_translate [G.IsFiniteRelIndex H] (f : CuspForm G k) :
    let := conjugate_finiteRelIndex G H g
    (CuspForm.trace (toConjAct g⁻¹ • H) (CuspForm.translate f g) : ℍ → ℂ) =
      ((CuspForm.trace H f : ℍ → ℂ) ∣[k] g) := by
  classical
  let := conjugate_finiteRelIndex G H g
  let := Fintype.ofFinite (H ⧸ G.subgroupOf H)
  let := Fintype.ofFinite
    (↥(toConjAct g⁻¹ • H) ⧸ (toConjAct g⁻¹ • G).subgroupOf (toConjAct g⁻¹ • H))
  change (∑ q : ↥(toConjAct g⁻¹ • H) ⧸
      (toConjAct g⁻¹ • G).subgroupOf (toConjAct g⁻¹ • H),
      SlashInvariantForm.quotientFunc (CuspForm.translate f g) q) =
    ((∑ q : H ⧸ G.subgroupOf H, SlashInvariantForm.quotientFunc f q) ∣[k] g)
  rw [← (conjugateTraceEquiv G H g).sum_comp, SlashAction.sum_slash]
  exact Finset.sum_congr rfl (fun q _ => quotientFunc_translate G H g k f q)

#print axioms conjugateTraceEquiv
#print axioms conjugate_finiteRelIndex
#print axioms quotientFunc_translate
#print axioms trace_translate

end AsymptoticClassicalCusp
