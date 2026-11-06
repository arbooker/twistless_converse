module

public import AsymptoticClassicalFrickeGroupV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane ConjAct
open scoped ModularForm Pointwise

variable (G : Subgroup (GL (Fin 2) ℝ)) [G.HasDetOne] (k : ℤ)
variable (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)

/-- Positive-determinant translation is complex linear between the
 actual classical cusp spaces on conjugate groups. -/
def translateLinear : CuspForm G k →ₗ[ℂ] CuspForm (toConjAct g⁻¹ • G) k where
  toFun f := CuspForm.translate f g
  map_add' f h := by
    apply DFunLike.coe_injective
    change ((f + h : CuspForm G k) : ℍ → ℂ) ∣[k] g = _
    rw [FunLike.coe_add, SlashAction.add_slash]
    rfl
  map_smul' c f := by
    apply DFunLike.coe_injective
    change ((c • f : CuspForm G k) : ℍ → ℂ) ∣[k] g = _
    rw [FunLike.coe_smul, ModularForm.smul_slash]
    simp only [σ, hg, ite_true, ContinuousAlgEquiv.refl_apply]
    rfl

@[simp] theorem translateLinear_coe (f : CuspForm G k) :
    (translateLinear G k g hg f : ℍ → ℂ) = (f : ℍ → ℂ) ∣[k] g := rfl

theorem translateLinear_injective : Function.Injective (translateLinear G k g hg) := by
  intro f h he
  apply DFunLike.coe_injective
  have hh := congrArg (fun u : CuspForm (toConjAct g⁻¹ • G) k =>
    (u : ℍ → ℂ) ∣[k] g⁻¹) he
  simpa only [translateLinear_coe, ← SlashAction.slash_mul, mul_inv_cancel,
    SlashAction.slash_one] using hh

theorem translateLinear_surjective : Function.Surjective (translateLinear G k g hg) := by
  intro f
  have hgroup : G = toConjAct (g⁻¹)⁻¹ • (toConjAct g⁻¹ • G) := by
    simp only [inv_inv, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  let h : CuspForm G k := CuspForm.mcast rfl (CuspForm.translate f g⁻¹) hgroup
  refine ⟨h, ?_⟩
  apply DFunLike.coe_injective
  change ((f : ℍ → ℂ) ∣[k] g⁻¹) ∣[k] g = (f : ℍ → ℂ)
  rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]

/-- An equivalence obtained by translating back with the inverse matrix. -/
def translateEquiv : CuspForm G k ≃ₗ[ℂ] CuspForm (toConjAct g⁻¹ • G) k :=
  LinearEquiv.ofBijective (translateLinear G k g hg)
    ⟨translateLinear_injective G k g hg, translateLinear_surjective G k g hg⟩

include hg in
theorem conjugate_finrank :
    Module.finrank ℂ (CuspForm (toConjAct g⁻¹ • G) k) = Module.finrank ℂ (CuspForm G k) :=
  (translateEquiv G k g hg).finrank_eq.symm

#print axioms translateLinear_injective
#print axioms translateLinear_surjective
#print axioms conjugate_finrank

end AsymptoticClassicalCusp
