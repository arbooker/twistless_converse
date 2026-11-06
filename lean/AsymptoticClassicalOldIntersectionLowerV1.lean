module

public import AsymptoticClassicalOldIntersectionPeriodsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix Filter Topology
open scoped ModularForm Manifold

/-- A real lower unipotent, before any projective quotient. -/
def lowerTranslation (r : ℝ) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; r, 1] (by simp)

theorem S_translation_intertwine (r : ℝ) :
    SpecialLinearGroup.mapGL ℝ ModularGroup.S * AsymptoticMobiusFold.translation (-r) =
      lowerTranslation r * SpecialLinearGroup.mapGL ℝ ModularGroup.S := by
  apply Units.ext
  change (ModularGroup.S.val.map (fun a : ℤ => (a : ℝ))) *
    (AsymptoticMobiusFold.translation (-r)).val =
      (lowerTranslation r).val * (ModularGroup.S.val.map (fun a : ℤ => (a : ℝ)))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.S, AsymptoticMobiusFold.translation, lowerTranslation,
      GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

/-- Translation matrices act by literal horizontal translation in every
 integral weight. -/
theorem translation_slash_apply (k : ℤ) (f : ℍ → ℂ) (r : ℝ) (z : ℍ) :
    (f ∣[k] AsymptoticMobiusFold.translation r) z = f (r +ᵥ z) := by
  have ha : AsymptoticMobiusFold.translation r • z = r +ᵥ z := by
    apply UpperHalfPlane.ext
    rw [AsymptoticMobiusFold.translation_action, UpperHalfPlane.coe_vadd, add_comm]
  have hd : denom (AsymptoticMobiusFold.translation r) z = 1 := by
    change (0 : ℂ) * (z : ℂ) + 1 = 1
    ring
  simp only [ModularForm.slash_def]
  rw [hd, AsymptoticMobiusFold.translation_det]
  simp only [σ, AsymptoticMobiusFold.translation_det, zero_lt_one, ite_true,
    ContinuousAlgEquiv.refl_apply, abs_one, Complex.ofReal_one, _root_.one_zpow,
    mul_one, ha]

/-- Accumulating lower unipotent slash symmetries force an arithmetic cusp
 form to vanish; applying S turns them into small ordinary periods. -/
theorem cusp_zero_of_small_lower_symmetries
    {G : Subgroup (GL (Fin 2) ℝ)} [G.HasDetOne] [G.IsArithmetic]
    (k : ℤ) (f : CuspForm G k) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) (hne : ∀ n, r n ≠ 0)
    (hsym : ∀ n, (f : ℍ → ℂ) ∣[k] lowerTranslation (r n) = f) : f = 0 := by
  let S := SpecialLinearGroup.mapGL ℝ ModularGroup.S
  let g : ℍ → ℂ := (f : ℍ → ℂ) ∣[k] S
  have hg : MDiff g := (CuspForm.translate f S).holo'
  have hzero : IsZeroAtImInfty g := by
    change IsZeroAtImInfty ((f : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ ModularGroup.S)
    exact CuspFormClass.zero_at_infty_slash f ModularGroup.S
  have hp : ∀ n z, g (-r n +ᵥ z) = g z := by
    intro n z
    rw [← translation_slash_apply k g (-r n) z]
    change (((f : ℍ → ℂ) ∣[k] S) ∣[k] AsymptoticMobiusFold.translation (-r n)) z = _
    rw [← SlashAction.slash_mul, S_translation_intertwine, SlashAction.slash_mul, hsym]
  have hgz : g = 0 := zero_of_small_periods hg hzero (fun n => -r n)
    (by simpa only [neg_zero] using hr.neg) (fun n => neg_ne_zero.mpr (hne n)) hp
  apply DFunLike.coe_injective
  change (f : ℍ → ℂ) = 0
  have hz := congrArg (fun u : ℍ → ℂ => u ∣[k] S⁻¹) hgz
  change (((f : ℍ → ℂ) ∣[k] S) ∣[k] S⁻¹) = (0 : ℍ → ℂ) ∣[k] S⁻¹ at hz
  simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
    SlashAction.zero_slash] using hz

#print axioms S_translation_intertwine
#print axioms translation_slash_apply
#print axioms cusp_zero_of_small_lower_symmetries

end AsymptoticClassicalCusp
