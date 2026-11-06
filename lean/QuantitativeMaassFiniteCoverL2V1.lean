module

public import QuantitativeMaassAutomorphicL2V1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QuantitativeMaass.AutomorphicL2

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
    (μ : Measure α) (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (H J : Subgroup G) (hHJ : H ≤ J) [Finite (J ⧸ H.subgroupOf J)]
    (ρ σ : α → ℝ≥0∞) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hnρ : ∀ x, ∑' g : J, ρ (g.val • x) = 1)
    (hnσ : ∀ x, ∑' h : H, σ (h.val • x) = 1)

include hmp hHJ hρ hσ hnρ hnσ in
theorem lintegral_cover (f : α → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ g : J, ∀ x, f (g.val • x) = f x) :
    (∫⁻ x, f x ∂μ.withDensity σ) =
      ((H.subgroupOf J).index : ℝ≥0∞) * ∫⁻ x, f x ∂μ.withDensity ρ := by
  apply OrbitIntegral.lintegral_finite_cover μ (fun g : J => hmp g.val)
    (H.subgroupOf J) ρ σ hρ hσ hnρ
  · intro x
    have he := (Subgroup.subgroupOfEquivOfLe hHJ).toEquiv.tsum_eq
      (fun h : H => σ (h.val • x))
    exact he.trans (hnσ x)
  · exact hf
  · exact hinv

include hmp hHJ hρ hσ hnρ hnσ in
theorem eLpNorm_cover (f : α → ℂ) (hf : Measurable f)
    (hinv : ∀ g : J, ∀ x, f (g.val • x) = f x) :
    eLpNorm f 2 (μ.withDensity σ) =
      ((H.subgroupOf J).index : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        eLpNorm f 2 (μ.withDensity ρ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (μ := μ.withDensity σ)
      (f := f) (by norm_num) (by norm_num) hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (μ := μ.withDensity ρ)
      (f := f) (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  rw [lintegral_cover μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ
    (fun x => ‖f x‖ₑ ^ (2 : ℝ)) (by fun_prop) (by intro g x; rw [hinv]),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]

/-- The literal identity of functions along a finite automorphic cover. -/
def coverRepresentative : representatives J (μ.withDensity ρ) →ₗ[ℂ]
    representatives H (μ.withDensity σ) where
  toFun f := ⟨f.val, f.property.1,
    (fun h x => f.property.2.1 ⟨h.val, hHJ h.property⟩ x), (by
      change eLpNorm f.val 2 (μ.withDensity σ) < ∞
      rw [eLpNorm_cover μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ f.val
        f.property.1 f.property.2.1]
      exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp))
        f.property.2.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coverRepresentative_norm (f : representatives J (μ.withDensity ρ)) :
    ‖denseEmbedding H (μ.withDensity σ)
      (coverRepresentative μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ f)‖ =
      Real.sqrt ((H.subgroupOf J).index : ℝ) *
        ‖denseEmbedding J (μ.withDensity ρ) f‖ := by
  rw [embedding_norm, embedding_norm]
  change (eLpNorm f.val 2 (μ.withDensity σ)).toReal = _
  rw [eLpNorm_cover μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ f.val
    f.property.1 f.property.2.1, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  simp only [ENNReal.toReal_natCast, Real.sqrt_eq_rpow]

/-- The genuine finite-cover inclusion extends to a bounded operator between
the automorphic Hilbert completions, with its sharp square-root index norm. -/
def coverOperator : space J (μ.withDensity ρ) →L[ℂ] space H (μ.withDensity σ) :=
  ((denseEmbedding H (μ.withDensity σ)).comp
    (coverRepresentative μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ)).extendOfNorm
      (denseEmbedding J (μ.withDensity ρ))

theorem coverOperator_apply (f : representatives J (μ.withDensity ρ)) :
    coverOperator μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ
      (denseEmbedding J (μ.withDensity ρ) f) =
    denseEmbedding H (μ.withDensity σ)
      (coverRepresentative μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ f) := by
  apply LinearMap.extendOfNorm_eq (denseEmbedding_dense J (μ.withDensity ρ))
  exact ⟨Real.sqrt ((H.subgroupOf J).index : ℝ), fun f =>
    (coverRepresentative_norm μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ f).le⟩

theorem coverOperator_norm_le :
    ‖coverOperator μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ‖ ≤
      Real.sqrt ((H.subgroupOf J).index : ℝ) := by
  apply LinearMap.opNorm_extendOfNorm_le (denseEmbedding_dense J (μ.withDensity ρ))
    (Real.sqrt_nonneg _)
  intro f
  exact (coverRepresentative_norm μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ f).le

#print axioms coverOperator_apply
#print axioms coverOperator_norm_le

end QuantitativeMaass.AutomorphicL2
