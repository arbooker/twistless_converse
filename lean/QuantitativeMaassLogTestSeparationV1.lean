module

public import QuantitativeMaassHalfDensityTestV1
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass

theorem logTestVector_inner (A B : ℝ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (f : Lp ℂ 2 (volume.restrict (Icc A B))) :
    inner ℂ (logTestVector A B ψ hψ) f=∫ y in Icc A B, star (ψ y)*f y := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [logTestVector_ae A B ψ hψ] with y hy
  simp only [hy,RCLike.inner_apply]
  exact mul_comm _ _

/-- Smooth tests supported in the band separate actual local L2 classes.
The open-interior test theorem suffices because the two endpoints are null. -/
theorem logTestVector_separates (A B : ℝ)
    (f : Lp ℂ 2 (volume.restrict (Icc A B)))
    (h : ∀ (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ), Function.support ψ⊆Icc A B →
      inner ℂ (logTestVector A B ψ hψ.continuous) f=0) : f=0 := by
  have hi : IntegrableOn (f : ℝ → ℂ) (Icc A B) volume :=
    (Lp.memLp f).integrable (by norm_num)
  have hloc : LocallyIntegrableOn (f : ℝ → ℂ) (Ioo A B) volume :=
    (hi.mono_set Ioo_subset_Icc_self).locallyIntegrableOn
  have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun ψ hψ hcompact hs => ?_)
  · have ha : ∀ᵐ y ∂volume.restrict (Ioo A B), f y=0 :=
      (ae_restrict_iff' measurableSet_Ioo).mpr hz
    have hac : volume.restrict (Icc A B) ≪ volume.restrict (Ioo A B) := by
      rw [restrict_Ioo_eq_restrict_Icc]
    exact Lp.eq_zero_iff_ae_eq_zero.mpr (hac.ae_eq ha)
  · have hψc : ContDiff ℝ ∞ (fun y => (ψ y:ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
    have hsupport : Function.support (fun y => (ψ y:ℂ))⊆Icc A B := by
      intro y hy
      have hn : ψ y≠0 := by simpa only [Function.mem_support,ne_eq,Complex.ofReal_eq_zero] using hy
      exact Ioo_subset_Icc_self (hs (subset_closure hn))
    have ht := h _ hψc hsupport
    rw [logTestVector_inner] at ht
    have he : (fun y => (ψ y:ℝ) • f y)=fun y => star (ψ y:ℂ)*f y := by
      funext y
      simp only [Complex.real_smul,Complex.star_def,Complex.conj_ofReal]
    rw [he]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc A B)]
    · exact ht
    · intro y hy
      have hp : ψ y=0 := by
        by_contra hn
        exact hy (Ioo_subset_Icc_self (hs (subset_closure hn)))
      simp only [hp,Complex.ofReal_zero,star_zero,zero_mul]

#print axioms logTestVector_separates

end QuantitativeMaass
