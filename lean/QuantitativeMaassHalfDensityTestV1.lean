module

public import QuantitativeMaassHalfDensityPairingV1
public import QuantitativeMaassHalfDensityGeneratorV1
public import QuantitativeMaassCuspAveragedTestV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass

theorem logTest_memLp (A B : ℝ) (g : ℝ → ℂ) (hg : Continuous g) :
    MemLp g 2 (volume.restrict (Icc A B)) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hg.norm.continuousOn
  apply MemLp.of_bound hg.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC (mem_image_of_mem _ hx)

def logTestVector (A B : ℝ) (g : ℝ → ℂ) (hg : Continuous g) :
    Lp ℂ 2 (volume.restrict (Icc A B)) := (logTest_memLp A B g hg).toLp g

theorem logTestVector_ae (A B : ℝ) (g : ℝ → ℂ) (hg : Continuous g) :
    (logTestVector A B g hg : ℝ → ℂ)=ᵐ[volume.restrict (Icc A B)] g :=
  MemLp.coeFn_toLp _

theorem logHalfDensity_continuous (g : ℝ → ℂ) (hg : Continuous g) :
    Continuous (logHalfDensity g) := by
  unfold logHalfDensity
  fun_prop

theorem logHalfDensity_smooth (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (logHalfDensity g) := by
  exact (Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_id.neg.div_const 2))).mul (hg.comp Real.contDiff_exp)

theorem logHalfDensity_second_continuous (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    Continuous (deriv (deriv (logHalfDensity g))) :=
  ((contDiff_infty_iff_deriv.mp (logHalfDensity_smooth g hg)).2).continuous_deriv (by simp)

/-- Exact transformation of genuine continuous height test vectors. -/
theorem localHalfDensity_heightTest (w A B : ℝ) (hw : 0<w)
    (g : ℝ → ℂ) (hg : Continuous g) :
    localHalfDensity w A B hw
      (heightTestVector _ (upperRectangle_compact 0 w (Real.exp A) (Real.exp B) (Real.exp_pos A)) g hg)=
      logTestVector A B (logHalfDensity g) (logHalfDensity_continuous g hg) := by
  apply Lp.ext
  exact (localHalfDensity_representative_ae w A B hw _ g (heightTestVector_ae _ _ g hg)).trans
    (logTestVector_ae A B _ _).symm

/-- Differential conjugation on local L2 test vectors, using the already
proved scalar generator identity and exact representative formulas. -/
theorem localHalfDensity_laplacianTest (w A B : ℝ) (hw : 0<w)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    localHalfDensity w A B hw
      (heightTestVector _ (upperRectangle_compact 0 w (Real.exp A) (Real.exp B) (Real.exp_pos A))
        (heightLaplacianTest g) (heightLaplacianTest_continuous g hg))=
      -logTestVector A B (deriv (deriv (logHalfDensity g))) (logHalfDensity_second_continuous g hg)+
        (1/4:ℂ) • logTestVector A B (logHalfDensity g) (logHalfDensity_continuous g hg.continuous) := by
  apply Lp.ext
  have h1 := localHalfDensity_representative_ae w A B hw _ (heightLaplacianTest g)
    (heightTestVector_ae _
      (upperRectangle_compact 0 w (Real.exp A) (Real.exp B) (Real.exp_pos A))
      _ (heightLaplacianTest_continuous g hg))
  filter_upwards [h1, logTestVector_ae A B (deriv (deriv (logHalfDensity g)))
    (logHalfDensity_second_continuous g hg),logTestVector_ae A B (logHalfDensity g)
    (logHalfDensity_continuous g hg.continuous),
    Lp.coeFn_add (-logTestVector A B _ (logHalfDensity_second_continuous g hg))
      ((1/4:ℂ) • logTestVector A B _ (logHalfDensity_continuous g hg.continuous)),
    Lp.coeFn_neg (logTestVector A B _ (logHalfDensity_second_continuous g hg)),
    Lp.coeFn_smul (1/4:ℂ) (logTestVector A B _ (logHalfDensity_continuous g hg.continuous))]
      with x hleft hsecond hvalue hadd hneg hsmul
  simp only [hleft,hadd,Pi.add_apply,hneg,Pi.neg_apply,hsmul,Pi.smul_apply,
    hsecond,hvalue,smul_eq_mul]
  have he := logHalfDensity_generator g (deriv g) (deriv (deriv g))
    (fun y _ => ((contDiff_infty_iff_deriv.mp hg).1 y).hasDerivAt)
    (fun y _ => ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hg).2).1 y).hasDerivAt) x
  rw [he]
  unfold heightLaplacianTest logHalfDensity
  ring

#print axioms localHalfDensity_heightTest
#print axioms localHalfDensity_laplacianTest

end QuantitativeMaass
