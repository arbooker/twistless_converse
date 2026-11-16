module

public import QuantitativeMaassAbelCosineRepresentationV1
public import QuantitativeMaassAbelSpectralInitialV1
public import QuantitativeMaassAbelInitialGraphV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

/-- The normalized geometric and spectral approximate identities determine
the recovered position. The factor two is forced by positive-time integration. -/
theorem regularizedAbelPosition_initial (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (c : AutomorphicSpace N×AutomorphicSpace N)
    (hcT : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) :
    c.1=(2:ℂ) • Wave.resolventCutoffOperator (friedrichsResolvent N) ε f := by
  let R : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hR (n : ℕ) : 0<R n := by dsimp [R]; positivity
  have hR0 : Tendsto R atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let P := Wave.resolventCutoffOperator (friedrichsResolvent N) ε
  have hg : Tendsto (fun n => (2:ℂ) • P (abelNormalizedOperator N (R n) (hR n) f)) atTop
      (𝓝 ((2:ℂ) • P f)) :=
    (P.continuous.tendsto _ |>.comp (abelNormalizedOperator_tendsto atTop N R hR hR0 f)).const_smul (2:ℂ)
  have hw := abelNormalizedWavePacket_tendsto atTop N R hR hR0 c.1
  have he (n : ℕ) : (2:ℂ) • P (abelNormalizedOperator N (R n) (hR n) f)=
      coshWavePacket N (abelNormalizedTest (R n)) (abelNormalizedTest_smooth (R n))
        (R n) (hR n).le (abelNormalizedTest_support (R n) (hR n)) c.1 :=
    regularizedAbelPosition_packet N ε hε f c hcT (abelNormalizedTest (R n))
      (abelNormalizedTest_smooth (R n)) (abelNormalizedTest_compact (R n) (hR n))
      (abelNormalizedTest_real (R n)) (R n) (hR n).le (abelNormalizedTest_support (R n) (hR n))
  exact (tendsto_nhds_unique hg (hw.congr' (Eventually.of_forall (fun n => (he n).symm)))).symm

/-- Literal regularized geometric=spectral identity for every original real
smooth compact q-test. No unknown position or velocity remains. -/
theorem regularizedAbelKernel_eq_coshWavePacket (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Wave.resolventCutoffOperator (friedrichsResolvent N) ε (abelKernelOperator N F hF hc R hR hs f)=
      coshWavePacket N F hF R hR hs (Wave.resolventCutoffOperator (friedrichsResolvent N) ε f) := by
  obtain ⟨c,hcT,_⟩ := regularizedAbelDistribution_cauchy N ε hε f
  have he := regularizedAbelPosition_packet N ε hε f c hcT F hF hc hr R hR hs
  rw [regularizedAbelPosition_initial N ε hε f c hcT,map_smul] at he
  exact (smul_right_injective _ (by norm_num : (2:ℂ)≠0)) he

/-- The actual normalized geometric Abel kernel equals the actual shifted
quotient-wave packet. The cutoff is removed strongly on arbitrary L2 vectors. -/
theorem abelKernelOperator_eq_coshWavePacket (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    abelKernelOperator N F hF hc R hR hs=coshWavePacket N F hF R hR hs := by
  apply ContinuousLinearMap.ext
  intro f
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0<ε n := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hg := Wave.friedrichsCutoff_tendsto atTop N ε (Eventually.of_forall hε) hε0
    (abelKernelOperator N F hF hc R hR hs f)
  have hw := (coshWavePacket N F hF R hR hs).continuous.tendsto _ |>.comp
    (Wave.friedrichsCutoff_tendsto atTop N ε (Eventually.of_forall hε) hε0 f)
  apply tendsto_nhds_unique hg
  apply hw.congr'
  filter_upwards with n
  exact (regularizedAbelKernel_eq_coshWavePacket N (ε n) (hε n) f F hF hc hr R hR hs).symm

#print axioms regularizedAbelPosition_initial
#print axioms regularizedAbelKernel_eq_coshWavePacket
#print axioms abelKernelOperator_eq_coshWavePacket

end QuantitativeMaass
