module

public import QuantitativeMaassAbelZeroVelocityV1
public import QuantitativeMaassPositiveTimeCosineActionV1
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Distributions InnerProductSpace

namespace QuantitativeMaass

/-- The full-line integral of an even integrable vector curve is twice its
positive-half-line integral. This records the normalization explicitly. -/
theorem integral_even_eq_two_half {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (g : ℝ → H) (hg : Integrable g) (he : ∀ t,g (-t)=g t) :
    (∫ t,g t)=(2:ℂ) • (∫ t in Ioi (0:ℝ),g t) := by
  have hn : (∫ t in Iic (0:ℝ),g t)=∫ t in Ioi (0:ℝ),g t := by
    have h := integral_comp_neg_Ioi (0:ℝ) g
    simp only [he,neg_zero] at h
    exact h.symm
  calc
    _ = (∫ t in Iic (0:ℝ),g t)+∫ t in Ioi (0:ℝ),g t := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hg.integrableOn hg.integrableOn,
        Iic_union_Ioi,Measure.restrict_univ]
    _ = _ := by rw [hn,two_smul]

/-- The actual cosine packet is exactly twice the positive-time integral. -/
theorem coshWavePacket_eq_two_half (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (v : AutomorphicSpace N) :
    coshWavePacket N F hF R hR hs v=
      (2:ℂ) • (∫ t in Ioi (0:ℝ),coshTimeTest F t • Wave.shiftedQuotientWave N t v) := by
  change Wave.shiftedQuotientWavePacket N _ _ v=_
  rw [Wave.shiftedQuotientWavePacket_apply]
  apply integral_even_eq_two_half
  · exact coshCurve_integrable F hF R hR hs _ (Wave.shiftedQuotientWave_stronglyContinuous N v)
  · intro t
    simp only [coshTimeTest,Real.cosh_neg,Wave.shiftedQuotientWave_neg]

/-- The recovered actual Abel position is the actual quotient cosine wave
of its initial vector, for every nonnegative time. -/
theorem regularizedAbelPosition_eq_wave (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (c : AutomorphicSpace N×AutomorphicSpace N)
    (hcT : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)
    (t : ℝ) (ht : 0≤t) :
    boundedCauchyPosition (regularizedShiftedGenerator N ε) c t=Wave.shiftedQuotientWave N t c.1 := by
  have hc2 := regularizedAbelPosition_zero_velocity N ε hε f c hcT
  apply ext_inner_right ℂ
  have he : (fun a : AutomorphicSpace N => inner ℂ
      (boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) a)=
    (fun a => inner ℂ (Wave.shiftedQuotientWave N t c.1) a) := by
    apply (friedrichsResolvent_denseRange N).equalizer
      (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
    funext z
    have h := regularizedAbelPosition_cauchy_pairing N ε hε f c hcT
      (friedrichsGraph_resolvent N z) t ht
    rw [hc2,neg_zero,inner_zero_left,zero_add,← Wave.shiftedWave_inner] at h
    exact h
  intro a
  exact congrFun he a

/-- The original geometric q-test is the actual spectral packet of the
recovered initial position, with its half-line factor retained. -/
theorem regularizedAbelPosition_packet (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (c : AutomorphicSpace N×AutomorphicSpace N)
    (hcT : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (2:ℂ) • Wave.resolventCutoffOperator (friedrichsResolvent N) ε
      (abelKernelOperator N F hF hc R hR hs f)=coshWavePacket N F hF R hR hs c.1 := by
  rw [regularizedAbelPosition_originalTest N ε f c hcT F hF hc hr R hR hs,
    coshWavePacket_eq_two_half]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change coshTimeTest F t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t=
    coshTimeTest F t • Wave.shiftedQuotientWave N t c.1
  rw [regularizedAbelPosition_eq_wave N ε hε f c hcT t (le_of_lt ht)]

#print axioms integral_even_eq_two_half
#print axioms coshWavePacket_eq_two_half
#print axioms regularizedAbelPosition_eq_wave
#print axioms regularizedAbelPosition_packet

end QuantitativeMaass
