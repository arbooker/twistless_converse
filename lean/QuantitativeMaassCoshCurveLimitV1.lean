module

public import QuantitativeMaassBoundaryWaveLimitV1
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem coshTimeTest_compact (F : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) : HasCompactSupport (coshTimeTest F) :=
  (isCompact_Icc : IsCompact (Icc (-R) R)).of_isClosed_subset isClosed_closure
    (closure_minimal (coshTimeTest_support F R hR hs) isClosed_Icc)

theorem abelBoundaryPart_tendsto_zero_above_one {ι : Type*} (l : Filter ι)
    (F : ℝ → ℂ) (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0))
    (q : ℝ) (hq : 1<q) : Tendsto (fun i => abelBoundaryPart F (a i) q) l (𝓝 0) := by
  have he : ∀ᶠ i in l,a i<(q-1)/2 := ha0.eventually (Iio_mem_nhds (by linarith))
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with i hi
  have hz : abelBoundaryPart F (a i) q=0 := by
    by_contra hn
    have h := abelBoundaryPart_support F (a i) (ha i) hn
    change q≤1+2*a i at h
    linarith
  exact hz.symm

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem coshCurve_integrable (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (u : ℝ → H) (hu : Continuous u) : Integrable (fun t => coshTimeTest F t • u t) :=
  ((hF.comp Real.contDiff_cosh).continuous.smul hu).integrable_of_hasCompactSupport
    (coshTimeTest_compact F R hR hs).smul_right

/-- The discarded endpoint contribution tends to zero against ANY
continuous vector curve. The bound is the original compact test times the
curve; no derivative estimates or spectral representation are assumed. -/
theorem coshBoundaryCurve_tendsto_zero {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (u : ℝ → H) (hu : Continuous u)
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => ∫ t in Ioi (0:ℝ),coshTimeTest (abelBoundaryPart F (a i)) t • u t) l (𝓝 0) := by
  have hi := (coshCurve_integrable F hF R hR hs u hu).norm.integrableOn (s:=Ioi (0:ℝ))
  have hlim : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      Tendsto (fun i => coshTimeTest (abelBoundaryPart F (a i)) t • u t) l (𝓝 (0:H)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h := (abelBoundaryPart_tendsto_zero_above_one l F a ha ha0 (Real.cosh t)
      (Real.one_lt_cosh.mpr (ne_of_gt ht))).smul (tendsto_const_nhds (x:=u t))
    simpa only [coshTimeTest,zero_smul] using h
  have hb (i : ι) : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      ‖coshTimeTest (abelBoundaryPart F (a i)) t • u t‖≤‖coshTimeTest F t • u t‖ := by
    filter_upwards with t
    simp only [coshTimeTest,abelBoundaryPart,norm_smul,norm_mul]
    have hc : ‖abelBoundaryCutoff (a i) (Real.cosh t)‖≤1 :=
      abelCutoff_norm_le_one (a i) (Real.cosh t-a i)
    calc
      _ ≤ (‖F (Real.cosh t)‖*1)*‖u t‖ := by gcongr
      _ = _ := by ring
  have hm (i : ι) : AEStronglyMeasurable
      (fun t => coshTimeTest (abelBoundaryPart F (a i)) t • u t)
      (volume.restrict (Ioi (0:ℝ))) :=
    (((abelBoundaryPart_smooth F hF (a i)).comp Real.contDiff_cosh).continuous.smul hu).aestronglyMeasurable
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖coshTimeTest F t • u t‖) (Eventually.of_forall hm) (Eventually.of_forall hb) hi hlim
  simpa only [integral_zero] using h

/-- Removing the endpoint hole recovers the full original q-test integral
on positive time. -/
theorem coshPuncturedCurve_tendsto {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (u : ℝ → H) (hu : Continuous u)
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => ∫ t in Ioi (0:ℝ),
      coshTimeTest (fun q => F q-abelBoundaryPart F (a i) q) t • u t) l
      (𝓝 (∫ t in Ioi (0:ℝ),coshTimeTest F t • u t)) := by
  have h := (tendsto_const_nhds (x:=∫ t in Ioi (0:ℝ),coshTimeTest F t • u t)).sub (coshBoundaryCurve_tendsto_zero l F hF R hR hs u hu a ha ha0)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards with i
  simp only [coshTimeTest,sub_smul]
  exact (integral_sub (coshCurve_integrable F hF R hR hs u hu).integrableOn
    (coshCurve_integrable (abelBoundaryPart F (a i)) (abelBoundaryPart_smooth F hF (a i)) R hR
      (abelBoundaryPart_support_source F (a i) _ hs) u hu).integrableOn).symm

#print axioms abelBoundaryPart_tendsto_zero_above_one
#print axioms coshBoundaryCurve_tendsto_zero
#print axioms coshPuncturedCurve_tendsto

end QuantitativeMaass
