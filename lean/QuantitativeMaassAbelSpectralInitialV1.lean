module

public import QuantitativeMaassAbelNormalizedTimeMassV1
public import QuantitativeMaassWavePacketInitialV1
public import QuantitativeMaassCoshWavePacketV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- The actual spectral packets of the same normalized Abel tests converge
strongly to identity. Their mass and absolute-mass hypotheses are proved,
not assumed, from the explicit smooth cutoff. -/
theorem abelNormalizedWavePacket_tendsto {ι : Type*} (l : Filter ι) (N : ℕ)
    (R : ι → ℝ) (hR : ∀ i,0<R i) (hlim : Tendsto R l (𝓝 0))
    (v : AutomorphicSpace N) :
    Tendsto (fun i => coshWavePacket N (abelNormalizedTest (R i))
      (abelNormalizedTest_smooth (R i)) (R i) (hR i).le
      (abelNormalizedTest_support (R i) (hR i)) v) l (𝓝 v) := by
  exact Wave.shiftedQuotientWavePacket_initial l N
    (fun i => coshTimeTest (abelNormalizedTest (R i)))
    (fun i => coshTimeTest_waveWeight _ (abelNormalizedTest_smooth (R i))
      (R i) (hR i).le (abelNormalizedTest_support (R i) (hR i)))
    (fun i => coshWeightedTest_integrable _ (abelNormalizedTest_smooth (R i))
      (R i) (hR i).le (abelNormalizedTest_support (R i) (hR i)))
    (fun i => abelNormalizedTest_time_mass (R i) (hR i))
    (fun i => (abelNormalizedTest_time_norm_mass (R i) (hR i)).le)
    R (fun i => coshTimeTest_support _ (R i) (hR i).le
      (abelNormalizedTest_support (R i) (hR i))) hlim v

#print axioms abelNormalizedWavePacket_tendsto

end QuantitativeMaass
