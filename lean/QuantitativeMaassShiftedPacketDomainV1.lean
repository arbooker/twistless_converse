module

public import QuantitativeMaassShiftedWavePacketV1
public import QuantitativeMaassShiftedWaveDomainV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ComplexConjugate

namespace QuantitativeMaass.Wave

theorem shiftedQuotientWavePacket_commute_resolvent (N : ℕ) (φ : ℝ→ℂ) (hφ : ShiftedWaveWeight φ) :
    Commute (shiftedQuotientWavePacket N φ hφ) (friedrichsResolvent N) := by
  apply DFunLike.coe_injective
  funext v
  change shiftedQuotientWavePacket N φ hφ (friedrichsResolvent N v)=
    friedrichsResolvent N (shiftedQuotientWavePacket N φ hφ v)
  simp only [shiftedQuotientWavePacket_apply]
  rw [← (friedrichsResolvent N).integral_comp_comm (shiftedQuotientWave_packet_integrable N hφ v)]
  apply integral_congr_ae
  filter_upwards with t
  rw [map_smul]
  have hc := congrArg (fun A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => A v)
    (shiftedQuotientWave_commute_resolvent N t).eq
  change shiftedQuotientWave N t (friedrichsResolvent N v)=
    friedrichsResolvent N (shiftedQuotientWave N t v) at hc
  rw [hc]

/-- Strong wave packets preserve the actual unbounded operator domain and
commute there with its Friedrichs Laplacian. -/
theorem shiftedQuotientWavePacket_graph (N : ℕ) (φ : ℝ→ℂ) (hφ : ShiftedWaveWeight φ)
    {v w : AutomorphicSpace N} (h : FriedrichsGraph N v w) :
    FriedrichsGraph N (shiftedQuotientWavePacket N φ hφ v) (shiftedQuotientWavePacket N φ hφ w) := by
  change friedrichsResolvent N (shiftedQuotientWavePacket N φ hφ v+
    shiftedQuotientWavePacket N φ hφ w)=shiftedQuotientWavePacket N φ hφ v
  rw [← map_add]
  have hc := congrArg (fun A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => A (v+w))
    (shiftedQuotientWavePacket_commute_resolvent N φ hφ).eq
  change shiftedQuotientWavePacket N φ hφ (friedrichsResolvent N (v+w))=
    friedrichsResolvent N (shiftedQuotientWavePacket N φ hφ (v+w)) at hc
  rw [← hc,h]

/-- Real-valued time weights give genuinely self-adjoint bounded packets. -/
theorem shiftedQuotientWavePacket_isSelfAdjoint (N : ℕ) (φ : ℝ→ℂ) (hφ : ShiftedWaveWeight φ)
    (hr : ∀ t, conj (φ t)=φ t) : IsSelfAdjoint (shiftedQuotientWavePacket N φ hφ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro v w
  change inner ℂ (shiftedQuotientWavePacket N φ hφ v) w=inner ℂ v (shiftedQuotientWavePacket N φ hφ w)
  rw [shiftedQuotientWavePacket_apply,shiftedQuotientWavePacket_apply]
  rw [← inner_conj_symm,← integral_inner (shiftedQuotientWave_packet_integrable N hφ v) w,
    ← integral_conj,← integral_inner (shiftedQuotientWave_packet_integrable N hφ w) v]
  apply integral_congr_ae
  filter_upwards with t
  rw [inner_smul_right w (shiftedQuotientWave N t v) (φ t),
    inner_smul_right v (shiftedQuotientWave N t w) (φ t),map_mul,hr,inner_conj_symm]
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (shiftedQuotientWave_isSelfAdjoint N t) v w
  change inner ℂ (shiftedQuotientWave N t v) w=inner ℂ v (shiftedQuotientWave N t w) at hs
  rw [hs]

#print axioms shiftedQuotientWavePacket_commute_resolvent
#print axioms shiftedQuotientWavePacket_graph
#print axioms shiftedQuotientWavePacket_isSelfAdjoint

end QuantitativeMaass.Wave
