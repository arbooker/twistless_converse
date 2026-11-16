module

public import QuantitativeMaassShiftedWaveCommuteV1
public import QuantitativeMaassShiftedWavePacketV1
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory

namespace QuantitativeMaass

/-- A closed subspace invariant under a self-adjoint operator has a
commuting orthogonal projection. -/
theorem invariantSpace_projection_commute {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) [CompleteSpace W]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hW : ∀ x∈W,T x∈W) :
    Commute W.starProjection T := by
  let P := W.starProjection
  have hp : IsSelfAdjoint P := isSelfAdjoint_starProjection W
  have hi : P*T*P=T*P := by
    apply ContinuousLinearMap.ext
    intro x
    exact Submodule.starProjection_eq_self_iff.mpr (hW (P x) (W.starProjection_apply_mem x))
  have hj := congrArg star hi
  simp only [star_mul,hp.star_eq,hT.star_eq] at hj
  change P*T=T*P
  exact hj.symm.trans ((mul_assoc P T P).symm.trans hi)

/-- Resolvent invariance suffices for invariance under the genuine wave
packet; no spectral basis or density in an eigenspace is assumed. -/
theorem resolventInvariantSpace_timePacket (N : ℕ) (W : Submodule ℂ (AutomorphicSpace N))
    [CompleteSpace W] (hW : ∀ x∈W,friedrichsResolvent N x∈W)
    (f : ℝ → ℂ) (hf : Wave.ShiftedWaveWeight f)
    (x : AutomorphicSpace N) (hx : x∈W) :
    Wave.shiftedQuotientWavePacket N f hf x∈W := by
  have hp := invariantSpace_projection_commute W (friedrichsResolvent N)
    (friedrichsResolvent_isSelfAdjoint N) hW
  have hc (t : ℝ) (y : AutomorphicSpace N) :
      W.starProjection (Wave.shiftedQuotientWave N t y)=
        Wave.shiftedQuotientWave N t (W.starProjection y) :=
    DFunLike.congr_fun (Wave.shiftedQuotientWave_commute_of_resolvent N W.starProjection hp t) y
  apply Submodule.starProjection_eq_self_iff.mp
  change W.starProjection (∫ t,f t • Wave.shiftedQuotientWave N t x)=
    ∫ t,f t • Wave.shiftedQuotientWave N t x
  rw [←W.starProjection.integral_comp_comm (Wave.shiftedQuotientWave_packet_integrable N hf x)]
  apply integral_congr_ae
  filter_upwards with t
  rw [map_smul,hc,Submodule.starProjection_eq_self_iff.mpr hx]

#print axioms invariantSpace_projection_commute
#print axioms resolventInvariantSpace_timePacket

end QuantitativeMaass
