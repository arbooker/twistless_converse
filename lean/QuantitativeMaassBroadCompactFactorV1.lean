module

public import QuantitativeMaassCompactFactorEnergyV1
public import QuantitativeMaassBroadCarrierV1
public import QuantitativeMaassRawColumnBesselV1
public import QuantitativeMaassCylinderBranchTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap

namespace QuantitativeMaass

def broadAbelColumn (N : ℕ) [NeZero N] (L : ℝ) (hL : 0 < L) (t : ℝ) :
    ℍ → AutomorphicSpace N :=
  timeAbelColumn N (broadTimeSchwartz L hL t) (broadTimeWeight_compact L hL t)
    (broadTimeWeight_even L t) (1/L) (by positivity) (broadTimeWeight_support L hL t)

theorem broadAbelColumn_continuous (N : ℕ) [NeZero N]
    (L : ℝ) (hL : 0 < L) (t : ℝ) : Continuous (broadAbelColumn N L hL t) :=
  oneSidedAbelColumn_continuous N _
    (evenCoshLift_smoothOn _ ((broadTimeSchwartz L hL t).smooth ⊤)
      (broadTimeWeight_even L t) (broadTimeWeight_compact L hL t))
    (1/L) (by positivity)
    (evenCoshLift_support_of_time_support _ (1/L) (by positivity) (broadTimeWeight_support L hL t))

theorem broadAbelColumn_invariant (N : ℕ) [NeZero N]
    (L : ℝ) (hL : 0 < L) (t : ℝ) (γ : gamma N) (z : ℍ) :
    broadAbelColumn N L hL t (γ • z) = broadAbelColumn N L hL t z :=
  oneSidedAbelColumn_invariant N _
    (evenCoshLift_smoothOn _ ((broadTimeSchwartz L hL t).smooth ⊤)
      (broadTimeWeight_even L t) (broadTimeWeight_compact L hL t))
    (1/L) (by positivity)
    (evenCoshLift_support_of_time_support _ (1/L) (by positivity) (broadTimeWeight_support L hL t)) γ z

theorem broadAbelColumn_packet_coeFn (N : ℕ) [NeZero N]
    (L : ℝ) (hL : 0 < L) (t : ℝ) (v : AutomorphicSpace N) :
    (broadQuotientPacket N L hL t v).val =ᵐ[quotientMeasure N]
      (fun z => inner ℂ (broadAbelColumn N L hL t z) v) :=
  timeAbelColumn_packet_coeFn N (broadTimeSchwartz L hL t)
    (broadTimeWeight_compact L hL t) (broadTimeWeight_even L t)
    (broadTimeWeight_real L t) (1/L) (by positivity) (broadTimeWeight_support L hL t) v

/-- Restriction of the actual packet followed by a self-adjoint operator
is exactly the finite-energy operator of its compact column family. -/
theorem broadCompact_column_operator (N : ℕ) [NeZero N]
    (L : ℝ) (hL : 0 < L) (t : ℝ) (K : Set ℍ) (hK : IsCompact K)
    (D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (hD : IsSelfAdjoint D) :
    finiteEnergyColumnOperator (volume.restrict K)
      (fun z => D (broadAbelColumn N L hL t z))
      (compact_column_memLp _ (D.continuous.comp (broadAbelColumn_continuous N L hL t)) K hK) =
      (quotientRestriction N K hK hK.measurableSet).comp
        ((broadQuotientPacket N L hL t).comp D) := by
  apply finiteEnergyColumnOperator_eq_of_kernel
  intro v
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hD
  have he := continuous_invariant_raw_restriction N K hK
    (broadQuotientPacket N L hL t (D v))
    (fun z => inner ℂ (broadAbelColumn N L hL t z) (D v))
    ((broadAbelColumn_continuous N L hL t).inner continuous_const)
    (fun γ z => by rw [broadAbelColumn_invariant])
    (broadAbelColumn_packet_coeFn N L hL t (D v))
  filter_upwards [he] with z hz
  change (quotientRestriction N K hK hK.measurableSet
    (broadQuotientPacket N L hL t (D v))) z = _
  rw [hz]
  exact (hs (broadAbelColumn N L hL t z) v).symm

/-- The adjoint is the literal compact-input transfer D Q R*, with no
commutation of a spatial cutoff with the quotient wave. -/
theorem broadCompact_column_operator_adjoint (N : ℕ) [NeZero N]
    (L : ℝ) (hL : 0 < L) (t : ℝ) (K : Set ℍ) (hK : IsCompact K)
    (D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (hD : IsSelfAdjoint D) :
    (finiteEnergyColumnOperator (volume.restrict K)
      (fun z => D (broadAbelColumn N L hL t z))
      (compact_column_memLp _ (D.continuous.comp (broadAbelColumn_continuous N L hL t)) K hK)).adjoint =
      D.comp ((broadQuotientPacket N L hL t).comp
        (quotientRestriction N K hK hK.measurableSet).adjoint) := by
  rw [broadCompact_column_operator N L hL t K hK D hD, adjoint_comp, adjoint_comp]
  have hQ : IsSelfAdjoint (broadQuotientPacket N L hL t) :=
    Wave.shiftedQuotientWavePacket_isSelfAdjoint N _ _ (broadTimeWeight_real L t)
  rw [hD.adjoint_eq, hQ.adjoint_eq]
  rfl

#print axioms broadAbelColumn_packet_coeFn
#print axioms broadCompact_column_operator
#print axioms broadCompact_column_operator_adjoint

end QuantitativeMaass
