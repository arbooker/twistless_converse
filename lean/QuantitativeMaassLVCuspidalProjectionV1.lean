module

public import QuantitativeMaassLVCuspHeightV1
public import QuantitativeMaassCuspWaveAverageV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology MatrixGroups InnerProductSpace

namespace QuantitativeMaass

instance localCuspidalSpace_complete (N : ℕ) (hN : 0<N) :
    CompleteSpace (localCuspidalSpace N hN) :=
  (localCuspidalSpace_closed N hN).completeSpace_coe

/-- The orthogonal projection onto the actual closed all-cusp kernel. -/
def localCuspidalProjection (N : ℕ) (hN : 0<N) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  (localCuspidalSpace N hN).starProjection

theorem localCuspidalProjection_selfAdjoint (N : ℕ) (hN : 0<N) :
    IsSelfAdjoint (localCuspidalProjection N hN) :=
  isSelfAdjoint_starProjection _

theorem localCuspidalProjection_idempotent (N : ℕ) (hN : 0<N) :
    localCuspidalProjection N hN * localCuspidalProjection N hN =
      localCuspidalProjection N hN :=
  (localCuspidalSpace N hN).isIdempotentElem_starProjection

theorem localCuspidalProjection_actualLVFilter (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ) :
    localCuspidalProjection N hN * actualLVFilter N p hN hpN a b hab d =
      actualLVFilter N p hN hpN a b hab d := by
  apply ContinuousLinearMap.ext
  intro f
  exact (Submodule.starProjection_eq_self_iff).mpr
    (actualLVFilter_mem_localCuspidalSpace N p hN hpN hNp hpres a b hab d f)

/-- Self-adjointness upgrades range containment to support on the cuspidal
space on both sides of the operator. -/
theorem actualLVFilter_localCuspidalProjection (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ) :
    actualLVFilter N p hN hpN a b hab d * localCuspidalProjection N hN =
      actualLVFilter N p hN hpN a b hab d := by
  have h := congrArg ContinuousLinearMap.adjoint
    (localCuspidalProjection_actualLVFilter N p hN hpN hNp hpres a b hab d)
  have hQ : IsSelfAdjoint (actualLVFilter N p hN hpN a b hab d) :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (actualLVFilter_order N p hN hpN a b hab d).1).isSelfAdjoint
  change ((localCuspidalProjection N hN).comp
    (actualLVFilter N p hN hpN a b hab d)).adjoint =
      (actualLVFilter N p hN hpN a b hab d).adjoint at h
  simp only [ContinuousLinearMap.adjoint_comp,hQ.adjoint_eq,
    (localCuspidalProjection_selfAdjoint N hN).adjoint_eq] at h
  apply ContinuousLinearMap.ext
  intro f
  exact congrArg (fun T : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => T f) h

/-- The literal LV polynomial is dominated by the genuine cuspidal
projection, not only by the identity. This is the operator inequality
needed when its smoothed trace is used as a cuspidal lower bound. -/
theorem actualLVFilter_le_localCuspidalProjection (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ) :
    actualLVFilter N p hN hpN a b hab d ≤ localCuspidalProjection N hN := by
  have h := star_left_conjugate_le_conjugate
    (actualLVFilter_order N p hN hpN a b hab d).2.1 (localCuspidalProjection N hN)
  simpa only [(localCuspidalProjection_selfAdjoint N hN).star_eq,
    localCuspidalProjection_actualLVFilter N p hN hpN hNp hpres a b hab d,
    actualLVFilter_localCuspidalProjection N p hN hpN hNp hpres a b hab d,
    mul_one,localCuspidalProjection_idempotent] using h

/-- Every admissibly integrable shifted wave packet preserves the actual
closed cuspidal space; exceptional spectrum is included in the weight. -/
theorem shiftedQuotientWavePacket_mem_localCuspidalSpace (N : ℕ) (hN : 0<N)
    (φ : ℝ → ℂ) (hφ : Wave.ShiftedWaveWeight φ)
    (f : AutomorphicSpace N) (hf : f∈localCuspidalSpace N hN) :
    Wave.shiftedQuotientWavePacket N φ hφ f∈localCuspidalSpace N hN := by
  rw [mem_localCuspidalSpace]
  intro s A B
  change cuspLogConstantComplex N hN s A B (Wave.shiftedQuotientWavePacket N φ hφ f)=0
  rw [Wave.shiftedQuotientWavePacket_apply,
    ← (cuspLogConstantComplex N hN s A B).integral_comp_comm
      (Wave.shiftedQuotientWave_packet_integrable N hφ f)]
  have hz (t : ℝ) : cuspLogConstantComplex N hN s A B (Wave.shiftedQuotientWave N t f)=0 :=
    (mem_localCuspidalSpace N hN _).mp
      (shiftedQuotientWave_mem_localCuspidalSpace N hN f hf t) s A B
  simp only [map_smul,hz,smul_zero,integral_zero]

#print axioms actualLVFilter_localCuspidalProjection
#print axioms actualLVFilter_le_localCuspidalProjection
#print axioms shiftedQuotientWavePacket_mem_localCuspidalSpace

end QuantitativeMaass
