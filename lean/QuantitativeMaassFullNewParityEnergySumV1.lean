module

public import QuantitativeMaassCanonicalProjectionSumV1
public import QuantitativeMaassParitySectorEnergyV1
public import QuantitativeMaassIsometricPacketSummabilityV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set ContinuousLinearMap AsymptoticClassicalPetersson QuantitativeNinaMaass
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass
local instance (N : ℕ) [NeZero N] (hN : 0<N) :
    NormedAddCommGroup (completedCuspidalNewSpace N hN) := inferInstance
local instance (N : ℕ) [NeZero N] (hN : 0<N) :
    InnerProductSpace ℂ (completedCuspidalNewSpace N hN) := inferInstance
local instance (N : ℕ) [NeZero N] (hN : 0<N) (η : ℝ) :
    NormedAddCommGroup (completedCuspidalNewParitySpace N hN η) := inferInstance
local instance (N : ℕ) [NeZero N] (hN : 0<N) (η : ℝ) :
    InnerProductSpace ℂ (completedCuspidalNewParitySpace N hN η) := inferInstance

/-- Both actual parity projections preserve the full cuspidal newspace. -/
theorem completedCuspidalNew_parity (N : ℕ) [NeZero N] (hN : 0<N) (η : ℝ)
    (x : AutomorphicSpace N) (hx : x∈completedCuspidalNewSpace N hN) :
    parityProjection N η x∈completedCuspidalNewSpace N hN := by
  have hr : reflectionIsometry N x∈completedCuspidalNewSpace N hN :=
    ⟨reflectionIsometry_mem_localCuspidalSpace N hN x hx.1,newSpace_reflection N hN x hx.2⟩
  rw [parityProjection_apply]
  exact (completedCuspidalNewSpace N hN).smul_mem _
    ((completedCuspidalNewSpace N hN).add_mem hx ((completedCuspidalNewSpace N hN).smul_mem _ hr))

/-- Orthogonal parity ranges exhaust the actual completed cuspidal newspace. -/
theorem completedCuspidalNew_parity_range_sum (N : ℕ) [NeZero N] (hN : 0<N)
    (η : ℝ) (hη : η^2=1) :
    let Jp := completedCuspidalNewParityInclusion N hN η
    let Jm := completedCuspidalNewParityInclusion N hN (-η)
    haveI : CompleteSpace Jp.toContinuousLinearMap.range :=
      Jp.isometry.isClosedEmbedding.isClosed_range.completeSpace_coe
    haveI : CompleteSpace Jm.toContinuousLinearMap.range :=
      Jm.isometry.isClosedEmbedding.isClosed_range.completeSpace_coe
    (1 : completedCuspidalNewSpace N hN→L[ℂ]completedCuspidalNewSpace N hN)=
      Jp.toContinuousLinearMap.range.starProjection+Jm.toContinuousLinearMap.range.starProjection := by
  intro Jp Jm
  let : CompleteSpace Jp.toContinuousLinearMap.range :=
    Jp.isometry.isClosedEmbedding.isClosed_range.completeSpace_coe
  let : CompleteSpace Jm.toContinuousLinearMap.range :=
    Jm.isometry.isClosedEmbedding.isClosed_range.completeSpace_coe
  let : CompleteSpace (⊤ : Submodule ℂ (completedCuspidalNewSpace N hN)) :=
    isClosed_univ.completeSpace_coe
  have hh := projection_add_of_orthogonal_decomposition
    (⊤ : Submodule ℂ (completedCuspidalNewSpace N hN))
    Jp.toContinuousLinearMap.range Jm.toContinuousLinearMap.range le_top le_top ?_ ?_
  · simpa only [Submodule.starProjection_top'] using hh
  · rintro x ⟨u,rfl⟩ y ⟨v,rfl⟩
    have hu := (mem_completedParitySpace N η u.val).mp u.property.2
    have hv := (mem_completedParitySpace N (-η) v.val).mp v.property.2
    have hv0 : parityProjection N η v.val=0 := by
      have hh := parityProjection_add_neg N η v.val
      rw [hv] at hh
      exact add_right_cancel (hh.trans (zero_add v.val).symm)
    have hh := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (parityProjection_selfAdjoint N η)) u.val v.val
    change inner ℂ (parityProjection N η u.val) v.val=inner ℂ u.val (parityProjection N η v.val) at hh
    change inner ℂ u.val v.val = 0
    simpa only [hu,hv0,inner_zero_right] using hh
  · intro x _
    let up : completedCuspidalNewParitySpace N hN η :=
      ⟨parityProjection N η x.val,completedCuspidalNew_parity N hN η x.val x.property,
        (mem_completedParitySpace N η _).mpr (parityProjection_idempotent N η hη x.val)⟩
    let um : completedCuspidalNewParitySpace N hN (-η) :=
      ⟨parityProjection N (-η) x.val,completedCuspidalNew_parity N hN (-η) x.val x.property,
        (mem_completedParitySpace N (-η) _).mpr
          (parityProjection_idempotent N (-η) (by simpa only [neg_sq] using hη) x.val)⟩
    refine ⟨Jp up,⟨up,rfl⟩,Jm um,⟨um,rfl⟩,?_⟩
    apply Subtype.ext
    exact (parityProjection_add_neg N η x.val).symm

/-- The full newspace packet energy is exactly the sum of its two parity
energies. All sums are finite-energy Hilbert sums for the actual operators. -/
theorem completedCuspidalNewTimePacket_parity_energy_sum {ι κ ρ : Type*}
    (N : ℕ) [NeZero N] (hN : 0<N) (η : ℝ) (hη : η^2=1)
    (b : HilbertBasis ι ℂ (completedCuspidalNewSpace N hN))
    (bp : HilbertBasis κ ℂ (completedCuspidalNewParitySpace N hN η))
    (bm : HilbertBasis ρ ℂ (completedCuspidalNewParitySpace N hN (-η)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    hilbertSchmidtEnergy b (completedCuspidalNewTimePacket N hN f (f.smooth ⊤) hc)=
      hilbertSchmidtEnergy bp (completedCuspidalNewParityTimePacket N hN η f hc he hr R hR hs)+
      hilbertSchmidtEnergy bm (completedCuspidalNewParityTimePacket N hN (-η) f hc he hr R hR hs) := by
  let Jp := completedCuspidalNewParityInclusion N hN η
  let Jm := completedCuspidalNewParityInclusion N hN (-η)
  let : CompleteSpace Jp.toContinuousLinearMap.range :=
    Jp.isometry.isClosedEmbedding.isClosed_range.completeSpace_coe
  let : CompleteSpace Jm.toContinuousLinearMap.range :=
    Jm.isometry.isClosedEmbedding.isClosed_range.completeSpace_coe
  let B := completedCuspidalNewTimePacket N hN f (f.smooth ⊤) hc
  have hsum : (1 : completedCuspidalNewSpace N hN→L[ℂ]completedCuspidalNewSpace N hN)=
      Jp.toContinuousLinearMap.range.starProjection+Jm.toContinuousLinearMap.range.starProjection :=
    completedCuspidalNew_parity_range_sum N hN η hη
  have horth : Jp.toContinuousLinearMap.rangeᗮ.starProjection=Jm.toContinuousLinearMap.range.starProjection := by
    rw [Submodule.starProjection_orthogonal',hsum,add_sub_cancel_left]
  rw [source_projection_energy_split b Jp.toContinuousLinearMap.range B
    (completedCuspidalNewTimePacket_summable N hN b f (f.smooth ⊤) hc),horth]
  rw [isometric_target_energy b bp Jp B (completedCuspidalNewParityTimePacket N hN η f hc he hr R hR hs)
    (fun _ => rfl) (completedCuspidalNewParityTimePacket_summable N hN η bp f hc he hr R hR hs)]
  rw [isometric_target_energy b bm Jm B (completedCuspidalNewParityTimePacket N hN (-η) f hc he hr R hR hs)
    (fun _ => rfl) (completedCuspidalNewParityTimePacket_summable N hN (-η) bm f hc he hr R hR hs)]

#print axioms completedCuspidalNew_parity
#print axioms completedCuspidalNew_parity_range_sum
#print axioms completedCuspidalNewTimePacket_parity_energy_sum
end QuantitativeMaass
