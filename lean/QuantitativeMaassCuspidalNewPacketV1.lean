module

public import QuantitativeMaassCompletedNewSignPacketV1
public import QuantitativeMaassOrthogonalSectorEnergyV1
public import QuantitativeArithmeticMaassCuspidalEigenbasisV1
public import QuantitativeMaassSmoothPacketTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set AsymptoticClassicalPetersson QuantitativeNinaMaass
open scoped ContDiff

namespace QuantitativeMaass

def completedCuspidalTimePacket (N : ℕ) (hN : 0<N)
    (f : ℝ→ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    localCuspidalSpace N hN→L[ℂ]localCuspidalSpace N hN :=
  ((Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc)).comp
    (localCuspidalSpace N hN).subtypeL).codRestrict (localCuspidalSpace N hN)
    (fun x => shiftedQuotientWavePacket_mem_localCuspidalSpace N hN f (compactSmoothWaveWeight f hf hc) x.val x.property)

theorem completedCuspidalTimePacket_summable {ι : Type*} (N : ℕ) (hN : 0<N)
    (b : HilbertBasis ι ℂ (localCuspidalSpace N hN))
    (f : ℝ→ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Summable (fun i => ‖completedCuspidalTimePacket N hN f hf hc (b i)‖^2) := by
  obtain ⟨κ,c,e,he,hgraph,_⟩ := QuantitativeArithmeticMaassCuspBand.exists_cuspidal_energy_basis N hN
  have hsum : Summable (fun j => ‖completedCuspidalTimePacket N hN f hf hc (c j)‖^2) :=
    cuspidal_smooth_packet_square_summable N hN (fun j => (c j:AutomorphicSpace N))
      (c.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ)
      (fun j => (c j).property) e he hgraph f hf hc
  exact (energy_change_basis_le c b (completedCuspidalTimePacket N hN f hf hc) hsum).1

def completedCuspidalNewSpace (N : ℕ) (hN : 0<N) [NeZero N] : Submodule ℂ (AutomorphicSpace N) :=
  localCuspidalSpace N hN ⊓ newSpace N hN

instance completedCuspidalNewSpace_complete (N : ℕ) (hN : 0<N) [NeZero N] :
    CompleteSpace (completedCuspidalNewSpace N hN) :=
  ((localCuspidalSpace_closed N hN).inter (actualNewSpace_closed N hN)).completeSpace_coe

def completedCuspidalNewInclusion (N : ℕ) (hN : 0<N) [NeZero N] :
    completedCuspidalNewSpace N hN→ₗᵢ[ℂ]localCuspidalSpace N hN where
  toLinearMap := Submodule.inclusion (show completedCuspidalNewSpace N hN≤localCuspidalSpace N hN from inf_le_left)
  norm_map' _ := rfl

def completedCuspidalNewTimePacket (N : ℕ) (hN : 0<N) [NeZero N]
    (f : ℝ→ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    completedCuspidalNewSpace N hN→L[ℂ]completedCuspidalNewSpace N hN :=
  ((Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc)).comp
    (completedCuspidalNewSpace N hN).subtypeL).codRestrict (completedCuspidalNewSpace N hN)
    (fun x => ⟨shiftedQuotientWavePacket_mem_localCuspidalSpace N hN f (compactSmoothWaveWeight f hf hc) x.val x.property.1,
      actualNewSpace_timePacket N hN f (compactSmoothWaveWeight f hf hc) x.val x.property.2⟩)

theorem completedCuspidalNewTimePacket_summable {ι : Type*} (N : ℕ) (hN : 0<N) [NeZero N]
    (b : HilbertBasis ι ℂ (completedCuspidalNewSpace N hN))
    (f : ℝ→ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Summable (fun i => ‖completedCuspidalNewTimePacket N hN f hf hc (b i)‖^2) := by
  obtain ⟨κ,c,_⟩ := QuantitativeArithmeticMaassCuspBand.exists_cuspidal_energy_basis N hN
  have hv : Orthonormal ℂ (fun i => completedCuspidalNewInclusion N hN (b i)) :=
    ⟨fun i => b.orthonormal.norm_eq_one i,fun _ _ hij => b.orthonormal.inner_eq_zero hij⟩
  have hsum := (orthonormal_energy_le c (fun i => completedCuspidalNewInclusion N hN (b i)) hv
    (completedCuspidalTimePacket N hN f hf hc)
    (completedCuspidalTimePacket_summable N hN c f hf hc)).1
  exact hsum

#print axioms completedCuspidalTimePacket_summable
#print axioms completedCuspidalNewTimePacket_summable

end QuantitativeMaass
