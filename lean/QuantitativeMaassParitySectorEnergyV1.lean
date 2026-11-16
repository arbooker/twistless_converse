module

public import QuantitativeMaassParityTerminalEmbeddingV1
public import QuantitativeMaassOriginalSectorEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set AsymptoticClassicalPetersson AsymptoticSectorSigns
open scoped SchwartzMap ContDiff BigOperators

namespace QuantitativeMaass

def completedNewSignParityNewInclusion (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (η : ℝ) :
    completedNewSignParitySpace N hN χ η→ₗᵢ[ℂ]completedCuspidalNewParitySpace N hN η where
  toLinearMap := Submodule.inclusion (by intro x hx; exact ⟨⟨hx.1.1,hx.1.2.1⟩,hx.2⟩)
  norm_map' _ := rfl

theorem originalParitySectorInclusion_orthogonal (N : ℕ) (hN : 0<N) [NeZero N] (η : ℝ) :
    OrthogonalFamily (E := completedCuspidalNewParitySpace N hN η) ℂ
      (fun e : Sector N => completedNewSignParitySpace N hN (sectorCharacter N hN e) η)
      (fun e => completedNewSignParityNewInclusion N hN (sectorCharacter N hN e) η) := by
  intro e d hne x y
  exact completedNewSignSpace_orthogonal N hN _ _ ((sectorCharacter_injective N hN).ne hne)
    (completedNewSignParityInclusion N hN _ η x) (completedNewSignParityInclusion N hN _ η y)

theorem completedCuspidalNewParityTimePacket_summable {ι : Type*} (N : ℕ) (hN : 0<N) [NeZero N]
    (η : ℝ) (b : HilbertBasis ι ℂ (completedCuspidalNewParitySpace N hN η))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    Summable (fun i => ‖completedCuspidalNewParityTimePacket N hN η f hc he hr R hR hs (b i)‖^2) := by
  obtain ⟨w,c,_⟩ := exists_hilbertBasis ℂ (completedCuspidalNewSpace N hN)
  have hv : Orthonormal ℂ (fun i => completedCuspidalNewParityInclusion N hN η (b i)) :=
    ⟨fun i => b.orthonormal.norm_eq_one i,fun _ _ hij => b.orthonormal.inner_eq_zero hij⟩
  exact (orthonormal_energy_le c (fun i => completedCuspidalNewParityInclusion N hN η (b i)) hv
    (completedCuspidalNewTimePacket N hN f (f.smooth ⊤) hc)
    (completedCuspidalNewTimePacket_summable N hN c f (f.smooth ⊤) hc)).1

/-- The original finite sign sectors contribute with coefficient one to
the actual fixed-parity cuspidal newspace energy. -/
theorem original_parity_sector_energy_le {ι : Type*} (N : ℕ) (hN : 0<N) [NeZero N] (η : ℝ)
    (b : HilbertBasis ι ℂ (completedCuspidalNewParitySpace N hN η)) (κ : Sector N→Type*)
    (c : ∀ e,HilbertBasis (κ e) ℂ (completedNewSignParitySpace N hN (sectorCharacter N hN e) η))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    (∑ e : Sector N,hilbertSchmidtEnergy (c e)
      (completedNewSignParityTimePacket N hN (sectorCharacter N hN e) η f hc he hr R hR hs))≤
      hilbertSchmidtEnergy b (completedCuspidalNewParityTimePacket N hN η f hc he hr R hR hs) := by
  have hh := orthogonal_sector_energy_le (H := completedCuspidalNewParitySpace N hN η)
    (fun e : Sector N => completedNewSignParityNewInclusion N hN (sectorCharacter N hN e) η)
    (originalParitySectorInclusion_orthogonal N hN η) b c
    (completedCuspidalNewParityTimePacket N hN η f hc he hr R hR hs)
    (fun e => completedNewSignParityTimePacket N hN (sectorCharacter N hN e) η f hc he hr R hR hs)
    (fun _ _ => rfl) (completedCuspidalNewParityTimePacket_summable N hN η b f hc he hr R hR hs)
  simpa only [tsum_fintype] using hh.2.2

#print axioms originalParitySectorInclusion_orthogonal
#print axioms completedCuspidalNewParityTimePacket_summable
#print axioms original_parity_sector_energy_le

end QuantitativeMaass
