module

public import QuantitativeMaassCanonicalSectorEnergyV1
public import QuantitativeMaassSectorCharacterChoiceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set AsymptoticClassicalPetersson AsymptoticSectorSigns
open scoped ContDiff BigOperators

namespace QuantitativeMaass

theorem originalSectorInclusion_orthogonal (N : ℕ) (hN : 0<N) [NeZero N] :
    OrthogonalFamily (E := completedCuspidalNewSpace N hN) ℂ
      (fun e : Sector N => completedNewSignSpace N hN (sectorCharacter N hN e))
      (fun e => completedNewSignInclusion N hN (sectorCharacter N hN e)) := by
  intro e d hne x y
  exact completedNewSignSpace_orthogonal N hN _ _ ((sectorCharacter_injective N hN).ne hne) x y

/-- The coefficient-one canonical energy bound for the original finite
Euler sectors, including empty canonical spaces. -/
theorem original_sector_energy_le {ι : Type*} (N : ℕ) (hN : 0<N) [NeZero N]
    (b : HilbertBasis ι ℂ (completedCuspidalNewSpace N hN)) (κ : Sector N→Type*)
    (c : ∀ e,HilbertBasis (κ e) ℂ (completedNewSignSpace N hN (sectorCharacter N hN e)))
    (f : ℝ→ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    (∑ e : Sector N,hilbertSchmidtEnergy (c e)
      (completedNewSignTimePacket N hN (sectorCharacter N hN e) f hf he hc hr R hR hs))≤
      hilbertSchmidtEnergy b (completedCuspidalNewTimePacket N hN f hf hc) := by
  have hh := orthogonal_sector_energy_le (H := completedCuspidalNewSpace N hN)
    (fun e : Sector N => completedNewSignInclusion N hN (sectorCharacter N hN e))
    (originalSectorInclusion_orthogonal N hN) b c
    (completedCuspidalNewTimePacket N hN f hf hc)
    (fun e => completedNewSignTimePacket N hN (sectorCharacter N hN e) f hf he hc hr R hR hs)
    (fun _ _ => rfl) (completedCuspidalNewTimePacket_summable N hN b f hf hc)
  simpa only [tsum_fintype] using hh.2.2

#print axioms originalSectorInclusion_orthogonal
#print axioms original_sector_energy_le

end QuantitativeMaass
