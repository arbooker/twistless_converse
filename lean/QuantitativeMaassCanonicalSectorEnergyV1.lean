module

public import QuantitativeMaassCuspidalNewPacketV1
public import QuantitativeMaassRealizedCharacterSectorsV1
public import QuantitativeMaassGeneratorSectorOrthogonalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set AsymptoticClassicalPetersson
open scoped ContDiff

namespace QuantitativeMaass

def completedNewSignInclusion (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) :
    completedNewSignSpace N hN χ→ₗᵢ[ℂ]completedCuspidalNewSpace N hN where
  toLinearMap := Submodule.inclusion (by intro x hx; exact ⟨hx.1,hx.2.1⟩)
  norm_map' _ := rfl

theorem completedNewSignInclusion_orthogonal (N : ℕ) (hN : 0<N) [NeZero N] :
    OrthogonalFamily (E := completedCuspidalNewSpace N hN) ℂ (fun χ : realizedNewCharacter N hN => completedNewSignSpace N hN χ.val)
      (fun χ => completedNewSignInclusion N hN χ.val) := by
  intro χ ψ hne x y
  have hv : χ.val≠ψ.val := fun h => hne (Subtype.ext h)
  exact completedNewSignSpace_orthogonal N hN χ.val ψ.val hv x y

/-- All realized canonical sectors together contribute at most the
actual cuspidal newspace energy, with coefficient one. Summability and
orthogonality are proved for the actual operators and spaces. -/
theorem canonical_sector_energy_le {ι : Type*} (N : ℕ) (hN : 0<N) [NeZero N]
    (b : HilbertBasis ι ℂ (completedCuspidalNewSpace N hN))
    (κ : realizedNewCharacter N hN→Type*)
    (c : ∀ χ,HilbertBasis (κ χ) ℂ (completedNewSignSpace N hN χ.val))
    (f : ℝ→ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    (∀ χ,Summable (fun j => ‖completedNewSignTimePacket N hN χ.val f hf he hc hr R hR hs (c χ j)‖^2)) ∧
    Summable (fun χ => hilbertSchmidtEnergy (c χ)
      (completedNewSignTimePacket N hN χ.val f hf he hc hr R hR hs)) ∧
    (∑' χ,hilbertSchmidtEnergy (c χ) (completedNewSignTimePacket N hN χ.val f hf he hc hr R hR hs))≤
      hilbertSchmidtEnergy b (completedCuspidalNewTimePacket N hN f hf hc) := by
  apply orthogonal_sector_energy_le (H := completedCuspidalNewSpace N hN)
    (fun χ : realizedNewCharacter N hN => completedNewSignInclusion N hN χ.val)
    (completedNewSignInclusion_orthogonal N hN) b c
    (completedCuspidalNewTimePacket N hN f hf hc)
    (fun χ => completedNewSignTimePacket N hN χ.val f hf he hc hr R hR hs)
  · intro χ x
    rfl
  · exact completedCuspidalNewTimePacket_summable N hN b f hf hc

#print axioms completedNewSignInclusion_orthogonal
#print axioms canonical_sector_energy_le

end QuantitativeMaass
