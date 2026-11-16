module

public import QuantitativeMaassCanonicalSectorEnergyV1
public import QuantitativeMaassParityWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set AsymptoticClassicalPetersson
open scoped SchwartzMap ContDiff

namespace QuantitativeMaass

def completedParitySpace (N : ℕ) (η : ℝ) : Submodule ℂ (AutomorphicSpace N) :=
  (parityProjection N η-1).ker

theorem mem_completedParitySpace (N : ℕ) (η : ℝ) (x : AutomorphicSpace N) :
    x∈completedParitySpace N η ↔ parityProjection N η x=x := by
  change (parityProjection N η-1) x=0 ↔ _
  simp only [sub_apply,one_apply_eq_self,sub_eq_zero]

theorem completedParitySpace_closed (N : ℕ) (η : ℝ) :
    IsClosed (completedParitySpace N η : Set (AutomorphicSpace N)) :=
  (parityProjection N η-1).isClosed_ker

def completedNewSignParitySpace (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (η : ℝ) : Submodule ℂ (AutomorphicSpace N) :=
  completedNewSignSpace N hN χ ⊓ completedParitySpace N η

def completedCuspidalNewParitySpace (N : ℕ) (hN : 0<N) [NeZero N]
    (η : ℝ) : Submodule ℂ (AutomorphicSpace N) :=
  completedCuspidalNewSpace N hN ⊓ completedParitySpace N η

instance completedNewSignParitySpace_complete (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (η : ℝ) : CompleteSpace (completedNewSignParitySpace N hN χ η) :=
  ((completedNewSignSpace_closed N hN χ).inter (completedParitySpace_closed N η)).completeSpace_coe

instance completedCuspidalNewParitySpace_complete (N : ℕ) (hN : 0<N) [NeZero N]
    (η : ℝ) : CompleteSpace (completedCuspidalNewParitySpace N hN η) :=
  (((localCuspidalSpace_closed N hN).inter (actualNewSpace_closed N hN)).inter
    (completedParitySpace_closed N η)).completeSpace_coe

def completedNewSignParityInclusion (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (η : ℝ) :
    completedNewSignParitySpace N hN χ η→ₗᵢ[ℂ]completedNewSignSpace N hN χ where
  toLinearMap := Submodule.inclusion inf_le_left
  norm_map' _ := rfl

def completedCuspidalNewParityInclusion (N : ℕ) (hN : 0<N) [NeZero N] (η : ℝ) :
    completedCuspidalNewParitySpace N hN η→ₗᵢ[ℂ]completedCuspidalNewSpace N hN where
  toLinearMap := Submodule.inclusion inf_le_left
  norm_map' _ := rfl

theorem completedParitySpace_timePacket (N : ℕ) [NeZero N] (η : ℝ)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (x : AutomorphicSpace N) (hx : x∈completedParitySpace N η) :
    Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc) x∈
      completedParitySpace N η := by
  apply (mem_completedParitySpace N η _).mpr
  have hh := DFunLike.congr_fun (parityProjection_commute N η _
    (evenWavePacket_reflection_commute N f hc he hr R hR hs)) x
  change parityProjection N η (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc) x)=
    Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc) (parityProjection N η x) at hh
  rw [(mem_completedParitySpace N η x).mp hx] at hh
  exact hh

def completedNewSignParityTimePacket (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (η : ℝ)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    completedNewSignParitySpace N hN χ η→L[ℂ]completedNewSignParitySpace N hN χ η :=
  ((Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)).comp
    (completedNewSignParitySpace N hN χ η).subtypeL).codRestrict (completedNewSignParitySpace N hN χ η)
    (fun x => ⟨completedNewSignSpace_timePacket N hN χ f (f.smooth ⊤) he hc hr R hR hs x.val x.property.1,
      completedParitySpace_timePacket N η f hc he hr R hR hs x.val x.property.2⟩)

def completedCuspidalNewParityTimePacket (N : ℕ) (hN : 0<N) [NeZero N] (η : ℝ)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    completedCuspidalNewParitySpace N hN η→L[ℂ]completedCuspidalNewParitySpace N hN η :=
  ((Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)).comp
    (completedCuspidalNewParitySpace N hN η).subtypeL).codRestrict (completedCuspidalNewParitySpace N hN η)
    (fun x => ⟨⟨shiftedQuotientWavePacket_mem_localCuspidalSpace N hN f
      (compactSmoothWaveWeight f (f.smooth ⊤) hc) x.val x.property.1.1,
      actualNewSpace_timePacket N hN f (compactSmoothWaveWeight f (f.smooth ⊤) hc) x.val x.property.1.2⟩,
      completedParitySpace_timePacket N η f hc he hr R hR hs x.val x.property.2⟩)

#print axioms mem_completedParitySpace
#print axioms completedParitySpace_closed
#print axioms completedParitySpace_timePacket

end QuantitativeMaass
