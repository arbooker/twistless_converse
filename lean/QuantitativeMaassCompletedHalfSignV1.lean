module

public import QuantitativeMaassFiniteGeneratorSignsV1
public import QuantitativeMaassCompletedNewSignSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson QuantitativeNinaMaass

namespace QuantitativeMaass

/-- Newness itself forces the half-translation sign on every completed vector. -/
theorem newSpace_half_completed (N : ℕ) (hN : 0<N) (h4 : 4∣N) [NeZero N]
    (x : AutomorphicSpace N) (hx : x∈newSpace N hN) :
    quotientNormalizerPullback N (completedHalfNormalizer N hN h4) x= -x := by
  have h2 : 2∣N := (by decide : 2∣4).trans h4
  simp only [newSpace,Submodule.mem_iInf] at hx
  have ht := hx ⟨2,by decide,h2⟩
  obtain ⟨M,rfl⟩ := h2
  have hM : 0<M := by omega
  have hM2 : 2∣M := by omega
  have hdiv : 2*M/2=M := by omega
  have ht' : x∈newTraceKernel (Nat.mul_pos (by decide : 0<2) hM) (Nat.dvd_mul_left M 2) := by
    simpa only [hdiv] using ht
  exact dyadic_new_half_completed M hM hM2 x ht'

def halfGeneratorIndex (N : ℕ) (hN : 0<N) (h4 : 4∣N) : admissibleGeneratorIndex N hN :=
  ⟨AsymptoticIntegralSubgroup.translationLabel (1/2),admissibleNormalizerGenerator.half h4⟩

theorem completedNewSign_half_character (N : ℕ) (hN : 0<N) (h4 : 4∣N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN → ℂ) (x : AutomorphicSpace N)
    (hx : x∈completedNewSignSpace N hN χ) (hx0 : x≠0) :
    χ (halfGeneratorIndex N hN h4)= -1 := by
  have he := newSpace_half_completed N hN h4 x hx.2.1
  change quotientNormalizerPullback N (admissibleGeneratorLift N hN (halfGeneratorIndex N hN h4)) x= -x at he
  rw [hx.2.2 (halfGeneratorIndex N hN h4)] at he
  exact smul_left_injective ℂ hx0 (he.trans (neg_one_smul ℂ x).symm)

#print axioms newSpace_half_completed
#print axioms completedNewSign_half_character

end QuantitativeMaass
