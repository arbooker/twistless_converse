module

public import QuantitativeMaassGeneratorInvolutionsV1
public import QuantitativeMaassCompletedNewSignSpaceV1
public import Mathlib.Analysis.InnerProductSpace.Spectrum

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson
open scoped InnerProductSpace

namespace QuantitativeMaass

theorem admissibleGeneratorPullback_symmetric (N : ℕ) (hN : 0<N)
    (i : admissibleGeneratorIndex N hN) :
    (quotientNormalizerPullback N (admissibleGeneratorLift N hN i)).toLinearMap.IsSymmetric := by
  intro x y
  have he := (quotientNormalizerPullback N (admissibleGeneratorLift N hN i)).inner_map_map x
    (quotientNormalizerPullback N (admissibleGeneratorLift N hN i) y)
  rw [admissibleGeneratorPullback_involutive N hN i y] at he
  exact he

/-- Distinct realized generator characters have orthogonal completed
joint eigenspaces. No simultaneous decomposition is assumed. -/
theorem completedGeneratorSpace_orthogonal (N : ℕ) (hN : 0<N)
    (χ ψ : admissibleGeneratorIndex N hN→ℂ) (hne : χ≠ψ)
    (x y : AutomorphicSpace N) (hx : x∈completedGeneratorSpace N hN χ)
    (hy : y∈completedGeneratorSpace N hN ψ) : inner ℂ x y=0 := by
  classical
  have hex : ∃ i,χ i≠ψ i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨i,hi⟩ := hex
  exact (admissibleGeneratorPullback_symmetric N hN i).orthogonalFamily_eigenspaces
    hi ⟨x,Module.End.mem_eigenspace_iff.mpr (hx i)⟩
    ⟨y,Module.End.mem_eigenspace_iff.mpr (hy i)⟩

theorem completedNewSignSpace_orthogonal (N : ℕ) (hN : 0<N) [NeZero N]
    (χ ψ : admissibleGeneratorIndex N hN→ℂ) (hne : χ≠ψ)
    (x : completedNewSignSpace N hN χ) (y : completedNewSignSpace N hN ψ) :
    inner ℂ x.val y.val=0 :=
  completedGeneratorSpace_orthogonal N hN χ ψ hne x.val y.val x.property.2.2 y.property.2.2

#print axioms admissibleGeneratorPullback_symmetric
#print axioms completedGeneratorSpace_orthogonal
#print axioms completedNewSignSpace_orthogonal

end QuantitativeMaass
