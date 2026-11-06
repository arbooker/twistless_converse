module

public import AsymptoticClassicalEigenNormalizationV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalEigenbasis

open Module

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Spectral theory and first-coefficient extraction produce exactly
`finrank` distinct normalized simultaneous eigenvectors. -/
theorem exists_normalized_joint_family (T : ι → E →ₗ[ℂ] E)
    (hT : ∀ i, (T i).IsSymmetric)
    (hcomm : Pairwise fun i j => Commute (T i) (T j))
    (first : E →ₗ[ℂ] ℂ) (coeff : ι → E →ₗ[ℂ] ℂ)
    (hcoeff : ∀ i v, first (T i v) = coeff i v)
    (hsep : ∀ v, (∀ i, coeff i v = 0) → v = 0) :
    ∃ b : Fin (finrank ℂ E) → E, Function.Injective b ∧
      (∀ j, first (b j) = 1) ∧
      ∀ j, ∃ χ : ι → ℂ, ∀ i, T i (b j) = χ i • b j := by
  obtain ⟨b, hb, he⟩ := exists_joint_family T hT hcomm
  have hfirst : ∀ j, first (b j) ≠ 0 := by
    intro j
    obtain ⟨χ, hχ⟩ := he j
    exact first_ne_zero T first coeff hcoeff hsep (hb.ne_zero j) hχ
  refine ⟨fun j => normalizedVector first (b j),
    normalizedVector_injective hb first hfirst,
    fun j => first_normalizedVector first (hfirst j), ?_⟩
  intro j
  obtain ⟨χ, hχ⟩ := he j
  exact ⟨χ, normalizedVector_eigen T first hχ⟩

/-- A finite target set containing the injective images of all normalized
joint eigenvectors has cardinality at least the dimension. The analytic
membership and operator identities are explicit hypotheses here. -/
theorem dimension_le_target_ncard {α : Type*} (S : Set α) (hS : S.Finite)
    (T : ι → E →ₗ[ℂ] E) (hT : ∀ i, (T i).IsSymmetric)
    (hcomm : Pairwise fun i j => Commute (T i) (T j))
    (first : E →ₗ[ℂ] ℂ) (coeff : ι → E →ₗ[ℂ] ℂ)
    (hcoeff : ∀ i v, first (T i v) = coeff i v)
    (hsep : ∀ v, (∀ i, coeff i v = 0) → v = 0)
    (sequence : E → α) (hseq : Function.Injective sequence)
    (hmem : ∀ v, first v = 1 →
      (∃ χ : ι → ℂ, ∀ i, T i v = χ i • v) → sequence v ∈ S) :
    finrank ℂ E ≤ S.ncard := by
  obtain ⟨b, hb, hfirst, he⟩ :=
    exists_normalized_joint_family T hT hcomm first coeff hcoeff hsep
  have hsub : Set.range (sequence ∘ b) ⊆ S := by
    rintro _ ⟨j, rfl⟩
    exact hmem (b j) (hfirst j) (he j)
  have hc := Set.ncard_le_ncard hsub hS
  rw [Set.ncard_range_of_injective (hseq.comp hb)] at hc
  simpa using hc

#print axioms exists_normalized_joint_family
#print axioms dimension_le_target_ncard

end AsymptoticClassicalEigenbasis
