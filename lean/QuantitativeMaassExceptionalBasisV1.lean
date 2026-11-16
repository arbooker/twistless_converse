module

public import QuantitativeArithmeticExceptionalOldSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Module QuantitativeArithmeticExceptionalMoments QuantitativeArithmeticExceptionalOldSpace
open scoped InnerProductSpace

namespace QuantitativeMaass

/-- The exceptional space can be identified using any orthonormal
Hecke eigenbasis, including a basis simultaneously diagonalizing energy. -/
theorem exceptionalSpace_eq_basis_span {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [Fintype ι]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (b : OrthonormalBasis ι ℂ E)
    (τ : ι→ℝ) (hb : ∀ i,T (b i)=(τ i:ℂ) • b i) (a : ℝ) :
    exceptionalSpace hT a=Submodule.span ℂ
      (Set.range (fun i : {i : ι // a≤|τ i|} => b i.val)) := by
  classical
  apply le_antisymm
  · unfold exceptionalSpace
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change hT.eigenvectorBasis rfl i.val∈_
    rw [←b.sum_repr (hT.eigenvectorBasis rfl i.val)]
    apply Submodule.sum_mem
    intro j _
    by_cases hj : a≤|τ j|
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j,hj⟩,rfl⟩)
    · have hne : (τ j:ℂ)≠(hT.eigenvalues rfl i.val:ℂ) := by
        intro heq
        apply hj
        rw [Complex.ofReal_injective heq]
        exact (Finset.mem_filter.mp i.property).2
      have hz : b.repr (hT.eigenvectorBasis rfl i.val) j=0 := by
        rw [b.repr_apply_apply]
        exact hT.orthogonalFamily_eigenspaces hne
          ⟨b j,Module.End.mem_eigenspace_iff.mpr (hb j)⟩
          ⟨hT.eigenvectorBasis rfl i.val,Module.End.mem_eigenspace_iff.mpr (hT.apply_eigenvectorBasis rfl i.val)⟩
      rw [hz,zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact eigen_mem_exceptional hT a (τ i.val) i.property (b i.val) (hb i.val)

/-- Exceptional rank equals the number of qualifying vectors in any
joint orthonormal eigenbasis, independently of the canonical spectral basis. -/
theorem exceptionalSpace_finrank_basis {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [Fintype ι]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (b : OrthonormalBasis ι ℂ E)
    (τ : ι→ℝ) (hb : ∀ i,T (b i)=(τ i:ℂ) • b i) (a : ℝ) :
    finrank ℂ (exceptionalSpace hT a)=Nat.card {i : ι // a≤|τ i|} := by
  classical
  rw [exceptionalSpace_eq_basis_span T hT b τ hb a]
  have hi : LinearIndependent ℂ (fun i : {i : ι // a≤|τ i|} => b i.val) :=
    b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  simpa only [Nat.card_eq_fintype_card] using finrank_span_eq_card hi

#print axioms exceptionalSpace_eq_basis_span
#print axioms exceptionalSpace_finrank_basis

end QuantitativeMaass
