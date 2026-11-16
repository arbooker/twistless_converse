module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space

/-! Consolidated chapter: QuantitativeArithmeticMaassCuspBand. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticDenseEigenspaceBasisV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 0
set_option Elab.async false
@[expose] public noncomputable section
open Set
open scoped InnerProductSpace
universe u
namespace QuantitativeArithmeticMaassCuspBand
/-- An orthonormal eigenbasis follows from the dense family of eigenspaces.
This separates the abstract Hilbert-space construction from the concrete
quotient and its inherited instances. -/
theorem exists_eigenbasis_of_dense_eigenspaces
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (hd : (⨆ μ : ℂ, Module.End.eigenspace T.toLinearMap μ).topologicalClosure = ⊤) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ H) (μ : ι → ℂ),
      ∀ i, T (b i) = μ i • b i := by
  classical
  let E := fun μ : ℂ => Module.End.eigenspace T.toLinearMap μ
  have hclosed (μ : ℂ) : IsClosed (E μ : Set H) := by
    have he : (E μ : Set H) = {v | T v = μ • v} := by
      ext v
      exact Module.End.mem_eigenspace_iff
    rw [he]
    exact isClosed_eq T.continuous (continuous_const_smul μ)
  let (μ : ℂ) : CompleteSpace (E μ) := (hclosed μ).completeSpace_coe
  choose J b hb using fun μ : ℂ => exists_hilbertBasis ℂ (E μ)
  let v : (Σ μ : ℂ, J μ) → H := fun i => (b i.1 i.2 : H)
  have hv : Orthonormal ℂ v :=
    hT.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
      (fun μ => (b μ).orthonormal)
  let W := (Submodule.span ℂ (Set.range v)).topologicalClosure
  have hle (μ : ℂ) : E μ ≤ W := by
    let C := W.comap (E μ).subtype
    have hC : IsClosed (C : Set (E μ)) :=
      (Submodule.span ℂ (Set.range v)).isClosed_topologicalClosure.preimage
        continuous_subtype_val
    have hspan : Submodule.span ℂ (Set.range (b μ)) ≤ C := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact (Submodule.span ℂ (Set.range v)).le_topologicalClosure
        (Submodule.subset_span ⟨⟨μ, j⟩, rfl⟩)
    have htop : (⊤ : Submodule ℂ (E μ)) ≤ C := by
      rw [← (b μ).dense_span]
      exact (Submodule.span ℂ (Set.range (b μ))).topologicalClosure_minimal hspan hC
    intro x hx
    exact htop (show (⟨x, hx⟩ : E μ) ∈ (⊤ : Submodule ℂ (E μ)) from by trivial)
  have htotal : (⊤ : Submodule ℂ H) ≤ W := by
    have h := (⨆ μ : ℂ, E μ).topologicalClosure_minimal
      (iSup_le hle) (Submodule.span ℂ (Set.range v)).isClosed_topologicalClosure
    rw [show (⨆ μ : ℂ, E μ).topologicalClosure = ⊤ from hd] at h
    exact h
  refine ⟨Σ μ : ℂ, J μ, HilbertBasis.mk hv htotal, fun i => i.1, ?_⟩
  intro i
  rw [HilbertBasis.coe_mk]
  exact Module.End.mem_eigenspace_iff.mp (b i.1 i.2).property

#print axioms exists_eigenbasis_of_dense_eigenspaces

end QuantitativeArithmeticMaassCuspBand
end
end

/-! ## QuantitativeArithmeticL2SubspaceEigenbasisV4 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
open MeasureTheory Set
namespace QuantitativeArithmeticMaassCuspBand
open scoped ENNReal
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

/-- Specialize the spectral-basis construction before introducing a concrete
quotient measure. This keeps both inherited subspace structures identical at
the interface, rather than comparing them through the quotient construction. Both inherited structures are supplied explicitly to the abstract theorem. -/
theorem exists_eigenbasis_in_nested_L2_subspace
    {α : Type} [MeasurableSpace α] (ν : Measure α)
    (A : Submodule ℂ (Lp ℂ 2 ν)) (S : Submodule ℂ A) [CompleteSpace S]
    (T : S →L[ℂ] S)
    (hT : LinearMap.IsSymmetric (𝕜 := ℂ) (E := ↥S) T.toLinearMap)
    (hd : (⨆ μ : ℂ, Module.End.eigenspace (R := ℂ) (M := ↥S)
      T.toLinearMap μ).topologicalClosure = ⊤) :
    ∃ (ι : Type) (b : HilbertBasis ι ℂ S) (μ : ι → ℂ),
      ∀ i, T (b i) = μ i • b i := by
  exact @exists_eigenbasis_of_dense_eigenspaces ↥S
    (Submodule.normedAddCommGroup (𝕜 := ℂ) (E := ↥A) S)
    (Submodule.innerProductSpace (𝕜 := ℂ) (E := ↥A) S)
    inferInstance T hT hd


#print axioms exists_eigenbasis_in_nested_L2_subspace
end QuantitativeArithmeticMaassCuspBand
end
end
