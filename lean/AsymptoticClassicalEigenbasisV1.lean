module

public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalEigenbasis

open Module

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A commuting symmetric family has a full linearly independent family of
simultaneous eigenvectors. The indexing family of operators may be infinite. -/
theorem exists_joint_family (T : ι → E →ₗ[ℂ] E)
    (hT : ∀ i, (T i).IsSymmetric)
    (hcomm : Pairwise fun i j => Commute (T i) (T j)) :
    ∃ b : Fin (finrank ℂ E) → E, LinearIndependent ℂ b ∧
      ∀ j, ∃ χ : ι → ℂ, ∀ i, T i (b j) = χ i • b j := by
  classical
  let s : Set E := {v | ∃ χ : ι → ℂ, ∀ i, T i v = χ i • v}
  have hspan : Submodule.span ℂ s = ⊤ := by
    apply top_unique
    rw [← LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hcomm]
    refine iSup_le fun χ => ?_
    intro v hv
    apply Submodule.subset_span
    refine ⟨χ, fun i => ?_⟩
    exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf (fun i => Module.End.eigenspace (T i) (χ i))).mp hv i)
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℂ s
  have hdim : finrank ℂ (Submodule.span ℂ s) = finrank ℂ E := by
    rw [hspan, finrank_top]
  rw [hdim] at hex
  obtain ⟨b, hb, _, hli⟩ := hex
  exact ⟨b, hli, hb⟩

#print axioms exists_joint_family

end AsymptoticClassicalEigenbasis
