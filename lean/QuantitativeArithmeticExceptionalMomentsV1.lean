module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

open Module

namespace QuantitativeArithmeticExceptionalMoments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E}

/-- The actual eigenvectors with eigenvalue magnitude at least `a`, counted
with multiplicity. The threshold will be above the regular Hecke norm. -/
def exceptionalIndices (hT : T.IsSymmetric) (a : ℝ) : Finset (Fin (finrank ℂ E)) :=
  Finset.univ.filter (fun i => a ≤ |hT.eigenvalues rfl i|)

def exceptionalSpace (hT : T.IsSymmetric) (a : ℝ) : Submodule ℂ E :=
  Submodule.span ℂ (Set.range (fun i : exceptionalIndices hT a =>
    hT.eigenvectorBasis rfl i.val))

theorem exceptionalSpace_finrank (hT : T.IsSymmetric) (a : ℝ) :
    finrank ℂ (exceptionalSpace hT a) = (exceptionalIndices hT a).card := by
  classical
  unfold exceptionalSpace
  have hi : LinearIndependent ℂ (fun i : exceptionalIndices hT a =>
      hT.eigenvectorBasis rfl i.val) :=
    (hT.eigenvectorBasis rfl).orthonormal.linearIndependent.comp
      (fun i : exceptionalIndices hT a => i.val) Subtype.val_injective
  exact (finrank_span_eq_card hi).trans (Fintype.card_coe _)

/-- The power trace is the even spectral moment, with no asymptotic or
trace-comparison hypothesis. -/
theorem trace_even_power (hT : T.IsSymmetric) (d : ℕ) :
    (LinearMap.trace ℂ E (T ^ (2*d))).re =
      ∑ i : Fin (finrank ℂ E), (hT.eigenvalues rfl i) ^ (2*d) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (hT.eigenvectorBasis rfl).toBasis,
    ← LinearMap.toMatrix_pow, hT.toMatrix_eigenvectorBasis rfl]
  simp [Matrix.diagonal_pow, Matrix.trace, Function.comp_def, ← Complex.ofReal_pow]

/-- Markov's even-moment bound for the literal exceptional eigenspace. -/
theorem exceptionalSpace_moment (hT : T.IsSymmetric) (a : ℝ) (ha : 0 ≤ a) (d : ℕ) :
    a^(2*d) * (finrank ℂ (exceptionalSpace hT a) : ℝ) ≤
      (LinearMap.trace ℂ E (T^(2*d))).re := by
  classical
  rw [exceptionalSpace_finrank, trace_even_power hT d]
  have hp (i) (hi : i ∈ exceptionalIndices hT a) :
      a^(2*d) ≤ (hT.eigenvalues rfl i)^(2*d) := by
    have h := (Finset.mem_filter.mp hi).2
    have hh : a^(2*d) ≤ |hT.eigenvalues rfl i|^(2*d) := by gcongr
    simpa only [pow_mul, sq_abs] using hh
  calc
    _ = ∑ _i ∈ exceptionalIndices hT a, a^(2*d) := by simp [mul_comm]
    _ ≤ ∑ i ∈ exceptionalIndices hT a, (hT.eigenvalues rfl i)^(2*d) :=
      Finset.sum_le_sum hp
    _ ≤ ∑ i : Fin (finrank ℂ E), (hT.eigenvalues rfl i)^(2*d) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      rw [pow_mul]
      positivity

/-- Degeneracy maps transfer exceptional rank without dividing by the
angle between their images. -/
theorem two_image_finrank {F : Type*} [AddCommGroup F] [Module ℂ F]
    [FiniteDimensional ℂ F] (U : Submodule ℂ E) (f g : E →ₗ[ℂ] F) :
    finrank ℂ ↥(U.map f ⊔ U.map g) ≤ 2 * finrank ℂ U := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (U.map f) (U.map g)
  have hf := Submodule.finrank_map_le f U
  have hg := Submodule.finrank_map_le g U
  omega

#print axioms exceptionalSpace_finrank
#print axioms trace_even_power
#print axioms exceptionalSpace_moment
#print axioms two_image_finrank

end QuantitativeArithmeticExceptionalMoments
