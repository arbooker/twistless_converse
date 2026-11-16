module

public import QuantitativeMaassFilterSquaredErrorV1
public import Mathlib.Analysis.InnerProductSpace.Trace

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Module
open scoped InnerProductSpace

namespace QuantitativeMaass

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℂ E] in
/-- The finite-band squared observation energy is independent of its
orthonormal basis, including observations into an infinite Hilbert space. -/
theorem finite_band_squared_sum_eq_trace {ι : Type*} [Fintype ι]
    (L : E →L[ℂ] F) (b : OrthonormalBasis ι ℂ E) :
    (∑ i,‖L (b i)‖^2)=(LinearMap.trace ℂ E (L.adjoint.comp L).toLinearMap).re := by
  rw [LinearMap.trace_eq_sum_inner _ b,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ‖L (b i)‖^2=(inner ℂ (b i) (L.adjoint (L (b i)))).re
  rw [L.adjoint_inner_right]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

/-- The physical filter error bound holds in every orthonormal band basis. -/
theorem half_filter_bounded_squared_error_basis {ι : Type*} [Fintype ι]
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric)
    (heig : ∀ i,0≤hS.eigenvalues rfl i ∧ hS.eigenvalues rfl i≤2)
    (L : E →L[ℂ] F) (m : ℕ) (b : OrthonormalBasis ι ℂ E) :
    (∑ i,‖L (((1-(1/2:ℂ) • S)^m) (b i)-S.ker.starProjection (b i))‖^2) ≤
      ‖L‖^2*((LinearMap.trace ℂ E ((1-(1/2:ℂ) • S)^m)).re-(finrank ℂ S.ker:ℝ)) := by
  let D : E →L[ℂ] F := L.comp (((1-(1/2:ℂ) • S)^m).toContinuousLinearMap-S.ker.starProjection)
  have hh := (finite_band_squared_sum_eq_trace D b).trans
    (finite_band_squared_sum_eq_trace D (hS.eigenvectorBasis rfl)).symm
  change (∑ i,‖L (((1-(1/2:ℂ) • S)^m) (b i)-S.ker.starProjection (b i))‖^2)=_ at hh
  rw [hh]
  exact half_filter_bounded_squared_error S hS heig L m

#print axioms finite_band_squared_sum_eq_trace
#print axioms half_filter_bounded_squared_error_basis

end QuantitativeMaass
