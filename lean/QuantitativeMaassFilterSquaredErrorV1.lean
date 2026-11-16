module

public import QuantitativeMaassFilterEigenvectorsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Module

namespace QuantitativeMaass

/-- The squared Hilbert--Schmidt error of the actual kernel filter is at
most its trace excess. This makes the spectral rank estimate usable after
bounded embeddings and reconstruction maps. -/
theorem half_filter_squared_error_le_trace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric)
    (heig : ∀ i,0≤hS.eigenvalues rfl i ∧ hS.eigenvalues rfl i≤2) (m : ℕ) :
    (∑ i : Fin (finrank ℂ E),
      ‖((1-(1/2:ℂ) • S)^m) (hS.eigenvectorBasis rfl i)-
        S.ker.starProjection (hS.eigenvectorBasis rfl i)‖^2) ≤
      (LinearMap.trace ℂ E ((1-(1/2:ℂ) • S)^m)).re-(finrank ℂ S.ker:ℝ) := by
  classical
  have hk : (Finset.univ.filter (fun i : Fin (finrank ℂ E) => hS.eigenvalues rfl i=0)).card=
      finrank ℂ S.ker := by
    have hh := hS.card_filter_eigenvalues_eq rfl (0:ℂ)
    rw [Module.End.eigenspace_zero] at hh
    simpa using hh
  have ht : (LinearMap.trace ℂ E ((1-(1/2:ℂ) • S)^m)).re=
      ∑ i : Fin (finrank ℂ E),(1-hS.eigenvalues rfl i/2)^m := by
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,div_mul_eq_mul_div,one_mul]
      using symmetric_affine_power_trace S hS (1/2) m
  have hp (i : Fin (finrank ℂ E)) :
      ‖((1-(1/2:ℂ) • S)^m) (hS.eigenvectorBasis rfl i)-
        S.ker.starProjection (hS.eigenvectorBasis rfl i)‖^2 ≤
      (1-hS.eigenvalues rfl i/2)^m-(if hS.eigenvalues rfl i=0 then (1:ℝ) else 0) := by
    have ha : ((1-(1/2:ℂ) • S)^m) (hS.eigenvectorBasis rfl i)=
        (((1-hS.eigenvalues rfl i/2)^m:ℝ):ℂ) • hS.eigenvectorBasis rfl i := by
      simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,div_mul_eq_mul_div,one_mul]
        using affine_filter_eigenvector S hS (1/2) m i
    rw [ha,kernelProjection_eigenvector]
    by_cases hz : hS.eigenvalues rfl i=0
    · simp [hz]
    · simp only [hz,ite_false,sub_zero,norm_smul,Complex.norm_real,Real.norm_eq_abs,
        (hS.eigenvectorBasis rfl).orthonormal.norm_eq_one i,mul_one,sq_abs]
      have h0 : 0≤(1-hS.eigenvalues rfl i/2)^m := pow_nonneg (by linarith only [(heig i).2]) _
      have h1 : (1-hS.eigenvalues rfl i/2)^m≤1 := pow_le_one₀
        (by linarith only [(heig i).2]) (by linarith only [(heig i).1])
      nlinarith only [h0,h1]
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hp i)
  rw [ht]
  simpa [Finset.sum_sub_distrib,hk] using hh

#print axioms half_filter_squared_error_le_trace

/-- The same trace error controls the filter after any bounded observation
or reconstruction map, with its explicit squared operator norm. -/
theorem half_filter_bounded_squared_error {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric)
    (heig : ∀ i,0≤hS.eigenvalues rfl i ∧ hS.eigenvalues rfl i≤2)
    (L : E →L[ℂ] F) (m : ℕ) :
    (∑ i : Fin (finrank ℂ E),
      ‖L (((1-(1/2:ℂ) • S)^m) (hS.eigenvectorBasis rfl i)-
        S.ker.starProjection (hS.eigenvectorBasis rfl i))‖^2) ≤
      ‖L‖^2*((LinearMap.trace ℂ E ((1-(1/2:ℂ) • S)^m)).re-(finrank ℂ S.ker:ℝ)) := by
  calc
    _ ≤ ∑ i : Fin (finrank ℂ E), ‖L‖^2*
        ‖((1-(1/2:ℂ) • S)^m) (hS.eigenvectorBasis rfl i)-
          S.ker.starProjection (hS.eigenvectorBasis rfl i)‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm _) 2
    _ = ‖L‖^2*∑ i : Fin (finrank ℂ E),
        ‖((1-(1/2:ℂ) • S)^m) (hS.eigenvectorBasis rfl i)-
          S.ker.starProjection (hS.eigenvectorBasis rfl i)‖^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (half_filter_squared_error_le_trace S hS heig m) (sq_nonneg _)

#print axioms half_filter_bounded_squared_error

end QuantitativeMaass
