module

public import QuantitativeMaassLowSpectrumFilterV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open scoped InnerProductSpace

namespace QuantitativeMaass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The quadratic form of a symmetric idempotent is its projected norm. -/
theorem symmetric_idempotent_inner (P : E →ₗ[ℂ] E) (hP : P.IsSymmetric)
    (hPP : IsIdempotentElem P) (v : E) :
    (inner ℂ (P v) v).re=‖P v‖^2 := by
  have hh := hP (P v) v
  have hp : P (P v)=P v := DFunLike.congr_fun hPP v
  rw [hp] at hh
  exact (congrArg Complex.re hh).trans (inner_self_eq_norm_sq (𝕜 := ℂ) _)

/-- Symmetry and idempotence imply contraction without a spectral hypothesis. -/
theorem symmetric_idempotent_norm_le (P : E →ₗ[ℂ] E) (hP : P.IsSymmetric)
    (hPP : IsIdempotentElem P) (v : E) : ‖P v‖≤‖v‖ := by
  have hh := (Complex.re_le_norm (inner ℂ (P v) v)).trans (norm_inner_le_norm (P v) v)
  rw [symmetric_idempotent_inner P hP hPP v,pow_two] at hh
  by_cases hz : ‖P v‖=0
  · rw [hz]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left hh (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))

/-- The sum of two actual orthogonal projections has spectrum in [0,2],
regardless of how small the angle between their ranges is. -/
theorem two_projection_eigenvalue_bounds (P Q : E →ₗ[ℂ] E)
    (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hPP : IsIdempotentElem P) (hQQ : IsIdempotentElem Q)
    (v : E) (hv : ‖v‖=1) (μ : ℝ) (he : (P+Q) v=(μ:ℂ) • v) :
    0≤μ ∧ μ≤2 := by
  have hi : (inner ℂ ((P+Q) v) v).re=μ := by
    rw [he,inner_smul_left]
    simp [inner_self_eq_norm_sq_to_K,hv]
  have heq : μ=‖P v‖^2+‖Q v‖^2 := by
    rw [←hi,LinearMap.add_apply,inner_add_left,Complex.add_re,
      symmetric_idempotent_inner P hP hPP v,symmetric_idempotent_inner Q hQ hQQ v]
  have hp := (symmetric_idempotent_norm_le P hP hPP v).trans_eq hv
  have hq := (symmetric_idempotent_norm_le Q hQ hQQ v).trans_eq hv
  rw [heq]
  constructor
  · positivity
  · nlinarith [norm_nonneg (P v),norm_nonneg (Q v)]

/-- The canonical finite-band eigenvalues satisfy the same proved bounds. -/
theorem two_projection_spectrum_bounds [FiniteDimensional ℂ E]
    (P Q : E →ₗ[ℂ] E) (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hPP : IsIdempotentElem P) (hQQ : IsIdempotentElem Q)
    (i : Fin (Module.finrank ℂ E)) :
    0≤(hP.add hQ).eigenvalues rfl i ∧ (hP.add hQ).eigenvalues rfl i≤2 := by
  exact two_projection_eigenvalue_bounds P Q hP hQ hPP hQQ
    ((hP.add hQ).eigenvectorBasis rfl i) (((hP.add hQ).eigenvectorBasis rfl).orthonormal.norm_eq_one i)
    _ ((hP.add hQ).apply_eigenvectorBasis rfl i)

/-- The kernel of the sum is the common kernel of the two projections. -/
theorem two_projection_kernel (P Q : E →ₗ[ℂ] E)
    (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hPP : IsIdempotentElem P) (hQQ : IsIdempotentElem Q) :
    (P+Q).ker=P.ker ⊓ Q.ker := by
  ext v
  constructor
  · intro hv
    change P v+Q v=0 at hv
    have hi : ‖P v‖^2+‖Q v‖^2=0 := by
      rw [←symmetric_idempotent_inner P hP hPP v,←symmetric_idempotent_inner Q hQ hQQ v,
        ←Complex.add_re,←inner_add_left,hv,inner_zero_left,Complex.zero_re]
    have hp : ‖P v‖=0 := by nlinarith [sq_nonneg ‖Q v‖]
    have hq : ‖Q v‖=0 := by nlinarith [sq_nonneg ‖P v‖]
    exact ⟨norm_eq_zero.mp hp,norm_eq_zero.mp hq⟩
  · rintro ⟨hp,hq⟩
    change P v+Q v=0
    change P v=0 at hp
    change Q v=0 at hq
    rw [hp,hq,add_zero]

#print axioms two_projection_kernel

#print axioms symmetric_idempotent_inner
#print axioms symmetric_idempotent_norm_le
#print axioms two_projection_eigenvalue_bounds
#print axioms two_projection_spectrum_bounds

end QuantitativeMaass
