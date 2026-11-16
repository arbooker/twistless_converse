module

public import QuantitativeArithmeticExceptionalOldSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open scoped InnerProductSpace
open QuantitativeArithmeticExceptionalOldSpace

namespace QuantitativeMaass

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A common real normalization of two adjoint maps identifies the second
cross term from the symmetry of the first one. -/
theorem paired_adjoint_cross (A B : E →ₗ[ℂ] F) (A' B' : F →ₗ[ℂ] E)
    (C : E →ₗ[ℂ] E) (r : ℝ)
    (hA : ∀ x y, inner ℂ x (A' y) = (r:ℂ)*inner ℂ (A x) y)
    (hB : ∀ x y, inner ℂ x (B' y) = (r:ℂ)*inner ℂ (B x) y)
    (hC : C.IsSymmetric) (hab : ∀ x, A' (B x)=C x) :
    ∀ x, B' (A x)=C x := by
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [hB]
  have hh := congrArg (starRingEnd ℂ) (hA x (B y))
  simp only [map_mul,Complex.conj_ofReal,inner_conj_symm,hab] at hh
  rw [←hh]
  exact hC y x

/-- A normalized adjoint left inverse gives an actual symmetric
idempotent on the larger space. -/
theorem paired_adjoint_projection (A : E →ₗ[ℂ] F) (A' : F →ₗ[ℂ] E)
    (r : ℝ) (hr : r≠0)
    (hA : ∀ x y, inner ℂ x (A' y) = (r:ℂ)*inner ℂ (A x) y)
    (haa : ∀ x, A' (A x)=x) :
    (A.comp A').IsSymmetric ∧ IsIdempotentElem (A.comp A') := by
  constructor
  · intro x y
    have h1 := hA (A' x) y
    have h2 := congrArg (starRingEnd ℂ) (hA (A' y) x)
    simp only [map_mul,Complex.conj_ofReal,inner_conj_symm] at h2
    apply mul_left_cancel₀ (show (r:ℂ)≠0 by exact_mod_cast hr)
    exact h1.symm.trans h2
  · ext x
    change A (A' (A (A' x)))=A (A' x)
    rw [haa]

/-- The kernel of an inclusion followed by its left inverse is exactly
the kernel of the trace. -/
theorem paired_projection_kernel (A : E →ₗ[ℂ] F) (A' : F →ₗ[ℂ] E)
    (haa : ∀ x, A' (A x)=x) : (A.comp A').ker=A'.ker := by
  ext x
  change A (A' x)=0 ↔ A' x=0
  constructor
  · intro h
    have hh := congrArg A' h
    simpa only [haa,map_zero] using hh
  · intro h
    rw [h,map_zero]

#print axioms paired_adjoint_cross
#print axioms paired_adjoint_projection
#print axioms paired_projection_kernel

end QuantitativeMaass
