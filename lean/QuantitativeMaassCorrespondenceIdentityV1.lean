module

public import QuantitativeMaassCorrespondenceWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open scoped Topology ENNReal

namespace QuantitativeMaass

attribute [local instance] Classical.propDecidable

/-- At most one projective congruence element makes a fixed positive
integral correspondence scalar. -/
theorem integralProduct_scalar_unique (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : 0<M.det) (γ η : gamma N)
    (hγ : ¬integralProductNonscalar N M γ)
    (hη : ¬integralProductNonscalar N M η) : γ=η := by
  have he (z : ℍ) : γ•z=η•z := by
    have h1 := congruence_product_fixed_of_scalar N M hM γ hγ
      ((positiveIntegralGL M hM)⁻¹•z)
    have h2 := congruence_product_fixed_of_scalar N M hM η hη
      ((positiveIntegralGL M hM)⁻¹•z)
    simpa only [smul_inv_smul] using h1.trans h2.symm
  have hi : γ⁻¹*η=1 := by
    apply Subtype.ext
    apply QuantitativeHolomorphic.rational_label_eq_one_of_fixed
    intro z
    change (γ⁻¹*η)•z=z
    rw [mul_smul,← he z,inv_smul_smul]
  exact inv_mul_eq_one.mp hi

/-- Concrete identity-coset test for a positive integral correspondence. -/
def integralIdentityCoset (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∃ γ : gamma N,¬integralProductNonscalar N M γ

/-- A scalar product belongs to every nonnegative propagation truncation
at any point of its localization ball. -/
theorem integralProduct_scalar_mem_orbit (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : 0<M.det) (γ : gamma N) (hγ : ¬integralProductNonscalar N M γ)
    (o x : ℍ) (L R : ℝ) (hx : dist x o≤L) (hR : 0≤R) :
    γ∈diagonalOrbitSet N o (R+2*L+dist (positiveIntegralGL M hM • o) o) := by
  apply correspondence_displacement_in_diagonalOrbitSet N M hM o x L R hx
  rw [congruence_product_fixed_of_scalar N M hM γ hγ x,dist_self]
  exact hR

/-- The finite scalar sum is exactly one identity contribution or zero.
There is no truncation-dependent multiplicity in the main term. -/
theorem integralProduct_scalar_sum (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : 0<M.det) (c : ℂ) (o x : ℍ) (L R : ℝ)
    (hx : dist x o≤L) (hR : 0≤R) :
    (∑ γ∈diagonalOrbitSet N o (R+2*L+dist (positiveIntegralGL M hM • o) o),
      if integralProductNonscalar N M γ then 0 else c)=
      if integralIdentityCoset N M then c else 0 := by
  by_cases h : integralIdentityCoset N M
  · rw [ite_eq_left h]
    obtain ⟨γ,hγ⟩ := h
    rw [Finset.sum_eq_single γ]
    · exact ite_eq_right hγ
    · intro η _ hne
      apply ite_eq_left
      by_contra hη
      exact hne (integralProduct_scalar_unique N M hM η γ hη hγ)
    · intro hnot
      exact (hnot (integralProduct_scalar_mem_orbit N M hM γ hγ o x L R hx hR)).elim
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro γ _
    apply ite_eq_left
    by_contra hγ
    exact h ⟨γ,hγ⟩

/-- Global correspondence split with the actual, arithmetic identity-coset
indicator and the genuine nonscalar remainder. -/
theorem radialIntegralKernel_identity_split (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) (x : ℍ) :
    radialPoincareKernel N g x (positiveIntegralGL M hM • x)=
      (if integralIdentityCoset N M then g 1 else 0)+radialIntegralRemainder N M hM g x := by
  rw [radialIntegralKernel_scalar_split N M hM g R hR hs x x 0 (by simp),
    integralProduct_scalar_sum N M hM (g 1) x x 0 R (by simp) hR]

#print axioms integralProduct_scalar_unique
#print axioms integralProduct_scalar_mem_orbit
#print axioms integralProduct_scalar_sum
#print axioms radialIntegralKernel_identity_split

end QuantitativeMaass
