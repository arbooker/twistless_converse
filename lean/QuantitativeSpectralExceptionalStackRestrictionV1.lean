module

public import QuantitativeSpectralExceptionalQuotientPolynomialV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane ContinuousLinearMap AsymptoticObservationStack AsymptoticOrbitDiagonal
open QuantitativeSpectralExceptionalUnweight (G Space)
open scoped MatrixGroups lp

abbrev EnlargedData (J : Type*) (A : Finset SL(2,ℤ)) := PiLp 2 (fun _ : J ⊕ ↥A => Space)

/-- Select one rational row and all generator rows, restricting their
outputs to the two compact regions used by the actual factorization. -/
def stackRestriction {J : Type*} [Fintype J] (A : Finset SL(2,ℤ))
    (j : J) (s u : Set ℍ) (x : ℍ) : EnlargedData J A →L[ℂ] GeneratorData A :=
  stack (fun o : Option ↥A => match o with
    | none => (corner s x).comp (PiLp.proj 2 (fun _ : J ⊕ ↥A => Space) (Sum.inl j))
    | some a => (corner u x).comp (PiLp.proj 2 (fun _ : J ⊕ ↥A => Space) (Sum.inr a)))

/-- Restricting outputs and discarding unselected rational rows loses no
norm factor, independently of the number of pieces or generators. -/
theorem stackRestriction_norm {J : Type*} [Fintype J] (A : Finset SL(2,ℤ))
    (j : J) (s u : Set ℍ) (x : ℍ) : ‖stackRestriction A j s u x‖≤1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  simp only [stackRestriction,stack_apply,comp_apply,PiLp.proj_apply,
    Fintype.sum_option,Fintype.sum_sum_type]
  have hs : ‖corner s x (v (Sum.inl j))‖^2≤‖v (Sum.inl j)‖^2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    simpa only [one_mul] using (corner s x).le_of_opNorm_le
      (AsymptoticOrbitRegion.corner_norm_le _ _) (v (Sum.inl j))
  have hu : (∑ a : ↥A, ‖corner u x (v (Sum.inr a))‖^2)≤
      ∑ a : ↥A, ‖v (Sum.inr a)‖^2 := by
    apply Finset.sum_le_sum
    intro a _
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    simpa only [one_mul] using (corner u x).le_of_opNorm_le
      (AsymptoticOrbitRegion.corner_norm_le _ _) (v (Sum.inr a))
  have hj : ‖v (Sum.inl j)‖^2≤∑ k : J, ‖v (Sum.inl k)‖^2 :=
    Finset.single_le_sum (f := fun k : J => ‖v (Sum.inl k)‖^2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  linarith

#print axioms stackRestriction_norm

end QuantitativeSpectralExceptionalReducedRows
