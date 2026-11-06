module

public import AsymptoticQuotientSupportV1
public import AsymptoticRegularSignedTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticQuotientOperators

open AsymptoticNestedQuotients AsymptoticRegularTrace ContinuousLinearMap InnerProductSpace
open scoped lp InnerProduct

variable {G : Type*} [Group G] {H S T : Subgroup G}

/-- Separation kills every off-diagonal summand when a T-supported
operator acts on a column supported in S. -/
theorem separated_column (hS : H≤S) (hT : H≤T) (hST : S⊓T≤H)
    (B A : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ))
    (hB : Supported hS B) (hA : Supported hT A)
    (c : ℂ) (hdiag : ∀ q,matrix A q q=c) (g : G) (hg : g∈S) :
    matrix (A.comp B) (classOf H g) (classOf H 1)=
      c*matrix B (classOf H g) (classOf H 1) := by
  classical
  rw [matrix_comp,tsum_eq_single (classOf H g)]
  · rw [hdiag]
  · intro q hq
    have heq : classOf H q.out=q := q.out_eq
    by_cases hqS : q.out∈S
    · have hnot : g*q.out⁻¹∉T := by
        intro ht
        have hh := hST ⟨S.mul_mem hg (S.inv_mem hqS),ht⟩
        have he := (classOf_eq_iff H g q.out).mpr hh
        rw [heq] at he
        exact hq he.symm
      have hz : matrix A (classOf H g) q=0 := by
        rw [← heq]
        exact (supported_iff hT A).mp hA g q.out hnot
      rw [hz,zero_mul]
    · have hz : matrix B q (classOf H 1)=0 := by
        rw [← heq]
        apply (supported_iff hS B).mp hB q.out 1
        simpa only [inv_one,mul_one] using hqS
      rw [hz,mul_zero]

/-- A positive sandwich has a factored rooted coefficient under
subgroup separation. No commutation between A and B is assumed. -/
theorem separated_sandwich (hS : H≤S) (hT : H≤T) (hST : S⊓T≤H)
    (B A : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ))
    (hB : Supported hS B) (hA : Supported hT A)
    (c : ℂ) (hdiag : ∀ q,matrix A q q=c) :
    matrix (B.adjoint.comp (A.comp B)) (classOf H 1) (classOf H 1)=
      c*((‖B (delta (classOf H 1))‖^2:ℝ):ℂ) := by
  rw [matrix_cross,lp.inner_eq_tsum]
  have he (q : Classes H) :
      ⟪B (delta (classOf H 1)) q,(A.comp B) (delta (classOf H 1)) q⟫_ℂ=
        c*⟪B (delta (classOf H 1)) q,B (delta (classOf H 1)) q⟫_ℂ := by
    have heq : classOf H q.out=q := q.out_eq
    by_cases hqS : q.out∈S
    · have hh := separated_column hS hT hST B A hB hA c hdiag q.out hqS
      rw [heq] at hh
      change matrix (A.comp B) q (classOf H 1)=c*matrix B q (classOf H 1) at hh
      change ⟪matrix B q (classOf H 1),matrix (A.comp B) q (classOf H 1)⟫_ℂ=_
      rw [hh]
      simp only [RCLike.inner_apply, matrix]
      ring
    · have hz : B (delta (classOf H 1)) q=0 := by
        change matrix B q (classOf H 1)=0
        rw [← heq]
        apply (supported_iff hS B).mp hB q.out 1
        simpa only [inv_one,mul_one] using hqS
      rw [hz,inner_zero_left,inner_zero_left,mul_zero]
  simp_rw [he]
  rw [tsum_mul_left,← lp.inner_eq_tsum,inner_self_eq_norm_sq_to_K]
  simp only [Complex.ofReal_pow]
  rfl

#print axioms separated_column
#print axioms separated_sandwich

end AsymptoticQuotientOperators
