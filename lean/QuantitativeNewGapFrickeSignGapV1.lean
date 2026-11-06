module

public import QuantitativeNewGapFrickeSignV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open InnerProductSpace AsymptoticSubspaceIntersection
open scoped lp InnerProduct

theorem permutationSignSpace_projection {ι : Type*} (e : ι ≃ ι)
    (he : Function.Involutive e) (s : ℝ) (hs : s^2=1) (f : ℓ²(ι,ℂ)) :
    (permutationSignSpace e s).starProjection f=
      (1/2:ℂ) • (f+(s:ℂ) • permutationOperator e f) := by
  have hsC : (s:ℂ)*(s:ℂ)=1 := by exact_mod_cast (show s*s=1 by nlinarith)
  have hT : permutationOperator e (permutationOperator e f)=f :=
    congrArg (fun T : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ) => T f) (permutationOperator_involutive e he)
  have hsa : (permutationOperator e).adjoint=permutationOperator e :=
    (permutationOperator_selfAdjoint e he).adjoint_eq
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change permutationOperator e ((1/2:ℂ) • (f+(s:ℂ) • permutationOperator e f))-
      (s:ℂ) • ((1/2:ℂ) • (f+(s:ℂ) • permutationOperator e f))=0
    simp only [map_smul,map_add,hT,smul_add,smul_smul]
    have hc : (s:ℂ)*((1/2:ℂ)*(s:ℂ))=(1/2:ℂ) := by
      linear_combination (1/2:ℂ)*hsC
    rw [hc]
    module
  · intro g hg
    have hgT : permutationOperator e g=(s:ℂ) • g := sub_eq_zero.mp hg
    change ⟪f-(1/2:ℂ) • (f+(s:ℂ) • permutationOperator e f),g⟫_ℂ=0
    rw [inner_sub_left,inner_smul_left,inner_add_left,inner_smul_left,
      ← (permutationOperator e).adjoint_inner_right,hsa,hgT,inner_smul_right]
    have hc : (starRingEnd ℂ) (1/2:ℂ)=(1/2:ℂ) := by
      convert Complex.conj_ofReal (1/2:ℝ) using 1 <;> push_cast <;> rfl
    rw [hc,Complex.conj_ofReal]
    linear_combination -(1/2:ℂ)*⟪f,g⟫_ℂ*hsC

/-- Exact residual gap for the two signs of an actual involutive
quotient permutation. -/
theorem permutationSignSpace_gap {ι : Type*} (e : ι ≃ ι)
    (he : Function.Involutive e) (s : ℝ) (hs : s^2=1) (f : ℓ²(ι,ℂ)) :
    4*‖f-(permutationSignSpace e s).starProjection f‖^2=
      ‖permutationOperator e f-(s:ℂ) • f‖^2 := by
  rw [permutationSignSpace_projection e he s hs]
  have hsign : s=1 ∨ s=-1 := (sq_eq_one_iff).mp hs
  rcases hsign with rfl | rfl
  · simp only [Complex.ofReal_one]
    have hv : f-(1/2:ℂ) • (f+(1:ℂ) • permutationOperator e f)=
        (1/2:ℂ) • (f-permutationOperator e f) := by module
    rw [hv,norm_smul]
    simp only [Complex.norm_div,norm_one,Complex.norm_ofNat,one_smul]
    rw [norm_sub_rev f (permutationOperator e f)]
    ring
  · have hv : f-(1/2:ℂ) • (f+((-1:ℝ):ℂ) • permutationOperator e f)=
        (1/2:ℂ) • (f+permutationOperator e f) := by push_cast; module
    rw [hv,norm_smul]
    simp only [Complex.norm_div,norm_one,Complex.norm_ofNat,Complex.ofReal_neg,
      Complex.ofReal_one,neg_smul,one_smul,sub_neg_eq_add]
    rw [add_comm (permutationOperator e f) f]
    ring

/-- Quantitative global Fricke/new intersection estimate. The old
distance here is to the literal total-new space, with no angle premise. -/
theorem globalFricke_new_sign_gap (N : ℕ) (hN : 0<N) (s : ℝ) (hs : s^2=1)
    (f : ℓ²(AsymptoticNestedQuotients.Classes (AsymptoticCongruenceStrip.gamma N),ℂ)) :
    4*‖f-(inter (AsymptoticTotalNewCorner.space N hN)
      (permutationSignSpace (globalFrickeEquiv N hN) s)).starProjection f‖^2≤
      4*‖f-(AsymptoticTotalNewCorner.space N hN).starProjection f‖^2+
      ‖permutationOperator (globalFrickeEquiv N hN) f-(s:ℂ) • f‖^2 := by
  have hh := mul_le_mul_of_nonneg_left (inter_projection_distance _ _
    (globalFricke_totalNew_sign_commute N hN s) f) (show (0:ℝ)≤4 by norm_num)
  rwa [mul_add,permutationSignSpace_gap _ (globalFrickeEquiv_involutive N hN) s hs] at hh

#print axioms permutationSignSpace_projection
#print axioms permutationSignSpace_gap
#print axioms globalFricke_new_sign_gap

end QuantitativeNewGap
