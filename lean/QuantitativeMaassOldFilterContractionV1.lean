module

public import QuantitativeMaassTwoProjectionSpectrumV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem symmetric_idempotent_complement (P : E →ₗ[ℂ] E)
    (hPP : IsIdempotentElem P) : IsIdempotentElem (1-P) := by
  change (1-P)*(1-P)=1-P
  simp only [mul_sub,sub_mul,one_mul,mul_one,show P*P=P from hPP]
  abel

/-- The old-space filter is a contraction for every degree, even when
the two old projections do not commute. -/
theorem two_projection_filter_pointwise (P Q : E →ₗ[ℂ] E)
    (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hPP : IsIdempotentElem P) (hQQ : IsIdempotentElem Q) (m : ℕ) (v : E) :
    ‖((1-(1/2:ℂ) • (P+Q))^m) v‖ ≤ ‖v‖ := by
  have hb (x : E) : ‖(1-(1/2:ℂ) • (P+Q)) x‖ ≤ ‖x‖ := by
    have he : (1-(1/2:ℂ) • (P+Q)) x=(1/2:ℂ) • ((1-P) x+(1-Q) x) := by
      simp only [LinearMap.sub_apply,Module.End.one_apply,LinearMap.smul_apply,LinearMap.add_apply]
      module
    have hp := symmetric_idempotent_norm_le (1-P) (LinearMap.IsSymmetric.one.sub hP)
      (symmetric_idempotent_complement P hPP) x
    have hq := symmetric_idempotent_norm_le (1-Q) (LinearMap.IsSymmetric.one.sub hQ)
      (symmetric_idempotent_complement Q hQQ) x
    rw [he,norm_smul]
    have hc : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
    rw [hc]
    nlinarith [norm_add_le ((1-P) x) ((1-Q) x)]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ',Module.End.mul_apply]
    exact (hb _).trans ih

theorem two_projection_filter_norm [FiniteDimensional ℂ E] (P Q : E →ₗ[ℂ] E)
    (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hPP : IsIdempotentElem P) (hQQ : IsIdempotentElem Q) (m : ℕ) :
    ‖((1-(1/2:ℂ) • (P+Q))^m).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [one_mul,LinearMap.coe_toContinuousLinearMap'] using two_projection_filter_pointwise P Q hP hQ hPP hQQ m v

#print axioms symmetric_idempotent_complement
#print axioms two_projection_filter_pointwise
#print axioms two_projection_filter_norm

end QuantitativeMaass
