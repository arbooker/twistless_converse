module

public import QuantitativeMaassPowerFilterExcessTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeMaass

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
/-- Cyclicity transfers the finite polynomial between a Gram operator and
its cogram. No assertion about an infinite ambient identity trace is used. -/
theorem cyclic_power_filter (τ : 𝔄→L[ℝ]ℝ)
    (hc : ∀ a b, τ (a*b)=τ (b*a)) (A B : 𝔄) (m : ℕ) :
    τ (1-(1-A*B)^m)=τ (1-(1-B*A)^m) := by
  have hi (n : ℕ) : (1-A*B)^n*A=A*(1-B*A)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        (1-A*B)^n*(1-A*B)*A = (1-A*B)^n*A*(1-B*A) := by noncomm_ring
        _ = A*(1-B*A)^n*(1-B*A) := by rw [ih]
        _ = A*((1-B*A)^n*(1-B*A)) := mul_assoc _ _ _
  have step (X : 𝔄) (n : ℕ) :
      1-(1-X)^(n+1)=(1-(1-X)^n)+(1-X)^n*X := by
    rw [pow_succ]
    noncomm_ring
  induction m with
  | zero => simp
  | succ m ih =>
    rw [step, step, map_add, map_add, ih]
    congr 1
    rw [←mul_assoc, hi, mul_assoc A, hc A ((1-B*A)^m*B)]
    simp only [mul_assoc]

/-- A contraction can move a canonical projection without increasing the
trace of any positive power filter beyond its original dimension. -/
theorem conjugated_projection_filter_trace (τ : 𝔄→L[ℝ]ℝ) (hm : Monotone τ)
    (hc : ∀ a b,τ (a*b)=τ (b*a)) (S E : 𝔄)
    (hS : ‖S‖≤1) (hE : IsStarProjection E) (m : ℕ) :
    τ (1-(1-S*E*star S)^m)≤τ E := by
  have hn : ‖star S*S‖≤1 := by
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg S]
  have hSS : star S*S≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg S)).mp hn
  have hG0 : 0≤E*(star S*S)*E := by
    simpa only [hE.isSelfAdjoint.star_eq] using
      star_left_conjugate_nonneg (star_mul_self_nonneg S) E
  have hGE : E*(star S*S)*E≤E := by
    simpa only [hE.isSelfAdjoint.star_eq,mul_one,hE.isIdempotentElem.eq] using
      star_left_conjugate_le_conjugate hSS E
  have ht := cyclic_power_filter τ hc (S*E) (E*star S) m
  have he : S*E*(E*star S)=S*E*star S := by
    simp only [mul_assoc,←mul_assoc E E,hE.isIdempotentElem.eq]
  have he' : E*star S*(S*E)=E*(star S*S)*E := by simp only [mul_assoc]
  rw [he,he'] at ht
  rw [ht]
  exact hm (positive_power_filter_minorant _ E hG0 (hGE.trans hE.le_one) hE hGE m)

#print axioms cyclic_power_filter
#print axioms conjugated_projection_filter_trace
end QuantitativeMaass
