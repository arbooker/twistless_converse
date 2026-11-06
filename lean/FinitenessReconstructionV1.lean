module

public import FinitenessCertificateV1

@[expose] public section

namespace FinitenessReconstruction

open FinitenessCertificate SpanningIntegerRows Matrix

variable {N Q : ℕ} {hQ : 0 < Q} {K : Type*} [Field K] [CharZero K]

theorem coordinate_cast (A : Certificate N Q hQ) (j t : Fin Q) :
    ∑ i ∈ (A.coeff j).support, (A.coeff j i : K) * (primitiveRows N hQ i t : K) =
      if t = j then 1 else 0 := by
  classical
  have h := congrArg (fun a : ℚ => (a : K)) (coordinate_identity A j t)
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, apply_ite,
    Rat.cast_one, Rat.cast_zero] using h

/-- The literal finite reconstruction identity after scalar extension. -/
theorem reconstruct_vector (A : Certificate N Q hQ) (j : Fin Q) (v : Fin Q → K) :
    ∑ i ∈ (A.coeff j).support, (A.coeff j i : K) *
      dotProduct (fun t => (primitiveRows N hQ i t : K)) v = v j := by
  classical
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ t, ∑ i ∈ (A.coeff j).support,
        (A.coeff j i : K) * ((primitiveRows N hQ i t : K) * v t)) =
        ∑ t, (∑ i ∈ (A.coeff j).support,
          (A.coeff j i : K) * (primitiveRows N hQ i t : K)) * v t := by
      simp only [Finset.sum_mul, mul_assoc]
    _ = ∑ t, (if t = j then (1 : K) else 0) * v t := by
      simp only [coordinate_cast]
    _ = v j := by simp

open SpanningCyclicCoordinates SpanningTraceAlgebra

/-- Reconstruction of any Q-periodic K-valued sequence by the actual
primitive row sums. No analytic transformation law has yet been used. -/
theorem reconstruct_periodic (A : Certificate N Q hQ) (j : Fin Q) (v : ℤ → K)
    (hv : Cyclic Q v) :
    ∑ i ∈ (A.coeff j).support, (A.coeff j i : K) *
      primitive i.val.1 (Q / i.val.1) v i.val.2 = v j := by
  have h := reconstruct_vector A j (coordinates v)
  have he := extend_coordinates hQ hv
  simpa only [primitiveRows, primitiveRow_eval, he, coordinates] using h

#print axioms reconstruct_periodic

end FinitenessReconstruction
