module

public import AsymptoticFiberCompressionV1
public import AsymptoticCongruenceOldTraceV1
public import AsymptoticCongruenceCovolumeV1
public import AsymptoticQuotientProductBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceQuotient

open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticRegularTrace
open scoped lp ComplexConjugate ENNReal

variable (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)

/-- Transport a fixed coset-space operator to the normalized strip model. -/
noncomputable def compression (B : ℓ²(Classes N,ℂ) →L[ℂ] ℓ²(Classes N,ℂ)) (z : ℍ) :
    ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  ((induction N hε ht z).toContinuousLinearMap.comp B).comp
    (induction N hε ht z).toContinuousLinearMap.adjoint

theorem compression_matrix (B : ℓ²(Classes N,ℂ) →L[ℂ] ℓ²(Classes N,ℂ))
    (z : ℍ) (g k : AsymptoticRationalGroup.Group) :
    matrix (compression N hε ht B z) g k=
      amplitude N ε t (g • z)*conj (amplitude N ε t (k • z))*
        matrix B (classOf N g) (classOf N k) :=
  AsymptoticFiberIsometry.compression_matrix (classOf N)
    (fun g => amplitude N ε t (g • z)) (fibre_amplitude_hasSum N hε ht z) B g k

theorem compression_diagonal (B : ℓ²(Classes N,ℂ) →L[ℂ] ℓ²(Classes N,ℂ))
    (z : ℍ) (g : AsymptoticRationalGroup.Group) :
    (matrix (compression N hε ht B z) g g).re=
      (matrix (projection N hε ht z) g g).re*(matrix B (classOf N g) (classOf N g)).re := by
  rw [compression_matrix,projection_matrix]
  simp [Complex.mul_conj,Complex.mul_re]

/-- The strip trace of a positive rooted coefficient is exactly its
coset coefficient times the quotient covolume. -/
theorem compression_trace (B : ℓ²(Classes N,ℂ) →L[ℂ] ℓ²(Classes N,ℂ))
    (hB : 0≤(matrix B (classOf N 1) (classOf N 1)).re) :
    trace volume (compression N hε ht B)=
      ENNReal.ofReal (matrix B (classOf N 1) (classOf N 1)).re*
        trace volume (projection N hε ht) := by
  simp only [trace,compression_diagonal]
  simp_rw [mul_comm _ (matrix B (classOf N 1) (classOf N 1)).re,ENNReal.ofReal_mul hB]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem compression_trace_covolume (hN : 0<N)
    (B : ℓ²(Classes N,ℂ) →L[ℂ] ℓ²(Classes N,ℂ))
    (hB : 0≤(matrix B (classOf N 1) (classOf N 1)).re) :
    trace volume (compression N hε ht B)=
      ENNReal.ofReal (matrix B (classOf N 1) (classOf N 1)).re*
        ((gamma N).relIndex (gamma 1)*ENNReal.ofReal (Real.pi/3)) := by
  rw [compression_trace N hε ht B hB,projection_trace_covolume N hN hε ht]

#print axioms compression_matrix
#print axioms compression_diagonal
#print axioms compression_trace
#print axioms compression_trace_covolume

end AsymptoticCongruenceQuotient
