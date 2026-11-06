module

public import AsymptoticCylinderInversePolynomialV1
public import AsymptoticGramTracePerturbationV1
public import AsymptoticCylinderCutTraceErrorV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderObservation

open UpperHalfPlane Set ContinuousLinearMap Filter
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticObservation AsymptoticReconstructedCount AsymptoticCoerciveNeumann
open AsymptoticDiagonalTrace AsymptoticFourierNorm
open AsymptoticCompactObservationCount (Row)
open scoped Topology

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Replace only the cutoff normalization inverse by its finite
polynomial, keeping the actual reconstruction and Fourier projection. -/
noncomputable def cutPolynomialTrace (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N) (Y : ℝ) (n : ℕ) : ℝ :=
  trace (fourierBasis (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi) (parameters A P).epsilon_pos)
    (compressedSandwich (cutReconstruction A hN P h e Y) (cutInversePolynomial A hN P r s hs h e Y n)
      (holomorphicSpace (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi) (parameters A P).epsilon_pos))

/-- The actual inverse-polynomial approximation costs O(delta*k), with
all constants independent of weight, sector and polynomial degree. -/
theorem cutPolynomialTrace_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY : Y≤(parameters A P).ε) (n : ℕ) :
    ‖cutPolynomialTrace A hN P r s hs h e Y n-cutHolomorphicTrace A hN P r s hs h e Y hY‖≤
      polynomialError (AsymptoticSharedApproximation.normalBound A hN P r s hs) n*
        (1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P))^2*
        (1+majorantConstant ((parameters A P).s+4) (4*Real.pi) (parameters A P).ε)*(2*h+2:ℕ) :=
  compressedSandwich_trace_error (cutReconstruction A hN P h e Y)
    (cutInversePolynomial A hN P r s hs h e Y n) (cutTerminalInverse A hN P r s hs h e Y hY)
    (holomorphicSpace (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi) (parameters A P).epsilon_pos)
    (fourierBasis (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi) (parameters A P).epsilon_pos)
    (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi) (parameters A P).epsilon_pos (sq_nonneg _)
    (cutReconstruction_fourier_gram A hN P h e Y (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi))
    (cutInversePolynomial_error A hN P r s hs h e Y hY n)

/-- Polynomial degree is fixed before the weight limit: normalized
traces converge uniformly over every weight and sector. -/
theorem cutPolynomialTrace_tendstoUniformly (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℝ) (hY : Y≤(parameters A P).ε) :
    TendstoUniformly
      (fun n (he : ℕ × Sector N) => cutPolynomialTrace A hN P r s hs he.1 he.2 Y n/(2*he.1+2:ℕ))
      (fun he : ℕ × Sector N => cutHolomorphicTrace A hN P r s hs he.1 he.2 Y hY/(2*he.1+2:ℕ)) atTop := by
  let BR := 1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P)
  let K := majorantConstant ((parameters A P).s+4) (4*Real.pi) (parameters A P).ε
  have hd : Tendsto (fun n => polynomialError (AsymptoticSharedApproximation.normalBound A hN P r s hs) n*BR^2*(1+K)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ((polynomialError_tendsto_zero (AsymptoticSharedApproximation.normalBound A hN P r s hs)).mul_const (BR^2)).mul_const (1+K)
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  apply ((tendsto_order.mp hd).2 δ hδ).mono
  intro n hn he
  have hk : (0:ℝ)<(2*he.1+2:ℕ) := by positivity
  rw [dist_eq_norm,← sub_div,norm_div,Real.norm_of_nonneg hk.le,norm_sub_rev]
  have hb := div_le_div_of_nonneg_right (cutPolynomialTrace_error A hN P r s hs he.1 he.2 Y hY n) hk.le
  rw [mul_div_cancel_right₀ _ hk.ne'] at hb
  exact hb.trans_lt hn

#print axioms cutPolynomialTrace_error
#print axioms cutPolynomialTrace_tendstoUniformly

end AsymptoticCylinderObservation
