module

public import AsymptoticFiniteUpperRetainedLimitV1
public import AsymptoticRegularRetainedTraceV1
public import AsymptoticUpperCutTraceReductionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticSharedApproximation

open UpperHalfPlane MeasureTheory Set Filter
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount (Row)
open scoped Topology

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The fixed finite cutoff word limit for the actual weighted cylinder
and regular observation operators. -/
theorem finiteUpperCut_trace_limit (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (e : Sector N) {Y : ℝ} (hY : 0<Y) (H : ℝ) (n d : ℕ) (I : Finset ℤ) :
    Tendsto (fun h : ℕ =>
      AsymptoticCylinderObservation.finiteUpperCutPolynomialTrace A hN P r s hs h e Y H n d I/(2*h+2:ℕ))
      atTop (𝓝 (AsymptoticRegularObservation.finiteUpperCutPolynomialTrace A hN P r s hs e Y H n d I/(4*Real.pi))) := by
  rw [AsymptoticFiniteBranch.regular_finiteUpperCut_trace_eq_retained]
  exact AsymptoticFiniteBranch.finiteUpperCut_trace_tendsto_retained A hN P r s hs e hY H n d I

/-- The uncut fixed-observation large-weight trace limit, with its finite
word premise discharged by the concrete branch kernel calculation. -/
theorem holomorphic_trace_limit (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    Tendsto (fun h : ℕ => AsymptoticCylinderObservation.holomorphicTrace A hN P r s hs h e/(2*h+2:ℕ))
      atTop (𝓝 ((AsymptoticRegularTrace.trace volume
        (AsymptoticRegularObservation.positive A hN P r s hs e)).toReal/(4*Real.pi))) := by
  apply holomorphic_trace_limit_of_upper_cut_words A hN P r s hs _ e
  intro Y hY _ H _ n d I e
  exact finiteUpperCut_trace_limit A hN P r s hs e hY H n d I

#print axioms finiteUpperCut_trace_limit
#print axioms holomorphic_trace_limit

end AsymptoticSharedApproximation
