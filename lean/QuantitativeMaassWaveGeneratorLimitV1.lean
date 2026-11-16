module

public import QuantitativeMaassWaveGeneratorCFCV1
public import QuantitativeMaassWaveGeneratorCoreV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Second difference quotient with the graph-core parametrization fixed. -/
def rangeSecondDifference (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  (2/t^2 : ℝ) • ((rangeCosine A t-1)*A*A)

/-- Operator-norm generator convergence on the twice-resolvent graph core.
The punctured limit is essential because the difference quotient at zero
uses the totalized real inverse. -/
theorem rangeGeneratorError_tendsto (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (hd : DenseRange A) :
    Tendsto (rangeGeneratorError A) (𝓝[≠] 0) (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact rangeGeneratorError_norm_le A hp hn hd ht
  · have h : Continuous (fun t : ℝ => 6*t^2) := by fun_prop
    simpa using (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))

theorem rangeSecondDifference_tendsto (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (hd : DenseRange A) :
    Tendsto (rangeSecondDifference A) (𝓝[≠] 0) (𝓝 (-(A-A*A))) := by
  have h := (rangeGeneratorError_tendsto A hp hn hd).sub_const (A-A*A)
  have h' : Tendsto (fun t => rangeGeneratorError A t-(A-A*A)) (𝓝[≠] 0)
      (𝓝 (-(A-A*A))) := by simpa only [zero_sub] using h
  apply h'.congr'
  filter_upwards with t
  exact add_sub_cancel_right (rangeSecondDifference A t) (A-A*A)

theorem quotientGeneratorError_tendsto (N : ℕ) :
    Tendsto (rangeGeneratorError (friedrichsResolvent N)) (𝓝[≠] 0) (𝓝 0) :=
  rangeGeneratorError_tendsto _ (friedrichsResolvent_isPositive N)
    (friedrichsResolvent_opNorm_le N) (friedrichsResolvent_denseRange N)

theorem quotientWave_secondDifference_tendsto (N : ℕ) :
    Tendsto (rangeSecondDifference (friedrichsResolvent N)) (𝓝[≠] 0)
      (𝓝 (-(friedrichsResolvent N-friedrichsResolvent N*friedrichsResolvent N))) :=
  rangeSecondDifference_tendsto _ (friedrichsResolvent_isPositive N)
    (friedrichsResolvent_opNorm_le N) (friedrichsResolvent_denseRange N)

/-- Every vector in this graph core has the asserted actual differential
partner in the constructed quotient self-adjoint graph. -/
theorem twiceResolvent_laplacian (N : ℕ) (v : AutomorphicSpace N) :
    FriedrichsGraph N (friedrichsResolvent N (friedrichsResolvent N v))
      ((friedrichsResolvent N-friedrichsResolvent N*friedrichsResolvent N) v) :=
  friedrichsGraph_resolvent N (friedrichsResolvent N v)

#print axioms quotientWave_secondDifference_tendsto
#print axioms twiceResolvent_laplacian
#print axioms twiceResolvent_graph_core

end QuantitativeMaass.Wave
