module

public import QuantitativeMaassTestedFriedrichsGraphV1
public import QuantitativeMaassHalfLineCauchyV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions InnerProductSpace

namespace QuantitativeMaass

/-- The position recovered from the actual Abel distribution has the actual
quotient-wave Cauchy representation, not merely an abstract bounded-operator
representation. Its initial coefficients are still to be identified. -/
theorem regularizedAbelPosition_cauchy_pairing (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (c : AutomorphicSpace N×AutomorphicSpace N)
    (hc : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)
    {a b : AutomorphicSpace N} (hab : FriedrichsGraph N a b) (t : ℝ) (ht : 0≤t) :
    inner ℂ (boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) a=
      inner ℂ (-c.2) (Wave.quotientSine N t a)+inner ℂ c.1 (Wave.shiftedQuotientWave N t a) := by
  let u := boundedCauchyPosition (regularizedShiftedGenerator N ε) c
  let v := boundedCauchyVelocity (regularizedShiftedGenerator N ε) c
  let y := fun s => Wave.boundedResolventOperator (friedrichsResolvent N) ε (u s)
  have hu (s : ℝ) (_hs : 0≤s) : HasDerivAt u (v s) s :=
    boundedCauchyPosition_hasDerivAt _ c s
  have hv (s : ℝ) (_hs : 0≤s) : HasDerivAt v ((1/4:ℂ) • u s-y s) s := by
    have he : -regularizedShiftedGenerator N ε (u s)=(1/4:ℂ) • u s-y s := by
      change -(Wave.boundedResolventOperator (friedrichsResolvent N) ε (u s)-(1/4:ℂ) • u s)=_
      abel
    rw [← he]
    exact boundedCauchyVelocity_hasDerivAt _ c s
  have hg : ∀ s,0≤s → FriedrichsGraph N (u s) (y s) :=
    regularizedAbelPosition_graph N ε hε f c hc
  have he := Wave.wave_cauchy_pairing_nonneg N u v y hu hv hg hab t ht
  have h0 := boundedCauchy_initial (regularizedShiftedGenerator N ε) c
  change u 0=c.1 ∧ v 0= -c.2 at h0
  rw [h0.1,h0.2] at he
  exact he

/-- Unconditional actual geometric-to-wave representation at each positive
regularization parameter and for every original quotient-L2 input. The
position/velocity coefficient identification remains a separate endpoint step. -/
theorem regularizedAbelDistribution_cauchy (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N) :
    ∃ c : AutomorphicSpace N×AutomorphicSpace N,
      (∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
        ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) ∧
      (∀ a b : AutomorphicSpace N,FriedrichsGraph N a b → ∀ t : ℝ,0≤t →
        inner ℂ (boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) a=
          inner ℂ (-c.2) (Wave.quotientSine N t a)+inner ℂ c.1 (Wave.shiftedQuotientWave N t a)) := by
  obtain ⟨c,hc⟩ := regularizedAbelDistribution_position_velocity N ε hε f
  have hp := fun φ => (hc φ).1
  exact ⟨c,hp,fun a b hab t ht => regularizedAbelPosition_cauchy_pairing N ε hε f c hp hab t ht⟩

#print axioms regularizedAbelPosition_cauchy_pairing
#print axioms regularizedAbelDistribution_cauchy

end QuantitativeMaass
