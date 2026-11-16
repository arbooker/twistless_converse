module

public import QuantitativeMaassCombinedFilterScheduleV1
public import QuantitativeMaassGeometricLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter QuantitativeHolomorphic
open scoped Topology
namespace QuantitativeMaass

/-- The actual local-filter and Newton word degrees, together with any
fixed fourth-root reconstruction cost, still occupy a negligible geometric
radius. All schedules are explicit. -/
theorem combinedFilter_geometry_radius_sublinear (D W : ℝ) :
    Tendsto (fun t => (D*((growingMomentDegree t:ℝ)+1)*
      (((inverseSqrtPolynomial (bandNewtonDepth t)).natDegree:ℝ)+1)+
      W*fourthRootScale t)/30/slowScale t) atTop (𝓝 0) := by
  have hh := ((growingMomentDegree_newton_degree_sublinear.const_mul D).add
    (fourthRootScale_div_scale.const_mul W)).div_const 30
  simp only [mul_zero,add_zero,zero_div] at hh
  apply hh.congr
  intro t
  ring

/-- Exponential costs of the actual composed filter/Newton word degrees
are absorbed by the square-root spectral saving under the original width
condition. This is a bound on the explicit geometric majorant, not an
assumption or assertion about the unresolved physical residual trace. -/
theorem combinedFilter_geometric_majorant_tendsto
    (ε : ℝ → ℝ) (A C D W : ℝ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hW : 0≤W)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => C*Real.sqrt t*(ε t)^2*
      Real.exp (A*positiveWindowRadius ε t+
        D*((growingMomentDegree t:ℝ)+1)*
          (((inverseSqrtPolynomial (bandNewtonDepth t)).natDegree:ℝ)+1)+
        W*fourthRootScale t)/(t*ε t)) atTop (𝓝 0) := by
  let L := fun t => (D*((growingMomentDegree t:ℝ)+1)*
      (((inverseSqrtPolynomial (bandNewtonDepth t)).natDegree:ℝ)+1)+
      W*fourthRootScale t)/30
  have hLp : ∀ᶠ t in atTop,0≤L t := by
    filter_upwards [] with t
    dsimp only [L]
    have hw : 0≤fourthRootScale t := by unfold fourthRootScale; positivity
    positivity
  have hh := geometric_majorant_tendsto ε (positiveWindowRadius ε) L A C hA hC hε
    (Eventually.of_forall (fun t => (positiveWindowRadius_pos ε t).le)) hLp
    (positiveWindowRadius_div_scale ε (hε.mono (fun _ h => h.1)) hproduct)
    (combinedFilter_geometry_radius_sublinear D W)
  apply hh.congr
  intro t
  rw [show A*positiveWindowRadius ε t+30*L t=
      A*positiveWindowRadius ε t+D*((growingMomentDegree t:ℝ)+1)*
        (((inverseSqrtPolynomial (bandNewtonDepth t)).natDegree:ℝ)+1)+
      W*fourthRootScale t by dsimp only [L]; ring]

#print axioms combinedFilter_geometry_radius_sublinear
#print axioms combinedFilter_geometric_majorant_tendsto
end QuantitativeMaass
