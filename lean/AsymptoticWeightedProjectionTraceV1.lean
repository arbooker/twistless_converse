module

public import AsymptoticLocalizedModeComparisonV1
public import AsymptoticDiagonalComparisonV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderModeComparison

open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation
open AsymptoticDiagonalTrace ContinuousLinearMap InnerProductSpace
open scoped InnerProduct

/-- The trace of an arbitrary bounded operator localized above Y and
compressed to the actual weighted holomorphic Fourier space. -/
noncomputable def localizedTrace (m t : ℕ) {scale ε : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) (Y : ℝ) (W : Space →L[ℂ] Space) : ℝ :=
  trace (fourierBasis m t hs hε)
    (compressedSandwich (upperProjection Y) W (holomorphicSpace m t hs hε))

theorem localizedTrace_eq_sum (m t : ℕ) {scale ε : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) (Y : ℝ) (W : Space →L[ℂ] Space) :
    localizedTrace m t hs hε Y W =
      ∑' n, (⟪W (upperProjection Y (unitMode m t n hs hε)),
        upperProjection Y (unitMode m t n hs hε)⟫_ℂ).re := by
  unfold localizedTrace trace
  apply tsum_congr
  intro n
  let U := holomorphicSpace m t hs hε
  let b := fourierBasis m t hs hε n
  let P := upperProjection Y
  have hPa : P.adjoint = P := AsymptoticRegionL2.projection_adjoint _ _ _
  have hu := U.subtypeL.adjoint_inner_left b (P (W (P.adjoint (b : Space))))
  change (⟪U.subtypeL.adjoint (P (W (P.adjoint (b : Space)))),b⟫_ℂ).re = _
  rw [hu, ← P.adjoint_inner_right, hPa]
  simp only [b, fourierBasis_apply, modeInSpace, P, Submodule.subtypeL_apply]

noncomputable def massBound (m t : ℕ) (scale Y : ℝ) : ℝ :=
  ((m+2*t+1 : ℕ) : ℝ)*Real.log 2/(scale*Y/2) + 1/(1-Real.exp (-(scale*Y/2)))

theorem localized_modes_summable_bound (m t : ℕ) {scale ε Y : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) (hY : 0 < Y) :
    Summable (fun n => ‖upperProjection Y (unitMode m t n hs hε)‖^2) ∧
    (∑' n, ‖upperProjection Y (unitMode m t n hs hε)‖^2) ≤ massBound m t scale Y := by
  simp only [upperProjection_unitMode_norm_sq, massBound]
  exact upperMass_summable_bound m t hs hε hY

/-- The actual localized weighted and unweighted traces differ by
O_t,Y(‖W‖ sqrt(k)). This bound applies to nonpositive operators as well as
the finite polynomial words used in the reconstruction argument. -/
theorem localizedTrace_difference_bound (m t : ℕ) {scale ε Y : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) (hY : 0 < Y) (W : Space →L[ℂ] Space) :
    ‖localizedTrace m t hs hε Y W - localizedTrace m 0 hs hε Y W‖ ≤
      ‖W‖ * Real.sqrt (localizedErrorBound t scale Y) *
        (Real.sqrt (massBound m t scale Y) + Real.sqrt (massBound m 0 scale Y)) := by
  obtain ⟨hu, hu'⟩ := localized_modes_summable_bound m t hs hε hY
  obtain ⟨hv, hv'⟩ := localized_modes_summable_bound m 0 hs hε hY
  obtain ⟨hd, hd'⟩ := localized_mode_difference_summable_bound m t hs hε hY
  simp only [map_sub] at hd hd'
  rw [localizedTrace_eq_sum, localizedTrace_eq_sum]
  exact AsymptoticDiagonalComparison.trace_difference_bound W
    (fun n => upperProjection Y (unitMode m t n hs hε))
    (fun n => upperProjection Y (unitMode m 0 n hs hε)) hu hv hd hd' hu' hv'

#print axioms localizedTrace_eq_sum
#print axioms localizedTrace_difference_bound

end AsymptoticCylinderModeComparison
