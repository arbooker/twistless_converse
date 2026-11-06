module

public import QuantitativeHolomorphicCompactCoordinatesV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane MeasureTheory AsymptoticRationalFreeness
open AsymptoticCompactBranch AsymptoticFiniteBranch

/-- An explicit observation datum from matrix entries and input-region
coordinates. No compactness choice enters the fold cutoff or weight bound. -/
def matrixCompactData (g : GL (Fin 2) ℝ) (hg : 0<g.det.val)
    (s : Set UpperHalfPlane) {B R η ε : ℝ}
    (hB : 0<B) (hR : 0≤R) (hη : 0<η) (hε : 0<ε)
    (hentries : ∀ i j, |g i j|≤B)
    (hz : ∀ z∈s, ‖(z:ℂ)‖≤R) (hzi : ∀ z∈s, η≤z.im) (t : ℕ) :
    Data g s ε t :=
  imageBoundedCompactData g s hε (by positivity : 0<g.det.val*η/(B*(R+1))^2) t
    ⌈B*(R+1)/compactDenominatorLower g η⌉₊
    (fun z hs => ((compact_image_coordinates g hg hB hR hη hentries z (hz z hs) (hzi z hs)).1).trans
      (Nat.le_ceil _))
    (fun z hs => (compact_image_coordinates g hg hB hR hη hentries z (hz z hs) (hzi z hs)).2)

/-- Exact physical replacement of the original compact observation by any
explicit datum satisfying its concrete fold and ratio fields. -/
theorem compactExpression_physical_replacement (g : GL (Fin 2) ℚ)
    (hg : 0<(realMatrix g).det.val) {s : Set UpperHalfPlane} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) (D : Data (realMatrix g) s ε t) :
    holomorphicSum (compactExpression g hg hs.measurableSet hε t D) m =
      holomorphicSum (compactExpression g hg hs.measurableSet hε t
        (data (realMatrix g) hs hε t)) m := by
  rw [holomorphicSum_compactExpression, holomorphicSum_compactExpression]
  exact physical_compact_data_independent (realMatrix g) hs.measurableSet hε t D _ m

/-- The same replacement is exact for the regular orbit operator. -/
theorem compactExpression_regular_replacement (g : GL (Fin 2) ℚ)
    (hg : 0<(realMatrix g).det.val) {s : Set UpperHalfPlane} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t) (z : UpperHalfPlane) :
    regularSum (compactExpression g hg hs.measurableSet hε t D) z =
      regularSum (compactExpression g hg hs.measurableSet hε t
        (data (realMatrix g) hs hε t)) z := by
  rw [regularSum_compactExpression, regularSum_compactExpression]
  exact regular_compact_data_independent g hg hε t D _ z

/-- Both the number of branches and their coefficient mass are explicit
for bounded compact data. These are the quantities needed by the trace
estimate, separately from the matrix-height certificate. -/
theorem boundedCompactExpression_complexity (g : GL (Fin 2) ℚ)
    (hg : 0<(realMatrix g).det.val) {s : Set UpperHalfPlane} (hs : MeasurableSet s)
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) (t J : ℕ)
    (hre : ∀ z∈s, |(realMatrix g • z).re| ≤ J)
    (him : ∀ z∈s, η ≤ (realMatrix g • z).im) :
    let E := compactExpression g hg hs hε t
      (imageBoundedCompactData (realMatrix g) s hε hη t J hre him)
    E.length = 2*J+1 ∧ expressionBound E = (2*(J:ℝ)+1)*((min (η/ε) 1)^t)⁻¹ := by
  dsimp only
  constructor
  · rw [compactExpression, length_composeExpression]
    simpa [compactRawExpression, ofFinset] using
      imageBoundedCompactData_card (realMatrix g) s hε hη t J hre him
  · rw [compactExpression, expressionBound_compose]
    simp only [compactRawExpression, expressionBound, ofFinset, List.map_map,
      Function.comp_def, compactFold, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, corner, add_zero, mul_one]
    rw [Finset.sum_map_toList]
    simp only [Finset.sum_const, nsmul_eq_mul, imageBoundedCompactData_card]
    push_cast
    rfl

#print axioms matrixCompactData
#print axioms compactExpression_physical_replacement
#print axioms compactExpression_regular_replacement
#print axioms boundedCompactExpression_complexity

end QuantitativeHolomorphic
