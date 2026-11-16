module

public import QuantitativeMaassQuotientWeightPlaneV1
public import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

open Set UpperHalfPlane AsymptoticCongruenceWeight

namespace QuantitativeMaass

theorem quotientWeightPlane_nonneg (N : ℕ) (ε : ℝ) (v : ℕ) (Z : ℝ×ℝ) :
    0≤quotientWeightPlane N ε v Z := by
  unfold quotientWeightPlane
  split_ifs with h
  · unfold weight
    exact tsum_nonneg (fun _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
  · exact le_rfl

theorem quotientWeightPlane_le (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (Z : ℝ×ℝ) :
    quotientWeightPlane N ε v Z≤quotientWeightBound ε := by
  unfold quotientWeightPlane
  split_ifs with h
  · exact quotientWeight_uniform_bound N hε hv _
  · exact quotientWeightBound_nonneg ε

/-- Above any positive height the literal orbit weight agrees with a
bounded globally Lipschitz function on the coordinate plane. This is used
only to smooth compact seeds; it is not an invariant smooth replacement. -/
theorem quotientWeight_bounded_extension (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) {r : ℝ} (hr : 0<r) :
    ∃ (K : NNReal) (b : (ℝ×ℝ) → ℝ),LipschitzWith K b ∧
      (∀ Z,0≤b Z ∧ b Z≤quotientWeightBound ε) ∧
      EqOn b (quotientWeightPlane N ε v) {Z : ℝ×ℝ | r<Z.2} := by
  obtain ⟨b,hb,he⟩ := (quotientWeightPlane_lipschitzOn N hε hv hr).extend_real
  refine ⟨_,fun Z => min (quotientWeightBound ε) (max 0 (b Z)),
    (hb.const_max 0).const_min (quotientWeightBound ε),?_,?_⟩
  · intro Z
    exact ⟨le_min (quotientWeightBound_nonneg ε) (le_max_left _ _),min_le_left _ _⟩
  · intro Z hZ
    change min (quotientWeightBound ε) (max 0 (b Z))=quotientWeightPlane N ε v Z
    rw [←he hZ,max_eq_right (quotientWeightPlane_nonneg N ε v Z),
      min_eq_right (quotientWeightPlane_le N hε hv Z)]

#print axioms quotientWeightPlane_nonneg
#print axioms quotientWeightPlane_le
#print axioms quotientWeight_bounded_extension

end QuantitativeMaass
