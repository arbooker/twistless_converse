module

public import QuantitativeMaassQuotientWeightRegularityV1
public import QuantitativeMaassUniformQuotientWeightV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

open UpperHalfPlane AsymptoticCongruenceWeight

namespace QuantitativeMaass

theorem positive_sub_le_log_difference {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    a-b≤a*(Real.log a-Real.log b) := by
  have hh := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at hh
  have hm := mul_le_mul_of_nonneg_left hh ha.le
  have he : a*(b/a-1)=b-a := by field_simp
  rw [he] at hm
  nlinarith

/-- The literal orbit weight itself is globally Lipschitz, with an
explicit constant from the proved uniform weight bound. -/
theorem quotientWeight_lipschitz_dist (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (z w : ℍ) :
    |weight N ε v z-weight N ε v w|≤quotientWeightBound ε*(2*v:ℝ)*dist z w := by
  have hd (x y : ℍ) : weight N ε v x-weight N ε v y≤
      quotientWeightBound ε*(2*v:ℝ)*dist x y := by
    calc
      _ ≤ weight N ε v x*(Real.log (weight N ε v x)-Real.log (weight N ε v y)) :=
        positive_sub_le_log_difference (weight_pos N hε hv x) (weight_pos N hε hv y)
      _ ≤ weight N ε v x*((2*v:ℝ)*dist x y) :=
        mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (quotientWeight_log_dist N hε hv x y))
          (weight_pos N hε hv x).le
      _ ≤ quotientWeightBound ε*((2*v:ℝ)*dist x y) :=
        mul_le_mul_of_nonneg_right (quotientWeight_uniform_bound N hε hv x) (by positivity)
      _ = _ := by ring
  exact abs_le.mpr ⟨by have hh := hd w z; rw [dist_comm w z] at hh; linarith,hd z w⟩

theorem quotientWeight_lipschitz (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    LipschitzWith (⟨quotientWeightBound ε*(2*v:ℝ),
      mul_nonneg (quotientWeightBound_nonneg ε) (by positivity)⟩:NNReal) (weight N ε v) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  exact quotientWeight_lipschitz_dist N hε hv z w

#print axioms positive_sub_le_log_difference
#print axioms quotientWeight_lipschitz_dist
#print axioms quotientWeight_lipschitz

end QuantitativeMaass
