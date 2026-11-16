module

public import QuantitativeMaassQuotientWeightLipschitzV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

open Set UpperHalfPlane AsymptoticCongruenceWeight

namespace QuantitativeMaass

/-- Real-coordinate representative of the actual orbit weight. Its values
outside the upper half-plane are immaterial to all subsequent statements. -/
def quotientWeightPlane (N : ℕ) (ε : ℝ) (v : ℕ) (Z : ℝ×ℝ) : ℝ :=
  if h : 0<Z.2 then weight N ε v ⟨⟨Z.1,Z.2⟩,h⟩ else 0

theorem quotientWeightPlane_upper (N : ℕ) (ε : ℝ) (v : ℕ) (z : ℍ) :
    quotientWeightPlane N ε v (z.re,z.im)=weight N ε v z := by
  simp only [quotientWeightPlane,dite_eq_left z.im_pos]
  congr 1

theorem hyperbolic_dist_le_coordinate_dist {r : ℝ} (hr : 0<r) (z w : ℍ)
    (hz : r≤z.im) (hw : r≤w.im) :
    dist z w≤2*dist (z.re,z.im) (w.re,w.im)/r := by
  have hs : r≤Real.sqrt (z.im*w.im) := by
    have hh := Real.sqrt_le_sqrt (mul_le_mul hz hw hr.le z.im_pos.le)
    simpa only [Real.sqrt_mul_self hr.le] using hh
  have hc : dist (z:ℂ) (w:ℂ)≤2*dist (z.re,z.im) (w.re,w.im) := by
    rw [dist_eq_norm]
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    simp only [Complex.sub_re,Complex.sub_im,coe_re,coe_im,Prod.dist_eq,Real.dist_eq]
    linarith [le_max_left |z.re-w.re| |z.im-w.im|,le_max_right |z.re-w.re| |z.im-w.im|]
  exact (dist_le_dist_coe_div_sqrt z w).trans
    ((div_le_div_of_nonneg_left dist_nonneg hr hs).trans
      (div_le_div_of_nonneg_right hc hr.le))

/-- On each region separated from the real axis the literal weight is
Lipschitz in real coordinates, with an explicit reciprocal-height cost. -/
theorem quotientWeightPlane_lipschitzOn (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) {r : ℝ} (hr : 0<r) :
    LipschitzOnWith (⟨2*quotientWeightBound ε*(2*v:ℝ)/r,
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (quotientWeightBound_nonneg ε))
        (by positivity)) hr.le⟩:NNReal)
      (quotientWeightPlane N ε v) {Z : ℝ×ℝ | r<Z.2} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro Z hZ W hW
  let z : ℍ := ⟨⟨Z.1,Z.2⟩,hr.trans hZ⟩
  let w : ℍ := ⟨⟨W.1,W.2⟩,hr.trans hW⟩
  have hd := hyperbolic_dist_le_coordinate_dist hr z w hZ.le hW.le
  have hh := quotientWeight_lipschitz_dist N hε hv z w
  change |quotientWeightPlane N ε v Z-quotientWeightPlane N ε v W|≤
    (2*quotientWeightBound ε*(2*v:ℝ)/r)*dist Z W
  rw [quotientWeightPlane,dite_eq_left (hr.trans hZ),quotientWeightPlane,dite_eq_left (hr.trans hW)]
  apply hh.trans
  calc
    _ ≤ quotientWeightBound ε*(2*v:ℝ)*(2*dist Z W/r) :=
      mul_le_mul_of_nonneg_left hd
        (mul_nonneg (quotientWeightBound_nonneg ε) (by positivity))
    _ = _ := by ring

#print axioms quotientWeightPlane_upper
#print axioms hyperbolic_dist_le_coordinate_dist
#print axioms quotientWeightPlane_lipschitzOn

end QuantitativeMaass
