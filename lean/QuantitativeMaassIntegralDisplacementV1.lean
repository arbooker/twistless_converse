module

public import QuantitativeMaassHeckeColumnV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- The actual real Möbius transformation of a positive-determinant integral
matrix. In particular its determinant need not equal one. -/
def positiveIntegralGL (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero (M.map (Int.castRingHom ℝ)) (by
    have hd : (M.map (Int.castRingHom ℝ)).det=(M.det:ℝ) := by simp [Matrix.det_fin_two]
    rw [hd]
    exact_mod_cast hM.ne')

theorem positiveIntegralGL_det (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) :
    (positiveIntegralGL M hM).det.val=(M.det:ℝ) := by
  change (M.map (Int.castRingHom ℝ)).det=(M.det:ℝ)
  simp [Matrix.det_fin_two]

theorem positiveIntegralGL_fractional (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) (z : ℍ) :
    ((positiveIntegralGL M hM • z:ℍ):ℂ)=
      ((M 0 0:ℂ)*(z:ℂ)+M 0 1)/((M 1 0:ℂ)*(z:ℂ)+M 1 1) := by
  have hd : 0<(positiveIntegralGL M hM).det.val := by
    rw [positiveIntegralGL_det]
    exact_mod_cast hM
  rw [coe_smul_of_det_pos hd]
  change ((((M 0 0:ℝ):ℂ)*(z:ℂ)+((M 0 1:ℝ):ℂ))/
    (((M 1 0:ℝ):ℂ)*(z:ℂ)+((M 1 1:ℝ):ℂ)))=_
  simp only [Complex.ofReal_intCast]

/-- The integer-coefficient displacement estimate applies to every positive
integral determinant, including all nonscalar Hecke-word branches. -/
theorem positiveIntegralGL_euclidean_sublevel
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (hne : M 1 0≠0 ∨ M 1 1≠M 0 0 ∨ M 0 1≠0)
    (Ω : Set ℍ) (D r Y : ℝ) (hD : 0≤D) (hr : 0<r) (hr1 : r≤1)
    (hsmall : r*D≤1) (hY : 0<Y) (hheight : ∀ z∈Ω,Y≤z.im)
    (hbound : ∀ z∈Ω,‖(M 1 0:ℂ)*(z:ℂ)+M 1 1‖≤D) :
    volume {z∈Ω | ‖(z:ℂ)-((positiveIntegralGL M hM • z:ℍ):ℂ)‖<r}≤
      ENNReal.ofReal ((1/Y)^2*((2*Real.pi*D+Real.pi*D^2)*r)) := by
  have hd : M 0 0*M 1 1-M 0 1*M 1 0≠0 := by
    simpa only [Matrix.det_fin_two] using hM.ne'
  have hh := QuantitativeHolomorphic.hyperbolic_integral_matrix_displacement_volume
    (M 0 0) (M 0 1) (M 1 0) (M 1 1) hd hne Ω hD hr hr1 hsmall hY hheight
    (fun z _ => QuantitativeArithmetic.integer_matrix_denominator_ne_zero M hM.ne' z) hbound
  simpa only [positiveIntegralGL_fractional] using hh

/-- Hyperbolic near-return area for an actual positive integral matrix.
Only a denominator bound is supplied; the displacement estimate is proved. -/
theorem positiveIntegralGL_hyperbolic_sublevel
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (hne : M 1 0≠0 ∨ M 1 1≠M 0 0 ∨ M 0 1≠0)
    (o : ℍ) (L D : ℝ)
    (hbound : ∀ z∈Metric.closedBall o L,
      ‖(M 1 0:ℂ)*(z:ℂ)+M 1 1‖≤displacementDenominatorBound o L D)
    (r : ℝ) (hr : 0<r) :
    volume {z∈Metric.closedBall o L | dist (positiveIntegralGL M hM • z) z<r}≤
      ENNReal.ofReal (hyperbolicSublevelConstant o L D*r) := by
  let H := localDisplacementScale o L
  let B := displacementDenominatorBound o L D
  let V := volume.real (Metric.closedBall o L)
  let A := (1/(o.im/Real.exp L))^2*(2*Real.pi*B+Real.pi*B^2)
  let T := 1+H+H*B
  have hH : 0<H := localDisplacementScale_pos o L
  have hB : 0<B := displacementDenominatorBound_pos o L D
  have hV : 0≤V := ENNReal.toReal_nonneg
  have hA : 0≤A := by dsimp only [A];positivity
  have hT : 0<T := by dsimp only [T];positivity
  have hQ : hyperbolicSublevelConstant o L D=A*H+V*T := rfl
  have hvol : volume (Metric.closedBall o L)=ENNReal.ofReal V :=
    (ENNReal.ofReal_toReal (isCompact_closedBall o L).measure_ne_top).symm
  rw [hQ]
  by_cases hsmall : r*T≤1
  · have hr1 : r≤1 := by
      have h1 : 1≤T := by dsimp only [T];nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 hr.le]
    have hHr : H*r≤1 := by
      have hh : H≤T := by dsimp only [T];nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hh hr.le]
    have hHrB : (H*r)*B≤1 := by
      have hh : H*B≤T := by dsimp only [T];linarith
      nlinarith [mul_le_mul_of_nonneg_left hh hr.le]
    have harea := positiveIntegralGL_euclidean_sublevel M hM hne (Metric.closedBall o L)
      B (H*r) (o.im/Real.exp L) hB.le (mul_pos hH hr) hHr hHrB (by positivity)
      (fun z hz => im_lower_on_ball o z L hz)
      hbound
    apply (measure_mono (show {z∈Metric.closedBall o L | dist (positiveIntegralGL M hM • z) z<r}⊆
      {z∈Metric.closedBall o L | ‖(z:ℂ)-((positiveIntegralGL M hM • z : ℍ):ℂ)‖<H*r} from ?_)).trans
      (harea.trans ?_)
    · rintro z ⟨hz,hzr⟩
      refine ⟨hz,?_⟩
      exact (euclidean_displacement_le_hyperbolic o z (positiveIntegralGL M hM • z) L hz
        (hzr.le.trans hr1)).trans_lt (mul_lt_mul_of_pos_left hzr hH)
    · apply ENNReal.ofReal_le_ofReal
      rw [← mul_assoc]
      change A*(H*r)≤(A*H+V*T)*r
      nlinarith [mul_nonneg hV hT.le]
  · have hlarge : 1<r*T := lt_of_not_ge hsmall
    apply ((measure_mono (show {z∈Metric.closedBall o L | dist (positiveIntegralGL M hM • z) z<r}⊆
      Metric.closedBall o L from fun _ hz => hz.1)).trans_eq hvol).trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_le_mul_of_nonneg_left hlarge.le hV,mul_nonneg hA hH.le]


#print axioms positiveIntegralGL_det
#print axioms positiveIntegralGL_fractional
#print axioms positiveIntegralGL_euclidean_sublevel
#print axioms positiveIntegralGL_hyperbolic_sublevel

end QuantitativeMaass
