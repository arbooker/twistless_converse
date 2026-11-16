module

public import QuantitativeMaassCorrespondenceUniformV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip QuantitativeArithmeticMaassOverlap
open scoped Topology FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- The correspondence part of the geometric cost is polynomial in entry
height, uniformly over all positive integral determinants. -/
theorem correspondence_height_cost (o : ℍ) :
    ∃ C : ℝ,0<C ∧ ∀ (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (B : ℝ),1≤B → (∀ i j,|(M i j:ℝ)|≤B) →
      Real.exp (10*(dist (positiveIntegralGL M hM•o) o+2*Real.log (2*B)))≤C*B^40 := by
  let c := (‖(o:ℂ)‖+1)^2/o.im
  have hc : 0≤c := by dsimp only [c];positivity
  refine ⟨Real.exp (20*Real.log (1+c)+20*Real.log 2),Real.exp_pos _,?_⟩
  intro M hM B hB hm
  have hBp : 0<B := lt_of_lt_of_le zero_lt_one hB
  have hlog : Real.log (1+B*c)≤Real.log B+Real.log (1+c) := by
    rw [←Real.log_mul hBp.ne' (by positivity : (1+c:ℝ)≠0)]
    apply Real.log_le_log (by positivity)
    nlinarith only [hB]
  have hd := positiveIntegralGL_dist_log_bound M hM B hBp.le hm o
  have hd' : dist (positiveIntegralGL M hM•o) o≤2*(Real.log B+Real.log (1+c)) := by
    have heq : B*(‖(o:ℂ)‖+1)^2/o.im=B*c := by dsimp only [c];ring
    rw [heq] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))
  have hb : Real.log (2*B)=Real.log 2+Real.log B := Real.log_mul (by norm_num) hBp.ne'
  calc
    _ ≤ Real.exp ((20*Real.log (1+c)+20*Real.log 2)+40*Real.log B) := by
      apply Real.exp_le_exp.mpr
      rw [hb]
      linarith only [hd']
    _ = _ := by
      rw [Real.exp_add]
      congr 1
      simpa only [Nat.cast_ofNat,Real.exp_log hBp] using Real.exp_nat_mul (Real.log B) 40

/-- The actual off-diagonal window error on raw hyperbolic balls has a
uniform polynomial entry-height cost and square-root spectral saving. -/
theorem windowIntegralRemainder_uniform_height_bound
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ A C : ℝ,0<A ∧ 0<C ∧ ∀ (N : ℕ) [NeZero N]
      (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 1≤t →
      IntegrableOn (windowIntegralRemainder N M hM K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)) (Metric.closedBall o L) ∧
      (∫ z in Metric.closedBall o L,‖windowIntegralRemainder N M hM K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z‖)≤
        C*(integralMatrixHeight M)^40*Real.sqrt t*ε^2*Real.exp (A*R+30*L) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := windowIntegralRemainder_raw_integrated_bound K he hc
  obtain ⟨G,hG,hgeom⟩ := correspondence_geometry_uniform_exp o
  obtain ⟨J,hJ,hheight⟩ := correspondence_height_cost o
  refine ⟨20*U+2,C*G*J,by positivity,by positivity,?_⟩
  intro N _ M hM L R ε t hR hL hε hε1 ht
  have hB := integralMatrixHeight_bounds M
  have hb : 0≤2*Real.log (2*integralMatrixHeight M) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith only [hB.1]))
  obtain ⟨hi,hiBound⟩ := hbound N M hM o L R ε t hR hε hε1 ht
  refine ⟨hi,hiBound.trans ?_⟩
  have hg := hgeom L (2*(U*R)+2*L) (dist (positiveIntegralGL M hM•o) o)
    (2*Real.log (2*integralMatrixHeight M)) hL (by positivity) dist_nonneg hb
  have hj := hheight M hM _ hB.1 hB.2
  have hr : R^2≤Real.exp (2*R) := by
    have hh := Real.add_one_le_exp R
    have hle : R≤Real.exp R := by linarith only [hh]
    have hp := pow_le_pow_left₀ (by linarith only [hR] : 0≤R) hle 2
    simpa only [←Real.exp_nat_mul,Nat.cast_ofNat] using hp
  have heq : Real.exp (10*((2*(U*R)+2*L)+L+dist (positiveIntegralGL M hM•o) o+
      2*Real.log (2*integralMatrixHeight M)))=
      Real.exp (10*((2*(U*R)+2*L)+L))*
      Real.exp (10*(dist (positiveIntegralGL M hM•o) o+2*Real.log (2*integralMatrixHeight M))) := by
    rw [←Real.exp_add];congr 1;ring
  rw [heq] at hg
  have hg' := hg.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hj (Real.exp_pos _).le) hG.le)
  calc
    _ = (C*Real.sqrt t*R^2*ε^2)*((energyMultiplicity o 0
        (2*(U*R)+2*L+dist (positiveIntegralGL M hM•o) o):ℝ)*
      (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L
        (2*(U*R)+2*L+dist (positiveIntegralGL M hM•o) o+2*Real.log (2*integralMatrixHeight M))))) := by ring
    _ ≤ (C*Real.sqrt t*R^2*ε^2)*(G*(Real.exp (10*((2*(U*R)+2*L)+L))*(J*(integralMatrixHeight M)^40))) :=
      mul_le_mul_of_nonneg_left hg' (by positivity)
    _ ≤ (C*Real.sqrt t*Real.exp (2*R)*ε^2)*(G*(Real.exp (10*((2*(U*R)+2*L)+L))*(J*(integralMatrixHeight M)^40))) := by
      gcongr
    _ = _ := by
      rw [show Real.exp ((20*U+2)*R+30*L)=Real.exp (2*R)*Real.exp (10*((2*(U*R)+2*L)+L)) from by
        rw [←Real.exp_add];congr 1;ring]
      ac_rfl

#print axioms correspondence_height_cost
#print axioms windowIntegralRemainder_uniform_height_bound

end QuantitativeMaass
