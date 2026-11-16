module

public import QuantitativeMaassReflectionWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane QuantitativeArithmeticMaassOverlap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- Explicit growth of the reflected displacement-area factor, uniformly
in both radii and in all levels and integral reflected branches. -/
theorem reflectedSublevelConstant_exp (o : ℍ) :
    ∃ C : ℝ,0<C ∧ ∀ L D : ℝ,0≤L → 0≤D →
      reflectedSublevelConstant o L D≤C*Real.exp (6*(D+L)) := by
  obtain ⟨A,hA,hAb⟩ := displacementDenominatorBound_exp o
  let H := o.im*Real.exp 1
  let F := 1/o.im
  let P := ‖(o:ℂ)‖+o.im
  have hH : 0<H := by dsimp only [H];positivity
  have hF : 0<F := by dsimp only [F];positivity
  have hP : 0<P := by dsimp only [P];positivity
  let C := F^2*(4*P*F+8*P)*A*H+Real.pi
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro L D hL hD
  let E := Real.exp (D+L)
  have hE : 1≤E := Real.one_le_exp_iff.mpr (add_nonneg hD hL)
  have hE0 : 0≤E := le_trans zero_le_one hE
  have heL : Real.exp L≤E := Real.exp_le_exp.mpr (by linarith)
  have hb := hAb L D hL hD
  have hh : localDisplacementScale o L≤H*E := by
    unfold localDisplacementScale
    dsimp only [H]
    nlinarith [mul_le_mul_of_nonneg_left heL (mul_nonneg o.im_pos.le (Real.exp_pos 1).le)]
  have hy : 1/(o.im/Real.exp L)≤F*E := by
    have heq : 1/(o.im/Real.exp L)=F*Real.exp L := by dsimp only [F];field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left heL hF.le
  have hx : ‖(o:ℂ)‖+o.im*Real.exp L≤P*E := by
    dsimp only [P]
    nlinarith [mul_le_mul_of_nonneg_left hE (norm_nonneg (o:ℂ)),
      mul_le_mul_of_nonneg_left heL o.im_pos.le]
  have hv : volume.real (Metric.closedBall o L)≤Real.pi*E^4 := by
    apply (centre_ball_volume_exp o L).trans
    rw [← Real.exp_nat_mul]
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    linarith
  have h46 : E^4≤E^6 := pow_le_pow_right₀ hE (by omega)
  have h56 : E^5≤E^6 := pow_le_pow_right₀ hE (by omega)
  calc
    _ = (1/(o.im/Real.exp L))^2*
        (4*(‖(o:ℂ)‖+o.im*Real.exp L)*(1/(o.im/Real.exp L))+
          8*(‖(o:ℂ)‖+o.im*Real.exp L))*
        displacementDenominatorBound o L D*localDisplacementScale o L+
        volume.real (Metric.closedBall o L) := by unfold reflectedSublevelConstant;ring
    _ ≤ (F*E)^2*(4*(P*E)*(F*E)+8*(P*E))*(A*E)*(H*E)+Real.pi*E^4 := by
      have hp := displacementDenominatorBound_pos o L D
      have hq := localDisplacementScale_pos o L
      gcongr
    _ = (F^2*4*P*F*A*H)*E^6+(F^2*8*P*A*H)*E^5+Real.pi*E^4 := by ring
    _ ≤ (F^2*4*P*F*A*H)*E^6+(F^2*8*P*A*H)*E^6+Real.pi*E^6 := by gcongr
    _ = C*E^6 := by dsimp only [C];ring
    _ = _ := by rw [← Real.exp_nat_mul];rfl

/-- The full reflected lattice and area cost is at most exponential in the
two moving geometric radii, with a fixed basepoint constant. -/
theorem integrated_reflection_geometry_exp (o : ℍ) :
    ∃ C : ℝ,0<C ∧ ∀ L D : ℝ,0≤L → 0≤D →
      (energyMultiplicity o 0 D:ℝ)*
        (Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L D))≤
      C*Real.exp (10*(D+L)) := by
  obtain ⟨A,hA,ha⟩ := energyMultiplicity_exp o
  obtain ⟨B,hB,hb⟩ := reflectedSublevelConstant_exp o
  refine ⟨A*Real.pi*(Real.pi+B),by positivity,?_⟩
  intro L D hL hD
  have hQ := reflectedSublevelConstant_nonneg o L D
  have he4 : Real.exp (4*D)≤Real.exp (4*(D+L)) := Real.exp_le_exp.mpr (by linarith)
  have heL : Real.exp (4*L)≤Real.exp (6*(D+L)) := Real.exp_le_exp.mpr (by linarith)
  have hv := (centre_ball_volume_exp o L).trans (mul_le_mul_of_nonneg_left heL Real.pi_pos.le)
  calc
    _ ≤ (A*Real.exp (4*(D+L)))*(Real.pi*((Real.pi+B)*Real.exp (6*(D+L)))) := by
      apply mul_le_mul ((ha D hD).trans (mul_le_mul_of_nonneg_left he4 hA.le)) _
        (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      nlinarith [hb L D hL hD]
    _ = _ := by
      rw [show Real.exp (10*(D+L))=Real.exp (4*(D+L))*Real.exp (6*(D+L)) from by
        rw [← Real.exp_add];congr 1;ring]
      ring

/-- The literal reflected kernel for the original interval [a,b]. -/
def windowReflection (N : ℕ) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (z : ℍ) : ℂ :=
  radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution
    (windowTimeSchwartz K hc R hR a b) (windowTimeSchwartz K hc R hR a b)))) z (J•z)

/-- Actual reflected quotient integral with uniform exponential costs.
The displacement of the basepoint under J is absorbed into a fixed constant. -/
theorem windowReflection_exp_bound (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ A C : ℝ,0<A ∧ 0<C ∧ ∀ (N : ℕ) [NeZero N] (L R ε t : ℝ) (hR : 1≤R),
      0≤L → 0≤ε → ε≤1 → 1≤t →
      (∫ z in Metric.closedBall o L,‖windowReflection N K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z‖ ∂quotientMeasure N)≤
        C*Real.sqrt t*ε^2*Real.exp (A*R+30*L) := by
  obtain ⟨B,C,hB,hC,hbound⟩ := windowReflection_quotient_integrated_bound K he hc
  obtain ⟨G,hG,hgeom⟩ := integrated_reflection_geometry_exp o
  let T := Real.exp (10*dist (J•o) o)
  have hT : 0<T := Real.exp_pos _
  refine ⟨20*B+2,C*G*T,by positivity,by positivity,?_⟩
  intro N _ L R ε t hR hL hε hε1 ht
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hg := hgeom L (2*(B*R)+2*L+dist (J•o) o) hL (by positivity)
  have hb := hbound N o L R ε t hR hε hε1 ht
  apply hb.trans
  calc
    _ = (C*Real.sqrt t*R^2*ε^2)*((energyMultiplicity o 0 (2*(B*R)+2*L+dist (J•o) o):ℝ)*
        (Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L (2*(B*R)+2*L+dist (J•o) o)))) := by ring
    _ ≤ (C*Real.sqrt t*R^2*ε^2)*(G*Real.exp (10*((2*(B*R)+2*L+dist (J•o) o)+L))) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = (C*G*T)*Real.sqrt t*ε^2*(R^2*Real.exp ((20*B)*R))*Real.exp (30*L) := by
      rw [show Real.exp (10*((2*(B*R)+2*L+dist (J•o) o)+L))=
        Real.exp ((20*B)*R)*Real.exp (30*L)*T from by
          dsimp only [T]
          rw [← Real.exp_add,← Real.exp_add]
          congr 1
          ring]
      ring
    _ ≤ (C*G*T)*Real.sqrt t*ε^2*Real.exp ((20*B+2)*R)*Real.exp (30*L) := by
      gcongr
      exact radius_square_exp_le (20*B) R hRp.le
    _ = _ := by rw [Real.exp_add];ring

#print axioms reflectedSublevelConstant_exp
#print axioms integrated_reflection_geometry_exp
#print axioms windowReflection_exp_bound

end QuantitativeMaass
