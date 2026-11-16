module

public import QuantitativeMaassIntegratedWindowV1
public import QuantitativeMaassExceptionalWindowLimitV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeArithmeticMaassOverlap
open scoped Topology ENNReal FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- An explicit volume bound for every centre ball, obtained directly from
height bounds and its Euclidean image. -/
theorem centre_ball_volume_exp (o : ℍ) (L : ℝ) :
    volume.real (Metric.closedBall o L)≤Real.pi*Real.exp (4*L) := by
  have hsub : UpperHalfPlane.coe '' Metric.closedBall o L⊆
      Metric.ball (o:ℂ) (o.im*Real.exp L) := by
    rintro _ ⟨z,hz,rfl⟩
    apply (dist_coe_le z o).trans_lt
    have hh : Real.exp (dist z o)≤Real.exp L := Real.exp_le_exp.mpr hz
    nlinarith [o.im_pos,mul_le_mul_of_nonneg_left hh o.im_pos.le]
  have hh := QuantitativeHolomorphic.hyperbolic_volume_le_euclidean
    (Metric.closedBall o L) (Y:=o.im/Real.exp L) (by positivity)
    (fun z hz => im_lower_on_ball o z L hz)
  have hp : (NNReal.pi:ℝ≥0∞)=ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi,ENNReal.ofReal_coe_nnreal]
  have hv : volume (Metric.closedBall o L)≤ENNReal.ofReal (Real.pi*Real.exp (4*L)) := by
    calc
      _ ≤ ENNReal.ofReal ((1/(o.im/Real.exp L))^2)*
          volume (Metric.ball (o:ℂ) (o.im*Real.exp L)) :=
        hh.trans (mul_le_mul le_rfl (measure_mono hsub) (by positivity) (by positivity))
      _ = _ := by
        rw [Complex.volume_ball,hp,← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show Real.exp (4*L)=(Real.exp L)^4 from Real.exp_nat_mul L 4]
        field_simp [o.im_ne_zero]
  exact (ENNReal.toReal_le_toReal (isCompact_closedBall o L).measure_ne_top
    ENNReal.ofReal_ne_top).mpr hv |>.trans_eq (ENNReal.toReal_ofReal (by positivity))

/-- The actual lattice multiplicity has an exponential bound with a constant
chosen before its moving radius. -/
theorem energyMultiplicity_exp (o : ℍ) :
    ∃ C : ℝ,0<C ∧ ∀ D : ℝ,0≤D → (energyMultiplicity o 0 D:ℝ)≤C*Real.exp (4*D) := by
  refine ⟨625*Real.exp (4*(1+dist o I)),by positivity,?_⟩
  intro D hD
  have he : 1≤Real.exp (D+1+dist o I) := Real.one_le_exp_iff.mpr (by positivity)
  have hc := Nat.ceil_lt_add_one (Real.exp_pos (D+1+dist o I)).le
  have hb : (2*(⌈Real.exp (D+1+dist o I)⌉₊:ℝ)+1)≤5*Real.exp (D+1+dist o I) := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0≤2*(⌈Real.exp (D+1+dist o I)⌉₊:ℝ)+1) hb 4
  calc
    _ = (2*(⌈Real.exp (D+1+dist o I)⌉₊:ℝ)+1)^4 := by
      simp only [energyMultiplicity,add_zero,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    _ ≤ (5*Real.exp (D+1+dist o I))^4 := hp
    _ = _ := by
      rw [mul_pow,← Real.exp_nat_mul,mul_assoc,← Real.exp_add]
      norm_num only [Nat.cast_ofNat,show (5:ℝ)^4=625 by norm_num]
      congr 1
      ring

/-- A single exponential controls all denominator sizes uniformly in both
radii and in every level. -/
theorem displacementDenominatorBound_exp (o : ℍ) :
    ∃ A : ℝ,0<A ∧ ∀ L D : ℝ,0≤L → 0≤D →
      displacementDenominatorBound o L D≤A*Real.exp (D+L) := by
  refine ⟨Real.exp (dist o I)*(‖(o:ℂ)‖+o.im+1),by positivity,?_⟩
  intro L D hL hD
  have hEL : 1≤Real.exp L := Real.one_le_exp_iff.mpr hL
  have hb : ‖(o:ℂ)‖+o.im*Real.exp L+1≤(‖(o:ℂ)‖+o.im+1)*Real.exp L := by
    nlinarith [mul_le_mul_of_nonneg_left hEL (norm_nonneg (o:ℂ))]
  unfold displacementDenominatorBound
  calc
    _ ≤ Real.exp (D+dist o I)*((‖(o:ℂ)‖+o.im+1)*Real.exp L) := by
      gcongr
      linarith
    _ = _ := by rw [Real.exp_add,Real.exp_add];ring

/-- The complete displacement-area factor grows at most exponentially, with
one constant before both the propagation and centre-ball radii. -/
theorem hyperbolicSublevelConstant_exp (o : ℍ) :
    ∃ C : ℝ,0<C ∧ ∀ L D : ℝ,0≤L → 0≤D →
      hyperbolicSublevelConstant o L D≤C*Real.exp (6*(D+L)) := by
  obtain ⟨A,hA,hAb⟩ := displacementDenominatorBound_exp o
  let H := o.im*Real.exp 1
  let J := (1/o.im)^2
  have hH : 0<H := by dsimp only [H];positivity
  have hJ : 0<J := by dsimp only [J];positivity
  let C := J*(2*Real.pi*A+Real.pi*A^2)*H+Real.pi*(1+H+H*A)
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
  have hy : (1/(o.im/Real.exp L))^2≤J*E^2 := by
    have hp := pow_le_pow_left₀ (Real.exp_pos L).le heL 2
    have heq : (1/(o.im/Real.exp L))^2=J*(Real.exp L)^2 := by dsimp only [J];field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hp hJ.le
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
    _ ≤ (J*E^2)*(2*Real.pi*(A*E)+Real.pi*(A*E)^2)*(H*E)+
        (Real.pi*E^4)*(1+H*E+(H*E)*(A*E)) := by
      unfold hyperbolicSublevelConstant
      have hp := displacementDenominatorBound_pos o L D
      have hq := localDisplacementScale_pos o L
      gcongr
    _ = (J*2*Real.pi*A*H)*E^4+(J*Real.pi*A^2*H)*E^5+
        Real.pi*E^4+(Real.pi*H)*E^5+(Real.pi*H*A)*E^6 := by ring
    _ ≤ (J*2*Real.pi*A*H)*E^6+(J*Real.pi*A^2*H)*E^6+
        Real.pi*E^6+(Real.pi*H)*E^6+(Real.pi*H*A)*E^6 := by gcongr
    _ = C*E^6 := by dsimp only [C];ring
    _ = _ := by rw [← Real.exp_nat_mul];rfl

/-- The exact lattice and displacement factors in the quotient remainder
are bounded together, uniformly in both radii. -/
theorem integrated_geometry_exp (o : ℍ) :
    ∃ C : ℝ,0<C ∧ ∀ L D : ℝ,0≤L → 0≤D →
      (energyMultiplicity o 0 D:ℝ)*
        (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L D))≤
      C*Real.exp (10*(D+L)) := by
  obtain ⟨A,hA,ha⟩ := energyMultiplicity_exp o
  obtain ⟨B,hB,hb⟩ := hyperbolicSublevelConstant_exp o
  refine ⟨A*Real.pi*(Real.pi+B),by positivity,?_⟩
  intro L D hL hD
  have hQ := hyperbolicSublevelConstant_nonneg o L D
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

/-- A uniform exponential estimate for the literal quotient remainder, with
both radii free and constants chosen before the level and window parameters. -/
theorem windowGeometricRemainder_exp_bound (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ A C : ℝ,0<A ∧ 0<C ∧ ∀ (N : ℕ) [NeZero N] (L R ε t : ℝ) (hR : 1≤R),
      0≤L → 0≤ε → ε≤1 → 1≤t →
      (∫ z in Metric.closedBall o L,‖windowGeometricRemainder N K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z‖ ∂quotientMeasure N)≤
        C*Real.sqrt t*ε^2*Real.exp (A*R+30*L) := by
  obtain ⟨B,C,hB,hC,hbound⟩ := windowGeometricRemainder_quotient_integrated_bound K he hc
  obtain ⟨G,hG,hgeom⟩ := integrated_geometry_exp o
  refine ⟨20*B+2,C*G,by positivity,mul_pos hC hG,?_⟩
  intro N _ L R ε t hR hL hε hε1 ht
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hg := hgeom L (2*(B*R)+2*L) hL (by positivity)
  have hb := hbound N o L R ε t hR hε hε1 ht
  apply hb.trans
  calc
    _ = (C*Real.sqrt t*R^2*ε^2)*((energyMultiplicity o 0 (2*(B*R)+2*L):ℝ)*
        (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L (2*(B*R)+2*L)))) := by ring
    _ ≤ (C*Real.sqrt t*R^2*ε^2)*(G*Real.exp (10*((2*(B*R)+2*L)+L))) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = (C*G)*Real.sqrt t*ε^2*(R^2*Real.exp ((20*B)*R))*Real.exp (30*L) := by
      rw [show Real.exp (10*((2*(B*R)+2*L)+L))=
        Real.exp ((20*B)*R)*Real.exp (30*L) from by rw [← Real.exp_add];congr 1;ring]
      ring
    _ ≤ (C*G)*Real.sqrt t*ε^2*Real.exp ((20*B+2)*R)*Real.exp (30*L) := by
      gcongr
      exact radius_square_exp_le (20*B) R hRp.le
    _ = _ := by rw [Real.exp_add];ring

#print axioms windowGeometricRemainder_exp_bound

#print axioms centre_ball_volume_exp
#print axioms energyMultiplicity_exp
#print axioms displacementDenominatorBound_exp
#print axioms hyperbolicSublevelConstant_exp
#print axioms integrated_geometry_exp

end QuantitativeMaass
