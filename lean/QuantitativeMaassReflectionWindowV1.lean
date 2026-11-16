module

public import QuantitativeMaassReflectionSublevelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

local instance (N : ℕ) : ContinuousConstSMul (gamma N) ℍ :=
  ⟨fun γ => AsymptoticRationalBranches.action_continuous γ.val⟩

/-- The genuine orientation-reversing reflection is a hyperbolic isometry. -/
theorem reflection_dist (z w : ℍ) : dist (J•z) (J•w)=dist z w := by
  have him (u : ℍ) : (J•u).im=u.im := by
    change ((J•u:ℍ):ℂ).im=u.im
    rw [coe_J_smul]
    simp only [Complex.neg_im,Complex.conj_im,neg_neg,coe_im]
  rw [UpperHalfPlane.dist_eq,UpperHalfPlane.dist_eq,him,him,coe_J_smul,coe_J_smul,
    dist_neg_neg,Complex.dist_conj_conj]

/-- One finite orbit set contains every reflected displacement relevant on
an entire centre ball. The extra basepoint term is necessary when J o≠o. -/
theorem reflected_displacement_in_diagonalOrbitSet (N : ℕ) (o z : ℍ) (L R : ℝ)
    (hz : dist z o≤L) (γ : gamma N) (hγ : dist (γ•(J•z)) z≤R) :
    γ∈diagonalOrbitSet N o (R+2*L+dist (J•o) o) := by
  apply (mem_diagonalOrbitSet N o _ γ).mpr
  have h1 := dist_triangle (γ•o) (γ•(J•z)) o
  have h2 := dist_triangle (γ•(J•z)) z o
  have h3 := dist_triangle o (J•o) (J•z)
  rw [congruence_action_dist] at h1
  rw [reflection_dist,dist_comm o z,dist_comm o (J•o)] at h3
  linarith

/-- The actual reflected Poincare kernel is a finite sum on a centre ball. -/
theorem radialPoincareKernel_reflected_eq_finite (N : ℕ) (g : ℝ → ℂ)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (o z : ℍ) (L : ℝ) (hz : dist z o≤L) :
    radialPoincareKernel N g z (J•z)=
      ∑ γ∈diagonalOrbitSet N o (R+2*L+dist (J•o) o),g (Real.cosh (dist (γ•(J•z)) z)) := by
  classical
  simp only [radialPoincareKernel,poincareSum,radialFunction_upper]
  apply tsum_eq_sum
  intro γ hγ
  by_contra hn
  have hd : dist (γ•(J•z)) z≤R := by
    have hb := Real.cosh_le_cosh.mp (hs hn)
    simpa only [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] using hb
  exact hγ (reflected_displacement_in_diagonalOrbitSet N o z L R hz γ hd)

/-- Integrate an actual radial profile against a reflected congruence
transformation, removing its fixed points using the proved null-set estimate. -/
theorem diagonalOrbitSet_reflected_profile_integral_bound (N : ℕ) (o : ℍ) (L D : ℝ)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D)
    (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    IntegrableOn (fun z : ℍ => g (Real.cosh (dist (γ•(J•z)) z))) (Metric.closedBall o L) ∧
    (∫ z in Metric.closedBall o L,‖g (Real.cosh (dist (γ•(J•z)) z))‖)≤
      C*(Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L D)) := by
  have hc : Continuous (fun z : ℍ => g (Real.cosh (dist (γ•(J•z)) z))) :=
    hg.comp_continuous (Real.continuous_cosh.comp (((continuous_const_smul γ).comp (continuous_const_smul J)).dist continuous_id))
      (fun _ => Real.one_le_cosh _)
  have hi : IntegrableOn (fun z : ℍ => g (Real.cosh (dist (γ•(J•z)) z))) (Metric.closedBall o L) :=
    hc.continuousOn.integrableOn_compact (isCompact_closedBall o L)
  obtain ⟨hj,hbound⟩ := diagonalOrbitSet_reflected_inverse_sqrt_integral N o L D γ hγ
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ z in Metric.closedBall o L,C*(1/Real.sqrt (dist (γ•(J•z)) z)) := by
      apply integral_mono_ae hi.norm (hj.const_mul C)
      filter_upwards [diagonalOrbitSet_reflected_displacement_pos_ae N o L D γ hγ] with z hz
      calc
        _ ≤ C/Real.sqrt (Real.sinh (dist (γ•(J•z)) z)) := hb _ hz
        _ ≤ C/Real.sqrt (dist (γ•(J•z)) z) := div_le_div_of_nonneg_left hC
          (Real.sqrt_pos.mpr hz) (Real.sqrt_le_sqrt (Real.self_le_sinh_iff.mpr hz.le))
        _ = _ := by ring
    _ = C*(∫ z in Metric.closedBall o L,1/Real.sqrt (dist (γ•(J•z)) z)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hC

/-- Sum all actual reflected terms on the centre ball, using finite
propagation and the explicit lattice multiplicity. -/
theorem radialPoincareKernel_reflected_integral_bound (N : ℕ) [NeZero N] (o : ℍ) (L R : ℝ)
    (hR : 0≤R) (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1))
    (hs : Function.support g⊆Iic (Real.cosh R)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    (∫ z in Metric.closedBall o L,‖(fun z => radialPoincareKernel N g z (J•z)) z‖)≤
      (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+2*L+dist (J•o) o):ℝ)*C*
        (Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L (R+2*L+dist (J•o) o))) := by
  classical
  let S := diagonalOrbitSet N o (R+2*L+dist (J•o) o)
  let E := Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L (R+2*L+dist (J•o) o))
  have hE : 0≤E := by
    have hh := reflectedSublevelConstant_nonneg o L (R+2*L+dist (J•o) o)
    dsimp only [E]
    positivity
  have hi : IntegrableOn ((fun z => radialPoincareKernel N g z (J•z))) (Metric.closedBall o L) :=
    ((radialPoincareKernel_joint_continuous_physical N g hg R hR hs).comp
      (continuous_id.prodMk (continuous_const_smul J))).continuousOn.integrableOn_compact (isCompact_closedBall o L)
  have heach (γ : gamma N) (hγ : γ∈S) :=
    diagonalOrbitSet_reflected_profile_integral_bound N o L (R+2*L+dist (J•o) o) γ
      hγ g hg C hC hb
  have his (γ : gamma N) (hγ : γ∈S) :
      IntegrableOn (fun z : ℍ => ‖g (Real.cosh (dist (γ•(J•z)) z))‖) (Metric.closedBall o L) :=
    (heach γ hγ).1.norm
  calc
    _ ≤ ∫ z in Metric.closedBall o L,∑ γ∈S,‖g (Real.cosh (dist (γ•(J•z)) z))‖ := by
      apply integral_mono_ae hi.norm (integrable_finsetSum S his)
      filter_upwards [ae_restrict_mem ((isCompact_closedBall o L).measurableSet)] with z hz
      change ‖radialPoincareKernel N g z (J•z)‖≤_
      rw [radialPoincareKernel_reflected_eq_finite N g R hR hs o z L hz]
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr
      · ext γ
        rfl
      · intro γ _
        rfl
    _ = ∑ γ∈S,∫ z in Metric.closedBall o L,‖g (Real.cosh (dist (γ•(J•z)) z))‖ :=
      integral_finsetSum S his
    _ ≤ ∑ _γ∈S,C*E := Finset.sum_le_sum (fun γ hγ => (heach γ hγ).2)
    _ = (S.card:ℝ)*(C*E) := by simp
    _ ≤ (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+2*L+dist (J•o) o):ℝ)*(C*E) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC hE)
      exact_mod_cast (diagonalOrbitSet_card_bound N o (R+2*L+dist (J•o) o))
    _ = _ := by dsimp only [E];ring

/-- The integrated reflected estimate also holds for the actual quotient
measure used by the spectral trace. -/
theorem radialPoincareKernel_reflected_quotient_integral_bound (N : ℕ) [NeZero N] (o : ℍ) (L R : ℝ)
    (hR : 0≤R) (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1))
    (hs : Function.support g⊆Iic (Real.cosh R)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    (∫ z in Metric.closedBall o L,‖(fun z => radialPoincareKernel N g z (J•z)) z‖ ∂quotientMeasure N)≤
      (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+2*L+dist (J•o) o):ℝ)*C*
        (Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L (R+2*L+dist (J•o) o))) := by
  have hi : IntegrableOn ((fun z => radialPoincareKernel N g z (J•z))) (Metric.closedBall o L) :=
    ((radialPoincareKernel_joint_continuous_physical N g hg R hR hs).comp
      (continuous_id.prodMk (continuous_const_smul J))).continuousOn.integrableOn_compact (isCompact_closedBall o L)
  exact (integral_mono_measure
    (Measure.restrict_mono_measure (normalized_quotientMeasure_le_volume N) _)
    (Eventually.of_forall (fun z => norm_nonneg _)) hi.norm).trans
      (radialPoincareKernel_reflected_integral_bound N o L R hR g hg hs C hC hb)

/-- Literal original-window reflected kernel on the actual spectral quotient,
with explicit lattice and displacement-area factors. -/
theorem windowReflection_quotient_integrated_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ (N : ℕ) [NeZero N] (o : ℍ) (L R ε t : ℝ)
      (hR : 1≤R),0≤ε → ε≤1 → 1≤t →
      (∫ z in Metric.closedBall o L,‖radialPoincareKernel N (windowSquareProfile K hc R
        (lt_of_lt_of_le zero_lt_one hR) ε t) z (J•z)‖ ∂quotientMeasure N)≤
        (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (2*(B*R)+2*L+dist (J•o) o):ℝ)*
          (C*Real.sqrt t*R^2*ε^2)*
          (Real.pi*(volume.real (Metric.closedBall o L)+
            reflectedSublevelConstant o L (2*(B*R)+2*L+dist (J•o) o))) := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  obtain ⟨C,hC,hbound⟩ := windowTimeSquare_abel_decay K he hc
  refine ⟨B,C,hB,hC,?_⟩
  intro N _ o L R ε t hR hε hε1 ht
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let f := windowTimeSchwartz K hc R hRp (t-ε) (t+ε)
  have hfs : Function.support (f : ℝ → ℂ)⊆Icc (-(B*R)) (B*R) := hs R hRp (t-ε) (t+ε)
  have hgs : Function.support (timeConvolution f f : ℝ → ℂ)⊆Icc (-(2*(B*R))) (2*(B*R)) := by
    simpa only [two_mul] using timeConvolution_support f f (B*R) (B*R) hfs hfs
  have hps : Function.support (windowSquareProfile K hc R hRp ε t)⊆Iic (Real.cosh (2*(B*R))) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity) hgs)
  apply radialPoincareKernel_reflected_quotient_integral_bound N o L (2*(B*R)) (by positivity)
    (windowSquareProfile K hc R hRp ε t) (windowSquareProfile_continuous K he hc R hRp ε t)
    hps (C*Real.sqrt t*R^2*ε^2) (by positivity)
  intro d hd
  exact hbound R ε t d hR hε hε1 ht hd

#print axioms reflection_dist
#print axioms reflected_displacement_in_diagonalOrbitSet
#print axioms radialPoincareKernel_reflected_eq_finite
#print axioms diagonalOrbitSet_reflected_profile_integral_bound
#print axioms radialPoincareKernel_reflected_integral_bound
#print axioms radialPoincareKernel_reflected_quotient_integral_bound
#print axioms windowReflection_quotient_integrated_bound

end QuantitativeMaass
