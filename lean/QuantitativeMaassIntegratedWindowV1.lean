module

public import QuantitativeMaassHyperbolicSublevelV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

local instance (N : ℕ) : ContinuousConstSMul (gamma N) ℍ :=
  ⟨fun γ => AsymptoticRationalBranches.action_continuous γ.val⟩

/-- Integrate an actual radial profile against a nonidentity congruence
transformation, removing its fixed points using the proved null-set estimate. -/
theorem diagonalOrbitSet_profile_integral_bound (N : ℕ) (o : ℍ) (L D : ℝ)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D) (hne : γ≠1)
    (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    IntegrableOn (fun z : ℍ => g (Real.cosh (dist (γ•z) z))) (Metric.closedBall o L) ∧
    (∫ z in Metric.closedBall o L,‖g (Real.cosh (dist (γ•z) z))‖)≤
      C*(Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L D)) := by
  have hc : Continuous (fun z : ℍ => g (Real.cosh (dist (γ•z) z))) :=
    hg.comp_continuous (Real.continuous_cosh.comp ((continuous_const_smul γ).dist continuous_id))
      (fun _ => Real.one_le_cosh _)
  have hi : IntegrableOn (fun z : ℍ => g (Real.cosh (dist (γ•z) z))) (Metric.closedBall o L) :=
    hc.continuousOn.integrableOn_compact (isCompact_closedBall o L)
  obtain ⟨hj,hbound⟩ := diagonalOrbitSet_inverse_sqrt_integral N o L D γ hγ hne
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ z in Metric.closedBall o L,C*(1/Real.sqrt (dist (γ•z) z)) := by
      apply integral_mono_ae hi.norm (hj.const_mul C)
      filter_upwards [diagonalOrbitSet_displacement_pos_ae N o L D γ hγ hne] with z hz
      calc
        _ ≤ C/Real.sqrt (Real.sinh (dist (γ•z) z)) := hb _ hz
        _ ≤ C/Real.sqrt (dist (γ•z) z) := div_le_div_of_nonneg_left hC
          (Real.sqrt_pos.mpr hz) (Real.sqrt_le_sqrt (Real.self_le_sinh_iff.mpr hz.le))
        _ = _ := by ring
    _ = C*(∫ z in Metric.closedBall o L,1/Real.sqrt (dist (γ•z) z)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hC

/-- Physical continuity for the Abel profile of any original compact even
smooth time function, including the radial boundary q=1. -/
theorem evenTime_abel_continuous (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) :
    ContinuousOn (abelProfile (evenCoshLift f)) (Ici 1) := by
  obtain ⟨R,hR,hRs⟩ := hc.isCompact.isBounded.subset_closedBall_lt 0 (0:ℝ)
  have hs : Function.support f⊆Icc (-R) R := by
    intro u hu
    have hh := hRs (subset_tsupport f hu)
    have hab : |u|≤R := by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hh
    exact abs_le.mp hab
  exact abelProfile_continuousOn_physical _ (evenCoshLift_smoothOn f hf he hc)
    (Real.cosh R) (Real.one_le_cosh R) (evenCoshLift_support_of_time_support f R hR.le hs)

def windowSquareProfile (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (ε t : ℝ) : ℝ → ℂ :=
  abelProfile (evenCoshLift (timeConvolution
    (windowTimeSchwartz K hc R hR (t-ε) (t+ε))
    (windowTimeSchwartz K hc R hR (t-ε) (t+ε))))

theorem windowSquareProfile_continuous (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (ε t : ℝ) : ContinuousOn (windowSquareProfile K hc R hR ε t) (Ici 1) := by
  let f := windowTimeSchwartz K hc R hR (t-ε) (t+ε)
  have hfe : Function.Even f := symmetricWindowTimeTest_even K he R (t-ε) (t+ε)
  have hfc : HasCompactSupport (f : ℝ → ℂ) := symmetricWindowTimeTest_compact K hc R (t-ε) (t+ε) hR
  exact evenTime_abel_continuous (timeConvolution f f) ((timeConvolution f f).smooth ⊤)
    (timeConvolution_even f f hfe hfe) (timeConvolution_compact f f hfc hfc)

/-- The original window-square profile has an integrated nonidentity bound,
with one kernel constant before all levels, orbit elements and window parameters.
This is the orientation-preserving contribution, not a reflection estimate. -/
theorem windowSquareProfile_integrated_bound (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℕ) (o : ℍ) (L D : ℝ) (γ : gamma N),
      γ∈diagonalOrbitSet N o D → γ≠1 → ∀ (R ε t : ℝ) (hR : 1≤R),
      0≤ε → ε≤1 → 1≤t →
      IntegrableOn (fun z : ℍ => windowSquareProfile K hc R
        (lt_of_lt_of_le zero_lt_one hR) ε t (Real.cosh (dist (γ•z) z))) (Metric.closedBall o L) ∧
      (∫ z in Metric.closedBall o L,‖windowSquareProfile K hc R
        (lt_of_lt_of_le zero_lt_one hR) ε t (Real.cosh (dist (γ•z) z))‖)≤
        C*Real.sqrt t*R^2*ε^2*
          (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L D)) := by
  obtain ⟨C,hC,hbound⟩ := windowTimeSquare_abel_decay K he hc
  refine ⟨C,hC,?_⟩
  intro N o L D γ hγ hne R ε t hR hε hε1 ht
  apply diagonalOrbitSet_profile_integral_bound N o L D γ hγ hne
    (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t)
    (windowSquareProfile_continuous K he hc R _ ε t) (C*Real.sqrt t*R^2*ε^2) (by positivity)
  intro d hd
  exact hbound R ε t d hR hε hε1 ht hd

/-- Sum all actual nonidentity terms on the centre ball, using finite
propagation and the explicit lattice multiplicity. -/
theorem radialNonidentity_integral_bound (N : ℕ) [NeZero N] (o : ℍ) (L R : ℝ)
    (hR : 0≤R) (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1))
    (hs : Function.support g⊆Iic (Real.cosh R)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    (∫ z in Metric.closedBall o L,‖radialNonidentity N g z‖)≤
      (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+2*L):ℝ)*C*
        (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L (R+2*L))) := by
  classical
  let S := (diagonalOrbitSet N o (R+2*L)).erase 1
  let E := Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L (R+2*L))
  have hE : 0≤E := by
    have hh := hyperbolicSublevelConstant_nonneg o L (R+2*L)
    dsimp only [E]
    positivity
  have hi : IntegrableOn (radialNonidentity N g) (Metric.closedBall o L) :=
    (radialNonidentity_continuous N g hg R hR hs).continuousOn.integrableOn_compact (isCompact_closedBall o L)
  have heach (γ : gamma N) (hγ : γ∈S) :=
    diagonalOrbitSet_profile_integral_bound N o L (R+2*L) γ
      (Finset.mem_erase.mp hγ).2 (Finset.mem_erase.mp hγ).1 g hg C hC hb
  have his (γ : gamma N) (hγ : γ∈S) :
      IntegrableOn (fun z : ℍ => ‖g (Real.cosh (dist (γ•z) z))‖) (Metric.closedBall o L) :=
    (heach γ hγ).1.norm
  calc
    _ ≤ ∫ z in Metric.closedBall o L,∑ γ∈S,‖g (Real.cosh (dist (γ•z) z))‖ := by
      apply integral_mono_ae hi.norm (integrable_finsetSum S his)
      filter_upwards [ae_restrict_mem ((isCompact_closedBall o L).measurableSet)] with z hz
      rw [radialNonidentity_eq_finite N g R hR hs o z L hz]
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr
      · ext γ
        simp only [S,Finset.mem_erase]
      · intro γ _
        rfl
    _ = ∑ γ∈S,∫ z in Metric.closedBall o L,‖g (Real.cosh (dist (γ•z) z))‖ :=
      integral_finsetSum S his
    _ ≤ ∑ _γ∈S,C*E := Finset.sum_le_sum (fun γ hγ => (heach γ hγ).2)
    _ = (S.card:ℝ)*(C*E) := by simp
    _ ≤ (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+2*L):ℝ)*(C*E) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC hE)
      exact_mod_cast (Finset.card_erase_le.trans (diagonalOrbitSet_card_bound N o (R+2*L)))
    _ = _ := by dsimp only [E];ring

/-- The literal geometric remainder of the original window has a proved
integrated bound. Both constants precede every level and moving-window parameter. -/
theorem windowGeometricRemainder_integrated_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ (N : ℕ) [NeZero N] (o : ℍ) (L R ε t : ℝ)
      (hR : 1≤R),0≤ε → ε≤1 → 1≤t →
      (∫ z in Metric.closedBall o L,‖windowGeometricRemainder N K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z‖)≤
        (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (2*(B*R)+2*L):ℝ)*
          (C*Real.sqrt t*R^2*ε^2)*
          (Real.pi*(volume.real (Metric.closedBall o L)+
            hyperbolicSublevelConstant o L (2*(B*R)+2*L))) := by
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
  apply radialNonidentity_integral_bound N o L (2*(B*R)) (by positivity)
    (windowSquareProfile K hc R hRp ε t) (windowSquareProfile_continuous K he hc R hRp ε t)
    hps (C*Real.sqrt t*R^2*ε^2) (by positivity)
  intro d hd
  exact hbound R ε t d hR hε hε1 ht hd

/-- Normalization of the actual orbit density implies domination by
hyperbolic volume; no fundamental-domain identification is assumed. -/
theorem normalized_quotientMeasure_le_volume (N : ℕ) : quotientMeasure N≤volume := by
  have hd (z : ℍ) : density N z≤1 := by
    have hh := ENNReal.le_tsum (f:=fun γ : gamma N => density N (γ.val•z)) 1
    simpa only [OneMemClass.coe_one,one_smul,density_orbit_sum] using hh
  have hh := withDensity_mono (μ:=(volume : Measure ℍ)) (Eventually.of_forall hd)
  simpa only [quotientMeasure,withDensity_const,one_smul] using hh

/-- The integrated nonidentity estimate also holds for the actual quotient
measure used by the spectral trace. -/
theorem radialNonidentity_quotient_integral_bound (N : ℕ) [NeZero N] (o : ℍ) (L R : ℝ)
    (hR : 0≤R) (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1))
    (hs : Function.support g⊆Iic (Real.cosh R)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    (∫ z in Metric.closedBall o L,‖radialNonidentity N g z‖ ∂quotientMeasure N)≤
      (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+2*L):ℝ)*C*
        (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L (R+2*L))) := by
  have hi : IntegrableOn (radialNonidentity N g) (Metric.closedBall o L) :=
    (radialNonidentity_continuous N g hg R hR hs).continuousOn.integrableOn_compact (isCompact_closedBall o L)
  exact (integral_mono_measure
    (Measure.restrict_mono_measure (normalized_quotientMeasure_le_volume N) _)
    (Eventually.of_forall (fun z => norm_nonneg _)) hi.norm).trans
      (radialNonidentity_integral_bound N o L R hR g hg hs C hC hb)

/-- Literal original-window geometric error on the actual spectral quotient,
with explicit lattice and displacement-area factors. -/
theorem windowGeometricRemainder_quotient_integrated_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ (N : ℕ) [NeZero N] (o : ℍ) (L R ε t : ℝ)
      (hR : 1≤R),0≤ε → ε≤1 → 1≤t →
      (∫ z in Metric.closedBall o L,‖windowGeometricRemainder N K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z‖ ∂quotientMeasure N)≤
        (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (2*(B*R)+2*L):ℝ)*
          (C*Real.sqrt t*R^2*ε^2)*
          (Real.pi*(volume.real (Metric.closedBall o L)+
            hyperbolicSublevelConstant o L (2*(B*R)+2*L))) := by
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
  apply radialNonidentity_quotient_integral_bound N o L (2*(B*R)) (by positivity)
    (windowSquareProfile K hc R hRp ε t) (windowSquareProfile_continuous K he hc R hRp ε t)
    hps (C*Real.sqrt t*R^2*ε^2) (by positivity)
  intro d hd
  exact hbound R ε t d hR hε hε1 ht hd

#print axioms normalized_quotientMeasure_le_volume
#print axioms radialNonidentity_quotient_integral_bound
#print axioms windowGeometricRemainder_quotient_integrated_bound

#print axioms radialNonidentity_integral_bound
#print axioms windowGeometricRemainder_integrated_bound

#print axioms diagonalOrbitSet_profile_integral_bound
#print axioms evenTime_abel_continuous
#print axioms windowSquareProfile_continuous
#print axioms windowSquareProfile_integrated_bound

end QuantitativeMaass
