module

public import QuantitativeMaassCuspHeightIntegralV1
public import QuantitativeMaassCuspCompactKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip QuantitativeArithmeticMaassOverlap QuantitativeSpectralObservability
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- A fixed-propagation nonidentity profile with inverse-square-root
hyperbolic decay has a square-root truncation-height integral in every cusp
chart. The geometric constant precedes the profile, level, chart and cutoff. -/
theorem radialNonidentity_cusp_truncation_bound (R : ℝ) (hR : 0≤R) :
    ∃ D : ℝ,0<D ∧ ∀ (N : ℕ) (A : SL(2,ℤ)) (g : ℝ → ℂ),
      ContinuousOn g (Ici 1) → Function.support g⊆Iic (Real.cosh R) →
      ∀ C : ℝ,0≤C → (∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) →
      ∀ H : ℝ,(1:ℝ)/4≤H →
      (∫ z in wideBox H,‖radialNonidentity N g (A•z)‖)≤D*C*(1+Real.sqrt H) := by
  let H₀ := max 2 (Real.exp (R/2))
  let L := Real.log (4*(H₀+3)^2)
  let E := Real.pi*(volume.real (Metric.closedBall (I:ℍ) L)+hyperbolicSublevelConstant I L (R+2*L))
  let G : ℝ := (energyMultiplicity I 0 (R+2*L):ℝ)*E
  let Q := 6*Real.exp R+9
  have hE : 0≤E := by
    have hh := hyperbolicSublevelConstant_nonneg I L (R+2*L)
    dsimp only [E]
    positivity
  have hG : 0≤G := mul_nonneg (Nat.cast_nonneg _) hE
  have hQ : 0<Q := by dsimp only [Q];positivity
  refine ⟨G+30*Q+1,by positivity,?_⟩
  intro N A g hg hs C hC hb H hH
  let F : ℍ → ℝ := fun z => ‖radialNonidentity N g (A•z)‖
  let W : ℍ → ℝ := fun z => (1+z.im)*Real.sqrt z.im
  let B := wideBox H₀
  have hF : Continuous F :=
    ((radialNonidentity_continuous N g hg R hR hs).comp
      (Isometry.of_dist_eq (fun x y => integral_action_dist A x y)).continuous).norm
  have hW : Continuous W := by dsimp only [W];fun_prop
  have hF0 (z : ℍ) : 0≤F z := norm_nonneg _
  have hW0 (z : ℍ) : 0≤W z := by dsimp only [W];positivity
  have hB : IsCompact B := wideBox_compact H₀
  have hFi : Integrable (B.indicator F) :=
    (integrable_indicator_iff hB.measurableSet).mpr (hF.continuousOn.integrableOn_compact hB)
  have hFi0 (z : ℍ) : 0≤B.indicator F z := by
    by_cases hz : z∈B
    · rw [indicator_of_mem hz]
      exact hF0 z
    · rw [indicator_of_notMem hz]
  have hpoint (z : ℍ) (hz : z∈wideBox H) : F z≤B.indicator F z+Q*C*W z := by
    by_cases hh : Real.exp (R/2)<z.im
    · have ht := radialNonidentity_high_cusp_bound N A g R hR hs C hC hb z hh
      have hcoef : 6*z.im*(Real.exp R-1)+9≤Q*(1+z.im) := by
        dsimp only [Q]
        nlinarith [Real.exp_pos R,z.im_pos]
      have hm := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hC (Real.sqrt_nonneg z.im))
      have hw : F z≤Q*C*W z := by
        apply ht.trans
        dsimp only [W]
        convert hm using 1 <;> ring
      exact hw.trans (le_add_of_nonneg_left (hFi0 z))
    · have hzB : z∈B := ⟨hz.1,hz.2.1,hz.2.2.1,(le_of_not_gt hh).trans (le_max_right _ _)⟩
      rw [indicator_of_mem hzB]
      exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hQ.le hC) (hW0 z))
  have hmain : (∫ z in wideBox H,F z)≤(∫ z in B,F z)+Q*C*(∫ z in wideBox H,W z) := by
    calc
      _ ≤ ∫ z in wideBox H,B.indicator F z+Q*C*W z :=
        setIntegral_mono_on (hF.continuousOn.integrableOn_compact (wideBox_compact H))
          (hFi.integrableOn.add ((hW.continuousOn.integrableOn_compact (wideBox_compact H)).const_mul (Q*C)))
          (wideBox_compact H).measurableSet hpoint
      _ = (∫ z in wideBox H,B.indicator F z)+Q*C*(∫ z in wideBox H,W z) := by
        rw [integral_add hFi.integrableOn
          ((hW.continuousOn.integrableOn_compact (wideBox_compact H)).const_mul (Q*C)),integral_const_mul]
      _ ≤ _ := by
        apply add_le_add _ le_rfl
        have hh := setIntegral_le_integral (s := wideBox H) hFi (Eventually.of_forall hFi0)
        simpa only [integral_indicator hB.measurableSet] using hh
  have hsub : B⊆Metric.closedBall (I:ℍ) L := by
    intro z hz
    apply (Real.le_log_iff_exp_le (by dsimp only [H₀];positivity : 0<4*(H₀+3)^2)).mpr
    exact wideBox_exp_dist H₀ (le_max_left _ _) hz
  have hlow : (∫ z in B,F z)≤G*C := by
    calc
      _ ≤ ∫ z in Metric.closedBall (I:ℍ) L,F z :=
        setIntegral_mono_set (hF.continuousOn.integrableOn_compact (isCompact_closedBall I L))
          (Eventually.of_forall hF0) (Eventually.of_forall hsub)
      _ ≤ _ := by
        have hh := radialNonidentity_chart_integral_bound N A I L R hR g hg hs C hC hb
        convert hh using 1
        dsimp only [G,E,F]
        ring
  have hhigh : (∫ z in wideBox H,W z)≤30*Real.sqrt H := cusp_height_majorant_integral H hH
  have hh := hmain.trans (add_le_add hlow (mul_le_mul_of_nonneg_left hhigh (mul_nonneg hQ.le hC)))
  apply hh.trans
  have hr : 0≤Real.sqrt H := Real.sqrt_nonneg H
  nlinarith [mul_nonneg hG hC,mul_nonneg (mul_nonneg hG hC) hr,
    mul_nonneg hC hr,mul_nonneg hQ.le hC]

#print axioms radialNonidentity_cusp_truncation_bound

end QuantitativeMaass
