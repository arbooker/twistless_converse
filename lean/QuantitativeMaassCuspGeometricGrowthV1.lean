module

public import QuantitativeMaassCuspTruncatedKernelV1
public import QuantitativeMaassGeometricGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip QuantitativeArithmeticMaassOverlap QuantitativeSpectralObservability
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- The actual truncated-cusp geometric constant grows at most exponentially
in the propagation radius, uniformly before choosing a window or level. -/
theorem radialNonidentity_cusp_truncation_exp :
    ∃ D : ℝ,0<D ∧ ∀ R : ℝ,0≤R → ∀ (N : ℕ) (A : SL(2,ℤ)) (g : ℝ → ℂ),
      ContinuousOn g (Ici 1) → Function.support g⊆Iic (Real.cosh R) →
      ∀ C : ℝ,0≤C → (∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) →
      ∀ H : ℝ,(1:ℝ)/4≤H →
      (∫ z in wideBox H,‖radialNonidentity N g (A•z)‖)≤
        D*Real.exp (40*R)*C*(1+Real.sqrt H) := by
  obtain ⟨G₀,hG₀,hgeom⟩ := integrated_geometry_exp (I:ℍ)
  let D := G₀*Real.exp (30*Real.log 100)+451
  have hD : 0<D := by dsimp only [D];positivity
  refine ⟨D,hD,?_⟩
  intro R hR
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
  have hH₀ : 2≤H₀ := le_max_left _ _
  have hH₀exp : H₀≤2*Real.exp (R/2) := by
    have he : 1≤Real.exp (R/2) := Real.one_le_exp_iff.mpr (by positivity)
    exact max_le (by linarith) (by linarith)
  have harg : 1≤4*(H₀+3)^2 := by nlinarith
  have hL : 0≤L := Real.log_nonneg harg
  have hargexp : 4*(H₀+3)^2≤100*Real.exp R := by
    have he : 1≤Real.exp (R/2) := Real.one_le_exp_iff.mpr (by positivity)
    have hsq := pow_le_pow_left₀ (by positivity : 0≤H₀+3)
      (by linarith : H₀+3≤5*Real.exp (R/2)) 2
    have hid : (Real.exp (R/2))^2=Real.exp R := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    nlinarith
  have hLupper : L≤Real.log 100+R := by
    have hh := Real.log_le_log (by positivity : 0<4*(H₀+3)^2) hargexp
    rw [Real.log_mul (by norm_num : (100:ℝ)≠0) (Real.exp_ne_zero R),Real.log_exp] at hh
    exact hh
  have hGexp : G≤(G₀*Real.exp (30*Real.log 100))*Real.exp (40*R) := by
    apply (hgeom L (R+2*L) hL (by positivity)).trans
    have hh := Real.exp_le_exp.mpr (by linarith : 10*((R+2*L)+L)≤30*Real.log 100+40*R)
    apply (mul_le_mul_of_nonneg_left hh hG₀.le).trans_eq
    rw [Real.exp_add]
    ring
  have hQexp : Q≤15*Real.exp (40*R) := by
    have he := Real.exp_le_exp.mpr (by linarith : R≤40*R)
    have he1 : 1≤Real.exp (40*R) := Real.one_le_exp_iff.mpr (by positivity)
    dsimp only [Q]
    nlinarith
  have htotal : G+30*Q+1≤D*Real.exp (40*R) := by
    have he1 : 1≤Real.exp (40*R) := Real.one_le_exp_iff.mpr (by positivity)
    dsimp only [D]
    nlinarith
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
  have hr : 0≤Real.sqrt H := Real.sqrt_nonneg H
  have hfinal : G*C+Q*C*(30*Real.sqrt H)≤(G+30*Q+1)*C*(1+Real.sqrt H) := by
    nlinarith [mul_nonneg hG hC,mul_nonneg (mul_nonneg hG hC) hr,
      mul_nonneg hC hr,mul_nonneg hQ.le hC]
  exact hh.trans (hfinal.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right htotal hC) (by positivity)))

#print axioms radialNonidentity_cusp_truncation_exp

end QuantitativeMaass
