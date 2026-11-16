module

public import QuantitativeMaassAllLevelAbelDistributionV1
public import QuantitativeMaassPositiveTimeApproximationV1
public import QuantitativeMaassAbelOriginalTestRepresentationV1
public import QuantitativeMaassAbelZeroVelocityV1
public import QuantitativeMaassPositiveTimeRemainderV1
public import QuantitativeMaassPositiveTimeSmoothV1
public import QuantitativeMaassPositiveTimeWaveV1
public import QuantitativeMaassPositiveTimeCauchyV1
public import QuantitativeMaassPositiveTimeCosineActionV1
public import QuantitativeMaassAbelCosineRepresentationV1
public import QuantitativeMaassAbelInitialGraphV1
public import QuantitativeMaassAbelSpectralIdentificationV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

-- All-level extension of QuantitativeMaassPositiveTimeApproximationV1.
open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

local instance (N : ℕ) : ContinuousSMul ℝ (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  IsScalarTower.continuousSMul ℂ

theorem abelPuncturedPositiveTest_operator (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (a : ℝ) (ha : 0<a) (ha1 : a≤1) :
    positiveTimeAbelOperator N (abelPuncturedPositiveTest F hF hr R hR hs a ha ha1)=
      abelPuncturedOperator N F hF hc R hR hs a :=
  positiveTimeTestOfCosh_operator N (fun q => F q-abelBoundaryPart F a q)
    (hF.sub (abelBoundaryPart_smooth F hF a)) (hc.sub (abelBoundaryPart_compact F hc a))
    (abelPuncturedTest_real F hr a) (Real.arcosh (1+a)) R (Real.arcosh_pos (by linarith)) hR
    (abelPuncturedTest_zero_interval F a ha ha1)
    (support_sub_Iic F (abelBoundaryPart F a) _ hs (abelBoundaryPart_support_source F a _ hs))

/-- Every real smooth compact q-test operator is an operator-norm limit of
explicit genuine positive-time test operators. No spectral identity is assumed. -/
theorem abelPuncturedPositiveTest_tendsto {ι : Type*} (l : Filter ι)
    (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hr : ∀ q,star (F q)=F q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha1 : ∀ i,a i≤1) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => positiveTimeAbelOperator N
      (abelPuncturedPositiveTest F hF hr R hR hs (a i) (ha i) (ha1 i))) l
      (𝓝 (abelKernelOperator N F hF hc R hR hs)) := by
  have h := abelPuncturedOperator_tendsto l N F hF hc R hR hs a ha ha1 ha0
  apply h.congr'
  filter_upwards with i
  exact (abelPuncturedPositiveTest_operator N F hF hc hr R hR hs (a i) (ha i) (ha1 i)).symm



#print axioms abelPuncturedPositiveTest_operator
#print axioms abelPuncturedPositiveTest_tendsto

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassAbelOriginalTestRepresentationV1.
open Set Filter MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

theorem regularizedAbelDistribution_originalTest (N : ℕ)
    (ε : ℝ) (f : AutomorphicSpace N) (u : ℝ → AutomorphicSpace N) (hu : Continuous u)
    (huT : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=∫ t,φ t • u t)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Wave.resolventCutoffOperator (friedrichsResolvent N) ε (abelKernelOperator N F hF hc R hR hs f)=
      ∫ t in Ioi (0:ℝ),coshTimeTest F t • u t := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0<a n := by dsimp [a]; positivity
  have ha1 (n : ℕ) : a n≤1 := by
    dsimp [a]
    exact (div_le_one (by positivity)).mpr (by have h := Nat.cast_nonneg (α:=ℝ) n; linarith)
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let ψ (n : ℕ) := abelPuncturedPositiveTest F hF hr R hR hs (a n) (ha n) (ha1 n)
  let P := Wave.resolventCutoffOperator (friedrichsResolvent N) ε
  have he (n : ℕ) : P (positiveTimeAbelOperator N (ψ n) f)=
      ∫ t in Ioi (0:ℝ),coshTimeTest (fun q => F q-abelBoundaryPart F (a n) q) t • u t := by
    have h := huT (ψ n).toSmooth
    change P (abelTestDistribution N (ψ n).toSmooth f)=_ at h
    rw [PositiveTimeTest.toSmooth_operator N (ψ n),PositiveTimeTest.toSmooth_integral (ψ n) u] at h
    rw [h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0<t at ht
    change positiveCoshTest (fun q => F q-abelBoundaryPart F (a n) q) t • u t=_
    simp only [positiveCoshTest,ite_eq_left ht,coshTimeTest]
  have hg := abelPuncturedPositiveTest_tendsto atTop N F hF hc hr R hR hs a ha ha1 ha0
  have hv : Tendsto (fun n => P (positiveTimeAbelOperator N (ψ n) f)) atTop
      (𝓝 (P (abelKernelOperator N F hF hc R hR hs f))) :=
    P.continuous.tendsto _ |>.comp
      ((ContinuousLinearMap.apply ℂ (AutomorphicSpace N) f).continuous.tendsto _ |>.comp hg)
  have hi := coshPuncturedCurve_tendsto atTop F hF R hR hs u hu a ha ha0
  exact tendsto_nhds_unique hv (hi.congr' (Eventually.of_forall (fun n => (he n).symm)))

/-- The recovered actual bounded Cauchy evolution represents the original
q-tests, including those that do not vanish at q=1. -/
theorem regularizedAbelPosition_originalTest (N : ℕ)
    (ε : ℝ) (f : AutomorphicSpace N) (c : AutomorphicSpace N×AutomorphicSpace N)
    (hcT : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Wave.resolventCutoffOperator (friedrichsResolvent N) ε (abelKernelOperator N F hF hc R hR hs f)=
      ∫ t in Ioi (0:ℝ),coshTimeTest F t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t :=
  regularizedAbelDistribution_originalTest N ε f _ (boundedCauchyPosition_continuous _ c)
    hcT F hF hc hr R hR hs



#print axioms regularizedAbelDistribution_originalTest
#print axioms regularizedAbelPosition_originalTest

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassAbelZeroVelocityV1.
open Set Filter MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

theorem regularizedAbel_original_equation (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Wave.resolventCutoffOperator (friedrichsResolvent N) ε
      (abelKernelOperator N (coshTimeOperator F) (coshTimeOperator_smooth F hF)
        (coshTimeOperator_compact F hc) R hR (coshTimeOperator_support F _ hs) f)=
    -regularizedShiftedGenerator N ε
      (Wave.resolventCutoffOperator (friedrichsResolvent N) ε (abelKernelOperator N F hF hc R hR hs f)) := by
  let P := Wave.resolventCutoffOperator (friedrichsResolvent N) ε
  let G := Wave.boundedResolventOperator (friedrichsResolvent N) ε
  have hg := Wave.friedrichsCutoff_generator_on_graph N ε hε
    (abelKernelOperator_graph N F hF hc R hR hs hr f)
  change P ((1/4:ℂ) • abelKernelOperator N F hF hc R hR hs f-
      abelKernelOperator N (coshTimeOperator F) (coshTimeOperator_smooth F hF)
        (coshTimeOperator_compact F hc) R hR (coshTimeOperator_support F _ hs) f)=
    G (P (abelKernelOperator N F hF hc R hR hs f)) at hg
  rw [map_sub,map_smul] at hg
  change P _= -(G (P _)-(1/4:ℂ) • P _)
  rw [← hg]
  abel

/-- A complex bounded Cauchy evolution has the literal q-test boundary flux.
No decay or growth assumption on the evolving vector is required. -/
theorem boundedCauchy_cosh_boundary {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H) (c : H×H)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∫ t in Ioi (0:ℝ),coshTimeOperator F (Real.cosh t) • boundedCauchyPosition (A.restrictScalars ℝ) c t)+
      A (∫ t in Ioi (0:ℝ),coshTimeTest F t • boundedCauchyPosition (A.restrictScalars ℝ) c t)=
      F 1 • (-c.2) := by
  let u := boundedCauchyPosition (A.restrictScalars ℝ) c
  have hu : Continuous u := boundedCauchyPosition_continuous _ c
  have h := compactTest_second_boundary (coshTimeTest F) (hF.comp Real.contDiff_cosh)
    (coshTimeTest_compact F R hR hs) u (boundedCauchyVelocity (A.restrictScalars ℝ) c)
    (fun t => -A (u t)) (boundedCauchyPosition_hasDerivAt _ c)
    (boundedCauchyVelocity_hasDerivAt _ c) (A.continuous.comp hu).neg
  have hi := (coshCurve_integrable F hF R hR hs u hu).integrableOn (s:=Ioi (0:ℝ))
  have hH := (coshCurve_integrable (coshTimeOperator F) (coshTimeOperator_smooth F hF)
    R hR (coshTimeOperator_support F _ hs) u hu).integrableOn (s:=Ioi (0:ℝ))
  simp only [coshTimeTest_second F hF,coshTimeTest_deriv_zero F hF,zero_smul,sub_zero,
    smul_neg,sub_neg_eq_add] at h
  have hm : (∫ t in Ioi (0:ℝ),coshTimeTest F t • A (u t))=
      A (∫ t in Ioi (0:ℝ),coshTimeTest F t • u t) := by
    simpa only [map_smul] using A.integral_comp_comm hi
  have hAi : IntegrableOn (fun t => coshTimeTest F t • A (u t)) (Ioi (0:ℝ)) := by
    change Integrable _ (volume.restrict (Ioi (0:ℝ)))
    simpa only [map_smul] using A.integrable_comp hi
  change IntegrableOn (fun t => coshTimeOperator F (Real.cosh t) • u t) (Ioi (0:ℝ)) at hH
  rw [integral_add hH hAi,hm] at h
  simpa only [coshTimeTest,Real.cosh_zero,(boundedCauchy_initial (A.restrictScalars ℝ) c).2] using h

/-- The actual recovered Abel evolution has zero initial velocity. The
endpoint condition is derived from the original q-test PDE, rather than
assumed from the equation on tests supported strictly inside positive time. -/
theorem regularizedAbelPosition_zero_velocity (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (c : AutomorphicSpace N×AutomorphicSpace N)
    (hcT : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) : c.2=0 := by
  let F := abelCutoff (Real.cosh 1-1)
  have hF : ContDiff ℝ ∞ F := abelCutoff_smooth _
  have hc : HasCompactSupport F := abelCutoff_compact _ (sub_pos.mpr (Real.one_lt_cosh.mpr (by norm_num)))
  have hr : ∀ q,star (F q)=F q := by
    intro q
    simp only [F,abelCutoff,Complex.star_def,Complex.conj_ofReal]
  have hs : Function.support F⊆Iic (Real.cosh 1) := abelCutoff_radius_support 1 (by norm_num)
  let A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
    Wave.boundedResolventOperator (friedrichsResolvent N) ε-(1/4:ℂ) • 1
  have he := regularizedAbel_original_equation N ε hε f F hF hc hr 1 (by norm_num) hs
  rw [regularizedAbelPosition_originalTest N ε f c hcT F hF hc hr 1 (by norm_num) hs,
    regularizedAbelPosition_originalTest N ε f c hcT (coshTimeOperator F)
      (coshTimeOperator_smooth F hF) (coshTimeOperator_compact F hc)
      (coshTimeOperator_real F hr) 1 (by norm_num) (coshTimeOperator_support F _ hs)] at he
  have hb := boundedCauchy_cosh_boundary A c F hF 1 (by norm_num) hs
  change (∫ t in Ioi (0:ℝ),coshTimeTest (coshTimeOperator F) t •
      boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)+
    regularizedShiftedGenerator N ε (∫ t in Ioi (0:ℝ),coshTimeTest F t •
      boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)=F 1 • (-c.2) at hb
  rw [he,neg_add_cancel] at hb
  have hf1 : F 1=1 := by simp only [F,abelCutoff,abelCutoffReal_one,Complex.ofReal_one]
  rw [hf1,one_smul] at hb
  exact neg_eq_zero.mp hb.symm



#print axioms regularizedAbel_original_equation
#print axioms boundedCauchy_cosh_boundary
#print axioms regularizedAbelPosition_zero_velocity

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassAbelCosineRepresentationV1.
open Set Filter MeasureTheory
open scoped Topology ContDiff Distributions InnerProductSpace

namespace QuantitativeMaass.AllLevel

theorem regularizedAbelPosition_eq_wave (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (c : AutomorphicSpace N×AutomorphicSpace N)
    (hcT : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)
    (t : ℝ) (ht : 0≤t) :
    boundedCauchyPosition (regularizedShiftedGenerator N ε) c t=Wave.shiftedQuotientWave N t c.1 := by
  have hc2 := regularizedAbelPosition_zero_velocity N ε hε f c hcT
  apply ext_inner_right ℂ
  have he : (fun a : AutomorphicSpace N => inner ℂ
      (boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) a)=
    (fun a => inner ℂ (Wave.shiftedQuotientWave N t c.1) a) := by
    apply (friedrichsResolvent_denseRange N).equalizer
      (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
    funext z
    have h := regularizedAbelPosition_cauchy_pairing N ε hε f c hcT
      (friedrichsGraph_resolvent N z) t ht
    rw [hc2,neg_zero,inner_zero_left,zero_add,← Wave.shiftedWave_inner] at h
    exact h
  intro a
  exact congrFun he a

/-- The original geometric q-test is the actual spectral packet of the
recovered initial position, with its half-line factor retained. -/
theorem regularizedAbelPosition_packet (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (c : AutomorphicSpace N×AutomorphicSpace N)
    (hcT : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (2:ℂ) • Wave.resolventCutoffOperator (friedrichsResolvent N) ε
      (abelKernelOperator N F hF hc R hR hs f)=coshWavePacket N F hF R hR hs c.1 := by
  rw [regularizedAbelPosition_originalTest N ε f c hcT F hF hc hr R hR hs,
    coshWavePacket_eq_two_half]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change coshTimeTest F t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t=
    coshTimeTest F t • Wave.shiftedQuotientWave N t c.1
  rw [regularizedAbelPosition_eq_wave N ε hε f c hcT t (le_of_lt ht)]



#print axioms regularizedAbelPosition_eq_wave
#print axioms regularizedAbelPosition_packet

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassAbelInitialGraphV1.
open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

theorem abelNormalizedOperator_graph (N : ℕ) (R : ℝ) (hR : 0<R)
    {f h : AutomorphicSpace N} (hfh : FriedrichsGraph N f h) :
    FriedrichsGraph N (abelNormalizedOperator N R hR f) (abelNormalizedOperator N R hR h) := by
  have hg := radialKernelOperator_graph N (abelNormalizedProfile R)
    (abelNormalizedProfile_smooth R hR) R hR.le (abelNormalizedProfile_support R hR)
    (abelNormalizedProfile_real R) f
  have he := radialKernelOperator_on_graph N (abelNormalizedProfile R)
    (abelNormalizedProfile_smooth R hR) R hR.le (abelNormalizedProfile_support R hR)
    (abelNormalizedProfile_real R) hfh
  rw [← he] at hg
  exact hg

theorem abelNormalizedOperator_commute_wave (N : ℕ) (R : ℝ) (hR : 0<R) (t : ℝ) :
    Commute (abelNormalizedOperator N R hR) (Wave.shiftedQuotientWave N t) :=
  radialKernelOperator_commute_wave N (abelNormalizedProfile R) (abelNormalizedProfile_smooth R hR)
    R hR.le (abelNormalizedProfile_support R hR) (abelNormalizedProfile_real R) t

/-- Approximation is strong in both components of every actual graph pair,
so no domain regularity is lost when using the kernels in wave uniqueness. -/
theorem abelNormalizedOperator_graph_tendsto {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (N : ℕ) (R : ι → ℝ) (hR : ∀ i,0<R i) (hlim : Tendsto R l (𝓝 0))
    {f h : AutomorphicSpace N} (hfh : FriedrichsGraph N f h) :
    (∀ i,FriedrichsGraph N (abelNormalizedOperator N (R i) (hR i) f)
      (abelNormalizedOperator N (R i) (hR i) h)) ∧
    Tendsto (fun i => (abelNormalizedOperator N (R i) (hR i) f,
      abelNormalizedOperator N (R i) (hR i) h)) l (𝓝 (f,h)) :=
  ⟨fun i => abelNormalizedOperator_graph N (R i) (hR i) hfh,
    (abelNormalizedOperator_tendsto l N R hR hlim f).prodMk_nhds
      (abelNormalizedOperator_tendsto l N R hR hlim h)⟩



#print axioms abelNormalizedOperator_graph
#print axioms abelNormalizedOperator_commute_wave
#print axioms abelNormalizedOperator_graph_tendsto

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassAbelSpectralIdentificationV1.
open Set Filter MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

theorem regularizedAbelPosition_initial (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (c : AutomorphicSpace N×AutomorphicSpace N)
    (hcT : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) :
    c.1=(2:ℂ) • Wave.resolventCutoffOperator (friedrichsResolvent N) ε f := by
  let R : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hR (n : ℕ) : 0<R n := by dsimp [R]; positivity
  have hR0 : Tendsto R atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let P := Wave.resolventCutoffOperator (friedrichsResolvent N) ε
  have hg : Tendsto (fun n => (2:ℂ) • P (abelNormalizedOperator N (R n) (hR n) f)) atTop
      (𝓝 ((2:ℂ) • P f)) :=
    (P.continuous.tendsto _ |>.comp (abelNormalizedOperator_tendsto atTop N R hR hR0 f)).const_smul (2:ℂ)
  have hw := abelNormalizedWavePacket_tendsto atTop N R hR hR0 c.1
  have he (n : ℕ) : (2:ℂ) • P (abelNormalizedOperator N (R n) (hR n) f)=
      coshWavePacket N (abelNormalizedTest (R n)) (abelNormalizedTest_smooth (R n))
        (R n) (hR n).le (abelNormalizedTest_support (R n) (hR n)) c.1 :=
    regularizedAbelPosition_packet N ε hε f c hcT (abelNormalizedTest (R n))
      (abelNormalizedTest_smooth (R n)) (abelNormalizedTest_compact (R n) (hR n))
      (abelNormalizedTest_real (R n)) (R n) (hR n).le (abelNormalizedTest_support (R n) (hR n))
  exact (tendsto_nhds_unique hg (hw.congr' (Eventually.of_forall (fun n => (he n).symm)))).symm

/-- Literal regularized geometric=spectral identity for every original real
smooth compact q-test. No unknown position or velocity remains. -/
theorem regularizedAbelKernel_eq_coshWavePacket (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Wave.resolventCutoffOperator (friedrichsResolvent N) ε (abelKernelOperator N F hF hc R hR hs f)=
      coshWavePacket N F hF R hR hs (Wave.resolventCutoffOperator (friedrichsResolvent N) ε f) := by
  obtain ⟨c,hcT,_⟩ := regularizedAbelDistribution_cauchy N ε hε f
  have he := regularizedAbelPosition_packet N ε hε f c hcT F hF hc hr R hR hs
  rw [regularizedAbelPosition_initial N ε hε f c hcT,map_smul] at he
  exact (smul_right_injective _ (by norm_num : (2:ℂ)≠0)) he

/-- The actual normalized geometric Abel kernel equals the actual shifted
quotient-wave packet. The cutoff is removed strongly on arbitrary L2 vectors. -/
theorem abelKernelOperator_eq_coshWavePacket (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    abelKernelOperator N F hF hc R hR hs=coshWavePacket N F hF R hR hs := by
  apply ContinuousLinearMap.ext
  intro f
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0<ε n := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hg := Wave.friedrichsCutoff_tendsto atTop N ε (Eventually.of_forall hε) hε0
    (abelKernelOperator N F hF hc R hR hs f)
  have hw := (coshWavePacket N F hF R hR hs).continuous.tendsto _ |>.comp
    (Wave.friedrichsCutoff_tendsto atTop N ε (Eventually.of_forall hε) hε0 f)
  apply tendsto_nhds_unique hg
  apply hw.congr'
  filter_upwards with n
  exact (regularizedAbelKernel_eq_coshWavePacket N (ε n) (hε n) f F hF hc hr R hR hs).symm



#print axioms regularizedAbelPosition_initial
#print axioms regularizedAbelKernel_eq_coshWavePacket
#print axioms abelKernelOperator_eq_coshWavePacket

end QuantitativeMaass.AllLevel

