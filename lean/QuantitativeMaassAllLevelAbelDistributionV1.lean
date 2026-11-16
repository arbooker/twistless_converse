module

public import QuantitativeMaassAllLevelPositiveTimeV1
public import QuantitativeMaassAbelDistributionEquationV1
public import QuantitativeMaassAbelDistributionMomentsV1
public import QuantitativeMaassDistributionCauchyPairV1
public import QuantitativeMaassAbelRegularizedDistributionV1
public import QuantitativeMaassAbelRegularizedSeriesV1
public import QuantitativeMaassAbelRegularizedEvolutionV1
public import QuantitativeMaassTestedFriedrichsGraphV1
public import QuantitativeMaassAbelRegularizedCauchyV1
public import QuantitativeMaassPositiveTestConversionV1
public import QuantitativeMaassPositiveCoshTestV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

-- All-level extension of QuantitativeMaassAbelDistributionEquationV1.
open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions InnerProductSpace

namespace QuantitativeMaass.AllLevel

local instance (N : ℕ) : ContinuousSMul ℝ (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  IsScalarTower.continuousSMul ℂ

theorem abelTestDistribution_graph (N : ℕ)
    (φ : PositiveSmoothTest) (f : AutomorphicSpace N) :
    FriedrichsGraph N (abelTestDistribution N φ f)
      ((1/4:ℂ) • abelTestDistribution N φ f-
        abelTestDistribution N (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ)) f) := by
  have he := positiveTimeAbelOperator_congr N _ _ (positiveSmoothTestToAbel_second φ)
  simpa only [abelTestDistribution_apply,he] using
    positiveTimeAbelOperator_graph N (positiveSmoothTestToAbel φ) f

/-- The distribution values commute with the actual quotient shifted wave;
this follows from the real geometric radial kernel and full-domain graph. -/
theorem abelTestDistribution_commute_wave (N : ℕ)
    (φ : PositiveSmoothTest) (t : ℝ) :
    Commute (abelTestDistribution N φ) (Wave.shiftedQuotientWave N t) := by
  let ψ := positiveSmoothTestToAbel φ
  exact radialKernelOperator_commute_wave N (abelProfile ψ.lift)
    (abelProfile_smooth _ ψ.lift_smooth ψ.lift_compact) ψ.right ψ.right_nonneg
    (abelProfile_support _ _ ψ.lift_support) (abelProfile_real _ ψ.lift_real) t



#print axioms abelTestDistribution_graph
#print axioms abelTestDistribution_commute_wave

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassAbelDistributionMomentsV1.
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

theorem abelTestDistribution_norm_common (N : ℕ)
    (φ : PositiveSmoothTest) (δ R C : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (hs : tsupport φ ⊆ Icc δ R)
    (hb : ∀ t,‖positiveSmoothTestDeriv φ t‖≤C) :
    ‖abelTestDistribution N φ‖≤positiveTimeNormConstant δ R*C := by
  apply positiveTimeAbelOperator_norm_common N (positiveSmoothTestToAbel φ) δ R C hδ hR
  · intro t ht
    apply hs
    apply subset_tsupport
    intro hz
    exact ht (by change (φ t:ℂ)=0; rw [hz,Complex.ofReal_zero])
  · intro t
    have he : deriv (positiveSmoothTestToAbel φ).toFun t=
        ((positiveSmoothTestDeriv φ t:ℝ):ℂ) := by
      rw [positiveSmoothTestDeriv_apply]
      exact ((φ.contDiff.differentiable (by simp) t).hasDerivAt.ofReal_comp).deriv
    rw [he,Complex.norm_real]
    exact hb t

/-- Exponential moment bounds are proved for the literal Abel operator and
its distribution derivative, with constants chosen before the moment index.
No spectral equality or assumed distribution order enters this result. -/
theorem abelTestDistribution_exponential_moments (N : ℕ)
    (φ : PositiveSmoothTest) :
    ∃ C R : ℝ,0≤C ∧ 0≤R ∧ ∀ n,
      ‖abelTestDistribution N (positiveTestPower n φ)‖≤C*R^n ∧
      ‖abelTestDistribution N (positiveSmoothTestDeriv (positiveTestPower n φ))‖≤C*R^n := by
  obtain ⟨C,R,hC,hR,hb⟩ := positiveTestPower_exists_two_derivative_bound φ
  let I := positiveSmoothTestInterval φ
  let K := positiveTimeNormConstant I.left I.right
  have hK : 0≤K := positiveTimeNormConstant_nonneg _ _ I.left_pos
  refine ⟨K*C,R,mul_nonneg hK hC,hR,?_⟩
  intro n
  have hs : tsupport (positiveTestPower n φ) ⊆ Icc I.left I.right :=
    (positiveTestPower_tsupport_subset n φ).trans I.subset
  have hs' := (positiveSmoothTestDeriv_tsupport_subset (positiveTestPower n φ)).trans hs
  constructor
  · calc
      _ ≤ K*(C*R^n) := abelTestDistribution_norm_common N _ I.left I.right (C*R^n)
        I.left_pos I.right_nonneg hs (fun t => (hb n t).2.1)
      _ = _ := by ring
  · calc
      _ ≤ K*(C*R^n) := abelTestDistribution_norm_common N _ I.left I.right (C*R^n)
        I.left_pos I.right_nonneg hs' (fun t => (hb n t).2.2)
      _ = _ := by ring

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Bounded postcomposition preserves the two actual Abel moment bounds.
This will apply to bounded spectral regularizations and vector evaluation. -/
theorem abelTestDistribution_postcomp_moments (N : ℕ)
    (L : (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) →ₗ[ℝ] H)
    (K : ℝ) (hK : 0≤K) (hL : ∀ x,‖L x‖≤K*‖x‖) (φ : PositiveSmoothTest) :
    ∃ C R : ℝ,0≤C ∧ 0≤R ∧ ∀ n,
      ‖L (abelTestDistribution N (positiveTestPower n φ))‖≤C*R^n ∧
      ‖L (abelTestDistribution N (positiveSmoothTestDeriv (positiveTestPower n φ)))‖≤C*R^n := by
  obtain ⟨C,R,hC,hR,hb⟩ := abelTestDistribution_exponential_moments N φ
  refine ⟨K*C,R,mul_nonneg hK hC,hR,?_⟩
  intro n
  constructor
  · calc
      _ ≤ K*‖abelTestDistribution N (positiveTestPower n φ)‖ := hL _
      _ ≤ K*(C*R^n) := mul_le_mul_of_nonneg_left (hb n).1 hK
      _ = _ := by ring
  · calc
      _ ≤ K*‖abelTestDistribution N (positiveSmoothTestDeriv (positiveTestPower n φ))‖ := hL _
      _ ≤ K*(C*R^n) := mul_le_mul_of_nonneg_left (hb n).2 hK
      _ = _ := by ring



#print axioms abelTestDistribution_norm_common
#print axioms abelTestDistribution_exponential_moments
#print axioms abelTestDistribution_postcomp_moments

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassDistributionCauchyPairV1.
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

theorem abelCauchyPair_summable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] (N : ℕ)
    (L : (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) →ₗ[ℝ] H)
    (K : ℝ) (hK : 0≤K) (hL : ∀ x,‖L x‖≤K*‖x‖)
    (A : H →L[ℝ] H) (φ : PositiveSmoothTest) :
    Summable (distributionExpTerm
      (distributionCauchyPair (L.comp (abelTestDistribution N).toLinearMap))
      (distributionCauchyOperator A) φ) := by
  obtain ⟨C,R,hC,hR,hb⟩ := abelTestDistribution_postcomp_moments N L K hK hL φ
  apply distributionExpTerm_summable _ _ φ C R hC hR
  exact distributionCauchyPair_moments _ φ C R hC hR hb



#print axioms abelCauchyPair_summable

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassAbelRegularizedDistributionV1.
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

def regularizedAbelDistribution (N : ℕ) (ε : ℝ) (f : AutomorphicSpace N) :
    PositiveSmoothTest →ₗ[ℝ] AutomorphicSpace N :=
  (abelCutoffEvaluation N ε f).comp (abelTestDistribution N).toLinearMap

def regularizedShiftedGenerator (N : ℕ) (ε : ℝ) :
    AutomorphicSpace N →L[ℝ] AutomorphicSpace N :=
  (Wave.boundedResolventOperator (friedrichsResolvent N) ε-
    (1/4:ℂ) • (1 : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)).restrictScalars ℝ

/-- The actual regularized geometric distribution satisfies a bounded
second-order equation. This follows from its full Friedrichs graph and the
proved cutoff identity, with no spectral representation hypothesis. -/
theorem regularizedAbelDistribution_equation (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N) (φ : PositiveSmoothTest) :
    regularizedAbelDistribution N ε f (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ))=
      -regularizedShiftedGenerator N ε (regularizedAbelDistribution N ε f φ) := by
  let P := Wave.resolventCutoffOperator (friedrichsResolvent N) ε
  let G := Wave.boundedResolventOperator (friedrichsResolvent N) ε
  have hg := Wave.friedrichsCutoff_generator_on_graph N ε hε (abelTestDistribution_graph N φ f)
  change P ((1/4:ℂ) • abelTestDistribution N φ f-
      abelTestDistribution N (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ)) f)=
    G (P (abelTestDistribution N φ f)) at hg
  rw [map_sub,map_smul] at hg
  change P (abelTestDistribution N (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ)) f)=
    -(G (P (abelTestDistribution N φ f))-(1/4:ℂ) • P (abelTestDistribution N φ f))
  rw [← hg]
  abel

/-- The integrating factor for every actual regularized Abel distribution
is constant. Both its moment growth and its differential equation have
been proved above, rather than imposed as additional analytic premises. -/
theorem regularizedAbelDistribution_constant (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N) :
    ∃ hs : ∀ φ,Summable (distributionExpTerm
      (distributionCauchyPair (regularizedAbelDistribution N ε f))
      (distributionCauchyOperator (regularizedShiftedGenerator N ε)) φ),∀ φ,
      distributionExpTransform (distributionCauchyPair (regularizedAbelDistribution N ε f))
        (distributionCauchyOperator (regularizedShiftedGenerator N ε)) hs φ=
      (∫ t,φ t) • distributionExpTransform (distributionCauchyPair (regularizedAbelDistribution N ε f))
        (distributionCauchyOperator (regularizedShiftedGenerator N ε)) hs positiveUnitTest := by
  apply distributionCauchyPair_constant
  · intro φ
    exact abelTestDistribution_postcomp_moments N (abelCutoffEvaluation N ε f) ‖f‖
      (norm_nonneg _) (abelCutoffEvaluation_bound N ε hε f) φ
  · exact regularizedAbelDistribution_equation N ε hε f

/-- Removing the explicit cutoff recovers the actual Abel distribution
strongly on every test and every quotient-L2 input vector. -/
theorem regularizedAbelDistribution_tendsto {ι : Type*} (l : Filter ι)
    (N : ℕ) (ε : ι → ℝ) (hε : ∀ᶠ i in l,0<ε i) (hε0 : Tendsto ε l (𝓝 0))
    (f : AutomorphicSpace N) (φ : PositiveSmoothTest) :
    Tendsto (fun i => regularizedAbelDistribution N (ε i) f φ) l (𝓝 (abelTestDistribution N φ f)) :=
  Wave.friedrichsCutoff_tendsto l N ε hε hε0 _



#print axioms regularizedAbelDistribution
#print axioms regularizedShiftedGenerator
#print axioms regularizedAbelDistribution_equation
#print axioms regularizedAbelDistribution_constant
#print axioms regularizedAbelDistribution_tendsto

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassAbelRegularizedSeriesV1.
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

theorem regularizedAbelDistribution_series (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N) :
    ∃ c : AutomorphicSpace N×AutomorphicSpace N,∀ φ : PositiveSmoothTest,
      distributionCauchyPair (regularizedAbelDistribution N ε f) φ=
        ∑' n,((-1:ℝ)^n*(n.factorial:ℝ)⁻¹) •
          ((∫ t,φ t*t^n) •
            (distributionCauchyOperator (regularizedShiftedGenerator N ε)^n) c) := by
  obtain ⟨hs,_⟩ := regularizedAbelDistribution_constant N ε hε f
  let T := distributionCauchyPair (regularizedAbelDistribution N ε f)
  let B := distributionCauchyOperator (regularizedShiftedGenerator N ε)
  refine ⟨distributionExpTransform T B hs positiveUnitTest,?_⟩
  intro φ
  obtain ⟨C,R,hC,hR,hb⟩ := abelTestDistribution_postcomp_moments N
    (abelCutoffEvaluation N ε f) ‖f‖ (norm_nonneg _) (abelCutoffEvaluation_bound N ε hε f) φ
  have hm : ∀ n,‖T (positiveTestPower n φ)‖≤C*R^n := by
    intro n
    exact max_le (hb n).1 (hb n).2
  have he : ∀ ψ,T (positiveSmoothTestDeriv ψ)=B (T ψ) :=
    distributionCauchyPair_equation _ _ (regularizedAbelDistribution_equation N ε hε f)
  exact distributionExpTransform_series_representation T B hs he φ C R hC hR hm



#print axioms regularizedAbelDistribution_series

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassAbelRegularizedEvolutionV1.
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

theorem regularizedAbelDistribution_evolution (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N) :
    ∃ c : AutomorphicSpace N×AutomorphicSpace N,∀ φ : PositiveSmoothTest,
      distributionCauchyPair (regularizedAbelDistribution N ε f) φ=
        ∫ t,φ t • boundedExpEvolution
          (distributionCauchyOperator (regularizedShiftedGenerator N ε)) c t := by
  obtain ⟨c,hc⟩ := regularizedAbelDistribution_series N ε hε f
  exact ⟨c,fun φ => (hc φ).trans (boundedExpEvolution_test_integral _ c φ)⟩

/-- Both components are identified with the position and minus velocity
integrals. The sign matches the tested derivative in the Cauchy pair. -/
theorem regularizedAbelDistribution_position_velocity (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N) :
    ∃ c : AutomorphicSpace N×AutomorphicSpace N,∀ φ : PositiveSmoothTest,
      regularizedAbelDistribution N ε f φ=
        (∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) ∧
      regularizedAbelDistribution N ε f (positiveSmoothTestDeriv φ)=
        -(∫ t,φ t • boundedCauchyVelocity (regularizedShiftedGenerator N ε) c t) := by
  obtain ⟨c,hc⟩ := regularizedAbelDistribution_evolution N ε hε f
  refine ⟨c,?_⟩
  intro φ
  exact ⟨(congrArg Prod.fst (hc φ)).trans (boundedCauchy_integral_fst _ c φ),
    (congrArg Prod.snd (hc φ)).trans (boundedCauchy_integral_snd _ c φ)⟩



#print axioms regularizedAbelDistribution_evolution
#print axioms regularizedAbelDistribution_position_velocity

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassTestedFriedrichsGraphV1.
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

theorem regularizedAbelPosition_graph (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (c : AutomorphicSpace N×AutomorphicSpace N)
    (hc : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) :
    ∀ t,0≤t → FriedrichsGraph N
      (boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)
      (Wave.boundedResolventOperator (friedrichsResolvent N) ε
        (boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)) := by
  apply friedrichsGraph_of_tested_integrals
    N _ _ (boundedCauchyPosition_continuous _ c)
  intro φ
  rw [← hc φ]
  exact Wave.friedrichsCutoff_graph N ε hε (abelTestDistribution N φ f)



#print axioms regularizedAbelPosition_graph

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassAbelRegularizedCauchyV1.
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions InnerProductSpace

namespace QuantitativeMaass.AllLevel

theorem regularizedAbelPosition_cauchy_pairing (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (c : AutomorphicSpace N×AutomorphicSpace N)
    (hc : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)
    {a b : AutomorphicSpace N} (hab : FriedrichsGraph N a b) (t : ℝ) (ht : 0≤t) :
    inner ℂ (boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) a=
      inner ℂ (-c.2) (Wave.quotientSine N t a)+inner ℂ c.1 (Wave.shiftedQuotientWave N t a) := by
  let u := boundedCauchyPosition (regularizedShiftedGenerator N ε) c
  let v := boundedCauchyVelocity (regularizedShiftedGenerator N ε) c
  let y := fun s => Wave.boundedResolventOperator (friedrichsResolvent N) ε (u s)
  have hu (s : ℝ) (_hs : 0≤s) : HasDerivAt u (v s) s :=
    boundedCauchyPosition_hasDerivAt _ c s
  have hv (s : ℝ) (_hs : 0≤s) : HasDerivAt v ((1/4:ℂ) • u s-y s) s := by
    have he : -regularizedShiftedGenerator N ε (u s)=(1/4:ℂ) • u s-y s := by
      change -(Wave.boundedResolventOperator (friedrichsResolvent N) ε (u s)-(1/4:ℂ) • u s)=_
      abel
    rw [← he]
    exact boundedCauchyVelocity_hasDerivAt _ c s
  have hg : ∀ s,0≤s → FriedrichsGraph N (u s) (y s) :=
    regularizedAbelPosition_graph N ε hε f c hc
  have he := Wave.wave_cauchy_pairing_nonneg N u v y hu hv hg hab t ht
  have h0 := boundedCauchy_initial (regularizedShiftedGenerator N ε) c
  change u 0=c.1 ∧ v 0= -c.2 at h0
  rw [h0.1,h0.2] at he
  exact he

/-- Unconditional actual geometric-to-wave representation at each positive
regularization parameter and for every original quotient-L2 input. The
position/velocity coefficient identification remains a separate endpoint step. -/
theorem regularizedAbelDistribution_cauchy (N : ℕ)
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N) :
    ∃ c : AutomorphicSpace N×AutomorphicSpace N,
      (∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
        ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) ∧
      (∀ a b : AutomorphicSpace N,FriedrichsGraph N a b → ∀ t : ℝ,0≤t →
        inner ℂ (boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) a=
          inner ℂ (-c.2) (Wave.quotientSine N t a)+inner ℂ c.1 (Wave.shiftedQuotientWave N t a)) := by
  obtain ⟨c,hc⟩ := regularizedAbelDistribution_position_velocity N ε hε f
  have hp := fun φ => (hc φ).1
  exact ⟨c,hp,fun a b hab t ht => regularizedAbelPosition_cauchy_pairing N ε hε f c hp hab t ht⟩



#print axioms regularizedAbelPosition_cauchy_pairing
#print axioms regularizedAbelDistribution_cauchy

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassPositiveTestConversionV1.
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

theorem PositiveTimeTest.toSmooth_operator (N : ℕ) (ψ : PositiveTimeTest) :
    abelTestDistribution N ψ.toSmooth=positiveTimeAbelOperator N ψ :=
  positiveSmoothTestToAbel_congr N ψ.toSmooth ψ (fun t => (ψ.toSmooth_coe t).symm)

/-- The real and complex scalar actions agree in this conversion. -/
theorem PositiveTimeTest.toSmooth_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ : PositiveTimeTest) (t : ℝ) (v : H) : ψ.toSmooth t • v=ψ.toFun t • v := by
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),RCLike.ofReal_eq_complex_ofReal,ψ.toSmooth_coe]



#print axioms PositiveTimeTest.toSmooth_operator
#print axioms PositiveTimeTest.toSmooth_smul

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassPositiveCoshTestV1.
open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

theorem positiveTimeTestOfCosh_operator (N : ℕ)
    (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G)
    (hr : ∀ q,star (G q)=G q) (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (hz : ∀ q∈Icc 1 (Real.cosh δ),G q=0) (hs : Function.support G⊆Iic (Real.cosh R)) :
    positiveTimeAbelOperator N (positiveTimeTestOfCosh G hG hr δ R hδ hR hz hs)=
      abelKernelOperator N G hG hc R hR hs := by
  let ψ := positiveTimeTestOfCosh G hG hr δ R hδ hR hz hs
  exact abelKernelOperator_congr_above_one N ψ.lift G ψ.lift_smooth hG ψ.lift_compact hc
    R R hR hR ψ.lift_support hs (coshTestLift_positiveCoshTest G)



#print axioms positiveTimeTestOfCosh_operator

end QuantitativeMaass.AllLevel

