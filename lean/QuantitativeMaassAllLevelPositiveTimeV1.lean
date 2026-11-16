module

public import QuantitativeMaassAllLevelAbelCalculusV1
public import QuantitativeMaassAllLevelAbelInitialV1
public import QuantitativeMaassPositiveTimeTestV1
public import QuantitativeMaassCoshTestBoundV1
public import QuantitativeMaassPositiveTimeContinuityV1
public import QuantitativeMaassPositiveTimeAlgebraV1
public import QuantitativeMaassPositiveTimeTranslateV1
public import QuantitativeMaassPositiveTimeSeminormV1
public import QuantitativeMaassSupportedTimeTestV1
public import QuantitativeMaassSupportedAbelDistributionV1
public import QuantitativeMaassPositiveTestSpaceV1
public import QuantitativeMaassAbelTestDistributionV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

-- All-level extension of QuantitativeMaassPositiveTimeTestV1.
open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

def positiveTimeAbelOperator (N : ℕ) (ψ : PositiveTimeTest) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  abelKernelOperator N ψ.lift ψ.lift_smooth ψ.lift_compact ψ.right ψ.right_nonneg ψ.lift_support

/-- Ordinary second time differentiation now gives the actual operator-valued
weak shifted-wave equation, with membership in the full Friedrichs graph. -/
theorem positiveTimeAbelOperator_graph (N : ℕ) (ψ : PositiveTimeTest)
    (f : AutomorphicSpace N) :
    FriedrichsGraph N (positiveTimeAbelOperator N ψ f)
      ((1/4:ℂ) • positiveTimeAbelOperator N ψ f-positiveTimeAbelOperator N ψ.second f) := by
  have h := abelKernelOperator_graph N ψ.lift ψ.lift_smooth ψ.lift_compact
    ψ.right ψ.right_nonneg ψ.lift_support ψ.lift_real f
  simpa only [positiveTimeAbelOperator,ψ.lift_second,
    show ψ.second.right=ψ.right from rfl] using h



#print axioms positiveTimeAbelOperator
#print axioms positiveTimeAbelOperator_graph

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassCoshTestBoundV1.
open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

theorem positiveTimeAbelOperator_derivative_bound (N : ℕ)
    (ψ : PositiveTimeTest) (C : ℝ) (hb : ∀ t,‖deriv ψ.toFun t‖≤C) :
    ‖positiveTimeAbelOperator N ψ‖≤
      2*Real.pi*((Real.sqrt 2/Real.pi)*((C/Real.sinh ψ.left)*(Real.cosh ψ.right+1))*
        (Real.cosh ψ.right-1)) :=
  abelKernelOperator_derivative_bound N ψ.lift ψ.lift_smooth ψ.lift_compact
    ψ.right ψ.right_nonneg ψ.lift_support (C/Real.sinh ψ.left)
    (coshTestLift_deriv_bound ψ.toFun ψ.smooth ψ.left ψ.right C ψ.left_pos ψ.support hb)



#print axioms positiveTimeAbelOperator_derivative_bound

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassPositiveTimeContinuityV1.
open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

theorem abelKernelOperator_radius (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R S : ℝ) (hR : 0≤R) (hS : 0≤S)
    (hsR : Function.support F⊆Iic (Real.cosh R))
    (hsS : Function.support F⊆Iic (Real.cosh S)) :
    abelKernelOperator N F hF hc R hR hsR=abelKernelOperator N F hF hc S hS hsS := rfl

/-- On one fixed positive time interval, the difference of actual Abel
operators is bounded by the uniform first-derivative difference of the tests. -/
theorem positiveTimeAbelOperator_sub_norm (N : ℕ)
    (ψ θ : PositiveTimeTest) (δ R C : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (hsψ : Function.support ψ.toFun⊆Icc δ R) (hsθ : Function.support θ.toFun⊆Icc δ R)
    (hb : ∀ t,‖deriv ψ.toFun t-deriv θ.toFun t‖≤C) :
    ‖positiveTimeAbelOperator N ψ-positiveTimeAbelOperator N θ‖≤
      2*Real.pi*((Real.sqrt 2/Real.pi)*((C/Real.sinh δ)*(Real.cosh R+1))*(Real.cosh R-1)) := by
  have hsF : Function.support ψ.lift⊆Iic (Real.cosh R) :=
    fun _ h => (coshTestLift_support ψ.toFun δ R hδ hR hsψ h).2
  have hsG : Function.support θ.lift⊆Iic (Real.cosh R) :=
    fun _ h => (coshTestLift_support θ.toFun δ R hδ hR hsθ h).2
  have heψ : positiveTimeAbelOperator N ψ=
      abelKernelOperator N ψ.lift ψ.lift_smooth ψ.lift_compact R hR hsF := rfl
  have heθ : positiveTimeAbelOperator N θ=
      abelKernelOperator N θ.lift θ.lift_smooth θ.lift_compact R hR hsG := rfl
  rw [heψ,heθ]
  apply abelKernelOperator_sub_norm
  intro q
  have hd : deriv (coshTestLift (fun t => ψ.toFun t-θ.toFun t)) q=
      deriv ψ.lift q-deriv θ.lift q := by
    rw [coshTestLift_sub]
    exact deriv_sub (ψ.lift_smooth.differentiable (by simp) q)
      (θ.lift_smooth.differentiable (by simp) q)
  rw [← hd]
  apply coshTestLift_deriv_bound _ (ψ.smooth.sub θ.smooth) δ R C hδ
    (support_sub_interval ψ.toFun θ.toFun δ R hsψ hsθ)
  intro t
  have hd : deriv (fun v => ψ.toFun v-θ.toFun v) t=deriv ψ.toFun t-deriv θ.toFun t :=
    deriv_sub (ψ.smooth.differentiable (by simp) t) (θ.smooth.differentiable (by simp) t)
  rw [hd]
  exact hb t



#print axioms abelKernelOperator_radius
#print axioms positiveTimeAbelOperator_sub_norm

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassPositiveTimeAlgebraV1.
open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

theorem positiveTimeAbelOperator_scaledSub (N : ℕ)
    (ψ θ : PositiveTimeTest) (c : ℝ) :
    positiveTimeAbelOperator N (ψ.scaledSub θ c)=
      (c:ℂ) • positiveTimeAbelOperator N ψ-positiveTimeAbelOperator N θ := by
  let R := max ψ.right θ.right
  have hR : 0≤R := ψ.right_nonneg.trans (le_max_left _ _)
  have hsψ : Function.support ψ.lift⊆Iic (Real.cosh R) := by
    intro q hq
    exact (ψ.lift_support hq).trans
      (Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg ψ.right_nonneg,abs_of_nonneg hR]; exact le_max_left _ _))
  have hsθ : Function.support θ.lift⊆Iic (Real.cosh R) := by
    intro q hq
    exact (θ.lift_support hq).trans
      (Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg θ.right_nonneg,abs_of_nonneg hR]; exact le_max_right _ _))
  let χ := ψ.scaledSub θ c
  have he : χ.lift=(fun q => (c:ℂ)*ψ.lift q-θ.lift q) := coshTestLift_scaledSub _ _ _
  have hp (q : ℝ) : abelProfile χ.lift q=(c:ℂ)*abelProfile ψ.lift q-abelProfile θ.lift q := by
    rw [he,abelProfile_sub _ _ (contDiff_const.mul ψ.lift_smooth) θ.lift_smooth
      ψ.lift_compact.mul_left θ.lift_compact,abelProfile_const_mul]
  apply ContinuousLinearMap.ext
  intro f
  have h := radialKernelOperator_linear N (abelProfile ψ.lift) (abelProfile θ.lift)
    (abelProfile χ.lift) (abelProfile_smooth _ ψ.lift_smooth ψ.lift_compact)
    (abelProfile_smooth _ θ.lift_smooth θ.lift_compact)
    (abelProfile_smooth _ χ.lift_smooth χ.lift_compact) R hR
    (abelProfile_support _ _ hsψ) (abelProfile_support _ _ hsθ)
    (abelProfile_support _ _ χ.lift_support) (c:ℂ) hp f
  exact h



#print axioms positiveTimeAbelOperator_scaledSub

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassPositiveTimeTranslateV1.
open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

theorem positiveTimeAbelOperator_congr (N : ℕ) (ψ θ : PositiveTimeTest)
    (he : ψ.toFun=θ.toFun) : positiveTimeAbelOperator N ψ=positiveTimeAbelOperator N θ := by
  have hl : ψ.lift=θ.lift := congrArg coshTestLift he
  unfold positiveTimeAbelOperator
  simp only [hl]
  rfl

/-- Translation as an everywhere-defined operator curve. Only the open set
where the translated support remains positive is used for differentiation. -/
def translatedPositiveTimeAbelOperator (N : ℕ) (ψ : PositiveTimeTest)
    (x : ℝ) : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  if hx : 0<ψ.left+x then positiveTimeAbelOperator N (ψ.translate x hx) else 0

theorem translatedPositiveTimeAbelOperator_eq (N : ℕ) (ψ : PositiveTimeTest)
    (x : ℝ) (hx : 0<ψ.left+x) :
    translatedPositiveTimeAbelOperator N ψ x=positiveTimeAbelOperator N (ψ.translate x hx) :=
  dite_eq_left hx

theorem translatedPositiveTimeAbelOperator_zero (N : ℕ) (ψ : PositiveTimeTest) :
    translatedPositiveTimeAbelOperator N ψ 0=positiveTimeAbelOperator N ψ := by
  rw [translatedPositiveTimeAbelOperator_eq N ψ 0 (by simpa using ψ.left_pos)]
  exact positiveTimeAbelOperator_congr N _ _ (by ext t; simp [PositiveTimeTest.translate])

/-- A fixed compact positive interval controls every sufficiently nearby
translation. This is the support estimate needed in the operator-norm bounds. -/
theorem PositiveTimeTest.translate_support_near (ψ : PositiveTimeTest) (x : ℝ)
    (hx : 0<ψ.left+x) (z : ℝ) (hz : |z-x|<(ψ.left+x)/2) :
    0<ψ.left+z ∧ Function.support (fun t => ψ.toFun (t-z))⊆
      Icc ((ψ.left+x)/2) (ψ.right+|x|+(ψ.left+x)/2) := by
  have hz' := abs_lt.mp hz
  constructor
  · linarith [hz'.1]
  · intro t ht
    have h := ψ.support ht
    constructor
    · linarith [h.1,hz'.1]
    · linarith [h.2,hz'.2,le_abs_self x]



#print axioms positiveTimeAbelOperator_congr
#print axioms translatedPositiveTimeAbelOperator
#print axioms translatedPositiveTimeAbelOperator_eq
#print axioms translatedPositiveTimeAbelOperator_zero
#print axioms PositiveTimeTest.translate_support_near

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassPositiveTimeSeminormV1.
open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

theorem positiveTimeAbelOperator_norm_common (N : ℕ) (ψ : PositiveTimeTest)
    (δ R C : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (hs : Function.support ψ.toFun⊆Icc δ R) (hb : ∀ t,‖deriv ψ.toFun t‖≤C) :
    ‖positiveTimeAbelOperator N ψ‖≤positiveTimeNormConstant δ R*C := by
  let θ : PositiveTimeTest := {ψ with left:=δ,right:=R,left_pos:=hδ,right_nonneg:=hR,support:=hs}
  rw [positiveTimeAbelOperator_congr N ψ θ rfl]
  have h := positiveTimeAbelOperator_derivative_bound N θ C hb
  change _≤2*Real.pi*((Real.sqrt 2/Real.pi)*((C/Real.sinh δ)*(Real.cosh R+1))*(Real.cosh R-1)) at h
  calc
    _ ≤ _ := h
    _ = _ := by unfold positiveTimeNormConstant; ring

theorem PositiveTimeTest.scaledSub_support (ψ θ : PositiveTimeTest) (c δ R : ℝ)
    (hp : Function.support ψ.toFun⊆Icc δ R) (hq : Function.support θ.toFun⊆Icc δ R) :
    Function.support (ψ.scaledSub θ c).toFun⊆Icc δ R := by
  intro t ht
  by_contra hn
  have hp0 : ψ.toFun t=0 := by by_contra h; exact hn (hp h)
  have hq0 : θ.toFun t=0 := by by_contra h; exact hn (hq h)
  exact ht (by change (c:ℂ)*ψ.toFun t-θ.toFun t=0; rw [hp0,hq0,mul_zero,sub_self])

theorem PositiveTimeTest.scaledSub_deriv (ψ θ : PositiveTimeTest) (c t : ℝ) :
    deriv (ψ.scaledSub θ c).toFun t=(c:ℂ)*deriv ψ.toFun t-deriv θ.toFun t := by
  exact (((ψ.smooth.differentiable (by simp) t).hasDerivAt.const_mul (c:ℂ)).sub
    (θ.smooth.differentiable (by simp) t).hasDerivAt).deriv



#print axioms positiveTimeAbelOperator_norm_common
#print axioms PositiveTimeTest.scaledSub_support
#print axioms PositiveTimeTest.scaledSub_deriv

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassSupportedTimeTestV1.
open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

def supportedTimeAbelOperator (N : ℕ) (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (φ : SupportedTimeTest δ R) : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  positiveTimeAbelOperator N (supportedPositiveTimeTest δ R hδ hR φ)

theorem supportedTimeAbelOperator_scaledSub (N : ℕ)
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) (φ ψ : SupportedTimeTest δ R) (c : ℝ) :
    supportedTimeAbelOperator N δ R hδ hR (c • φ-ψ)=
      c • supportedTimeAbelOperator N δ R hδ hR φ-supportedTimeAbelOperator N δ R hδ hR ψ := by
  have he : (supportedPositiveTimeTest δ R hδ hR (c • φ-ψ)).toFun=
      ((supportedPositiveTimeTest δ R hδ hR φ).scaledSub
        (supportedPositiveTimeTest δ R hδ hR ψ) c).toFun := by
    funext t
    change ((c*φ t-ψ t:ℝ):ℂ)=(c:ℂ)*(φ t:ℂ)-(ψ t:ℂ)
    push_cast
    rfl
  unfold supportedTimeAbelOperator
  rw [positiveTimeAbelOperator_congr N _ _ he,positiveTimeAbelOperator_scaledSub]
  rfl

theorem supportedTimeAbelOperator_bound (N : ℕ)
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) (φ : SupportedTimeTest δ R) :
    ‖supportedTimeAbelOperator N δ R hδ hR φ‖≤positiveTimeNormConstant δ R*
      ContDiffMapSupportedIn.seminorm ℝ ℝ ℝ ⊤ (positiveTimeCompact δ R) 1 φ :=
  positiveTimeAbelOperator_norm_common N (supportedPositiveTimeTest δ R hδ hR φ)
    δ R _ hδ hR (supportedPositiveTimeTest δ R hδ hR φ).support
    (supportedPositiveTimeTest_deriv_bound δ R hδ hR φ)



#print axioms supportedTimeAbelOperator
#print axioms supportedTimeAbelOperator_scaledSub
#print axioms supportedTimeAbelOperator_bound

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassSupportedAbelDistributionV1.
open Set Filter
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

local instance (N : ℕ) :
    ContinuousSMul ℝ (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  IsScalarTower.continuousSMul ℂ

private theorem map_zero_of_scaledSub {E G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup G] [Module ℝ G] (A : E → G)
    (h : ∀ (f g : E) (c : ℝ),A (c • f-g)=c • A f-A g) : A 0=0 := by
  simpa only [one_smul,sub_self] using h 0 0 1

private theorem map_smul_of_scaledSub {E G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup G] [Module ℝ G] (A : E → G)
    (h : ∀ (f g : E) (c : ℝ),A (c • f-g)=c • A f-A g) (c : ℝ) (f : E) : A (c • f)=c • A f := by
  simpa only [map_zero_of_scaledSub A h,sub_zero] using h f 0 c

private theorem map_add_of_scaledSub {E G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup G] [Module ℝ G] (A : E → G)
    (h : ∀ (f g : E) (c : ℝ),A (c • f-g)=c • A f-A g) (f g : E) : A (f+g)=A f+A g := by
  have hn : A (-g)= -A g := by
    simpa only [neg_one_smul] using map_smul_of_scaledSub A h (-1) g
  simpa only [one_smul,sub_neg_eq_add,hn] using h f (-g) 1

theorem supportedTimeAbelOperator_zero (N : ℕ)
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) :
    supportedTimeAbelOperator N δ R hδ hR 0=0 :=
  map_zero_of_scaledSub (supportedTimeAbelOperator N δ R hδ hR) (supportedTimeAbelOperator_scaledSub N δ R hδ hR)

theorem supportedTimeAbelOperator_smul (N : ℕ)
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) (c : ℝ) (φ : SupportedTimeTest δ R) :
    supportedTimeAbelOperator N δ R hδ hR (c • φ)=
      c • supportedTimeAbelOperator N δ R hδ hR φ :=
  map_smul_of_scaledSub (supportedTimeAbelOperator N δ R hδ hR) (supportedTimeAbelOperator_scaledSub N δ R hδ hR) c φ

theorem supportedTimeAbelOperator_add (N : ℕ)
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) (φ ψ : SupportedTimeTest δ R) :
    supportedTimeAbelOperator N δ R hδ hR (φ+ψ)=
      supportedTimeAbelOperator N δ R hδ hR φ+supportedTimeAbelOperator N δ R hδ hR ψ :=
  map_add_of_scaledSub (supportedTimeAbelOperator N δ R hδ hR) (supportedTimeAbelOperator_scaledSub N δ R hδ hR) φ ψ

/-- The actual geometric Abel test map is a continuous real-linear map on
fixed-support smooth tests. Its continuity is proved by the first-derivative
seminorm estimate, so it can be used in distribution and smoothing arguments. -/
def supportedAbelDistribution (N : ℕ)
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) :
    SupportedTimeTest δ R →L[ℝ] (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  ContDiffMapSupportedIn.mkCLMtoNormedSpace ℝ
    (supportedTimeAbelOperator N δ R hδ hR)
    (supportedTimeAbelOperator_add N δ R hδ hR)
    (supportedTimeAbelOperator_smul N δ R hδ hR)
    ⟨{1},positiveTimeNormConstant δ R,positiveTimeNormConstant_nonneg δ R hδ,
      fun φ => by simpa only [Finset.sup_singleton] using
        supportedTimeAbelOperator_bound N δ R hδ hR φ⟩

theorem supportedAbelDistribution_apply (N : ℕ)
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) (φ : SupportedTimeTest δ R) :
    supportedAbelDistribution N δ R hδ hR φ=supportedTimeAbelOperator N δ R hδ hR φ := rfl



#print axioms supportedTimeAbelOperator_zero
#print axioms supportedTimeAbelOperator_smul
#print axioms supportedTimeAbelOperator_add
#print axioms supportedAbelDistribution
#print axioms supportedAbelDistribution_apply

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassPositiveTestSpaceV1.
open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

theorem positiveSmoothTestToAbel_congr (N : ℕ)
    (φ : PositiveSmoothTest) (ψ : PositiveTimeTest) (h : ∀ t,ψ.toFun t=(φ t:ℂ)) :
    positiveTimeAbelOperator N (positiveSmoothTestToAbel φ)=positiveTimeAbelOperator N ψ :=
  positiveTimeAbelOperator_congr N _ _ (funext (fun t => (h t).symm))



#print axioms positiveSmoothTestToAbel_congr

end QuantitativeMaass.AllLevel

-- All-level extension of QuantitativeMaassAbelTestDistributionV1.
open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass.AllLevel

local instance (N : ℕ) :
    ContinuousSMul ℝ (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  IsScalarTower.continuousSMul ℂ

local instance (N : ℕ) :
    LocallyConvexSpace ℝ (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  by
    convert! (NormedSpace.toLocallyConvexSpace' (E:=AutomorphicSpace N →L[ℂ] AutomorphicSpace N) ℂ) using 1

def compactAbelDistribution (N : ℕ)
    (K : Compacts ℝ) (hK : (K:Set ℝ)⊆Ioi 0) :
    𝓓_{K}(ℝ,ℝ) →L[ℝ] (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  let I := positiveCompactInterval K hK
  (supportedAbelDistribution N I.left I.right I.left_pos I.right_nonneg).comp
    (ContDiffMapSupportedIn.monoCLM ℝ)

theorem compactAbelDistribution_apply (N : ℕ)
    (K : Compacts ℝ) (hK : (K:Set ℝ)⊆Ioi 0) (φ : 𝓓_{K}(ℝ,ℝ)) :
    compactAbelDistribution N K hK φ=
      positiveTimeAbelOperator N (positiveSmoothTestToAbel (TestFunction.ofSupportedIn hK φ)) := by
  let I := positiveCompactInterval K hK
  change positiveTimeAbelOperator N
    (supportedPositiveTimeTest I.left I.right I.left_pos I.right_nonneg
      (ContDiffMapSupportedIn.monoCLM ℝ φ))=_
  symm
  apply positiveSmoothTestToAbel_congr
  intro t
  have hk : K≤positiveTimeCompact I.left I.right := I.subset
  have he : ((ContDiffMapSupportedIn.monoCLM ℝ φ : SupportedTimeTest I.left I.right):ℝ → ℝ)=φ := by
    rw [ContDiffMapSupportedIn.monoCLM_apply,ite_eq_left ⟨le_rfl,hk⟩]
  change (((ContDiffMapSupportedIn.monoCLM ℝ φ : SupportedTimeTest I.left I.right) t):ℂ)=(φ t:ℂ)
  rw [congrFun he t]

/-- The actual Abel test operator, now as a distribution on the whole
positive half-line with its canonical LF topology. Continuity is checked on
every compact support, using the proved first-derivative operator bound. -/
def abelTestDistribution (N : ℕ) :
    PositiveSmoothTest →L[ℝ] (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :=
  TestFunction.limitCLM ℝ
    (fun φ => positiveTimeAbelOperator N (positiveSmoothTestToAbel φ))
    (compactAbelDistribution N)
    (fun K hK φ => (compactAbelDistribution_apply N K hK φ).symm)

theorem abelTestDistribution_apply (N : ℕ) (φ : PositiveSmoothTest) :
    abelTestDistribution N φ=positiveTimeAbelOperator N (positiveSmoothTestToAbel φ) := rfl



#print axioms compactAbelDistribution
#print axioms compactAbelDistribution_apply
#print axioms abelTestDistribution
#print axioms abelTestDistribution_apply

end QuantitativeMaass.AllLevel

