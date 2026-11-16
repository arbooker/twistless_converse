module

public import QuantitativeMaassAllLevelRadialGraphV1
public import QuantitativeMaassAllLevelRadialCommuteV1
public import QuantitativeMaassRadialKernelLinearV1
public import QuantitativeMaassAbelKernelGraphV1
public import QuantitativeMaassAbelOperatorBoundV1
public import QuantitativeMaassAbelOperatorLinearV1
public import QuantitativeMaassAbelAboveOneCongruenceV1
public import QuantitativeMaassAbelShrinkingSupportV1
public import QuantitativeMaassAbelBoundaryLimitV1
public import QuantitativeMaassAbelPuncturedLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

-- All-level extension of RadialKernelLinear.
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

theorem radialPoincareKernel_linear (N : ℕ) (g h j : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (R : ℝ) (hR : 0≤R)
    (hsg : Function.support g⊆Iic (Real.cosh R))
    (hsh : Function.support h⊆Iic (Real.cosh R))
    (c : ℂ) (he : ∀ q,j q=c*g q-h q) (x y : ℍ) :
    radialPoincareKernel N j x y=c*radialPoincareKernel N g x y-radialPoincareKernel N h x y := by
  have hgS : Summable (fun γ : gamma N => upperFunction (radialFunction g x) (γ•y)) :=
    summable_of_hasFiniteSupport (compact_seed_point_support _ (radialSeed g hg x R hR hsg).compact y)
  have hhS : Summable (fun γ : gamma N => upperFunction (radialFunction h x) (γ•y)) :=
    summable_of_hasFiniteSupport (compact_seed_point_support _ (radialSeed h hh x R hR hsh).compact y)
  simp only [radialFunction_upper] at hgS hhS
  simp only [radialPoincareKernel,poincareSum,radialFunction_upper,he]
  rw [(hgS.mul_left c).tsum_sub hhS,tsum_mul_left]

/-- Linearity in the literal radial profile follows from finite group
sums and the proved almost-everywhere absolute integrability of each row. -/
theorem radialKernelOperator_linear (N : ℕ) (g h j : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (hj : ContDiff ℝ ∞ j)
    (R : ℝ) (hR : 0≤R)
    (hsg : Function.support g⊆Iic (Real.cosh R))
    (hsh : Function.support h⊆Iic (Real.cosh R))
    (hsj : Function.support j⊆Iic (Real.cosh R))
    (c : ℂ) (he : ∀ q,j q=c*g q-h q) (f : AutomorphicSpace N) :
    radialKernelOperator N j hj R hR hsj f=
      c • radialKernelOperator N g hg R hR hsg f-radialKernelOperator N h hh R hR hsh f := by
  apply Subtype.ext
  apply Lp.ext
  let K := radialKernelOperator N g hg R hR hsg f
  let H := radialKernelOperator N h hh R hR hsh f
  filter_upwards [radialKernelOperator_coeFn N j hj R hR hsj f,
    radialKernelOperator_coeFn N g hg R hR hsg f,
    radialKernelOperator_coeFn N h hh R hR hsh f,
    Lp.coeFn_sub (c • K.val) H.val,Lp.coeFn_smul c K.val,
    (radialKernelData N g hg R hR hsg).output_row_ae f.val
      (Lp.stronglyMeasurable f.val).measurable (Lp.memLp f.val),
    (radialKernelData N h hh R hR hsh).output_row_ae f.val
      (Lp.stronglyMeasurable f.val).measurable (Lp.memLp f.val)] with x hx hgx hhx hsub hsmul hig hih
  change _=(c • K.val-H.val) x
  rw [hsub,Pi.sub_apply,hsmul]
  change _=c*K.val x-H.val x
  rw [hx,hgx,hhx]
  simp_rw [radialPoincareKernel_linear N g h j hg hh R hR hsg hsh c he,sub_mul,mul_assoc]
  have hig' : Integrable (fun y => radialPoincareKernel N g x y*f.val y) (quotientMeasure N) := hig.1
  have hih' : Integrable (fun y => radialPoincareKernel N h x y*f.val y) (quotientMeasure N) := hih.1
  rw [integral_sub (hig'.const_mul c) hih',integral_const_mul]

#print axioms radialPoincareKernel_linear
#print axioms radialKernelOperator_linear

end QuantitativeMaass.AllLevel

-- All-level extension of AbelKernelGraph.
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff ComplexConjugate

namespace QuantitativeMaass.AllLevel

theorem coshTimeOperator_support (F : ℝ → ℂ) (B : ℝ)
    (hs : Function.support F⊆Iic B) : Function.support (coshTimeOperator F)⊆Iic B := by
  have ht : tsupport F⊆Iic B := closure_minimal hs isClosed_Iic
  have h1 : Function.support (deriv F)⊆Iic B := support_deriv_subset.trans ht
  have h2 : Function.support (deriv (deriv F))⊆Iic B :=
    support_deriv_subset.trans (tsupport_deriv_subset.trans ht)
  intro q hq
  by_contra hn
  have hd1 : deriv F q=0 := by
    by_contra h
    exact hn (h1 h)
  have hd2 : deriv (deriv F) q=0 := by
    by_contra h
    exact hn (h2 h)
  exact hq (by simp [coshTimeOperator,hd1,hd2])

theorem abelProfile_real (F : ℝ → ℂ) (hr : ∀ q,star (F q)=F q) (q : ℝ) :
    star (abelProfile F q)=abelProfile F q := by
  have hi : star (abelIntegral (deriv F) q)=abelIntegral (deriv F) q := by
    change conj (∫ s in Ioi (0:ℝ),deriv F (q+s^2))=∫ s in Ioi (0:ℝ),deriv F (q+s^2)
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with s
    exact deriv_real_profile F hr (q+s^2)
  simp [abelProfile,star_mul,hi]
  ring

/-- The normalized geometric Abel operator takes arbitrary quotient L2
inputs into the actual Friedrichs domain and satisfies the shifted wave
identity at the level of bounded test-function operators. -/
theorem abelKernelOperator_graph (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (hr : ∀ q,star (F q)=F q) (f : AutomorphicSpace N) :
    FriedrichsGraph N (abelKernelOperator N F hF hc R hR hs f)
      ((1/4:ℂ) • abelKernelOperator N F hF hc R hR hs f-
        abelKernelOperator N (coshTimeOperator F) (coshTimeOperator_smooth F hF)
          (coshTimeOperator_compact F hc) R hR (coshTimeOperator_support F _ hs) f) := by
  have hA := abelProfile_smooth F hF hc
  have hsA := abelProfile_support F _ hs
  have hH := abelProfile_smooth (coshTimeOperator F) (coshTimeOperator_smooth F hF)
    (coshTimeOperator_compact F hc)
  have hsH := abelProfile_support (coshTimeOperator F) _ (coshTimeOperator_support F _ hs)
  have hg := radialKernelOperator_graph N (abelProfile F) hA R hR hsA (abelProfile_real F hr) f
  have he := radialKernelOperator_linear N (abelProfile F) (abelProfile (coshTimeOperator F))
    (radialLaplacianProfile (abelProfile F)) hA hH (radialLaplacianProfile_smooth _ hA)
    R hR hsA hsH (radialLaplacianProfile_support _ _ hsA) (1/4:ℂ)
    (abelProfile_laplacian F hF hc) f
  rw [he] at hg
  exact hg

#print axioms coshTimeOperator_support
#print axioms abelProfile_real
#print axioms abelKernelOperator_graph

end QuantitativeMaass.AllLevel

-- All-level extension of AbelOperatorBound.
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

/-- An elementary uniform bound for the desingularized Abel integral. -/
theorem abelIntegral_norm_bound (f : ℝ → ℂ) (B C : ℝ) (hB : 1≤B)
    (hs : Function.support f⊆Iic B) (hb : ∀ q,‖f q‖≤C) (q : ℝ) (hq : 1≤q) :
    ‖abelIntegral f q‖≤C*(B+1) := by
  have he : abelIntegral f q=∫ s in Ioc (0:ℝ) (B+1),f (q+s^2) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun _ h => h.1)
    intro s hs'
    have hlow : 0<s := hs'.1
    have hhigh : B+1<s := by
      by_contra hn
      exact hs'.2 ⟨hlow,le_of_not_gt hn⟩
    by_contra hn
    have hh := hs hn
    change q+s^2≤B at hh
    nlinarith [sq_nonneg (s-1)]
  rw [he]
  have h := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Ioc (0:ℝ) (B+1))
    (f:=fun s => f (q+s^2)) (by simp) (fun s _ => hb (q+s^2))
  simpa only [Real.volume_real_Ioc_of_le (by linarith : 0≤B+1),sub_zero] using h

theorem abelProfile_norm_bound (F : ℝ → ℂ) (B C : ℝ) (hB : 1≤B)
    (hs : Function.support F⊆Iic B) (hb : ∀ q,‖deriv F q‖≤C) (q : ℝ) (hq : 1≤q) :
    ‖abelProfile F q‖≤(Real.sqrt 2/Real.pi)*(C*(B+1)) := by
  have hs' : Function.support (deriv F)⊆Iic B :=
    support_deriv_subset.trans (closure_minimal hs isClosed_Iic)
  have h := abelIntegral_norm_bound (deriv F) B C hB hs' hb q hq
  rw [abelProfile,norm_mul,norm_neg]
  have hn : ‖(Real.sqrt 2/Real.pi:ℂ)‖=Real.sqrt 2/Real.pi := by
    rw [← Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le)]
  rw [hn]
  exact mul_le_mul_of_nonneg_left h (div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le)

/-- The actual Schur mass is controlled by one derivative seminorm of the
compact q-test. This supplies continuity needed for test translations. -/
theorem abelProfile_absolute_mass_bound (F : ℝ → ℂ) (B C : ℝ) (hB : 1≤B)
    (hs : Function.support F⊆Iic B) (hb : ∀ q,‖deriv F q‖≤C) :
    2*Real.pi*(∫ q in Ioi (1:ℝ),‖abelProfile F q‖)≤
      2*Real.pi*((Real.sqrt 2/Real.pi)*(C*(B+1))*(B-1)) := by
  have he : (∫ q in Ioi (1:ℝ),‖abelProfile F q‖)=∫ q in Ioc (1:ℝ) B,‖abelProfile F q‖ := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun _ h => h.1)
    intro q hq
    have hhigh : B<q := by
      by_contra hn
      exact hq.2 ⟨hq.1,le_of_not_gt hn⟩
    have hz : abelProfile F q=0 := by
      by_contra hn
      exact (not_le_of_gt hhigh) (abelProfile_support F B hs hn)
    rw [hz,norm_zero]
  have h := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Ioc (1:ℝ) B)
    (f:=fun q => ‖abelProfile F q‖) (by simp) (fun q hq => by
      rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
      exact abelProfile_norm_bound F B C hB hs hb q hq.1.le)
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),
    Real.volume_real_Ioc_of_le hB] at h
  rw [he]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem abelKernelOperator_derivative_bound (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (C : ℝ) (hb : ∀ q,‖deriv F q‖≤C) :
    ‖abelKernelOperator N F hF hc R hR hs‖≤
      2*Real.pi*((Real.sqrt 2/Real.pi)*(C*(Real.cosh R+1))*(Real.cosh R-1)) :=
  (radialKernelOperator_norm N (abelProfile F) (abelProfile_smooth F hF hc) R hR
    (abelProfile_support F _ hs)).trans
      (abelProfile_absolute_mass_bound F _ C (Real.one_le_cosh R) hs hb)

#print axioms abelIntegral_norm_bound
#print axioms abelProfile_norm_bound
#print axioms abelProfile_absolute_mass_bound
#print axioms abelKernelOperator_derivative_bound

end QuantitativeMaass.AllLevel

-- All-level extension of AbelOperatorLinear.
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

theorem support_sub_Iic (F G : ℝ → ℂ) (B : ℝ)
    (hF : Function.support F⊆Iic B) (hG : Function.support G⊆Iic B) :
    Function.support (fun q => F q-G q)⊆Iic B := by
  intro q hq
  by_contra hn
  have hf : F q=0 := by by_contra h;exact hn (hF h)
  have hg : G q=0 := by by_contra h;exact hn (hG h)
  exact hq (by dsimp only;rw [hf,hg,sub_self])

theorem abelProfile_sub (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) (q : ℝ) :
    abelProfile (fun v => F v-G v) q=abelProfile F q-abelProfile G q := by
  have hd : deriv (fun v => F v-G v)=(fun v => deriv F v-deriv G v) := by
    funext v
    exact deriv_sub (hF.differentiable (by simp) v) (hG.differentiable (by simp) v)
  simp only [abelProfile,hd,abelIntegral]
  rw [integral_sub
    (quadratic_integrable (deriv F) (contDiff_infty_iff_deriv.mp hF).2.continuous hcF.deriv q).integrableOn
    (quadratic_integrable (deriv G) (contDiff_infty_iff_deriv.mp hG).2.continuous hcG.deriv q).integrableOn]
  ring

/-- Subtraction of test functions is literal subtraction of the constructed
quotient operators; both integral interchanges use proved integrability. -/
theorem abelKernelOperator_sub (N : ℕ)
    (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (R : ℝ) (hR : 0≤R) (hsF : Function.support F⊆Iic (Real.cosh R))
    (hsG : Function.support G⊆Iic (Real.cosh R)) :
    abelKernelOperator N (fun q => F q-G q) (hF.sub hG) (hcF.sub hcG) R hR
      (support_sub_Iic F G _ hsF hsG)=
        abelKernelOperator N F hF hcF R hR hsF-abelKernelOperator N G hG hcG R hR hsG := by
  apply ContinuousLinearMap.ext
  intro f
  have h := radialKernelOperator_linear N (abelProfile F) (abelProfile G)
    (abelProfile (fun q => F q-G q))
    (abelProfile_smooth F hF hcF) (abelProfile_smooth G hG hcG)
    (abelProfile_smooth _ (hF.sub hG) (hcF.sub hcG)) R hR
    (abelProfile_support F _ hsF) (abelProfile_support G _ hsG)
    (abelProfile_support _ _ (support_sub_Iic F G _ hsF hsG)) 1
    (fun q => by simpa only [one_mul] using abelProfile_sub F G hF hG hcF hcG q) f
  simpa only [one_smul,sub_apply,abelKernelOperator] using h

/-- Uniform first-derivative convergence of compact q-tests controls the
operator-norm difference, rather than merely pointwise kernel convergence. -/
theorem abelKernelOperator_sub_norm (N : ℕ)
    (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (R : ℝ) (hR : 0≤R) (hsF : Function.support F⊆Iic (Real.cosh R))
    (hsG : Function.support G⊆Iic (Real.cosh R))
    (C : ℝ) (hb : ∀ q,‖deriv F q-deriv G q‖≤C) :
    ‖abelKernelOperator N F hF hcF R hR hsF-abelKernelOperator N G hG hcG R hR hsG‖≤
      2*Real.pi*((Real.sqrt 2/Real.pi)*(C*(Real.cosh R+1))*(Real.cosh R-1)) := by
  rw [← abelKernelOperator_sub N F G hF hG hcF hcG R hR hsF hsG]
  apply abelKernelOperator_derivative_bound
  intro q
  have hd : deriv (fun v => F v-G v) q=deriv F q-deriv G q :=
    deriv_sub (hF.differentiable (by simp) q) (hG.differentiable (by simp) q)
  rw [hd]
  exact hb q

#print axioms abelProfile_sub
#print axioms abelKernelOperator_sub
#print axioms abelKernelOperator_sub_norm

end QuantitativeMaass.AllLevel

-- All-level extension of AbelAboveOneCongruence.
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

/-- The Abel profile above one depends only on the test strictly above one. -/
theorem abelProfile_congr_above_one (F G : ℝ → ℂ) (he : ∀ q,1<q → F q=G q)
    (q : ℝ) (hq : 1≤q) : abelProfile F q=abelProfile G q := by
  have hd (v : ℝ) (hv : 1<v) : deriv F v=deriv G v := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioi_mem_nhds hv] with w hw
    exact he w hw
  unfold abelProfile abelIntegral
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  apply hd
  have hs' : 0<s := hs
  nlinarith [sq_pos_of_pos hs']

/-- Radial kernels only evaluate their profiles at cosh distances, hence
values below one have no effect on the actual periodized kernel. -/
theorem radialPoincareKernel_congr_above_one (N : ℕ) (g h : ℝ → ℂ)
    (he : ∀ q,1≤q → g q=h q) (x y : ℍ) :
    radialPoincareKernel N g x y=radialPoincareKernel N h x y := by
  simp only [radialPoincareKernel,poincareSum,radialFunction_upper]
  apply tsum_congr
  intro γ
  exact he _ (Real.one_le_cosh _)

theorem radialKernelOperator_congr_above_one (N : ℕ)
    (g h : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (R S : ℝ) (hR : 0≤R) (hS : 0≤S)
    (hsg : Function.support g⊆Iic (Real.cosh R))
    (hsh : Function.support h⊆Iic (Real.cosh S))
    (he : ∀ q,1≤q → g q=h q) :
    radialKernelOperator N g hg R hR hsg=radialKernelOperator N h hh S hS hsh := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [radialKernelOperator_coeFn N g hg R hR hsg f,
    radialKernelOperator_coeFn N h hh S hS hsh f] with x hx hy
  rw [hx,hy]
  apply integral_congr_ae
  filter_upwards with y
  rw [radialPoincareKernel_congr_above_one N g h he x y]

/-- A change of smooth extension below q=1 leaves the constructed geometric
operator unchanged, even when its two support-radius witnesses differ. -/
theorem abelKernelOperator_congr_above_one (N : ℕ)
    (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (R S : ℝ) (hR : 0≤R) (hS : 0≤S)
    (hsF : Function.support F⊆Iic (Real.cosh R))
    (hsG : Function.support G⊆Iic (Real.cosh S))
    (he : ∀ q,1<q → F q=G q) :
    abelKernelOperator N F hF hcF R hR hsF=abelKernelOperator N G hG hcG S hS hsG :=
  radialKernelOperator_congr_above_one N (abelProfile F) (abelProfile G)
    (abelProfile_smooth F hF hcF) (abelProfile_smooth G hG hcG) R S hR hS
    (abelProfile_support F _ hsF) (abelProfile_support G _ hsG)
    (abelProfile_congr_above_one F G he)

#print axioms abelProfile_congr_above_one
#print axioms radialKernelOperator_congr_above_one
#print axioms abelKernelOperator_congr_above_one

end QuantitativeMaass.AllLevel

-- All-level extension of AbelShrinkingSupport.
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

/-- A derivative of size C/(B-1) still gives a vanishing operator bound
when the radial q-support shrinks to one. -/
theorem abelKernelOperator_shrinking_support_bound (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hsR : Function.support F⊆Iic (Real.cosh R))
    (B C : ℝ) (hB : 1<B) (hs : Function.support F⊆Iic B)
    (hb : ∀ q,‖deriv F q‖≤C/(B-1)) :
    ‖abelKernelOperator N F hF hc R hR hsR‖≤2*Real.sqrt 2*C*Real.sqrt (B-1) := by
  have h := (radialKernelOperator_norm N (abelProfile F) (abelProfile_smooth F hF hc)
    R hR (abelProfile_support F _ hsR)).trans
      (abelProfile_small_radius_mass_bound F B (C/(B-1)) hB.le hs hb)
  calc
    _ ≤ _ := h
    _ = _ := by
      field_simp [Real.pi_ne_zero,ne_of_gt (sub_pos.mpr hB)]

/-- Shrinking q-support and the explicit reciprocal-width derivative bound
force operator-norm convergence to zero. The tests themselves may vary. -/
theorem abelKernelOperator_shrinking_support_tendsto {ι : Type*} (l : Filter ι)
    (N : ℕ) (F : ι → ℝ → ℂ) (hF : ∀ i,ContDiff ℝ ∞ (F i))
    (hc : ∀ i,HasCompactSupport (F i)) (R : ι → ℝ) (hR : ∀ i,0≤R i)
    (hsR : ∀ i,Function.support (F i)⊆Iic (Real.cosh (R i)))
    (B : ι → ℝ) (C : ℝ) (hB : ∀ i,1<B i) (hlim : Tendsto B l (𝓝 1))
    (hs : ∀ i,Function.support (F i)⊆Iic (B i))
    (hb : ∀ i q,‖deriv (F i) q‖≤C/(B i-1)) :
    Tendsto (fun i => abelKernelOperator N (F i) (hF i) (hc i) (R i) (hR i) (hsR i)) l (𝓝 0) := by
  apply (tendsto_zero_iff_norm_tendsto_zero
    (f := fun i => abelKernelOperator N (F i) (hF i) (hc i) (R i) (hR i) (hsR i))).mpr
  have ht : Tendsto (fun i => 2*Real.sqrt 2*C*Real.sqrt (B i-1)) l (𝓝 0) := by
    simpa only [sub_self,Real.sqrt_zero,mul_zero] using
      ((hlim.sub_const 1).sqrt).const_mul (2*Real.sqrt 2*C)
  exact squeeze_zero
    (fun i => norm_nonneg (abelKernelOperator N (F i) (hF i) (hc i) (R i) (hR i) (hsR i)))
    (fun i => abelKernelOperator_shrinking_support_bound N (F i) (hF i) (hc i)
      (R i) (hR i) (hsR i) (B i) C (hB i) (hs i) (hb i)) ht

#print axioms abelKernelOperator_shrinking_support_bound
#print axioms abelKernelOperator_shrinking_support_tendsto

end QuantitativeMaass.AllLevel

-- All-level extension of AbelBoundaryLimit.
open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

def abelBoundaryOperator (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (a : ℝ) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  abelKernelOperator N (abelBoundaryPart F a) (abelBoundaryPart_smooth F hF a)
    (abelBoundaryPart_compact F hc a) R hR (abelBoundaryPart_support_source F a _ hs)

/-- Removing a shrinking neighborhood of q=1 changes the geometric operator
by a term tending to zero in operator norm. All cutoff derivative constants
are derived from the given smooth compact test. -/
theorem abelBoundaryOperator_tendsto {ι : Type*} (l : Filter ι)
    (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha1 : ∀ i,a i≤1) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => abelBoundaryOperator N F hF hc R hR hs (a i)) l (𝓝 0) := by
  obtain ⟨A,hA⟩ := hc.deriv.exists_bound_of_continuous (hF.continuous_deriv (by simp))
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hF.continuous
  obtain ⟨D,hD,hTD⟩ := smoothTransition_deriv_bounded
  have hA0 : 0≤A := (norm_nonneg (deriv F 0)).trans (hA 0)
  have hB0 : 0≤B := (norm_nonneg (F 0)).trans (hB 0)
  have hlim : Tendsto (fun i => 1+2*a i) l (𝓝 1) := by
    simpa only [mul_zero,add_zero] using (ha0.const_mul 2).const_add 1
  exact abelKernelOperator_shrinking_support_tendsto l N (fun i => abelBoundaryPart F (a i))
    (fun i => abelBoundaryPart_smooth F hF (a i))
    (fun i => abelBoundaryPart_compact F hc (a i)) (fun _ => R) (fun _ => hR)
    (fun i => abelBoundaryPart_support_source F (a i) _ hs)
    (fun i => 1+2*a i) (2*(A+2*B*D)) (fun i => by have := ha i; linarith) hlim
    (fun i => abelBoundaryPart_support F (a i) (ha i)) (fun i q => by
      have he : 2*(A+2*B*D)/(1+2*a i-1)=(A+2*B*D)/a i := by
        rw [show 1+2*a i-1=2*a i by ring]
        field_simp
      rw [he]
      exact abelBoundaryPart_derivative_bound F hF A B D hA0 hB0 hD hA hB hTD
        (a i) (ha i) (ha1 i) q)

/-- The complementary test is identically zero in a genuine interval next
to the singular endpoint. -/
theorem abelBoundaryPart_sub_zero_near (F : ℝ → ℂ) (a : ℝ) (ha : 0<a) (ha1 : a≤1)
    (q : ℝ) (hq : 1≤q) (hqa : q≤1+a) : F q-abelBoundaryPart F a q=0 := by
  rw [abelBoundaryPart,abelBoundaryCutoff_one a ha ha1 q hq hqa,mul_one,sub_self]

#print axioms abelBoundaryOperator_tendsto
#print axioms abelBoundaryPart_sub_zero_near

end QuantitativeMaass.AllLevel

-- All-level extension of AbelPuncturedLimit.
open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

/-- The actual geometric operator of the test with a neighborhood of q=1
removed. This is defined from its kernel, rather than as an operator difference. -/
def abelPuncturedOperator (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (a : ℝ) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  abelKernelOperator N (fun q => F q-abelBoundaryPart F a q)
    (hF.sub (abelBoundaryPart_smooth F hF a)) (hc.sub (abelBoundaryPart_compact F hc a))
    R hR (support_sub_Iic F (abelBoundaryPart F a) _ hs (abelBoundaryPart_support_source F a _ hs))

theorem abelPuncturedOperator_eq_sub (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (a : ℝ) :
    abelPuncturedOperator N F hF hc R hR hs a=
      abelKernelOperator N F hF hc R hR hs-abelBoundaryOperator N F hF hc R hR hs a :=
  abelKernelOperator_sub N F (abelBoundaryPart F a) hF (abelBoundaryPart_smooth F hF a)
    hc (abelBoundaryPart_compact F hc a) R hR hs (abelBoundaryPart_support_source F a _ hs)

/-- Every original smooth compact q-test operator is an operator-norm limit
of actual test operators whose time tests vanish near zero. -/
theorem abelPuncturedOperator_tendsto {ι : Type*} (l : Filter ι)
    (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha1 : ∀ i,a i≤1) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => abelPuncturedOperator N F hF hc R hR hs (a i)) l
      (𝓝 (abelKernelOperator N F hF hc R hR hs)) := by
  apply (tendsto_iff_norm_sub_tendsto_zero
    (f := fun i => abelPuncturedOperator N F hF hc R hR hs (a i))
    (b := abelKernelOperator N F hF hc R hR hs)).mpr
  have he : (fun i => ‖abelPuncturedOperator N F hF hc R hR hs (a i)-
      abelKernelOperator N F hF hc R hR hs‖)=
      (fun i => ‖abelBoundaryOperator N F hF hc R hR hs (a i)‖) := by
    funext i
    rw [abelPuncturedOperator_eq_sub]
    have hid : (abelKernelOperator N F hF hc R hR hs-
        abelBoundaryOperator N F hF hc R hR hs (a i))-
        abelKernelOperator N F hF hc R hR hs=
        -abelBoundaryOperator N F hF hc R hR hs (a i) := by abel
    rw [hid]
    exact norm_neg (abelBoundaryOperator N F hF hc R hR hs (a i))
  rw [he]
  exact (tendsto_zero_iff_norm_tendsto_zero
    (f := fun i => abelBoundaryOperator N F hF hc R hR hs (a i))).mp
      (abelBoundaryOperator_tendsto l N F hF hc R hR hs a ha ha1 ha0)

#print axioms abelPuncturedOperator_eq_sub
#print axioms abelPuncturedOperator_tendsto

end QuantitativeMaass.AllLevel

