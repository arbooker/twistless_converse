module

public import QuantitativeMaassPeriodicCutoffScaleV1
public import QuantitativeMaassCuspRectangleV1
public import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Tensor test in actual Cartesian cusp coordinates. -/
def cuspTensor (h g : ℝ → ℂ) (Z : Point) : ℂ := h Z.1*g Z.2

theorem cuspTensor_smooth (h g : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (cuspTensor h g) :=
  (hh.comp contDiff_fst).mul (hg.comp contDiff_snd)

theorem cuspTensor_support (h g : ℝ → ℂ) (l r a b : ℝ) (ha : 0<a)
    (hh : Function.support h⊆Icc l r) (hg : Function.support g⊆Icc a b) :
    tsupport (upperFunction (cuspTensor h g))⊆upperRectangle l r a b := by
  apply closure_minimal _ (upperRectangle_compact l r a b ha).isClosed
  intro Z hZ
  have hp : h Z.re*g Z.im≠0 := hZ
  exact ⟨hh (left_ne_zero_of_mul hp),hg (right_ne_zero_of_mul hp)⟩

/-- Compact vertical support bounded away from zero gives a genuine smooth
upper-half-plane seed, not a formal periodic test. -/
def cuspTensorSeed (h g : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hg : ContDiff ℝ ∞ g)
    (l r a b : ℝ) (ha : 0<a)
    (hhs : Function.support h⊆Icc l r) (hgs : Function.support g⊆Icc a b) : SmoothUpperSeed where
  toFun := cuspTensor h g
  smooth := (cuspTensor_smooth h g hh hg).contDiffOn
  compact := (upperRectangle_compact l r a b ha).of_isClosed_subset isClosed_closure
    (cuspTensor_support h g l r a b ha hhs hgs)

/-- The literal hyperbolic Laplacian separates on tensor tests. -/
theorem cuspTensor_laplacian (h g : ℝ → ℂ) (Z : Point) :
    hyperbolic (cuspTensor h g) Z=
      -(Z.2:ℂ)^2*(deriv (deriv h) Z.1*g Z.2+h Z.1*deriv (deriv g) Z.2) := by
  simp only [hyperbolic,euclidean,cuspTensor,deriv_mul_const_field',deriv_const_mul_field',
    Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_pow]

/-- Smooth compact horizontal partition at width w. -/
def cuspHorizontal (w x : ℝ) : ℂ := (periodCutoff (x/w):ℂ)

theorem cuspHorizontal_smooth (w : ℝ) : ContDiff ℝ ∞ (cuspHorizontal w) :=
  Complex.ofRealCLM.contDiff.comp (periodCutoff_smooth.comp (contDiff_id.div_const w))

theorem cuspHorizontal_support (w : ℝ) (hw : 0<w) :
    Function.support (cuspHorizontal w)⊆Icc (0:ℝ) (2*w) := by
  intro x hx
  have hn : periodCutoff (x/w)≠0 := by
    intro he
    exact hx (by simp only [cuspHorizontal,he,Complex.ofReal_zero])
  have hs := periodCutoff_support (subset_closure hn)
  constructor
  · simpa only [zero_mul] using (le_div_iff₀ hw).mp hs.1
  · exact (div_le_iff₀ hw).mp hs.2

private theorem realScaled_hasDerivAt (h : ℝ → ℝ) (hh : Differentiable ℝ h) (w x : ℝ) :
    HasDerivAt (fun x => (h (x/w):ℂ)) (((deriv h (x/w):ℝ):ℂ)/(w:ℂ)) x := by
  have hd := ((hh (x/w)).hasDerivAt.comp x ((hasDerivAt_id x).div_const w)).ofReal_comp
  simpa only [Function.comp_apply,id_eq,one_div,Complex.ofReal_mul,Complex.ofReal_inv,
    Complex.ofReal_one,one_mul,div_eq_mul_inv] using hd

theorem cuspHorizontal_deriv (w x : ℝ) :
    deriv (cuspHorizontal w) x=((deriv periodCutoff (x/w):ℝ):ℂ)/(w:ℂ) :=
  (realScaled_hasDerivAt periodCutoff (periodCutoff_smooth.differentiable (by simp)) w x).deriv

theorem cuspHorizontal_second (w x : ℝ) :
    deriv (deriv (cuspHorizontal w)) x=((deriv (deriv periodCutoff) (x/w):ℝ):ℂ)/(w:ℂ)^2 := by
  have hd : ContDiff ℝ ∞ (deriv periodCutoff) := (contDiff_infty_iff_deriv.mp periodCutoff_smooth).2
  have he : deriv (cuspHorizontal w)=fun x => ((deriv periodCutoff (x/w):ℝ):ℂ)/(w:ℂ) :=
    funext (cuspHorizontal_deriv w)
  have hd2 := (realScaled_hasDerivAt (deriv periodCutoff) (hd.differentiable (by simp)) w x).div_const (w:ℂ)
  rw [he,hd2.deriv]
  ring

/-- The compact test used to extract the period average in the weak PDE. -/
def cuspPeriodTest (w : ℝ) (hw : 0<w) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (a b : ℝ) (ha : 0<a) (hgs : Function.support g⊆Icc a b) : SmoothUpperSeed :=
  cuspTensorSeed (cuspHorizontal w) g (cuspHorizontal_smooth w) hg
    0 (2*w) a b ha (cuspHorizontal_support w hw) hgs

#print axioms cuspTensor_support
#print axioms cuspTensor_laplacian
#print axioms cuspHorizontal_second
#print axioms cuspPeriodTest

end QuantitativeMaass
