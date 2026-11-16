module

public import QuantitativeMaassPeriodLaplacianV1
public import MaassDirectionalV1
public import MaassFrickeCovarianceV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- The real Cartesian profile, with horizontal width rescaled to one. -/
def scaledProfile (w : ℝ) (u : Point → ℂ) (x y : ℝ) : ℂ := u (w*x,y)

theorem scaledProfile_smooth (w : ℝ) {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) :
    ContDiffOn ℝ ∞ (Function.uncurry (scaledProfile w u)) {Z | 0<Z.2} :=
  hu.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn
    (fun _ hZ => hZ)

theorem smooth_vertical_hasDerivAt {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (x y : ℝ) (hy : 0<y) :
    HasDerivAt (fun v => u (x,v)) (Y u (x,y)) y := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have hd := ((hu.contDiffAt (hs.mem_nhds (show (x,y) ∈ {Z : Point | 0<Z.2} from hy))).differentiableAt (by simp)).hasFDerivAt
  exact hd.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

/-- Width scaling is reflected in the actual horizontal second derivative,
not an assumption on the differential expression. -/
theorem periodLaplacian_scaledProfile (w : ℝ) (hw : w≠0) {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (x y : ℝ) (hy : 0<y) :
    periodLaplacian w (scaledProfile w u) x y=hyperbolic u (w*x,y) := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have hx := second_curve hu hs (g := fun z => (w*z,y))
    (g' := fun _ => (w,0)) (g'' := 0)
    (Eventually.of_forall fun z => by simpa using
      ((hasDerivAt_id z).const_mul w).prodMk (hasDerivAt_const z y))
    (hasDerivAt_const x (w,0)) hy
  have hvec : (w,0)=w•e₁ := by ext <;> simp [e₁]
  rw [hvec,map_zero,add_zero] at hx
  simp only [map_smul,smul_apply,smul_smul] at hx
  rw [← second_horizontal hu hs hy] at hx
  unfold periodLaplacian scaledProfile hyperbolic euclidean
  rw [hx]
  simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_pow,Complex.ofReal_mul]
  have hwC : (w:ℂ)≠0 := by exact_mod_cast hw
  field_simp

/-- The constant-term differential identity for any genuine smooth periodic
Cartesian profile. All derivative and integrability hypotheses are discharged
from smoothness on positive height. -/
theorem zeroFourier_periodLaplacian_smooth (w : ℝ) {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hperiod : ∀ y, 0<y → Function.Periodic (fun x => u (x,y)) 1)
    (y : ℝ) (hy : 0<y) :
    zeroFourier (periodLaplacian w (Function.curry u)) y=
      -(y:ℂ)^2*deriv (deriv (zeroFourier (Function.curry u))) y := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have huY := dir_contDiffOn hu hs e₂
  have huYY := dir_contDiffOn huY hs e₂
  have huX := dir_contDiffOn hu hs e₁
  have huXX := dir_contDiffOn huX hs e₁
  have hcont (v : Point → ℂ) (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2}) :
      ContinuousOn (Function.uncurry (Function.curry v)) (univ ×ˢ Ioi (0:ℝ)) := by
    exact hv.continuousOn.mono (fun _ hz => hz.2)
  apply zeroFourier_periodLaplacian w (Function.curry u) (Function.curry (Y u))
    (Function.curry (Y (Y u))) (hcont u hu) (hcont _ huY) (hcont _ huYY)
    (smooth_vertical_hasDerivAt hu) (smooth_vertical_hasDerivAt huY) hperiod
  · intro v hv
    change Differentiable ℝ (deriv (fun x => u (x,v)))
    have he : deriv (fun x => u (x,v))=fun x => X u (x,v) :=
      funext fun x => (X_eq_deriv hu hs hv).symm
    rw [he]
    exact fun x => (horizontal_hasDerivAt huX hs hv).differentiableAt
  · intro v hv
    change Continuous (deriv (deriv (fun x => u (x,v))))
    have he : deriv (deriv (fun x => u (x,v)))=fun x => X (X u) (x,v) :=
      funext fun x => (XX_eq_deriv hu hs hv).symm
    rw [he]
    exact huXX.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
      (fun _ => hv)
  · exact hy

#print axioms periodLaplacian_scaledProfile
#print axioms zeroFourier_periodLaplacian_smooth

end QuantitativeMaass
