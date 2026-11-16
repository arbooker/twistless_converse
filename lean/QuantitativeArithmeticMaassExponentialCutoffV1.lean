module
public import QuantitativeArithmeticMaassWeightedTheoryV4
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology ContDiff
namespace QuantitativeArithmeticMaassWeighted
open QuantitativeMaass QuantitativeMaass.Weighted MaassDifferential
open QuantitativeArithmeticMaassGradient

/-- Exact hyperbolic gradient length, with no smoothness assumption. -/
theorem gradient_sq_eq (b : Point → ℂ) (z : ℍ) :
    ‖cutoffGradient true b z‖^2+‖cutoffGradient false b z‖^2=
      (upperEnergy b b z).re := by
  unfold cutoffGradient upperEnergy upperFunction
  rw [hyperbolicEnergy_self_eq]
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,axis,
    ite_true,Bool.false_eq_true,ite_false]
  change z.im^2*‖X b (z.re,z.im)‖^2+z.im^2*‖Y b (z.re,z.im)‖^2=_
  ring

def exponentialValue (a : ℝ) (b : Point → ℂ) : Point → ℂ :=
  fun Z => Complex.exp ((a:ℂ)*b Z)

theorem exponential_gradient (N : ℕ) (b : Cutoff N) (a : ℝ) (i : Bool) (z : ℍ) :
    cutoffGradient i (exponentialValue a b.value) z=
      (a:ℂ)*upperFunction (exponentialValue a b.value) z*cutoffGradient i b.value z := by
  have hd := ((b.smooth.contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds
      (show (z.re,z.im) ∈ {Z : Point | 0<Z.2} from z.im_pos))).differentiableAt
    (by simp)).hasFDerivAt
  have he := congrArg (fun L : Point →L[ℝ] ℂ => L (axis i))
    ((hd.const_mul (a:ℂ)).cexp.fderiv)
  unfold cutoffGradient upperFunction exponentialValue dir D
  simp only [smul_apply,smul_eq_mul] at he
  rw [he]
  ring

theorem exponential_log_gradient (N : ℕ) (b : Cutoff N) {a : ℝ} (_ha : 0≤a) (z : ℍ) :
    ‖cutoffGradient true (exponentialValue a b.value) z‖^2+
      ‖cutoffGradient false (exponentialValue a b.value) z‖^2 ≤
      (a*|b.gradientBound|)^2*‖upperFunction (exponentialValue a b.value) z‖^2 := by
  rw [exponential_gradient,exponential_gradient]
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hg := b.gradient_bound z
  rw [← gradient_sq_eq] at hg
  have hm := mul_le_mul_of_nonneg_left hg
    (mul_nonneg (sq_nonneg a) (sq_nonneg ‖upperFunction (exponentialValue a b.value) z‖))
  nlinarith only [hm]

theorem exponential_value_bound (N : ℕ) (b : Cutoff N) {a : ℝ} (ha : 0≤a) (z : ℍ) :
    ‖upperFunction (exponentialValue a b.value) z‖≤Real.exp (a*b.bound) := by
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (b.value_bound z) ha

/-- Bounded invariant exponential weights suitable for the weighted wave estimate. -/
def exponentialCutoff (N : ℕ) (b : Cutoff N) (a : ℝ) (ha : 0≤a) : Cutoff N where
  value := exponentialValue a b.value
  smooth := (contDiffOn_const.mul b.smooth).cexp
  invariant := by
    intro g z
    change Complex.exp ((a:ℂ)*upperFunction b.value (g•z))=_
    rw [b.invariant]
    rfl
  real := by
    intro Z
    change star (Complex.exp ((a:ℂ)*b.value Z))=_
    rw [Complex.star_def,← Complex.exp_conj]
    simp only [map_mul,Complex.conj_ofReal]
    rw [← Complex.star_def,b.real]
    rfl
  bound := Real.exp (a*b.bound)
  bound_nonneg := (Real.exp_pos _).le
  value_bound := exponential_value_bound N b ha
  gradientBound := a*|b.gradientBound| * Real.exp (a*b.bound)
  gradient_bound := by
    intro z
    rw [← gradient_sq_eq]
    apply (exponential_log_gradient N b ha z).trans
    have he := exponential_value_bound N b ha z
    have hs := sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le |>.mpr he
    have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (a*|b.gradientBound|))
    simpa only [mul_pow] using hm

/-- The actual shifted quotient wave satisfies the exponential-weight estimate.
No finite-propagation or support estimate is assumed. -/
theorem exponential_wave_bound (N : ℕ) (b : Cutoff N) {a : ℝ} (ha : 0≤a)
    {x y z : AutomorphicSpace N} (hxy : FriedrichsGraph N x y)
    (hyz : FriedrichsGraph N y z) {t : ℝ} (ht : 0≤t) :
    waveEnergy N (exponentialCutoff N b a ha) x y t ≤
      waveEnergy N (exponentialCutoff N b a ha) x y 0 *
        Real.exp ((2*(a*|b.gradientBound|)+5/4)*t) := by
  exact waveEnergy_exp_bound N (exponentialCutoff N b a ha)
    (mul_nonneg ha (abs_nonneg _)) (exponential_log_gradient N b ha) hxy hyz ht

#print axioms exponential_wave_bound
#print axioms gradient_sq_eq
#print axioms exponential_gradient
#print axioms exponential_log_gradient
#print axioms exponentialCutoff
end QuantitativeArithmeticMaassWeighted
