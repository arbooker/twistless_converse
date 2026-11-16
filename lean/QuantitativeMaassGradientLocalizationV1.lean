module

public import QuantitativeArithmeticMaassGradientExtensionV1
public import QuantitativeMaassFormLocalizationDefectV1
public import QuantitativeMaassLocalizationRepresentativeV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass

open MaassDifferential QuantitativeArithmeticMaassGradient

/-- A hyperbolic coordinate derivative of the cutoff. -/
def cutoffGradient (i : Bool) (b : Point → ℂ) (z : ℍ) : ℂ :=
  (z.im : ℂ)*upperFunction (dir (axis i) b) z

theorem cutoffGradient_continuous (i : Bool) (b : Point → ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2}) : Continuous (cutoffGradient i b) :=
  (Complex.continuous_ofReal.comp continuous_im).mul
    (upperFunction_continuous (dir_contDiffOn hb
      (isOpen_lt continuous_const continuous_snd) (axis i)))

theorem cutoffGradient_norm_le (i : Bool) (b : Point → ℂ) {C : ℝ}
    (hg : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) (z : ℍ) :
    ‖cutoffGradient i b z‖≤|C| := by
  apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg C)).mp
  rw [sq_abs]
  apply le_trans _ (hg z)
  have hE := hyperbolicEnergy_self_eq b (z.re,z.im)
  unfold cutoffGradient upperEnergy upperFunction
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,hE]
  cases i <;> simp only [axis,Bool.false_eq_true,ite_false,ite_true]
  · change z.im^2*‖Y b (z.re,z.im)‖^2≤_
    nlinarith [mul_nonneg (sq_nonneg z.im) (sq_nonneg ‖X b (z.re,z.im)‖)]
  · change z.im^2*‖X b (z.re,z.im)‖^2≤_
    nlinarith [mul_nonneg (sq_nonneg z.im) (sq_nonneg ‖Y b (z.re,z.im)‖)]

/-- The literal seed gradient obeys the product rule for an invariant cutoff. -/
theorem seedGradient_localized (N : ℕ) (i : Bool) (u : SmoothUpperSeed) (b : Point → ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z) (z : ℍ) :
    seedGradient N i (u.localized b hb) z=upperFunction b z*seedGradient N i u z+
      cutoffGradient i b z*poincareSum (G := gamma N) (upperFunction u.toFun) z := by
  have he := localized_poincare_germ N u b hb hi (Z := (z.re,z.im)) z.im_pos
  have hd := congrArg (fun L : Point →L[ℝ] ℂ => L (axis i)) he.fderiv_eq
  change dir (axis i) (congruencePoincareCartesian N (u.localized b hb).toFun) (z.re,z.im)=
    dir (axis i) (fun W => b W*congruencePoincareCartesian N u.toFun W) (z.re,z.im) at hd
  rw [dir_mul_smooth (isOpen_lt continuous_const continuous_snd) hb
    (congruencePoincareCartesian_smooth N u.smooth u.compact) z.im_pos] at hd
  unfold seedGradient cutoffGradient upperFunction
  have hrep : congruencePoincareCartesian N u.toFun (z.re,z.im)=
      poincareSum (G := gamma N) (fun w : ℍ => u.toFun (w.re,w.im)) z :=
    congruencePoincareCartesian_represents N u.toFun z
  rw [hd,hrep]
  ring

theorem seedGradientLp_localized (N : ℕ) (i : Bool) (u : SmoothUpperSeed) (b : Point → ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction b (g•z)=upperFunction b z)
    {B C : ℝ} (hbound : ∀ z : ℍ, ‖upperFunction b z‖≤B)
    (hg : ∀ z : ℍ, (upperEnergy b b z).re≤C^2) :
    seedGradientLp N i (u.localized b hb)=
      AsymptoticL2Multiplier.operator (upperFunction b)
        (upperFunction_continuous hb).aestronglyMeasurable (Eventually.of_forall hbound)
        (seedGradientLp N i u)+
      AsymptoticL2Multiplier.operator (cutoffGradient i b)
        (cutoffGradient_continuous i b hb).aestronglyMeasurable
        (Eventually.of_forall (cutoffGradient_norm_le i b hg)) (poincareSeedVector N u).val := by
  apply Lp.ext
  filter_upwards [(seedGradient_memLp N i (u.localized b hb)).coeFn_toLp,
    (seedGradient_memLp N i u).coeFn_toLp,poincareSeedVector_coeFn N u,
    AsymptoticL2Multiplier.operator_coeFn (upperFunction b)
      (upperFunction_continuous hb).aestronglyMeasurable (Eventually.of_forall hbound) (seedGradientLp N i u),
    AsymptoticL2Multiplier.operator_coeFn (cutoffGradient i b)
      (cutoffGradient_continuous i b hb).aestronglyMeasurable
      (Eventually.of_forall (cutoffGradient_norm_le i b hg)) (poincareSeedVector N u).val,
    Lp.coeFn_add
      (AsymptoticL2Multiplier.operator (upperFunction b)
        (upperFunction_continuous hb).aestronglyMeasurable (Eventually.of_forall hbound) (seedGradientLp N i u))
      (AsymptoticL2Multiplier.operator (cutoffGradient i b)
        (cutoffGradient_continuous i b hb).aestronglyMeasurable
        (Eventually.of_forall (cutoffGradient_norm_le i b hg)) (poincareSeedVector N u).val)]
    with z hl hu hp hm hn ha
  change (seedGradientLp N i (u.localized b hb)) z=_ at hl
  rw [ha]
  simp only [Pi.add_apply]
  rw [hm,hn,hl]
  change (seedGradientLp N i u) z=seedGradient N i u z at hu
  rw [hu,hp]
  exact seedGradient_localized N i u b hb hi z

#print axioms cutoffGradient_norm_le
#print axioms seedGradientLp_localized

end QuantitativeMaass
