module

public import QuantitativeMaassLocalizationModuleV1
public import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeArithmeticMaassGradient

open QuantitativeMaass MaassDifferential

def axis (i : Bool) : Point := if i then e₁ else e₂

def seedGradient (N : ℕ) (i : Bool) (u : SmoothUpperSeed) (z : ℍ) : ℂ :=
  (z.im : ℂ)*upperFunction (dir (axis i) (congruencePoincareCartesian N u.toFun)) z

theorem seedGradient_continuous (N : ℕ) (i : Bool) (u : SmoothUpperSeed) :
    Continuous (seedGradient N i u) := by
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp continuous_im
  · exact upperFunction_continuous (dir_contDiffOn
      (congruencePoincareCartesian_smooth N u.smooth u.compact)
      (isOpen_lt continuous_const continuous_snd) (axis i))

theorem seedGradient_sq_le (N : ℕ) (i : Bool) (u : SmoothUpperSeed) (z : ℍ) :
    ‖seedGradient N i u z‖^2≤poincareEnergyDensity N u z := by
  have hE := hyperbolicEnergy_self_eq (congruencePoincareCartesian N u.toFun) (z.re,z.im)
  unfold seedGradient poincareEnergyDensity upperEnergy upperFunction
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,hE]
  cases i <;> simp only [axis,Bool.false_eq_true,ite_false,ite_true]
  · change z.im^2*‖Y (congruencePoincareCartesian N u.toFun) (z.re,z.im)‖^2≤_
    nlinarith [sq_nonneg ‖poincareSum (G := gamma N) (upperFunction u.toFun) z‖,
      mul_nonneg (sq_nonneg z.im) (sq_nonneg ‖X (congruencePoincareCartesian N u.toFun) (z.re,z.im)‖)]
  · change z.im^2*‖X (congruencePoincareCartesian N u.toFun) (z.re,z.im)‖^2≤_
    nlinarith [sq_nonneg ‖poincareSum (G := gamma N) (upperFunction u.toFun) z‖,
      mul_nonneg (sq_nonneg z.im) (sq_nonneg ‖Y (congruencePoincareCartesian N u.toFun) (z.re,z.im)‖)]

theorem seedGradient_memLp (N : ℕ) (i : Bool) (u : SmoothUpperSeed) :
    MemLp (seedGradient N i u) 2 (quotientMeasure N) := by
  apply (memLp_two_iff_integrable_sq_norm (seedGradient_continuous N i u).aestronglyMeasurable).mpr
  apply (poincareEnergyDensity_integrable N u).mono'
    (((seedGradient_continuous N i u).norm.pow 2).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun z => by
    change ‖‖seedGradient N i u z‖^2‖≤poincareEnergyDensity N u z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (‖seedGradient N i u z‖))]
    exact seedGradient_sq_le N i u z)

theorem norm_toLp_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℂ) (hf : MemLp f 2 μ) : ‖hf.toLp f‖^2=∫ z, ‖f z‖^2 ∂μ := by
  let v := hf.toLp f
  calc
    ‖hf.toLp f‖^2=(inner ℂ v v).re := (inner_self_eq_norm_sq (𝕜 := ℂ) v).symm
    _ = ∫ z, (inner ℂ (v z) (v z)).re ∂μ := by
      rw [L2.inner_def]
      exact (integral_re (L2.integrable_inner (𝕜 := ℂ) v v)).symm
    _ = ∫ z, ‖f z‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with z hz
      change (inner ℂ ((hf.toLp f) z) ((hf.toLp f) z)).re=‖f z‖^2
      rw [hz]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (f z)

def seedGradientLp (N : ℕ) (i : Bool) (u : SmoothUpperSeed) : Lp ℂ 2 (quotientMeasure N) :=
  (seedGradient_memLp N i u).toLp (seedGradient N i u)

theorem seedGradientLp_norm_le (N : ℕ) (i : Bool) (u : SmoothUpperSeed) :
    ‖seedGradientLp N i u‖≤‖poincareEnergySeed N u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [seedGradientLp,norm_toLp_sq,poincareEnergySeed_norm_sq_integral]
  exact integral_mono ((seedGradient_memLp N i u).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    (poincareEnergyDensity_integrable N u) (seedGradient_sq_le N i u)

#print axioms seedGradientLp_norm_le

end QuantitativeArithmeticMaassGradient
