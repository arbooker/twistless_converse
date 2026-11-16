module

public import QuantitativeNinaMaassFourierSeparationV1
public import QuantitativeMaassCuspTensorSeedV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory QuantitativeMaass
open scoped Topology ContDiff

/-!
Compact horizontal Fourier tests. Their first two translate identities
extract the literal horocycle Fourier integral and its horizontal Laplace
eigenvalue, even when the function being tested is merely continuous.
These are genuine compact tensor seeds for the actual Friedrichs graph.
-/

namespace QuantitativeNinaMaass

def lineCharacter (n : ℤ) (x : ℝ) : ℂ := fourier n (x : AddCircle (1 : ℝ))

theorem lineCharacter_smooth (n : ℤ) : ContDiff ℝ ∞ (lineCharacter n) := by
  unfold lineCharacter
  simp only [fourier_coe_apply]
  exact (show ContDiff ℝ ∞ Complex.exp from Complex.contDiff_exp).comp
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).div_const _)

theorem lineCharacter_periodic (n : ℤ) : Function.Periodic (lineCharacter n) 1 := by
  intro x
  unfold lineCharacter
  congr 1
  exact AddCircle.coe_add_period 1 x

def lineFrequency (n : ℤ) : ℂ := 2 * Real.pi * Complex.I * n

theorem lineCharacter_hasDerivAt (n : ℤ) (x : ℝ) :
    HasDerivAt (lineCharacter n) (lineFrequency n * lineCharacter n x) x := by
  change HasDerivAt (fun y : ℝ => fourier n (y : AddCircle (1 : ℝ)))
    (2 * (Real.pi : ℂ) * Complex.I * n * fourier n (x : AddCircle (1 : ℝ))) x
  have h := hasDerivAt_fourier (1 : ℝ) n x
  simpa only [Complex.ofReal_one, div_one] using h

theorem lineCharacter_deriv (n : ℤ) :
    deriv (lineCharacter n) = fun x => lineFrequency n * lineCharacter n x :=
  funext (fun x => (lineCharacter_hasDerivAt n x).deriv)

theorem lineCharacter_second (n : ℤ) (x : ℝ) :
    deriv (deriv (lineCharacter n)) x =
      (-((2 * Real.pi * (n : ℝ)) ^ 2) : ℝ) * lineCharacter n x := by
  rw [lineCharacter_deriv, ((lineCharacter_hasDerivAt n x).const_mul (lineFrequency n)).deriv]
  have he : lineFrequency n * lineFrequency n = ((-((2 * Real.pi * (n : ℝ)) ^ 2) : ℝ) : ℂ) := by
    simp only [lineFrequency, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_intCast]
    calc
      _ = (2 * (Real.pi : ℂ) * n) ^ 2 * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [← mul_assoc, he]

def compactFourierTest (n : ℤ) (x : ℝ) : ℂ := (periodCutoff x : ℂ) * lineCharacter n x

theorem compactFourierTest_smooth (n : ℤ) : ContDiff ℝ ∞ (compactFourierTest n) :=
  (Complex.ofRealCLM.contDiff.comp periodCutoff_smooth).mul (lineCharacter_smooth n)

theorem compactFourierTest_support (n : ℤ) :
    Function.support (compactFourierTest n) ⊆ Icc (0 : ℝ) 2 := by
  intro x hx
  apply periodCutoff_support
  apply subset_tsupport
  intro hz
  exact hx (by simp only [compactFourierTest, hz, Complex.ofReal_zero, zero_mul])

theorem compactFourierTest_partition (n : ℤ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    compactFourierTest n x + compactFourierTest n (x + 1) = lineCharacter n x := by
  simp only [compactFourierTest, lineCharacter_periodic n x]
  rw [← add_mul, ← Complex.ofReal_add, periodCutoff_partition x hx,
    Complex.ofReal_one, one_mul]

theorem complex_derivative_translate_sum (w g : ℝ → ℂ)
    (hw : Differentiable ℝ w) (_hg : Differentiable ℝ g)
    (hwd : Continuous (deriv w)) (hgd : Continuous (deriv g))
    (hp : ∀ x ∈ Icc (0 : ℝ) 1, w x + w (x + 1) = g x) :
    ∀ x ∈ Icc (0 : ℝ) 1, deriv w x + deriv w (x + 1) = deriv g x := by
  have he : EqOn (fun x => deriv w x + deriv w (x + 1)) (deriv g) (Ioo (0 : ℝ) 1) := by
    intro x hx
    have hl : (fun y => w y + w (y + 1)) =ᶠ[𝓝 x] g := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hp y ⟨hy.1.le, hy.2.le⟩
    have hd := (hw x).hasDerivAt.add
      ((hw (x + 1)).hasDerivAt.scomp x ((hasDerivAt_id x).add_const 1))
    have hh := (hd.congr_of_eventuallyEq hl.symm).deriv
    simpa only [one_smul] using hh.symm
  have hc := he.closure (hwd.add (hwd.comp (continuous_id.add continuous_const))) hgd
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hc
  exact hc

theorem compactFourierTest_second_partition (n : ℤ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv (deriv (compactFourierTest n)) x + deriv (deriv (compactFourierTest n)) (x + 1) =
      (-((2 * Real.pi * (n : ℝ)) ^ 2) : ℝ) * lineCharacter n x := by
  have hw := compactFourierTest_smooth n
  have hg := lineCharacter_smooth n
  have hp := complex_derivative_translate_sum _ _
    (hw.differentiable (by simp)) (hg.differentiable (by simp))
    (hw.continuous_deriv (by simp)) (hg.continuous_deriv (by simp))
    (compactFourierTest_partition n)
  have hw' := (contDiff_infty_iff_deriv.mp hw).2
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have h := complex_derivative_translate_sum _ _
    (hw'.differentiable (by simp)) (hg'.differentiable (by simp))
    (hw'.continuous_deriv (by simp)) (hg'.continuous_deriv (by simp)) hp x hx
  rwa [lineCharacter_second] at h

theorem complex_periodic_weight_integral (w : ℝ → ℂ) (hw : Continuous w)
    (F : ℝ → ℂ) (hF : Continuous F) (hp : Function.Periodic F 1) :
    (∫ x in (0 : ℝ)..2, w x * F x) =
      ∫ x in (0 : ℝ)..1, (w x + w (x + 1)) * F x := by
  have hc : Continuous (fun x => w x * F x) := hw.mul hF
  have ht : (∫ x in (1 : ℝ)..2, w x * F x) =
      ∫ x in (0 : ℝ)..1, w (x + 1) * F x := by
    have he := intervalIntegral.integral_comp_add_right (fun x => w x * F x)
      (a := (0 : ℝ)) (b := 1) 1
    norm_num only [zero_add, one_add_one_eq_two] at he
    rw [← he]
    apply intervalIntegral.integral_congr
    intro x _
    change w (x + 1) * F (x + 1) = w (x + 1) * F x
    rw [hp x]
  have htc : Continuous (fun x => w (x + 1) * F x) :=
    (hw.comp (continuous_id.add continuous_const)).mul hF
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 1)
    (hc.intervalIntegrable 1 2), ht, ← intervalIntegral.integral_add
      (hc.intervalIntegrable 0 1) (htc.intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro x _
  exact (add_mul _ _ _).symm

theorem compactFourierTest_integral (n : ℤ) (F : ℝ → ℂ)
    (hF : Continuous F) (hp : Function.Periodic F 1) :
    (∫ x in (0 : ℝ)..2, star (compactFourierTest n x) * F x) = unitLineFourierCoeff F n := by
  rw [complex_periodic_weight_integral _ (compactFourierTest_smooth n).continuous.star F hF hp]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [← star_add, compactFourierTest_partition n x (by simpa using hx)]
  simp only [lineCharacter, Complex.star_def, ← fourier_neg]

theorem compactFourierTest_second_integral (n : ℤ) (F : ℝ → ℂ)
    (hF : Continuous F) (hp : Function.Periodic F 1) :
    (∫ x in (0 : ℝ)..2, star (deriv (deriv (compactFourierTest n)) x) * F x) =
      ((-((2 * Real.pi * (n : ℝ)) ^ 2) : ℝ) : ℂ) * unitLineFourierCoeff F n := by
  have hd := (contDiff_infty_iff_deriv.mp (compactFourierTest_smooth n)).2
  rw [complex_periodic_weight_integral _ (hd.continuous_deriv (by simp)).star F hF hp]
  unfold unitLineFourierCoeff
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [← star_add, compactFourierTest_second_partition n x (by simpa using hx), star_mul]
  simp only [Complex.star_def, Complex.conj_ofReal, lineCharacter, ← fourier_neg]
  ring

def fourierTensorSeed (n : ℤ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (a b : ℝ) (ha : 0 < a) (hs : Function.support g ⊆ Icc a b) : SmoothUpperSeed :=
  cuspTensorSeed (compactFourierTest n) g (compactFourierTest_smooth n) hg
    0 2 a b ha (compactFourierTest_support n) hs

#print axioms lineCharacter_smooth
#print axioms lineCharacter_periodic
#print axioms lineCharacter_second
#print axioms compactFourierTest_smooth
#print axioms compactFourierTest_support
#print axioms compactFourierTest_second_partition
#print axioms complex_periodic_weight_integral
#print axioms compactFourierTest_integral
#print axioms compactFourierTest_second_integral
#print axioms fourierTensorSeed

end QuantitativeNinaMaass
