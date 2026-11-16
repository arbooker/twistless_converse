module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology

/-!
Uniqueness from literal Fourier integrals on a horocycle. The proofs use
the existing Fourier completeness theorem on the additive circle. They do
not assume a Fourier expansion or a coefficient-separation property for
Maass eigenvectors. Applying them to normalized eigenforms still requires
the physical Fourier-Bessel coefficient formula.
-/

namespace QuantitativeNinaMaass

theorem continuous_circle_zero_of_fourier {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ)) (hf : ∀ n : ℤ, fourierCoeff f n = 0) : f = 0 := by
  have hs : Summable (fourierCoeff f) := by
    rw [show fourierCoeff f = fun _ : ℤ => (0 : ℂ) from funext hf]
    exact summable_zero
  have hh := hasSum_fourier_series_of_summable hs
  simp_rw [hf, zero_smul] at hh
  exact hh.unique hasSum_zero

theorem continuous_circle_eq_of_fourier {T : ℝ} [Fact (0 < T)]
    (f g : C(AddCircle T, ℂ))
    (hfg : ∀ n : ℤ, fourierCoeff f n = fourierCoeff g n) : f = g := by
  apply sub_eq_zero.mp
  apply continuous_circle_zero_of_fourier
  intro n
  have hf : Integrable (fun x : AddCircle T => fourier (-n) x * f x)
      AddCircle.haarAddCircle :=
    ((fourier (-n)).continuous.mul f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (fun x : AddCircle T => fourier (-n) x * g x)
      AddCircle.haarAddCircle :=
    ((fourier (-n)).continuous.mul g.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ x : AddCircle T, fourier (-n) x * (f x - g x)
    ∂AddCircle.haarAddCircle) = 0
  simp_rw [mul_sub]
  rw [integral_sub hf hg]
  exact sub_eq_zero.mpr (hfg n)

theorem periodic_lift_continuous (f : ℝ → ℂ) (hf : Continuous f)
    (hp : Function.Periodic f 1) : Continuous hp.lift := by
  have he : AddCircle.liftIoc 1 0 f = hp.lift := by
    funext z
    obtain ⟨x, hx, rfl⟩ := AddCircle.eq_coe_Ioc z
    rw [AddCircle.liftIoc_zero_coe_apply hx, hp.lift_coe]
  rw [← he]
  apply AddCircle.liftIoc_zero_continuous
  · simpa only [zero_add] using (hp 0).symm
  · exact hf.continuousOn

/-- The actual unit-period Fourier integral; it is not an abstract
coefficient functional chosen to make injectivity hold. -/
def unitLineFourierCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, fourier (-n) (x : AddCircle (1 : ℝ)) * f x

theorem periodic_fourierCoeff_eq (f : ℝ → ℂ) (hp : Function.Periodic f 1) (n : ℤ) :
    fourierCoeff hp.lift n = unitLineFourierCoeff f n := by
  rw [fourierCoeff_eq_intervalIntegral hp.lift n 0]
  simp only [div_one, one_smul, zero_add, hp.lift_coe, smul_eq_mul, unitLineFourierCoeff]

theorem unitLineFourierCoeff_zero (f : ℝ → ℂ) :
    unitLineFourierCoeff f 0 = ∫ x in (0 : ℝ)..1, f x := by
  simp only [unitLineFourierCoeff, neg_zero, fourier_zero, one_mul]

/-- Equality of all literal Fourier integrals gives equality everywhere
on the real line, using continuity and genuine unit periodicity. -/
theorem continuous_periodic_eq_of_fourier (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (he : ∀ n : ℤ, unitLineFourierCoeff f n = unitLineFourierCoeff g n) : f = g := by
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨hpf.lift, periodic_lift_continuous f hf hpf⟩
  let G : C(AddCircle (1 : ℝ), ℂ) := ⟨hpg.lift, periodic_lift_continuous g hg hpg⟩
  have hFG : F = G := continuous_circle_eq_of_fourier F G (fun n => by
    change fourierCoeff hpf.lift n = fourierCoeff hpg.lift n
    rw [periodic_fourierCoeff_eq, periodic_fourierCoeff_eq]
    exact he n)
  funext x
  exact congrArg (fun H : C(AddCircle (1 : ℝ), ℂ) => H (x : AddCircle (1 : ℝ))) hFG

theorem fourier_argument_neg {T : ℝ} (n : ℤ) (x : AddCircle T) :
    fourier n (-x) = fourier (-n) x := by
  simp only [fourier_apply, smul_neg, neg_smul]

/-- Reflection parity determines the negative Fourier integrals from the
positive ones. No sign-sector asymptotic or expansion is used. -/
theorem circle_fourier_negative_of_parity {T : ℝ} [Fact (0 < T)]
    (f : AddCircle T → ℂ) (s : ℂ) (hf : ∀ x, f (-x) = s * f x) (n : ℤ) :
    fourierCoeff f (-n) = s * fourierCoeff f n := by
  unfold fourierCoeff
  rw [neg_neg, ← integral_neg_eq_self (fun x : AddCircle T => fourier n x • f x)
    AddCircle.haarAddCircle]
  simp_rw [fourier_argument_neg, hf, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem periodic_lift_parity (f : ℝ → ℂ) (hp : Function.Periodic f 1)
    (s : ℂ) (hs : ∀ x, f (-x) = s * f x) (z : AddCircle (1 : ℝ)) :
    hp.lift (-z) = s * hp.lift z := by
  obtain ⟨x, _, rfl⟩ := AddCircle.eq_coe_Ioc z
  change hp.lift ((-x : ℝ) : AddCircle (1 : ℝ)) = s * hp.lift (x : AddCircle (1 : ℝ))
  rw [hp.lift_coe, hp.lift_coe]
  exact hs x

theorem unitLineFourierCoeff_negative_of_parity (f : ℝ → ℂ)
    (hp : Function.Periodic f 1) (s : ℂ) (hs : ∀ x, f (-x) = s * f x) (n : ℤ) :
    unitLineFourierCoeff f (-n) = s * unitLineFourierCoeff f n := by
  rw [← periodic_fourierCoeff_eq f hp, ← periodic_fourierCoeff_eq f hp]
  exact circle_fourier_negative_of_parity hp.lift s (periodic_lift_parity f hp s hs) n

/-- For functions with the same reflection parity, the nonnegative
Fourier integrals suffice for pointwise uniqueness. In the cuspidal
application the zero integral vanishes for both functions. -/
theorem continuous_periodic_eq_of_nonnegative_fourier (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (s : ℂ) (hsf : ∀ x, f (-x) = s * f x) (hsg : ∀ x, g (-x) = s * g x)
    (he : ∀ n : ℕ, unitLineFourierCoeff f n = unitLineFourierCoeff g n) : f = g := by
  apply continuous_periodic_eq_of_fourier f g hf hg hpf hpg
  intro n
  cases n with
  | ofNat n => exact he n
  | negSucc n =>
    change unitLineFourierCoeff f (-((n + 1 : ℕ) : ℤ)) =
      unitLineFourierCoeff g (-((n + 1 : ℕ) : ℤ))
    rw [unitLineFourierCoeff_negative_of_parity f hpf s hsf,
      unitLineFourierCoeff_negative_of_parity g hpg s hsg, he]

#print axioms continuous_circle_zero_of_fourier
#print axioms continuous_circle_eq_of_fourier
#print axioms periodic_lift_continuous
#print axioms periodic_fourierCoeff_eq
#print axioms unitLineFourierCoeff_zero
#print axioms continuous_periodic_eq_of_fourier
#print axioms fourier_argument_neg
#print axioms circle_fourier_negative_of_parity
#print axioms periodic_lift_parity
#print axioms unitLineFourierCoeff_negative_of_parity
#print axioms continuous_periodic_eq_of_nonnegative_fourier

end QuantitativeNinaMaass
