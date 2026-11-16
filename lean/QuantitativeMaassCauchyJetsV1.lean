module

public import QuantitativeMaassPlanePDEV1
public import QuantitativeMaassAnalyticFlatV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

def normalJet : ℕ → ((ℝ × ℝ) → ℂ) → (ℝ × ℝ) → ℂ
  | 0,f => f
  | n+1,f => planeDerivative (1,0) (normalJet n f)

theorem normalJet_contDiffOn {f : (ℝ × ℝ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2}) (n : ℕ) :
    ContDiffOn ℝ ∞ (normalJet n f) {z : ℝ × ℝ | 0<z.2} := by
  induction n with
  | zero => exact hf
  | succ n ih => exact planeDerivative_contDiffOn ih (isOpen_lt continuous_const continuous_snd) (1,0)

theorem normalJet_eigenEquation {f : (ℝ × ℝ) → ℂ} {lam : ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2}) (he : planeEigenEquation lam f) (n : ℕ) :
    planeEigenEquation lam (normalJet n f) := by
  induction n with
  | zero => exact he
  | succ n ih => exact planeEigenEquation_horizontal (normalJet_contDiffOn hf n) ih

theorem planeDerivative_vertical_axis_zero {f : (ℝ × ℝ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2})
    (hzero : ∀ y : ℝ,0<y → f (0,y)=0) (y : ℝ) (hy : 0<y) :
    planeDerivative (0,1) f (0,y)=0 := by
  have hU : IsOpen {z : ℝ × ℝ | 0<z.2} := isOpen_lt continuous_const continuous_snd
  rw [←planeDerivative_vertical hf hU 0 y hy]
  have he : (fun u => f (0,u)) =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with u hu
    exact hzero u hu
  rw [he.deriv_eq,deriv_const]

theorem planeDerivative_vertical_twice_axis_zero {f : (ℝ × ℝ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2})
    (hzero : ∀ y : ℝ,0<y → f (0,y)=0) (y : ℝ) (hy : 0<y) :
    planeDerivative (0,1) (planeDerivative (0,1) f) (0,y)=0 :=
  planeDerivative_vertical_axis_zero
    (planeDerivative_contDiffOn hf (isOpen_lt continuous_const continuous_snd) (0,1))
    (planeDerivative_vertical_axis_zero hf hzero) y hy

/-- The differential equation recursively determines every normal derivative
from the value and first normal derivative on the positive imaginary axis. -/
theorem normalJet_axis_zero {f : (ℝ × ℝ) → ℂ} {lam : ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2}) (he : planeEigenEquation lam f)
    (hzero : ∀ y : ℝ,0<y → f (0,y)=0)
    (hone : ∀ y : ℝ,0<y → planeDerivative (1,0) f (0,y)=0) :
    ∀ n : ℕ,∀ y : ℝ,0<y → normalJet n f (0,y)=0 := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact hzero
  | one => exact hone
  | more n hn _ =>
    intro y hy
    have hh := normalJet_eigenEquation hf he n 0 y hy
    rw [planeDerivative_vertical_twice_axis_zero (normalJet_contDiffOn hf n) hn y hy,
      hn y hy,add_zero,mul_zero] at hh
    have hyc : (y:ℂ)≠0 := by exact_mod_cast hy.ne'
    exact (mul_eq_zero.mp hh).resolve_left (neg_ne_zero.mpr (pow_ne_zero 2 hyc))

theorem normalJet_eq_iteratedDeriv {f : (ℝ × ℝ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2}) (n : ℕ) (x y : ℝ) (hy : 0<y) :
    iteratedDeriv n (fun u => f (u,y)) x=normalJet n f (x,y) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,show iteratedDeriv n (fun u => f (u,y))=(fun u => normalJet n f (u,y)) from funext ih]
    exact (planeDerivative_hasDerivAt_horizontal (normalJet_contDiffOn hf n) x y hy).deriv

/-- Analytic Cauchy uniqueness on the upper half-plane, using actual smoothness,
the hyperbolic eigenfunction equation, and horizontal real analyticity. -/
theorem planeEigenEquation_zero_cauchy {f : (ℝ × ℝ) → ℂ} {lam : ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2}) (he : planeEigenEquation lam f)
    (ha : ∀ y : ℝ,0<y → AnalyticOnNhd ℝ (fun x => f (x,y)) univ)
    (hzero : ∀ y : ℝ,0<y → f (0,y)=0)
    (hone : ∀ y : ℝ,0<y → planeDerivative (1,0) f (0,y)=0) :
    ∀ x y : ℝ,0<y → f (x,y)=0 := by
  intro x y hy
  have hh := analytic_line_zero_of_all_derivatives (x:=0) (ha y hy) (fun n => by
    rw [normalJet_eq_iteratedDeriv hf n 0 y hy]
    exact normalJet_axis_zero hf he hzero hone n y hy)
  exact congrFun hh x

#print axioms normalJet_contDiffOn
#print axioms normalJet_eigenEquation
#print axioms planeDerivative_vertical_axis_zero
#print axioms planeDerivative_vertical_twice_axis_zero
#print axioms normalJet_axis_zero
#print axioms normalJet_eq_iteratedDeriv
#print axioms planeEigenEquation_zero_cauchy

end QuantitativeMaass
