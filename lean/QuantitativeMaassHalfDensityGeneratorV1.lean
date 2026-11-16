module

public import QuantitativeMaassZeroChannelLaplacianV1
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace QuantitativeMaass

/-- The geometric half-density conjugation from positive height to log height. -/
def logHalfDensity (C : ℝ → ℂ) (u : ℝ) : ℂ := (Real.exp (-u/2):ℂ)*C (Real.exp u)

def logHalfDensityFirst (C C₁ : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Real.exp (-u/2):ℂ)*((Real.exp u:ℂ)*C₁ (Real.exp u)-C (Real.exp u)/2)

theorem exp_halfWeight_hasDerivAt (u : ℝ) :
    HasDerivAt (fun v : ℝ => (Real.exp (-v/2):ℂ))
      (-(Real.exp (-u/2):ℂ)/2) u := by
  have h := ((Real.hasDerivAt_exp (-u/2)).comp u ((hasDerivAt_id u).neg.div_const 2)).ofReal_comp
  convert h using 1
  simp
  push_cast
  ring

theorem comp_exp_hasDerivAt (C C₁ : ℝ → ℂ)
    (hC : ∀ y, 0<y → HasDerivAt C (C₁ y) y) (u : ℝ) :
    HasDerivAt (fun v => C (Real.exp v)) ((Real.exp u:ℂ)*C₁ (Real.exp u)) u := by
  simpa only [Function.comp_def,Complex.real_smul] using
    (hC _ (Real.exp_pos u)).scomp u (Real.hasDerivAt_exp u)

theorem logHalfDensity_hasDerivAt (C C₁ : ℝ → ℂ)
    (hC : ∀ y, 0<y → HasDerivAt C (C₁ y) y) (u : ℝ) :
    HasDerivAt (logHalfDensity C) (logHalfDensityFirst C C₁ u) u := by
  convert (exp_halfWeight_hasDerivAt u).mul (comp_exp_hasDerivAt C C₁ hC u) using 1
  · funext v
    rfl
  · unfold logHalfDensityFirst
    ring

theorem logHalfDensityFirst_hasDerivAt (C C₁ C₂ : ℝ → ℂ)
    (hC : ∀ y, 0<y → HasDerivAt C (C₁ y) y)
    (hC₁ : ∀ y, 0<y → HasDerivAt C₁ (C₂ y) y) (u : ℝ) :
    HasDerivAt (logHalfDensityFirst C C₁)
      ((Real.exp (-u/2):ℂ)*((Real.exp u:ℂ)^2*C₂ (Real.exp u)+C (Real.exp u)/4)) u := by
  have he := (Real.hasDerivAt_exp u).ofReal_comp
  have hc := comp_exp_hasDerivAt C C₁ hC u
  have hc₁ := comp_exp_hasDerivAt C₁ C₂ hC₁ u
  convert (exp_halfWeight_hasDerivAt u).mul ((he.mul hc₁).sub (hc.div_const 2)) using 1
  · funext v
    rfl
  · dsimp only [Pi.sub_apply,Pi.mul_apply]
    ring

/-- Exact differential conjugation: subtracting 1/4 from the zero-channel
hyperbolic Laplacian becomes the free operator -d²/du². This identifies the
correct wave generator and the spectral shift without a resolution axiom. -/
theorem logHalfDensity_generator (C C₁ C₂ : ℝ → ℂ)
    (hC : ∀ y, 0<y → HasDerivAt C (C₁ y) y)
    (hC₁ : ∀ y, 0<y → HasDerivAt C₁ (C₂ y) y) (u : ℝ) :
    -deriv (deriv (logHalfDensity C)) u =
      (Real.exp (-u/2):ℂ)*(-(Real.exp u:ℂ)^2*deriv (deriv C) (Real.exp u)-C (Real.exp u)/4) := by
  have he : deriv (logHalfDensity C)=logHalfDensityFirst C C₁ :=
    funext fun v => (logHalfDensity_hasDerivAt C C₁ hC v).deriv
  have heC : deriv C =ᶠ[𝓝 (Real.exp u)] C₁ := by
    filter_upwards [Ioi_mem_nhds (Real.exp_pos u)] with y hy
    exact (hC y hy).deriv
  rw [he,(logHalfDensityFirst_hasDerivAt C C₁ C₂ hC hC₁ u).deriv,
    heC.deriv_eq,(hC₁ _ (Real.exp_pos u)).deriv]
  ring

#print axioms logHalfDensity_generator

end QuantitativeMaass
