module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

set_option autoImplicit false

@[expose] public section

namespace MaassSqrtRescaling

noncomputable def W (k : ℝ → ℝ) (x : ℝ) := Real.sqrt x * k x

noncomputable def W₁ (k k₁ : ℝ → ℝ) (x : ℝ) :=
  k x / (2 * Real.sqrt x) + Real.sqrt x * k₁ x

noncomputable def W₂ (k k₁ k₂ : ℝ → ℝ) (x : ℝ) :=
  -(k x / (4 * x * Real.sqrt x)) + k₁ x / Real.sqrt x + Real.sqrt x * k₂ x

theorem W_hasDerivAt {k k₁ : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hk : HasDerivAt k (k₁ x) x) :
    HasDerivAt (W k) (W₁ k k₁ x) x := by
  convert (Real.hasDerivAt_sqrt hx.ne').mul hk using 1
  all_goals try dsimp [W, W₁]
  all_goals try rfl
  all_goals ring

theorem W₁_hasDerivAt {k k₁ k₂ : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hk : HasDerivAt k (k₁ x) x)
    (hk₁ : HasDerivAt k₁ (k₂ x) x) :
    HasDerivAt (W₁ k k₁) (W₂ k k₁ k₂ x) x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hd := Real.hasDerivAt_sqrt hx.ne'
  convert (hk.div (hd.const_mul 2) (by positivity : 2 * Real.sqrt x ≠ 0)).add
    (hd.mul hk₁) using 1
  all_goals try dsimp [W₁, W₂]
  all_goals try rfl
  all_goals field_simp [hx.ne', hs.ne']
  all_goals rw [Real.sq_sqrt hx.le]
  all_goals ring

/-- The rescaled differential equation, with the spectral coefficient
shown explicitly. This lemma only performs the algebraic change of variable. -/
theorem rescaled_ode {k k₁ k₂ : ℝ → ℝ} {x lam : ℝ} (hx : 0 < x)
    (hode : x^2 * k₂ x + x * k₁ x + (lam-1/4-x^2)*k x = 0) :
    W₂ k k₁ k₂ x = (1-lam/x^2) * W k x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  dsimp [W₂, W]
  field_simp
  rw [Real.sq_sqrt hx.le]
  nlinarith [congrArg (fun z : ℝ => 4*x*z) hode]

#print axioms W₁_hasDerivAt
#print axioms rescaled_ode

end MaassSqrtRescaling
