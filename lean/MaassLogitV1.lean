module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

set_option autoImplicit false

@[expose] public section

open Set

namespace MaassMellin

noncomputable def logit (u : ℝ) : ℝ := (Real.log u - Real.log (1-u))/2
noncomputable def logistic (r : ℝ) : ℝ := Real.exp (2*r)/(1+Real.exp (2*r))

theorem logistic_mem (r : ℝ) : logistic r ∈ Ioo (0:ℝ) 1 := by
  have he := Real.exp_pos (2*r)
  constructor
  · exact div_pos he (by linarith)
  · dsimp [logistic]
    exact (div_lt_one (by linarith)).mpr (by linarith)

theorem exp_two_logit {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    Real.exp (2*logit u) = u/(1-u) := by
  rw [show 2*logit u = Real.log u - Real.log (1-u) by unfold logit; ring,
    Real.exp_sub, Real.exp_log hu.1, Real.exp_log (sub_pos.mpr hu.2)]

theorem logistic_logit {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) : logistic (logit u) = u := by
  have hv : 1-u ≠ 0 := (sub_pos.mpr hu.2).ne'
  dsimp [logistic]
  rw [exp_two_logit hu]
  field_simp
  ring

theorem logit_logistic (r : ℝ) : logit (logistic r) = r := by
  apply (mul_left_cancel₀ (two_ne_zero : (2:ℝ)≠0))
  apply Real.exp_injective
  rw [exp_two_logit (logistic_mem r)]
  dsimp [logistic]
  have he : 1+Real.exp (2*r) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem logit_injOn : InjOn logit (Ioo (0:ℝ) 1) := by
  intro u hu v hv huv
  have h := congrArg logistic huv
  simpa only [logistic_logit hu, logistic_logit hv] using h

theorem logit_image : logit '' Ioo (0:ℝ) 1 = univ := by
  apply eq_univ_of_forall
  intro r
  exact ⟨logistic r, logistic_mem r, logit_logistic r⟩

theorem logit_hasDerivAt {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    HasDerivAt logit (1/(2*u*(1-u))) u := by
  have hv : 1-u ≠ 0 := (sub_pos.mpr hu.2).ne'
  have h := ((Real.hasDerivAt_log hu.1.ne').sub
    (((hasDerivAt_id u).const_sub 1).log hv)).div_const 2
  convert h using 1
  · rfl
  · dsimp
    field_simp [hu.1.ne', hv]
    ring

theorem log_cosh_logit {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    Real.log (Real.cosh (logit u)) =
      -Real.log 2 - (Real.log u + Real.log (1-u))/2 := by
  have hv : 0<1-u := sub_pos.mpr hu.2
  have hp : Real.exp (logit u) * Real.exp ((Real.log u + Real.log (1-u))/2) = u := by
    rw [← Real.exp_add]
    convert Real.exp_log hu.1 using 1
    congr 1
    unfold logit
    ring
  have hm : Real.exp (-logit u) * Real.exp ((Real.log u + Real.log (1-u))/2) = 1-u := by
    rw [← Real.exp_add]
    convert Real.exp_log hv using 1
    congr 1
    unfold logit
    ring
  have hc : Real.cosh (logit u) * Real.exp ((Real.log u + Real.log (1-u))/2) = 1/2 := by
    rw [Real.cosh_eq]
    nlinarith
  have hl := congrArg Real.log hc
  rw [Real.log_mul (Real.cosh_pos _).ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_div one_ne_zero (two_ne_zero : (2:ℝ)≠0), Real.log_one] at hl
  linarith

#print axioms logit_image
#print axioms logit_hasDerivAt
#print axioms log_cosh_logit

end MaassMellin
