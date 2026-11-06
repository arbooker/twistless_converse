module

public import SmallLevelTwentyOneTheoryV4

set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentyOneFirstJet

/-- The three reduced scalar equations suffice without any division by
the Hecke eigenvalue a. Their occurrence at actual poles is a separate
analytic/certificate-linkage obligation. -/
theorem conditions_of_three_residuals (E u v x y z a : ℂ)
    (hE : E≠0) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (h0 : (-7*E*y/z)*(a*x+x^2-1)=0)
    (h1 : (98*E/(x^2*z))*(y+3*u)=0)
    (h2 : (v-E*u-z-E*y+E*(u-y)*(a*x+x^2))/z=0) :
    a*x+x^2-1=0 ∧ y+3*u=0 ∧ z=6*E*u+v := by
  have hc0 : -7*E*y/z≠0 := div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hE) hy) hz
  have hc1 : 98*E/(x^2*z)≠0 := div_ne_zero
    (mul_ne_zero (by norm_num) hE) (mul_ne_zero (pow_ne_zero _ hx) hz)
  have ha := (mul_eq_zero.mp h0).resolve_left hc0
  have hb := (mul_eq_zero.mp h1).resolve_left hc1
  have hc := (div_eq_zero_iff.mp h2).resolve_right hz
  refine ⟨ha,hb,?_⟩
  apply sub_eq_zero.mp
  linear_combination -hc+E*(u-y)*ha-2*E*hb

theorem written_sign_value (E u v : ℂ) (hE : E=1 ∨ E= -1) (hu : u=1 ∨ u= -1) :
    6*E*u+v=E*u*(6+E*u*v) := by
  rcases hE with rfl|rfl <;> rcases hu with rfl|rfl <;> ring

#print axioms conditions_of_three_residuals
#print axioms written_sign_value
end SmallLevelTwentyOneFirstJet
