module

public import MaassSecondCurveV1
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 30000

@[expose] public section

namespace MaassDifferential

noncomputable def F (L x y : ℝ) : Point :=
  (-x/(L*(x^2+y^2)), y/(L*(x^2+y^2)))
noncomputable def a (L x y : ℝ) := (x^2-y^2)/(L*(x^2+y^2)^2)
noncomputable def b (L x y : ℝ) := (2*x*y)/(L*(x^2+y^2)^2)
noncomputable def aa (L x y : ℝ) := (2*x*(3*y^2-x^2))/(L*(x^2+y^2)^3)
noncomputable def bb (L x y : ℝ) := (2*y*(3*x^2-y^2))/(L*(x^2+y^2)^3)

theorem radius_pos {x y : ℝ} (hy : 0<y) : 0<x^2+y^2 := by
  nlinarith [sq_nonneg x]

theorem F_height_pos {L x y : ℝ} (hL : 0<L) (hy : 0<y) : 0<(F L x y).2 :=
  div_pos hy (mul_pos hL (radius_pos hy))

theorem F_hasDerivAt_X {L x y : ℝ} (hL : 0<L) (hr : x^2+y^2≠0) :
    HasDerivAt (fun z => F L z y) (a L x y,-b L x y) x := by
  have hd := (((hasDerivAt_id x).pow 2).add_const (y^2)).const_mul L
  have hn : L*(x^2+y^2)≠0 := mul_ne_zero hL.ne' hr
  have h1 := (hasDerivAt_id x).neg.div hd hn
  have h2 := (hasDerivAt_const x y).div hd hn
  apply (h1.prodMk h2).congr_deriv
  apply Prod.ext
  · dsimp [a]
    field_simp
    ring
  · dsimp [b]
    field_simp
    ring

theorem F_hasDerivAt_Y {L x y : ℝ} (hL : 0<L) (hr : x^2+y^2≠0) :
    HasDerivAt (fun z => F L x z) (b L x y,a L x y) y := by
  have hd := (((hasDerivAt_id y).pow 2).const_add (x^2)).const_mul L
  have hn : L*(x^2+y^2)≠0 := mul_ne_zero hL.ne' hr
  have h1 := (hasDerivAt_const y (-x)).div hd hn
  have h2 := (hasDerivAt_id y).div hd hn
  apply (h1.prodMk h2).congr_deriv
  apply Prod.ext
  · dsimp [b]
    field_simp
    ring
  · dsimp [a]
    field_simp
    ring

theorem F_scale {L x y : ℝ} (hL : 0<L) (hr : x^2+y^2≠0) :
    y^2*(a L x y^2+b L x y^2)=(F L x y).2^2 := by
  dsimp [a,b,F]
  field_simp
  ring

#print axioms F_hasDerivAt_X
#print axioms F_hasDerivAt_Y
#print axioms F_scale

end MaassDifferential
