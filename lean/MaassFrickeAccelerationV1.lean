module

public import MaassFrickeGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 30000

@[expose] public section

namespace MaassDifferential

theorem a_hasDerivAt_X {L x y : ℝ} (hL : 0<L) (hr : x^2+y^2≠0) :
    HasDerivAt (fun z => a L z y) (aa L x y) x := by
  have hnum := ((hasDerivAt_id x).pow 2).sub_const (y^2)
  have hden := ((((hasDerivAt_id x).pow 2).add_const (y^2)).pow 2).const_mul L
  apply (hnum.div hden (mul_ne_zero hL.ne' (pow_ne_zero 2 hr))).congr_deriv
  dsimp [aa]
  field_simp [hr,hL.ne']
  ring

theorem b_hasDerivAt_X {L x y : ℝ} (hL : 0<L) (hr : x^2+y^2≠0) :
    HasDerivAt (fun z => b L z y) (-bb L x y) x := by
  have hnum := ((hasDerivAt_id x).const_mul 2).mul_const y
  have hden := ((((hasDerivAt_id x).pow 2).add_const (y^2)).pow 2).const_mul L
  apply (hnum.div hden (mul_ne_zero hL.ne' (pow_ne_zero 2 hr))).congr_deriv
  dsimp [bb]
  field_simp [hr,hL.ne']
  ring

theorem a_hasDerivAt_Y {L x y : ℝ} (hL : 0<L) (hr : x^2+y^2≠0) :
    HasDerivAt (fun z => a L x z) (-bb L x y) y := by
  have hnum := ((hasDerivAt_id y).pow 2).const_sub (x^2)
  have hden := ((((hasDerivAt_id y).pow 2).const_add (x^2)).pow 2).const_mul L
  apply (hnum.div hden (mul_ne_zero hL.ne' (pow_ne_zero 2 hr))).congr_deriv
  dsimp [bb]
  field_simp [hr,hL.ne']
  ring

theorem b_hasDerivAt_Y {L x y : ℝ} (hL : 0<L) (hr : x^2+y^2≠0) :
    HasDerivAt (fun z => b L x z) (-aa L x y) y := by
  have hnum := (hasDerivAt_id y).const_mul (2*x)
  have hden := ((((hasDerivAt_id y).pow 2).const_add (x^2)).pow 2).const_mul L
  apply (hnum.div hden (mul_ne_zero hL.ne' (pow_ne_zero 2 hr))).congr_deriv
  dsimp [aa]
  field_simp [hr,hL.ne']
  ring

theorem velocity_hasDerivAt_X {L x y : ℝ} (hL : 0<L) (hr : x^2+y^2≠0) :
    HasDerivAt (fun z => (a L z y,-b L z y)) (aa L x y,bb L x y) x := by
  simpa only [Pi.neg_apply,neg_neg] using (a_hasDerivAt_X hL hr).prodMk (b_hasDerivAt_X hL hr).neg

theorem velocity_hasDerivAt_Y {L x y : ℝ} (hL : 0<L) (hr : x^2+y^2≠0) :
    HasDerivAt (fun z => (b L x z,a L x z)) (-aa L x y,-bb L x y) y :=
  (b_hasDerivAt_Y hL hr).prodMk (a_hasDerivAt_Y hL hr)

#print axioms velocity_hasDerivAt_X
#print axioms velocity_hasDerivAt_Y

end MaassDifferential
