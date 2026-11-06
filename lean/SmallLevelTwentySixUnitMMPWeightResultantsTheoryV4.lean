module

public import SmallLevelTwentySixUnitMMPTheoryV4

/-! Consolidated chapter: SmallLevelTwentySixUnitMMP.WeightResultants. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixUnitMMPWeightResultantsV1 -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMP.WeightResultants
open Complex
def p0 (x y z w a b t : ℂ) : ℂ := ((-2)*y) + ((-2)*y*t) + (2*y*a*t) + (2*y^2) + ((-2)*x*y*t) + ((-2)*x*y^2) + ((-3)*x^2) + ((-3)*x^2*t) + ((-2)*x^2*a) + (1*x^2*a*t) + ((-1)*x^2*z) + (2*x^2*y) + ((-1)*x^2*y*t) + ((-2)*x^3) + ((-2)*x^3*t) + (1*x^3*a) + ((-1)*x^3*y) + ((-1)*x^4) + ((-2)*x^4*t)

def p1 (x y z w a b t : ℂ) : ℂ := ((-1)) + ((-1)*t) + ((-1)*a) + (1*a^2*t) + ((-1)*y*t) + (1*y*a) + (1*y*a*t) + (1*y^2) + ((-1)*x*t) + ((-1)*x*a*t) + ((-1)*x*y) + ((-1)*x*y*t) + ((-1)*x*y*a) + ((-1)*x*y^2) + ((-1)*x^2) + (1*x^3)

def p2 (x y z w a b t : ℂ) : ℂ := (2*y) + (2*y*t) + ((-2)*y*a*t) + ((-2)*y^2) + (2*x) + (2*x*t) + ((-2)*x*a*t) + ((-4)*x*y) + (2*x*y*a*t) + (4*x*y^2) + (3*x^2) + (2*x^2*t) + (1*x^2*b) + (1*x^2*a) + (1*x^2*w) + (1*x^2*z) + (1*x^2*y) + ((-2)*x^2*y^2) + ((-3)*x^3) + ((-1)*x^3*t) + ((-1)*x^3*b) + ((-2)*x^3*a) + (1*x^3*a*t) + ((-1)*x^3*w) + ((-1)*x^3*z) + (2*x^3*y) + ((-3)*x^3*y*t) + ((-1)*x^4) + ((-1)*x^4*t) + (1*x^4*a) + (1*x^4*a*t) + ((-1)*x^4*y) + (1*x^4*y*t) + ((-1)*x^5) + ((-2)*x^5*t)

def p3 (x y z w a b t : ℂ) : ℂ := ((-2)*y) + ((-2)*y*t) + (2*y*a*t) + (2*y^2) + (1*x) + (1*x*t) + ((-1)*x*b) + ((-1)*x*b*t) + ((-1)*x*a*t) + (1*x*a*b*t) + (1*x*w) + (1*x*w*t) + ((-1)*x*w*a*t) + ((-1)*x*y) + ((-2)*x*y*t) + (1*x*y*b) + ((-1)*x*y*w) + ((-2)*x*y^2) + ((-1)*x^2*t) + ((-1)*x^2*b*t) + ((-2)*x^2*a) + (1*x^2*w*t) + (1*x^2*y) + ((-1)*x^2*y*b) + (1*x^2*y*w) + ((-1)*x^3) + (1*x^3*t) + (2*x^3*a) + (1*x^4) + (1*x^5*t)

def p4 (x y z w a b t : ℂ) : ℂ := ((-2)*y) + ((-2)*y*t) + (2*y*a*t) + (2*y^2) + ((-2)*x) + ((-2)*x*t) + (2*x*a*t) + (2*x*y) + ((-2)*x*y*t) + ((-2)*x*y^2) + ((-5)*x^2) + ((-4)*x^2*t) + ((-1)*x^2*b) + ((-1)*x^2*a) + (2*x^2*a*t) + ((-1)*x^2*w) + ((-1)*x^2*z) + (1*x^2*y) + ((-2)*x^2*y*t) + ((-2)*x^3) + ((-3)*x^3*t) + (1*x^3*a) + (1*x^3*a*t) + ((-1)*x^3*y) + (1*x^3*y*t) + ((-1)*x^4) + ((-2)*x^4*t)

def r (x y z w a b t : ℂ) : ℂ := (2*a^2) + (2*a^3) + ((-1)*z) + (1*z*a^2) + (2*y) + ((-3)*y*a) + (1*y*a^2) + ((-1)*y*z) + (1*y*z*a) + ((-1)*y^2) + ((-2)*y^2*a) + ((-1)*y^3) + ((-3)*x) + ((-2)*x*a) + ((-1)*x*a^3) + ((-1)*x*z) + ((-1)*x*z*a) + ((-1)*x*y) + (5*x*y*a) + ((-1)*x*y*a^2) + ((-1)*x*y*z) + (3*x*y^2) + (1*x*y^2*a) + (1*x*y^3) + (2*x^2) + (2*x^2*a^2) + ((-3)*x^2*y) + (1*x^2*y*a) + ((-1)*x^2*y^2) + ((-2)*x^3) + (2*x^3*y*a) + (2*x^3*y^2) + ((-2)*x^5)

def v (x y z w a b t : ℂ) : ℂ := (8*y^2) + ((-16)*y^2*a) + (8*y^2*a^2) + (4*y^2*z) + ((-8)*y^2*z*a) + (4*y^2*z*a^2) + ((-8)*y^3) + (12*y^3*a) + ((-4)*y^3*a^2) + (4*y^4) + ((-4)*y^4*a) + (16*x*y*a^2) + ((-12)*x*y*a^3) + (4*x*y*a^4) + (8*x*y*w*a^2) + ((-8)*x*y*w*a^3) + ((-8)*x*y*z) + (14*x*y*z*a) + ((-8)*x*y*z*a^2) + (2*x*y*z*a^3) + ((-4)*x*y*z*w) + (8*x*y*z*w*a) + ((-4)*x*y*z*w*a^2) + (12*x*y^2) + ((-20)*x*y^2*a) + ((-10)*x*y^2*a^2) + (2*x*y^2*a^3) + ((-4)*x*y^2*w*a) + (4*x*y^2*w*a^2) + (14*x*y^2*z) + ((-14)*x*y^2*z*a) + ((-12)*x*y^3) + (12*x*y^3*a) + (2*x*y^3*a^2) + ((-4)*x*y^3*w) + (4*x*y^3*w*a) + ((-2)*x*y^3*z) + (2*x*y^3*z*a) + (6*x*y^4) + (2*x*y^4*a) + ((-2)*x*y^5) + (8*x^2*a^4) + ((-8)*x^2*z*a^2) + (8*x^2*z*a^3) + (2*x^2*z^2) + ((-4)*x^2*z^2*a) + (2*x^2*z^2*a^2) + ((-6)*x^2*y*a) + ((-4)*x^2*y*a^3) + ((-2)*x^2*y*a^4) + ((-12)*x^2*y*w) + (16*x^2*y*w*a) + (4*x^2*y*w*a^3) + ((-2)*x^2*y*z) + (2*x^2*y*z*a) + ((-4)*x^2*y*z*a^2) + ((-8)*x^2*y*z*w) + (8*x^2*y*z*w*a) + (26*x^2*y^2) + ((-20)*x^2*y^2*a) + (14*x^2*y^2*a^2) + (8*x^2*y^2*w) + ((-12)*x^2*y^2*w*a) + (12*x^2*y^2*z) + ((-2)*x^2*y^2*z*a) + ((-8)*x^2*y^3) + ((-4)*x^2*y^3*a) + ((-8)*x^2*y^3*a^2) + ((-4)*x^2*y^3*w*a) + (2*x^2*y^3*z) + ((-4)*x^2*y^3*z*a) + ((-6)*x^2*y^4) + (4*x^2*y^4*a) + (6*x^2*y^5) + (6*x^3*a^3) + ((-2)*x^3*a^4) + (12*x^3*w*a^2) + ((-4)*x^3*w*a^3) + ((-3)*x^3*z*a) + ((-2)*x^3*z*a^2) + (1*x^3*z*a^3) + ((-6)*x^3*z*w) + (8*x^3*z*w*a) + ((-2)*x^3*z*w*a^2) + (3*x^3*z^2) + ((-4)*x^3*z^2*a) + (1*x^3*z^2*a^2) + (2*x^3*y) + (14*x^3*y*a) + ((-19)*x^3*y*a^2) + (3*x^3*y*a^3) + ((-16)*x^3*y*w) + (10*x^3*y*w*a) + ((-6)*x^3*y*w*a^2) + (5*x^3*y*z) + (6*x^3*y*z*a) + ((-7)*x^3*y*z*a^2) + ((-6)*x^3*y*z*w) + (2*x^3*y*z*w*a) + (1*x^3*y*z^2) + ((-1)*x^3*y*z^2*a) + ((-20)*x^3*y^2*a) + ((-1)*x^3*y^2*a^2) + (4*x^3*y^2*a^3) + ((-2)*x^3*y^2*w) + (4*x^3*y^2*w*a) + ((-2)*x^3*y^2*z) + (1*x^3*y^2*z*a) + (2*x^3*y^2*z*a^2) + (21*x^3*y^3) + (7*x^3*y^3*a) + (6*x^3*y^3*a^2) + (2*x^3*y^3*w) + (3*x^3*y^3*z) + (2*x^3*y^3*z*a) + ((-11)*x^3*y^4) + ((-4)*x^3*y^4*a) + ((-6)*x^3*y^5) + ((-9)*x^4*a) + (2*x^4*a^2) + (14*x^4*a^3) + (1*x^4*a^4) + ((-18)*x^4*w) + (12*x^4*w*a) + (2*x^4*w*a^3) + (2*x^4*z) + ((-14)*x^4*z*a) + (6*x^4*z*a^2) + (2*x^4*z*a^3) + ((-10)*x^4*z*w) + (6*x^4*z*w*a) + (2*x^4*z^2) + ((-3)*x^4*z^2*a) + (1*x^4*z^2*a^2) + (13*x^4*y) + (2*x^4*y*a) + ((-17)*x^4*y*a^2) + (7*x^4*y*a^3) + ((-2)*x^4*y*w) + (6*x^4*y*w*a) + ((-2)*x^4*y*w*a^2) + (12*x^4*y*z) + ((-2)*x^4*y*z*a) + (4*x^4*y*z*a^2) + ((-2)*x^4*y*z*w) + (1*x^4*y*z^2*a) + (18*x^4*y^2) + ((-18)*x^4*y^2*a) + ((-3)*x^4*y^2*a^2) + ((-2)*x^4*y^2*a^3) + (10*x^4*y^2*w) + ((-10)*x^4*y^2*w*a) + ((-6)*x^4*y^2*z*a) + ((-25)*x^4*y^3) + ((-1)*x^4*y^3*a) + ((-2)*x^4*y^3*a^2) + (2*x^4*y^3*w) + ((-4)*x^4*y^3*z) + (16*x^4*y^4) + (2*x^4*y^4*a) + (2*x^4*y^5) + ((-9)*x^5) + ((-3)*x^5*a) + (5*x^5*a^3) + ((-3)*x^5*a^4) + ((-18)*x^5*w) + (18*x^5*w*a) + (1*x^5*z) + ((-11)*x^5*z*a) + (6*x^5*z*a^2) + ((-2)*x^5*z*a^3) + ((-8)*x^5*z*w) + (4*x^5*z*w*a) + (1*x^5*z^2) + ((-1)*x^5*z^2*a) + (4*x^5*y) + (6*x^5*y*a) + ((-7)*x^5*y*a^2) + ((-1)*x^5*y*a^3) + ((-4)*x^5*y*w) + (2*x^5*y*w*a) + ((-8)*x^5*y*z) + (6*x^5*y*z*a) + ((-1)*x^5*y*z*a^2) + ((-1)*x^5*y*z^2) + (22*x^5*y^2) + (1*x^5*y^2*a) + (11*x^5*y^2*a^2) + (6*x^5*y^2*w) + (4*x^5*y^2*z) + (2*x^5*y^2*z*a) + ((-13)*x^5*y^3) + (3*x^5*y^3*a) + (1*x^5*y^3*z) + ((-14)*x^5*y^4) + ((-7)*x^6) + ((-9)*x^6*a) + (6*x^6*a^2) + (1*x^6*a^3) + (1*x^6*a^4) + ((-22)*x^6*w) + (14*x^6*w*a) + ((-4)*x^6*w*a^2) + (2*x^6*z) + ((-8)*x^6*z*a) + (4*x^6*z*a^2) + ((-4)*x^6*z*w) + (9*x^6*y) + (9*x^6*y*a) + (14*x^6*y*w) + ((-4)*x^6*y*w*a) + ((-6)*x^6*y*z) + (4*x^6*y*z*a) + ((-3)*x^6*y^2) + ((-13)*x^6*y^2*a) + ((-2)*x^6*y^2*a^2) + (8*x^6*y^2*w) + ((-4)*x^6*y^2*z) + (4*x^6*y^3) + (4*x^6*y^3*a) + (5*x^6*y^4) + ((-17)*x^7) + (4*x^7*a) + ((-3)*x^7*a^3) + ((-8)*x^7*w) + (8*x^7*w*a) + ((-3)*x^7*z) + ((-1)*x^7*z*a) + (6*x^7*y) + (19*x^7*y*a) + (2*x^7*y*a^2) + (4*x^7*y*w) + ((-5)*x^7*y*z) + (2*x^7*y*z*a) + ((-7)*x^7*y^2) + (7*x^7*y^2*a) + (2*x^7*y^2*z) + ((-6)*x^7*y^3) + ((-8)*x^8) + (2*x^8*a) + (2*x^8*a^2) + ((-4)*x^8*w) + ((-2)*x^8*z) + (3*x^8*y) + (7*x^8*y*a) + ((-2)*x^8*y*a^2) + (8*x^8*y*w) + ((-3)*x^8*y^2) + (2*x^8*y^3) + ((-10)*x^9) + (6*x^9*a) + ((-2)*x^9*z) + ((-2)*x^9*y) + (2*x^9*y*a) + (2*x^9*y^2) + ((-2)*x^10) + (2*x^10*a) + ((-2)*x^10*y) + ((-2)*x^11)

def q (x y z w a b t : ℂ) : ℂ := (2*x^2) + (4*x^2*t) + (2*x^2*t^2) + ((-4)*x^2*a*t) + ((-4)*x^2*a*t^2) + (2*x^2*a^2*t^2) + ((-6)*x^2*y) + ((-6)*x^2*y*t) + (6*x^2*y*a*t) + (4*x^2*y^2) + (3*x^3) + (6*x^3*t) + (3*x^3*t^2) + ((-1)*x^3*a) + ((-5)*x^3*a*t) + ((-4)*x^3*a*t^2) + (1*x^3*a^2*t) + (1*x^3*a^2*t^2) + (2*x^3*w) + (2*x^3*w*t) + ((-2)*x^3*w*a*t) + ((-1)*x^3*y*t) + (1*x^3*y*t^2) + (1*x^3*y*a) + ((-2)*x^3*y*a*t) + ((-1)*x^3*y*a*t^2) + ((-2)*x^3*y*w) + ((-5)*x^3*y^2) + ((-1)*x^3*y^2*t) + (2*x^4*t) + (2*x^4*t^2) + ((-2)*x^4*a) + ((-2)*x^4*a*t) + ((-3)*x^4*a*t^2) + (1*x^4*a^2*t^2) + (2*x^4*w*t) + (3*x^4*y) + ((-1)*x^4*y*a) + (1*x^4*y*a*t^2) + (2*x^4*y*w) + (1*x^4*y^2) + (2*x^4*y^2*t) + ((-1)*x^5) + (1*x^5*t) + (1*x^5*t^2) + (2*x^5*a) + ((-1)*x^5*a*t^2) + (1*x^5*y*t) + ((-1)*x^5*y*t^2) + ((-1)*x^5*y*a*t) + ((-1)*x^5*y^2*t) + (1*x^6) + (1*x^7*t)

def l0 (x y z w a b t : ℂ) : ℂ := ((-2)*y) + (2*y*a) + ((-2)*x*y) + ((-3)*x^2) + (1*x^2*a) + ((-1)*x^2*y) + ((-2)*x^3) + ((-2)*x^4)

def l1 (x y z w a b t : ℂ) : ℂ := ((-1)) + (1*a^2) + ((-1)*y) + (1*y*a) + ((-1)*x) + ((-1)*x*a) + ((-1)*x*y)

def c0 (x y z w a b t : ℂ) : ℂ := ((-2)*y) + (2*y^2) + ((-2)*x*y^2) + ((-3)*x^2) + ((-2)*x^2*a) + ((-1)*x^2*z) + (2*x^2*y) + ((-2)*x^3) + (1*x^3*a) + ((-1)*x^3*y) + ((-1)*x^4)

def q1 (x y z w a b t : ℂ) : ℂ := (4*x^2) + ((-4)*x^2*a) + ((-6)*x^2*y) + (6*x^2*y*a) + (6*x^3) + ((-5)*x^3*a) + (1*x^3*a^2) + (2*x^3*w) + ((-2)*x^3*w*a) + ((-1)*x^3*y) + ((-2)*x^3*y*a) + ((-1)*x^3*y^2) + (2*x^4) + ((-2)*x^4*a) + (2*x^4*w) + (2*x^4*y^2) + (1*x^5) + (1*x^5*y) + ((-1)*x^5*y*a) + ((-1)*x^5*y^2) + (1*x^7)

def q2 (x y z w a b t : ℂ) : ℂ := (2*x^2) + ((-4)*x^2*a) + (2*x^2*a^2) + (3*x^3) + ((-4)*x^3*a) + (1*x^3*a^2) + (1*x^3*y) + ((-1)*x^3*y*a) + (2*x^4) + ((-3)*x^4*a) + (1*x^4*a^2) + (1*x^4*y*a) + (1*x^5) + ((-1)*x^5*a) + ((-1)*x^5*y)

def p3b (x y z w a b t : ℂ) : ℂ := ((-1)*x) + ((-1)*x*t) + (1*x*a*t) + (1*x*y) + ((-1)*x^2*t) + ((-1)*x^2*y)

theorem r_identity (x y z w a b t : ℂ) :
    x^2*r x y z w a b t=l0 x y z w a b t*p1 x y z w a b t-l1 x y z w a b t*p0 x y z w a b t := by
  unfold r l0 l1 p0 p1
  ring

theorem q_identity (x y z w a b t : ℂ) :
    q x y z w a b t=x^2*p3 x y z w a b t+p3b x y z w a b t*(p4 x y z w a b t-p0 x y z w a b t) := by
  unfold q p3 p3b p4 p0
  ring

theorem v_identity (x y z w a b t : ℂ) :
    x^4*v x y z w a b t=(l0 x y z w a b t)^2*q x y z w a b t-
      (l0 x y z w a b t*q2 x y z w a b t*t+l0 x y z w a b t*q1 x y z w a b t-q2 x y z w a b t*c0 x y z w a b t)*p0 x y z w a b t := by
  unfold v l0 q q2 q1 c0 p0
  ring

theorem necessary (x y z w a b t : ℂ) (hx : x≠0)
    (h0 : p0 x y z w a b t=0) (h1 : p1 x y z w a b t=0)
    (h3 : p3 x y z w a b t=0) (h4 : p4 x y z w a b t=0) :
    r x y z w a b t=0 ∧ v x y z w a b t=0 := by
  have hr : x^2*r x y z w a b t=0 := by rw [r_identity,h0,h1]; ring
  have hq : q x y z w a b t=0 := by rw [q_identity,h0,h3,h4]; ring
  have hv : x^4*v x y z w a b t=0 := by rw [v_identity,h0,hq]; ring
  exact ⟨(mul_eq_zero.mp hr).resolve_left (pow_ne_zero _ hx),
    (mul_eq_zero.mp hv).resolve_left (pow_ne_zero _ hx)⟩

theorem source_kernel_resultants (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (u : Fin 780→ℂ) (hu : ∀ i,sourceRows X Y Z W a b u i=0) (h300 : u 300≠0) :
    r X (Y^2) Z (W^2) (a*Y) (b*W) (u 540/u 300)=0 ∧
    v X (Y^2) Z (W^2) (a*Y) (b*W) (u 540/u 300)=0 := by
  apply necessary _ _ _ _ _ _ _ hX
  · have hh:=weight_row0 X Y Z W a b hX hY hZ hW u hu
    apply (mul_eq_zero.mp (show p0 X (Y^2) Z (W^2) (a*Y) (b*W) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
    unfold p0
    linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
  · have hh:=weight_row1 X Y Z W a b hX hY hZ hW u hu
    apply (mul_eq_zero.mp (show p1 X (Y^2) Z (W^2) (a*Y) (b*W) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
    unfold p1
    linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
  · have hh:=weight_row3 X Y Z W a b hX hY hZ hW u hu
    apply (mul_eq_zero.mp (show p3 X (Y^2) Z (W^2) (a*Y) (b*W) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
    unfold p3
    linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
  · have hh:=weight_row4 X Y Z W a b hX hY hZ hW u hu
    apply (mul_eq_zero.mp (show p4 X (Y^2) Z (W^2) (a*Y) (b*W) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
    unfold p4
    linear_combination (norm := (field_simp [h300]; all_goals ring)) hh

#print axioms necessary
#print axioms source_kernel_resultants
end SmallLevelTwentySixUnitMMP.WeightResultants
end
end

/-! ## SmallLevelTwentySixUnitMMPWeightTwoV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMP.WeightResultants
open Complex
theorem no_weight_two_plus (A B t : ℂ)
    (h0 : p0 2 9 13 25 A B t=0)
    (h1 : p1 2 9 13 25 A B t=0)
    (h2 : p2 2 9 13 25 A B t=0)
    (h3 : p3 2 9 13 25 A B t=0)
    (_h4 : p4 2 9 13 25 A B t=0)
    : False := by
  unfold p0 at h0
  unfold p1 at h1
  unfold p2 at h2
  unfold p3 at h3
  unfold p4 at _h4
  have hh : (1:ℂ)=0 := by
    linear_combination ((-3039761/2183832:ℂ))*h0 +
      ((-555763/727944:ℂ)*t)*h0 +
      ((16285/727944:ℂ)*B)*h0 +
      ((-4129/272979:ℂ)*B*t)*h0 +
      ((-4129/1091916:ℂ)*B^2)*h0 +
      ((-100715/545958:ℂ)*A)*h0 +
      ((63829/727944:ℂ)*A*t)*h0 +
      ((-935990/272979:ℂ))*h1 +
      ((-702119/363972:ℂ)*t)*h1 +
      ((4129/30331:ℂ)*B)*h1 +
      ((216325/363972:ℂ))*h2 +
      ((-125833/2183832:ℂ)*t)*h2 +
      ((4129/77994:ℂ)*B)*h2 +
      ((4129/51996:ℂ)*B*t)*h2 +
      ((4129/30331:ℂ)*A)*h2 +
      ((-3023063/2183832:ℂ))*h3 +
      ((-1465795/1091916:ℂ)*t)*h3 +
      ((45419/1091916:ℂ)*B)*h3 +
      ((-4129/60662:ℂ)*A)*h3
  norm_num at hh

theorem source_kernel_weight_two_plus (a b : ℂ) (u : Fin 780→ℂ)
    (hu : ∀ i,sourceRows 2 3 13 5 a b u i=0) : ∀ j : Fin 320,u (support j)=0 := by
  by_cases h300 : u 300=0
  · exact source_zero_chart 2 3 13 5 a b (Or.inl (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) u hu h300
  · exfalso
    apply no_weight_two_plus (a*3) (b*5) (u 540/u 300)
    · have hh:=weight_row0 2 3 13 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p0 2 9 13 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p0
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row1 2 3 13 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p1 2 9 13 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p1
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row2 2 3 13 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p2 2 9 13 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p2
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row3 2 3 13 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p3 2 9 13 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p3
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row4 2 3 13 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p4 2 9 13 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p4
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh

#print axioms source_kernel_weight_two_plus

theorem no_weight_two_minus (A B t : ℂ)
    (h0 : p0 2 9 (-13) 25 A B t=0)
    (h1 : p1 2 9 (-13) 25 A B t=0)
    (h2 : p2 2 9 (-13) 25 A B t=0)
    (h3 : p3 2 9 (-13) 25 A B t=0)
    (_h4 : p4 2 9 (-13) 25 A B t=0)
    : False := by
  unfold p0 at h0
  unfold p1 at h1
  unfold p2 at h2
  unfold p3 at h3
  unfold p4 at _h4
  have hh : (1:ℂ)=0 := by
    linear_combination ((10016593/3769767188:ℂ))*h0 +
      ((-38666433/7539534376:ℂ)*t)*h0 +
      ((-1759917/7539534376:ℂ)*B)*h0 +
      ((-3807/171353054:ℂ)*B*t)*h0 +
      ((-3807/685412216:ℂ)*B^2)*h0 +
      ((-2181545/3769767188:ℂ)*A)*h0 +
      ((6912915/7539534376:ℂ)*A*t)*h0 +
      ((3316165/342706108:ℂ))*h1 +
      ((-6912915/342706108:ℂ)*t)*h1 +
      ((19035/342706108:ℂ)*B)*h1 +
      ((-11522673/3769767188:ℂ))*h2 +
      ((16096923/1884883594:ℂ)*t)*h2 +
      ((-11421/171353054:ℂ)*B)*h2 +
      ((79947/685412216:ℂ)*B*t)*h2 +
      ((19035/342706108:ℂ)*A)*h2 +
      ((1494789/342706108:ℂ))*h3 +
      ((-1351485/685412216:ℂ)*t)*h3 +
      ((41877/685412216:ℂ)*B)*h3 +
      ((-19035/685412216:ℂ)*A)*h3
  norm_num at hh

theorem source_kernel_weight_two_minus (a b : ℂ) (u : Fin 780→ℂ)
    (hu : ∀ i,sourceRows 2 3 (-13) 5 a b u i=0) : ∀ j : Fin 320,u (support j)=0 := by
  by_cases h300 : u 300=0
  · exact source_zero_chart 2 3 (-13) 5 a b (Or.inl (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) u hu h300
  · exfalso
    apply no_weight_two_minus (a*3) (b*5) (u 540/u 300)
    · have hh:=weight_row0 2 3 (-13) 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p0 2 9 (-13) 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p0
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row1 2 3 (-13) 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p1 2 9 (-13) 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p1
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row2 2 3 (-13) 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p2 2 9 (-13) 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p2
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row3 2 3 (-13) 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p3 2 9 (-13) 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p3
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row4 2 3 (-13) 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p4 2 9 (-13) 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p4
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh

#print axioms source_kernel_weight_two_minus

end SmallLevelTwentySixUnitMMP.WeightResultants
end
end
