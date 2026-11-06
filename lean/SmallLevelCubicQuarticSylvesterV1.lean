module
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelCubicQuarticSylvester
open Complex

/-- The seven coefficient identities in a cubic/quartic Bezout certificate
imply its constant resultant vanishes at every common root. -/
theorem resultant_zero
    (r0 r1 r2 r3 v0 v1 v2 v3 v4 c0 c1 c2 c3 c4 c5 c6 D a : ℂ)
    (h0 : c0*r0+c4*v0=D)
    (h1 : c0*r1+c1*r0+c4*v1+c5*v0=0)
    (h2 : c0*r2+c1*r1+c2*r0+c4*v2+c5*v1+c6*v0=0)
    (h3 : c0*r3+c1*r2+c2*r1+c3*r0+c4*v3+c5*v2+c6*v1=0)
    (h4 : c1*r3+c2*r2+c3*r1+c4*v4+c5*v3+c6*v2=0)
    (h5 : c2*r3+c3*r2+c5*v4+c6*v3=0)
    (h6 : c3*r3+c6*v4=0)
    (hr : r0+r1*a+r2*a^2+r3*a^3=0)
    (hv : v0+v1*a+v2*a^2+v3*a^3+v4*a^4=0) : D=0 := by
  have h : D=(c0+c1*a+c2*a^2+c3*a^3)*(r0+r1*a+r2*a^2+r3*a^3)+
      (c4+c5*a+c6*a^2)*(v0+v1*a+v2*a^2+v3*a^3+v4*a^4) := by
    linear_combination -h0-a*h1-a^2*h2-a^3*h3-a^4*h4-a^5*h5-a^6*h6
  rw [hr,hv,mul_zero,mul_zero,add_zero] at h
  exact h

#print axioms resultant_zero
end SmallLevelCubicQuarticSylvester
