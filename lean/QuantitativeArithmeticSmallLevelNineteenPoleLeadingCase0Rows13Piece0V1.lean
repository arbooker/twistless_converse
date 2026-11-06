module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 6000
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading
theorem pivot0_3858 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (ha : a≠0) (v : Fin 114→ℂ)
    (hi : ((1))*v 16 + (((-1)*a)/(x))*v 32 + (((1))/(x^2))*v 64 + ((1))*v 73=0)
    (hp3742 : ((-1)*x^6 + (-1)*x^5*a + (-1)*x^4 + (-1)*x^3*a + (-1)*x^2*a^2 + (-1)*x*a + y^2)*v 18 + (((-1)*x^5*a + (-1)*x^4*a^2 + (-1)*x^3*a + (-1)*x^2 + (-1)*x*y*a*b + (-1)*x*a + (-1)*y*b)/(x*a))*v 42 + (((-1)*x^4*a + (-1)*x^3 + (-1)*x^2*a + (-1)*x*y*b + (-1)*y*a*b + a)/(a))*v 72 + ((1))*v 90=0)
    (hp3607 : (((-1)*x^5*a + (-1)*x^4*a^2 + x^3*y*a*b + (-1)*x^3*a + x^2*y*a^2*b + x*y*a*b + (1))/(x^2*y^2))*v 18 + (((-1)*x^4*a^2 + (-1)*x^3*a^3 + (-1)*x^2*a^2 + (-1)*x*a + (1))/(x^3*y^2*a))*v 42 + ((1))*v 70 + (((-1)*x^2*a^2 + (-1)*x*a + (-1)*a^2 + (1))/(x*y^2*a))*v 72=0)
    (hp3556 : (x^2 + x*a + (1))*v 18 + ((x^3*a + x^2*a^2 + x*a + (1))/(x^3*a))*v 42 + ((x^2*a + x + a)/(x^2*a))*v 72 + ((1))*v 93=0)
    (hp3463 : ((b)/(y))*v 18 + ((1))*v 32 + ((1))*v 70=0)
    (hp3115 : ((1))*v 16 + (((-1))/(y^2))*v 18 + (((-1)*x*a)/(y^2))*v 90=0)
    (hp2526 : ((1))*v 64 + (((-1)*x^2)/(y^2))*v 93=0)
    : ((x^10*a + x^9*a^2 + x^8*a + x^7*a^2 + x^6*a^3 + (2)*x^5*a^2 + (-1)*x^5 + (-1)*x^4*y^2*a + x^4*a^3 + (-1)*x^4*a + (-1)*x^3*y*a^2*b + x^3*a^2 + (-1)*x^2*y*a^3*b + x^2*y*a*b + (-1)*x*y*a^2*b + (-1)*a)/(x^3*y^2))*v 18 + ((x^9*a^2 + x^8*a^3 + x^7*a^2 + x^6*a + x^5*y*a^2*b + x^5*a^2 + x^4*y*a*b + x^4*a^3 + (-1)*x^4*a + x^3*a^4 + (-1)*x^3*a^2 + x^2*a^3 + (-1)*x^2*a + x*a^2 + (-1)*x + (-1)*a)/(x^4*y^2*a))*v 42 + ((x^7*a^2 + x^6*a + x^5*a^2 + x^4*y*a*b + x^3*y*a^2*b + (-1)*x^3*a^2 + x^2*a^3 + (-1)*x^2*a + x*a^2 + (-1)*x + a^3 + (-2)*a)/(x^2*y^2*a))*v 72 + ((1))*v 73=0 := by
  have c_hi : (x^2)*v 16 + ((-1)*x*a)*v 32 + ((1))*v 64 + (x^2)*v 73=0 := by
    calc (x^2)*v 16 + ((-1)*x*a)*v 32 + ((1))*v 64 + (x^2)*v 73 = (x^2)*(((1))*v 16 + (((-1)*a)/(x))*v 32 + (((1))/(x^2))*v 64 + ((1))*v 73) := by field_simp [hx,hy,hz,ha] <;> ring1
         _ = 0 := by rw [hi]; ring1
  have c_hp3742 : ((-1)*x^7*a + (-1)*x^6*a^2 + (-1)*x^5*a + (-1)*x^4*a^2 + (-1)*x^3*a^3 + (-1)*x^2*a^2 + x*y^2*a)*v 18 + ((-1)*x^5*a + (-1)*x^4*a^2 + (-1)*x^3*a + (-1)*x^2 + (-1)*x*y*a*b + (-1)*x*a + (-1)*y*b)*v 42 + ((-1)*x^5*a + (-1)*x^4 + (-1)*x^3*a + (-1)*x^2*y*b + (-1)*x*y*a*b + x*a)*v 72 + (x*a)*v 90=0 := by
    calc ((-1)*x^7*a + (-1)*x^6*a^2 + (-1)*x^5*a + (-1)*x^4*a^2 + (-1)*x^3*a^3 + (-1)*x^2*a^2 + x*y^2*a)*v 18 + ((-1)*x^5*a + (-1)*x^4*a^2 + (-1)*x^3*a + (-1)*x^2 + (-1)*x*y*a*b + (-1)*x*a + (-1)*y*b)*v 42 + ((-1)*x^5*a + (-1)*x^4 + (-1)*x^3*a + (-1)*x^2*y*b + (-1)*x*y*a*b + x*a)*v 72 + (x*a)*v 90 = (x*a)*(((-1)*x^6 + (-1)*x^5*a + (-1)*x^4 + (-1)*x^3*a + (-1)*x^2*a^2 + (-1)*x*a + y^2)*v 18 + (((-1)*x^5*a + (-1)*x^4*a^2 + (-1)*x^3*a + (-1)*x^2 + (-1)*x*y*a*b + (-1)*x*a + (-1)*y*b)/(x*a))*v 42 + (((-1)*x^4*a + (-1)*x^3 + (-1)*x^2*a + (-1)*x*y*b + (-1)*y*a*b + a)/(a))*v 72 + ((1))*v 90) := by field_simp [hx,hy,hz,ha] <;> ring1
         _ = 0 := by rw [hp3742]; ring1
  have c_hp3607 : ((-1)*x^6*a^2 + (-1)*x^5*a^3 + x^4*y*a^2*b + (-1)*x^4*a^2 + x^3*y*a^3*b + x^2*y*a^2*b + x*a)*v 18 + ((-1)*x^4*a^2 + (-1)*x^3*a^3 + (-1)*x^2*a^2 + (-1)*x*a + (1))*v 42 + (x^3*y^2*a)*v 70 + ((-1)*x^4*a^2 + (-1)*x^3*a + (-1)*x^2*a^2 + x^2)*v 72=0 := by
    calc ((-1)*x^6*a^2 + (-1)*x^5*a^3 + x^4*y*a^2*b + (-1)*x^4*a^2 + x^3*y*a^3*b + x^2*y*a^2*b + x*a)*v 18 + ((-1)*x^4*a^2 + (-1)*x^3*a^3 + (-1)*x^2*a^2 + (-1)*x*a + (1))*v 42 + (x^3*y^2*a)*v 70 + ((-1)*x^4*a^2 + (-1)*x^3*a + (-1)*x^2*a^2 + x^2)*v 72 = (x^3*y^2*a)*((((-1)*x^5*a + (-1)*x^4*a^2 + x^3*y*a*b + (-1)*x^3*a + x^2*y*a^2*b + x*y*a*b + (1))/(x^2*y^2))*v 18 + (((-1)*x^4*a^2 + (-1)*x^3*a^3 + (-1)*x^2*a^2 + (-1)*x*a + (1))/(x^3*y^2*a))*v 42 + ((1))*v 70 + (((-1)*x^2*a^2 + (-1)*x*a + (-1)*a^2 + (1))/(x*y^2*a))*v 72) := by field_simp [hx,hy,hz,ha] <;> ring1
         _ = 0 := by rw [hp3607]; ring1
  have c_hp3556 : (x^5*a + x^4*a^2 + x^3*a)*v 18 + (x^3*a + x^2*a^2 + x*a + (1))*v 42 + (x^3*a + x^2 + x*a)*v 72 + (x^3*a)*v 93=0 := by
    calc (x^5*a + x^4*a^2 + x^3*a)*v 18 + (x^3*a + x^2*a^2 + x*a + (1))*v 42 + (x^3*a + x^2 + x*a)*v 72 + (x^3*a)*v 93 = (x^3*a)*((x^2 + x*a + (1))*v 18 + ((x^3*a + x^2*a^2 + x*a + (1))/(x^3*a))*v 42 + ((x^2*a + x + a)/(x^2*a))*v 72 + ((1))*v 93) := by field_simp [hx,hy,hz,ha] <;> ring1
         _ = 0 := by rw [hp3556]; ring1
  have c_hp3463 : (b)*v 18 + (y)*v 32 + (y)*v 70=0 := by
    calc (b)*v 18 + (y)*v 32 + (y)*v 70 = (y)*(((b)/(y))*v 18 + ((1))*v 32 + ((1))*v 70) := by field_simp [hx,hy,hz,ha] <;> ring1
         _ = 0 := by rw [hp3463]; ring1
  have c_hp3115 : (y^2)*v 16 + ((-1))*v 18 + ((-1)*x*a)*v 90=0 := by
    calc (y^2)*v 16 + ((-1))*v 18 + ((-1)*x*a)*v 90 = (y^2)*(((1))*v 16 + (((-1))/(y^2))*v 18 + (((-1)*x*a)/(y^2))*v 90) := by field_simp [hx,hy,hz,ha] <;> ring1
         _ = 0 := by rw [hp3115]; ring1
  have c_hp2526 : (y^2)*v 64 + ((-1)*x^2)*v 93=0 := by
    calc (y^2)*v 64 + ((-1)*x^2)*v 93 = (y^2)*(((1))*v 64 + (((-1)*x^2)/(y^2))*v 93) := by field_simp [hx,hy,hz,ha] <;> ring1
         _ = 0 := by rw [hp2526]; ring1
  have hpoly : ((1))*((x^11*a^2 + x^10*a^3 + x^9*a^2 + x^8*a^3 + x^7*a^4 + (2)*x^6*a^3 + (-1)*x^6*a + (-1)*x^5*y^2*a^2 + x^5*a^4 + (-1)*x^5*a^2 + (-1)*x^4*y*a^3*b + x^4*a^3 + (-1)*x^3*y*a^4*b + x^3*y*a^2*b + (-1)*x^2*y*a^3*b + (-1)*x*a^2)*v 18 + (x^9*a^2 + x^8*a^3 + x^7*a^2 + x^6*a + x^5*y*a^2*b + x^5*a^2 + x^4*y*a*b + x^4*a^3 + (-1)*x^4*a + x^3*a^4 + (-1)*x^3*a^2 + x^2*a^3 + (-1)*x^2*a + x*a^2 + (-1)*x + (-1)*a)*v 42 + (x^9*a^2 + x^8*a + x^7*a^2 + x^6*y*a*b + x^5*y*a^2*b + (-1)*x^5*a^2 + x^4*a^3 + (-1)*x^4*a + x^3*a^2 + (-1)*x^3 + x^2*a^3 + (-2)*x^2*a)*v 72 + (x^4*y^2*a)*v 73)=0 := by
    linear_combination (norm := ring1) (x^2*y^2*a)*c_hi-(x^4*a)*c_hp3742-(a)*c_hp3607-(x)*c_hp3556-((-1)*x^3*y*a^2)*c_hp3463-(x^4*a)*c_hp3115-(x^2*a)*c_hp2526
  have hE : (((1)) : ℂ)≠0 := one_ne_zero
  have hzP : (x^11*a^2 + x^10*a^3 + x^9*a^2 + x^8*a^3 + x^7*a^4 + (2)*x^6*a^3 + (-1)*x^6*a + (-1)*x^5*y^2*a^2 + x^5*a^4 + (-1)*x^5*a^2 + (-1)*x^4*y*a^3*b + x^4*a^3 + (-1)*x^3*y*a^4*b + x^3*y*a^2*b + (-1)*x^2*y*a^3*b + (-1)*x*a^2)*v 18 + (x^9*a^2 + x^8*a^3 + x^7*a^2 + x^6*a + x^5*y*a^2*b + x^5*a^2 + x^4*y*a*b + x^4*a^3 + (-1)*x^4*a + x^3*a^4 + (-1)*x^3*a^2 + x^2*a^3 + (-1)*x^2*a + x*a^2 + (-1)*x + (-1)*a)*v 42 + (x^9*a^2 + x^8*a + x^7*a^2 + x^6*y*a*b + x^5*y*a^2*b + (-1)*x^5*a^2 + x^4*a^3 + (-1)*x^4*a + x^3*a^2 + (-1)*x^3 + x^2*a^3 + (-2)*x^2*a)*v 72 + (x^4*y^2*a)*v 73=0 := (mul_eq_zero.mp hpoly).resolve_left hE
  have hmul : (x^4*y^2*a)*(((x^10*a + x^9*a^2 + x^8*a + x^7*a^2 + x^6*a^3 + (2)*x^5*a^2 + (-1)*x^5 + (-1)*x^4*y^2*a + x^4*a^3 + (-1)*x^4*a + (-1)*x^3*y*a^2*b + x^3*a^2 + (-1)*x^2*y*a^3*b + x^2*y*a*b + (-1)*x*y*a^2*b + (-1)*a)/(x^3*y^2))*v 18 + ((x^9*a^2 + x^8*a^3 + x^7*a^2 + x^6*a + x^5*y*a^2*b + x^5*a^2 + x^4*y*a*b + x^4*a^3 + (-1)*x^4*a + x^3*a^4 + (-1)*x^3*a^2 + x^2*a^3 + (-1)*x^2*a + x*a^2 + (-1)*x + (-1)*a)/(x^4*y^2*a))*v 42 + ((x^7*a^2 + x^6*a + x^5*a^2 + x^4*y*a*b + x^3*y*a^2*b + (-1)*x^3*a^2 + x^2*a^3 + (-1)*x^2*a + x*a^2 + (-1)*x + a^3 + (-2)*a)/(x^2*y^2*a))*v 72 + ((1))*v 73)=0 := by
    calc (x^4*y^2*a)*(((x^10*a + x^9*a^2 + x^8*a + x^7*a^2 + x^6*a^3 + (2)*x^5*a^2 + (-1)*x^5 + (-1)*x^4*y^2*a + x^4*a^3 + (-1)*x^4*a + (-1)*x^3*y*a^2*b + x^3*a^2 + (-1)*x^2*y*a^3*b + x^2*y*a*b + (-1)*x*y*a^2*b + (-1)*a)/(x^3*y^2))*v 18 + ((x^9*a^2 + x^8*a^3 + x^7*a^2 + x^6*a + x^5*y*a^2*b + x^5*a^2 + x^4*y*a*b + x^4*a^3 + (-1)*x^4*a + x^3*a^4 + (-1)*x^3*a^2 + x^2*a^3 + (-1)*x^2*a + x*a^2 + (-1)*x + (-1)*a)/(x^4*y^2*a))*v 42 + ((x^7*a^2 + x^6*a + x^5*a^2 + x^4*y*a*b + x^3*y*a^2*b + (-1)*x^3*a^2 + x^2*a^3 + (-1)*x^2*a + x*a^2 + (-1)*x + a^3 + (-2)*a)/(x^2*y^2*a))*v 72 + ((1))*v 73) = (x^11*a^2 + x^10*a^3 + x^9*a^2 + x^8*a^3 + x^7*a^4 + (2)*x^6*a^3 + (-1)*x^6*a + (-1)*x^5*y^2*a^2 + x^5*a^4 + (-1)*x^5*a^2 + (-1)*x^4*y*a^3*b + x^4*a^3 + (-1)*x^3*y*a^4*b + x^3*y*a^2*b + (-1)*x^2*y*a^3*b + (-1)*x*a^2)*v 18 + (x^9*a^2 + x^8*a^3 + x^7*a^2 + x^6*a + x^5*y*a^2*b + x^5*a^2 + x^4*y*a*b + x^4*a^3 + (-1)*x^4*a + x^3*a^4 + (-1)*x^3*a^2 + x^2*a^3 + (-1)*x^2*a + x*a^2 + (-1)*x + (-1)*a)*v 42 + (x^9*a^2 + x^8*a + x^7*a^2 + x^6*y*a*b + x^5*y*a^2*b + (-1)*x^5*a^2 + x^4*a^3 + (-1)*x^4*a + x^3*a^2 + (-1)*x^3 + x^2*a^3 + (-2)*x^2*a)*v 72 + (x^4*y^2*a)*v 73 := by field_simp [hx,hy,hz,ha] <;> ring1
         _ = 0 := hzP
  exact (mul_eq_zero.mp hmul).resolve_left ((mul_ne_zero (mul_ne_zero (pow_ne_zero 4 hx) (pow_ne_zero 2 hy)) ha))

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
