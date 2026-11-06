module

public import SmallLevelExponentialDominanceV1

/-! Consolidated chapter: SmallLevelTwentyOneChiFiveObstruction. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyOneChiFiveObstructionV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFiveObstruction

def obstruction (r t : ℝ) : ℝ :=
  (64)*r^8*t^0+(72)*r^7*t^0+(-36)*r^6*t^2+(52)*r^6*t^0+(72)*r^5*t^2+(18)*r^5*t^0+(-55)*r^4*t^2+(73)*r^4*t^0+(-126)*r^3*t^2+(72)*r^3*t^0+(-52)*r^2*t^2+(36)*r^2*t^0+(-72)*r^1*t^2+(-64)*r^0*t^2

def bases : Fin 13 → ℝ := ![256,128,64,288,32,144,16,72,8,36,4,18,9]
def coefficients : Fin 13 → ℝ := ![(-16/9),(-2),(-13/9),(-2),(-1/2),(55/36),(-73/36),(7/2),(-2),(13/9),(-1),(2),(16/9)]

theorem obstruction_eval (n : ℕ) :
    obstruction (2^n) (3^n)= -36*((576:ℝ)^n+∑ i, coefficients i*bases i^n) := by
  have h0 : ((2:ℝ)^n)^8*((3:ℝ)^n)^0=(256:ℝ)^n := by
    calc
      _ = ((2:ℝ)^8*(3:ℝ)^0)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  have h1 : ((2:ℝ)^n)^7*((3:ℝ)^n)^0=(128:ℝ)^n := by
    calc
      _ = ((2:ℝ)^7*(3:ℝ)^0)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  have h2 : ((2:ℝ)^n)^6*((3:ℝ)^n)^2=(576:ℝ)^n := by
    calc
      _ = ((2:ℝ)^6*(3:ℝ)^2)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  have h3 : ((2:ℝ)^n)^6*((3:ℝ)^n)^0=(64:ℝ)^n := by
    calc
      _ = ((2:ℝ)^6*(3:ℝ)^0)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  have h4 : ((2:ℝ)^n)^5*((3:ℝ)^n)^2=(288:ℝ)^n := by
    calc
      _ = ((2:ℝ)^5*(3:ℝ)^2)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  have h5 : ((2:ℝ)^n)^5*((3:ℝ)^n)^0=(32:ℝ)^n := by
    calc
      _ = ((2:ℝ)^5*(3:ℝ)^0)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  have h6 : ((2:ℝ)^n)^4*((3:ℝ)^n)^2=(144:ℝ)^n := by
    calc
      _ = ((2:ℝ)^4*(3:ℝ)^2)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  have h7 : ((2:ℝ)^n)^4*((3:ℝ)^n)^0=(16:ℝ)^n := by
    calc
      _ = ((2:ℝ)^4*(3:ℝ)^0)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  have h8 : ((2:ℝ)^n)^3*((3:ℝ)^n)^2=(72:ℝ)^n := by
    calc
      _ = ((2:ℝ)^3*(3:ℝ)^2)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  have h9 : ((2:ℝ)^n)^3*((3:ℝ)^n)^0=(8:ℝ)^n := by
    calc
      _ = ((2:ℝ)^3*(3:ℝ)^0)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  have h10 : ((2:ℝ)^n)^2*((3:ℝ)^n)^2=(36:ℝ)^n := by
    calc
      _ = ((2:ℝ)^2*(3:ℝ)^2)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  have h11 : ((2:ℝ)^n)^2*((3:ℝ)^n)^0=(4:ℝ)^n := by
    calc
      _ = ((2:ℝ)^2*(3:ℝ)^0)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  have h12 : ((2:ℝ)^n)^1*((3:ℝ)^n)^2=(18:ℝ)^n := by
    calc
      _ = ((2:ℝ)^1*(3:ℝ)^2)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  have h13 : ((2:ℝ)^n)^0*((3:ℝ)^n)^2=(9:ℝ)^n := by
    calc
      _ = ((2:ℝ)^0*(3:ℝ)^2)^n := by simp only [mul_pow,← pow_mul,Nat.mul_comm n]
      _ = _ := by norm_num
  calc
    _ = (64:ℝ)*(((2:ℝ)^n)^8*((3:ℝ)^n)^0)+(72:ℝ)*(((2:ℝ)^n)^7*((3:ℝ)^n)^0)+(-36:ℝ)*(((2:ℝ)^n)^6*((3:ℝ)^n)^2)+(52:ℝ)*(((2:ℝ)^n)^6*((3:ℝ)^n)^0)+(72:ℝ)*(((2:ℝ)^n)^5*((3:ℝ)^n)^2)+(18:ℝ)*(((2:ℝ)^n)^5*((3:ℝ)^n)^0)+(-55:ℝ)*(((2:ℝ)^n)^4*((3:ℝ)^n)^2)+(73:ℝ)*(((2:ℝ)^n)^4*((3:ℝ)^n)^0)+(-126:ℝ)*(((2:ℝ)^n)^3*((3:ℝ)^n)^2)+(72:ℝ)*(((2:ℝ)^n)^3*((3:ℝ)^n)^0)+(-52:ℝ)*(((2:ℝ)^n)^2*((3:ℝ)^n)^2)+(36:ℝ)*(((2:ℝ)^n)^2*((3:ℝ)^n)^0)+(-72:ℝ)*(((2:ℝ)^n)^1*((3:ℝ)^n)^2)+(-64:ℝ)*(((2:ℝ)^n)^0*((3:ℝ)^n)^2) := by unfold obstruction; ring
    _ = _ := by
      rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13]
      norm_num [bases,coefficients,Fin.sum_univ_succ]
      ring

/-- The exact dominant-base inequality applies uniformly to all shifts,
including the three initial cases checked separately. -/
theorem obstruction_nonzero (n : ℕ) : obstruction (2^n) (3^n)≠0 := by
  by_cases hn : 3 ≤ n
  · rw [obstruction_eval]
    apply mul_ne_zero (by norm_num)
    exact SmallLevelExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 576
      (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 3 n hn
      (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  · interval_cases n <;> norm_num [obstruction]

#print axioms obstruction_eval
#print axioms obstruction_nonzero
end SmallLevelTwentyOneChiFiveObstruction
end
end

/-! ## SmallLevelTwentyOneChiFiveNormV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFiveObstruction
open Complex
open scoped ComplexConjugate

def coefficientA (x : ℂ) : ℂ := 3*x^3-4*x^2-3*x-4
def coefficientB (x : ℂ) : ℂ := 4*x^4+3*x^3+4*x^2+3*x
def residual (x y : ℂ) : ℂ := coefficientA x*y+coefficientB x

theorem conjugate_root {u : ℂ} (hu : 2*u^2-3*u+2=0) (hnorm : ‖u‖=1) :
    conj u=3/2-u := by
  have hu0 : u≠0 := by intro h; simp [h] at hu
  apply mul_left_cancel₀ hu0
  rw [Complex.mul_conj',hnorm]
  norm_num
  linear_combination (1/2:ℂ)*hu

/-- Exact reduction modulo the denominator's quadratic polynomial. -/
theorem norm_identity (r t : ℝ) {u : ℂ} (hu : 2*u^2-3*u+2=0) (hnorm : ‖u‖=1) :
    4*(‖coefficientB ((r:ℂ)*u)‖^2-t^2*‖coefficientA ((r:ℂ)*u)‖^2)=obstruction r t := by
  have hc := conjugate_root hu hnorm
  apply Complex.ofReal_injective
  push_cast
  rw [← Complex.mul_conj',← Complex.mul_conj']
  simp only [coefficientA,coefficientB,map_add,map_sub,map_mul,map_pow,map_ofNat,
    Complex.conj_ofReal,hc]
  unfold obstruction
  push_cast
  linear_combination ((-18:ℂ)*(r:ℂ)^2*(t:ℂ)^0*u^0+(-46:ℂ)*(r:ℂ)^2*(t:ℂ)^2*u^0+(-36:ℂ)*(r:ℂ)^3*(t:ℂ)^0*u^0+(144:ℂ)*(r:ℂ)^3*(t:ℂ)^2*u^0+(-73/2:ℂ)*(r:ℂ)^4*(t:ℂ)^0*u^0+(6:ℂ)*(r:ℂ)^4*(t:ℂ)^0*u^1+(-4:ℂ)*(r:ℂ)^4*(t:ℂ)^0*u^2+(55/2:ℂ)*(r:ℂ)^4*(t:ℂ)^2*u^0+(102:ℂ)*(r:ℂ)^4*(t:ℂ)^2*u^1+(-68:ℂ)*(r:ℂ)^4*(t:ℂ)^2*u^2+(-9:ℂ)*(r:ℂ)^5*(t:ℂ)^0*u^0+(108:ℂ)*(r:ℂ)^5*(t:ℂ)^0*u^1+(-72:ℂ)*(r:ℂ)^5*(t:ℂ)^0*u^2+(-36:ℂ)*(r:ℂ)^5*(t:ℂ)^2*u^0+(-54:ℂ)*(r:ℂ)^5*(t:ℂ)^2*u^1+(36:ℂ)*(r:ℂ)^5*(t:ℂ)^2*u^2+(-26:ℂ)*(r:ℂ)^6*(t:ℂ)^0*u^0+(-39:ℂ)*(r:ℂ)^6*(t:ℂ)^0*u^1+(259/2:ℂ)*(r:ℂ)^6*(t:ℂ)^0*u^2+(-138:ℂ)*(r:ℂ)^6*(t:ℂ)^0*u^3+(46:ℂ)*(r:ℂ)^6*(t:ℂ)^0*u^4+(18:ℂ)*(r:ℂ)^6*(t:ℂ)^2*u^0+(27:ℂ)*(r:ℂ)^6*(t:ℂ)^2*u^1+(45/2:ℂ)*(r:ℂ)^6*(t:ℂ)^2*u^2+(-54:ℂ)*(r:ℂ)^6*(t:ℂ)^2*u^3+(18:ℂ)*(r:ℂ)^6*(t:ℂ)^2*u^4+(-36:ℂ)*(r:ℂ)^7*(t:ℂ)^0*u^0+(-54:ℂ)*(r:ℂ)^7*(t:ℂ)^0*u^1+(-45:ℂ)*(r:ℂ)^7*(t:ℂ)^0*u^2+(108:ℂ)*(r:ℂ)^7*(t:ℂ)^0*u^3+(-36:ℂ)*(r:ℂ)^7*(t:ℂ)^0*u^4+(-32:ℂ)*(r:ℂ)^8*(t:ℂ)^0*u^0+(-48:ℂ)*(r:ℂ)^8*(t:ℂ)^0*u^1+(-40:ℂ)*(r:ℂ)^8*(t:ℂ)^0*u^2+(-12:ℂ)*(r:ℂ)^8*(t:ℂ)^0*u^3+(184:ℂ)*(r:ℂ)^8*(t:ℂ)^0*u^4+(-144:ℂ)*(r:ℂ)^8*(t:ℂ)^0*u^5+(32:ℂ)*(r:ℂ)^8*(t:ℂ)^0*u^6)*hu

theorem residual_nonzero (n : ℕ) {u y : ℂ}
    (hu : 2*u^2-3*u+2=0) (hnorm : ‖u‖=1) (hy : ‖y‖=(3:ℝ)^n) :
    residual (((2:ℝ)^n:ℂ)*u) y≠0 := by
  intro h
  have he : coefficientB (((2:ℝ)^n:ℂ)*u)= -(coefficientA (((2:ℝ)^n:ℂ)*u)*y) := by
    unfold residual at h
    linear_combination h
  have hh := congrArg norm he
  rw [norm_neg,norm_mul,hy] at hh
  have hz : 4*(‖coefficientB (((2:ℝ)^n:ℂ)*u)‖^2-
      ((3:ℝ)^n)^2*‖coefficientA (((2:ℝ)^n:ℂ)*u)‖^2)=0 := by rw [hh]; ring
  have hi := norm_identity ((2:ℝ)^n) ((3:ℝ)^n) hu hnorm
  simp only [Complex.ofReal_pow] at hi
  exact obstruction_nonzero n (hi.symm.trans hz)

#print axioms norm_identity
#print axioms residual_nonzero
end SmallLevelTwentyOneChiFiveObstruction
end
end
