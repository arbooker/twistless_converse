module
public import Mathlib.Tactic

/-! Rational polynomial certificates checked by kernel reduction. The arithmetic
normalization is represented by data, rather than by an expanded ring proof. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace SmallLevelRationalPolynomialCheck

abbrev Poly := List ℚ

def add : Poly→Poly→Poly
  | [],q => q
  | p,[] => p
  | a::p,b::q => (a+b)::add p q

def scale (a : ℚ) (p : Poly) : Poly := p.map (a*·)

def mul : Poly→Poly→Poly
  | [],_ => []
  | a::p,q => add (scale a q) (0::mul p q)

def pow (p : Poly) : ℕ→Poly
  | 0 => [1]
  | n+1 => mul p (pow p n)

def eval (y : ℂ) : Poly→ℂ
  | [] => 0
  | a::p => (a:ℂ)+y*eval y p

theorem eval_add (y : ℂ) (p q : Poly) : eval y (add p q)=eval y p+eval y q := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add,eval]
    | cons b q => simp only [add,eval,Rat.cast_add,ih]; ring

theorem eval_scale (y : ℂ) (a : ℚ) (p : Poly) : eval y (scale a p)=(a:ℂ)*eval y p := by
  induction p with
  | nil => simp [scale,eval]
  | cons b p ih =>
    change ((a*b:ℚ):ℂ)+y*eval y (scale a p)=(a:ℂ)*((b:ℂ)+y*eval y p)
    rw [Rat.cast_mul,ih]
    ring

theorem eval_mul (y : ℂ) (p q : Poly) : eval y (mul p q)=eval y p*eval y q := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih => simp only [mul,eval_add,eval_scale,eval,Rat.cast_zero,ih]; ring

theorem eval_pow (y : ℂ) (p : Poly) (n : ℕ) : eval y (pow p n)=(eval y p)^n := by
  induction n with
  | zero => simp [pow,eval]
  | succ n ih => simp only [pow,eval_mul,ih,pow_succ]; ring

inductive Expr where
  | constant : ℤ→ℕ→Expr
  | var : Expr
  | natural : ℕ→Expr
  | add : Expr→Expr→Expr
  | mul : Expr→Expr→Expr
  | neg : Expr→Expr
  | pow : Expr→ℕ→Expr

def Expr.value (y : ℂ) : Expr→ℂ
  | .constant n d => (n:ℂ)/(d:ℂ)
  | .var => y
  | .natural n => (n:ℂ)
  | .add a b => a.value y+b.value y
  | .mul a b => a.value y*b.value y
  | .neg a => -a.value y
  | .pow a n => (a.value y)^n

def Expr.coefficients : Expr→Poly
  | .constant n d => [(n:ℚ)/(d:ℚ)]
  | .var => [0,1]
  | .natural n => [(n:ℚ)]
  | .add a b => SmallLevelRationalPolynomialCheck.add a.coefficients b.coefficients
  | .mul a b => SmallLevelRationalPolynomialCheck.mul a.coefficients b.coefficients
  | .neg a => scale (-1) a.coefficients
  | .pow a n => SmallLevelRationalPolynomialCheck.pow a.coefficients n

theorem Expr.eval_coefficients (y : ℂ) (e : Expr) : eval y e.coefficients=e.value y := by
  induction e with
  | constant n d => simp [Expr.coefficients,Expr.value,eval,Rat.cast_div]
  | var => simp [Expr.coefficients,Expr.value,eval]
  | natural n => simp [Expr.coefficients,Expr.value,eval]
  | add a b ha hb => simp only [Expr.coefficients,Expr.value,eval_add,ha,hb]
  | mul a b ha hb => simp only [Expr.coefficients,Expr.value,eval_mul,ha,hb]
  | neg a ha => simp [Expr.coefficients,Expr.value,eval_scale,ha]
  | pow a n ha => simp only [Expr.coefficients,Expr.value,eval_pow,ha]

def checkZero (p : Poly) : Bool := p.all (fun a => decide (a=0))

theorem eval_of_checkZero (y : ℂ) (p : Poly) (h : checkZero p=true) : eval y p=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have h' : a=0 ∧ checkZero p=true := by simpa [checkZero] using h
    simp [eval,h'.1,ih h'.2]

theorem Expr.value_eq_zero (y : ℂ) (e : Expr) (h : checkZero e.coefficients=true) : e.value y=0 := by
  rw [←e.eval_coefficients y]
  exact eval_of_checkZero y e.coefficients h

#print axioms Expr.value_eq_zero
end SmallLevelRationalPolynomialCheck
