module
public import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace SmallLevelSparseIntegerPolynomialCheck

abbrev Monomial := List ℕ
abbrev Poly := List (Monomial × ℤ)

def monomialValue (v : ℕ→ℂ) (m : Monomial) : ℂ := (m.map v).prod

def keyInsert (n : ℕ) : Monomial→Monomial
  | [] => [n]
  | m::s => if n≤m then n::m::s else m::keyInsert n s

def keySort : Monomial→Monomial
  | [] => []
  | n::s => keyInsert n (keySort s)

theorem monomialValue_insert (v : ℕ→ℂ) (n : ℕ) (s : Monomial) :
    monomialValue v (keyInsert n s)=v n*monomialValue v s := by
  induction s with
  | nil => simp [keyInsert,monomialValue]
  | cons m s ih =>
    by_cases h : n≤m
    · simp [keyInsert,h,monomialValue]
    · simp only [keyInsert,ite_eq_right h,monomialValue,List.map_cons,List.prod_cons] at *
      rw [ih]; ring

theorem monomialValue_sort (v : ℕ→ℂ) (m : Monomial) :
    monomialValue v (keySort m)=monomialValue v m := by
  induction m with
  | nil => rfl
  | cons n s ih =>
    change monomialValue v (keyInsert n (keySort s))=v n*monomialValue v s
    rw [monomialValue_insert,ih]

def monomialMul (a b : Monomial) : Monomial := keySort (a++b)

theorem monomialValue_mul (v : ℕ→ℂ) (a b : Monomial) :
    monomialValue v (monomialMul a b)=monomialValue v a*monomialValue v b := by
  rw [monomialMul,monomialValue_sort]
  simp [monomialValue,List.map_append,List.prod_append]

def eval (v : ℕ→ℂ) : Poly→ℂ
  | [] => 0
  | (m,c)::p => (c:ℂ)*monomialValue v m+eval v p

def keyLexLE : Monomial→Monomial→Bool
  | [],_ => true
  | _::_,[] => false
  | a::p,b::q => if a=b then keyLexLE p q else decide (a≤b)

def keyLE (p q : Monomial) : Bool :=
  if p.length=q.length then keyLexLE p q else decide (p.length≤q.length)

def addFuel : ℕ→Poly→Poly→Poly
  | 0,p,q => p++q
  | _+1,[],q => q
  | _+1,p,[] => p
  | n+1,(m,c)::p,(k,d)::q =>
    if m=k then
      if c+d=0 then addFuel n p q else (m,c+d)::addFuel n p q
    else if keyLE m k then (m,c)::addFuel n p ((k,d)::q)
    else (k,d)::addFuel n ((m,c)::p) q

def add (p q : Poly) : Poly := addFuel (p.length+q.length) p q

def scale (m : Monomial) (c : ℤ) : Poly→Poly
  | [] => []
  | (n,d)::p => (monomialMul m n,c*d)::scale m c p

def mul : Poly→Poly→Poly
  | [],_ => []
  | (m,c)::p,q => if c=0 then mul p q else add (scale m c q) (mul p q)

def pow (p : Poly) : ℕ→Poly
  | 0 => [([],1)]
  | n+1 => mul p (pow p n)

theorem eval_append (v : ℕ→ℂ) (p q : Poly) : eval v (p++q)=eval v p+eval v q := by
  induction p with
  | nil => simp [eval]
  | cons a p ih => rcases a with ⟨m,c⟩; simp [eval,ih,add_assoc]

theorem eval_addFuel (v : ℕ→ℂ) (n : ℕ) (p q : Poly) :
    eval v (addFuel n p q)=eval v p+eval v q := by
  induction n generalizing p q with
  | zero => exact eval_append v p q
  | succ n ih =>
    cases p with
    | nil => simp [addFuel,eval]
    | cons a p =>
      rcases a with ⟨m,c⟩
      cases q with
      | nil => simp [addFuel,eval]
      | cons b q =>
        rcases b with ⟨k,d⟩
        by_cases h : m=k
        · subst k
          by_cases hz : c+d=0
          · simp only [addFuel,↓reduceIte,hz,ih,eval]
            have hc : (c:ℂ)+(d:ℂ)=0 := by exact_mod_cast hz
            linear_combination -(monomialValue v m)*hc
          · simp only [addFuel,↓reduceIte,hz,ih,eval,Int.cast_add]; ring
        · by_cases ht : keyLE m k=true
          · rw [addFuel,ite_eq_right h,ite_eq_left ht]
            simp only [eval,ih]; ring
          · rw [addFuel,ite_eq_right h,ite_eq_right ht]
            simp only [eval,ih]; ring

theorem eval_add (v : ℕ→ℂ) (p q : Poly) : eval v (add p q)=eval v p+eval v q :=
  eval_addFuel v _ p q

theorem eval_scale (v : ℕ→ℂ) (m : Monomial) (c : ℤ) (p : Poly) :
    eval v (scale m c p)=(c:ℂ)*monomialValue v m*eval v p := by
  induction p with
  | nil => simp [scale,eval]
  | cons a p ih =>
    rcases a with ⟨n,d⟩
    simp only [scale,eval,Int.cast_mul,monomialValue_mul,ih]; ring

theorem eval_mul (v : ℕ→ℂ) (p q : Poly) : eval v (mul p q)=eval v p*eval v q := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih =>
    rcases a with ⟨m,c⟩
    by_cases h : c=0
    · simp [mul,h,eval,ih]
    · simp only [mul,ite_eq_right h,eval_add,eval_scale,eval,ih]; ring

theorem eval_pow (v : ℕ→ℂ) (p : Poly) (n : ℕ) : eval v (pow p n)=(eval v p)^n := by
  induction n with
  | zero => simp [pow,eval,monomialValue]
  | succ n ih => simp only [pow,eval_mul,ih,pow_succ]; ring

inductive Expr where
  | var : ℕ→Expr
  | natural : ℕ→Expr
  | add : Expr→Expr→Expr
  | mul : Expr→Expr→Expr
  | neg : Expr→Expr
  | pow : Expr→ℕ→Expr

def Expr.value (v : ℕ→ℂ) : Expr→ℂ
  | .var i => v i
  | .natural n => (n:ℂ)
  | .add a b => a.value v+b.value v
  | .mul a b => a.value v*b.value v
  | .neg a => -a.value v
  | .pow a n => (a.value v)^n

def Expr.coefficients : Expr→Poly
  | .var i => [([i],1)]
  | .natural n => [([],(n:ℤ))]
  | .add a b => SmallLevelSparseIntegerPolynomialCheck.add a.coefficients b.coefficients
  | .mul a b => SmallLevelSparseIntegerPolynomialCheck.mul a.coefficients b.coefficients
  | .neg a => scale [] (-1) a.coefficients
  | .pow a n => SmallLevelSparseIntegerPolynomialCheck.pow a.coefficients n

theorem Expr.eval_coefficients (v : ℕ→ℂ) (e : Expr) : eval v e.coefficients=e.value v := by
  induction e with
  | var i => simp [Expr.coefficients,Expr.value,eval,monomialValue]
  | natural n => simp [Expr.coefficients,Expr.value,eval,monomialValue]
  | add a b ha hb => simp only [Expr.coefficients,Expr.value,eval_add,ha,hb]
  | mul a b ha hb => simp only [Expr.coefficients,Expr.value,eval_mul,ha,hb]
  | neg a ha => simp [Expr.coefficients,Expr.value,eval_scale,ha,monomialValue]
  | pow a n ha => simp only [Expr.coefficients,Expr.value,eval_pow,ha]

def checkZero (p : Poly) : Bool := p.all (fun a => decide (a.2=0))

theorem eval_of_checkZero (v : ℕ→ℂ) (p : Poly) (h : checkZero p=true) : eval v p=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rcases a with ⟨m,c⟩
    have h' : c=0 ∧ checkZero p=true := by simpa [checkZero] using h
    simp [eval,h'.1,ih h'.2]

theorem Expr.value_eq_zero (v : ℕ→ℂ) (e : Expr) (h : checkZero e.coefficients=true) : e.value v=0 := by
  rw [←e.eval_coefficients v]
  exact eval_of_checkZero v e.coefficients h

#print axioms Expr.value_eq_zero
end SmallLevelSparseIntegerPolynomialCheck
