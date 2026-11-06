module

public import Mathlib.Tactic
public import Mathlib.Tactic.Eval

/-! Consolidated chapter: QuantitativeArithmeticSparsePolynomialCertificate. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSparsePolynomialCertificateTheoryV4 -/
section
/-! Consolidated chapter: QuantitativeArithmeticSparsePolynomialCertificate. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSparsePolynomialCertificateV1 -/
section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSparsePolynomialCertificate
abbrev Exponent := ℕ × ℕ × ℕ × ℕ × ℕ
abbrev Term := ℤ × Exponent
abbrev Poly := List Term

def exponentAdd (e f : Exponent) : Exponent :=
  (e.1+f.1,e.2.1+f.2.1,e.2.2.1+f.2.2.1,e.2.2.2.1+f.2.2.2.1,e.2.2.2.2+f.2.2.2.2)
def monomial (B A Z Y X : ℂ) (e : Exponent) : ℂ :=
  B^e.1*A^e.2.1*Z^e.2.2.1*Y^e.2.2.2.1*X^e.2.2.2.2
def eval (B A Z Y X : ℂ) (p : Poly) : ℂ :=
  (p.map fun t => (t.1:ℂ)*monomial B A Z Y X t.2).sum

theorem monomial_add (B A Z Y X : ℂ) (e f : Exponent) :
    monomial B A Z Y X (exponentAdd e f) = monomial B A Z Y X e * monomial B A Z Y X f := by
  simp only [monomial,exponentAdd,pow_add]
  ring
@[simp] theorem eval_nil (B A Z Y X : ℂ) : eval B A Z Y X []=0 := rfl
@[simp] theorem eval_cons (B A Z Y X : ℂ) (t : Term) (p : Poly) :
    eval B A Z Y X (t::p)=(t.1:ℂ)*monomial B A Z Y X t.2+eval B A Z Y X p := rfl
@[simp] theorem eval_append (B A Z Y X : ℂ) (p q : Poly) :
    eval B A Z Y X (p++q)=eval B A Z Y X p+eval B A Z Y X q := by
  simp [eval]

def exponentKey (e : Exponent) : ℕ :=
  (((e.1*16+e.2.1)*16+e.2.2.1)*16+e.2.2.2.1)*16+e.2.2.2.2

/-- A sparse merge. Fuel exhaustion retains both lists, so soundness does
not depend on ordering, fuel adequacy, or a trusted normalization procedure. -/
def mergeFuel : ℕ → Poly → Poly → Poly
  | 0,p,q => p++q
  | _+1,[],q => q
  | _+1,p,[] => p
  | n+1,(a,e)::p,(b,f)::q =>
      if e=f then
        if a+b=0 then mergeFuel n p q
        else (a+b,e)::mergeFuel n p q
      else if exponentKey e < exponentKey f then (a,e)::mergeFuel n p ((b,f)::q)
      else (b,f)::mergeFuel n ((a,e)::p) q

def merge (p q : Poly) : Poly := mergeFuel (p.length+q.length) p q

theorem eval_mergeFuel (B A Z Y X : ℂ) (n : ℕ) (p q : Poly) :
    eval B A Z Y X (mergeFuel n p q)=eval B A Z Y X p+eval B A Z Y X q := by
  induction n generalizing p q with
  | zero => simp [mergeFuel]
  | succ n ih =>
    cases p with
    | nil => simp [mergeFuel]
    | cons t p =>
      cases q with
      | nil => simp [mergeFuel]
      | cons u q =>
        rcases t with ⟨a,e⟩
        rcases u with ⟨b,f⟩
        by_cases hef : e=f
        · subst f
          by_cases hab : a+b=0
          · have hc : (a:ℂ)+(b:ℂ)=0 := by exact_mod_cast hab
            simp [mergeFuel,hab,ih]
            linear_combination -(monomial B A Z Y X e)*hc
          · simp [mergeFuel,hab,ih,Int.cast_add] <;> ring
        · by_cases hlt : exponentKey e < exponentKey f
          · simp [mergeFuel,hef,hlt,ih] <;> ring
          · simp [mergeFuel,hef,hlt,ih] <;> ring

theorem eval_merge (B A Z Y X : ℂ) (p q : Poly) :
    eval B A Z Y X (merge p q)=eval B A Z Y X p+eval B A Z Y X q :=
  eval_mergeFuel B A Z Y X _ p q

def shift (c : ℤ) (e : Exponent) (p : Poly) : Poly :=
  p.map fun t => (c*t.1,exponentAdd e t.2)
theorem eval_shift (B A Z Y X : ℂ) (c : ℤ) (e : Exponent) (p : Poly) :
    eval B A Z Y X (shift c e p)=(c:ℂ)*monomial B A Z Y X e*eval B A Z Y X p := by
  induction p with
  | nil => simp [shift]
  | cons t p ih =>
    simp only [shift,List.map_cons,eval_cons,Int.cast_mul,monomial_add] at *
    rw [ih]
    ring

inductive Certificate where
  | leaf : ℕ → ℤ → Exponent → Certificate
  | add : Certificate → Certificate → Certificate

def combine (inputs : ℕ→Poly) : Certificate → Poly
  | .leaf i c e => shift c e (inputs i)
  | .add t u => merge (combine inputs t) (combine inputs u)

theorem eval_combine_zero (B A Z Y X : ℂ) (inputs : ℕ→Poly)
    (h : ∀ i, eval B A Z Y X (inputs i)=0) (t : Certificate) :
    eval B A Z Y X (combine inputs t)=0 := by
  induction t with
  | leaf i c e => simp [combine,eval_shift,h]
  | add t u ht hu => simp [combine,eval_merge,ht,hu]

theorem of_certificate (B A Z Y X : ℂ) (inputs : ℕ→Poly)
    (h : ∀ i, eval B A Z Y X (inputs i)=0) (t : Certificate) (target : Poly)
    (certificate : combine inputs t=target) : eval B A Z Y X target=0 := by
  rw [← certificate]
  exact eval_combine_zero B A Z Y X inputs h t

#print axioms eval_mergeFuel
#print axioms eval_shift
#print axioms of_certificate
end QuantitativeArithmeticSparsePolynomialCertificate
end
end

/-! ## QuantitativeArithmeticSparsePolynomialBoundedCertificateV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSparsePolynomialCertificate
/-- A fixed work bound avoids traversing each intermediate polynomial merely
for its length. Fuel exhaustion still preserves the polynomial exactly. -/
def combineBounded (inputs : ℕ→Poly) : Certificate → Poly
  | .leaf i c e => shift c e (inputs i)
  | .add t u => mergeFuel 5000 (combineBounded inputs t) (combineBounded inputs u)
theorem eval_combineBounded_zero (B A Z Y X : ℂ) (inputs : ℕ→Poly)
    (h : ∀ i, eval B A Z Y X (inputs i)=0) (t : Certificate) :
    eval B A Z Y X (combineBounded inputs t)=0 := by
  induction t with
  | leaf i c e => simp [combineBounded,eval_shift,h]
  | add t u ht hu => simp [combineBounded,eval_mergeFuel,ht,hu]
theorem of_bounded_certificate (B A Z Y X : ℂ) (inputs : ℕ→Poly)
    (h : ∀ i, eval B A Z Y X (inputs i)=0) (t : Certificate) (target : Poly)
    (certificate : combineBounded inputs t=target) : eval B A Z Y X target=0 := by
  rw [← certificate]
  exact eval_combineBounded_zero B A Z Y X inputs h t
#print axioms of_bounded_certificate
end QuantitativeArithmeticSparsePolynomialCertificate
end
end

/-! ## QuantitativeArithmeticSparsePolynomialComputeV1 -/
section
@[expose] public section
namespace QuantitativeArithmeticSparsePolynomialCertificate
/-- Executable data producer. Its output is never accepted as a proof:
all uses below are subsequently checked by kernel reduction. -/
def computeExponentAdd (e f : Exponent) : Exponent :=
  (e.1+f.1,e.2.1+f.2.1,e.2.2.1+f.2.2.1,e.2.2.2.1+f.2.2.2.1,e.2.2.2.2+f.2.2.2.2)
def computeKey (e : Exponent) : ℕ :=
  (((e.1*16+e.2.1)*16+e.2.2.1)*16+e.2.2.2.1)*16+e.2.2.2.2
def computeMerge : ℕ → Poly → Poly → Poly
  | 0,p,q => p++q
  | _+1,[],q => q
  | _+1,p,[] => p
  | n+1,(a,e)::p,(b,f)::q =>
      if e=f then
        if a+b=0 then computeMerge n p q
        else (a+b,e)::computeMerge n p q
      else if computeKey e < computeKey f then (a,e)::computeMerge n p ((b,f)::q)
      else (b,f)::computeMerge n ((a,e)::p) q
def computeShift (c : ℤ) (e : Exponent) (p : Poly) : Poly :=
  p.map fun t => (c*t.1,computeExponentAdd e t.2)
def computeCombine (inputs : ℕ→Poly) : Certificate → Poly
  | .leaf i c e => computeShift c e (inputs i)
  | .add t u => computeMerge 5000 (computeCombine inputs t) (computeCombine inputs u)
def descend : List Bool → Certificate → Certificate
  | [],t => t
  | false::p,.add t _ => descend p t
  | true::p,.add _ t => descend p t
  | _::p,t => descend p t
end QuantitativeArithmeticSparsePolynomialCertificate
end
end
end

/-! ## QuantitativeArithmeticSparsePolynomialProductV4 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSparsePolynomialCertificate

/-- Multiply sparse polynomials by merging shifted copies. Correctness does not
require sorted inputs: sorting affects only the resulting normal form. -/
def product (p : Poly) : Poly → Poly
  | [] => []
  | (c,e)::q => merge (shift c e p) (product p q)

theorem eval_product (B A Z Y X : ℂ) (p q : Poly) :
    eval B A Z Y X (product p q) = eval B A Z Y X p * eval B A Z Y X q := by
  induction q with
  | nil => simp [product]
  | cons t q ih =>
    rcases t with ⟨c,e⟩
    simp only [product, eval_merge, eval_shift, eval_cons, ih]
    ring

/-- A coefficient-list equality checked by the kernel lifts to an identity
at arbitrary complex arguments, without expanding a symbolic ring proof. -/
theorem eval_of_eq (B A Z Y X : ℂ) (p q : Poly) (h : p = q) :
    eval B A Z Y X p = eval B A Z Y X q := congrArg (eval B A Z Y X) h

#print axioms eval_product
#print axioms eval_of_eq
end QuantitativeArithmeticSparsePolynomialCertificate
end
end
