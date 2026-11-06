module

public import QuantitativeArithmeticLaurentProgramComputeV4
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic
public import QuantitativeArithmeticRationalRowsTheoryV4
public import QuantitativeArithmeticVerticalBoundedTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSevenLaurentRows. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSevenLaurentRowsV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows


def exponentAdd (e f : Exponent) : Exponent :=
  (e.1+f.1,e.2.1+f.2.1,e.2.2.1+f.2.2.1,e.2.2.2.1+f.2.2.2.1,
   e.2.2.2.2.1+f.2.2.2.2.1,e.2.2.2.2.2.1+f.2.2.2.2.2.1,e.2.2.2.2.2.2+f.2.2.2.2.2.2)

def monomial (x y z w a b c : ℂ) (e : Exponent) : ℂ :=
  x^e.1*y^e.2.1*z^e.2.2.1*w^e.2.2.2.1*
    a^e.2.2.2.2.1*b^e.2.2.2.2.2.1*c^e.2.2.2.2.2.2

def eval (x y z w a b c : ℂ) (v : ℕ → ℂ) (p : Poly) : ℂ :=
  (p.map fun t => (t.1:ℂ)*monomial x y z w a b c t.2.2*v t.2.1).sum

theorem monomial_add (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (e f : Exponent) :
    monomial x y z w a b c (exponentAdd e f)=
      monomial x y z w a b c e*monomial x y z w a b c f := by
  simp only [monomial,exponentAdd,zpow_add₀ hx,zpow_add₀ hy,zpow_add₀ hz,zpow_add₀ hw,pow_add]
  ring

@[simp] theorem eval_nil (x y z w a b c : ℂ) (v : ℕ → ℂ) : eval x y z w a b c v []=0 := rfl
@[simp] theorem eval_cons (x y z w a b c : ℂ) (v : ℕ → ℂ) (t : Term) (p : Poly) :
    eval x y z w a b c v (t::p)=
      (t.1:ℂ)*monomial x y z w a b c t.2.2*v t.2.1+eval x y z w a b c v p := rfl
@[simp] theorem eval_append (x y z w a b c : ℂ) (v : ℕ → ℂ) (p q : Poly) :
    eval x y z w a b c v (p++q)=eval x y z w a b c v p+eval x y z w a b c v q := by
  simp [eval]

def key (j : ℕ) (e : Exponent) : ℤ :=
  (((((((j:ℤ)*100+e.1)*100+e.2.1)*100+e.2.2.1)*100+e.2.2.2.1)*100+
    e.2.2.2.2.1)*100+e.2.2.2.2.2.1)*100+e.2.2.2.2.2.2

/-- Fuel exhaustion concatenates the remaining terms. Soundness never
requires that terms are sorted, that keys are injective, or that fuel suffices. -/
def mergeFuel : ℕ → Poly → Poly → Poly
  | 0,p,q => p++q
  | _+1,[],q => q
  | _+1,p,[] => p
  | n+1,(a,j,e)::p,(b,k,f)::q =>
      if j=k ∧ e=f then
        if a+b=0 then mergeFuel n p q
        else (a+b,j,e)::mergeFuel n p q
      else if key j e < key k f then (a,j,e)::mergeFuel n p ((b,k,f)::q)
      else (b,k,f)::mergeFuel n ((a,j,e)::p) q

theorem eval_mergeFuel (x y z w a b c : ℂ) (v : ℕ → ℂ) (n : ℕ) (p q : Poly) :
    eval x y z w a b c v (mergeFuel n p q)=
      eval x y z w a b c v p+eval x y z w a b c v q := by
  induction n generalizing p q with
  | zero => simp [mergeFuel]
  | succ n ih =>
    cases p with
    | nil => simp [mergeFuel]
    | cons t p =>
      cases q with
      | nil => simp [mergeFuel]
      | cons u q =>
        rcases t with ⟨r,j,e⟩
        rcases u with ⟨s,k,f⟩
        by_cases hef : j=k ∧ e=f
        · rcases hef with ⟨rfl,rfl⟩
          by_cases hrs : r+s=0
          · have hc : (r:ℂ)+(s:ℂ)=0 := by exact_mod_cast hrs
            simp [mergeFuel,hrs,ih]
            linear_combination -(monomial x y z w a b c e*v j)*hc
          · simp [mergeFuel,hrs,ih,Rat.cast_add]; ring
        · by_cases hlt : key j e < key k f
          · simp [mergeFuel,hef,hlt,ih]; ring
          · simp [mergeFuel,hef,hlt,ih]; ring

def shift (r : ℚ) (e : Exponent) (p : Poly) : Poly :=
  p.map fun t => (r*t.1,t.2.1,exponentAdd e t.2.2)

theorem eval_shift (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (r : ℚ) (e : Exponent) (p : Poly) :
    eval x y z w a b c v (shift r e p)=
      (r:ℂ)*monomial x y z w a b c e*eval x y z w a b c v p := by
  induction p with
  | nil => simp [shift]
  | cons t p ih =>
    simp only [shift,List.map_cons,eval_cons,Rat.cast_mul,monomial_add x y z w a b c hx hy hz hw] at *
    rw [ih]
    ring

/-- Substitute sparse linear forms for the coordinate variables. This is
used both for row-operation certificates and for a kernel-basis check. -/
def substitute (inputs : ℕ → Poly) : Poly → Poly
  | [] => []
  | (r,j,e)::p => mergeFuel 20000 (shift r e (inputs j)) (substitute inputs p)

theorem eval_substitute (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (inputs : ℕ → Poly) (p : Poly) :
    eval x y z w a b c v (substitute inputs p)=
      eval x y z w a b c (fun i => eval x y z w a b c v (inputs i)) p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨r,j,e⟩
    simp only [substitute,eval_mergeFuel,eval_shift x y z w a b c v hx hy hz hw,ih,eval_cons]

theorem substitution_zero (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (inputs : ℕ → Poly) (p : Poly) (h : substitute inputs p=[]) :
    eval x y z w a b c (fun i => eval x y z w a b c v (inputs i)) p=0 := by
  rw [← eval_substitute x y z w a b c v hx hy hz hw, h, eval_nil]

#print axioms eval_mergeFuel
#print axioms eval_substitute
#print axioms substitution_zero
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticLaurentRescaleV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

/-! Parameter rescaling and coordinate substitution for sparse Laurent rows.

These are the two operations needed to reuse a base row at different Taylor
orders. Their correctness is independent of the level, source row, and order.
The rational coefficient computation can subsequently be checked as finite
data, rather than reproving the complex identity for every row and order.
-/

namespace QuantitativeArithmeticSevenLaurentRows

/-- Relabel coordinate variables without altering scalar coefficients. -/
def relabel (f : ℕ → ℕ) (p : Poly) : Poly :=
  p.map fun t => (t.1, f t.2.1, t.2.2)

theorem eval_relabel (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (f : ℕ → ℕ) (p : Poly) :
    eval x y z w a b c v (relabel f p) =
      eval x y z w a b c (fun j => v (f j)) p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [relabel, List.map_cons, eval_cons] at *
    rw [ih]

/-- The scalar acquired by a Laurent monomial when its first four arguments
are divided by rational constants. The last three arguments are unchanged. -/
def dilationDenominator (r s t u : ℚ) (e : Exponent) : ℚ :=
  r ^ e.1 * s ^ e.2.1 * t ^ e.2.2.1 * u ^ e.2.2.2.1

def dilate (r s t u : ℚ) (p : Poly) : Poly :=
  p.map fun term =>
    (term.1 / dilationDenominator r s t u term.2.2, term.2.1, term.2.2)

theorem monomial_div (x y z w a b c r s t u : ℂ) (e : Exponent) :
    monomial (x/r) (y/s) (z/t) (w/u) a b c e =
      monomial x y z w a b c e / (r^e.1*s^e.2.1*t^e.2.2.1*u^e.2.2.2.1) := by
  simp only [monomial, div_zpow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The formula remains valid even at zero arguments: no cancellation of
Laurent powers, or additional nonvanishing assumption, is used here. -/
theorem eval_dilate (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (r s t u : ℚ) (p : Poly) :
    eval x y z w a b c v (dilate r s t u p) =
      eval (x/(r:ℂ)) (y/(s:ℂ)) (z/(t:ℂ)) (w/(u:ℂ)) a b c v p := by
  induction p with
  | nil => rfl
  | cons term p ih =>
    simp only [dilate, List.map_cons, eval_cons] at *
    rw [ih, monomial_div]
    simp only [Rat.cast_div, dilationDenominator, Rat.cast_mul, Rat.cast_zpow]
    ring

/-- A Taylor layer simultaneously rescales the four physical prime parameters
and relabels the source coordinates. The same identity works for every layer. -/
theorem eval_dilate_relabel (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (r s t u : ℚ) (f : ℕ → ℕ) (p : Poly) :
    eval x y z w a b c v (dilate r s t u (relabel f p)) =
      eval (x/(r:ℂ)) (y/(s:ℂ)) (z/(t:ℂ)) (w/(u:ℂ)) a b c
        (fun j => v (f j)) p := by
  rw [eval_dilate, eval_relabel]

#print axioms eval_relabel
#print axioms monomial_div
#print axioms eval_dilate
#print axioms eval_dilate_relabel
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentComputeV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
@[expose] public section
namespace QuantitativeArithmeticSevenLaurentRows

/-- A computational implementation of the existing merge. The larger
instance budget constructs equality on the seven-component exponents
without falling back on classical decidability. -/
noncomputable def mergeCompute : ℕ → Poly → Poly → Poly
  | 0,p,q => p++q
  | _+1,[],q => q
  | _+1,p,[] => p
  | n+1,(a,j,e)::p,(b,k,f)::q =>
      if j=k ∧ e=f then
        if a+b=0 then mergeCompute n p q
        else (a+b,j,e)::mergeCompute n p q
      else if key j e < key k f then (a,j,e)::mergeCompute n p ((b,k,f)::q)
      else (b,k,f)::mergeCompute n ((a,j,e)::p) q

theorem mergeCompute_eq (n : ℕ) (p q : Poly) :
    mergeCompute n p q=mergeFuel n p q := by
  induction n generalizing p q with
  | zero => rfl
  | succ n ih =>
    cases p with
    | nil => rfl
    | cons t p =>
      cases q with
      | nil => rfl
      | cons u q =>
        rcases t with ⟨a,j,e⟩
        rcases u with ⟨b,k,f⟩
        simp only [mergeCompute,mergeFuel,ih]

noncomputable def substituteCompute (inputs : ℕ → Poly) : Poly → Poly
  | [] => []
  | (r,j,e)::p => mergeCompute 20000 (shift r e (inputs j)) (substituteCompute inputs p)

theorem substituteCompute_eq (inputs : ℕ → Poly) (p : Poly) :
    substituteCompute inputs p=substitute inputs p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨r,j,e⟩
    simp only [substituteCompute,substitute,mergeCompute_eq,ih]

#print axioms mergeCompute_eq
#print axioms substituteCompute_eq
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticLaurentRowArithmeticV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section

namespace QuantitativeArithmeticSevenLaurentRows

/-- Rational scaling does not introduce or cancel powers of the parameters. -/
def coefficientScale (r : ℚ) (p : Poly) : Poly :=
  p.map fun t => (r*t.1, t.2.1, t.2.2)

theorem eval_coefficientScale (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (r : ℚ) (p : Poly) :
    eval x y z w a b c v (coefficientScale r p) = r * eval x y z w a b c v p := by
  induction p with
  | nil => simp [coefficientScale]
  | cons t p ih =>
    simp only [coefficientScale, List.map_cons, eval_cons, Rat.cast_mul] at *
    rw [ih]
    ring

theorem eval_flatten (x y z w a b c : ℂ) (v : ℕ → ℂ) (ps : List Poly) :
    eval x y z w a b c v ps.flatten =
      (ps.map (eval x y z w a b c v)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatten_cons, eval_append, List.map_cons, List.sum_cons, ih]

/-- Collect a finite row by the existing verified merge, dropping zero terms.
Correctness needs neither injectivity of the sorting key nor a fuel bound.
The finite equality check, rather than an assumed normal-form property,
determines whether this collection suffices for a particular certificate. -/
def collectCoefficients : Poly → Poly
  | [] => []
  | t::p => if t.1=0 then collectCoefficients p
      else mergeCompute 20000 [t] (collectCoefficients p)

theorem eval_collectCoefficients (x y z w a b c : ℂ) (v : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c v (collectCoefficients p) = eval x y z w a b c v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    by_cases ht : t.1=0
    · simp [collectCoefficients, ht, ih]
    · simp only [collectCoefficients, ht, ↓reduceIte, mergeCompute_eq,
        eval_mergeFuel, eval_cons, eval_nil, ih, add_zero]

/-- A decidable equality of collected rational rows proves equality of their
complex evaluations for every parameter and every coordinate vector. -/
theorem eval_eq_of_collectCoefficients_eq (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (p q : Poly) (h : collectCoefficients p = collectCoefficients q) :
    eval x y z w a b c v p = eval x y z w a b c v q := by
  calc
    eval x y z w a b c v p = eval x y z w a b c v (collectCoefficients p) :=
      (eval_collectCoefficients x y z w a b c v p).symm
    _ = eval x y z w a b c v (collectCoefficients q) := congrArg (eval x y z w a b c v) h
    _ = eval x y z w a b c v q := eval_collectCoefficients x y z w a b c v q

#print axioms eval_coefficientScale
#print axioms eval_flatten
#print axioms eval_collectCoefficients
#print axioms eval_eq_of_collectCoefficients_eq
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentRowsMatrixV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticRationalRows (extend)

def coefficient (x y z w a b c : ℂ) (p : Poly) (j : ℕ) : ℂ :=
  (p.map fun t => if t.2.1=j then (t.1:ℂ)*monomial x y z w a b c t.2.2 else 0).sum

@[simp] theorem coefficient_nil (x y z w a b c : ℂ) (j : ℕ) :
    coefficient x y z w a b c [] j=0 := rfl
@[simp] theorem coefficient_cons (x y z w a b c : ℂ) (t : Term) (p : Poly) (j : ℕ) :
    coefficient x y z w a b c (t::p) j=
      (if t.2.1=j then (t.1:ℂ)*monomial x y z w a b c t.2.2 else 0)+
        coefficient x y z w a b c p j := rfl

theorem coefficient_zero (x y z w a b c : ℂ) (p : Poly) (j : ℕ)
    (h : ∀ t∈p, t.2.1≠j) : coefficient x y z w a b c p j=0 := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [coefficient_cons,ite_eq_right (h t (by simp)),ih (by intro u hu; exact h u (by simp [hu])),zero_add]

theorem eval_congr (x y z w a b c : ℂ) (v v' : ℕ → ℂ) (p : Poly)
    (h : ∀ t∈p, v t.2.1=v' t.2.1) : eval x y z w a b c v p=eval x y z w a b c v' p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [eval_cons,eval_cons,h t (by simp),ih (by intro u hu; exact h u (by simp [hu]))]

theorem single_sum {n : ℕ} (v : Fin n → ℂ) (a : ℂ) (j : ℕ) :
    ∑ i : Fin n, (if j=i.val then a else 0)*v i=a*extend v j := by
  by_cases hj : j<n
  · have he (i : Fin n) : j=i.val ↔ i=⟨j,hj⟩ := by
      constructor
      · intro h; apply Fin.ext; exact h.symm
      · intro h; rw [h]
    simp only [he,ite_mul,zero_mul]
    simp [extend,hj]
  · have he (i : Fin n) : j≠i.val := by intro h; exact hj (h.symm ▸ i.isLt)
    simp [he,extend,hj]

theorem eval_extend_eq_sum (x y z w a b c : ℂ) {n : ℕ} (v : Fin n → ℂ) (p : Poly) :
    eval x y z w a b c (extend v) p=
      ∑ i : Fin n, coefficient x y z w a b c p i.val*v i := by
  induction p with
  | nil => simp
  | cons t p ih =>
    simp only [eval_cons,coefficient_cons,add_mul,Finset.sum_add_distrib]
    rw [ih,single_sum]

theorem eval_bounded_eq_sum (x y z w a b c : ℂ) {n : ℕ} (v : ℕ → ℂ) (p : Poly)
    (h : ∀ t∈p, t.2.1<n) :
    eval x y z w a b c v p=∑ i : Fin n, coefficient x y z w a b c p i.val*v i.val := by
  have he : eval x y z w a b c v p=eval x y z w a b c (extend (fun i : Fin n => v i.val)) p := by
    apply eval_congr
    intro t ht
    simp [extend,h t ht]
  rw [he,eval_extend_eq_sum]

#print axioms eval_bounded_eq_sum
#print axioms coefficient_zero
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentRowsProjectionV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

def coordinatePolynomial (p : Poly) (j : ℕ) : Poly :=
  (p.filter fun t => t.2.1=j).map fun t => (t.1,0,t.2.2)

theorem coefficient_project (x y z w a b c : ℂ) (p : Poly) (j : ℕ) :
    coefficient x y z w a b c p j=eval x y z w a b c (fun _ => 1) (coordinatePolynomial p j) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    by_cases ht : t.2.1=j
    · simp [coordinatePolynomial,ht,coefficient_cons,ih,eval_cons]
    · simp [coordinatePolynomial,ht,coefficient_cons,ih]

theorem monomial_meromorphic (x y z w a b c : ℂ → ℂ) (s : ℂ)
    (hx : MeromorphicAt x s) (hy : MeromorphicAt y s) (hz : MeromorphicAt z s)
    (hw : MeromorphicAt w s) (ha : MeromorphicAt a s) (hb : MeromorphicAt b s)
    (hc : MeromorphicAt c s) (e : Exponent) :
    MeromorphicAt (fun t => monomial (x t) (y t) (z t) (w t) (a t) (b t) (c t) e) s :=
  ((((((hx.zpow e.1).mul (hy.zpow e.2.1)).mul (hz.zpow e.2.2.1)).mul
    (hw.zpow e.2.2.2.1)).mul (ha.pow e.2.2.2.2.1)).mul
      (hb.pow e.2.2.2.2.2.1)).mul (hc.pow e.2.2.2.2.2.2)

theorem coefficient_meromorphic (x y z w a b c : ℂ → ℂ) (s : ℂ)
    (hx : MeromorphicAt x s) (hy : MeromorphicAt y s) (hz : MeromorphicAt z s)
    (hw : MeromorphicAt w s) (ha : MeromorphicAt a s) (hb : MeromorphicAt b s)
    (hc : MeromorphicAt c s) (p : Poly) (j : ℕ) :
    MeromorphicAt (fun t => coefficient (x t) (y t) (z t) (w t) (a t) (b t) (c t) p j) s := by
  induction p with
  | nil => simpa only [coefficient_nil] using (MeromorphicAt.const (0:ℂ) s : MeromorphicAt (fun _ : ℂ => (0:ℂ)) s)
  | cons t p ih =>
    simp only [coefficient_cons]
    by_cases ht : t.2.1=j
    · simp only [ht,ite_true]
      exact ((MeromorphicAt.const _ s).mul (monomial_meromorphic x y z w a b c s hx hy hz hw ha hb hc t.2.2)).add ih
    · simp only [ht,ite_false,zero_add]
      exact ih
#print axioms coefficient_project
#print axioms coefficient_meromorphic
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticLaurentVerticalBoundedV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticVerticalBounded

theorem monomial_bounded (x y z w : ℂ → ℂ) (a b c : ℂ)
    (hx : Bounded x) (hy : Bounded y) (hz : Bounded z) (hw : Bounded w)
    (hxi : Bounded (fun s => (x s)⁻¹)) (hyi : Bounded (fun s => (y s)⁻¹))
    (hzi : Bounded (fun s => (z s)⁻¹)) (hwi : Bounded (fun s => (w s)⁻¹)) (e : Exponent) :
    Bounded (fun s => monomial (x s) (y s) (z s) (w s) a b c e) :=
  ((((((hx.zpow hxi e.1).mul (hy.zpow hyi e.2.1)).mul (hz.zpow hzi e.2.2.1)).mul
    (hw.zpow hwi e.2.2.2.1)).mul (Bounded.const (a^e.2.2.2.2.1))).mul
      (Bounded.const (b^e.2.2.2.2.2.1))).mul (Bounded.const (c^e.2.2.2.2.2.2))

theorem coefficient_bounded (x y z w : ℂ → ℂ) (a b c : ℂ)
    (hx : Bounded x) (hy : Bounded y) (hz : Bounded z) (hw : Bounded w)
    (hxi : Bounded (fun s => (x s)⁻¹)) (hyi : Bounded (fun s => (y s)⁻¹))
    (hzi : Bounded (fun s => (z s)⁻¹)) (hwi : Bounded (fun s => (w s)⁻¹)) (p : Poly) (j : ℕ) :
    Bounded (fun s => coefficient (x s) (y s) (z s) (w s) a b c p j) := by
  induction p with
  | nil => simpa only [coefficient_nil] using Bounded.const 0
  | cons t p ih =>
    simp only [coefficient_cons]
    by_cases ht : t.2.1=j
    · simp only [ht,ite_true]
      exact ((Bounded.const (t.1:ℂ)).mul
        (monomial_bounded x y z w a b c hx hy hz hw hxi hyi hzi hwi t.2.2)).add ih
    · simpa only [ht,ite_false,zero_add] using ih
#print axioms coefficient_bounded
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentAnalyticV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

theorem eval_sub (x y z w a b c : ℂ) (v u : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c (fun j => v j-u j) p=
      eval x y z w a b c v p-eval x y z w a b c u p := by
  induction p with
  | nil => simp
  | cons t p ih => simp only [eval_cons,ih]; ring

theorem eval_add (x y z w a b c : ℂ) (v u : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c (fun j => v j+u j) p=
      eval x y z w a b c v p+eval x y z w a b c u p := by
  induction p with
  | nil => simp
  | cons t p ih => simp only [eval_cons,ih]; ring

theorem eval_smul (x y z w a b c d : ℂ) (v : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c (fun j => d*v j) p=d*eval x y z w a b c v p := by
  induction p with
  | nil => simp
  | cons t p ih => simp only [eval_cons,ih]; ring

theorem monomial_analytic (X Y Z W : ℂ → ℂ) (a b c s : ℂ) (e : Exponent)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (hw : W s≠0) :
    AnalyticAt ℂ (fun t => monomial (X t) (Y t) (Z t) (W t) a b c e) s := by
  unfold monomial
  exact ((((((hX.zpow hx).mul (hY.zpow hy)).mul (hZ.zpow hz)).mul
    (hW.zpow hw)).mul analyticAt_const).mul analyticAt_const).mul analyticAt_const

theorem eval_analytic (X Y Z W : ℂ → ℂ) (a b c s : ℂ)
    (v : ℂ → ℕ → ℂ) (p : Poly)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (hw : W s≠0)
    (hv : ∀ i, AnalyticAt ℂ (fun t => v t i) s) :
    AnalyticAt ℂ (fun t => eval (X t) (Y t) (Z t) (W t) a b c (v t) p) s := by
  induction p with
  | nil => exact analyticAt_const
  | cons t p ih =>
    simp only [eval_cons]
    exact ((analyticAt_const.mul
      (monomial_analytic X Y Z W a b c s t.2.2 hX hY hZ hW hx hy hz hw)).mul (hv t.2.1)).add ih

/-- A checked source-free basis can be removed directly as sparse linear
forms, avoiding expansion of a large dense matrix. -/
theorem gauge_source (x y z w a b c : ℂ) (v u : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (basis : ℕ → Poly) (p : Poly) (h : substitute basis p=[]) :
    eval x y z w a b c (fun j => v j-eval x y z w a b c u (basis j)) p=
      eval x y z w a b c v p := by
  rw [eval_sub,substitution_zero x y z w a b c u hx hy hz hw basis p h,sub_zero]

#print axioms eval_analytic
#print axioms gauge_source
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentMinusOneV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows
/-- Substitute the relation a*x=-1 in a Laurent row. -/
def minusOneTerm (t : Term) : Term :=
  let e := t.2.2
  (t.1*(-1)^e.2.2.2.2.1,t.2.1,
   (e.1-(e.2.2.2.2.1:ℤ),e.2.1,e.2.2.1,e.2.2.2.1,0,e.2.2.2.2.2.1,e.2.2.2.2.2.2))
def minusOne (p : Poly) : Poly := p.map minusOneTerm

theorem eval_minusOne (x y z w a b c : ℂ) (v : ℕ → ℂ) (hx : x≠0) (p : Poly) :
    eval x y z w a b c v (minusOne p)=eval x y z w (-x⁻¹) b c v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨r,j,e⟩
    simp only [minusOne,List.map_cons,eval_cons] at ih ⊢
    rw [ih]
    congr 1
    dsimp only [minusOneTerm]
    push_cast
    have hn : -x⁻¹=(-1:ℂ)*x⁻¹ := by ring
    simp only [monomial,hn,mul_pow,zpow_sub₀ hx,zpow_natCast,pow_zero,mul_one,inv_pow]
    ring

theorem eval_minusOne_of_relation (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (ha : a*x= -1) (p : Poly) :
    eval x y z w a b c v (minusOne p)=eval x y z w a b c v p := by
  have he : a= -x⁻¹ := by
    apply (mul_right_cancel₀ hx)
    simpa [hx] using ha
  rw [eval_minusOne x y z w a b c v hx p,← he]
#print axioms eval_minusOne_of_relation
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentMinusOneNormalizeV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows
noncomputable def normalizeLaurent (p : Poly) : Poly :=
  p.foldr (fun t q => mergeCompute 20000 [t] q) []
theorem eval_normalizeLaurent (x y z w a b c : ℂ) (v : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c v (normalizeLaurent p)=eval x y z w a b c v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    change eval x y z w a b c v (mergeCompute 20000 [t] (normalizeLaurent p))=_
    rw [mergeCompute_eq,eval_mergeFuel,ih]
    simp only [eval_cons,eval_nil,add_zero]
noncomputable def normalizedMinusOne (p : Poly) : Poly := normalizeLaurent (minusOne p)
theorem eval_normalizedMinusOne (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (ha : a*x= -1) (p : Poly) :
    eval x y z w a b c v (normalizedMinusOne p)=eval x y z w a b c v p := by
  rw [normalizedMinusOne,eval_normalizeLaurent,eval_minusOne_of_relation x y z w a b c v hx ha]
#print axioms eval_normalizedMinusOne
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentBalancedNormalizeV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows
/-- Divide-and-conquer normalization. Fuel exhaustion preserves evaluation;
no completeness assumption about the sorting step is used in soundness. -/
def normalizeBalancedFuel : ℕ → Poly → Poly
  | 0,p => p
  | n+1,p => if p.length≤1 then p else
    mergeCompute 20000 (normalizeBalancedFuel n (p.take (p.length/2)))
      (normalizeBalancedFuel n (p.drop (p.length/2)))

theorem eval_normalizeBalancedFuel (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (n : ℕ) (p : Poly) :
    eval x y z w a b c v (normalizeBalancedFuel n p)=eval x y z w a b c v p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    unfold normalizeBalancedFuel
    split
    · rfl
    · rw [mergeCompute_eq,eval_mergeFuel,ih,ih,← eval_append,List.take_append_drop]

def balancedMinusOne (p : Poly) : Poly := normalizeBalancedFuel 20 (minusOne p)
theorem eval_balancedMinusOne (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (ha : a*x= -1) (p : Poly) :
    eval x y z w a b c v (balancedMinusOne p)=eval x y z w a b c v p := by
  rw [balancedMinusOne,eval_normalizeBalancedFuel,eval_minusOne_of_relation x y z w a b c v hx ha]
#print axioms eval_balancedMinusOne
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentFiniteSumV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

theorem eval_congr_support (x y z w a b c : ℂ) (v u : ℕ → ℂ) (p : Poly)
    (h : ∀ t∈p, v t.2.1=u t.2.1) :
    eval x y z w a b c v p=eval x y z w a b c u p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [eval_cons,eval_cons,h t (by simp),ih (fun t ht => h t (by simp [ht]))]

theorem eval_eq_sum_fin (x y z w a b c : ℂ) (v : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c v p=
      ∑ i : Fin p.length, ((p.get i).1:ℂ)*monomial x y z w a b c (p.get i).2.2*v (p.get i).2.1 := by
  rw [← List.sum_ofFn]
  unfold eval
  exact congrArg List.sum (List.ofFn_getElem_eq_map p
    (fun t : Term => (t.1:ℂ)*monomial x y z w a b c t.2.2*v t.2.1)).symm

#print axioms eval_congr_support
#print axioms eval_eq_sum_fin
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentFiniteCoordinatesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

/-- Expansion of a sparse linear form on any finite coordinate grid. -/
theorem eval_finite_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (index : ℕ → ι) (x y z w a b c : ℂ) (v : ι → ℂ) (p : Poly) :
    eval x y z w a b c (fun j => v (index j)) p=
      ∑ i, eval x y z w a b c (fun j => (Pi.single i (1:ℂ) : ι → ℂ) (index j)) p*v i := by
  induction p with
  | nil => simp
  | cons t p ih =>
    simp only [eval_cons,add_mul,Finset.sum_add_distrib,← ih]
    congr 1
    simp [Pi.single_apply,mul_ite,ite_mul]

#print axioms eval_finite_coordinates
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentKernelV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

theorem eval_zero_of_support (x y z w a b c : ℂ) (v : ℕ → ℂ) (p : Poly)
    (h : ∀ t ∈ p, v t.2.1=0) : eval x y z w a b c v p=0 := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [eval_cons,h t (by simp),mul_zero,zero_add]
    exact ih (fun u hu => h u (by simp [hu]))

theorem eval_of_substitution (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (inputs : ℕ → Poly) (operations target : Poly)
    (hcert : substitute inputs operations=target)
    (hzero : ∀ t ∈ operations, eval x y z w a b c v (inputs t.2.1)=0) :
    eval x y z w a b c v target=0 := by
  rw [← hcert,eval_substitute x y z w a b c v hx hy hz hw]
  exact eval_zero_of_support x y z w a b c _ operations hzero

/-- Replay an acyclic sequence of Laurent row operations. The computable
certificates include the bound ensuring that no row uses its own conclusion. -/
theorem forward_elimination (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (m n : ℕ) (source reduced operations : ℕ → Poly)
    (hcert : ∀ i<n, substitute (fun j => if j<m then source j else reduced (j-m))
      (operations i)=reduced i)
    (hprior : ∀ i<n, ∀ t ∈ operations i, t.2.1<m+i)
    (hsource : ∀ j<m, eval x y z w a b c v (source j)=0) :
    ∀ i<n, eval x y z w a b c v (reduced i)=0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    apply eval_of_substitution x y z w a b c v hx hy hz hw
      (fun j => if j<m then source j else reduced (j-m)) (operations i) (reduced i) (hcert i hi)
    intro t ht
    by_cases hj : t.2.1<m
    · simpa only [ite_true,hj] using hsource t.2.1 hj
    · simp only [hj,ite_false]
      have hlt : t.2.1-m < i := by have := hprior i hi t ht; omega
      exact ih _ hlt (by omega)

/-- Back-substitution for unit triangular sparse rows. It uses only finite
support and a strictly increasing coordinate order, not field computation. -/
theorem triangular_kernel (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (n : ℕ) (coordinate : Fin n → ℕ) (tails : Fin n → Poly)
    (hrows : ∀ i, v (coordinate i)+eval x y z w a b c v (tails i)=0)
    (hhigher : ∀ i, ∀ t ∈ tails i, ∃ j : Fin n, i<j ∧ t.2.1=coordinate j) :
    ∀ i, v (coordinate i)=0 := by
  have hb : ∀ r : ℕ, ∀ i : Fin n, n ≤ i.val+r → v (coordinate i)=0 := by
    intro r
    induction r with
    | zero => intro i hi; omega
    | succ r ih =>
      intro i hi
      have hz : eval x y z w a b c v (tails i)=0 := by
        apply eval_zero_of_support
        intro t ht
        obtain ⟨j,hij,htj⟩ := hhigher i t ht
        rw [htj]
        apply ih j
        have hj : i.val<j.val := hij
        omega
      simpa only [hz,add_zero] using hrows i
  intro i
  exact hb n i (by omega)

#print axioms forward_elimination
#print axioms triangular_kernel
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentPredicateSupportV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

theorem merge_support (P : ℕ → Prop) (n : ℕ) (p q : Poly)
    (hp : ∀ t ∈ p,P t.2.1) (hq : ∀ t ∈ q,P t.2.1) :
    ∀ t ∈ mergeFuel n p q,P t.2.1 := by
  induction n generalizing p q with
  | zero =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hp t ht
    · exact hq t ht
  | succ n ih =>
    cases p with
    | nil => simpa only [mergeFuel] using hq
    | cons t p =>
      cases q with
      | nil => simpa only [mergeFuel] using hp
      | cons u q =>
        rcases t with ⟨r,j,e⟩
        rcases u with ⟨s,k,f⟩
        have hp0 := hp (r,j,e) (by simp)
        have hq0 := hq (s,k,f) (by simp)
        have hpt : ∀ t ∈ p,P t.2.1 := fun t ht => hp t (by simp [ht])
        have hqt : ∀ t ∈ q,P t.2.1 := fun t ht => hq t (by simp [ht])
        unfold mergeFuel
        split
        · split
          · exact ih p q hpt hqt
          · simpa only [List.forall_mem_cons] using And.intro hp0 (ih p q hpt hqt)
        · split
          · simpa only [List.forall_mem_cons] using And.intro hp0 (ih p ((s,k,f)::q) hpt hq)
          · simpa only [List.forall_mem_cons] using And.intro hq0 (ih ((r,j,e)::p) q hp hqt)

theorem shift_support (P : ℕ → Prop) (r : ℚ) (e : Exponent) (p : Poly)
    (hp : ∀ t ∈ p,P t.2.1) : ∀ t ∈ shift r e p,P t.2.1 := by
  intro t ht
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
  exact hp u hu

theorem substitute_support (P : ℕ → Prop) (inputs : ℕ → Poly) (p : Poly)
    (hp : ∀ t ∈ p,∀ u ∈ inputs t.2.1,P u.2.1) :
    ∀ t ∈ substitute inputs p,P t.2.1 := by
  induction p with
  | nil => simp [substitute]
  | cons t p ih =>
    rcases t with ⟨r,j,e⟩
    apply merge_support
    · exact shift_support P r e (inputs j) (hp (r,j,e) (by simp))
    · exact ih (fun t ht => hp t (by simp [ht]))

#print axioms substitute_support
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentRationalEvalV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

def rationalMonomial (x y z w a b c : ℚ) (e : Exponent) : ℚ :=
  x^e.1*y^e.2.1*z^e.2.2.1*w^e.2.2.2.1*
    a^e.2.2.2.2.1*b^e.2.2.2.2.2.1*c^e.2.2.2.2.2.2

def rationalEval (x y z w a b c : ℚ) (v : ℕ→ℚ) (p : Poly) : ℚ :=
  (p.map fun t => t.1*rationalMonomial x y z w a b c t.2.2*v t.2.1).sum

theorem rationalMonomial_cast (x y z w a b c : ℚ) (e : Exponent) :
    (rationalMonomial x y z w a b c e:ℂ)=monomial x y z w a b c e := by
  simp [rationalMonomial,monomial]

theorem rationalEval_cast (x y z w a b c : ℚ) (v : ℕ→ℚ) (p : Poly) :
    (rationalEval x y z w a b c v p:ℂ)=
      eval x y z w a b c (fun j => (v j:ℂ)) p := by
  induction p with
  | nil => simp [rationalEval]
  | cons t p ih =>
    simp only [rationalEval,List.map_cons,List.sum_cons,Rat.cast_add,Rat.cast_mul,
      rationalMonomial_cast,eval_cons] at *
    rw [ih]

#print axioms rationalEval_cast
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentRationalLiftV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

def liftRationalRow (p : QuantitativeArithmeticRationalRows.Row) : Poly :=
  p.map fun t => (t.1,t.2,(0,0,0,0,0,0,0))

theorem coefficient_lift (x y z w a b c : ℂ) (p : QuantitativeArithmeticRationalRows.Row) (j : ℕ) :
    coefficient x y z w a b c (liftRationalRow p) j=
      (QuantitativeArithmeticRationalRows.coefficient p j:ℂ) := by
  induction p with
  | nil => simp [liftRationalRow,QuantitativeArithmeticRationalRows.coefficient]
  | cons t p ih =>
    simp only [liftRationalRow,List.map_cons,coefficient_cons,
      QuantitativeArithmeticRationalRows.coefficient,List.sum_cons,Rat.cast_add] at *
    rw [ih]
    by_cases ht : t.2=j
    · simp [ht,monomial]
    · simp [ht]
#print axioms coefficient_lift
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentRescaleV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

def rescaleThree (u v w : ℚ) (p : Poly) : Poly :=
  p.map fun t => (t.1*u^t.2.2.1*v^t.2.2.2.1*w^t.2.2.2.2.1,t.2.1,t.2.2)

theorem eval_rescaleThree (u v w : ℚ) (x y z η a b c : ℂ) (f : ℕ→ℂ) (p : Poly) :
    eval x y z η a b c f (rescaleThree u v w p)=
      eval ((u:ℂ)*x) ((v:ℂ)*y) ((w:ℂ)*z) η a b c f p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [rescaleThree,List.map_cons,eval_cons,Rat.cast_mul,Rat.cast_zpow,
      monomial,mul_zpow] at ih ⊢
    rw [ih]
    ring

/-- A kernel parameterization can be substituted into any finitely supported
row. Its coordinate support is checked separately by exact arithmetic. -/
theorem eval_substitute_of_coordinates (x y z η a b c : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hη : η≠0)
    (basis : ℕ→Poly) (p : Poly)
    (he : ∀ t∈p,v t.2.1=eval x y z η a b c v (basis t.2.1)) :
    eval x y z η a b c v p=eval x y z η a b c v (substitute basis p) := by
  rw [eval_substitute x y z η a b c v hx hy hz hη]
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [eval_cons,eval_cons,he t (by simp),ih (fun t ht => he t (by simp [ht]))]

#print axioms eval_rescaleThree
#print axioms eval_substitute_of_coordinates
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentRowMatrixV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows
open Matrix
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def rowLinearMap (idx : ℕ→κ) (p : Poly) (x y z w a b c : ℂ) :
    (κ→ℂ)→ₗ[ℂ](Fin 1→ℂ) where
  toFun v := fun _ => eval x y z w a b c (fun j => v (idx j)) p
  map_add' v u := by
    funext i
    exact eval_add x y z w a b c (fun j => v (idx j)) (fun j => u (idx j)) p
  map_smul' d v := by
    funext i
    exact eval_smul x y z w a b c d (fun j => v (idx j)) p

def rowMatrix (idx : ℕ→κ) (p : Poly) (x y z w a b c : ℂ) : Matrix (Fin 1) κ ℂ :=
  (rowLinearMap idx p x y z w a b c).toMatrix'

theorem rowMatrix_mulVec (idx : ℕ→κ) (p : Poly) (x y z w a b c : ℂ) (v : κ→ℂ)
    (i : Fin 1) :
    (rowMatrix idx p x y z w a b c *ᵥv) i=eval x y z w a b c (fun j => v (idx j)) p := by
  rw [rowMatrix,LinearMap.toMatrix'_mulVec]
  rfl

theorem rowMatrix_mul_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ℕ→κ) (p : Poly) (x y z w a b c : ℂ) (A : Matrix κ ι ℂ)
    (h : ∀ v : ι→ℂ,eval x y z w a b c (fun j => (A*ᵥv) (idx j)) p=0) :
    rowMatrix idx p x y z w a b c*A=0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec,Matrix.zero_mulVec]
  funext i
  exact (rowMatrix_mulVec idx p x y z w a b c (A*ᵥv) i).trans (h v)

theorem rowMatrix_analytic (idx : ℕ→κ) (p : Poly)
    (X Y Z W : ℂ→ℂ) (a b c s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (hw : W s≠0)
    (i : Fin 1) (j : κ) :
    AnalyticAt ℂ (fun t => rowMatrix idx p (X t) (Y t) (Z t) (W t) a b c i j) s := by
  simp only [rowMatrix,LinearMap.toMatrix'_apply]
  change AnalyticAt ℂ (fun t => eval (X t) (Y t) (Z t) (W t) a b c
    (fun n => (Pi.single j (1:ℂ) : κ→ℂ) (idx n)) p) s
  exact eval_analytic X Y Z W a b c s (fun (_ : ℂ) (n : ℕ) =>
    (Pi.single j (1:ℂ) : κ→ℂ) (idx n)) p
    hX hY hZ hW hx hy hz hw (fun _ => analyticAt_const)

#print axioms rowMatrix_mul_zero
#print axioms rowMatrix_analytic
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentRowsBlocksV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

theorem spike_block_term (d : ℂ) (v : ℕ → ℂ) (j target lo len : ℕ)
    (hd : target<lo ∨ lo+len≤target)
    (hj : j=target ∨ (lo≤j ∧ j<lo+len)) :
    d*v j=(if j=target then d else 0)*v target+
      ∑ i : Fin len, (if j=lo+i.val then d else 0)*v (lo+i.val) := by
  rcases hj with rfl | ⟨hjlo,hjhi⟩
  · have hne (i : Fin len) : j≠lo+i.val := by omega
    simp [hne]
  · have hne : j≠target := by omega
    rw [ite_eq_right hne,zero_mul,zero_add]
    let idx : Fin len := ⟨j-lo,by omega⟩
    have hidx : lo+idx.val=j := by dsimp [idx]; omega
    rw [Finset.sum_eq_single idx]
    · simp [hidx]
    · intro i _ hi
      have he : j≠lo+i.val := by
        intro hh
        apply hi
        apply Fin.ext
        dsimp [idx]
        omega
      simp [he]
    · simp

/-- A sparse row supported on a block and one separate coordinate. This
keeps the reconstruction certificate triangular without expanding its inverse. -/
theorem eval_spike_block (x y z w a b c : ℂ) (v : ℕ → ℂ) (p : Poly)
    (target lo len : ℕ) (hd : target<lo ∨ lo+len≤target)
    (hp : ∀ t∈p, t.2.1=target ∨ (lo≤t.2.1 ∧ t.2.1<lo+len)) :
    eval x y z w a b c v p=coefficient x y z w a b c p target*v target+
      ∑ i : Fin len, coefficient x y z w a b c p (lo+i.val)*v (lo+i.val) := by
  induction p with
  | nil => simp
  | cons t p ih =>
    rw [eval_cons,ih (by intro u hu; exact hp u (by simp [hu]))]
    simp only [coefficient_cons,add_mul,Finset.sum_add_distrib]
    have hh := spike_block_term ((t.1:ℂ)*monomial x y z w a b c t.2.2)
      v t.2.1 target lo len hd (hp t (by simp))
    linear_combination hh

#print axioms eval_spike_block
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentScalarCramerV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

def scalarEval (x y z w a b c : ℂ) (p : Poly) : ℂ :=
  eval x y z w a b c (fun _ => 1) p

def scalarProduct (p q : Poly) : Poly := substitute (fun _ => q) p

theorem eval_scalarProduct (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (p q : Poly) :
    eval x y z w a b c v (scalarProduct p q)=
      scalarEval x y z w a b c p*eval x y z w a b c v q := by
  rw [scalarProduct,eval_substitute x y z w a b c v hx hy hz hw]
  have h := eval_smul x y z w a b c (eval x y z w a b c v q) (fun _ => 1) p
  simpa only [one_mul,mul_one,scalarEval,mul_comm] using h

def scalarNeg (p : Poly) : Poly := shift (-1) (0,0,0,0,0,0,0) p

def scalarSub (p q : Poly) : Poly := p ++ scalarNeg q

theorem eval_scalarNeg (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (p : Poly) :
    eval x y z w a b c v (scalarNeg p)= -eval x y z w a b c v p := by
  rw [scalarNeg,eval_shift x y z w a b c v hx hy hz hw]
  norm_num [monomial]

theorem eval_scalarSub (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (p q : Poly) :
    eval x y z w a b c v (scalarSub p q)=
      eval x y z w a b c v p-eval x y z w a b c v q := by
  rw [scalarSub,eval_append,eval_scalarNeg x y z w a b c v hx hy hz hw]
  rfl

def coordinatePoly (p : Poly) (j : ℕ) : Poly := p.filter (fun t => t.2.1==j)

theorem eval_three_coordinates (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (p : Poly) (i j k : ℕ) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (hp : ∀ t ∈ p,t.2.1=i ∨ t.2.1=j ∨ t.2.1=k) :
    eval x y z w a b c v p=
      scalarEval x y z w a b c (coordinatePoly p i)*v i+
      scalarEval x y z w a b c (coordinatePoly p j)*v j+
      scalarEval x y z w a b c (coordinatePoly p k)*v k := by
  induction p with
  | nil => simp [coordinatePoly,scalarEval]
  | cons t p ih =>
    have ht := hp t (by simp)
    have hh := ih (fun t ht => hp t (by simp [ht]))
    rcases ht with ht | ht | ht
    all_goals
      simp only [coordinatePoly,List.filter_cons,scalarEval,eval_cons] at *
      simp [ht,hij,hik,hjk,Ne.symm hij,Ne.symm hik,Ne.symm hjk,eval_cons] at *
      linear_combination hh

theorem scalarProduct_support (P : ℕ → Prop) (p q : Poly)
    (hq : ∀ t ∈ q,P t.2.1) : ∀ t ∈ scalarProduct p q,P t.2.1 := by
  exact substitute_support P (fun _ => q) p (fun _ _ => hq)

theorem scalarSub_support (P : ℕ → Prop) (p q : Poly)
    (hp : ∀ t ∈ p,P t.2.1) (hq : ∀ t ∈ q,P t.2.1) :
    ∀ t ∈ scalarSub p q,P t.2.1 := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hp t ht
  · exact shift_support P (-1) (0,0,0,0,0,0,0) q hq t ht

def cramerFour (l00 l01 l02 l10 l20 l21 l22 l30 l31 l32 : ℂ) : Fin 4 → ℂ :=
  ![l10*(l21*l32-l22*l31),
    l00*(l21*l32-l22*l31)-l01*(l20*l32-l22*l30)+l02*(l20*l31-l21*l30),
    l10*(l01*l32-l02*l31),l10*(l21*l02-l22*l01)]

theorem cramerFour_cancels (l00 l01 l02 l10 l20 l21 l22 l30 l31 l32 v0 v1 v2 : ℂ) :
    let C := cramerFour l00 l01 l02 l10 l20 l21 l22 l30 l31 l32
    C 0*(l00*v0+l01*v1+l02*v2)-C 1*(l10*v0)-
    C 2*(l20*v0+l21*v1+l22*v2)-C 3*(l30*v0+l31*v1+l32*v2)=0 := by
  simp only [cramerFour,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  ring
#print axioms eval_three_coordinates
#print axioms cramerFour_cancels
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentScaleRatesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

def scaleRates (q₂ q₃ q₅ q₇ : ℚ) (p : Poly) : Poly :=
  p.map fun (r,j,e) => (r*q₂^e.1*q₃^e.2.1*q₅^e.2.2.1*q₇^e.2.2.2.1,j,e)

theorem eval_scaleRates (q₂ q₃ q₅ q₇ : ℚ) (x y z w a b c : ℂ)
    (v : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c v (scaleRates q₂ q₃ q₅ q₇ p)=
      eval ((q₂:ℂ)*x) ((q₃:ℂ)*y) ((q₅:ℂ)*z) ((q₇:ℂ)*w) a b c v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨r,j,e⟩
    simp only [scaleRates,List.map_cons,eval_cons] at ih ⊢
    rw [ih]
    simp only [monomial,mul_zpow,Rat.cast_mul,Rat.cast_zpow]
    ring

def lowerRates (p : Poly) : Poly := scaleRates (1/2) (1/3) (1/5) (1/7) p

theorem eval_lowerRates (x y z w a b c : ℂ) (v : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c v (lowerRates p)=eval (x/2) (y/3) (z/5) (w/7) a b c v p := by
  rw [lowerRates,eval_scaleRates]
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  congr 1 <;> ring

#print axioms eval_scaleRates
#print axioms eval_lowerRates
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentSpecializeSignsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

def specializeSigns (σ : ℚ) (p : Poly) : Poly :=
  p.map fun t => (t.1*σ^t.2.2.2.2.2.1,t.2.1,
    (t.2.2.1,t.2.2.2.1,t.2.2.2.2.1,0,t.2.2.2.2.2.2.1,0,0))

theorem eval_specializeSigns (x y z a : ℂ) (σ : ℚ) (v : ℕ→ℂ) (p : Poly) :
    eval x y z 1 a 1 1 v (specializeSigns σ p)=eval x y z σ a 1 1 v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨r,j,e⟩
    rcases e with ⟨ex,ey,ez,ew,ea,eb,ec⟩
    simp only [specializeSigns,List.map_cons,eval_cons,monomial,
      Rat.cast_mul,Rat.cast_zpow,one_zpow,one_pow,mul_one] at ih ⊢
    rw [ih]
    ring

#print axioms eval_specializeSigns
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentStagedV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1500000
@[expose] public section
namespace QuantitativeArithmeticSevenLaurentRows

/-- The same right-associated substitution, starting from an already
verified suffix. This permits bounded-memory certificate checking without
changing the polynomial algorithm or assuming associativity of its merge. -/
noncomputable def substituteTail (inputs : ℕ → Poly) : Poly → Poly → Poly
  | [],acc => acc
  | (r,j,e)::p,acc => mergeCompute 20000 (shift r e (inputs j))
      (substituteTail inputs p acc)

theorem substituteCompute_append (inputs : ℕ → Poly) (p q : Poly) :
    substituteCompute inputs (p++q)=substituteTail inputs p (substituteCompute inputs q) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨r,j,e⟩
    simp only [List.cons_append,substituteCompute,substituteTail,ih]

theorem substituteCompute_drop_split (inputs : ℕ → Poly) (p : Poly) (j n : ℕ) :
    substituteCompute inputs (p.drop j)=
      substituteTail inputs ((p.drop j).take n) (substituteCompute inputs (p.drop (j+n))) := by
  calc
    substituteCompute inputs (p.drop j) =
        substituteCompute inputs ((p.drop j).take n ++ (p.drop j).drop n) :=
      congrArg (substituteCompute inputs) (List.take_append_drop n (p.drop j)).symm
    _ = substituteTail inputs ((p.drop j).take n)
        (substituteCompute inputs ((p.drop j).drop n)) := substituteCompute_append _ _ _
    _ = _ := by rw [List.drop_drop]

theorem substituteCompute_stage (inputs : ℕ → Poly) (p : Poly)
    (j n : ℕ) (r next : Poly)
    (hnext : substituteCompute inputs (p.drop (j+n))=next)
    (hstep : substituteTail inputs ((p.drop j).take n) next=r) :
    substituteCompute inputs (p.drop j)=r := by
  rw [substituteCompute_drop_split inputs p j n,hnext]
  exact hstep

#print axioms substituteCompute_append
#print axioms substituteCompute_drop_split
#print axioms substituteCompute_stage
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentSupportV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

def Supported (n : ℕ) (p : Poly) : Prop := ∀ t∈p, t.2.1<n

theorem supported_append {n : ℕ} {p q : Poly}
    (hp : Supported n p) (hq : Supported n q) : Supported n (p++q) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hp t ht
  · exact hq t ht

theorem supported_merge {n : ℕ} (fuel : ℕ) {p q : Poly}
    (hp : Supported n p) (hq : Supported n q) : Supported n (mergeFuel fuel p q) := by
  induction fuel generalizing p q with
  | zero => exact supported_append hp hq
  | succ fuel ih =>
    cases p with
    | nil => exact hq
    | cons t p =>
      cases q with
      | nil => exact hp
      | cons u q =>
        rcases t with ⟨a,j,e⟩
        rcases u with ⟨b,k,f⟩
        have hp' : Supported n p := fun t ht => hp t (List.mem_cons_of_mem _ ht)
        have hq' : Supported n q := fun t ht => hq t (List.mem_cons_of_mem _ ht)
        have hj : j<n := hp (a,j,e) (by simp)
        have hk : k<n := hq (b,k,f) (by simp)
        dsimp only [mergeFuel]
        split
        · split
          · exact ih hp' hq'
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact hj
            · exact ih hp' hq' t ht
        · split
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact hj
            · exact ih hp' hq t ht
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact hk
            · exact ih hp hq' t ht

theorem supported_shift {n : ℕ} {p : Poly} (r : ℚ) (e : Exponent)
    (hp : Supported n p) : Supported n (shift r e p) := by
  intro t ht
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
  exact hp u hu

theorem supported_substitute {n m : ℕ} (inputs : ℕ → Poly) (p : Poly)
    (hp : Supported m p) (hi : ∀ i<m, Supported n (inputs i)) :
    Supported n (substitute inputs p) := by
  induction p with
  | nil => simp [substitute,Supported]
  | cons t p ih =>
    rcases t with ⟨a,j,e⟩
    apply supported_merge
    · exact supported_shift a e (hi j (hp (a,j,e) (by simp)))
    · exact ih (fun t ht => hp t (List.mem_cons_of_mem _ ht))

#print axioms supported_substitute
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentTransportV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

def reindex (index : ℕ → ℕ) (p : Poly) : Poly :=
  p.map fun t => (t.1,index t.2.1,t.2.2)

theorem eval_reindex (index : ℕ → ℕ) (x y z w a b c : ℂ)
    (v : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c v (reindex index p)=
      eval x y z w a b c (fun j => v (index j)) p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [reindex,List.map_cons,eval_cons] at *
    rw [ih]

theorem eval_compact_certificate (inputs compact : ℕ → Poly) (index : ℕ → ℕ)
    (operations result : Poly)
    (hcert : substituteCompute compact operations=result)
    (hmatch : ∀ t ∈ operations,compact t.2.1=inputs (index t.2.1))
    (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c v result=
      eval x y z w a b c (fun j => eval x y z w a b c v (inputs j))
        (reindex index operations) := by
  rw [← hcert,substituteCompute_eq,eval_substitute x y z w a b c v hx hy hz hw,
    eval_reindex]
  apply eval_congr_support
  intro t ht
  rw [hmatch t ht]

#print axioms eval_reindex
#print axioms eval_compact_certificate
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentTwoCoordinatesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

def coefficientAt (x y z a : ℂ) (p : Poly) (i : ℕ) : ℂ :=
  eval x y z 1 a 1 1 (fun j => if j=i then 1 else 0) p

theorem eval_two_coordinates (x y z a : ℂ) (p : Poly) (v : ℕ→ℂ) (i j : ℕ)
    (hij : i≠j) (hp : ∀ t∈p,t.2.1=i ∨ t.2.1=j) :
    eval x y z 1 a 1 1 v p=coefficientAt x y z a p i*v i+coefficientAt x y z a p j*v j := by
  unfold coefficientAt
  induction p with
  | nil => simp
  | cons t p ih =>
    have ht := hp t (by simp)
    have htail : ∀ t∈p,t.2.1=i ∨ t.2.1=j := fun t ht => hp t (by simp [ht])
    rw [eval_cons,eval_cons,eval_cons,ih htail]
    rcases ht with ht|ht
    · simp only [ht,ite_true,ite_eq_right hij]
      ring
    · simp only [ht,ite_true,ite_eq_right (Ne.symm hij)]
      ring

theorem two_coordinate_minor_zero (x y z a : ℂ) (p q : Poly) (v : ℕ→ℂ) (i j : ℕ)
    (hij : i≠j) (hp : ∀ t∈p,t.2.1=i ∨ t.2.1=j)
    (hq : ∀ t∈q,t.2.1=i ∨ t.2.1=j)
    (hn : v i≠0 ∨ v j≠0)
    (hv : eval x y z 1 a 1 1 v p=0) (hw : eval x y z 1 a 1 1 v q=0) :
    coefficientAt x y z a p i*coefficientAt x y z a q j-
      coefficientAt x y z a p j*coefficientAt x y z a q i=0 := by
  rw [eval_two_coordinates x y z a p v i j hij hp] at hv
  rw [eval_two_coordinates x y z a q v i j hij hq] at hw
  rcases hn with hn|hn
  · apply (mul_eq_zero.mp (show (coefficientAt x y z a p i*coefficientAt x y z a q j-
        coefficientAt x y z a p j*coefficientAt x y z a q i)*v i=0 by
      linear_combination coefficientAt x y z a q j*hv-coefficientAt x y z a p j*hw)).resolve_right hn
  · apply (mul_eq_zero.mp (show (coefficientAt x y z a p i*coefficientAt x y z a q j-
        coefficientAt x y z a p j*coefficientAt x y z a q i)*v j=0 by
      linear_combination coefficientAt x y z a p i*hw-coefficientAt x y z a q i*hv)).resolve_right hn

#print axioms two_coordinate_minor_zero
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentZeroAV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

def zeroA (p : Poly) : Poly := p.filter (fun t => decide (t.2.2.2.2.2.2.1=0))

theorem eval_zeroA (x y z w a b c : ℂ) (v : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c v (zeroA p)=eval x y z w 0 b c v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨r,j,e₂,e₃,e₅,e₇,ea,eb,ec⟩
    by_cases h : ea=0
    · subst ea
      simp [zeroA,eval,monomial] at ih ⊢
      exact ih
    · simp [zeroA,eval,monomial,h] at ih ⊢
      exact ih
#print axioms eval_zeroA
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticSevenLaurentZeroTwoV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows
/-- Specialization at a zero second Hecke parameter. -/
def zeroTwo (p : Poly) : Poly := p.filter fun t => t.2.2.2.2.2.2.1=0

theorem eval_zeroTwo (x y z w a b c : ℂ) (v : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c v (zeroTwo p)=eval x y z w 0 b c v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨r,j,e⟩
    by_cases he : e.2.2.2.2.1=0
    · simp [zeroTwo,he,eval_cons,monomial,← ih]
    · simp [zeroTwo,he,eval_cons,monomial,← ih,zero_pow he]
#print axioms eval_zeroTwo
end QuantitativeArithmeticSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticTwoChunkReplayV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows
theorem two_chunk_zero (inputs : ℕ → Poly) (p p₀ p₁ r₀ r₁ : Poly)
    (hs : p=p₀++p₁) (h₀ : substitute inputs p₀=r₀)
    (h₁ : substitute inputs p₁=r₁) (hc : mergeFuel 20000 r₀ r₁=[])
    (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun i => eval x y z w a b c v (inputs i)) p=0 := by
  rw [hs,eval_append,← eval_substitute x y z w a b c v hx hy hz hw,
    ← eval_substitute x y z w a b c v hx hy hz hw,h₀,h₁,
    ← eval_mergeFuel,hc,eval_nil]
#print axioms two_chunk_zero
end QuantitativeArithmeticSevenLaurentRows
end
end
