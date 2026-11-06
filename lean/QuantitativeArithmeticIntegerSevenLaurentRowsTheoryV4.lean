module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Tactic

/-! Consolidated chapter: QuantitativeArithmeticIntegerSevenLaurentRows. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticIntegerSevenLaurentRowsV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticIntegerSevenLaurentRows

abbrev Exponent := ℤ × ℤ × ℤ × ℤ × ℕ × ℕ × ℕ
abbrev Term := ℤ × ℕ × Exponent
abbrev Poly := List Term

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
          · simp [mergeFuel,hrs,ih,Int.cast_add]; ring
        · by_cases hlt : key j e < key k f
          · simp [mergeFuel,hef,hlt,ih]; ring
          · simp [mergeFuel,hef,hlt,ih]; ring

def shift (r : ℤ) (e : Exponent) (p : Poly) : Poly :=
  p.map fun t => (r*t.1,t.2.1,exponentAdd e t.2.2)

theorem eval_shift (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (r : ℤ) (e : Exponent) (p : Poly) :
    eval x y z w a b c v (shift r e p)=
      (r:ℂ)*monomial x y z w a b c e*eval x y z w a b c v p := by
  induction p with
  | nil => simp [shift]
  | cons t p ih =>
    simp only [shift,List.map_cons,eval_cons,Int.cast_mul,monomial_add x y z w a b c hx hy hz hw] at *
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
end QuantitativeArithmeticIntegerSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticIntegerLaurentAnalyticV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticIntegerSevenLaurentRows

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

#print axioms eval_analytic
end QuantitativeArithmeticIntegerSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticIntegerLaurentCoordinateV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticIntegerSevenLaurentRows

theorem eval_single_coordinate (x y z w a b c : ℂ) (v : ℕ→ℂ)
    (p : Poly) (j : ℕ) (hp : ∀ t∈p,t.2.1=j) :
    eval x y z w a b c v p=eval x y z w a b c (fun _ => 1) p*v j := by
  induction p with
  | nil => simp
  | cons t p ih =>
    have ht : t.2.1=j := hp t (by simp)
    have htail : ∀ u∈p,u.2.1=j := fun u hu => hp u (by simp [hu])
    rw [eval_cons,eval_cons,ht,ih htail]
    ring

#print axioms eval_single_coordinate
end QuantitativeArithmeticIntegerSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticIntegerLaurentTransposeV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticIntegerSevenLaurentRows

/-- A column of a sparse row, with its output coordinate replaced by the
index of that row. No sorting or distinctness condition is needed. -/
def columnPiece (i j : ℕ) : Poly → Poly
  | [] => []
  | (c,k,e)::p => if k=j then (c,i,e)::columnPiece i j p else columnPiece i j p

def column (rows : ℕ→Poly) : List ℕ → ℕ → Poly
  | [],_ => []
  | i::is,j => columnPiece i j (rows i) ++ column rows is j

theorem eval_columnPiece (x y z w a b c : ℂ) (u : ℕ→ℂ) (i j : ℕ) (p : Poly) :
    eval x y z w a b c u (columnPiece i j p)=
      u i*eval x y z w a b c (fun k => if k=j then 1 else 0) p := by
  induction p with
  | nil => simp [columnPiece]
  | cons t p ih =>
    rcases t with ⟨r,k,e⟩
    by_cases hk : k=j
    · simp only [columnPiece,hk,ite_true,eval_cons,ih]
      ring
    · simp only [columnPiece,hk,ite_false,eval_cons,ih,mul_zero,zero_add]

theorem eval_partition (x y z w a b c : ℂ) (v : ℕ→ℂ) (js : Finset ℕ)
    (p : Poly) (hp : ∀ t∈p,t.2.1∈js) :
    eval x y z w a b c v p=
      ∑ j∈js, eval x y z w a b c (fun k => if k=j then 1 else 0) p*v j := by
  classical
  induction p with
  | nil => simp
  | cons t p ih =>
    have ht : t.2.1∈js := hp t (by simp)
    have htail : ∀ u∈p,u.2.1∈js := fun u hu => hp u (by simp [hu])
    simp only [eval_cons,add_mul,Finset.sum_add_distrib]
    rw [ih htail]
    congr 1
    simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
    simp [ht]

/-- Exact row-column interchange. This lets a large row certificate be
checked in small output-coordinate blocks without changing its meaning. -/
theorem row_column_identity (x y z w a b c : ℂ) (u v : ℕ→ℂ)
    (rows : ℕ→Poly) (is : List ℕ) (js : Finset ℕ)
    (hcover : ∀ i∈is,∀ t∈rows i,t.2.1∈js) :
    (is.map fun i => u i*eval x y z w a b c v (rows i)).sum=
      ∑ j∈js, eval x y z w a b c u (column rows is j)*v j := by
  classical
  induction is with
  | nil => simp [column]
  | cons i is ih =>
    have hi : ∀ t∈rows i,t.2.1∈js := hcover i (by simp)
    have his : ∀ r∈is,∀ t∈rows r,t.2.1∈js := fun r hr => hcover r (by simp [hr])
    simp only [List.map_cons,List.sum_cons,column,eval_append,add_mul,Finset.sum_add_distrib]
    rw [ih his,eval_partition x y z w a b c v js (rows i) hi]
    simp_rw [eval_columnPiece]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring

theorem row_combination_zero (x y z w a b c : ℂ) (u v : ℕ→ℂ)
    (rows : ℕ→Poly) (is : List ℕ) (js : Finset ℕ)
    (hcover : ∀ i∈is,∀ t∈rows i,t.2.1∈js)
    (hzero : ∀ j∈js,eval x y z w a b c u (column rows is j)=0) :
    (is.map fun i => u i*eval x y z w a b c v (rows i)).sum=0 := by
  rw [row_column_identity x y z w a b c u v rows is js hcover]
  apply Finset.sum_eq_zero
  intro j hj
  rw [hzero j hj,zero_mul]

#print axioms row_column_identity
#print axioms row_combination_zero
end QuantitativeArithmeticIntegerSevenLaurentRows
end
end

/-! ## QuantitativeArithmeticIntegerSevenLaurentBalancedV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticIntegerSevenLaurentRows

/-- Balanced evaluation avoids repeatedly copying a growing polynomial.
Fuel exhaustion uses the already proved ordinary substitution. -/
def substituteBalanced : ℕ → (ℕ→Poly) → Poly → Poly
  | 0,inputs,p => substitute inputs p
  | n+1,inputs,p =>
      if p.length≤1 then substitute inputs p else
        mergeFuel 20000 (substituteBalanced n inputs (p.take (p.length/2)))
          (substituteBalanced n inputs (p.drop (p.length/2)))

theorem eval_substituteBalanced (x y z w a b c : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (n : ℕ) (inputs : ℕ→Poly) (p : Poly) :
    eval x y z w a b c v (substituteBalanced n inputs p)=
      eval x y z w a b c (fun i => eval x y z w a b c v (inputs i)) p := by
  induction n generalizing p with
  | zero => exact eval_substitute x y z w a b c v hx hy hz hw inputs p
  | succ n ih =>
    simp only [substituteBalanced]
    split
    · exact eval_substitute x y z w a b c v hx hy hz hw inputs p
    · rw [eval_mergeFuel,ih,ih,← eval_append,List.take_append_drop]

#print axioms eval_substituteBalanced
end QuantitativeArithmeticIntegerSevenLaurentRows
end
end
