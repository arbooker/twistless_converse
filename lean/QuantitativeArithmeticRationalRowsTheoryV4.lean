module

public import Mathlib.Tactic

/-! Consolidated chapter: QuantitativeArithmeticRationalRows. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticRationalRowsV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRationalRows
abbrev Row := List (ℚ×ℕ)
def eval (v : ℕ → ℂ) (p : Row) : ℂ := (p.map fun t => (t.1:ℂ)*v t.2).sum
@[simp] theorem eval_nil (v : ℕ → ℂ) : eval v []=0 := rfl
@[simp] theorem eval_cons (v : ℕ → ℂ) (t : ℚ×ℕ) (p : Row) :
    eval v (t::p)=(t.1:ℂ)*v t.2+eval v p := rfl
@[simp] theorem eval_append (v : ℕ → ℂ) (p q : Row) :
    eval v (p++q)=eval v p+eval v q := by simp [eval]

def mergeFuel : ℕ → Row → Row → Row
  | 0,p,q => p++q
  | _+1,[],q => q
  | _+1,p,[] => p
  | n+1,(a,j)::p,(b,k)::q =>
    if j=k then
      if a+b=0 then mergeFuel n p q
      else (a+b,j)::mergeFuel n p q
    else if j<k then (a,j)::mergeFuel n p ((b,k)::q)
    else (b,k)::mergeFuel n ((a,j)::p) q

theorem eval_mergeFuel (v : ℕ → ℂ) (n : ℕ) (p q : Row) :
    eval v (mergeFuel n p q)=eval v p+eval v q := by
  induction n generalizing p q with
  | zero => simp [mergeFuel]
  | succ n ih =>
    cases p with
    | nil => simp [mergeFuel]
    | cons t p =>
      cases q with
      | nil => simp [mergeFuel]
      | cons u q =>
        rcases t with ⟨r,j⟩
        rcases u with ⟨s,k⟩
        by_cases hj : j=k
        · subst k
          by_cases hrs : r+s=0
          · have hc : (r:ℂ)+(s:ℂ)=0 := by exact_mod_cast hrs
            simp [mergeFuel,hrs,ih]
            linear_combination -(v j)*hc
          · simp [mergeFuel,hrs,ih,Rat.cast_add]; ring
        · by_cases hlt : j<k
          · simp [mergeFuel,hj,hlt,ih]; ring
          · simp [mergeFuel,hj,hlt,ih]; ring

def scale (r : ℚ) (p : Row) : Row := p.map fun t => (r*t.1,t.2)
theorem eval_scale (v : ℕ → ℂ) (r : ℚ) (p : Row) :
    eval v (scale r p)=(r:ℂ)*eval v p := by
  induction p with
  | nil => simp [scale]
  | cons t p ih => simp only [scale,List.map_cons,eval_cons,Rat.cast_mul] at *; rw [ih]; ring

def substitute (inputs : ℕ → Row) : Row → Row
  | [] => []
  | (r,j)::p => mergeFuel 10000 (scale r (inputs j)) (substitute inputs p)

theorem eval_substitute (v : ℕ → ℂ) (inputs : ℕ → Row) (p : Row) :
    eval v (substitute inputs p)=eval (fun i => eval v (inputs i)) p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨r,j⟩
    simp only [substitute,eval_mergeFuel,eval_scale,ih,eval_cons]

theorem certificate_eval (v : ℕ → ℂ) (inputs : ℕ → Row) (p q : Row)
    (h : substitute inputs p=q) : eval (fun i => eval v (inputs i)) p=eval v q := by
  rw [← eval_substitute,h]
#print axioms certificate_eval
end QuantitativeArithmeticRationalRows
end
end

/-! ## QuantitativeArithmeticRationalRowsMatrixV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRationalRows

def coefficient (p : Row) (j : ℕ) : ℚ :=
  (p.map fun t => if t.2=j then t.1 else 0).sum

def extend {n : ℕ} (v : Fin n → ℂ) (j : ℕ) : ℂ :=
  if h : j<n then v ⟨j,h⟩ else 0

theorem single_sum {n : ℕ} (v : Fin n → ℂ) (a : ℚ) (j : ℕ) :
    ∑ i : Fin n, (if j=i.val then (a:ℂ) else 0)*v i=(a:ℂ)*extend v j := by
  by_cases hj : j<n
  · have he (i : Fin n) : j=i.val ↔ i=⟨j,hj⟩ := by
      constructor
      · intro h; apply Fin.ext; exact h.symm
      · intro h; rw [h]
    simp only [he,ite_mul,zero_mul]
    simp [extend,hj]
  · have he (i : Fin n) : j≠i.val := by intro h; exact hj (h.symm ▸ i.isLt)
    simp [he,extend,hj]

/-- Sparse certificate evaluation agrees with the ordinary finite matrix
row action, even if an unused index lies outside the finite coordinate set. -/
theorem eval_extend_eq_sum {n : ℕ} (v : Fin n → ℂ) (p : Row) :
    eval (extend v) p=∑ i : Fin n, (coefficient p i.val:ℂ)*v i := by
  induction p with
  | nil => simp [eval,coefficient]
  | cons t p ih =>
    rcases t with ⟨a,j⟩
    simp only [eval_cons,coefficient,List.map_cons,List.sum_cons,Rat.cast_add,add_mul,
      Finset.sum_add_distrib]
    rw [ih]
    congr 1
    rw [(single_sum v a j).symm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : j=i.val <;> simp [h]
#print axioms eval_extend_eq_sum
end QuantitativeArithmeticRationalRows
end
end

/-! ## QuantitativeArithmeticRationalRowsCongruenceV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRationalRows

theorem eval_congr (v w : ℕ → ℂ) (p : Row)
    (h : ∀ t∈p, v t.2=w t.2) : eval v p=eval w p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [eval_cons,eval_cons,h t (by simp),ih (by intro u hu; exact h u (by simp [hu]))]

theorem eval_bounded_eq_sum {n : ℕ} (v : ℕ → ℂ) (p : Row)
    (h : ∀ t∈p, t.2<n) :
    eval v p=∑ i : Fin n, (coefficient p i.val:ℂ)*v i.val := by
  have he : eval v p=eval (extend (fun i : Fin n => v i.val)) p := by
    apply eval_congr
    intro t ht
    simp [extend,h t ht]
  rw [he,eval_extend_eq_sum]
#print axioms eval_bounded_eq_sum
end QuantitativeArithmeticRationalRows
end
end

/-! ## QuantitativeArithmeticRationalRowsKernelV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticRationalRows

theorem eval_zero (v : ℕ → ℂ) (r : Row) (h : ∀ t ∈ r, v t.2=0) :
    eval v r=0 := by
  induction r with
  | nil => rfl
  | cons t r ih =>
    have ht := h t (List.mem_cons_self)
    have hr := ih (fun u hu => h u (List.mem_cons_of_mem t hu))
    simp only [eval_cons, ht, hr, mul_zero, zero_add]

/-- A rational left-inverse certificate proves the kernel trivial. The
finite-support condition lets the represented row family use a finite domain. -/
theorem kernel_of_certificates {m n : ℕ} (inputs certificates : ℕ → Row)
    (rows : (Fin n → ℂ) → Fin m → ℂ)
    (hinput : ∀ v : ℕ → ℂ, ∀ i : Fin m,
      eval v (inputs i.val)=rows (fun j => v j.val) i)
    (hcert : ∀ i : Fin n, substitute inputs (certificates i.val)=[(1,i.val)])
    (hsupport : ∀ i : Fin n, ∀ t ∈ certificates i.val, t.2<m)
    (w : Fin n → ℂ) (hw : ∀ i, rows w i=0) : w=0 := by
  let v : ℕ → ℂ := fun j => if h : j<n then w ⟨j,h⟩ else 0
  have hv : (fun j : Fin n => v j.val)=w := by
    funext j
    simp only [v, dite_eq_left j.isLt]
  have hz (j : ℕ) (hj : j<m) : eval v (inputs j)=0 := by
    have h := hinput v ⟨j,hj⟩
    rw [hv] at h
    exact h.trans (hw ⟨j,hj⟩)
  funext i
  change w i=0
  calc
    w i = eval v [(1,i.val)] := by simp [v, i.isLt]
    _ = eval (fun j => eval v (inputs j)) (certificates i.val) := by
      rw [← hcert i]
      exact eval_substitute v inputs (certificates i.val)
    _ = 0 := eval_zero _ _ (fun t ht => hz t.2 (hsupport i t ht))

#print axioms kernel_of_certificates
end QuantitativeArithmeticRationalRows
end
end
