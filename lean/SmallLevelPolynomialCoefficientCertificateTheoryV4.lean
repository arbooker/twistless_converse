module

public import Mathlib.Tactic

/-! Consolidated chapter: SmallLevelPolynomialCoefficientCertificate. Original declarations and local scopes are retained. -/

/-! ## SmallLevelPolynomialCoefficientCertificateV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelPolynomialCoefficientCertificate

def evaluate (y : ℂ) : List ℂ→ℂ
  | [] => 0
  | a::p => a+y*evaluate y p

def add : List ℂ→List ℂ→List ℂ
  | [],q => q
  | p,[] => p
  | a::p,b::q => (a+b)::add p q

def scale (a : ℂ) (p : List ℂ) : List ℂ := p.map (a*·)

def multiply : List ℂ→List ℂ→List ℂ
  | [],_ => []
  | a::p,q => add (scale a q) (0::multiply p q)

theorem evaluate_add (y : ℂ) (p q : List ℂ) :
    evaluate y (add p q)=evaluate y p+evaluate y q := by
  induction p generalizing q with
  | nil => simp [add,evaluate]
  | cons a p ih =>
    cases q with
    | nil => simp [add,evaluate]
    | cons b q => simp only [add,evaluate,ih]; ring

theorem evaluate_scale (y a : ℂ) (p : List ℂ) :
    evaluate y (scale a p)=a*evaluate y p := by
  induction p with
  | nil => simp [scale,evaluate]
  | cons b p ih =>
    change a*b+y*evaluate y (scale a p)=a*(b+y*evaluate y p)
    rw [ih]
    ring

theorem evaluate_multiply (y : ℂ) (p q : List ℂ) :
    evaluate y (multiply p q)=evaluate y p*evaluate y q := by
  induction p with
  | nil => simp [multiply,evaluate]
  | cons a p ih =>
    simp only [multiply,evaluate_add,evaluate_scale,evaluate,ih]
    ring

theorem evaluate_zero (y : ℂ) (p : List ℂ) (hp : ∀ a∈p,a=0) :
    evaluate y p=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have ha : a=0 := hp a (by simp)
    have hq : ∀ b∈p,b=0 := fun b hb => hp b (by simp [hb])
    simp only [evaluate,ha,ih hq,mul_zero,add_zero]

theorem zero_of_getElem? (p : List ℂ) (n : ℕ) (hlen : p.length=n)
    (h : ∀ i : Fin n,p[i.val]?=some 0) : ∀ a∈p,a=0 := by
  intro a ha
  obtain ⟨i,hi,he⟩:=List.getElem_of_mem ha
  have hn : i<n := by simpa only [hlen] using hi
  have hz:=h ⟨i,hn⟩
  change p[i]?=some 0 at hz
  rw [List.getElem?_eq_getElem hi,he] at hz
  exact Option.some.inj hz

/-- A large polynomial identity may be checked one coefficient at a time. -/
theorem of_zero_coefficients (y : ℂ) (p0 p1 p2 p3 p4 p5 p6 : List ℂ)
    (h : ∀ a∈add (add (multiply p0 p1) (multiply p2 p3))
      (add (scale (-1) p4) (scale (-1) (multiply p5 p6))),a=0) :
    evaluate y p0*evaluate y p1+evaluate y p2*evaluate y p3=
      evaluate y p4+evaluate y p5*evaluate y p6 := by
  have hz:=evaluate_zero y _ h
  simp only [evaluate_add,evaluate_scale,evaluate_multiply] at hz
  linear_combination hz

#print axioms of_zero_coefficients
end SmallLevelPolynomialCoefficientCertificate
end
end

/-! ## SmallLevelPolynomialCoefficientLengthV1 -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelPolynomialCoefficientCertificate

theorem length_add (p q : List ℂ) : (add p q).length=max p.length q.length := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q =>
      simp only [add,List.length_cons,ih]
      omega

theorem length_scale (a : ℂ) (p : List ℂ) : (scale a p).length=p.length := by
  simp [scale]

/-- The list representation retains trailing zeros, including when the second
factor is empty; this formula records that exact convention. -/
theorem length_multiply (p q : List ℂ) :
    (multiply p q).length=if p.length=0 then 0 else p.length+(q.length-1) := by
  induction p with
  | nil => simp [multiply]
  | cons a p ih =>
    simp only [multiply,length_add,length_scale,List.length_cons,ih]
    split_ifs at * <;> omega

#print axioms length_add
#print axioms length_multiply
end SmallLevelPolynomialCoefficientCertificate
end
end

/-! ## SmallLevelPolynomialHornerListV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelPolynomialCoefficientCertificate
theorem evaluate_positive_16 (x c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 : ℂ) :
    evaluate x [0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16]=((((((((((((((((c16*x+c15)*x+c14)*x+c13)*x+c12)*x+c11)*x+c10)*x+c9)*x+c8)*x+c7)*x+c6)*x+c5)*x+c4)*x+c3)*x+c2)*x+c1)*x) := by
  simp only [evaluate]
  ring
#print axioms evaluate_positive_16
theorem evaluate_positive_17 (x c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 : ℂ) :
    evaluate x [0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17]=(((((((((((((((((c17*x+c16)*x+c15)*x+c14)*x+c13)*x+c12)*x+c11)*x+c10)*x+c9)*x+c8)*x+c7)*x+c6)*x+c5)*x+c4)*x+c3)*x+c2)*x+c1)*x) := by
  simp only [evaluate]
  ring
#print axioms evaluate_positive_17
end SmallLevelPolynomialCoefficientCertificate
end
end

/-! ## SmallLevelPolynomialTransposeCertificateV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelPolynomialCoefficientCertificate

theorem evaluate_ofFn (z : ℂ) (n : ℕ) : ∀ c : Fin n→ℂ,
    evaluate z (List.ofFn c) = ∑ i : Fin n,c i*z^(i:ℕ) := by
  induction n with
  | zero => intro c; simp [evaluate]
  | succ n ih =>
    intro c
    rw [List.ofFn_succ,evaluate,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem evaluate_ofFn_congr (z : ℂ) {n : ℕ} (c d : Fin n→ℂ)
    (h : ∀ i,c i=d i) : evaluate z (List.ofFn c)=evaluate z (List.ofFn d) := by
  rw [show c=d from funext h]

/-- Reordering the two coefficient directions needs only distributivity.
This avoids expanding a large bivariate polynomial in one ring-normalization step. -/
theorem evaluate_transpose (x y : ℂ) {m n : ℕ} (c : Fin m→Fin n→ℂ) :
    evaluate y (List.ofFn (fun i => evaluate x (List.ofFn (c i)))) =
      evaluate x (List.ofFn (fun j => evaluate y (List.ofFn (fun i => c i j)))) := by
  simp_rw [evaluate_ofFn,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms evaluate_ofFn
#print axioms evaluate_ofFn_congr
#print axioms evaluate_transpose
end SmallLevelPolynomialCoefficientCertificate
end
end
