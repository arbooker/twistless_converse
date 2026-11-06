module
public import QuantitativeArithmeticExponentEncodingV1
set_option autoImplicit false
set_option maxHeartbeats 0
@[expose] public noncomputable section

namespace QuantitativeArithmeticPackedIntegerSubstitution
open QuantitativeArithmeticIntegerSevenLaurentRows
open QuantitativeArithmeticExponentEncoding

/-! A small-code checker for polynomial certificates. Coefficients and
exponents remain exact integers; the degree bounds establish lossless decoding.
The normalization proof does not assume any ordering of the input terms. -/

abbrev Packed := List (ℤ × ℕ)

def evalPacked (v : ℕ → ℂ) (p : Packed) : ℂ :=
  (p.map fun t => (t.1 : ℂ) * v t.2).sum

@[simp] theorem evalPacked_nil (v : ℕ → ℂ) : evalPacked v [] = 0 := rfl
@[simp] theorem evalPacked_cons (v : ℕ → ℂ) (t : ℤ × ℕ) (p : Packed) :
    evalPacked v (t :: p) = (t.1 : ℂ) * v t.2 + evalPacked v p := rfl
@[simp] theorem evalPacked_append (v : ℕ → ℂ) (p q : Packed) :
    evalPacked v (p ++ q) = evalPacked v p + evalPacked v q := by simp [evalPacked]

def merge : ℕ → Packed → Packed → Packed
  | 0,p,q => p ++ q
  | _+1,[],q => q
  | _+1,p,[] => p
  | n+1,(r,j)::p,(s,k)::q =>
      if j=k then
        if r+s=0 then merge n p q else (r+s,j)::merge n p q
      else if j<k then (r,j)::merge n p ((s,k)::q)
      else (s,k)::merge n ((r,j)::p) q

theorem eval_merge (v : ℕ → ℂ) (n : ℕ) (p q : Packed) :
    evalPacked v (merge n p q) = evalPacked v p + evalPacked v q := by
  induction n generalizing p q with
  | zero => simp [merge]
  | succ n ih =>
      cases p with
      | nil => simp [merge]
      | cons t p =>
          cases q with
          | nil => simp [merge]
          | cons u q =>
              rcases t with ⟨r,j⟩
              rcases u with ⟨s,k⟩
              by_cases hk : j=k
              · subst k
                by_cases hrs : r+s=0
                · have hc : (r:ℂ)+(s:ℂ)=0 := by exact_mod_cast hrs
                  simp [merge,hrs,ih]
                  linear_combination -(v j)*hc
                · simp [merge,hrs,ih,Int.cast_add]; ring
              · by_cases hlt : j<k
                · simp [merge,hk,hlt,ih]; ring
                · simp [merge,hk,hlt,ih]; ring

def pairs : List Packed → List Packed
  | p::q::ps => merge (p.length+q.length+1) p q :: pairs ps
  | ps => ps

def reduce : ℕ → List Packed → Packed
  | 0,ps => ps.flatten
  | _+1,[] => []
  | _+1,[p] => p
  | n+1,p::q::ps => reduce n (pairs (p::q::ps))

theorem eval_flatten (v : ℕ → ℂ) (ps : List Packed) :
    evalPacked v ps.flatten = (ps.map (evalPacked v)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.flatten_cons,evalPacked_append,List.map_cons,List.sum_cons,ih]

theorem eval_pairs (v : ℕ → ℂ) : ∀ ps : List Packed,
    ((pairs ps).map (evalPacked v)).sum = (ps.map (evalPacked v)).sum
  | [] => rfl
  | [p] => rfl
  | p::q::ps => by
      simp only [pairs,List.map_cons,List.sum_cons,eval_merge,eval_pairs v ps,add_assoc]

theorem eval_reduce (v : ℕ → ℂ) (n : ℕ) (ps : List Packed) :
    evalPacked v (reduce n ps) = (ps.map (evalPacked v)).sum := by
  induction n generalizing ps with
  | zero => exact eval_flatten v ps
  | succ n ih =>
      cases ps with
      | nil => rfl
      | cons p ps =>
          cases ps with
          | nil => simp only [reduce,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
          | cons q ps => exact (ih (pairs (p::q::ps))).trans (eval_pairs v (p::q::ps))

def pack (p : Poly) : Packed := p.map fun t => (t.1,encode t.2.2)
def shiftPacked (r : ℤ) (code : ℕ) (p : Packed) : Packed :=
  p.map fun t => (r*t.1,code+t.2)

/-- Use the same structurally recursive merge checker for initial sorting.
This avoids well-founded proof transports in kernel evaluation. -/
def sortPacked (p : Packed) : Packed := reduce p.length (p.map fun t => [t])

theorem eval_sortPacked (v : ℕ → ℂ) (p : Packed) :
    evalPacked v (sortPacked p) = evalPacked v p := by
  rw [sortPacked,eval_reduce]
  induction p with
  | nil => rfl
  | cons t p ih =>
      simp only [List.map_cons,List.sum_cons,evalPacked_cons,evalPacked_nil,add_zero,ih]

theorem eval_shiftPacked (v : ℕ → ℂ) (r : ℤ) (code : ℕ) (p : Packed) :
    evalPacked v (shiftPacked r code p) = (r:ℂ)*evalPacked (fun k => v (code+k)) p := by
  induction p with
  | nil => simp [shiftPacked]
  | cons t p ih =>
      simp only [shiftPacked,List.map_cons,evalPacked_cons,Int.cast_mul] at *
      rw [ih]
      ring

theorem eval_shiftPacked_sort (v : ℕ → ℂ) (r : ℤ) (code : ℕ) (p : Packed) :
    evalPacked v (shiftPacked r code (sortPacked p)) = evalPacked v (shiftPacked r code p) := by
  rw [eval_shiftPacked,eval_sortPacked,eval_shiftPacked]

theorem eval_shift_pack (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (r : ℤ) (e : Exponent) (p : Poly) (he : Small e)
    (hp : ∀ t ∈ p, Small t.2.2) :
    evalPacked (fun code => monomial x y z w a b c (decode code))
      (shiftPacked r (encode e) (pack p)) =
      (r:ℂ)*monomial x y z w a b c e * eval x y z w a b c (fun _ => 1) p := by
  induction p with
  | nil => simp [pack,shiftPacked]
  | cons t p ih =>
      have ht : Small t.2.2 := hp t (by simp)
      have htail : ∀ u ∈ p, Small u.2.2 := fun u hu => hp u (by simp [hu])
      change ((r*t.1:ℤ):ℂ)*monomial x y z w a b c (decode (encode e+encode t.2.2)) +
        evalPacked (fun code => monomial x y z w a b c (decode code))
          (shiftPacked r (encode e) (pack p)) =
        (r:ℂ)*monomial x y z w a b c e *
          ((t.1:ℂ)*monomial x y z w a b c t.2.2*1+eval x y z w a b c (fun _ => 1) p)
      rw [ih htail,decode_add e t.2.2 he ht,monomial_add x y z w a b c hx hy hz hw]
      push_cast
      ring

def substitutePacked (inputs : ℕ → Poly) (op : Poly) : Packed :=
  reduce op.length (op.map fun t => shiftPacked t.1 (encode t.2.2) (sortPacked (pack (inputs t.2.1))))

theorem eval_substitutePacked (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (inputs : ℕ → Poly) (op : Poly)
    (h : ∀ t ∈ op, Small t.2.2 ∧ ∀ u ∈ inputs t.2.1, Small u.2.2) :
    evalPacked (fun code => monomial x y z w a b c (decode code)) (substitutePacked inputs op) =
      eval x y z w a b c (fun i => eval x y z w a b c (fun _ => 1) (inputs i)) op := by
  rw [substitutePacked,eval_reduce]
  induction op with
  | nil => rfl
  | cons t op ih =>
      have ht := h t (by simp)
      have htail : ∀ u ∈ op, Small u.2.2 ∧ ∀ v ∈ inputs u.2.1, Small v.2.2 :=
        fun u hu => h u (by simp [hu])
      simp only [List.map_cons,List.sum_cons,eval_cons,eval_shiftPacked_sort,
        eval_shift_pack x y z w a b c hx hy hz hw t.1 t.2.2 (inputs t.2.1) ht.1 ht.2,ih htail]

theorem substitution_zero (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (inputs : ℕ → Poly) (op : Poly)
    (hb : ∀ t ∈ op, Small t.2.2 ∧ ∀ u ∈ inputs t.2.1, Small u.2.2)
    (hzp : substitutePacked inputs op = []) :
    eval x y z w a b c (fun i => eval x y z w a b c (fun _ => 1) (inputs i)) op = 0 := by
  rw [← eval_substitutePacked x y z w a b c hx hy hz hw inputs op hb,hzp,evalPacked_nil]

#print axioms eval_merge
#print axioms eval_substitutePacked
#print axioms substitution_zero
end QuantitativeArithmeticPackedIntegerSubstitution
