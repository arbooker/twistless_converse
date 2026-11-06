module

/- Raw cyclic-row identities, valid in every characteristic.
Vectors are represented as periodic functions on Z; these identities in
fact hold on all functions, before any period or legal-window hypotheses.
-/
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace SpanningTraceAlgebra

open Finset
variable {F : Type*} [AddCommMonoid F]

def restrict (m : ℕ) (t : ℤ) (v : ℤ → F) : ℤ → F := fun n => v (m*n+t)

/-- q is the trace length; B is the output period. -/
def trace (q B : ℕ) (v : ℤ → F) : ℤ → F :=
  fun n => ∑ a∈range q, v (n+a*B)

def primitive (q B : ℕ) (v : ℤ → F) (u : ℤ) : F :=
  ∑ a∈(range q).filter (fun a => Nat.Coprime a q), v (u+a*B)

theorem complete_restrict (q B m : ℕ) (t u : ℤ) (v : ℤ → F) :
    trace q B (restrict m t v) u = trace q (m*B) v (m*u+t) := by
  apply sum_congr rfl
  intro a _
  dsimp [restrict]
  congr 1
  ring

theorem primitive_restrict (q B m : ℕ) (t u : ℤ) (v : ℤ → F) :
    primitive q B (restrict m t v) u = primitive q (m*B) v (m*u+t) := by
  apply sum_congr rfl
  intro a _
  dsimp [restrict]
  congr 1
  ring

theorem trace_restrict (q B m : ℕ) (t : ℤ) (v : ℤ → F) :
    trace q B (restrict m t v) = restrict m t (trace q (m*B) v) := by
  funext u
  exact complete_restrict q B m t u v

theorem sum_range_blocks (f : ℕ → F) (p q : ℕ) :
    (∑ i∈range (p*q), f i) = ∑ a∈range p, ∑ b∈range q, f (a*q+b) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Nat.succ_mul,sum_range_add,ih,sum_range_succ]

theorem trace_comp (p q B : ℕ) (v : ℤ → F) :
    trace q B (trace p (q*B) v) = trace (p*q) B v := by
  funext u
  unfold trace
  rw [sum_range_blocks,sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  congr 1
  push_cast
  ring

theorem trace_comm (p q B : ℕ) (v : ℤ → F) :
    trace q B (trace p (q*B) v)=trace p B (trace q (p*B) v) := by
  rw [trace_comp,trace_comp,Nat.mul_comm p q]

omit [AddCommMonoid F] in
theorem restrict_comp (m n : ℕ) (s t : ℤ) (v : ℤ → F) :
    restrict n t (restrict m s v)=restrict (m*n) (m*t+s) v := by
  funext j
  dsimp [restrict]
  congr 1
  ring

theorem zero_of_all_restrictions {m : ℕ} (hm : 0<m) {v : ℤ → F}
    (hv : ∀ t : ℕ, t<m → restrict m t v=0) : v=0 := by
  funext j
  have ht : 0≤j%(m:ℤ) := Int.emod_nonneg _ (by exact_mod_cast (Nat.ne_of_gt hm))
  have ht' : j%(m:ℤ)<m := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  have hh := congrFun (hv (j%(m:ℤ)).toNat (by omega)) (j/(m:ℤ))
  dsimp [restrict] at hh
  have he : (m:ℤ)*(j/(m:ℤ))+(j%(m:ℤ)).toNat=j := by
    rw [Int.toNat_of_nonneg ht]
    exact Int.mul_ediv_add_emod j m
  simpa only [he,Pi.zero_apply] using hh

#print axioms primitive_restrict
#print axioms trace_comp
#print axioms zero_of_all_restrictions

def Cyclic (Q : ℕ) (v : ℤ → F) : Prop := ∀ j, v (j+Q)=v j

omit [AddCommMonoid F] in
theorem restrict_cyclic {m Q : ℕ} {v : ℤ → F} (hv : Cyclic (m*Q) v) (t : ℤ) :
    Cyclic Q (restrict m t v) := by
  intro j
  have he : (m:ℤ)*(j+Q)+t=(m*j+t)+(m*Q:ℕ) := by push_cast; ring
  dsimp [restrict]
  rw [he]
  exact hv (m*j+t)

theorem sum_shift_of_close (g : ℕ → F) (q : ℕ) (hg : g q=g 0) :
    (∑ i∈range q, g (i+1))=∑ i∈range q, g i := by
  cases q with
  | zero => simp
  | succ q =>
    calc
      (∑ i∈range (q+1),g (i+1))=(∑ i∈range q,g (i+1))+g (q+1) := sum_range_succ _ _
      _ = (∑ i∈range q,g (i+1))+g 0 := by rw [hg]
      _ = ∑ i∈range (q+1),g i := by rw [sum_range_succ']

theorem trace_cyclic {q B : ℕ} {v : ℤ → F} (hv : Cyclic (q*B) v) :
    Cyclic B (trace q B v) := by
  intro j
  have hh := sum_shift_of_close (fun a : ℕ => v (j+a*B)) q (by
    simpa using hv j)
  calc
    trace q B v (j+B) = ∑ a∈range q,v (j+(a+1)*B) := by
      apply sum_congr rfl
      intro a _
      congr 1
      ring
    _ = trace q B v j := hh

#print axioms restrict_cyclic
#print axioms trace_cyclic

end SpanningTraceAlgebra
