module

/- Elementary arithmetic of multiplicatively independent integer bases. -/
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace IndependentBases

/-- Independent positive bases have no equal nontrivial natural powers. -/
def Independent (k l : ℕ) : Prop :=
  ∀ a b : ℕ, k^a = l^b → a=0 ∧ b=0

theorem independent_powers {k l : ℕ} (hi : Independent k l)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : Independent (k^a) (l^b) := by
  intro n m he
  rw [← pow_mul, ← pow_mul] at he
  obtain ⟨hn,hm⟩ := hi _ _ he
  constructor
  · exact (Nat.mul_eq_zero.mp hn).resolve_left (by omega)
  · exact (Nat.mul_eq_zero.mp hm).resolve_left (by omega)

theorem independent_of_coprime {k l : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hcop : Nat.Coprime k l) : Independent k l := by
  intro n m he
  have hc := hcop.pow n m
  rw [← he] at hc
  have h1 : k^n = 1 := by simpa only [Nat.coprime_self] using hc
  have h2 : l^m = 1 := he.symm.trans h1
  exact ⟨Nat.pow_right_injective hk (by simpa using h1),
    Nat.pow_right_injective hl (by simpa using h2)⟩

theorem cross_unique_ordered {k l n m n' m' : ℕ}
    (hk : 2 ≤ k) (hl : 2 ≤ l) (hi : Independent k l)
    (hn : n ≤ n') (he : k^n*l^m' = k^n'*l^m) : n=n' ∧ m=m' := by
  have hkpos : 0 < k^n := pow_pos (by omega) _
  have hlpos : 0 < l^m := pow_pos (by omega) _
  have hm : m ≤ m' := by
    by_contra h
    have hp : l^m' < l^m := Nat.pow_lt_pow_right (by omega) (by omega)
    have hn' : k^n ≤ k^n' := Nat.pow_le_pow_right (by omega) hn
    have hlt : k^n*l^m' < k^n'*l^m :=
      (Nat.mul_lt_mul_of_pos_left hp hkpos).trans_le (Nat.mul_le_mul_right _ hn')
    omega
  have hnp : k^n' = k^n*k^(n'-n) := by
    rw [← pow_add, Nat.add_sub_of_le hn]
  have hmp : l^m' = l^m*l^(m'-m) := by
    rw [← pow_add, Nat.add_sub_of_le hm]
  rw [hnp,hmp] at he
  have he' : (k^n*l^m)*l^(m'-m) = (k^n*l^m)*k^(n'-n) := by
    calc
      (k^n*l^m)*l^(m'-m) = k^n*(l^m*l^(m'-m)) := by ring
      _ = (k^n*k^(n'-n))*l^m := he
      _ = (k^n*l^m)*k^(n'-n) := by ring
  have hp : k^(n'-n) = l^(m'-m) :=
    (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hkpos hlpos) he').symm
  obtain ⟨hn0,hm0⟩ := hi _ _ hp
  omega

theorem cross_unique {k l n m n' m' : ℕ}
    (hk : 2 ≤ k) (hl : 2 ≤ l) (hi : Independent k l)
    (he : k^n*l^m' = k^n'*l^m) : n=n' ∧ m=m' := by
  rcases le_total n n' with h | h
  · exact cross_unique_ordered hk hl hi h he
  · obtain ⟨hn,hm⟩ := cross_unique_ordered hk hl hi h he.symm
    exact ⟨hn.symm,hm.symm⟩

/-- Genuine two-base rigidity for zero additive constant, including
arbitrary rational coefficients of either sign. -/
theorem homogeneous_unique {k l n m n' m' : ℕ} {A B : ℚ}
    (hk : 2 ≤ k) (hl : 2 ≤ l) (hi : Independent k l) (hA : A ≠ 0)
    (h : A*(k:ℚ)^n = B*(l:ℚ)^m)
    (h' : A*(k:ℚ)^n' = B*(l:ℚ)^m') : n=n' ∧ m=m' := by
  have hc : A*((k:ℚ)^n*(l:ℚ)^m') = A*((k:ℚ)^n'*(l:ℚ)^m) := by
    calc
      A*((k:ℚ)^n*(l:ℚ)^m') = (A*(k:ℚ)^n)*(l:ℚ)^m' := by ring
      _ = (B*(l:ℚ)^m)*(l:ℚ)^m' := by rw [h]
      _ = (B*(l:ℚ)^m')*(l:ℚ)^m := by ring
      _ = (A*(k:ℚ)^n')*(l:ℚ)^m := by rw [h']
      _ = A*((k:ℚ)^n'*(l:ℚ)^m) := by ring
  have he := mul_left_cancel₀ hA hc
  have heN : k^n*l^m' = k^n'*l^m := by exact_mod_cast he
  exact cross_unique hk hl hi heN

theorem homogeneous_finite {k l : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hi : Independent k l) (A B : ℚ) (hA : A ≠ 0) :
    {p : ℕ × ℕ | A*(k:ℚ)^p.1 = B*(l:ℚ)^p.2}.Finite := by
  apply Set.Subsingleton.finite
  intro p hp q hq
  obtain ⟨hn,hm⟩ := homogeneous_unique hk hl hi hA hp hq
  exact Prod.ext hn hm

/-- Equal-offset nonconstant affine-geometric families meet at most once. -/
theorem equal_offset_unique {k l n m n' m' : ℕ} {A B C : ℚ}
    (hk : 2 ≤ k) (hl : 2 ≤ l) (hi : Independent k l) (hA : A ≠ 0)
    (h : A*(k:ℚ)^n+C = B*(l:ℚ)^m+C)
    (h' : A*(k:ℚ)^n'+C = B*(l:ℚ)^m'+C) : n=n' ∧ m=m' := by
  exact homogeneous_unique hk hl hi hA (add_right_cancel h) (add_right_cancel h')

/-- Unequal offsets leave precisely the nonzero-constant equation.
This is an algebraic equivalence, NOT a finiteness theorem. -/
theorem unequal_offset_equation {k l n m : ℕ} (A B C D : ℚ) :
    A*(k:ℚ)^n+C = B*(l:ℚ)^m+D ↔
      A*(k:ℚ)^n-B*(l:ℚ)^m = D-C := by
  constructor <;> intro h <;> linarith

#print axioms independent_of_coprime
#print axioms homogeneous_unique
#print axioms homogeneous_finite
#print axioms equal_offset_unique

end IndependentBases
