module
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticDilationRecurrence
open Finset

/-- A recurrence with nonzero constant coefficient propagates vanishing
from the positive half-line to the entire real line. -/
theorem zero_of_nonneg {H : ℝ → ℂ} {L : ℝ} (hL : 0<L)
    (d : ℕ) (a : ℕ → ℂ) (ha : a 0≠0)
    (hrec : ∀ t : ℝ, ∑ j ∈ range (d+1), a j*H (t+(j:ℝ)*L)=0)
    (hzero : ∀ t : ℝ, 0≤t → H t=0) : ∀ t, H t=0 := by
  have step (n : ℕ) : ∀ t : ℝ, -(n:ℝ)*L≤t → H t=0 := by
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
      intro t ht
      have hs : (∑ j ∈ range (d+1), a j*H (t+(j:ℝ)*L))=a 0*H t := by
        rw [sum_eq_single 0]
        · simp
        · intro j hj hj0
          have hj1 : (1:ℝ)≤(j:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
          have ht' : -((n:ℝ)+1)*L≤t := by simpa using ht
          have hh : -(n:ℝ)*L≤t+(j:ℝ)*L := by nlinarith
          rw [ih _ hh,mul_zero]
        · simp
      have hh : a 0*H t=0 := hs.symm.trans (hrec t)
      exact (mul_eq_zero.mp hh).resolve_left ha
  intro t
  obtain ⟨n,hn⟩ := exists_nat_gt (-t/L)
  apply step n t
  have hn' := (div_lt_iff₀ hL).mp hn
  linarith

/-- Once transform uniqueness gives a constant on one half-line, no
additional regularity is needed to recover the function everywhere. -/
theorem constant_of_nonneg {H : ℝ → ℂ} {L : ℝ} (hL : 0<L)
    (d : ℕ) (a : ℕ → ℂ) (ha : a 0≠0) (C : ℂ)
    (hrec : ∀ t : ℝ, ∑ j ∈ range (d+1), a j*H (t+(j:ℝ)*L)=0)
    (hconstant : ∀ t : ℝ, 0≤t → H t=C) :
    (∀ t, H t=C) ∧ (∑ j ∈ range (d+1), a j)*C=0 := by
  have hsum : (∑ j ∈ range (d+1), a j*C)=0 := by
    have hr := hrec 0
    have he : (∑ j ∈ range (d+1), a j*H (0+(j:ℝ)*L))=
        ∑ j ∈ range (d+1), a j*C := by
      apply sum_congr rfl
      intro j hj
      rw [hconstant _ (by positivity)]
    exact he.symm.trans hr
  have hz := zero_of_nonneg (H := fun t => H t-C) hL d a ha
    (by
      intro t
      simp only [mul_sub,sum_sub_distrib,hrec t,hsum,sub_self])
    (by intro t ht; exact sub_eq_zero.mpr (hconstant t ht))
  exact ⟨fun t => sub_eq_zero.mp (hz t),by simpa only [sum_mul] using hsum⟩

#print axioms zero_of_nonneg
#print axioms constant_of_nonneg
end QuantitativeArithmeticDilationRecurrence
