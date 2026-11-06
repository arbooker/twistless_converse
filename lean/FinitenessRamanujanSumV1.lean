module

public import FinitenessOriginalFrickeV1
public import Mathlib.Data.Nat.GCD.Basic

@[expose] public section

set_option autoImplicit false

namespace FinitenessRamanujanSum

open Complex
open scoped ComplexConjugate

def residues (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q)

noncomputable def phase (q n a : ℕ) : ℂ :=
  Complex.exp (((2*Real.pi*n*a/q : ℝ):ℂ)*I)

noncomputable def complexSum (q n : ℕ) : ℂ := ∑ a ∈ residues q, phase q n a

noncomputable def ramanujan (q n : ℕ) : ℝ := (complexSum q n).re

theorem phase_norm (q n a : ℕ) : ‖phase q n a‖=1 := by
  rw [phase, Complex.norm_exp]
  simp only [mul_I_re, ofReal_im, neg_zero, Real.exp_zero]

theorem turn (n : ℕ) : Complex.exp (((2*Real.pi*n : ℝ):ℂ)*I)=1 := by
  have he : (((2*Real.pi*n : ℝ):ℂ)*I)=(n : ℂ)*(2*Real.pi*I) := by push_cast; ring
  rw [he, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

theorem phase_reflected {q : ℕ} (hq : 0 < q) (n a : ℕ) (ha : a ≤ q) :
    phase q n (q-a)=conj (phase q n a) := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have harg : (2*Real.pi*n*(q-a : ℕ)/q : ℝ)=2*Real.pi*n-2*Real.pi*n*a/q := by
    rw [Nat.cast_sub ha]
    field_simp
  unfold phase
  rw [harg, ofReal_sub, sub_mul, Complex.exp_sub, turn, one_div, ← Complex.exp_neg,
    ← Complex.exp_conj]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I]
  ring

theorem residue_bounds {q a : ℕ} (hq : 1 < q) (ha : a ∈ residues q) : 0 < a ∧ a < q := by
  obtain ⟨har,hcop⟩ := Finset.mem_filter.mp ha
  have hlt := Finset.mem_range.mp har
  have ha0 : a ≠ 0 := by
    intro hz
    subst a
    simp only [Nat.coprime_zero_left] at hcop
    omega
  exact ⟨Nat.pos_of_ne_zero ha0,hlt⟩

theorem residue_reflected {q a : ℕ} (hq : 1 < q) (ha : a ∈ residues q) : q-a ∈ residues q := by
  obtain ⟨ha0,hlt⟩ := residue_bounds hq ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by omega),?_⟩
  exact (Nat.coprime_self_sub_left hlt.le).mpr (Finset.mem_filter.mp ha).2

theorem conjugate_sum (q n : ℕ) : conj (complexSum q n)=complexSum q n := by
  by_cases hq : 1 < q
  · unfold complexSum
    rw [map_sum]
    apply Finset.sum_bij (fun a _ => q-a)
    · intro a ha
      exact residue_reflected hq ha
    · intro a ha b hb he
      have ha' := residue_bounds hq ha
      have hb' := residue_bounds hq hb
      omega
    · intro b hb
      refine ⟨q-b,residue_reflected hq hb,?_⟩
      have hb' := residue_bounds hq hb
      omega
    · intro a ha
      exact (phase_reflected (by omega) n a (residue_bounds hq ha).2.le).symm
  · have hq' : q=0 ∨ q=1 := by omega
    rcases hq' with rfl | rfl <;> simp [complexSum,residues,phase]

/-- The finite primitive exponential sum is real, including q=1. -/
theorem ofReal_ramanujan (q n : ℕ) : (ramanujan q n : ℂ)=complexSum q n := by
  have hh := congrArg Complex.im (conjugate_sum q n)
  simp only [conj_im] at hh
  apply Complex.ext
  · rfl
  · simp only [ofReal_im]
    linarith

theorem complexSum_bound (q n : ℕ) : ‖complexSum q n‖ ≤ q := by
  calc
    ‖complexSum q n‖ ≤ ∑ a ∈ residues q, ‖phase q n a‖ := norm_sum_le _ _
    _ = ((residues q).card : ℝ) := by simp only [phase_norm, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ q := by
      exact_mod_cast (Finset.card_filter_le (Finset.range q) (fun a => Nat.Coprime a q)).trans_eq (Finset.card_range q)

theorem abs_bound (q n : ℕ) : |ramanujan q n| ≤ q := by
  have hh := complexSum_bound q n
  rw [← ofReal_ramanujan, Complex.norm_real, Real.norm_eq_abs] at hh
  exact hh

#print axioms ofReal_ramanujan
#print axioms abs_bound

end FinitenessRamanujanSum
