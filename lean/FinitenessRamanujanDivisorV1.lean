module

public import FinitenessRamanujanSumV1
public import Mathlib.NumberTheory.Divisors

@[expose] public section

set_option autoImplicit false

namespace FinitenessRamanujanDivisor

open Complex Finset FinitenessRamanujanSum

noncomputable def complete (q n : ℕ) : ℂ := ∑ a ∈ range q, phase q n a

theorem phase_pow (q n a : ℕ) : phase q n a=(phase q n 1)^a := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem phase_one_iff {q : ℕ} (hq : 0<q) (n : ℕ) : phase q n 1=1 ↔ q ∣ n := by
  have he : (((2*Real.pi*n*1/q:ℝ):ℂ)*I)=2*Real.pi*I*n/q := by
    push_cast
    ring
  rw [phase,Nat.cast_one,he]
  exact Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hq.ne'

theorem phase_full {q : ℕ} (hq : 0<q) (n : ℕ) : phase q n q=1 := by
  have hqr : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
  simpa only [phase,mul_div_cancel_right₀ _ hqr] using turn n

theorem complete_eval {q : ℕ} (hq : 0<q) (n : ℕ) :
    complete q n=if q ∣ n then (q:ℂ) else 0 := by
  unfold complete
  rw [show (∑ a ∈ range q, phase q n a)=∑ a ∈ range q, (phase q n 1)^a from
    sum_congr rfl (fun a _ => phase_pow q n a)]
  by_cases hqn : q ∣ n
  · simp [(phase_one_iff hq n).mpr hqn,hqn]
  · rw [ite_eq_right hqn]
    have hne : phase q n 1-1≠0 := sub_ne_zero.mpr (mt (phase_one_iff hq n).mp hqn)
    have H := geom_sum_mul (phase q n 1) q
    rw [← phase_pow,phase_full hq,sub_self] at H
    exact (mul_eq_zero.mp H).resolve_right hne

theorem phase_scaled (d e n a : ℕ) (hd : 0<d) :
    phase (d*e) n (d*a)=phase e n a := by
  have hd' : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  unfold phase
  apply congrArg (fun x : ℝ => Complex.exp ((x:ℂ)*I))
  push_cast
  rw [show 2*Real.pi*n*((d:ℝ)*a)=d*(2*Real.pi*n*a) by ring]
  exact mul_div_mul_left _ _ hd'

theorem fiber_sum (d e n : ℕ) (hd : 0<d) :
    (∑ a ∈ (range (d*e)).filter (fun a => Nat.gcd (d*e) a=d), phase (d*e) n a)=
      complexSum e n := by
  symm
  unfold complexSum residues
  apply sum_bij (fun a _ => d*a)
  · intro a ha
    obtain ⟨ha,hcop⟩ := mem_filter.mp ha
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp ha) hd),?_⟩
    rw [Nat.gcd_mul_left,hcop.symm.gcd_eq_one,Nat.mul_one]
  · intro a _ b _ he
    exact Nat.eq_of_mul_eq_mul_left hd he
  · intro a ha
    obtain ⟨ha,hg⟩ := mem_filter.mp ha
    have hda : d ∣ a := by rw [← hg]; exact Nat.gcd_dvd_right _ _
    obtain ⟨b,rfl⟩ := hda
    refine ⟨b,mem_filter.mpr ⟨mem_range.mpr (Nat.lt_of_mul_lt_mul_left (mem_range.mp ha)),?_⟩,rfl⟩
    rw [Nat.gcd_mul_left] at hg
    have h1 : Nat.gcd e b=1 := by
      apply Nat.eq_of_mul_eq_mul_left hd
      simpa using hg
    exact (show Nat.Coprime e b from h1).symm
  · intro a _
    exact (phase_scaled d e n a hd).symm

/-- Partitioning the full exponential sum by gcd gives the divisor sum
of the literal primitive Ramanujan sums, not just a dimension relation. -/
theorem sum_divisors {q : ℕ} (hq : 0<q) (n : ℕ) :
    (∑ d ∈ q.divisors, complexSum d n)=if q ∣ n then (q:ℂ) else 0 := by
  have H : (∑ d ∈ q.divisors, ∑ a ∈ (range q).filter (fun a => Nat.gcd q a=d),
      phase q n a)=complete q n := by
    apply sum_fiberwise_of_maps_to
    intro a _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left q a,hq.ne'⟩
  rw [← Nat.sum_div_divisors q (fun d => complexSum d n)]
  calc
    (∑ d ∈ q.divisors, complexSum (q/d) n)=
        ∑ d ∈ q.divisors, ∑ a ∈ (range q).filter (fun a => Nat.gcd q a=d), phase q n a := by
      apply sum_congr rfl
      intro d hd
      have hd0 := Nat.pos_of_mem_divisors hd
      have he : d*(q/d)=q := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      have hf := fiber_sum d (q/d) n hd0
      rw [he] at hf
      exact hf.symm
    _ = complete q n := H
    _ = _ := complete_eval hq n

#print axioms complete_eval
#print axioms sum_divisors

end FinitenessRamanujanDivisor
