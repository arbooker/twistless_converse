module

public import FinitenessTwistedEulerProductV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessFiniteOrderClosure

open Complex FinitenessFiniteOrder FinitenessInputBounds

theorem add {F G : ℂ → ℂ} (hF : Bound F) (hG : Bound G) :
    Bound (fun z => F z+G z) := by
  obtain ⟨A,hA,d,hf⟩ := hF
  obtain ⟨B,hB,e,hg⟩ := hG
  refine ⟨A+B+1,by positivity,max d e,fun z => ?_⟩
  have hbase : (1:ℝ)≤1+‖z‖ := by linarith [norm_nonneg z]
  have hd : (1+‖z‖)^d≤(1+‖z‖)^(max d e) := pow_le_pow_right₀ hbase (le_max_left _ _)
  have he : (1+‖z‖)^e≤(1+‖z‖)^(max d e) := pow_le_pow_right₀ hbase (le_max_right _ _)
  have hu : 1≤(1+‖z‖)^(max d e) := one_le_pow₀ hbase
  have hf' : ‖F z‖≤Real.exp ((A+B)*(1+‖z‖)^(max d e)) := by
    apply (hf z).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hB (pow_nonneg (by positivity : 0≤1+‖z‖) (max d e))]
  have hg' : ‖G z‖≤Real.exp ((A+B)*(1+‖z‖)^(max d e)) := by
    apply (hg z).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hA (pow_nonneg (by positivity : 0≤1+‖z‖) (max d e))]
  calc
    ‖F z+G z‖≤2*Real.exp ((A+B)*(1+‖z‖)^(max d e)) := by
      linarith [norm_add_le (F z) (G z)]
    _ ≤ Real.exp 1*Real.exp ((A+B)*(1+‖z‖)^(max d e)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp 1]) (Real.exp_pos _).le
    _ = Real.exp (1+(A+B)*(1+‖z‖)^(max d e)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((A+B+1)*(1+‖z‖)^(max d e)) := Real.exp_le_exp.mpr (by nlinarith)

theorem neg {F : ℂ → ℂ} (hF : Bound F) : Bound (fun z => -F z) := by
  obtain ⟨A,hA,d,hd⟩ := hF
  exact ⟨A,hA,d,fun z => by simpa only [norm_neg] using hd z⟩

theorem sub {F G : ℂ → ℂ} (hF : Bound F) (hG : Bound G) : Bound (fun z => F z-G z) := by
  simpa only [sub_eq_add_neg] using add hF (neg hG)

theorem pow {F : ℂ → ℂ} (hF : Bound F) (n : ℕ) : Bound (fun z => (F z)^n) := by
  induction n with
  | zero => simpa only [pow_zero] using bound_const (1:ℂ)
  | succ n ih => simpa only [pow_succ] using FinitenessFiniteOrder.mul ih hF

theorem prod {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i∈s, Bound (F i)) : Bound (fun z => ∏ i∈s, F i z) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using bound_const (1:ℂ)
  | @insert a s ha ih =>
      have hs := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      simpa only [Finset.prod_insert ha] using
        FinitenessFiniteOrder.mul (hF a (Finset.mem_insert_self _ _)) hs

#print axioms add
#print axioms prod

end FinitenessFiniteOrderClosure
