module

public import QuantitativeEulerEndpointAPKernelsV1
public import QuantitativeHolomorphicDensityTransferV1
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointAP
open Finset Filter MeasureTheory
open scoped Topology

/-- Explicit p-series bound, uniform as the exponent approaches one. -/
theorem shifted_pseries_bound {t : ℝ} (ht : 0<t) :
    (∑' n : ℕ, 1/((n : ℝ)+1)^(1+t))≤1+1/t := by
  have ha : AntitoneOn (fun u : ℝ => u^(-(1+t))) (Set.Ici 1) := by
    intro u hu v hv huv
    exact Real.rpow_le_rpow_of_nonpos (by linarith [show 1≤u from hu]) huv (by linarith)
  have hi : IntegrableOn (fun u : ℝ => u^(-(1+t))) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have h := AntitoneOn.tsum_comp_add_le_integral (f := fun u : ℝ => u^(-(1+t))) 1
    (by simpa only [Nat.cast_one] using ha) (by simpa only [Nat.cast_one] using hi)
    (fun u hu => Real.rpow_nonneg (by
      have hh : (1 : ℝ)<u := by simpa only [Set.mem_Ioi,Nat.cast_one] using hu
      linarith) _)
  simp only [Nat.cast_one] at h
  rw [integral_Ioi_rpow_of_lt (by linarith : -(1+t)< -1) zero_lt_one] at h
  have he : -(1+t)+1= -t := by ring
  simp only [Real.one_rpow,he,neg_div_neg_eq] at h
  have hs : Summable (fun n : ℕ => 1/((n : ℝ)+1)^(1+t)) := by
    apply ((Real.summable_one_div_nat_rpow.mpr (show 1<1+t by linarith)).comp_injective
      (show Function.Injective (fun n : ℕ => n+1) from fun _ _ h => Nat.add_right_cancel h)).congr
    intro n
    simp only [Function.comp_apply,Nat.cast_add,Nat.cast_one]
  have hd := hs.tsum_eq_zero_add
  simp only [Nat.cast_zero,zero_add,Real.one_rpow,div_one] at hd
  have hh : (∑' n : ℕ, 1/((n+1 : ℕ)+1 : ℝ)^(1+t))≤1/t := by
    have hp (n : ℕ) : ((n+1+1 : ℕ) : ℝ)^(-(1+t))=1/((n+1 : ℕ)+1 : ℝ)^(1+t) := by
      rw [Real.rpow_neg (Nat.cast_nonneg _)]
      simp only [one_div,Nat.cast_add,Nat.cast_one]
    simpa only [hp] using h
  rw [hd]
  exact add_le_add le_rfl hh

private def primeLogShift (n : ℕ) : ℝ := if (n+1).Prime then Real.log (n+1 : ℝ) else 0

private theorem primeLogShift_nonneg (n : ℕ) : 0≤primeLogShift n := by
  unfold primeLogShift
  split_ifs
  · exact Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  · exact le_rfl

private theorem primeLogShift_prefix (n : ℕ) :
    (∑ i∈range n, primeLogShift i)=Chebyshev.theta (n : ℝ) := by
  rw [Chebyshev.theta,Nat.floor_natCast,sum_filter]
  apply sum_bij (fun (i : ℕ) _ => i+1)
  · intro i hi
    simp only [mem_Ioc,mem_range] at *
    omega
  · intro i _ j _ hij
    omega
  · intro j hj
    have hj' := mem_Ioc.mp hj
    exact ⟨j-1,mem_range.mpr (by omega),by omega⟩
  · intro i _
    simp only [primeLogShift,Nat.cast_add,Nat.cast_one]

/-- Uniform upper bound for the actual logarithmically weighted prime
Dirichlet sum. Only Chebyshev's inequality and Abel summation are used. -/
theorem prime_log_dirichlet_upper {t : ℝ} (ht : 0<t) :
    (∑' n : ℕ, if n.Prime then Real.log (n : ℝ)/(n : ℝ)^(1+t) else 0)≤
      Real.log 4*(1+1/t) := by
  let w : ℕ → ℝ := fun n => 1/((n : ℝ)+1)^(1+t)
  have hw0 (n : ℕ) : 0≤w n := by dsimp [w]; positivity
  have hw : Antitone w := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by positivity)
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1) (by linarith)
  have hws : Summable w := by
    apply ((Real.summable_one_div_nat_rpow.mpr (show 1<1+t by linarith)).comp_injective
      (show Function.Injective (fun n : ℕ => n+1) from fun _ _ h => Nat.add_right_cancel h)).congr
    intro n
    simp only [w,Function.comp_apply,Nat.cast_add,Nat.cast_one]
  have hfinite (n : ℕ) : (∑ i∈range n, w i*primeLogShift i)≤Real.log 4*(1+1/t) := by
    have hab := QuantitativeHolomorphic.weighted_prefix_comparison
      primeLogShift (fun _ => (1 : ℝ)) w (C := 0) (ε := Real.log 4)
      (by norm_num) hw0 hw n (fun j _ => by
        rw [primeLogShift_prefix]
        simpa only [sum_const,card_range,nsmul_eq_mul,mul_one,add_zero] using
          Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg j))
    simp only [mul_one,zero_mul,add_zero] at hab
    have hsum : (∑ i∈range n, w i)≤1+1/t :=
      (hws.sum_le_tsum (range n) (fun i _ => hw0 i)).trans (shifted_pseries_bound ht)
    exact hab.trans (mul_le_mul_of_nonneg_left hsum (Real.log_nonneg (by norm_num)))
  have hsum := Real.tsum_le_of_sum_range_le
    (fun n => mul_nonneg (hw0 n) (primeLogShift_nonneg n)) hfinite
  have hs : Summable (fun n : ℕ => if n.Prime then Real.log (n : ℝ)/(n : ℝ)^(1+t) else 0) := by
    apply (primeLogDirichlet_summable (0 : ZMod 1) ht).congr
    intro n
    simp only [primeLogDirichlet,show (n : ZMod 1)=0 from Subsingleton.elim _ _,and_true]
  have he : (∑' n : ℕ, if n.Prime then Real.log (n : ℝ)/(n : ℝ)^(1+t) else 0)=
      ∑' n : ℕ, w n*primeLogShift n := by
    rw [hs.tsum_eq_zero_add]
    simp only [Nat.not_prime_zero,ite_false,zero_add]
    apply tsum_congr
    intro n
    simp only [w,primeLogShift,Nat.cast_add,Nat.cast_one]
    split_ifs <;> ring
  rwa [he]

#print axioms shifted_pseries_bound
#print axioms prime_log_dirichlet_upper
end QuantitativeEulerEndpointAP
