module

public import QuantitativeHolomorphicDensityTransferV1
public import QuantitativeEulerEndpointSieveDenominatorV1
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSieve
open Finset

private def primeLog (i : ℕ) : ℝ :=
  if (i+1).Prime then Real.log (i+1 : ℝ) else 0

private theorem primeLog_nonneg (i : ℕ) : 0≤primeLog i := by
  unfold primeLog
  split_ifs
  · exact Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
  · exact le_rfl

private theorem primeLog_prefix (n : ℕ) :
    (∑ i ∈ range n, primeLog i)=Chebyshev.theta (n : ℝ) := by
  rw [Chebyshev.theta,Nat.floor_natCast,sum_filter]
  apply sum_bij (fun (i : ℕ) _ => i+1)
  · intro i hi
    simp only [mem_Ioc,mem_range] at *
    omega
  · intro i _ j _ hij
    omega
  · intro j hj
    have hj' := mem_Ioc.mp hj
    refine ⟨j-1,mem_range.mpr (by omega),by omega⟩
  · intro i _
    simp only [primeLog,Nat.cast_add,Nat.cast_one]

/-- Uniform logarithmic first moment of the actual primes, obtained from
Chebyshev's proved upper bound by finite Abel summation. -/
theorem prime_log_reciprocal_bound (S : Finset ℕ) (n : ℕ)
    (hp : ∀ p∈S, p.Prime) (hn : ∀ p∈S, p≤n) :
    (∑ p ∈ S, Real.log (p : ℝ)/(p : ℝ))≤Real.log 4*(1+Real.log (n : ℝ)) := by
  let w : ℕ → ℝ := fun i => 1/((i : ℝ)+1)
  have hw0 (i : ℕ) : 0≤w i := by dsimp [w]; positivity
  have hw : Antitone w := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    have hc : (i : ℝ)≤(j : ℝ) := by exact_mod_cast hij
    linarith
  have hab := QuantitativeHolomorphic.weighted_prefix_comparison
    primeLog (fun _ => (1 : ℝ)) w (C := 0) (ε := Real.log 4)
    (by norm_num) hw0 hw n (fun j _ => by
      rw [primeLog_prefix]
      simpa only [sum_const,card_range,nsmul_eq_mul,mul_one,add_zero] using
        Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg j))
  have hharm : (∑ i ∈ range n, w i)=(harmonic n : ℝ) := by
    simp [harmonic,w,one_div]
  simp only [mul_one,zero_mul,add_zero,hharm] at hab
  have hsub : (∑ p ∈ S, Real.log (p : ℝ)/(p : ℝ))≤∑ i ∈ range n, w i*primeLog i := by
    apply sum_le_sum_of_injOn (fun p : ℕ => p-1)
    · intro p hps q hqs he
      change p-1=q-1 at he
      have := (hp p hps).one_lt
      have := (hp q hqs).one_lt
      omega
    · intro i hi
      obtain ⟨p,hps,rfl⟩ := mem_image.mp hi
      exact mem_range.mpr (by have := (hp p hps).one_lt; have := hn p hps; omega)
    · intro p hps
      have he : p-1+1=p := Nat.sub_add_cancel (hp p hps).one_lt.le
      have her : ((p-1 : ℕ) : ℝ)+1=(p : ℝ) := by exact_mod_cast he
      simp only [w,primeLog,he,hp p hps,ite_true,her]
      exact le_of_eq (by ring)
    · intro i _ _
      exact mul_nonneg (hw0 i) (primeLog_nonneg i)
  apply hsub.trans (hab.trans ?_)
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n)
    (Real.log_nonneg (by norm_num : (1 : ℝ)≤4))

/-- Actual local densities at most 2/p have an explicit logarithmic first
moment. This discharges the former abstract moment input in the finite
Selberg-denominator estimate. -/
theorem denominator_ge_half_product_of_cutoff (s : BoundingSieve) (z y : ℕ)
    (hz : 1<z) (S : Finset ℕ) (hS : S⊆s.prodPrimes.primeFactors)
    (hy : ∀ p∈S, p≤y) (hν : ∀ p∈S, s.nu p≤2/(p : ℝ))
    (hcut : 4*Real.log 4*(1+Real.log (y : ℝ))≤Real.log (z : ℝ)) :
    (∏ p ∈ S, (1+s.selbergTerms p))/2≤denominator s z := by
  apply denominator_ge_half_product s z hz S hS
  have hp (p : ℕ) (h : p∈S) := Nat.prime_of_mem_primeFactors (hS h)
  have hmoment : (∑ p ∈ S, s.nu p*Real.log p)≤
      2*(∑ p ∈ S, Real.log (p : ℝ)/(p : ℝ)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hps
    have hl : 0≤Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (hp p hps).one_lt.le)
    have h := mul_le_mul_of_nonneg_right (hν p hps) hl
    convert h using 1
    ring
  have hprime := prime_log_reciprocal_bound S y hp hy
  linarith

/-- A fixed polynomial relation between the two cutoffs suffices. There is
no assumed prime moment or unspecified choice of a small exponent. -/
theorem denominator_ge_half_product_of_pow (s : BoundingSieve) (z y : ℕ)
    (hy4 : 4≤y) (hyz : y^24≤z) (S : Finset ℕ)
    (hS : S⊆s.prodPrimes.primeFactors) (hy : ∀ p∈S, p≤y)
    (hν : ∀ p∈S, s.nu p≤2/(p : ℝ)) :
    (∏ p ∈ S, (1+s.selbergTerms p))/2≤denominator s z := by
  have hyR : (4 : ℝ)≤y := by exact_mod_cast hy4
  have hypos : (0 : ℝ)<y := by linarith
  have hyl : 1≤Real.log (y : ℝ) :=
    (Real.le_log_iff_exp_le hypos).mpr (Real.exp_one_lt_three.le.trans (by linarith))
  have h4l : Real.log 4≤3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<4)
    norm_num at h ⊢
    exact h
  have hy1 : 1<y := by omega
  have hypow : 1<y^24 := one_lt_pow₀ hy1 (by norm_num)
  have hz : 1<z := lt_of_lt_of_le hypow hyz
  apply denominator_ge_half_product_of_cutoff s z y hz S hS hy hν
  have hlog : 24*Real.log (y : ℝ)≤Real.log (z : ℝ) := by
    have hp : (y : ℝ)^24≤z := by exact_mod_cast hyz
    have h := Real.log_le_log (pow_pos hypos 24) hp
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  have hmul := mul_le_mul_of_nonneg_right h4l (by linarith : 0≤1+Real.log (y : ℝ))
  nlinarith

#print axioms denominator_ge_half_product_of_pow
#print axioms prime_log_reciprocal_bound
#print axioms denominator_ge_half_product_of_cutoff
end QuantitativeEulerEndpointSieve
