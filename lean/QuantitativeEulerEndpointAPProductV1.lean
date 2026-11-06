module

public import QuantitativeEulerEndpointAPHarmonicV1
public import QuantitativeEulerEndpointProductV1
public import QuantitativeHolomorphicPrimeProductV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointAP
open Finset

def auxiliaryPrimes (B : Finset ℕ) (Y : ℕ) : Finset ℕ :=
  Y.primesBelow.filter (fun p => p∉B)

theorem finite_remove_bound (S B : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0≤f n) :
    (∑ n∈S, f n)≤(∑ n∈S.filter (fun n => n∉B), f n)+∑ n∈B, f n := by
  have hsplit := sum_filter_add_sum_filter_not S (fun n => n∈B) f
  have hbad : (∑ n∈S.filter (fun n => n∈B), f n)≤∑ n∈B, f n :=
    sum_le_sum_of_subset_of_nonneg (fun n hn => (mem_filter.mp hn).2) (fun n _ _ => hf n)
  linarith

/-- Finite exclusions only change the additive constant in the quantitative
AP reciprocal estimate. -/
theorem auxiliary_AP_mass_lower {M : ℕ} [NeZero M] (a : ZMod M) (ha : IsUnit a)
    (B : Finset ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ Y : ℕ, 4≤Y →
      apExponent M*Real.log (Real.log (Y : ℝ))-C≤
        ∑ p∈auxiliaryPrimes B Y, if (p : ZMod M)=a then 1/(p : ℝ) else 0 := by
  obtain ⟨C,hC,hwhole⟩ := primeReciprocal_loglog_lower a ha
  refine ⟨C+∑ p∈B, primeReciprocal a p,add_nonneg hC (sum_nonneg (fun p _ => primeReciprocal_nonneg a p)),?_⟩
  intro Y hY
  have hr := finite_remove_bound (range Y) B (primeReciprocal a) (primeReciprocal_nonneg a)
  have he : (∑ n∈(range Y).filter (fun n => n∉B), primeReciprocal a n)=
      ∑ p∈auxiliaryPrimes B Y, if (p : ZMod M)=a then 1/(p : ℝ) else 0 := by
    simp only [auxiliaryPrimes,Nat.primesBelow_eq_filter_range,filter_filter,sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hnB : n∈B <;> by_cases hp : n.Prime <;> simp [primeReciprocal,hnB,hp]
  rw [he] at hr
  have h := hwhole Y hY
  linarith

/-- The full baseline Euler product supplies exactly one logarithmic power,
even after any fixed finite exclusions. -/
theorem auxiliary_baseline_bound (B : Finset ℕ) (Y : ℕ) (hY : 2≤Y) :
    (∏ p∈auxiliaryPrimes B Y, (1-1/(p : ℝ)))≤
      Real.exp (∑ p∈B, |1/((p : ℝ)-1)|)/Real.log (Y : ℝ) := by
  let K : ℝ := ∑ p∈B, |1/((p : ℝ)-1)|
  have hbad : (∑ p∈Y.primesBelow.filter (fun p => ¬p∉B), 1/((p : ℝ)-1))≤K := by
    apply (sum_le_sum (fun (p : ℕ) _ => le_abs_self (1/((p : ℝ)-1)))).trans
    exact sum_le_sum_of_subset_of_nonneg
      (fun p hp => by simpa only [not_not] using (mem_filter.mp hp).2)
      (fun p _ _ => abs_nonneg _)
  have hNat : Y-1+1=Y := Nat.sub_add_cancel (by omega)
  have hCast : ((Y-1 : ℕ) : ℝ)+1=(Y : ℝ) := by exact_mod_cast hNat
  have h := QuantitativeEulerEndpointProduct.endpoint_product (fun p => p∉B) (Y-1)
    (by omega) (B := K) (by simpa only [hNat] using hbad)
  simp only [hNat,hCast] at h
  convert h using 1
  apply prod_congr rfl
  intro p hp
  exact (QuantitativeEulerEndpointProduct.variable_tolerance_factor
    (Nat.prime_of_mem_primesBelow (mem_filter.mp hp).1)).symm

/-- Quantitative decay of the actual two-residue Euler product, with a
strictly positive extra logarithmic exponent for every unit class. -/
theorem two_residue_AP_product_bound {M : ℕ} [NeZero M]
    (a : ZMod M) (ha : IsUnit a) (B : Finset ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ Y : ℕ, 4≤Y →
      (∏ p∈auxiliaryPrimes B Y, (1-(if (p : ZMod M)=a then (2 : ℝ) else 1)/(p : ℝ)))≤
        C/(Real.log (Y : ℝ))^(1+apExponent M) := by
  obtain ⟨C,hC,hAP⟩ := auxiliary_AP_mass_lower a ha B
  let K : ℝ := ∑ p∈B, |1/((p : ℝ)-1)|
  refine ⟨Real.exp (K+C),Real.exp_pos _,fun Y hY => ?_⟩
  let S := auxiliaryPrimes B Y
  let r : ℕ → ℝ := fun p => if (p : ZMod M)=a then 1/(p : ℝ) else 0
  have hp (p : ℕ) (h : p∈S) : p.Prime := Nat.prime_of_mem_primesBelow (mem_filter.mp h).1
  have hp2 (p : ℕ) (h : p∈S) : (2 : ℝ)≤p := by exact_mod_cast (hp p h).two_le
  have hr (p : ℕ) (h : p∈S) : 0≤r p ∧ r p≤1 := by
    dsimp [r]
    split_ifs
    · refine ⟨by positivity,(div_le_one (by have := hp2 p h; linarith)).mpr ?_⟩
      have := hp2 p h
      linarith
    · norm_num
  have hprod : (∏ p∈S, (1-(if (p : ZMod M)=a then (2 : ℝ) else 1)/(p : ℝ)))≤
      (∏ p∈S, (1-1/(p : ℝ)))*(∏ p∈S, (1-r p)) := by
    rw [← prod_mul_distrib]
    apply prod_le_prod₀
    · intro p h
      have hpp := hp2 p h
      split_ifs <;> apply sub_nonneg.mpr <;> apply (div_le_one (by linarith)).mpr <;> linarith
    · intro p h
      dsimp [r]
      split_ifs
      · simp only [div_eq_mul_inv,one_mul]
        nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
      · simp
  have hextra : (∏ p∈S, (1-r p))≤Real.exp (C-apExponent M*Real.log (Real.log (Y : ℝ))) := by
    apply (QuantitativeHolomorphic.contraction_product_le_exp S r hr).trans
    apply Real.exp_le_exp.mpr
    have h := hAP Y hY
    change _≤∑ p∈S, r p at h
    linarith
  have hlY : 0<Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (show 1<Y by omega))
  have hbase := auxiliary_baseline_bound B Y (by omega)
  have hmul := mul_le_mul hbase hextra
    (prod_nonneg (fun p h => sub_nonneg.mpr (hr p h).2))
    (div_nonneg (Real.exp_pos _).le hlY.le)
  apply hprod.trans
  apply hmul.trans
  apply le_of_eq
  dsimp only [K]
  rw [Real.rpow_add hlY,Real.rpow_one,Real.rpow_def_of_pos hlY,Real.exp_sub,Real.exp_add]
  ring

#print axioms auxiliary_AP_mass_lower
#print axioms two_residue_AP_product_bound
end QuantitativeEulerEndpointAP
