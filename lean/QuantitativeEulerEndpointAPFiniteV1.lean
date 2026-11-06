module

public import QuantitativeEulerEndpointAPSmoothedV1
public import QuantitativeEulerEndpointPrimeTailV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointAP
open Finset

def primeReciprocal {M : ℕ} (a : ZMod M) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n : ZMod M)=a then 1/(n : ℝ) else 0

theorem primeReciprocal_nonneg {M : ℕ} (a : ZMod M) (n : ℕ) : 0≤primeReciprocal a n := by
  unfold primeReciprocal
  split_ifs <;> positivity

/-- Removing the smoothed tail costs at most the global logarithmic prime
Dirichlet sum divided by log Y. This is an actual finite-cutoff inequality. -/
theorem primeDirichlet_le_finite_add_tail {M : ℕ} (a : ZMod M) {t : ℝ}
    (ht : 0<t) (Y : ℕ) (hY : 2≤Y) :
    (∑' n, primeDirichlet a t n)≤(∑ n∈range Y, primeReciprocal a n)+
      Real.log 4*(1+1/t)/Real.log (Y : ℝ) := by
  let F : ℕ → ℝ := fun n => if n<Y then primeReciprocal a n else 0
  let G : ℕ → ℝ := fun n => if n.Prime then Real.log (n : ℝ)/(n : ℝ)^(1+t) else 0
  have hYpos : (0 : ℝ)<Y := by exact_mod_cast (show 0<Y by omega)
  have hlY : 0<Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (show 1<Y by omega))
  have hG0 (n : ℕ) : 0≤G n := by
    dsimp only [G]
    split_ifs with hn
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn.one_lt.le))
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · exact le_rfl
  have hpoint (n : ℕ) : primeDirichlet a t n≤F n+G n/Real.log (Y : ℝ) := by
    by_cases hp : n.Prime ∧ (n : ZMod M)=a
    · have hnpos : (0 : ℝ)<n := by exact_mod_cast hp.1.pos
      have hn1 : (1 : ℝ)≤n := by exact_mod_cast hp.1.one_lt.le
      by_cases hnY : n<Y
      · have hpow : (n : ℝ)≤(n : ℝ)^(1+t) := by
          conv_lhs => rw [← Real.rpow_one (n : ℝ)]
          exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        have hle := one_div_le_one_div_of_le hnpos hpow
        have htail : 0≤G n/Real.log (Y : ℝ) := div_nonneg (hG0 n) hlY.le
        simpa only [primeDirichlet,primeReciprocal,F,hp,and_self,ite_true,hnY] using
          hle.trans (le_add_of_nonneg_right htail)
      · have hl : Real.log (Y : ℝ)≤Real.log (n : ℝ) :=
          Real.log_le_log hYpos (by exact_mod_cast (show Y≤n by omega))
        have hh := div_le_div_of_nonneg_right hl (Real.rpow_nonneg (Nat.cast_nonneg n) (1+t))
        have hk : 1/(n : ℝ)^(1+t)≤(Real.log (n : ℝ)/(n : ℝ)^(1+t))/Real.log (Y : ℝ) := by
          apply (le_div_iff₀ hlY).mpr
          simpa only [div_eq_mul_inv,one_mul,mul_comm] using hh
        simpa only [primeDirichlet,F,G,hp,hp.1,and_self,ite_true,hnY,ite_false,zero_add] using hk
    · have hz : primeDirichlet a t n=0 := by simp [primeDirichlet,hp]
      rw [hz]
      exact add_nonneg (by dsimp [F]; split_ifs; exact primeReciprocal_nonneg a n; exact le_rfl)
        (div_nonneg (hG0 n) hlY.le)
  have hFs : Summable F := summable_of_ne_finset_zero (s := range Y) (by
    intro n hn
    simp only [mem_range,not_lt] at hn
    simp only [F,show ¬n<Y from not_lt.mpr hn,ite_false])
  have hGs : Summable G := by
    apply (primeLogDirichlet_summable (0 : ZMod 1) ht).congr
    intro n
    simp only [G,primeLogDirichlet,show (n : ZMod 1)=0 from Subsingleton.elim _ _,and_true]
  have hFsum : (∑' n, F n)=∑ n∈range Y, primeReciprocal a n := by
    rw [tsum_eq_sum (s := range Y) (by intro n hn; simp only [mem_range] at hn; simp [F,hn])]
    apply sum_congr rfl
    intro n hn
    simp only [F,mem_range.mp hn,ite_true]
  have hsum := (primeDirichlet_summable a ht).tsum_le_tsum hpoint (hFs.add (hGs.div_const _))
  rw [hFs.tsum_add (hGs.div_const _),hFsum,tsum_div_const] at hsum
  exact hsum.trans (add_le_add le_rfl
    (div_le_div_of_nonneg_right (prime_log_dirichlet_upper ht) hlY.le))

/-- Actual finite reciprocal mass in a unit residue class at a prescribed
logarithmic scale. The tail loss is an absolute constant. -/
theorem finite_primeReciprocal_dyadic_lower {M : ℕ} [NeZero M]
    (a : ZMod M) (ha : IsUnit a) :
    ∃ C : ℝ, 0≤C ∧ ∀ J Y : ℕ, 2≤Y → 1≤dyadic J*Real.log (Y : ℝ) →
      (M.totient : ℝ)⁻¹*(J : ℝ)/2-C≤∑ n∈range Y, primeReciprocal a n := by
  obtain ⟨C,hC,hsm⟩ := primeDirichlet_dyadic_lower a ha
  have h4 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨C+2*Real.log 4,by positivity,fun J Y hY hcut => ?_⟩
  have ht := dyadic_pos J
  have ht1 := dyadic_le_one J
  have hlY : 0<Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (show 1<Y by omega))
  have htail : Real.log 4*(1+1/dyadic J)/Real.log (Y : ℝ)≤2*Real.log 4 := by
    apply (div_le_iff₀ hlY).mpr
    have hL : 1/dyadic J≤Real.log (Y : ℝ) := (div_le_iff₀ ht).mpr (by nlinarith)
    have h1 : 1≤Real.log (Y : ℝ) := by nlinarith
    have hh := mul_le_mul_of_nonneg_left (show 1+1/dyadic J≤2*Real.log (Y : ℝ) by linarith) h4
    nlinarith
  have hupper := primeDirichlet_le_finite_add_tail a ht Y hY
  have hlower := hsm J
  linarith

#print axioms primeDirichlet_le_finite_add_tail
#print axioms finite_primeReciprocal_dyadic_lower
end QuantitativeEulerEndpointAP
