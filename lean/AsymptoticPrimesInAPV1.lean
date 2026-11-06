module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPrimesInAP

open ArithmeticFunction ArithmeticFunction.vonMangoldt Filter
open scoped Topology

/-- A summable majorant for the scaled logarithmic prime terms. -/
theorem scaled_log_le_inv (n x : ℝ) (hn : 0<n) :
    (x-1)*(Real.log n/n^x)≤n⁻¹ := by
  have he : (x-1)*Real.log n≤n^(x-1) := by
    rw [Real.rpow_def_of_pos hn]
    have h := Real.add_one_le_exp (Real.log n*(x-1))
    nlinarith
  have hpow : n^x=n*n^(x-1) := by
    conv_lhs => rw [show x=1+(x-1) by ring]
    rw [Real.rpow_add hn,Real.rpow_one]
  rw [hpow,← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos hn (Real.rpow_pos_of_pos hn _))).mpr
  simpa only [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul] using he

noncomputable def reciprocal {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n:ZMod q)=a then (n:ℝ)⁻¹ else 0

/-- Reciprocal primes in every unit residue class have divergent sum.
The proof uses the pole of the residue-class von Mangoldt L-series and
dominated convergence, not a prime-number theorem in progressions. -/
theorem not_summable_reciprocal {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ¬Summable (reciprocal a) := by
  classical
  intro hsum
  let B : ℕ → ℝ := fun n => reciprocal a n+(if n.Prime then 0 else residueClass a n)/n
  have hB : Summable B := hsum.add (summable_residueClass_non_primes_div a)
  let F : ℝ → ℕ → ℝ := fun x n => (x-1)*(residueClass a n/(n:ℝ)^x)
  have hpoint (n : ℕ) : Tendsto (fun x => F x n) (𝓝[>] (1:ℝ)) (𝓝 0) := by
    by_cases hn : n=0
    · subst n
      simpa only [F,residueClass_apply_zero,zero_div,mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℝ)) (𝓝[>] (1:ℝ)) (𝓝 0))
    · have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
      have hc : ContinuousAt (fun x : ℝ => F x n) 1 :=
        (continuousAt_id.sub continuousAt_const).mul
          (continuousAt_const.div (Real.continuousAt_const_rpow hn') (by simpa using hn'))
      simpa only [F,sub_self,zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ x : ℝ in 𝓝[>] 1,x∈Set.Ioc 1 2 := by
    filter_upwards [Ioo_mem_nhdsGT (show (1:ℝ)<2 by norm_num)] with x hx
    exact ⟨hx.1,hx.2.le⟩
  have hbound : ∀ᶠ x : ℝ in 𝓝[>] 1,∀ n,‖F x n‖≤B n := by
    filter_upwards [hnear] with x hx n
    have hnonneg : 0≤F x n := mul_nonneg (sub_nonneg.mpr hx.1.le)
      (div_nonneg (residueClass_nonneg a n) (Real.rpow_nonneg (Nat.cast_nonneg n) x))
    rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
    by_cases hp : n.Prime
    · by_cases he : (n:ZMod q)=a
      · simpa only [F,B,reciprocal,hp,he,and_self,ite_true,residueClass,
          Set.indicator,Set.mem_ofPred_eq,he,ite_true,vonMangoldt_apply_prime hp,zero_div,add_zero] using
          scaled_log_le_inv (n:ℝ) x (by exact_mod_cast hp.pos)
      · simp [F,B,reciprocal,residueClass,hp,he]
    · by_cases hn : n=0
      · subst n
        simp [F,B,reciprocal]
      · have hn' : (1:ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        have hpos : (0:ℝ)<n := lt_of_lt_of_le zero_lt_one hn'
        have hpow : (n:ℝ)≤(n:ℝ)^x := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn' hx.1.le
        have hv : residueClass a n/(n:ℝ)^x≤residueClass a n/n :=
          div_le_div_of_nonneg_left (residueClass_nonneg a n) hpos hpow
        have hm : (x-1)*(residueClass a n/(n:ℝ)^x)≤1*(residueClass a n/(n:ℝ)^x) :=
          mul_le_mul_of_nonneg_right (by linarith [hx.2])
            (div_nonneg (residueClass_nonneg a n) (Real.rpow_nonneg hpos.le x))
        simpa only [F,B,reciprocal,hp,false_and,ite_false,zero_add,one_mul] using hm.trans (by simpa using hv)
  have ht : Tendsto (fun x => ∑' n,F x n) (𝓝[>] (1:ℝ)) (𝓝 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hB hpoint hbound
  obtain ⟨C,hC⟩ := LSeries_residueClass_lower_bound ha
  have hlow : ∀ᶠ x : ℝ in 𝓝[>] 1,(q.totient:ℝ)⁻¹≤(∑' n,F x n)+C*(x-1) := by
    filter_upwards [hnear] with x hx
    have hh := mul_le_mul_of_nonneg_left (hC hx) (sub_nonneg.mpr hx.1.le)
    have hz : x-1≠0 := sub_ne_zero.mpr hx.1.ne'
    rw [mul_sub,mul_div_cancel₀ _ hz] at hh
    rw [show (∑' n,F x n)=(x-1)*(∑' n,residueClass a n/(n:ℝ)^x) by
      exact tsum_mul_left]
    nlinarith
  have hc : Tendsto (fun x : ℝ => C*(x-1)) (𝓝[>] (1:ℝ)) (𝓝 0) := by
    have hc' : ContinuousAt (fun x : ℝ => C*(x-1)) 1 := by fun_prop
    simpa only [sub_self,mul_zero] using hc'.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : (q.totient:ℝ)⁻¹≤0 := by
    simpa only [add_zero] using ge_of_tendsto (ht.add hc) hlow
  exact (not_le_of_gt (inv_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)))) hzero

#print axioms scaled_log_le_inv
#print axioms not_summable_reciprocal

end AsymptoticPrimesInAP
