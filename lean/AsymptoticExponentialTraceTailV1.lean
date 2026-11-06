module

public import AsymptoticFourierUpperTailV1
public import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFourierNorm

open Filter Finset
open scoped BigOperators

/-- Sum of a constant bound and an exponential tail. Keeping the constant
explicit also controls the localized difference of two Fourier families. -/
theorem bounded_exp_summable_bound (f : ℕ → ℝ) {a b C : ℝ} (ha : 0<a) (hb : 0≤b)
    (hC : 0≤C) (h0 : ∀ n,0≤f n) (h1 : ∀ n,f n≤C)
    (hexp : ∀ n,f n≤Real.exp (b-a*(n+1:ℕ))) :
    Summable f ∧ (∑' n,f n)≤C*(b/a)+1/(1-Real.exp (-a)) := by
  let q := Real.exp (-a)
  have hq0 : 0≤q := (Real.exp_pos _).le
  have hq1 : q<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  have hgeom := summable_geometric_of_lt_one hq0 hq1
  have hexp_eq (n : ℕ) : Real.exp (b-a*(n+1:ℕ))=Real.exp (b-a)*q^n := by
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hsum : Summable f := Summable.of_nonneg_of_le h0
    (fun n => (hexp n).trans_eq (hexp_eq n)) (hgeom.mul_left (Real.exp (b-a)))
  refine ⟨hsum,?_⟩
  let M := Nat.floor (b/a)
  have hM : (M:ℝ)≤b/a := Nat.floor_le (div_nonneg hb ha.le)
  have hM' : b/a<(M:ℝ)+1 := Nat.lt_floor_add_one _
  have htail (n : ℕ) : f (n+M)≤q^n := by
    apply (hexp (n+M)).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hm := (div_lt_iff₀ ha).mp hM'
    push_cast
    nlinarith
  have htailsum : Summable (fun n => f (n+M)) :=
    hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have htailbound : (∑' n,f (n+M))≤1/(1-q) := by
    apply (htailsum.tsum_le_tsum htail hgeom).trans_eq
    simpa only [one_div] using tsum_geometric_of_lt_one hq0 hq1
  have hhead : (∑ n∈range M,f n)≤C*(b/a) := by
    calc
      _ ≤ ∑ _n∈range M,C := sum_le_sum (fun n _ => h1 n)
      _ = C*(M:ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hM hC
  rw [← hsum.sum_add_tsum_nat_add M]
  exact add_le_add hhead htailbound

/-- The unit-bound version used for individual Fourier masses. -/
theorem capped_exp_summable_bound (f : ℕ → ℝ) {a b : ℝ} (ha : 0<a) (hb : 0≤b)
    (h0 : ∀ n,0≤f n) (h1 : ∀ n,f n≤1)
    (hexp : ∀ n,f n≤Real.exp (b-a*(n+1:ℕ))) :
    Summable f ∧ (∑' n,f n)≤b/a+1/(1-Real.exp (-a)) := by
  simpa only [one_mul] using bounded_exp_summable_bound f ha hb zero_le_one h0 h1 hexp

/-- The actual normalized Fourier mass above H has the manuscript's
O(k/H)+O_H(1) bound, including the capped weight. -/
theorem upperMass_summable_bound (m t : ℕ) {scale ε H : ℝ}
    (hs : 0<scale) (hε : 0<ε) (hH : 0<H) :
    Summable (fun n => upperMass m t (scale*(n+1:ℕ)) ε H) ∧
      (∑' n,upperMass m t (scale*(n+1:ℕ)) ε H)≤
        ((m+2*t+1:ℕ):ℝ)*Real.log 2/(scale*H/2)+1/(1-Real.exp (-(scale*H/2))) := by
  apply capped_exp_summable_bound _ (by positivity)
    (mul_nonneg (by positivity) (Real.log_nonneg (by norm_num)))
    (fun n => upperMass_nonneg m t (mul_pos hs (by positivity)) hε H)
    (fun n => upperMass_le_one m t (mul_pos hs (by positivity)) hε H)
  intro n
  apply (upperMass_le_exp m t (mul_pos hs (by positivity)) hε H).trans_eq
  rw [show (2:ℝ)^(m+2*t+1)=Real.exp (((m+2*t+1:ℕ):ℝ)*Real.log 2) by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]]
  rw [← Real.exp_add]
  congr 1
  ring

#print axioms bounded_exp_summable_bound
#print axioms capped_exp_summable_bound
#print axioms upperMass_summable_bound

end AsymptoticFourierNorm
