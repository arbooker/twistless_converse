module

public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

namespace AsymptoticTraceCutoff

open Finset
open scoped BigOperators

/-- The Fourier cutoff estimate behind the normalized trace approximation:
a uniform error on the first M modes plus a quadratic tail costs at most
M*δ + C*k²/M. This statement is about the actual diagonal sums, before
any infinite-dimensional trace construction. -/
theorem sum_bound (e : ℕ → ℝ) {k M N : ℕ} (hM : 0<M) {δ C : ℝ} (hC : 0≤C)
    (hnonneg : ∀ n, 0≤e n) (hhead : ∀ n, 0<n → n≤M → e n≤δ)
    (htail : ∀ n, M<n → e n≤C*(k:ℝ)^2*((n:ℝ)^2)⁻¹) :
    (∑ n∈Ioc 0 N,e n) ≤ (M:ℝ)*δ+C*(k:ℝ)^2/(M:ℝ) := by
  let R := max M N
  have hMR : M≤R := le_max_left _ _
  have hNR : N≤R := le_max_right _ _
  have hsum : (∑ n∈Ioc 0 N,e n) ≤ ∑ n∈Ioc 0 R,e n := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,((mem_Ioc.mp hn).2).trans hNR⟩
    · exact fun n _ _ => hnonneg n
  have hfirst : (∑ n∈Ioc 0 M,e n)≤(M:ℝ)*δ := by
    calc
      (∑ n∈Ioc 0 M,e n) ≤ ∑ _n∈Ioc 0 M,δ := sum_le_sum (fun n hn =>
        hhead n (mem_Ioc.mp hn).1 (mem_Ioc.mp hn).2)
      _ = _ := by simp
  have hlast : (∑ n∈Ioc M R,e n)≤C*(k:ℝ)^2/(M:ℝ) := by
    calc
      (∑ n∈Ioc M R,e n) ≤ ∑ n∈Ioc M R,C*(k:ℝ)^2*((n:ℝ)^2)⁻¹ :=
        sum_le_sum (fun n hn => htail n (mem_Ioc.mp hn).1)
      _ = C*(k:ℝ)^2*∑ n∈Ioc M R,((n:ℝ)^2)⁻¹ := by rw [mul_sum]
      _ ≤ C*(k:ℝ)^2*((M:ℝ)⁻¹-(R:ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub hM.ne' hMR)
          (mul_nonneg hC (sq_nonneg _))
      _ ≤ C*(k:ℝ)^2/(M:ℝ) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity))
          (mul_nonneg hC (sq_nonneg _))
  have hsplit : (∑ n∈Ioc 0 R,e n)=(∑ n∈Ioc 0 M,e n)+(∑ n∈Ioc M R,e n) := by
    rw [← Ioc_union_Ioc_eq_Ioc (Nat.zero_le M) hMR,
      sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [hsplit] at hsum
  linarith

/-- With cutoff M=A*k, the normalized error is A*δ+C/A, uniformly in the
number of modes. This is the two-parameter bound used before taking the
observation trace limit. -/
theorem normalized_sum_bound (e : ℕ → ℝ) {k A N : ℕ} (hk : 0<k) (hA : 0<A)
    {δ C : ℝ} (hC : 0≤C) (hnonneg : ∀ n, 0≤e n)
    (hhead : ∀ n, 0<n → n≤A*k → e n≤δ)
    (htail : ∀ n, A*k<n → e n≤C*(k:ℝ)^2*((n:ℝ)^2)⁻¹) :
    (∑ n∈Ioc 0 N,e n)/(k:ℝ) ≤ (A:ℝ)*δ+C/(A:ℝ) := by
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have hA' : (0:ℝ)<A := by exact_mod_cast hA
  apply (div_le_iff₀ hk').mpr
  have hh := sum_bound (N:=N) e (Nat.mul_pos hA hk) hC hnonneg hhead htail
  have he : (A*k:ℕ)*δ+C*(k:ℝ)^2/(A*k:ℕ)=((A:ℝ)*δ+C/(A:ℝ))*(k:ℝ) := by
    push_cast
    field_simp
  rwa [he] at hh

/-- The same estimate proves summability and bounds the full diagonal
trace, including the required tail control. -/
theorem summable_and_tsum_bound (e : ℕ → ℝ) {k M : ℕ} (hM : 0<M)
    {δ C : ℝ} (hC : 0≤C) (hzero : e 0=0) (hnonneg : ∀ n, 0≤e n)
    (hhead : ∀ n, 0<n → n≤M → e n≤δ)
    (htail : ∀ n, M<n → e n≤C*(k:ℝ)^2*((n:ℝ)^2)⁻¹) :
    Summable e ∧ (∑' n,e n)≤(M:ℝ)*δ+C*(k:ℝ)^2/(M:ℝ) := by
  have hfin : ∀ s : Finset ℕ, (∑ n∈s,e n)≤(M:ℝ)*δ+C*(k:ℝ)^2/(M:ℝ) := by
    intro s
    let R := s.sup id
    have hs : s ⊆ insert 0 (Ioc 0 R) := by
      intro n hn
      have hnR : n≤R := Finset.le_sup (f:=id) hn
      by_cases hz : n=0
      · simp [hz]
      · exact mem_insert_of_mem (mem_Ioc.mpr ⟨by omega,hnR⟩)
    calc
      (∑ n∈s,e n) ≤ ∑ n∈insert 0 (Ioc 0 R),e n :=
        sum_le_sum_of_subset_of_nonneg hs (fun n _ _ => hnonneg n)
      _ = ∑ n∈Ioc 0 R,e n := by rw [sum_insert (by simp),hzero,zero_add]
      _ ≤ _ := sum_bound e hM hC hnonneg hhead htail
  exact ⟨summable_of_sum_le hnonneg hfin,Real.tsum_le_of_sum_le hnonneg hfin⟩

#print axioms sum_bound
#print axioms normalized_sum_bound
#print axioms summable_and_tsum_bound

end AsymptoticTraceCutoff
