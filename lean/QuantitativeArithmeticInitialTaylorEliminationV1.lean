module
public import QuantitativeArithmeticInitialTaylorGermTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticInitialTaylorGerm
open Complex QuantitativeArithmeticAnalyticGerm

private theorem combine_sums {ι τ : Type*} [Fintype ι] [Fintype τ]
    (w e : ι → ℂ) (c : ι → ℕ → τ → ℂ) (g : ℕ → τ → ℂ) (M : ℕ) :
    (∑ i, w i*(e i+∑ n∈Finset.range M, ∑ j, c i n j*g n j))=
      (∑ i, w i*e i)+∑ n∈Finset.range M, ∑ j, (∑ i, w i*c i n j)*g n j := by
  classical
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_mul,mul_assoc]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]

/-- A finite weighted elimination of lower Taylor terms can be continued
using only the observed combinations G. No meromorphic continuation of the
individual functions hidden inside the lower residuals is required. -/
theorem finite_shifted_elimination_germ {ι τ : Type*} [Fintype ι] [Fintype τ]
    (G₀ G : ℂ → τ → ℂ) (R : ι → ℂ → ℂ)
    (C : ι → ℕ → ℂ → τ → ℂ) (E : ι → ℕ → ℂ → ℂ)
    (W : ι → ℂ → ℂ) (depth : ι → ℕ) (D : ℕ) (hd : ∀ i, depth i≤D)
    (A : ℂ → ℂ) (B : ℝ)
    (hrow : ∀ i M z, B<z.re → R i z=E i M z+
      ∑ n∈Finset.range M, ∑ j, C i n z j*G₀ (z+((n:ℂ)+1)) j)
    (hcompat : ∀ z, B<z.re → G₀ z=G z)
    (hcancel : ∀ z, B+(D:ℝ)<z.re →
      A z=∑ i, W i z*shiftedPrefix G₀ (R i) (C i) (depth i) z)
    (hG : ∀ j z, MeromorphicNFAt (fun w => G w j) z)
    (hA : ∀ z, MeromorphicAt A z)
    (hC : ∀ i n j z, AnalyticAt ℂ (fun w => C i n w j) z)
    (hE : ∀ i (M : ℕ) z, B-((M:ℝ)+1)<z.re → AnalyticAt ℂ (E i M) z)
    (hW : ∀ i z, MeromorphicAt (W i) z)
    (x : ℂ) (hWx : ∀ i, AnalyticAt ℂ (W i) x)
    (hshift : ∀ n : ℕ, 0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (x+n)) : HasAnalyticGerm A x := by
  classical
  let C' : ℕ → ℂ → τ → ℂ := fun n z j =>
    ∑ i, W i z*C i (n+depth i) (z-(depth i:ℂ)) j
  let E' : ℕ → ℂ → ℂ := fun M z =>
    ∑ i, W i z*E i (depth i+M) (z-(depth i:ℂ))
  have hCa (i : ι) (n : ℕ) (j : τ) (z : ℂ) :
      AnalyticAt ℂ (fun w => C i (n+depth i) (w-(depth i:ℂ)) j) z :=
    (hC i (n+depth i) j _).comp (f:=fun w : ℂ => w-(depth i:ℂ))
      (analyticAt_id.sub analyticAt_const)
  have hEa (i : ι) (M : ℕ) (z : ℂ) (hz : B-((M:ℝ)+1)<z.re) :
      AnalyticAt ℂ (fun w => E i (depth i+M) (w-(depth i:ℂ))) z :=
    shifted_remainder_analytic (E i) B (hE i) (depth i) M z hz
  apply analytic_germ_of_local_coefficients G A (B+(D:ℝ)) C' E' hG hA
  · intro n j z
    apply MeromorphicAt.fun_sum
    intro i hi
    exact (hW i z).mul (hCa i n j z).meromorphicAt
  · intro M z hz
    apply MeromorphicAt.fun_sum
    intro i hi
    have hD : (0:ℝ)≤D := Nat.cast_nonneg D
    exact (hW i z).mul (hEa i M z (by linarith)).meromorphicAt
  · intro M z hz
    rw [hcancel z hz]
    have hprefix (i : ι) : shiftedPrefix G₀ (R i) (C i) (depth i) z=
        E i (depth i+M) (z-(depth i:ℂ))+
        ∑ n∈Finset.range M, ∑ j,
          C i (n+depth i) (z-(depth i:ℂ)) j*G (z+((n:ℂ)+1)) j := by
      have hdi : (depth i:ℝ)≤D := by exact_mod_cast hd i
      rw [shifted_prefix_identity G₀ (R i) (C i) (E i) B (hrow i) (depth i) M z (by linarith)]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      have hh : B<(z+((n:ℂ)+1)).re := by
        simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
        have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
        have hD : (0:ℝ)≤D := Nat.cast_nonneg D
        linarith
      rw [hcompat _ hh]
    simp_rw [hprefix]
    exact combine_sums (fun i => W i z)
      (fun i => E i (depth i+M) (z-(depth i:ℂ)))
      (fun i n j => C i (n+depth i) (z-(depth i:ℂ)) j)
      (fun n j => G (z+((n:ℂ)+1)) j) M
  · intro n j
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact (hWx i).mul (hCa i n j x)
  · intro M hx
    apply Finset.analyticAt_fun_sum
    intro i hi
    have hD : (0:ℝ)≤D := Nat.cast_nonneg D
    exact (hWx i).mul (hEa i M x (by linarith))
  · exact hshift

#print axioms finite_shifted_elimination_germ
end QuantitativeArithmeticInitialTaylorGerm
