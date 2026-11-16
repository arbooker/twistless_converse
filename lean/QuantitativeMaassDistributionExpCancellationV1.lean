module

public import QuantitativeMaassDistributionIntegratingFactorV1
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Nat.Choose.Cast

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter Finset
open scoped Topology

namespace QuantitativeMaass

def inverseExpCoefficient (n m : ℕ) : ℝ :=
  (-1:ℝ)^n*(n.factorial:ℝ)⁻¹*(m.factorial:ℝ)⁻¹

theorem inverseExpCoefficient_antidiagonal (n : ℕ) :
    ∑ p∈antidiagonal n,inverseExpCoefficient p.1 p.2=(n.factorial:ℝ)⁻¹*(0:ℝ)^n := by
  have hb : (0:ℝ)^n=∑ p∈antidiagonal n,n.choose p.1 • (-1:ℝ)^p.1 := by
    simpa only [neg_add_cancel,one_pow,mul_one] using (Commute.all (-1:ℝ) 1).add_pow' n
  rw [hb,mul_sum]
  apply sum_congr rfl
  intro p hp
  have he : p.1+p.2=n := mem_antidiagonal.mp hp
  rw [← he,nsmul_eq_mul,Nat.cast_add_choose]
  unfold inverseExpCoefficient
  field_simp

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem inverseExpCoefficient_vector_antidiagonal (x : ℕ → H) (n : ℕ) :
    ∑ p∈antidiagonal n,inverseExpCoefficient p.1 p.2 • x (p.1+p.2)=
      if n=0 then x 0 else 0 := by
  classical
  have he : (∑ p∈antidiagonal n,inverseExpCoefficient p.1 p.2 • x (p.1+p.2))=
      (∑ p∈antidiagonal n,inverseExpCoefficient p.1 p.2) • x n := by
    rw [sum_smul]
    apply sum_congr rfl
    intro p hp
    rw [mem_antidiagonal.mp hp]
  rw [he,inverseExpCoefficient_antidiagonal]
  by_cases hn : n=0
  · simp [hn]
  · simp [hn,zero_pow hn]

/-- Absolute summability licenses grouping the double exponential series
by total degree. On each positive-degree antidiagonal the coefficients
cancel exactly, leaving only the original zeroth term. -/
theorem inverseExp_double_sum [CompleteSpace H] (x : ℕ → H)
    (hs : Summable (fun p : ℕ×ℕ => inverseExpCoefficient p.1 p.2 • x (p.1+p.2))) :
    (∑' n,∑' m,inverseExpCoefficient n m • x (n+m))=x 0 := by
  let F : ℕ×ℕ → H := fun p => inverseExpCoefficient p.1 p.2 • x (p.1+p.2)
  let e : (Σ n : ℕ,antidiagonal n) ≃ ℕ×ℕ := HasAntidiagonal.sigmaAntidiagonalEquivProd
  have hsig : Summable (fun p : Σ n : ℕ,antidiagonal n => F p.2) := e.summable_iff.mpr hs
  have he : (∑' p,F p)=∑' n,∑ p∈antidiagonal n,F p := by
    rw [← e.tsum_eq F]
    change (∑' p : Σ n : ℕ,antidiagonal n,F p.2)=_
    rw [hsig.tsum_sigma]
    apply tsum_congr
    intro n
    rw [tsum_fintype]
    change (∑ p : antidiagonal n,F p)=_
    convert! Finset.sum_finset_coe F (antidiagonal n) using 1
  rw [← hs.tsum_prod,he]
  change (∑' n,∑ p∈antidiagonal n,inverseExpCoefficient p.1 p.2 • x (p.1+p.2))=x 0
  simp_rw [inverseExpCoefficient_vector_antidiagonal]
  simp

/-- Exponential growth of a vector sequence implies absolute convergence
of the double inverse-exponential series. -/
theorem inverseExp_double_summable [CompleteSpace H] (x : ℕ → H)
    (C R : ℝ) (_hC : 0≤C) (hR : 0≤R) (hb : ∀ n,‖x n‖≤C*R^n) :
    Summable (fun p : ℕ×ℕ => inverseExpCoefficient p.1 p.2 • x (p.1+p.2)) := by
  have hs := Real.summable_pow_div_factorial R
  have hprod := hs.mul_of_nonneg hs (fun n => by positivity) (fun n => by positivity)
  apply Summable.of_norm_bounded (hprod.mul_left C)
  intro p
  have hc : ‖inverseExpCoefficient p.1 p.2‖=
      (p.1.factorial:ℝ)⁻¹*(p.2.factorial:ℝ)⁻¹ := by
    unfold inverseExpCoefficient
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,norm_inv,one_mul]
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤p.1.factorial),
      Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤p.2.factorial)]
  rw [norm_smul,hc]
  calc
    _ ≤ ((p.1.factorial:ℝ)⁻¹*(p.2.factorial:ℝ)⁻¹)*(C*R^(p.1+p.2)) :=
      mul_le_mul_of_nonneg_left (hb _) (by positivity)
    _ = C*((R^p.1/(p.1.factorial:ℝ))*(R^p.2/(p.2.factorial:ℝ))) := by
      rw [pow_add]
      ring

#print axioms inverseExpCoefficient_antidiagonal
#print axioms inverseExp_double_sum
#print axioms inverseExp_double_summable

end QuantitativeMaass
