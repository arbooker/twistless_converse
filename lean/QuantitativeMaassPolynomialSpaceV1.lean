module

public import QuantitativeMaassEulerDecayV1
public import AsymptoticCylinderEmbeddingV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter Asymptotics
open scoped Topology

namespace QuantitativeMaass

/-- Polynomially bounded cusp coefficients, allowing an individual degree
for each vector. This is a genuine complex vector space. -/
def polynomialCoefficientSpace : Submodule ℂ (ℕ → ℂ) where
  carrier := {a | a 0=0 ∧ ∃ d : ℕ,∃ C : ℝ,0≤C ∧ ∀ n : ℕ,0<n → ‖a n‖≤C*(n:ℝ)^d}
  zero_mem' := ⟨rfl,0,0,le_rfl,fun _ _ => by simp⟩
  add_mem' := by
    rintro a b ⟨ha0,d,C,hC,ha⟩ ⟨hb0,e,D,hD,hb⟩
    refine ⟨by simp [ha0,hb0],d+e,C+D,add_nonneg hC hD,?_⟩
    intro n hn
    have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
    have hd : (n:ℝ)^d≤(n:ℝ)^(d+e) := pow_le_pow_right₀ hn1 (Nat.le_add_right d e)
    have he : (n:ℝ)^e≤(n:ℝ)^(d+e) := pow_le_pow_right₀ hn1 (Nat.le_add_left e d)
    calc
      ‖(a+b) n‖≤‖a n‖+‖b n‖ := norm_add_le _ _
      _ ≤ C*(n:ℝ)^d+D*(n:ℝ)^e := add_le_add (ha n hn) (hb n hn)
      _ ≤ C*(n:ℝ)^(d+e)+D*(n:ℝ)^(d+e) := add_le_add
        (mul_le_mul_of_nonneg_left hd hC) (mul_le_mul_of_nonneg_left he hD)
      _ = _ := by ring
  smul_mem' := by
    rintro c a ⟨ha0,d,C,hC,ha⟩
    refine ⟨by simp [ha0],d,‖c‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
    intro n hn
    calc
      ‖(c•a) n‖=‖c‖*‖a n‖ := norm_smul c (a n)
      _ ≤ ‖c‖*(C*(n:ℝ)^d) := mul_le_mul_of_nonneg_left (ha n hn) (norm_nonneg _)
      _ = _ := by ring

theorem polynomialCoefficientSpace_growth (a : polynomialCoefficientSpace) :
    MaassOriginal.PolynomialGrowth a.val := by
  obtain ⟨_,d,C,_,hC⟩ := a.property
  refine ⟨d,IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  simpa only [norm_norm,Real.rpow_natCast,Real.norm_eq_abs,abs_norm,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) d)]
    using hC n hn

theorem mem_polynomialCoefficientSpace {b : ℕ → ℂ} (hb0 : b 0=0)
    (hb : MaassOriginal.PolynomialGrowth b) : b∈polynomialCoefficientSpace := by
  obtain ⟨d,C,hC,hb⟩ := polynomialGrowth_positive_bound hb
  refine ⟨hb0,d,C,hC.le,?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ n => exact hb n

#print axioms polynomialCoefficientSpace
#print axioms polynomialCoefficientSpace_growth
#print axioms mem_polynomialCoefficientSpace

end QuantitativeMaass
