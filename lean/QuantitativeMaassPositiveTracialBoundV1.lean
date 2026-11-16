module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

set_option autoImplicit false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeMaass

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- Norm bound for a positive-weighted real trace. The star condition is
retained explicitly; positivity on self-adjoint elements alone would not
control the skew-adjoint part of an arbitrary real-linear functional. -/
theorem positive_tracial_mul_bound (τ : 𝔄→L[ℝ]ℝ) (hm : Monotone τ)
    (hc : ∀ a b,τ (a*b)=τ (b*a)) (hs : ∀ a,τ (star a)=τ a)
    (B D : 𝔄) (hD : 0≤D) : |τ (B*D)|≤‖B‖*τ D := by
  let R := CFC.sqrt D
  have hR : IsSelfAdjoint R := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg D)
  have hRR : R*R=D := CFC.sqrt_mul_sqrt_self D hD
  have htrace (A : 𝔄) : τ (R*A*R)=τ (A*D) := by
    rw [hc (R*A) R,←mul_assoc,hRR,hc D A]
  have hstar : τ (star B*D)=τ (B*D) := by
    have hh := hs (B*D)
    rw [star_mul,(IsSelfAdjoint.of_nonneg hD).star_eq,hc D (star B)] at hh
    exact hh
  let S : 𝔄 := (1/2:ℝ) • (B+star B)
  have hS : IsSelfAdjoint S := by
    change star ((1/2:ℝ) • (B+star B))=(1/2:ℝ) • (B+star B)
    simp only [star_smul,star_add,star_star,star_trivial,add_comm]
  have hn : ‖S‖≤‖B‖ := by
    dsimp only [S]
    rw [norm_smul]
    have hh := norm_add_le B (star B)
    rw [norm_star] at hh
    norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    linarith
  have ht : τ (R*S*R)=τ (B*D) := by
    rw [htrace]
    dsimp only [S]
    rw [smul_mul_assoc,add_mul,map_smul,map_add,hstar]
    simp only [smul_eq_mul]
    ring
  have hup := star_left_conjugate_le_conjugate (hS.le_algebraMap_norm_self S) R
  have hlo := star_left_conjugate_le_conjugate (hS.neg_algebraMap_norm_le_self S) R
  have hu0 : R*S*R≤‖S‖ • D := by
    simpa only [hR.star_eq,Algebra.algebraMap_eq_smul_one,mul_smul_comm,
      smul_mul_assoc,mul_one,hRR] using hup
  have hl0 : -(‖S‖ • D)≤R*S*R := by
    simpa only [hR.star_eq,Algebra.algebraMap_eq_smul_one,mul_neg,neg_mul,
      mul_smul_comm,smul_mul_assoc,mul_one,hRR] using hlo
  have hu := hm hu0
  have hl := hm hl0
  rw [ht,map_smul,smul_eq_mul] at hu
  rw [ht,map_neg,map_smul,smul_eq_mul] at hl
  have hab : |τ (B*D)|≤‖S‖*τ D := abs_le.mpr ⟨hl,hu⟩
  have htd : 0≤τ D := by simpa only [map_zero] using hm hD
  exact hab.trans (mul_le_mul_of_nonneg_right hn htd)

#print axioms positive_tracial_mul_bound
end QuantitativeMaass
