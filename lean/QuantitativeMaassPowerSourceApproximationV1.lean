module

public import QuantitativeMaassPositivePowerDefectV1
public import QuantitativeMaassApproximateProjectionTraceV1
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
open ContinuousLinearMap
namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Quantitative approximate preservation from an order bound, including a
nonzero error. This applies after a bounded scalar change of metric and
does not require the source projection to commute with the filter. -/
theorem power_source_projection_error (A P : H→L[ℂ]H) (hA : A.IsPositive)
    (hAn : ‖A‖≤1) (hP : IsSelfAdjoint P) (hPP : P*P=P) (hP0 : 0≤P)
    {K δ : ℝ} (hK : 0≤K) (hδ : 0≤δ)
    (horder : P≤K • (1-A)+δ • (1:H→L[ℂ]H)) (m : ℕ) :
    ‖(1-A^m)*P-P‖^2≤K/(((2*m:ℕ):ℝ)+1)+δ := by
  let R := A^m
  have hR : IsSelfAdjoint R := hA.isSelfAdjoint.pow m
  have hRn : ‖R‖≤1 := by
    by_cases hm : m=0
    · subst m
      exact norm_id_le
    · exact (norm_pow_le' A (Nat.pos_of_ne_zero hm)).trans (pow_le_one₀ (norm_nonneg A) hAn)
  have hconj := star_left_conjugate_le_conjugate horder R
  rw [hR.star_eq] at hconj
  have hp : 0≤R*P*R := by
    have hh := (nonneg_iff_isPositive.mp hP0).adjoint_conj R
    simpa only [hR.adjoint_eq,←mul_def,mul_assoc] using nonneg_iff_isPositive.mpr hh
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hconj hp
  have he : R*(K • (1-A)+δ • (1:H→L[ℂ]H))*R=
      K • (R*(1-A)*R)+δ • (R*R) := by
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,mul_one]
  rw [he] at hn
  have hmain : ‖K • (R*(1-A)*R)‖≤K/(((2*m:ℕ):ℝ)+1) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hK]
    have hh := mul_le_mul_of_nonneg_left (positive_power_sandwich_norm A hA hAn m) hK
    simpa only [R,mul_one_div] using hh
  have herr : ‖δ • (R*R)‖≤δ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hδ]
    have hh : ‖R*R‖≤1 := (norm_mul_le R R).trans (by nlinarith [norm_nonneg R])
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hδ
  have hbound : ‖R*P*R‖≤K/(((2*m:ℕ):ℝ)+1)+δ :=
    hn.trans ((norm_add_le _ _).trans (add_le_add hmain herr))
  have hgram : (P*R).adjoint.comp (P*R)=R*P*R := by
    simp only [mul_def,adjoint_comp,hP.adjoint_eq,hR.adjoint_eq]
    apply ContinuousLinearMap.ext
    intro x
    have hh := DFunLike.congr_fun hPP (R x)
    change P (P (R x))=P (R x) at hh
    change R (P (P (R x)))=R (P (R x))
    rw [hh]
  have hnorm : ‖R*P‖=‖P*R‖ := by
    have heq : (P*R).adjoint=R*P := by
      simp only [mul_def,adjoint_comp,hP.adjoint_eq,hR.adjoint_eq]
    rw [←heq,adjoint.norm_map]
  have heq : (1-A^m)*P-P=-(R*P) := by dsimp only [R];noncomm_ring
  rw [heq,norm_neg,hnorm,pow_two,←norm_adjoint_comp_self,hgram]
  exact hbound

#print axioms power_source_projection_error
end QuantitativeMaass
