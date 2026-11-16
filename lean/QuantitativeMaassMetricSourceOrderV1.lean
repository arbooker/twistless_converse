module

public import QuantitativeMaassPowerSourceApproximationV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
open ContinuousLinearMap
namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded right factor controls the orthogonal range projection by
the actual cogram. The bound is quantitative and allows a proper range. -/
theorem projection_le_cogram_of_factorization (Q J K : H→L[ℂ]H)
    (hQ : IsSelfAdjoint Q) (hQQ : Q*Q=Q) (hfac : Q=J*K)
    {C : ℝ} (hK : ‖K‖≤C) : Q≤C^2 • (J*J.adjoint) := by
  have hC : 0≤C := (norm_nonneg K).trans hK
  have hkk : 0≤K*K.adjoint := by
    simpa only [adjoint_adjoint,mul_def] using
      nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self K.adjoint)
  have hn : ‖K*K.adjoint‖≤C^2 := by
    have hh := norm_mul_le K K.adjoint
    rw [adjoint.norm_map] at hh
    exact hh.trans (by nlinarith [norm_nonneg K])
  have hbound : K*K.adjoint≤C^2 • (1:H→L[ℂ]H) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg C) hkk).mp hn
  have hh := star_left_conjugate_le_conjugate hbound J.adjoint
  change J.adjoint.adjoint*(K*K.adjoint)*J.adjoint≤
    J.adjoint.adjoint*(C^2 • (1:H→L[ℂ]H))*J.adjoint at hh
  rw [adjoint_adjoint] at hh
  have he : J*(K*K.adjoint)*J.adjoint=Q := by
    calc
      _ = (J*K)*(J*K).adjoint := by
        simp only [mul_def,adjoint_comp,comp_assoc]
      _ = Q*Q := by rw [←hfac,hQ.adjoint_eq]
      _ = Q := hQQ
  rw [he] at hh
  simpa only [mul_smul_comm,smul_mul_assoc,mul_one] using hh

/-- Positivity and approximate preservation imply an operator-order bound,
before taking any physical or regular trace. -/
theorem projection_le_of_approx_fixed (E F : H→L[ℂ]H)
    (hE : IsSelfAdjoint E) (hEE : E*E=E) (hEn : ‖E‖≤1)
    (hF : 0≤F) {δ : ℝ} (hδ : ‖F*E-E‖≤δ) :
    E≤F+(3*δ) • (1:H→L[ℂ]H) := by
  have hδ0 : 0≤δ := (norm_nonneg _).trans hδ
  have hFs := (nonneg_iff_isPositive.mp hF).isSelfAdjoint
  let D := F-(1-E)*F*(1-E)
  have ha : (F*E-E).adjoint=E*F-E := by
    simp only [map_sub,mul_def,adjoint_comp,hE.adjoint_eq,hFs.adjoint_eq]
  have hd : D-E=(F*E-E)+(F*E-E).adjoint-E*(F*E-E) := by
    rw [ha,mul_sub,hEE]
    dsimp only [D]
    noncomm_ring
  have hnorm : ‖D-E‖≤3*δ := by
    rw [hd]
    have hm : ‖E*(F*E-E)‖≤δ := (norm_mul_le _ _).trans
      ((mul_le_mul_of_nonneg_right hEn (norm_nonneg _)).trans
        (by simpa only [one_mul] using hδ))
    have haa : ‖(F*E-E).adjoint‖≤δ := by rw [adjoint.norm_map];exact hδ
    have hh := (norm_sub_le ((F*E-E)+(F*E-E).adjoint) (E*(F*E-E))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    linarith
  have hp : 0≤(1-E)*F*(1-E) := by
    have hh := (nonneg_iff_isPositive.mp hF).adjoint_conj (1-E)
    have hs : (1-E).adjoint=1-E := by rw [map_sub,adjoint_one,hE.adjoint_eq]
    simpa only [hs,←mul_def,mul_assoc] using nonneg_iff_isPositive.mpr hh
  have hD : IsSelfAdjoint D := hFs.sub (nonneg_iff_isPositive.mp hp).isSelfAdjoint
  have he := (hE.sub hD).le_algebraMap_norm_self (E-D)
  have hn : ‖E-D‖≤3*δ := by rw [norm_sub_rev];exact hnorm
  have hs : algebraMap ℝ (H→L[ℂ]H) ‖E-D‖≤(3*δ) • (1:H→L[ℂ]H) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      smul_le_smul_of_nonneg_right hn (zero_le_one : (0:H→L[ℂ]H)≤1)
  have heD : E≤D+(3*δ) • (1:H→L[ℂ]H) := by
    simpa only [add_comm] using (sub_le_iff_le_add).mp (he.trans hs)
  exact heD.trans (add_le_add (sub_le_self F hp) le_rfl)

#print axioms projection_le_cogram_of_factorization
#print axioms projection_le_of_approx_fixed
end QuantitativeMaass
