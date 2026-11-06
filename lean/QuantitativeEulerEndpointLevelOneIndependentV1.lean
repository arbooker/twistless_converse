module

public import QuantitativeEulerEndpointLevelOneCuspV1
public import AsymptoticClassicalFiniteDimensionV1
public import FinitenessOriginalTheoremV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointLevelOne
open UpperHalfPlane Filter Complex
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped ModularForm MatrixGroups Manifold Topology

theorem solutionCusp_independent (m : ℕ) : LinearIndependent ℂ (solutionCusp m) := by
  have hi := FinitenessOriginalDiskIndependence.normalized_independent 1 (2*m)
  rw [linearIndependent_iff'] at hi ⊢
  intro s c hc
  apply hi s c
  apply FinitenessSeriesIndependence.relation
    (fun f : FinitenessOriginalInput.S 1 (2*m) => fullCoefficients f.val (2*m))
    (FinitenessOriginalDiskIndependence.polynomial 1 (2*m)) c s
  intro w hw
  have hwn : ‖w‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hw
  by_cases hw0 : w=0
  · subst w
    apply Finset.sum_eq_zero
    intro f _
    rw [FinitenessPolynomialSeries.zero (fullCoefficients_zero f.property.zero (2*m)),mul_zero]
  · have hz : 0<(Function.Periodic.invQParam 1 w).im := by
      rw [Function.Periodic.im_invQParam]
      exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (by norm_num) (by positivity))
        (Real.log_neg (norm_pos_iff.mpr hw0) hwn)
    let z : ℍ := ⟨Function.Periodic.invQParam 1 w,hz⟩
    have he := DFunLike.congr_fun hc z
    simp only [sum_apply,smul_apply,smul_eq_mul,zero_apply] at he
    change ∑ f∈s,c f*fourier (fullCoefficients f.val (2*m)) (Function.Periodic.invQParam 1 w)=0 at he
    simpa only [FinitenessFourierConstruction.fourier,Function.Periodic.qParam_right_inv (by norm_num : (1:ℝ)≠0) hw0] using he

theorem original_count_le_cusp_dimension (m : ℕ) (hm : 0<m) :
    (FinitenessOriginalInput.S 1 (2*m)).ncard≤Module.finrank ℂ (CuspForm 𝒮ℒ ((2*m : ℕ) : ℤ)) := by
  obtain ⟨C,_hC,hfin⟩ := FinitenessOriginalTheorem.admissible_level 1 (by norm_num)
    (by norm_num) (by intro p hp _h; exact fun hd => hp.not_dvd_one (dvd_trans (dvd_pow_self p (by decide : 2≠0)) hd))
  let := (hfin m hm).1.fintype
  let : Module.Finite ℂ (ModularForm 𝒮ℒ ((2*m : ℕ) : ℤ)) :=
    AsymptoticClassicalNorm.finiteDimensional one_mem_strictPeriods_SL _ le_rfl
  let : Module.Finite ℂ (CuspForm 𝒮ℒ ((2*m : ℕ) : ℤ)) :=
    Module.Finite.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective
  have hh := (solutionCusp_independent m).fintype_card_le_finrank
  simpa only [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hh

#print axioms solutionCusp_independent
#print axioms original_count_le_cusp_dimension
end QuantitativeEulerEndpointLevelOne
