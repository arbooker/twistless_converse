module

public import QuantitativeMaassCountingTotalApproximationV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter ContinuousLinearMap AsymptoticSectorSigns QuantitativeNewGap
open scoped Topology
namespace QuantitativeMaass.Counting

theorem sectorNewFilter_norm_bound (N : ℕ) [NeZero N] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (e : Sector N) (m : ℕ) :
    ‖sectorNewFilter N hN e m‖≤(2:ℝ)^((Finset.univ : Finset ↥N.primeFactors).toList.length) := by
  have ht := bounded_clm_list_product (Finset.univ : Finset ↥N.primeFactors).toList
    (localNewFilter N hN m) 2 (by norm_num) (localNewFilter_norm_two N hN hAd m)
  change ‖totalNewFilter N hN m‖≤_ at ht
  change ‖(totalNewFilter N hN m).comp (signProduct N hN e)‖≤_
  exact (opNorm_comp_le _ _).trans (by
    simpa only [mul_one] using mul_le_mul ht (signProduct_norm N hN e)
      (norm_nonneg _) (by positivity : 0≤(2:ℝ)^((Finset.univ : Finset ↥N.primeFactors).toList.length)))

theorem sectorNewFilter_weighted_limit (N : ℕ) [NeZero N] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (e : Sector N)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      ‖sectorNewFilter N hN e (growingLVDegree t)-(countingSectorSpace N hN e).starProjection‖/ε t)
      atTop (𝓝 0) := by
  apply squeeze_zero' (hε.mono (fun t ht => div_nonneg
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) ht.le)) _
    (totalNewFilter_weighted_limit N hN hAd ε hε hp W)
  filter_upwards [hε] with t ht
  apply div_le_div_of_nonneg_right _ ht.le
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [sectorNewFilter,countingSector_projection,←sub_comp]
  exact (opNorm_comp_le _ _).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (signProduct_norm N hN e) (norm_nonneg _))

/-- Uniformly bounded filters transfer operator approximation to their
Gram operators; the limiting operator is an orthogonal projection. -/
theorem gram_projection_error {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (F P : H→L[ℂ]H)
    (hP : IsSelfAdjoint P) (hPP : IsIdempotentElem P) (hPn : ‖P‖≤1)
    (C : ℝ) (hF : ‖F‖≤C) :
    ‖F.adjoint.comp F-P‖≤(C+1)*‖F-P‖ := by
  have he : F.adjoint.comp F-P=(F-P).adjoint.comp F+P.comp (F-P) := by
    rw [map_sub,sub_comp,comp_sub,hP.adjoint_eq,show P.comp P=P from hPP]
    abel
  rw [he]
  calc
    _ ≤ ‖(F-P).adjoint.comp F‖+‖P.comp (F-P)‖ := norm_add_le _ _
    _ ≤ ‖(F-P).adjoint‖*‖F‖+‖P‖*‖F-P‖ := add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)
    _ = ‖F-P‖*‖F‖+‖P‖*‖F-P‖ := by rw [adjoint.norm_map]
    _ ≤ ‖F-P‖*C+1*‖F-P‖ := add_le_add
      (mul_le_mul_of_nonneg_left hF (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hPn (norm_nonneg _))
    _ = _ := by ring

theorem sectorGram_weighted_limit (N : ℕ) [NeZero N] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (e : Sector N)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      ‖(sectorNewFilter N hN e (growingLVDegree t)).adjoint.comp
          (sectorNewFilter N hN e (growingLVDegree t))-
        (countingSectorSpace N hN e).starProjection‖/ε t) atTop (𝓝 0) := by
  let C := (2:ℝ)^((Finset.univ : Finset ↥N.primeFactors).toList.length)
  have hl := (sectorNewFilter_weighted_limit N hN hAd e ε hε hp W).const_mul (C+1)
  rw [mul_zero] at hl
  apply squeeze_zero' (hε.mono (fun t ht => div_nonneg
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) ht.le)) _ hl
  filter_upwards [hε] with t ht
  have hb := gram_projection_error (sectorNewFilter N hN e (growingLVDegree t))
    (countingSectorSpace N hN e).starProjection (isSelfAdjoint_starProjection _)
    (Submodule.isIdempotentElem_starProjection _) (Submodule.starProjection_norm_le _) C
    (sectorNewFilter_norm_bound N hN hAd e _)
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le) ht.le).trans_eq
    (by ring)

#print axioms sectorNewFilter_norm_bound
#print axioms sectorNewFilter_weighted_limit
#print axioms gram_projection_error
#print axioms sectorGram_weighted_limit
end QuantitativeMaass.Counting
