module

public import QuantitativeEulerEndpointInitialFiniteExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointInitialExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointWeightedExpression
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

theorem piLp_inverse_norm_ge_one {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (i : ι) (v : E) (hv : ‖v‖=1) :
    1≤‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => E)).symm.toContinuousLinearMap‖ := by
  let T := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => E)).symm.toContinuousLinearMap
  have h := T.le_opNorm (Pi.single i v)
  have he : T (Pi.single i v)=PiLp.single 2 i v := rfl
  rw [he,PiLp.norm_single,Pi.norm_single,hv,mul_one] at h
  exact h

theorem baseline_stack_norm_ge_one (N : ℕ) :
    1≤‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : NewBaselineIndex N => Space)).symm.toContinuousLinearMap‖ :=
  piLp_inverse_norm_ge_one (.inl none)
    (AsymptoticRegularTrace.delta (1:AsymptoticRationalGroup.Group)) AsymptoticOrbitDiagonal.root_delta_norm

theorem row_squares_le_detector (N : ℕ) [NeZero N] (sector : Sector N)
    (R Y H : ℝ) (t : ℕ) :
    (∑ j,(wideBaselineRowBound N sector R Y H t j)^2)≤(wideDetectorBound N sector R Y H t)^2 := by
  have hn := wideBaselineRowBound_nonneg N sector R Y H t
  have hs : 0≤∑ j,wideBaselineRowBound N sector R Y H t j := Finset.sum_nonneg (fun j _ => hn j)
  have hsum : (∑ j,wideBaselineRowBound N sector R Y H t j)≤wideDetectorBound N sector R Y H t := by
    unfold wideDetectorBound
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (baseline_stack_norm_ge_one N) hs
  exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => hn j)).trans (pow_le_pow_left₀ hs hsum 2)

theorem normalized_initial_mass_le_one (N : ℕ) [NeZero N] (sector : Sector N)
    {ι : Type*} [Fintype ι] (t : ι → ℕ) (R Y H a : ι → ℝ) (ha : ∀ i,0<a i)
    (u : Expression) (hu : expressionBound u≤1) (E : ι → NewBaselineIndex N → Expression)
    (hE : ∀ i j,expressionBound (E i j)≤wideBaselineRowBound N sector (R i) (Y i) (H i) (t i) j) :
    expressionBound (weightedGram u E (fun i => (a i)⁻¹)
      (QuantitativeEulerEndpointInitialWeighted.cap
        (fun i => wideDetectorBound N sector (R i) (Y i) (H i) (t i)) a)⁻¹)≤1 := by
  let C := fun i => wideDetectorBound N sector (R i) (Y i) (H i) (t i)
  let M := QuantitativeEulerEndpointInitialWeighted.cap C a
  have hM : 0<M := QuantitativeEulerEndpointInitialWeighted.cap_pos C a ha
  have hm := weighted_mass_le (inv_nonneg.mpr hM.le) (fun i => inv_nonneg.mpr (ha i).le) hu
    (fun i j => wideBaselineRowBound N sector (R i) (Y i) (H i) (t i) j) hE
  have hs : (∑ i,(a i)⁻¹*(∑ j,(wideBaselineRowBound N sector (R i) (Y i) (H i) (t i) j)^2))≤M := by
    calc
      _ ≤ ∑ i,(a i)⁻¹*(C i)^2 := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (row_squares_le_detector N sector (R i) (Y i) (H i) (t i))
          (inv_nonneg.mpr (ha i).le))
      _ ≤ _ := by unfold M QuantitativeEulerEndpointInitialWeighted.cap; linarith
  exact hm.trans ((mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hM.le)).trans_eq (inv_mul_cancel₀ hM.ne'))

#print axioms baseline_stack_norm_ge_one
#print axioms row_squares_le_detector
#print axioms normalized_initial_mass_le_one
end QuantitativeEulerEndpointInitialExpression
