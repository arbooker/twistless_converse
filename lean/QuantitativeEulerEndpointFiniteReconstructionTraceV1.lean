module

public import QuantitativeEulerEndpointActualTraceAssemblyV1
public import QuantitativeHolomorphicGrowingApproximationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointReconstructionTrace
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation AsymptoticDiagonalTrace
open QuantitativeHolomorphic InnerProductSpace
open scoped InnerProduct
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Change only reconstruction around an arbitrary contraction. The actual
nested filter is held fixed, so no iteration-depth loss occurs here. -/
theorem finite_reconstruction_trace_error (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (F : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε →L[ℂ]
      AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (hF : ‖F‖≤1) (Y : ℝ) (hY : 0≤Y) (j J n : ℕ) (hJ : 0<J)
    (hD : 0<countFilterError A P Y j J n 0) (hD1 : countFilterError A P Y j J n 0≤1) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let W := holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    let fb := fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos
    let U := normalizedCountReconstruction A hN P h e
    let V := polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n
    ‖trace fb (compressedSandwich V F W)-trace fb (compressedSandwich U F W)‖/(4*h+2:ℝ)≤
      (2+2*Sharp.countFilterMajorant A P n*majorantConstant (P'.s+4) (4*Real.pi) P'.ε)*
        Real.sqrt (countFilterError A P Y j J n 0) := by
  intro P' W fb U V
  have hU : ‖U‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    rw [normalizedCountReconstruction_norm,one_mul]
  have hV : ‖V‖≤1 := polynomialNormalizedReconstruction_norm_le _
    (scaledCutFiniteCountReconstruction_norm_le A hN P h e Y j J) n
  have herr : ‖V-U‖≤normalizedCutError A P Y j J n :=
    cut_normalizedCountReconstruction_closed_error A hN P h n e Y hY j J hJ
  have hC : 0≤Sharp.countFilterMajorant A P n := (sq_nonneg _).trans (le_max_left _ _)
  have hbU (l : ℕ) : ‖(⟪compressedSandwich U F W (fb l),fb l⟫_ℂ).re‖≤
      Sharp.countFilterMajorant A P n*modeRatio (2*h) (P'.s+4) (4*Real.pi) P'.ε (l+1) := by
    apply (compressedSandwich_diagonal_bound U F W (fb l)).trans
    apply (mul_le_mul_of_nonneg_right hF (sq_nonneg _)).trans
    rw [one_mul]
    exact (normalizedCountReconstruction_fourier_gram A hN P h e l).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (modeRatio_nonneg _ _ _ _ P'.epsilon_pos))
  have hbV (l : ℕ) : ‖(⟪compressedSandwich V F W (fb l),fb l⟫_ℂ).re‖≤
      Sharp.countFilterMajorant A P n*modeRatio (2*h) (P'.s+4) (4*Real.pi) P'.ε (l+1) := by
    apply (compressedSandwich_diagonal_bound V F W (fb l)).trans
    apply (mul_le_mul_of_nonneg_right hF (sq_nonneg _)).trans
    rw [one_mul]
    exact (Sharp.finiteCountReconstruction_fourier_gram A hN P h e Y j J n l).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (modeRatio_nonneg _ _ _ _ P'.epsilon_pos))
  have hd : ‖compressedSandwich V F W-compressedSandwich U F W‖≤countFilterError A P Y j J n 0 := by
    apply (orthogonalCompression_sub_norm_le W _ _).trans
    have hh := sandwich_sub_norm_le V U F F hF hF
    simp only [sub_self,norm_zero,mul_zero,add_zero] at hh
    apply hh.trans
    have hh' := mul_le_mul (show ‖V‖+‖U‖≤2 by linarith) herr (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
    simpa only [countFilterError,Nat.cast_zero,mul_zero,zero_add] using hh'
  have ht := normalized_trace_sub_le_sqrt_of_absolute_majorants fb _ _ (2*h) (P'.s+4)
    (by positivity : 0<4*Real.pi) P'.epsilon_pos hC hD hD1 hd hbV hbU
  convert ht using 1
  push_cast
  ring

#print axioms finite_reconstruction_trace_error
end QuantitativeEulerEndpointReconstructionTrace
