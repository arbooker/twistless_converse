module

public import QuantitativeMaassHilbertSchmidtIdealV1
public import QuantitativeEulerEndpointActualCommonFilterV1
public import AsymptoticDiagonalTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointApproximateTrace
open ContinuousLinearMap InnerProductSpace AsymptoticDiagonalTrace
open scoped InnerProduct
variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem sqrt_energy (T : H →L[ℂ] H) (hT : 0≤T) (v : H) :
    ‖CFC.sqrt T v‖^2=(⟪T v,v⟫_ℂ).re := by
  have hs : (CFC.sqrt T).adjoint*(CFC.sqrt T)=T := by
    rw [show (CFC.sqrt T).adjoint= CFC.sqrt T from
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)).star_eq,CFC.sqrt_mul_sqrt_self T hT]
  rw [norm_sq_eq_re_inner (𝕜:=ℂ)]
  rw [←(CFC.sqrt T).adjoint_inner_left]
  change (⟪((CFC.sqrt T).adjoint*CFC.sqrt T) v,v⟫_ℂ).re=_
  rw [hs]

/-- A finite orthonormal diagonal is bounded by the full summable positive trace. -/
theorem finite_diagonal_le_trace [Fintype κ] (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (hT : 0≤T) (v : κ → H) (hv : Orthonormal ℂ v)
    (hs : Summable (fun i => (⟪T (b i),b i⟫_ℂ).re)) :
    (∑ j,(⟪T (v j),v j⟫_ℂ).re)≤trace b T := by
  have hh := QuantitativeMaass.finite_orthonormal_energy_le b v hv (CFC.sqrt T)
    (by simpa only [sqrt_energy T hT] using hs)
  simpa only [QuantitativeMaass.hilbertSchmidtEnergy,sqrt_energy T hT,trace] using hh

/-- Approximate fixed vectors give a linear, rather than square-root, loss
in the dimension estimate. No trace domination is assumed. -/
theorem finrank_mul_le_trace (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (hT : 0≤T)
    (W : Submodule ℂ H) [FiniteDimensional ℂ W] (δ : ℝ)
    (herr : ∀ w∈W,‖T w-w‖≤δ*‖w‖)
    (hs : Summable (fun i => (⟪T (b i),b i⟫_ℂ).re)) :
    (1-δ)*(Module.finrank ℂ W:ℝ)≤trace b T := by
  classical
  let u := stdOrthonormalBasis ℂ W
  have hu : Orthonormal ℂ (fun j => (u j:H)) := W.subtypeₗᵢ.orthonormal_comp_iff.mpr u.orthonormal
  have hl (j) : 1-δ≤(⟪T (u j:H),(u j:H)⟫_ℂ).re := by
    have hn : ‖(u j:H)‖=1 := hu.norm_eq_one j
    have he := herr (u j:H) (u j).property
    rw [hn,mul_one] at he
    have hi := re_inner_le_norm (𝕜:=ℂ) ((u j:H)-T (u j:H)) (u j:H)
    rw [inner_sub_left,map_sub,inner_self_eq_norm_sq,hn,norm_sub_rev,mul_one] at hi
    norm_num at hi
    linarith
  have hsum := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hl j)
  have ht := finite_diagonal_le_trace b T hT (fun j => (u j:H)) hu hs
  have hh := hsum.trans ht
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hh

#print axioms sqrt_energy
#print axioms finite_diagonal_le_trace
#print axioms finrank_mul_le_trace
end QuantitativeEulerEndpointApproximateTrace
