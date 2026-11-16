module

public import QuantitativeMaassTwoProjectionApproximationV1
public import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
open ContinuousLinearMap
namespace QuantitativeMaass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The coercive estimate gives a geometric operator-norm bound at every
degree, suitable for finite products of local filters. -/
theorem two_projection_operator_approximation (P Q : E→L[ℂ]E)
    (hP : P.toLinearMap.IsSymmetric) (hQ : Q.toLinearMap.IsSymmetric)
    (hPP : IsIdempotentElem P) (hQQ : IsIdempotentElem Q)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hU : ∀ w∈U,P w=0 ∧ Q w=0) (γ : ℝ) (hγ : γ≤2)
    (hgap : ∀ v,γ*‖v-U.starProjection v‖^2≤‖P v‖^2+‖Q v‖^2) (m : ℕ) :
    ‖(1-(1/2:ℂ) • (P+Q))^m-U.starProjection‖ ≤ (Real.sqrt (1-γ/2))^m := by
  have hρ : 0≤1-γ/2 := by linarith
  have hρm : 0≤(Real.sqrt (1-γ/2))^m := pow_nonneg (Real.sqrt_nonneg _) _
  apply opNorm_le_bound _ hρm
  intro v
  have hpp : IsIdempotentElem P.toLinearMap := by
    apply LinearMap.ext; intro x; exact DFunLike.congr_fun hPP x
  have hqq : IsIdempotentElem Q.toLinearMap := by
    apply LinearMap.ext; intro x; exact DFunLike.congr_fun hQQ x
  have hh := two_projection_power_approximation P.toLinearMap Q.toLinearMap
    hP hQ hpp hqq U hU γ hγ hgap m v
  have hT : 1-(1/2:ℂ) • (P.toLinearMap+Q.toLinearMap)=
      (1-(1/2:ℂ) • (P+Q)).toLinearMap := rfl
  rw [hT,←toLinearMap_pow] at hh
  change ‖((1-(1/2:ℂ) • (P+Q))^m-U.starProjection) v‖^2 ≤
    (1-γ/2)^m*‖v-U.starProjection v‖^2 at hh
  have hr : ‖v-U.starProjection v‖≤‖v‖ := by
    rw [←U.starProjection_orthogonal_val v]
    exact Uᗮ.norm_starProjection_apply_le v
  have hrs := pow_le_pow_left₀ (norm_nonneg _) hr 2
  have hb := hh.trans (mul_le_mul_of_nonneg_left hrs (pow_nonneg hρ _))
  have he : (1-γ/2)^m=((Real.sqrt (1-γ/2))^m)^2 := by
    calc
      _ = ((Real.sqrt (1-γ/2))^2)^m := by rw [Real.sq_sqrt hρ]
      _ = _ := by rw [←pow_mul,←pow_mul,Nat.mul_comm]

  rw [he] at hb
  have hpos := mul_nonneg hρm (norm_nonneg v)
  nlinarith only [hb,hpos,norm_nonneg (((1-(1/2:ℂ) • (P+Q))^m-U.starProjection) v)]

#print axioms two_projection_operator_approximation
end QuantitativeMaass
