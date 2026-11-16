module

public import QuantitativeArithmeticRepeatedTwoProjectorV1
public import QuantitativeNinaMaassOldBandsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
@[expose] public noncomputable section

open QuantitativeMaass QuantitativeNinaMaass
open QuantitativeArithmeticRepeatedTwoPhysical QuantitativeArithmeticRepeatedTwoProjector
open scoped InnerProductSpace

namespace QuantitativeArithmeticRepeatedTwoBands

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance

def inclusion {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    S.parityBand a b σ →ₗ[ℂ] AutomorphicSpace N :=
  (localCuspidalSpace N hN).subtype.comp
    ((S.band a b).subtype.comp (S.parityBand a b σ).subtype)

theorem power_intertwines {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (I : E →ₗ[ℂ] F)
    (A : Module.End ℂ E) (B : Module.End ℂ F)
    (h : ∀ x, I (A x)=B (I x)) (n : ℕ) (x : E) :
    I ((A^n) x)=(B^n) (I x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ,Module.End.mul_apply,ih,h,pow_succ,Module.End.mul_apply]

theorem twice_pos (L : ℕ) (hL : 0<L) : 0<2*L := by omega
theorem four_pos (L : ℕ) (hL : 0<L) : 0<2*(2*L) := by omega

variable (L : ℕ) (hL : 0<L) [NeZero (2*L)] [NeZero (2*(2*L))]
    (S : CuspEnergySpectrum (2*L) (twice_pos L hL))
    (T : CuspEnergySpectrum (2*(2*L)) (four_pos L hL)) (a b σ : ℝ)

def bandOrdinary : Module.End ℂ (T.parityBand a b σ) :=
  (S.coverParityBandMap T (Nat.dvd_mul_left (2*L) 2) a b σ).comp
    (S.traceParityBandMap T (Nat.dvd_mul_left (2*L) 2) a b σ) - 1

def bandSum : Module.End ℂ (T.parityBand a b σ) :=
  bandOrdinary L hL S T a b σ +
    (T.frickeParityBandMap a b σ) *
      (bandOrdinary L hL S T a b σ * T.frickeParityBandMap a b σ)

def bandProjector : Module.End ℂ (T.parityBand a b σ) :=
  (1/24:ℂ) • ((bandSum L hL S T a b σ)^4 -
    (2:ℂ) • (bandSum L hL S T a b σ)^3 - (bandSum L hL S T a b σ)^2 +
    (2:ℂ) • bandSum L hL S T a b σ)

theorem sum_intertwines (x : T.parityBand a b σ) :
    inclusion T a b σ (bandSum L hL S T a b σ x) =
      reflectionSum L hL (inclusion T a b σ x) := rfl

theorem projector_intertwines (x : T.parityBand a b σ) :
    inclusion T a b σ (bandProjector L hL S T a b σ x) =
      projector (reflectionSum L hL) (inclusion T a b σ x) := by
  have hp (n : ℕ) : inclusion T a b σ (((bandSum L hL S T a b σ)^n) x) =
      ((reflectionSum L hL)^n) (inclusion T a b σ x) := by
    simpa only [←ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.coe_coe] using
      power_intertwines (inclusion T a b σ) (bandSum L hL S T a b σ)
      (reflectionSum L hL).toLinearMap (sum_intertwines L hL S T a b σ) n x
  rw [projector_formula]
  simp only [bandProjector,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.sub_apply,
    map_smul,map_add,map_sub,hp,sum_intertwines,smul_apply,add_apply,sub_apply]

/-- The finite polynomial restricts to the exact orthogonal projection
onto Nina's two trace equations in every spectral/parity band. -/
theorem bandProjector_eq (x : T.parityBand a b σ) :
    bandProjector L hL S T a b σ x =
      (S.traceNewParityBand T (Nat.dvd_mul_left (2*L) 2) a b σ).starProjection x := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (S.mem_traceNewParityBand T (Nat.dvd_mul_left (2*L) 2) a b σ _).mpr
    rw [←physical_kernel L hL]
    change (reflectionSum L hL+2) (inclusion T a b σ (bandProjector L hL S T a b σ x))=0
    rw [projector_intertwines]
    exact DFunLike.congr_fun (projector_range _ (reflectionSum_annihilator L hL)) _
  · intro w hw
    have hw' := (S.mem_traceNewParityBand T (Nat.dvd_mul_left (2*L) 2) a b σ w).mp hw
    rw [←physical_kernel L hL] at hw'
    change inner ℂ (inclusion T a b σ x -
      inclusion T a b σ (bandProjector L hL S T a b σ x)) (inclusion T a b σ w)=0
    rw [projector_intertwines,physical_projector]
    exact Submodule.starProjection_inner_eq_zero _ _ hw'

#print axioms power_intertwines
#print axioms projector_intertwines
#print axioms bandProjector_eq

end QuantitativeArithmeticRepeatedTwoBands
