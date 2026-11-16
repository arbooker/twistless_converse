module

public import QuantitativeArithmeticExceptionalMomentsV1
public import QuantitativeNinaMaassHeckeNewV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Module QuantitativeMaass QuantitativeNinaMaass
open QuantitativeArithmeticExceptionalMoments

namespace QuantitativeArithmeticMaassExceptionalBands

local instance (N : ℕ) (hN : 0 < N) :
    NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance

local instance (N : ℕ) (hN : 0 < N) :
    InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

local instance {N : ℕ} {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance

local instance {N : ℕ} {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance

/-- The normalized actual good-prime correspondence on the entire cusp
parity band. There is no newspace restriction or assumed spectral bound. -/
def normalizedBandHecke {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [Fact p.Prime]
    (a b σ : ℝ) : S.parityBand a b σ →ₗ[ℂ] S.parityBand a b σ :=
  ((Real.sqrt (p : ℝ) / ((p : ℝ)+1) : ℝ) : ℂ) •
    S.dilationTraceParityBandMap p (Fact.out : p.Prime).pos a b σ

theorem normalizedBandHecke_actual {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A B : ℤ) (hAB : (p : ℤ)*A+(N : ℤ)*B=1)
    (a b σ : ℝ) (v : S.parityBand a b σ) :
    ((normalizedBandHecke S p a b σ v).val.val : AutomorphicSpace N) =
      ((Real.sqrt (p : ℝ) / ((p : ℝ)+1) : ℝ) : ℂ) •
        HeckeL2.operator N p hN hpN A B hAB (v.val.val : AutomorphicSpace N) := by
  rw [hecke_eq_dilationTraceOperator]
  rfl

theorem normalizedBandHecke_symmetric {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A B : ℤ) (hAB : (p : ℤ)*A+(N : ℤ)*B=1)
    (a b σ : ℝ) : (normalizedBandHecke S p a b σ).IsSymmetric := by
  unfold normalizedBandHecke
  apply LinearMap.IsSymmetric.smul (by simp)
  intro v w
  change inner ℂ (dilationTraceOperator N p hN (Fact.out : p.Prime).pos
      (v.val.val : AutomorphicSpace N)) (w.val.val : AutomorphicSpace N) =
    inner ℂ (v.val.val : AutomorphicSpace N) (dilationTraceOperator N p hN
      (Fact.out : p.Prime).pos (w.val.val : AutomorphicSpace N))
  simp only [← hecke_eq_dilationTraceOperator N p hN hpN A B hAB]
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (HeckeL2.operator_selfAdjoint N p hN hpN A B hAB) _ _

/-- An actual exceptional Hecke-band moment bound. The right side is a
finite spectral trace; a geometric upper estimate for it is still needed. -/
theorem exceptional_band_moment {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A B : ℤ) (hAB : (p : ℤ)*A+(N : ℤ)*B=1)
    (a b σ η : ℝ) (hη : 0 ≤ η) (d : ℕ) :
    η^(2*d) * (finrank ℂ (exceptionalSpace
      (normalizedBandHecke_symmetric S p hpN A B hAB a b σ) η) : ℝ) ≤
      (LinearMap.trace ℂ (S.parityBand a b σ)
        ((normalizedBandHecke S p a b σ)^(2*d))).re :=
  exceptionalSpace_moment
    (normalizedBandHecke_symmetric S p hpN A B hAB a b σ) η hη d

/-- The two physical degeneracy images of any lower-level band subspace
have at most twice its dimension. This estimate has no angle denominator. -/
theorem old_band_two_image_rank {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0 < M} {hN : 0 < N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b σ : ℝ) (U : Submodule ℂ (S.parityBand a b σ)) :
    finrank ℂ ↥(U.map (S.coverParityBandMap T hMN a b σ) ⊔
      U.map ((T.frickeParityBandMap a b σ).comp (S.coverParityBandMap T hMN a b σ))) ≤
        2 * finrank ℂ U :=
  two_image_finrank U _ _

#print axioms normalizedBandHecke_actual
#print axioms normalizedBandHecke_symmetric
#print axioms exceptional_band_moment
#print axioms old_band_two_image_rank

end QuantitativeArithmeticMaassExceptionalBands
