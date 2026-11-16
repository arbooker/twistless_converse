module

public import QuantitativeMaassOldBandPairingV1
public import QuantitativeMaassLowRankFilterV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Module QuantitativeNinaMaass QuantitativeArithmeticMaassExceptionalBands
open QuantitativeArithmeticExceptionalOldSpace QuantitativeArithmeticExceptionalMoments

namespace QuantitativeMaass

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


/-- The exact physical Gram relations on complete cusp parity bands. -/
theorem oldBand_pairedGram {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (u v : ℤ) (huv : (p:ℤ)*u+(M:ℤ)*v=1)
    (a b σ : ℝ) :
    PairedGram (oldBandInclusion S p T a b σ) (oldBandFrickeInclusion S p T a b σ)
      (oldBandTrace S p T a b σ) (oldBandFrickeTrace S p T a b σ)
      (normalizedBandHecke S p a b σ) := by
  refine ⟨oldBandTrace_inclusion S p T hpM u v huv a b σ,
    oldBandFrickeTrace_inclusion S p T hpM u v huv a b σ,
    oldBand_cross_hecke S p T a b σ, ?_⟩
  exact paired_adjoint_cross _ _ _ _ _ (((p:ℝ)+1)⁻¹)
    (oldBandTrace_pairing S p T a b σ) (oldBandFrickeTrace_pairing S p T a b σ)
    (normalizedBandHecke_symmetric S p hpM u v huv a b σ)
    (oldBand_cross_hecke S p T a b σ)

/-- Both old-space projections are symmetric idempotents on the actual
finite spectral band. -/
theorem oldBand_projections {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (u v : ℤ) (huv : (p:ℤ)*u+(M:ℤ)*v=1)
    (a b σ : ℝ) :
    ((oldBandInclusion S p T a b σ).comp (oldBandTrace S p T a b σ)).IsSymmetric ∧
    IsIdempotentElem ((oldBandInclusion S p T a b σ).comp (oldBandTrace S p T a b σ)) ∧
    ((oldBandFrickeInclusion S p T a b σ).comp (oldBandFrickeTrace S p T a b σ)).IsSymmetric ∧
    IsIdempotentElem ((oldBandFrickeInclusion S p T a b σ).comp (oldBandFrickeTrace S p T a b σ)) := by
  have hr : ((p:ℝ)+1)⁻¹≠0 := by positivity
  have hA := paired_adjoint_projection _ _ _ hr (oldBandTrace_pairing S p T a b σ)
    (oldBandTrace_inclusion S p T hpM u v huv a b σ)
  have hB := paired_adjoint_projection _ _ _ hr (oldBandFrickeTrace_pairing S p T a b σ)
    (oldBandFrickeTrace_inclusion S p T hpM u v huv a b σ)
  exact ⟨hA.1,hA.2,hB.1,hB.2⟩

/-- Small positive old-spectrum rank is bounded by twice the exceptional
Hecke rank on the lower level. All maps are the physical cover/trace maps. -/
theorem oldBand_smallPositive_rank {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (u v : ℤ) (huv : (p:ℤ)*u+(M:ℤ)*v=1)
    (a b σ : ℝ) (η : ℝ) :
    finrank ℂ (smallPositiveSpace
      ((oldBand_projections S p T hpM u v huv a b σ).1.add
        (oldBand_projections S p T hpM u v huv a b σ).2.2.1) (1-η)) ≤
      2*finrank ℂ (exceptionalSpace (normalizedBandHecke_symmetric S p hpM u v huv a b σ) η) := by
  exact smallPositiveSpace_finrank _ _ _ _
    (normalizedBandHecke_symmetric S p hpM u v huv a b σ)
    (oldBand_pairedGram S p T hpM u v huv a b σ) _ η

#print axioms oldBand_pairedGram
#print axioms oldBand_projections
#print axioms oldBand_smallPositive_rank

end QuantitativeMaass
