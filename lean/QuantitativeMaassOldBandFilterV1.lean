module

public import QuantitativeMaassOldBandGramV1

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



/-- The sum of the two physical old projections on the fixed parity band. -/
def oldBandSum {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (a b σ : ℝ) : T.parityBand a b σ →ₗ[ℂ] T.parityBand a b σ :=
  (oldBandInclusion S p T a b σ).comp (oldBandTrace S p T a b σ)+
    (oldBandFrickeInclusion S p T a b σ).comp (oldBandFrickeTrace S p T a b σ)

/-- Normalization and lower-level Fricke conjugation leave the two
physical trace kernels unchanged. -/
theorem oldBand_trace_kernel {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (a b σ : ℝ) :
    (oldBandTrace S p T a b σ).ker ⊓ (oldBandFrickeTrace S p T a b σ).ker =
      S.traceNewParityBand T (Nat.dvd_mul_left M p) a b σ := by
  have hr : ((((p:ℝ)+1)⁻¹:ℝ):ℂ)≠0 := by
    exact_mod_cast (show ((p:ℝ)+1)⁻¹≠0 by positivity)
  have hz (y : T.parityBand a b σ) : oldBandTrace S p T a b σ y=0 ↔
      S.traceParityBandMap T (Nat.dvd_mul_left M p) a b σ y=0 := by
    change ((((p:ℝ)+1)⁻¹:ℝ):ℂ) • (S.traceParityBandMap T (Nat.dvd_mul_left M p) a b σ y)=0 ↔ _
    simp only [smul_eq_zero,hr,false_or]
  have hf (y : S.parityBand a b σ) : S.frickeParityBandMap a b σ y=0 ↔ y=0 := by
    constructor
    · intro h
      apply (S.frickeParityBandMap_involutive a b σ).injective
      simpa only [map_zero] using h
    · intro h
      rw [h,map_zero]
  ext x
  change (oldBandTrace S p T a b σ x=0 ∧
    S.frickeParityBandMap a b σ (oldBandTrace S p T a b σ (T.frickeParityBandMap a b σ x))=0) ↔
    (S.traceParityBandMap T (Nat.dvd_mul_left M p) a b σ x=0 ∧
      S.traceParityBandMap T (Nat.dvd_mul_left M p) a b σ (T.frickeParityBandMap a b σ x)=0)
  rw [hf,hz,hz]

theorem oldBandSum_symmetric {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (u v : ℤ) (huv : (p:ℤ)*u+(M:ℤ)*v=1)
    (a b σ : ℝ) : (oldBandSum S p T a b σ).IsSymmetric :=
  (oldBand_projections S p T hpM u v huv a b σ).1.add
    (oldBand_projections S p T hpM u v huv a b σ).2.2.1

/-- The exact null space of the old sum is the actual local new band. -/
theorem oldBandSum_kernel {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (u v : ℤ) (huv : (p:ℤ)*u+(M:ℤ)*v=1)
    (a b σ : ℝ) :
    (oldBandSum S p T a b σ).ker=S.traceNewParityBand T (Nat.dvd_mul_left M p) a b σ := by
  obtain ⟨hA,hAA,hB,hBB⟩ := oldBand_projections S p T hpM u v huv a b σ
  unfold oldBandSum
  rw [two_projection_kernel _ _ hA hB hAA hBB,
    paired_projection_kernel _ _ (oldBandTrace_inclusion S p T hpM u v huv a b σ),
    paired_projection_kernel _ _ (oldBandFrickeTrace_inclusion S p T hpM u v huv a b σ),
    oldBand_trace_kernel]

/-- The physical polynomial filter has an explicit trace error controlled
by the lower-level exceptional Hecke rank and geometric decay. -/
theorem oldBand_filter_trace {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (u v : ℤ) (huv : (p:ℤ)*u+(M:ℤ)*v=1)
    (a b σ : ℝ) (η : ℝ) (hη0 : 0≤η) (hη1 : η≤1) (m : ℕ) :
    (LinearMap.trace ℂ (T.parityBand a b σ) ((1-(1/2:ℂ) • oldBandSum S p T a b σ)^m)).re ≤
      (finrank ℂ (S.traceNewParityBand T (Nat.dvd_mul_left M p) a b σ):ℝ)+
      2*(finrank ℂ (exceptionalSpace (normalizedBandHecke_symmetric S p hpM u v huv a b σ) η):ℝ)+
      (1-(1-η)/2)^m*(finrank ℂ (T.parityBand a b σ):ℝ) := by
  obtain ⟨hA,hAA,hB,hBB⟩ := oldBand_projections S p T hpM u v huv a b σ
  have hh := half_low_rank_filter_trace (oldBandSum S p T a b σ)
    (oldBandSum_symmetric S p T hpM u v huv a b σ)
    (two_projection_spectrum_bounds _ _ hA hB hAA hBB) (1-η)
    (by linarith) (by linarith) m
  have hk := congrArg (fun U : Submodule ℂ (T.parityBand a b σ) => (finrank ℂ U : ℝ))
    (oldBandSum_kernel S p T hpM u v huv a b σ)
  have hr : (finrank ℂ (smallPositiveSpace
      (oldBandSum_symmetric S p T hpM u v huv a b σ) (1-η)):ℝ)≤
      2*(finrank ℂ (exceptionalSpace (normalizedBandHecke_symmetric S p hpM u v huv a b σ) η):ℝ) := by
    have hh := Nat.cast_le (α := ℝ).mpr (oldBand_smallPositive_rank S p T hpM u v huv a b σ η)
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh
  exact hh.trans (add_le_add (add_le_add hk.le hr) le_rfl)

#print axioms oldBand_trace_kernel
#print axioms oldBandSum_symmetric
#print axioms oldBandSum_kernel
#print axioms oldBand_filter_trace

end QuantitativeMaass
