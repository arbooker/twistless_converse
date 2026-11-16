module

public import QuantitativeArithmeticMaassExceptionalBandsV1
public import QuantitativeMaassPairedAdjointsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Module QuantitativeNinaMaass QuantitativeArithmeticMaassExceptionalBands
open QuantitativeArithmeticExceptionalOldSpace
open scoped InnerProductSpace

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


/-- The ordinary physical inclusion and its trace divided by the covering degree. -/
def oldBandInclusion {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (a b σ : ℝ) := S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ

def oldBandTrace {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (a b σ : ℝ) :=
  ((((p:ℝ)+1)⁻¹:ℝ):ℂ) • S.traceParityBandMap T (Nat.dvd_mul_left M p) a b σ

/-- Conjugating on both levels makes the cross Gram map the normalized
Hecke operator, without an extra lower-level Fricke factor. -/
def oldBandFrickeInclusion {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (a b σ : ℝ) :=
  (T.frickeParityBandMap a b σ).comp
    ((oldBandInclusion S p T a b σ).comp (S.frickeParityBandMap a b σ))

def oldBandFrickeTrace {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (a b σ : ℝ) :=
  (S.frickeParityBandMap a b σ).comp
    ((oldBandTrace S p T a b σ).comp (T.frickeParityBandMap a b σ))

theorem oldBandTrace_pairing {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (a b σ : ℝ) (x : S.parityBand a b σ) (y : T.parityBand a b σ) :
    inner ℂ x (oldBandTrace S p T a b σ y)=
      ((((p:ℝ)+1)⁻¹:ℝ):ℂ)*inner ℂ (oldBandInclusion S p T a b σ x) y := by
  change inner ℂ (x.val.val : AutomorphicSpace M)
      (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • levelTrace (Nat.dvd_mul_left M p)
        (y.val.val : AutomorphicSpace (p*M))) = _
  exact (inner_smul_right (𝕜 := ℂ) (x.val.val : AutomorphicSpace M)
    (levelTrace (Nat.dvd_mul_left M p) (y.val.val : AutomorphicSpace (p*M)))
    ((((p:ℝ)+1)⁻¹:ℝ):ℂ)).trans
      (congrArg (fun z : ℂ => ((((p:ℝ)+1)⁻¹:ℝ):ℂ)*z)
        (ContinuousLinearMap.adjoint_inner_right (levelCover (Nat.dvd_mul_left M p))
          (x.val.val : AutomorphicSpace M) (y.val.val : AutomorphicSpace (p*M))))

theorem frickeParityBandMap_symmetric {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (a b σ : ℝ) :
    (S.frickeParityBandMap a b σ).IsSymmetric := by
  intro x y
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (frickeIsometry_selfAdjoint M hM) (x.val.val : AutomorphicSpace M)
      (y.val.val : AutomorphicSpace M)

theorem oldBandFrickeTrace_pairing {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (a b σ : ℝ) (x : S.parityBand a b σ) (y : T.parityBand a b σ) :
    inner ℂ x (oldBandFrickeTrace S p T a b σ y)=
      ((((p:ℝ)+1)⁻¹:ℝ):ℂ)*inner ℂ (oldBandFrickeInclusion S p T a b σ x) y := by
  change inner ℂ x (S.frickeParityBandMap a b σ
      (oldBandTrace S p T a b σ (T.frickeParityBandMap a b σ y))) = _
  rw [←frickeParityBandMap_symmetric S a b σ,oldBandTrace_pairing]
  rw [←frickeParityBandMap_symmetric T a b σ]
  rfl

theorem oldBandTrace_inclusion {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (u v : ℤ) (huv : (p:ℤ)*u+(M:ℤ)*v=1)
    (a b σ : ℝ) (x : S.parityBand a b σ) :
    oldBandTrace S p T a b σ (oldBandInclusion S p T a b σ x)=x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change ((((p:ℝ)+1)⁻¹:ℝ):ℂ) • levelTrace (Nat.dvd_mul_left M p)
      (levelCover (Nat.dvd_mul_left M p) (x.val.val : AutomorphicSpace M)) = _
  rw [levelTrace_cover]
  have hi := HeckeL2.cover_index M p hM hpM u v huv
  change Nat.card (AsymptoticCongruenceStrip.gamma M ⧸
      (AsymptoticCongruenceStrip.gamma (p*M)).subgroupOf (AsymptoticCongruenceStrip.gamma M))=p+1 at hi
  rw [hi,smul_smul]
  have hn : (p:ℝ)+1≠0 := by positivity
  have hnC : (p:ℂ)+1≠0 := by exact_mod_cast hn
  simp only [Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,Nat.cast_add,Nat.cast_one,inv_mul_cancel₀ hnC,one_smul]

theorem oldBandFrickeTrace_inclusion {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (hpM : ¬p∣M) (u v : ℤ) (huv : (p:ℤ)*u+(M:ℤ)*v=1)
    (a b σ : ℝ) (x : S.parityBand a b σ) :
    oldBandFrickeTrace S p T a b σ (oldBandFrickeInclusion S p T a b σ x)=x := by
  change S.frickeParityBandMap a b σ (oldBandTrace S p T a b σ
    (T.frickeParityBandMap a b σ (T.frickeParityBandMap a b σ
      (oldBandInclusion S p T a b σ (S.frickeParityBandMap a b σ x)))))=x
  rw [T.frickeParityBandMap_involutive,oldBandTrace_inclusion S p T hpM u v huv,
    S.frickeParityBandMap_involutive]

theorem oldBand_cross_hecke {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (a b σ : ℝ) (x : S.parityBand a b σ) :
    oldBandTrace S p T a b σ (oldBandFrickeInclusion S p T a b σ x)=
      normalizedBandHecke S p a b σ x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change ((((p:ℝ)+1)⁻¹:ℝ):ℂ) • levelTrace (Nat.dvd_mul_left M p)
      (frickeIsometry (p*M) _ (levelCover (Nat.dvd_mul_left M p)
        (frickeIsometry M hM (x.val.val : AutomorphicSpace M)))) =
    ((Real.sqrt (p:ℝ)/((p:ℝ)+1):ℝ):ℂ) • dilationTraceOperator M p hM (Fact.out : p.Prime).pos
      (x.val.val : AutomorphicSpace M)
  rw [dilationTraceOperator_apply,smul_smul]
  congr 1
  have hp : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : Real.sqrt (p:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.2 hp)
  norm_cast
  field_simp

#print axioms oldBandTrace_pairing
#print axioms frickeParityBandMap_symmetric
#print axioms oldBandFrickeTrace_pairing
#print axioms oldBandTrace_inclusion
#print axioms oldBandFrickeTrace_inclusion
#print axioms oldBand_cross_hecke

end QuantitativeMaass
