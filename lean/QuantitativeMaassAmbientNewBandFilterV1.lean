module

public import QuantitativeMaassDivisorNewBandFilterV1
public import QuantitativeMaassDeepLVParityEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open scoped Topology
open QuantitativeNinaMaass
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



local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    CompleteSpace (S.parityBand a b σ) := FiniteDimensional.complete ℂ _

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (U : Submodule ℂ (S.parityBand a b σ)) : U.HasOrthogonalProjection := by
  let : CompleteSpace U := FiniteDimensional.complete ℂ _
  infer_instance



/-- Full quotient old-pair operator, without a spectral-band projection. -/
def ambientDivisorOldPair {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) :
    AutomorphicSpace N→L[ℂ]AutomorphicSpace N :=
  let B := (levelCover hMN).comp (levelTrace hMN)
  let W := (frickeIsometry N hN).toContinuousLinearMap
  B+W.comp (B.comp W)

/-- The same simple-prime polynomial used on every finite cusp band. -/
def ambientSimpleNewFilter {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N)
    (p m : ℕ) : AutomorphicSpace N→L[ℂ]AutomorphicSpace N :=
  (1-(1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • ambientDivisorOldPair hN hMN))^m

/-- The repeated-two polynomial is also defined on the full quotient.
Its exact-projection property is used only on the proved cusp bands. -/
def ambientRepeatedTwoNewFilter {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) :
    AutomorphicSpace N→L[ℂ]AutomorphicSpace N :=
  let B := (levelCover hMN).comp (levelTrace hMN)-1
  let W := (frickeIsometry N hN).toContinuousLinearMap
  let U := B+W.comp (B.comp W)
  (1/24:ℂ) • (U^4-(2:ℂ) • U^3-U^2+(2:ℂ) • U)

/-- Intertwining passes to powers without a commutativity hypothesis. -/
theorem inclusion_intertwines_power {E H : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup H] [Module ℂ H]
    (J : E→ₗ[ℂ]H) (T : Module.End ℂ E) (U : Module.End ℂ H)
    (h : ∀ x,J (T x)=U (J x)) (m : ℕ) (x : E) :
    J ((T^m) x)=(U^m) (J x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ',Module.End.mul_apply,h,ih,pow_succ',Module.End.mul_apply]

variable {M N : ℕ} [NeZero M] [NeZero N] {hM : 0<M} {hN : 0<N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M∣N) (a b σ : ℝ)

theorem ambientDivisorOldPair_band (x : T.parityBand a b σ) :
    parityBandQuotientInclusion T a b σ (divisorBandOldPair S T hMN a b σ x)=
      ambientDivisorOldPair hN hMN (parityBandQuotientInclusion T a b σ x) := rfl

theorem ambientSimpleNewFilter_band (p m : ℕ) (x : T.parityBand a b σ) :
    parityBandQuotientInclusion T a b σ (divisorSimpleNewBandFilter S T hMN p a b σ m x)=
      ambientSimpleNewFilter hN hMN p m (parityBandQuotientInclusion T a b σ x) := by
  let J := (parityBandQuotientInclusion T a b σ).toLinearMap
  have h : ∀ x,J ((1-(1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • divisorBandOldPair S T hMN a b σ)) x)=
      (1-(1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • ambientDivisorOldPair hN hMN)).toLinearMap (J x) := by
    intro y
    simp only [LinearMap.sub_apply,Module.End.one_apply,LinearMap.smul_apply,map_sub,map_smul]
    rw [show J (divisorBandOldPair S T hMN a b σ y)=ambientDivisorOldPair hN hMN (J y) from
      ambientDivisorOldPair_band S T hMN a b σ y]
    rfl
  have hh := inclusion_intertwines_power J _ _ h m x
  rw [←ContinuousLinearMap.toLinearMap_pow] at hh
  exact hh

theorem ambientRepeatedTwoNewFilter_band (x : T.parityBand a b σ) :
    parityBandQuotientInclusion T a b σ (divisorRepeatedTwoNewBandFilter S T hMN a b σ x)=
      ambientRepeatedTwoNewFilter hN hMN (parityBandQuotientInclusion T a b σ x) := by
  let J := (parityBandQuotientInclusion T a b σ).toLinearMap
  let B := (S.coverParityBandMap T hMN a b σ).comp (S.traceParityBandMap T hMN a b σ)-1
  let U := B+(T.frickeParityBandMap a b σ)*(B*T.frickeParityBandMap a b σ)
  let B₀ := (levelCover hMN).comp (levelTrace hMN)-1
  let W := (frickeIsometry N hN).toContinuousLinearMap
  let U₀ := B₀+W.comp (B₀.comp W)
  have h : ∀ y,J (U y)=U₀.toLinearMap (J y) := fun _ => rfl
  have hh := inclusion_intertwines_power J U U₀.toLinearMap h
  change J (((1/24:ℂ) • (U^4-(2:ℂ) • U^3-U^2+(2:ℂ) • U)) x)=_
  simp only [LinearMap.smul_apply,LinearMap.add_apply,LinearMap.sub_apply,map_smul,map_add,map_sub,hh,h]
  rfl

#print axioms ambientDivisorOldPair_band
#print axioms ambientSimpleNewFilter_band
#print axioms ambientRepeatedTwoNewFilter_band
end QuantitativeMaass
