module

public import QuantitativeMaassLocalNewBandFilterV1
public import QuantitativeMaassTotalNewBandApproximationV1
public import AsymptoticClassicalNewDimensionAdmissibleV1

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



/-- The physical trace pair at arbitrary divisor levels, before normalization. -/
def divisorBandOldPair {M N : ℕ} [NeZero M] [NeZero N] {hM : 0<M} {hN : 0<N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN) (hMN : M∣N)
    (a b σ : ℝ) : Module.End ℂ (T.parityBand a b σ) :=
  let B := (S.coverParityBandMap T hMN a b σ).comp (S.traceParityBandMap T hMN a b σ)
  B+(T.frickeParityBandMap a b σ)*(B*T.frickeParityBandMap a b σ)

def divisorSimpleNewBandFilter {M N : ℕ} [NeZero M] [NeZero N] {hM : 0<M} {hN : 0<N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN) (hMN : M∣N)
    (p : ℕ) (a b σ : ℝ) (m : ℕ) : T.parityBand a b σ →L[ℂ] T.parityBand a b σ :=
  LinearMap.toContinuousLinearMap ((1-(1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • divisorBandOldPair S T hMN a b σ))^m)

def divisorRepeatedTwoNewBandFilter {M N : ℕ} [NeZero M] [NeZero N] {hM : 0<M} {hN : 0<N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN) (hMN : M∣N)
    (a b σ : ℝ) : T.parityBand a b σ →L[ℂ] T.parityBand a b σ :=
  let B := (S.coverParityBandMap T hMN a b σ).comp (S.traceParityBandMap T hMN a b σ)-1
  let U := B+(T.frickeParityBandMap a b σ)*(B*T.frickeParityBandMap a b σ)
  LinearMap.toContinuousLinearMap ((1/24:ℂ) • (U^4-(2:ℂ) • U^3-U^2+(2:ℂ) • U))

theorem oldBandSum_eq_divisorPair {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (a b σ : ℝ) :
    oldBandSum S p T a b σ =
      (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • divisorBandOldPair S T (Nat.dvd_mul_left M p) a b σ) := by
  let C := S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ
  let D := S.traceParityBandMap T (Nat.dvd_mul_left M p) a b σ
  let F := S.frickeParityBandMap a b σ
  let W := T.frickeParityBandMap a b σ
  let c : ℂ := ((((p:ℝ)+1)⁻¹:ℝ):ℂ)
  have hF (v : S.parityBand a b σ) : F (F v)=v := S.frickeParityBandMap_involutive a b σ v
  apply LinearMap.ext
  intro x
  change C (c • D x)+W (C (F (F (c • D (W x)))))=
    c • (C (D x)+W (C (D (W x))))
  rw [hF]
  simp only [map_smul,smul_add]

theorem divisorSimpleNewBandFilter_eq {M : ℕ} [NeZero M] {hM : 0<M}
    (S : CuspEnergySpectrum M hM) (p : ℕ) [Fact p.Prime]
    (T : CuspEnergySpectrum (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (a b σ : ℝ) (m : ℕ) :
    divisorSimpleNewBandFilter S T (Nat.dvd_mul_left M p) p a b σ m=
      simpleNewBandFilter S p T a b σ m := by
  have he := congrArg (fun U : Module.End ℂ (T.parityBand a b σ) =>
    LinearMap.toContinuousLinearMap ((1-(1/2:ℂ) • U)^m))
    (oldBandSum_eq_divisorPair S p T a b σ)
  exact he.symm

theorem divisorRepeatedTwoNewBandFilter_eq (L : ℕ) (hL : 0<L)
    [NeZero (2*L)] [NeZero (2*(2*L))]
    (S : CuspEnergySpectrum (2*L) (QuantitativeArithmeticRepeatedTwoBands.twice_pos L hL))
    (T : CuspEnergySpectrum (2*(2*L)) (QuantitativeArithmeticRepeatedTwoBands.four_pos L hL))
    (a b σ : ℝ) :
    divisorRepeatedTwoNewBandFilter S T (Nat.dvd_mul_left (2*L) 2) a b σ=
      (S.traceNewParityBand T (Nat.dvd_mul_left (2*L) 2) a b σ).starProjection :=
  repeatedTwoNewBandFilter_eq L hL S T a b σ


theorem divisorSimpleNewBandFilter_norm {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0<M} {hN : 0<N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M∣N) (p : ℕ) [Fact p.Prime] (hpMN : p*M=N) (hpM : ¬p∣M)
    (a b σ : ℝ) (m : ℕ) : ‖divisorSimpleNewBandFilter S T hMN p a b σ m‖≤1 := by
  subst N
  rw [divisorSimpleNewBandFilter_eq]
  exact simpleNewBandFilter_norm S p T hpM a b σ m

theorem divisorRepeatedTwoNewBandFilter_exact {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0<M} {hN : 0<N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M∣N) (hNM : 2*M=N) (hM2 : 2∣M) (a b σ : ℝ) :
    divisorRepeatedTwoNewBandFilter S T hMN a b σ=(S.traceNewParityBand T hMN a b σ).starProjection := by
  obtain ⟨L,rfl⟩ := hM2
  have hL : 0<L := by omega
  subst N
  exact divisorRepeatedTwoNewBandFilter_eq L hL S T a b σ

theorem divisorSimpleNewBandFilter_weighted_energy {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0<M} {hN : 0<N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M∣N) (p : ℕ) [Fact p.Prime] (hpMN : p*M=N) (hpM : ¬p∣M)
    (σ D W : ℝ) (hD : 0≤D)
    (b : (t : ℝ) → OrthonormalBasis
      (Fin (Module.finrank ℂ (T.parityBand (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ))) ℂ
      (T.parityBand (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t)) σ))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in Filter.atTop,0<ε t)
    (hproduct : Filter.Tendsto (fun t => ε t*slowScale t) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun t => Real.exp (W*fourthRootScale t)*finiteBandEnergy (b t)
      (divisorSimpleNewBandFilter S T hMN p (t-Real.exp (D*fourthRootScale t))
        (t+Real.exp (D*fourthRootScale t)) σ (growingMomentDegree t)-
        (S.traceNewParityBand T hMN (t-Real.exp (D*fourthRootScale t))
          (t+Real.exp (D*fourthRootScale t)) σ).starProjection)/(t*ε t))
      Filter.atTop (nhds 0) := by
  subst N
  simpa only [divisorSimpleNewBandFilter_eq] using
    simpleNewBandFilter_weighted_energy S p T hpM σ D W hD b ε hε hproduct

/-- Admissibility leaves only simple primes and the repeated prime two. -/
theorem admissible_prime_filter_cases (N p : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (hp : p.Prime) (hpN : p∣N) :
    ¬p∣N/p ∨ (p=2 ∧ 4∣N) := by
  by_cases h : p∣N/p
  · right
    have hs : p^2∣N := by
      simpa only [pow_two,Nat.mul_div_cancel' hpN] using Nat.mul_dvd_mul_left p h
    have hp2 : p=2 := by
      by_contra hn
      exact hN.2.2 p hp hn hs
    exact ⟨hp2,by simpa only [hp2,show (2:ℕ)^2=4 by decide] using hs⟩
  · exact Or.inl h

#print axioms divisorSimpleNewBandFilter_norm
#print axioms divisorRepeatedTwoNewBandFilter_exact
#print axioms divisorSimpleNewBandFilter_weighted_energy
#print axioms oldBandSum_eq_divisorPair
#print axioms divisorSimpleNewBandFilter_eq
#print axioms divisorRepeatedTwoNewBandFilter_eq
#print axioms admissible_prime_filter_cases
end QuantitativeMaass
