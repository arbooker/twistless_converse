module

public import QuantitativeMaassSectorParityBandFilterV1
public import QuantitativeMaassAmbientNewBandFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Filter QuantitativeNinaMaass QuantitativeNewGap AsymptoticSectorSigns
open QuantitativeArithmeticRepeatedTwoBands QuantitativeArithmeticNewBandProjections
open QuantitativeArithmeticNewBandProduct
open scoped Topology
namespace QuantitativeMaass

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




local instance (N : ℕ) (p : ↥N.primeFactors) : NeZero p.val :=
  ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩

local instance (N : ℕ) [NeZero N] (p : ↥N.primeFactors) : NeZero (N/p.val) :=
  ⟨(prime_quotient_pos N p.val (NeZero.pos N)
    (Nat.prime_of_mem_primeFactors p.property) (Nat.dvd_of_mem_primeFactors p.property)).ne'⟩

local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    CompleteSpace (T.parityBand a b σ) := FiniteDimensional.complete ℂ _

local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (K : Submodule ℂ (T.parityBand a b σ)) : K.HasOrthogonalProjection := by
  let : CompleteSpace K := FiniteDimensional.complete ℂ _
  infer_instance



local instance {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (K : Submodule ℂ (S.parityBand a b σ)) :
    CompleteSpace K := FiniteDimensional.complete ℂ _


/-- Full quotient realization of each local polynomial. -/
def ambientAdmissibleLocalNewFilter (N : ℕ) [NeZero N] (hN : 0<N)
    (m : ℕ) (p : ↥N.primeFactors) : AutomorphicSpace N→L[ℂ]AutomorphicSpace N :=
  if p.val∣N/p.val then
    ambientRepeatedTwoNewFilter hN (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors p.property))
  else ambientSimpleNewFilter hN (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors p.property)) p.val m

def ambientAdmissibleTotalNewFilter (N : ℕ) [NeZero N] (hN : 0<N) (m : ℕ) :
    AutomorphicSpace N→L[ℂ]AutomorphicSpace N :=
  ((Finset.univ : Finset ↥N.primeFactors).toList.map (ambientAdmissibleLocalNewFilter N hN m)).prod

def ambientSectorSignFactor (N : ℕ) (hN : 0<N) (e : Sector N) (i : SectorSignIndex N) :
    AutomorphicSpace N→L[ℂ]AutomorphicSpace N :=
  (1/2:ℂ) • (1+(sectorNormalizerSign e i:ℂ) • completedSectorNormalizer N hN i)

def ambientSectorSignProduct (N : ℕ) (hN : 0<N) (e : Sector N) :
    AutomorphicSpace N→L[ℂ]AutomorphicSpace N :=
  ((Finset.univ : Finset (SectorSignIndex N)).toList.map (ambientSectorSignFactor N hN e)).prod

/-- An actual bounded operator built from finitely many cover, trace and
normalizer factors. No cusp or spectral-band projection occurs in its definition. -/
def ambientSectorNewFilter (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N) (m : ℕ) :
    AutomorphicSpace N→L[ℂ]AutomorphicSpace N :=
  ambientAdmissibleTotalNewFilter N hN m*ambientSectorSignProduct N hN e

theorem inclusion_intertwines_clm_product {E H I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (J : E→L[ℂ]H) (A : I→E→L[ℂ]E) (B : I→H→L[ℂ]H)
    (h : ∀ i x,J (A i x)=B i (J x)) (L : List I) (x : E) :
    J ((L.map A).prod x)=(L.map B).prod (J x) := by
  induction L generalizing x with
  | nil => rfl
  | cons i L ih =>
    simp only [List.map_cons,List.prod_cons,mul_apply_eq_comp]
    rw [h,ih]

variable (N : ℕ) [NeZero N] (hN : 0<N) (T : CuspEnergySpectrum N hN)
    (S : ∀ p : ↥N.primeFactors, CuspEnergySpectrum (N/p.val)
      (prime_quotient_pos N p.val hN (Nat.prime_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors p.property))) (a b σ : ℝ)

theorem ambientAdmissibleLocalNewFilter_band (m : ℕ) (p : ↥N.primeFactors)
    (x : T.parityBand a b σ) :
    parityBandQuotientInclusion T a b σ (admissibleLocalNewBandFilter N hN T S a b σ m p x)=
      ambientAdmissibleLocalNewFilter N hN m p (parityBandQuotientInclusion T a b σ x) := by
  classical
  by_cases hp : p.val∣N/p.val
  · simp only [admissibleLocalNewBandFilter,ambientAdmissibleLocalNewFilter,ite_eq_left hp]
    exact ambientRepeatedTwoNewFilter_band (S p) T _ a b σ x
  · simp only [admissibleLocalNewBandFilter,ambientAdmissibleLocalNewFilter,ite_eq_right hp]
    exact ambientSimpleNewFilter_band (S p) T _ a b σ p.val m x

theorem ambientAdmissibleTotalNewFilter_band (m : ℕ) (x : T.parityBand a b σ) :
    parityBandQuotientInclusion T a b σ (admissibleTotalNewBandFilter N hN T S a b σ m x)=
      ambientAdmissibleTotalNewFilter N hN m (parityBandQuotientInclusion T a b σ x) :=
  inclusion_intertwines_clm_product _ _ _ (ambientAdmissibleLocalNewFilter_band N hN T S a b σ m) _ x

theorem ambientSectorSignFactor_band (e : Sector N) (i : SectorSignIndex N)
    (x : T.parityBand a b σ) :
    parityBandQuotientInclusion T a b σ ((sectorParitySignSpace T a b σ e i).starProjection x)=
      ambientSectorSignFactor N hN e i (parityBandQuotientInclusion T a b σ x) := by
  rw [sectorParitySignProjection_apply,map_smul,map_add,map_smul]
  have he := sectorParityBandNormalizer_apply T a b σ i x
  change parityBandQuotientInclusion T a b σ (sectorParityBandNormalizer T a b σ i x)=
    completedSectorNormalizer N hN i (parityBandQuotientInclusion T a b σ x) at he
  rw [he]
  rfl

theorem ambientSectorSignProduct_band (e : Sector N) (x : T.parityBand a b σ) :
    parityBandQuotientInclusion T a b σ (sectorParitySignProduct T a b σ e x)=
      ambientSectorSignProduct N hN e (parityBandQuotientInclusion T a b σ x) :=
  inclusion_intertwines_clm_product _ _ _ (ambientSectorSignFactor_band N hN T a b σ e) _ x

/-- Exact restriction, for every degree and every finite cusp parity band. -/
theorem ambientSectorNewFilter_band (e : Sector N) (m : ℕ) (x : T.parityBand a b σ) :
    parityBandQuotientInclusion T a b σ (sectorParityBandFilter N hN T S a b σ e m x)=
      ambientSectorNewFilter N hN e m (parityBandQuotientInclusion T a b σ x) := by
  unfold sectorParityBandFilter ambientSectorNewFilter
  rw [mul_apply_eq_comp,ambientAdmissibleTotalNewFilter_band,
    ambientSectorSignProduct_band,mul_apply_eq_comp]

#print axioms ambientAdmissibleLocalNewFilter_band
#print axioms ambientAdmissibleTotalNewFilter_band
#print axioms ambientSectorSignFactor_band
#print axioms ambientSectorSignProduct_band
#print axioms ambientSectorNewFilter_band
end QuantitativeMaass
