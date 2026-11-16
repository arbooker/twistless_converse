module

public import QuantitativeMaassAmbientSectorNewFilterV1
public import QuantitativeMaassAmbientSimpleContractionV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open ContinuousLinearMap QuantitativeNinaMaass AsymptoticSectorSigns
open QuantitativeNewGap QuantitativeArithmeticNewBandProjections
namespace QuantitativeMaass

local instance (N : ℕ) (p : ↥N.primeFactors) : NeZero p.val :=
  ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
local instance (N : ℕ) [NeZero N] (p : ↥N.primeFactors) : NeZero (N/p.val) :=
  ⟨(prime_quotient_pos N p.val (NeZero.pos N)
    (Nat.prime_of_mem_primeFactors p.property) (Nat.dvd_of_mem_primeFactors p.property)).ne'⟩

theorem ambientSimpleNewFilter_divisor_norm {M N : ℕ} [NeZero M] [NeZero N]
    (hN : 0<N) (hMN : M∣N) (p : ℕ) [Fact p.Prime]
    (hpMN : p*M=N) (hpM : ¬p∣M) (m : ℕ) :
    ‖ambientSimpleNewFilter hN hMN p m‖≤1 := by
  subst N
  exact ambientSimpleNewFilter_norm M p (NeZero.pos M) hpM m

/-- The finite sign factors are actual orthogonal projections on the
full quotient, not just on a selected cusp band. -/
theorem ambientSectorSignFactor_projection (N : ℕ) (hN : 0<N) (e : Sector N)
    (i : SectorSignIndex N) :
    ambientSectorSignFactor N hN e i=
      (involutionSignSpace (completedSectorNormalizer N hN i) (sectorNormalizerSign e i)).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  exact (involutionSignSpace_projection _ (completedSectorNormalizer_selfAdjoint N hN i)
    (completedSectorNormalizer_involutive N hN i) _ (sectorNormalizerSign_sq e i) x).symm

theorem ambientSectorSignFactor_norm (N : ℕ) (hN : 0<N) (e : Sector N)
    (i : SectorSignIndex N) : ‖ambientSectorSignFactor N hN e i‖≤1 := by
  rw [ambientSectorSignFactor_projection]
  apply opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using
    (involutionSignSpace (completedSectorNormalizer N hN i) (sectorNormalizerSign e i)).norm_starProjection_apply_le x

theorem ambientSectorSignProduct_norm (N : ℕ) (hN : 0<N) (e : Sector N) :
    ‖ambientSectorSignProduct N hN e‖≤1 :=
  contraction_list_prod _ _ (ambientSectorSignFactor_norm N hN e)

theorem bounded_clm_list_product {H I : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] (L : List I)
    (A : I→H→L[ℂ]H) (C : ℝ) (hC : 0≤C) (hA : ∀ i,‖A i‖≤C) :
    ‖(L.map A).prod‖≤C^L.length := by
  induction L with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons i L ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ']
    exact (norm_mul_le _ _).trans (mul_le_mul (hA i) ih (norm_nonneg _) hC)

/-- A single level-dependent bound works for every degree on the full
quotient. At repeated primes the fixed polynomial is merely bounded here;
no uniform spectral gap or global projection identity is presumed. -/
theorem ambientSectorNewFilter_uniform_norm (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ C : ℝ,1≤C ∧ ∀ (e : Sector N) (m : ℕ),‖ambientSectorNewFilter N hN e m‖≤C := by
  classical
  let B : ↥N.primeFactors→ℝ := fun p =>
    ‖ambientRepeatedTwoNewFilter hN (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors p.property))‖
  let C₀ := 1+∑ p,B p
  have hC₀ : 1≤C₀ := by
    have hs : 0≤∑ p,B p := Finset.sum_nonneg (fun p _ => by
      dsimp only [B]
      exact norm_nonneg (ambientRepeatedTwoNewFilter hN
        (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors p.property))))
    dsimp only [C₀]
    linarith
  have hB (p : ↥N.primeFactors) : B p≤C₀ := by
    have hs := Finset.single_le_sum (fun q (_hq : q∈(Finset.univ : Finset ↥N.primeFactors)) =>
      show 0≤B q from norm_nonneg (ambientRepeatedTwoNewFilter hN
        (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors q.property)))) (Finset.mem_univ p)
    dsimp only [C₀]
    linarith
  have hlocal (m : ℕ) (p : ↥N.primeFactors) : ‖ambientAdmissibleLocalNewFilter N hN m p‖≤C₀ := by
    let : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    by_cases hp : p.val∣N/p.val
    · simpa only [ambientAdmissibleLocalNewFilter,ite_eq_left hp] using hB p
    · rw [ambientAdmissibleLocalNewFilter,ite_eq_right hp]
      exact (ambientSimpleNewFilter_divisor_norm hN _ p.val
        (Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors p.property)) hp m).trans hC₀
  let L := (Finset.univ : Finset ↥N.primeFactors).toList
  refine ⟨C₀^L.length,one_le_pow₀ hC₀,?_⟩
  intro e m
  have ht := bounded_clm_list_product L (ambientAdmissibleLocalNewFilter N hN m) C₀
    (zero_le_one.trans hC₀) (hlocal m)
  change ‖ambientAdmissibleTotalNewFilter N hN m‖≤C₀^L.length at ht
  change ‖(ambientAdmissibleTotalNewFilter N hN m).comp (ambientSectorSignProduct N hN e)‖≤_
  apply (opNorm_comp_le _ _).trans
  simpa only [mul_one] using mul_le_mul ht (ambientSectorSignProduct_norm N hN e)
    (norm_nonneg (ambientSectorSignProduct N hN e)) (pow_nonneg (zero_le_one.trans hC₀) _)

#print axioms ambientSimpleNewFilter_divisor_norm
#print axioms ambientSectorSignFactor_projection
#print axioms ambientSectorSignProduct_norm
#print axioms ambientSectorNewFilter_uniform_norm
end QuantitativeMaass
