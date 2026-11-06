module

public import QuantitativeEulerEndpointNestedOperatorV1
public import QuantitativeHolomorphicObservationFilterV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointNestedPhysical
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open ContinuousLinearMap AsymptoticCompactObservationCount QuantitativeHolomorphic
open Polynomial QuantitativeEulerEndpointBernstein

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

def energy (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i,IsCompact (s i)) :=
  (normalizedObservationBound A hN P qs r s hs)⁻¹ •
    normalizedObservationGram A hN P h e qs r s hs

theorem energy_order (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i,IsCompact (s i)) :
    0≤energy A hN P h e qs r s hs ∧ energy A hN P h e qs r s hs≤1 := by
  unfold energy
  exact QuantitativeEulerEndpointNestedOperator.scaled_energy_order
    (normalizedObservationGram A hN P h e qs r s hs)
    (normalizedObservationBound A hN P qs r s hs)
    (normalizedObservationBound_pos A hN P qs r s hs)
    (normalizedObservationGram_bounds A hN P h e qs r s hs)

theorem energy_sector_zero (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i,IsCompact (s i))
    (a : AsymptoticRamifiedSectors.sector N h
      (h+1+(AsymptoticReconstructedCount.parameters A P).s) e) :
    energy A hN P h e qs r s hs (normalizedSectorCoordinates A hN P h e a)=0 := by
  simp only [energy,smul_apply,normalizedObservationGram_sector_zero,smul_zero]

/-- Concrete nested filters in the normalized coordinates of the full physical sector. -/
def filter (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : ℕ → Finset ι) (r : ℕ → ι → Row N) (s : ℕ → ι → Set UpperHalfPlane)
    (hs : ∀ j i,IsCompact (s j i)) (q₀ : ℝ[X]) (d : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) :=
  QuantitativeEulerEndpointNestedOperator.filter
    (energy A hN P h e (qs 0) (r 0) (s 0) (hs 0))
    (fun j => energy A hN P h e (qs (j+1)) (r (j+1)) (s (j+1)) (hs (j+1))) q₀ d q n

theorem filter_order (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : ℕ → Finset ι) (r : ℕ → ι → Row N) (s : ℕ → ι → Set UpperHalfPlane)
    (hs : ∀ j i,IsCompact (s j i)) (q₀ : ℝ[X]) (d : ℕ → ℕ) (q : ℕ → ℝ[X])
    (hq₀ : ScalarInitializer q₀) (hq : ∀ j,ScalarSharpening (q j)) (n : ℕ) :
    0≤filter A hN P h e qs r s hs q₀ d q n ∧ filter A hN P h e qs r s hs q₀ d q n≤1 := by
  unfold filter
  exact QuantitativeEulerEndpointNestedOperator.filter_order
    (energy A hN P h e (qs 0) (r 0) (s 0) (hs 0))
    (fun j => energy A hN P h e (qs (j+1)) (r (j+1)) (s (j+1)) (hs (j+1))) q₀ d q
    (energy_order A hN P h e _ _ _ _) (fun _ => energy_order A hN P h e _ _ _ _) hq₀ hq n

theorem filter_sector_fixes (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : ℕ → Finset ι) (r : ℕ → ι → Row N) (s : ℕ → ι → Set UpperHalfPlane)
    (hs : ∀ j i,IsCompact (s j i)) (q₀ : ℝ[X]) (d : ℕ → ℕ) (q : ℕ → ℝ[X])
    (hq₀ : ScalarInitializer q₀) (hq : ∀ j,ScalarSharpening (q j)) (n : ℕ)
    (a : AsymptoticRamifiedSectors.sector N h
      (h+1+(AsymptoticReconstructedCount.parameters A P).s) e) :
    filter A hN P h e qs r s hs q₀ d q n (normalizedSectorCoordinates A hN P h e a)=
      normalizedSectorCoordinates A hN P h e a :=
  QuantitativeEulerEndpointNestedOperator.filter_apply_fixed _ _ q₀ d q _
    (energy_sector_zero A hN P h e _ _ _ _ a)
    (fun _ => energy_sector_zero A hN P h e _ _ _ _ a) hq₀.1 (fun j => (hq j).2.1) n

#print axioms energy_order
#print axioms filter_order
#print axioms filter_sector_fixes
end QuantitativeEulerEndpointNestedPhysical
