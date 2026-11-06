module

public import QuantitativeEulerEndpointTerminalObservationsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointTerminalAlgebra
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount QuantitativeEulerEndpointRegularBase
open Polynomial QuantitativeEulerEndpointBernstein

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (hN : 0<N) (P : Parameters A) (e : Sector N)
variable {ι : Type*} (qs : ℕ → Finset ι) (r : ℕ → ι → Row N) (s : ℕ → ι → Set UpperHalfPlane)
  (hs : ∀ j i,IsCompact (s j i)) (q₀ : ℝ[X]) (d : ℕ → ℕ) (q : ℕ → ℝ[X])

def nestedFilter (n : ℕ) : Algebra A P :=
  QuantitativeEulerEndpointNestedOperator.filter
    (observationEnergy A hN P e (qs 0) (r 0) (s 0) (hs 0))
    (fun j => observationEnergy A hN P e (qs (j+1)) (r (j+1)) (s (j+1)) (hs (j+1))) q₀ d q n

theorem nested_filter_order (hq₀ : ScalarInitializer q₀) (hq : ∀ j,ScalarSharpening (q j)) (n : ℕ) :
    0≤nestedFilter A hN P e qs r s hs q₀ d q n ∧ nestedFilter A hN P e qs r s hs q₀ d q n≤1 := by
  unfold nestedFilter
  exact QuantitativeEulerEndpointNestedOperator.filter_order _ _ _ _ _
    (observation_energy_order A hN P e _ _ _ _) (fun _ => observation_energy_order A hN P e _ _ _ _) hq₀ hq n

theorem nested_filter_step_le (hq₀ : ScalarInitializer q₀) (hq : ∀ j,ScalarSharpening (q j)) (n : ℕ) :
    nestedFilter A hN P e qs r s hs q₀ d q (n+1)≤nestedFilter A hN P e qs r s hs q₀ d q n :=
  QuantitativeEulerEndpointNestedOperator.filter_step_le _ _ _ _ _
    (observation_energy_order A hN P e _ _ _ _) (fun _ => observation_energy_order A hN P e _ _ _ _) hq₀ hq n

theorem nested_trace_bounds (hq₀ : ScalarInitializer q₀) (hq : ∀ j,ScalarSharpening (q j)) (n : ℕ) :
    0≤tr A P (nestedFilter A hN P e qs r s hs q₀ d q n) ∧
    tr A P (nestedFilter A hN P e qs r s hs q₀ d q n)≤(AsymptoticReconstructedCount.parameters A P).ε⁻¹ := by
  have hh := nested_filter_order A hN P e qs r s hs q₀ d q hq₀ hq n
  constructor
  · simpa only [map_zero] using tr_mono A P hh.1
  · exact (tr_mono A P hh.2).trans_eq (tr_one A P)

end QuantitativeEulerEndpointTerminalAlgebra

namespace QuantitativeEulerEndpointTerminalAlgebra
open FinitenessCertificate FinitenessGlobalHeight QuantitativeEulerEndpointRegularBase
open AsymptoticFiniteBranch Polynomial
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

def repAt (z : Base) : Algebra A P →ₗ[ℝ] (RegularSpace →L[ℂ] RegularSpace) where
  toFun a := rep A P a z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rep_aeval (a : Algebra A P) (q : ℝ[X]) (z : Base) :
    rep A P (aeval a q) z=aeval (rep A P a z) q*rep A P 1 z :=
  QuantitativeEulerEndpointCornerPolynomial.map_aeval_corner (repAt A P z) (fun _ _ => rfl) a q

theorem rep_update (a g : Algebra A P) (n : ℕ) (z : Base) :
    rep A P (QuantitativeEulerEndpointSoftUpdate.update a (a*g*a) n) z=
      QuantitativeEulerEndpointUpdateExpression.cornerUpdate (rep A P 1 z) (rep A P a z) (rep A P g z) n :=
  QuantitativeEulerEndpointUpdateExpression.map_update (repAt A P z) (fun _ _ => rfl) a g n

#print axioms nested_filter_order
#print axioms nested_filter_step_le
#print axioms nested_trace_bounds
#print axioms rep_aeval
#print axioms rep_update
end QuantitativeEulerEndpointTerminalAlgebra
