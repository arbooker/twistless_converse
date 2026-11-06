module

public import QuantitativeEulerEndpointNormalizedRecurrenceV1
public import QuantitativeEulerEndpointPreparedHalfV1
public import QuantitativeEulerEndpointSupportOperationsV1
public import QuantitativeEulerEndpointPacketSupportV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPacketSoftUpdate
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace Polynomial
open AsymptoticRegularCompactBranch (Space)
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointPreparedHalf QuantitativeEulerEndpointSubcorner
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open scoped ENNReal

variable {s₀ : Set ℍ} (hs₀ : IsCompact s₀) (p : Corner hs₀) (hp : IsStarProjection p)
  (U : Base → ClosedSubmodule ℂ Space)
  (hU : ∀ x, (U x).toSubmodule.starProjection=
    QuantitativeSpectralRegularAlgebra.representation AsymptoticRationalGroup.Group Base
      action_measurable (region s₀) (region_measurable hs₀) p x)
  (N : ℕ) (hN : 0<N) (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
  {ε : ℝ} (hε : 0<ε) (t : ℕ) (l : List (EligiblePrime N))
local notation "𝔄" => Subcorner action_measurable (region s₀) (region_measurable hs₀) p hp
local notation "ρ" => representation action_measurable (region s₀) (region_measurable hs₀) p hp
local notation "τ" => rootedTrace action_measurable (region s₀) (region_measurable hs₀) p hp measure (region_finite hs₀)
local notation "B" => packetRows N hN w hs hε t l
local notation "C" => packetSequenceBound N hN w hs hε t l
local notation "hmB" => fun i => And.left (packetRows_regular N hN w hs hε t l i)
local notation "hcB" => fun i => And.right (packetRows_regular N hN w hs hε t l i)
local notation "hC" => packetRows_norm N hN w hs hε t l
local notation "NB" => QuantitativeEulerEndpointNormalizedRows.row action_measurable (region s₀) (region_measurable hs₀) p B C l.length
local notation "NC" => QuantitativeEulerEndpointNormalizedRows.bound C l.length
local notation "hmNB" => QuantitativeEulerEndpointNormalizedRows.row_measurable action_measurable (region s₀) (region_measurable hs₀) p B hmB C l.length
local notation "hcNB" => QuantitativeEulerEndpointNormalizedRows.row_covariant action_measurable (region s₀) (region_measurable hs₀) p B hcB C l.length
local notation "hnNB" => QuantitativeEulerEndpointNormalizedRows.row_norm action_measurable (region s₀) (region_measurable hs₀) p hp B C hC l.length
local notation "hsNB" => QuantitativeEulerEndpointNormalizedRows.row_source action_measurable (region s₀) (region_measurable hs₀) p hp B C l.length

def gram : 𝔄 := QuantitativeEulerEndpointBlockGram.gramSum
  action_measurable (region s₀) (region_measurable hs₀) p hp NB hmNB hcNB NC hnNB hsNB l.length

def next (A : 𝔄) (L : ℕ) (z : ℝ[X]) : 𝔄 :=
  aeval (QuantitativeEulerEndpointSoftUpdate.update A (A*gram hs₀ p hp N hN w hs hε t l*A) L) z

theorem primeProduct_le_one {M : ℕ} (l : List (EligiblePrime M)) :
    (l.map primeFactor).prod≤1 := by
  induction l with
  | nil => simp
  | cons q l ih =>
    have hq : primeFactor q≤1 := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact (mul_le_mul_of_nonneg_left ih (primeFactor_nonneg q)).trans (by simpa using hq)

/-- Every still unused prime retains its support through the actual packet
Gram, soft update, and sharpening polynomial. -/
theorem next_supported (A : 𝔄) (r : EligiblePrime N) (hr : r∉l)
    (hP : ∀ x, Supported (integralGroup r.val)
      (QuantitativeSpectralRegularAlgebra.representation AsymptoticRationalGroup.Group Base
        action_measurable (region s₀) (region_measurable hs₀) p x))
    (hA : ∀ x, Supported (integralGroup r.val) (ρ A x)) (L : ℕ) (z : ℝ[X]) :
    ∀ x, Supported (integralGroup r.val) (ρ (next hs₀ p hp N hN w hs hε t l A L z) x) := by
  apply QuantitativeEulerEndpointSupportAlgebra.update_polynomial_supported
    action_measurable (region s₀) (region_measurable hs₀) p hp _ hP A _ hA
  apply QuantitativeEulerEndpointSupportAlgebra.block_gram_supported
    action_measurable (region s₀) (region_measurable hs₀) p hp _ hP NB hmNB hcNB NC hnNB hsNB
  exact QuantitativeEulerEndpointSupportAlgebra.normalized_rows_supported
    action_measurable (region s₀) (region_measurable hs₀) p _ hP B C
    (packetSequence_supported N hN w hs hε t l r hr) l.length

include U hU in
/-- A single polynomial performs the original packet contraction and
preserves all original exact row solutions. The sharp source is the canonical
half cut, so no separately supplied representable projection is required. -/
theorem exists_packet_update (A : 𝔄) (hA0 : 0≤A) (hA1 : A≤1)
    (c : ℝ) (hc : 0<c) {d K : ℝ} (hd : 0<d) (hK : 0<K)
    (hcut : 2*d^2<K) (hbound : 1+d^2≤K)
    (target : ℝ)
    (htheta0 : 0≤Real.log (K/(QuantitativeEulerEndpointBlockNormalization.factor C l.length*c)^2)/Real.log (K/(2*d^2)))
    (htheta1 : Real.log (K/(QuantitativeEulerEndpointBlockNormalization.factor C l.length*c)^2)/Real.log (K/(2*d^2))≤1)
    (hchain : (trace measure (QuantitativeSpectralRegularPacket.projectionFamily
      (fun x : Base => half hs₀ p hp A x) B c l.length)).toReal-target≤
      (l.map primeFactor).prod*(cornerMass (half hs₀ p hp A)-target))
    (L : ℕ) {J : ℕ} (hJ : 0<J) :
    ∃ z : ℝ[X], z.natDegree≤16*J^5+1 ∧
      (∑ i∈z.support, |z.coeff i|)≤(((16*J^5:ℕ):ℝ)+2)*3^(16*J^5) ∧
      0≤next hs₀ p hp N hN w hs hε t l A L z ∧
      next hs₀ p hp N hN w hs hε t l A L z≤A ∧
      τ (next hs₀ p hp N hN w hs hε t l A L z-(next hs₀ p hp N hN w hs hε t l A L z)^2)≤4*τ 1/(J:ℝ) ∧
      (∀ E : 𝔄, A*E=E → (∀ i : Fin l.length, ∀ x, B i x*ρ E x=0) →
        next hs₀ p hp N hN w hs hε t l A L z*E=E) ∧
      τ (next hs₀ p hp N hN w hs hε t l A L z)-target≤
        (1-(1-Real.exp (-(L:ℝ)*(d^2/32)))*(1-(l.map primeFactor).prod)*
          (1-Real.log (K/(QuantitativeEulerEndpointBlockNormalization.factor C l.length*c)^2)/Real.log (K/(2*d^2))))*(τ A-target)+
        (4+2*(L:ℝ))*τ (A-A^2)+(measure (region s₀)).toReal*(Real.log 2/Real.log (K/(2*d^2))) := by
  let q := QuantitativeEulerEndpointCanonicalHalf.projection
    action_measurable (region s₀) (region_measurable hs₀) p hp U hU A (IsSelfAdjoint.of_nonneg hA0)
  have hq := QuantitativeEulerEndpointCanonicalHalf.projection_isStarProjection
    action_measurable (region s₀) (region_measurable hs₀) p hp U hU A (IsSelfAdjoint.of_nonneg hA0)
  have hmass : QuantitativeSpectralFiniteCornerTrace.rootedTrace measure action_measurable
      (region s₀) (region_measurable hs₀) (region_finite hs₀) q=cornerMass (half hs₀ p hp A) :=
    QuantitativeEulerEndpointSubcornerMass.initial_trace_eq
      action_measurable (region s₀) (region_measurable hs₀) q hq measure (region_finite hs₀)
  apply QuantitativeEulerEndpointNormalizedRecurrence.exists_normalized_block_update
    action_measurable (region s₀) (region_measurable hs₀) p hp measure (region_finite hs₀)
    U hU q hq (fun x : Base => half hs₀ p hp A x) (fun _ => rfl)
    B hmB hcB C hC action_preserving A hA0 hA1 (fun _ => rfl) l.length c hc
    hd hK hcut ((add_le_add (QuantitativeEulerEndpointNormalizedRows.bound_square_sum C l.length) (le_refl (d^2))).trans hbound)
    target (l.map primeFactor).prod (primeProduct_nonneg l) (primeProduct_le_one l)
    htheta0 htheta1 _ L hJ
  simpa only [hmass] using hchain

#print axioms primeProduct_le_one
#print axioms next_supported
#print axioms exists_packet_update
end QuantitativeEulerEndpointPacketSoftUpdate
