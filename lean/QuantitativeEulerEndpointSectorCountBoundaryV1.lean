module

public import QuantitativeEulerEndpointSectorPacketCheckV1
public import QuantitativeEulerOldProjectionClassicalDimensionCountV1
public import AsymptoticArithmeticNewCoefficientV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane AsymptoticSectorSigns
open QuantitativeSpectralObservability
open scoped Classical MatrixGroups

/-- The actual summed packet bound with the same arithmetic coefficient
as the classical total-newspace dimension. This does not perform the
finite Euler-count transfer. -/
theorem prepared_sector_packet_sum_arithmetic (N : ℕ) [NeZero N] (hN : 2≤N) (hAdm : GridAdmissibleGap.Admissible N)
    (excluded : Finset ℕ) (hex : baselineDenominators N⊆excluded) (threshold : ℕ)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) {n : ℕ} (hn : 0<n) {H : ℝ} (hH : max ε⁻¹ 4≤H)
    (hdata : ∀ e i, sectorFamilyB N (NeZero.pos N) e S hS i≤H)
    {t : ℕ} (ht : 1≤t) :
    let d := fun e => sectorPacketWitness N hN e excluded hex threshold S hS hε
    ∑ e : Sector N,cornerMass ((d e).packet n H t)≤
      4*Real.pi*AsymptoticTotalNewCorner.arithmeticCoefficient N+
        (∑ e : Sector N,sectorTailConstant N (NeZero.pos N) e S hS)/H+
        ε⁻¹*(∑ e : Sector N,(d e).A0)/Real.log (n+1:ℝ) := by
  rw [←AsymptoticTotalNewCorner.coefficient_eq_arithmetic N hAdm]
  exact prepared_sector_packet_sum N hN excluded hex threshold S hS hε hn hH hdata ht

#print axioms prepared_sector_packet_sum_arithmetic
#print axioms QuantitativeEulerOldProjectionClassicalDimension.new_dimension_bounded
#print axioms QuantitativeEulerOldProjectionClassicalDimension.literal_count_squeeze
#print axioms QuantitativeEulerOldProjectionClassicalDimension.count_errors_differ_isBigO_one
end QuantitativeEulerEndpointPrepared
