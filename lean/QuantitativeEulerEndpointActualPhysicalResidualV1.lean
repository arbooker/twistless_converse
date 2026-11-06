module

public import QuantitativeEulerEndpointPhysicalCompressedGramV1
public import QuantitativeEulerEndpointTerminalPhysicalResidualV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointPhysicalNormalization QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointResidual QuantitativeEulerEndpointExponentialParameters
open ContinuousLinearMap
open scoped Classical MatrixGroups
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- Original physical row annihilation controls the selected finite Gram,
with only the common reconstruction error and no row-count loss. -/
theorem actualGramExpressions_original_residual (n j m : ℕ) (u : Expression)
    (V E : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (hu : ‖holomorphicSum u m‖≤1) (hV : ‖V‖≤1)
    (hbase : let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
      ∀ i,holomorphicSum (originalBaselineExpression N e b.compact
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+4) i) m*V*E=0)
    (hprime : let b := actualBlock A P hN excluded threshold e S hS W B Bg D H₀ G C Kobs n j
      ∀ i : Fin b.primes.length,holomorphicSum (originalPacketSequenceExpression b.compact
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos N (NeZero.pos N) (sign e.1)
        ((AsymptoticReconstructedCount.parameters A P).s+4) b.primes i) m*V*E=0) :
    ‖holomorphicSum (actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j) m*E‖≤
      2*‖holomorphicSum u m-V‖*‖E‖ := by
  let rows := actualReplacementRows A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n j
  let T := holomorphicSum (actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n [identity] j) m
  have hi : holomorphicSum [identity] m=1 := by
    simp only [holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,holomorphic_identity,add_zero]
  have ht := actualGramExpressions_physical_order A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs
    n j m [identity] (by
      rw [hi]
      exact ContinuousLinearMap.norm_id_le)
  have hn : ‖T‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ ht.1).mpr ht.2
  have he : holomorphicSum (actualGramExpressions A P e hN excluded threshold S hS W B Bg D H₀ G C Kobs n u j) m=
      star (holomorphicSum u m)*T*holomorphicSum u m := holomorphic_combined_compression rows.baseline rows.prime _ u m
  have hz : (star V*T*V)*E=0 := by
    change (star V*holomorphicSum (combinedGramExpression rows.baseline rows.prime _ [identity]) m*V)*E=0
    rw [rows.physical,holomorphic_combinedGramExpression]
    simp only [hi,mul_one]
    exact original_gram_kills _ _ _ V E hbase hprime
  rw [he]
  exact compression_residual T _ V E hn hu hV hz

end QuantitativeEulerEndpointBoundedIteration

namespace QuantitativeEulerEndpointCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic ContinuousLinearMap
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

def physicalExact (hN : 0<N) (h : ℕ) (e : Sector N) :=
  AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
    ((normalizedCountReconstruction A hN P h e).comp
      (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε).adjoint)

theorem physicalExact_norm (hN : 0<N) (h : ℕ) (e : Sector N) : ‖physicalExact A P hN h e‖≤1 := by
  have hv : ‖normalizedCountReconstruction A hN P h e‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro g
    rw [normalizedCountReconstruction_norm,one_mul]
  have hh := norm_isometric_transport_difference_le
    (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε)
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _) AsymptoticCylinderLift.lift.toContinuousLinearMap
    AsymptoticCylinderLift.lift.adjoint_comp_self (normalizedCountReconstruction A hN P h e)
    (0 : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε →L[ℂ] AsymptoticCylinder.Space)
  simp only [zero_comp,comp_zero,sub_zero] at hh
  exact hh.trans hv

#print axioms QuantitativeEulerEndpointBoundedIteration.actualGramExpressions_original_residual
#print axioms physicalExact_norm
end QuantitativeEulerEndpointCommonReconstruction
