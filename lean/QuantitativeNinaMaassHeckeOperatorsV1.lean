module

public import QuantitativeNinaMaassOldDescentV1
public import QuantitativeNinaMaassHeckeCoefficientsV1
public import AsymptoticRamifiedTwistedLawV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane QuantitativeMaass
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open AsymptoticFreshMatrices
open scoped Topology InnerProductSpace

/-!
The actual good-prime Hecke operator factors through physical level cover,
Fricke, and adjoint trace. This proves cusp preservation for every good
prime, without the additional congruence condition used by the auxiliary
trace estimates. The factorization will also transport the simultaneous
newform equations.
-/

namespace QuantitativeNinaMaass

theorem fricke_mul_fricke_eq_dilation (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    frickeLabel N hN * frickeLabel (p * N) (Nat.mul_pos hp hN) = dilationLabel p hp := by
  have hh := congrArg (fun g => g * frickeLabel (p * N) (Nat.mul_pos hp hN))
    (AsymptoticRamifiedTwistedLaw.dilation_mul_fricke N p hN hp)
  simpa only [mul_assoc, frickeLabel_mul_self, mul_one] using hh.symm

/-- An explicit bounded operator assembled from the actual quotient maps.
At a good prime it equals the existing normalized Hecke operator. -/
def dilationTraceOperator (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) •
    (levelTrace (Nat.dvd_mul_left N p)).comp
      ((frickeIsometry (p * N) (Nat.mul_pos hp hN)).toContinuousLinearMap.comp
        ((levelCover (Nat.dvd_mul_left N p)).comp (frickeIsometry N hN).toContinuousLinearMap))

theorem dilationTraceOperator_apply (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (v : AutomorphicSpace N) :
    dilationTraceOperator N p hN hp v =
      (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) • levelTrace (Nat.dvd_mul_left N p)
        (frickeIsometry (p * N) (Nat.mul_pos hp hN)
          (levelCover (Nat.dvd_mul_left N p) (frickeIsometry N hN v))) := rfl

theorem shiftedRepresentative_fricke_cover (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    HeckeL2.shiftedRepresentative N p hN hpN A B hAB f =
      frickeRepresentative (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)
        (levelCoverRepresentative (Nat.dvd_mul_left N p) (frickeRepresentative N hN f)) := by
  apply Subtype.ext
  funext z
  change f.val (AsymptoticClassicalCusp.heckeNormalizerLabel N p
      (Fact.out : p.Prime).pos A B hAB • z) =
    f.val (frickeLabel N hN • (frickeLabel (p * N)
      (Nat.mul_pos (Fact.out : p.Prime).pos hN) • z))
  rw [HeckeL2.normalizer_function_eq_dilation, ← mul_smul, fricke_mul_fricke_eq_dilation]

theorem heckeRepresentative_eq_trace (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    HeckeL2.heckeRepresentative N p hN hpN A B hAB f =
      (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) • levelTraceRepresentative (Nat.dvd_mul_left N p)
        (HeckeL2.shiftedRepresentative N p hN hpN A B hAB f) := by
  apply Subtype.ext
  funext z
  rfl

/-- This equality is on the completed physical Hilbert space. It is first
proved on actual representatives and then extended by density. -/
theorem hecke_eq_dilationTraceOperator (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) :
    HeckeL2.operator N p hN hpN A B hAB =
      dilationTraceOperator N p hN (Fact.out : p.Prime).pos := by
  apply DFunLike.coe_injective
  apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
    (HeckeL2.operator N p hN hpN A B hAB).continuous
    (dilationTraceOperator N p hN (Fact.out : p.Prime).pos).continuous
  funext f
  simp only [Function.comp_apply, HeckeL2.operator_on_representatives,
    heckeRepresentative_eq_trace, map_smul, shiftedRepresentative_fricke_cover,
    dilationTraceOperator_apply, frickeIsometry_apply, levelCover_apply,
    levelTraceRepresentative_embedding]

/-- Cusp preservation for the physical factorization at every positive
integer p. It uses the proved cover, trace, and Fricke cusp theorems. -/
theorem dilationTraceOperator_mem_cuspidal (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (v : AutomorphicSpace N)
    (hv : v ∈ localCuspidalSpace N hN) :
    dilationTraceOperator N p hN hp v ∈ localCuspidalSpace N hN := by
  rw [dilationTraceOperator_apply]
  apply (localCuspidalSpace N hN).smul_mem
  apply levelTrace_mem_cuspidal hN (Nat.mul_pos hp hN) (Nat.dvd_mul_left N p)
  apply fricke_mem_cuspidal (p * N) (Nat.mul_pos hp hN)
  apply levelCover_mem_cuspidal hN (Nat.mul_pos hp hN) (Nat.dvd_mul_left N p)
  exact fricke_mem_cuspidal N hN v hv

theorem hecke_mem_cuspidal_all_good_primes (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) (v : AutomorphicSpace N)
    (hv : v ∈ localCuspidalSpace N hN) :
    HeckeL2.operator N p hN hpN A B hAB v ∈ localCuspidalSpace N hN := by
  rw [hecke_eq_dilationTraceOperator]
  exact dilationTraceOperator_mem_cuspidal N p hN (Fact.out : p.Prime).pos v hv

theorem friedrichsGraph_scalar (N : ℕ) (c : ℂ) {v w : AutomorphicSpace N}
    (h : FriedrichsGraph N v w) : FriedrichsGraph N (c • v) (c • w) := by
  change friedrichsResolvent N (c • v + c • w) = c • v
  rw [← smul_add, map_smul, h]

/-- The same physical factorization preserves the actual Friedrichs
graph, including arbitrary domain vectors. -/
theorem dilationTraceOperator_friedrichsGraph (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (v w : AutomorphicSpace N) (hvw : FriedrichsGraph N v w) :
    FriedrichsGraph N (dilationTraceOperator N p hN hp v)
      (dilationTraceOperator N p hN hp w) := by
  simp only [dilationTraceOperator_apply]
  apply friedrichsGraph_scalar
  apply levelTrace_friedrichsGraph
  apply fricke_friedrichsGraph
  apply levelCover_friedrichsGraph
  exact fricke_friedrichsGraph N hN hvw

theorem dilationTraceOperator_reflection (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (v : AutomorphicSpace N) :
    dilationTraceOperator N p hN hp (reflectionIsometry N v) =
      reflectionIsometry N (dilationTraceOperator N p hN hp v) := by
  simp only [dilationTraceOperator_apply, frickeIsometry_reflection,
    ← levelCover_reflection, levelTrace_reflection, map_smul]

#print axioms fricke_mul_fricke_eq_dilation
#print axioms dilationTraceOperator_apply
#print axioms shiftedRepresentative_fricke_cover
#print axioms heckeRepresentative_eq_trace
#print axioms hecke_eq_dilationTraceOperator
#print axioms dilationTraceOperator_mem_cuspidal
#print axioms hecke_mem_cuspidal_all_good_primes
#print axioms friedrichsGraph_scalar
#print axioms dilationTraceOperator_friedrichsGraph
#print axioms dilationTraceOperator_reflection

end QuantitativeNinaMaass
