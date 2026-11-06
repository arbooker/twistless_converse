module

public import QuantitativeEulerEndpointReconstructedTerminalV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns
open FinitenessCertificate FinitenessGlobalHeight AsymptoticRegularReconstruction
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open AsymptoticRegularCompactBranch (Space)

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ)
variable (P : Parameters A) (e : Sector N)
variable (F : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (F x)]
variable (hF : ∀ x,F x≤TerminalSpace A (AsymptoticReconstructedCount.parameters A P) x)
variable {s : Set ℍ} (hs : IsCompact s) (a c : ℝ) (l : List (EligiblePrime N))

def reconstructedChainImage (x : ℍ) : ClosedSubmodule ℂ Space :=
  primeChain N (NeZero.pos N) (sign e.1) hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4) c
    (closedReconstructedBaseline A P e F hF hs a) l x

theorem reconstructed_chain_image_le (x : ℍ) :
    (reconstructedChainImage A P e F hF hs a c l x).toSubmodule ≤
      reconstructedImage A (NeZero.pos N) P e F hF x :=
  (primeChain_le N (NeZero.pos N) (sign e.1) hs _ _ c _ l x).trans
    (reconstructed_baseline_le A P e F hF hs a x)

/-- The actual original-prime chain returned to terminal coordinates. -/
def reconstructedChainPullback (x : ℍ) : Submodule ℂ Space :=
  reconstructedPullback A (NeZero.pos N) P e F
    (fun x => (reconstructedChainImage A P e F hF hs a c l x).toSubmodule) hF
    (reconstructed_chain_image_le A P e F hF hs a c l) x

instance reconstructedChainPullback_complete (x : ℍ) :
    CompleteSpace (reconstructedChainPullback A P e F hF hs a c l x) := by
  unfold reconstructedChainPullback
  infer_instance

def closedReconstructedChainPullback (x : ℍ) : ClosedSubmodule ℂ Space where
  toSubmodule := reconstructedChainPullback A P e F hF hs a c l x
  isClosed' := (completeSpace_coe_iff_isComplete.mp
    (inferInstance : CompleteSpace (reconstructedChainPullback A P e F hF hs a c l x))).isClosed

theorem reconstructed_chain_pullback_le (x : ℍ) :
    reconstructedChainPullback A P e F hF hs a c l x ≤ F x :=
  reconstructed_pullback_le A (NeZero.pos N) P e F _ hF _ x

theorem reconstructed_chain_image_regular
    (hmF : ∀ g k,Measurable (fun x => matrix (F x).starProjection g k))
    (hcF : Covariant (fun x => (F x).starProjection)) (ha : 0<a) (hc : 0<c) :
    (∀ g k,Measurable (fun x => matrix
      (reconstructedChainImage A P e F hF hs a c l x).toSubmodule.starProjection g k)) ∧
    Covariant (fun x => (reconstructedChainImage A P e F hF hs a c l x).toSubmodule.starProjection) := by
  have hr := reconstructed_baseline_regular A P e F hF hs hmF hcF a ha
  exact primeChain_regular N (NeZero.pos N) (sign e.1) hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4) c hc
    (closedReconstructedBaseline A P e F hF hs a) hr.1 hr.2 l

theorem reconstructed_chain_pullback_regular
    (hmF : ∀ g k,Measurable (fun x => matrix (F x).starProjection g k))
    (hcF : Covariant (fun x => (F x).starProjection)) (ha : 0<a) (hc : 0<c) :
    (∀ g k,Measurable (fun x => matrix
      (reconstructedChainPullback A P e F hF hs a c l x).starProjection g k)) ∧
    Covariant (fun x => (reconstructedChainPullback A P e F hF hs a c l x).starProjection) := by
  have hr := reconstructed_chain_image_regular A P e F hF hs a c l hmF hcF ha hc
  exact reconstructed_pullback_regular A (NeZero.pos N) P e F
    (fun x => (reconstructedChainImage A P e F hF hs a c l x).toSubmodule) hF
    (reconstructed_chain_image_le A P e F hF hs a c l) hr.1 hr.2

/-- Returning a block to terminal coordinates costs no trace. -/
theorem reconstructed_chain_pullback_mass
    (hmF : ∀ g k,Measurable (fun x => matrix (F x).starProjection g k))
    (hcF : Covariant (fun x => (F x).starProjection)) (ha : 0<a) (hc : 0<c) :
    cornerMass (closedReconstructedChainPullback A P e F hF hs a c l) =
      cornerMass (reconstructedChainImage A P e F hF hs a c l) := by
  have hr := reconstructed_chain_image_regular A P e F hF hs a c l hmF hcF ha hc
  exact congrArg ENNReal.toReal
    (reconstructed_pullback_trace A (NeZero.pos N) P e F
    (fun x => (reconstructedChainImage A P e F hF hs a c l x).toSubmodule) hF
    (reconstructed_chain_image_le A P e F hF hs a c l) hr.1 hr.2)

/-- All later primes retain support after a completed block, including the
adjoint pullback through the certificate reconstruction. -/
theorem reconstructed_chain_pullback_supported (ha : 0<a) (hc : 0<c)
    (r : ℕ) [Fact r.Prime] (hrN : ¬r∣N) (hrQ : ¬r∣Q)
    (hrfixed : ∀ b : QuantitativeArithmetic.UnitResidue N,
      ¬r∣(QuantitativeEulerDensityGenerators.primeLift N b).q)
    (hsF : ∀ x,Supported (integralGroup r) (F x).starProjection)
    (hl : ∀ p∈l,¬r∣p.val) (x : ℍ) :
    Supported (integralGroup r) (reconstructedChainPullback A P e F hF hs a c l x).starProjection := by
  apply reconstructed_pullback_supported A (NeZero.pos N) P e F
    (fun x => (reconstructedChainImage A P e F hF hs a c l x).toSubmodule) hF
    (reconstructed_chain_image_le A P e F hF hs a c l) r hrN hrQ _ x
  intro z
  exact primeChain_supported N (NeZero.pos N) (sign e.1) hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4) c hc
    (closedReconstructedBaseline A P e F hF hs a) r hrN
    (reconstructed_baseline_supported A P e F hF hs r hrN hrQ hrfixed hsF a ha) l hl z

#print axioms reconstructed_chain_pullback_le
#print axioms reconstructed_chain_pullback_regular
#print axioms reconstructed_chain_pullback_mass
#print axioms reconstructed_chain_pullback_supported
end QuantitativeEulerEndpointPrepared
