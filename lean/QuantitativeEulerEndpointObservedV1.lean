module

public import QuantitativeEulerEndpointPreparedV1
public import QuantitativeEulerDensityCanonicalV1
public import QuantitativeEulerDensityLowerNormV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeArithmeticDiamondLabels
open AsymptoticCongruenceLabels QuantitativeEulerDiamondDecode
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups Classical

/-- For the newly constructed summable-exception preparation, every good
prime supplies literal observed canonical matrices for all fixed generators
in its actual residue class. The certificate and branch index are witnesses,
not additional assumptions on the Euler solutions. -/
theorem prepared_observed_certificates (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (threshold q : ℕ) [Fact q.Prime]
    (hq : (prepared N hN excluded threshold).Good q) :
    let P := prepared N hN excluded threshold
    ∃ hqN : ¬q∣N, q∉excluded ∧ threshold<q ∧
      ∃ a : UnitResidue N, Nat.ModEq N q a.val.val ∧
        ∀ i, ∃ d : ℤ, ∃ cert : PolynomialPrimeCertificate
          (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K,
          ∃ j : Fin (q-1),
            (⟨lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
              upperUnipotent cert.l,cert.canonical_det⟩ : SL(2,ℤ))=
              swappedCanonical N q hqN j := by
  let P := prepared N hN excluded threshold
  obtain ⟨hex,hqN,hthreshold,a,hqa,hcert⟩ := P.prime_data q Fact.out hq
  refine ⟨hqN,hex,hthreshold,a,hqa,?_⟩
  intro i
  obtain ⟨d,⟨cert⟩⟩ := hcert i
  obtain ⟨j,hj⟩ := QuantitativeEulerDensityGenerators.PolynomialPrimeCertificate.canonical_eq_observed cert hqN
  exact ⟨d,cert,j,hj⟩

/-- The growing upper-unipotent multiplier has an explicit O(q) height;
its inverse translation is the actual multiplier in the prime identity. -/
theorem certificate_translation_height {Q B c D d : ℤ} {N q : ℕ} {K : ℝ}
    (cert : PolynomialPrimeCertificate Q B N c D d q K) (hq : 1≤q) :
    MatrixEntryBound (upperSL (-cert.l)).val ((1+K)*(q : ℝ)) := by
  have hqr : (1 : ℝ)≤q := by exact_mod_cast hq
  intro i j
  have hu := upperUnipotent_entry_bound (-cert.l) i j
  simp only [Int.cast_neg,abs_neg] at hu
  have hl : |(cert.l : ℝ)|≤K*(q : ℝ) := by simpa only [Int.cast_natCast] using cert.l_bound
  exact hu.trans (by nlinarith)

/-- Uniform polynomial height for the other growing right multiplier in
the fresh-prime identity. This uses the actual certificate height, not a
compactness-selected constant depending silently on q. -/
theorem certificate_first_transport_height {Q B c D d : ℤ} {N q : ℕ} {K : ℝ}
    (cert : PolynomialPrimeCertificate Q B N c D d q K)
    (hK : 0≤K) (hq : 1≤q) :
    MatrixEntryBound
      (lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
        upperUnipotent cert.l*upperUnipotent (-cert.l))
      (2*K*(1+K)*(q : ℝ)^4) := by
  have hu := certificate_translation_height cert hq
  have hc : MatrixEntryBound
      (lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*upperUnipotent cert.l)
      (K*(q : ℝ)^3) := by simpa only [Int.cast_natCast] using cert.canonical_height
  have h := matrix_entry_bound_mul (by positivity) hc hu
  intro i j
  have hi := h i j
  convert hi using 1
  · rfl
  · ring

/-- The canonical term in the actual compact prime-defect identity is
controlled by the original observed branch, with explicit polynomial
transport cost. No invariance of the tested vector is assumed. -/
theorem certificate_observed_compact_norm {Q B c D d : ℤ} {N q : ℕ}
    [Fact q.Prime] {K : ℝ}
    (cert : PolynomialPrimeCertificate Q B N c D d q K) (hK : 0≤K) (hqN : ¬q∣N) :
    ∃ j : Fin (q-1), ∀ {s : Set ℍ} (hs : IsCompact s) {ε H : ℝ} (hε : 0<ε)
      (_hre : ∀ z∈s, |z.re|≤1) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
      ‖matrixCompactAction hs hε t x
        ((matrixSymbol (lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
          upperUnipotent cert.l)-1)*matrixSymbol (upperUnipotent (-cert.l))) v‖≤
        (integerCompactDistortion ((1+K)*(q : ℝ)) H)^t*
          ‖AsymptoticCongruenceDefect.operator (swappedCanonical N q hqN j)
            (branchImage_compact (symbolBranch (integralLabel (upperSL (-cert.l)))) hs) hε t x v‖ := by
  obtain ⟨j,hj⟩ := QuantitativeEulerDensityGenerators.PolynomialPrimeCertificate.canonical_eq_observed cert hqN
  refine ⟨j,?_⟩
  intro s hs ε H hε hre him t x v
  have h := matrixCompactAction_integral_defect_norm
    (⟨_,cert.canonical_det⟩ : SL(2,ℤ)) (upperSL (-cert.l)) hs
    (by positivity) (certificate_translation_height cert (Fact.out : q.Prime).one_lt.le)
    hε hre him t x v
  rw [←hj]
  exact h

#print axioms prepared_observed_certificates
#print axioms certificate_translation_height
#print axioms certificate_first_transport_height
#print axioms certificate_observed_compact_norm
end QuantitativeEulerEndpointPrepared
