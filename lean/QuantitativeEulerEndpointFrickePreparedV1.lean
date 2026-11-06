module

public import QuantitativeEulerEndpointFrickeV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeArithmeticDiamondLabels
open AsymptoticCongruenceLabels QuantitativeEulerDiamondDecode AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups Classical

/-- The explicit cost of two original untwisted rows. The exponent r
changes only the image region and polynomial height, not the row count. -/
def lowerFrickeControl (N : ℕ) (hN : 0<N) (r : ℤ) (w : ℂ) (β : SL(2,ℤ))
    (B H : ℝ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (v : Space) : ℝ :=
  (integerCompactDistortion (2*(1+(N : ℝ)*|(r : ℝ)|)*B) H)^t*
    ‖twist N 1 hN Nat.zero_lt_one w
      (branchImage_compact (symbolBranch (integralLabel (lowerSL N r*β))) hs) hε t x v‖+
  (integerCompactDistortion B H)^t*
    ‖twist N 1 hN Nat.zero_lt_one w
      (branchImage_compact (symbolBranch (integralLabel β)) hs) hε t x v‖

/-- The entire prepared-prime operator is bounded by SIX original q=1
rows plus one observed canonical residual. All three lower-power defects
are eliminated directly, including the variable exponent r, with no
variable-length telescope. The canonical residual is addressed separately
by the existing signed Fricke/prime recovery identity. -/
theorem compact_prime_fricke_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) {d : ℤ} {q : ℕ}
    [Fact q.Prime]
    (cert : PolynomialPrimeCertificate
      (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K) (hqN : ¬q∣N) :
    let H₀ : SL(2,ℤ) := ⟨certificateMatrix (P.Q a) (P.B a i) N (P.c a i) (P.D a i),
      by rw [certificate_det]; exact P.determinant a i⟩
    let C : SL(2,ℤ) := ⟨lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
      upperUnipotent cert.l,cert.canonical_det⟩
    let U := upperSL (-cert.l)
    ∃ j : Fin (q-1), ∀ (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε H : ℝ} (hε : 0<ε)
      (_hre : ∀ z∈s, |z.re|≤1) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
      ‖(matrixCompactAction hs hε t x (matrixSymbol (family N a i).val)-
        matrixCompactAction hs hε t x 1) v‖≤
      lowerFrickeControl N (NeZero.pos N) 1 w (C*U) (2*P.K*(1+P.K)*(q : ℝ)^4) H hs hε t x v +
      (integerCompactDistortion ((1+P.K)*(q : ℝ)) H)^t*
        transportedResidual (swappedCanonical N q hqN j) U hs hε t x v +
      lowerFrickeControl N (NeZero.pos N) cert.r w H₀ (fixedMatrixHeight H₀.val) H hs hε t x v +
      lowerFrickeControl N (NeZero.pos N) (P.n a i) w (family N a i)
        (fixedMatrixHeight (family N a i).val) H hs hε t x v := by
  dsimp only
  obtain ⟨j,hcanonical⟩ := certificate_observed_compact_norm cert P.K_pos.le hqN
  refine ⟨j,?_⟩
  intro w s hs ε H hε hre him t x v
  let H₀ : SL(2,ℤ) := ⟨certificateMatrix (P.Q a) (P.B a i) N (P.c a i) (P.D a i),
    by rw [certificate_det]; exact P.determinant a i⟩
  let C : SL(2,ℤ) := ⟨lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
    upperUnipotent cert.l,cert.canonical_det⟩
  let U := upperSL (-cert.l)
  have hK : 0<P.K := P.K_pos
  have hfirst := compact_lower_fricke_norm N (NeZero.pos N) 1 w (C*U) hs
    (by positivity) (certificate_first_transport_height cert P.K_pos.le
      (Fact.out : q.Prime).one_lt.le) hε hre him t x v
  change ‖matrixCompactAction hs hε t x
    ((matrixSymbol (lowerUnipotent N 1)-1)*matrixSymbol (C.val*U.val)) v‖≤_ at hfirst
  rw [matrixSymbol_mul,←mul_assoc] at hfirst
  have hsecond := hcanonical hs hε hre him t x v
  have hthird := compact_lower_fricke_norm N (NeZero.pos N) cert.r w H₀ hs
    (fixedMatrixHeight_nonneg _) (fixedMatrixHeight_bounds _) hε hre him t x v
  have hfourth := compact_lower_fricke_norm N (NeZero.pos N) (P.n a i) w (family N a i) hs
    (fixedMatrixHeight_nonneg _) (fixedMatrixHeight_bounds _) hε hre him t x v
  have heq := congrArg (fun T : Space →L[ℂ] Space => T v)
    (P.compact_prime_defect a i cert hs hε t x)
  rw [heq,_root_.sub_apply,_root_.sub_apply,_root_.add_apply]
  have htriangle (u v w z : Space) : ‖u+v-w-z‖≤‖u‖+‖v‖+‖w‖+‖z‖ := by
    calc
      _ ≤ ‖u+v-w‖+‖z‖ := norm_sub_le _ _
      _ ≤ (‖u+v‖+‖w‖)+‖z‖ := add_le_add (norm_sub_le (u+v) w) le_rfl
      _ ≤ _ := add_le_add (add_le_add (norm_add_le u v) le_rfl) le_rfl
  exact (htriangle _ _ _ _).trans
    (add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth)

#print axioms compact_prime_fricke_bound
end QuantitativeEulerEndpointPrepared
