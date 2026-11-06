module

public import QuantitativeEulerEndpointObservedV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeArithmeticDiamondLabels
open AsymptoticCongruenceLabels QuantitativeEulerDiamondDecode
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups Classical

/-- Norm of an actual congruence residual on the exact compact region
obtained by its right multiplier. -/
def transportedResidual (γ β : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) : ℝ :=
  ‖AsymptoticCongruenceDefect.operator γ
    (branchImage_compact (symbolBranch (integralLabel β)) hs) hε t x v‖

/-- Quantitative realization of the entire prepared-prime identity. Every
term is an actual observed canonical or lower-unipotent residual on an
explicit compact image. The variable telescope has exactly |r| terms,
with |r|≤Kq; the growing transport heights are explicit polynomials in q.
This local operator inequality is not a small-spectrum or count theorem. -/
theorem compact_prime_defect_bound {N : ℕ} [NeZero N]
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
    let B₀ := fixedMatrixHeight H₀.val
    let B₁ := fixedMatrixHeight (family N a i).val
    ∃ j : Fin (q-1), ∃ n : ℕ, ∃ e : ℕ → ℤ, ∃ m : ℕ, ∃ f : ℕ → ℤ,
      n=cert.r.natAbs ∧ m=(P.n a i).natAbs ∧
      (∀ b<n, |e b|≤|cert.r|) ∧ (∀ b<m, |f b|≤|P.n a i|) ∧
      ∀ {s : Set ℍ} (hs : IsCompact s) {ε H : ℝ} (hε : 0<ε)
        (_hre : ∀ z∈s, |z.re|≤1) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      ‖(matrixCompactAction hs hε t x (matrixSymbol (family N a i).val)-
        matrixCompactAction hs hε t x 1) v‖≤
        (integerCompactDistortion (2*P.K*(1+P.K)*(q : ℝ)^4) H)^t*
          transportedResidual (lowerSL N 1) (C*U) hs hε t x v +
        (integerCompactDistortion ((1+P.K)*(q : ℝ)) H)^t*
          transportedResidual (swappedCanonical N q hqN j) U hs hε t x v +
        (integerCompactDistortion (2*(1+(N : ℝ)*|(cert.r : ℝ)|)*B₀) H)^t*
          ∑ b∈Finset.range n, transportedResidual (lowerSL N 1) (lowerSL N (e b)*H₀) hs hε t x v +
        (integerCompactDistortion (2*(1+(N : ℝ)*|(P.n a i : ℝ)|)*B₁) H)^t*
          ∑ b∈Finset.range m, transportedResidual (lowerSL N 1)
            (lowerSL N (f b)*family N a i) hs hε t x v := by
  dsimp only
  obtain ⟨j,hcanonical⟩ := certificate_observed_compact_norm cert P.K_pos.le hqN
  obtain ⟨n,e,hn,he,hr⟩ := lower_power_compact_norm N cert.r
  obtain ⟨m,f,hm,hf,hfixed⟩ := lower_power_compact_norm N (P.n a i)
  refine ⟨j,n,e,m,f,hn,hm,he,hf,?_⟩
  intro s hs ε H hε hre him t x v
  let H₀ : SL(2,ℤ) := ⟨certificateMatrix (P.Q a) (P.B a i) N (P.c a i) (P.D a i),
    by rw [certificate_det]; exact P.determinant a i⟩
  let C : SL(2,ℤ) := ⟨lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
    upperUnipotent cert.l,cert.canonical_det⟩
  let U := upperSL (-cert.l)
  have hK : 0<P.K := P.K_pos
  have hfirst := matrixCompactAction_integral_defect_norm (lowerSL N 1) (C*U) hs
    (by positivity) (certificate_first_transport_height cert P.K_pos.le
      (Fact.out : q.Prime).one_lt.le) hε hre him t x v
  change ‖matrixCompactAction hs hε t x
    ((matrixSymbol (lowerUnipotent N 1)-1)*matrixSymbol (C.val*U.val)) v‖≤_ at hfirst
  rw [matrixSymbol_mul,←mul_assoc] at hfirst
  have hsecond := hcanonical hs hε hre him t x v
  have hthird := hr H₀ hs (fixedMatrixHeight_nonneg _) (fixedMatrixHeight_bounds _)
    hε hre him t x v
  have hfourth := hfixed (family N a i) hs (fixedMatrixHeight_nonneg _)
    (fixedMatrixHeight_bounds _) hε hre him t x v
  have heq := congrArg (fun T : Space →L[ℂ] Space => T v)
    (P.compact_prime_defect a i cert hs hε t x)
  rw [heq,_root_.sub_apply,_root_.sub_apply,_root_.add_apply]
  have htriangle (u v w z : Space) :
      ‖u+v-w-z‖≤‖u‖+‖v‖+‖w‖+‖z‖ := by
    calc
      _ ≤ ‖u+v-w‖+‖z‖ := norm_sub_le _ _
      _ ≤ (‖u+v‖+‖w‖)+‖z‖ := add_le_add (norm_sub_le (u+v) w) le_rfl
      _ ≤ _ := add_le_add (add_le_add (norm_add_le u v) le_rfl) le_rfl
  exact (htriangle _ _ _ _).trans
    (add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth)

#print axioms compact_prime_defect_bound
end QuantitativeEulerEndpointPrepared
