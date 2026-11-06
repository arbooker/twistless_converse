module

public import QuantitativeEulerEndpointProjectiveNormV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode AsymptoticCongruenceLabels
open QuantitativeArithmeticDiamondLabels AsymptoticFreshAveraging
open AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularBranchFamily AsymptoticRegularObservationRows AsymptoticFreshCompactDefects
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- The seven original rows control a prepared defect after ANY rational
projective right action with an integral representative. The determinant
need not be one. The extra transport-height cost is exactly a factor 2B. -/
theorem projective_prime_rows_of_height {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) {d : ℤ} {q : ℕ} [Fact q.Prime]
    (cert : PolynomialPrimeCertificate
      (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K) (hqN : ¬q∣N)
    (g : G) {M : IntegerMatrix2} {B : ℝ} (hM : IntegerAction g M)
    (hB : 0≤B) (hb : MatrixEntryBound M B)
    (L : ℝ) (hheight : 2*(localTransportConstant P a i*(q : ℝ)^4)*B≤L) :
    ∃ j : Fin (q-1), ∀ (w : ℂ) (_hw : w*w=1)
      {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
      (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
      ‖compactAction hs hε t x
        ((symbol (integralLabel (family N a i))-1)*symbol g) v‖≤
      (integerCompactDistortion L H)^t*
        (7*‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (commonImageRegion_compact L H hY) hε t x v‖+
          ‖(w • compact (matrixBranch N q (NeZero.pos N) hqN j)
              (commonImageRegion_compact L H hY) hε t x-
            compact identityBranch (commonImageRegion_compact L H hY) hε t x) v‖) := by
  let H₀ := preparationMatrix P a i
  let C : SL(2,ℤ) := ⟨lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
    upperUnipotent cert.l,cert.canonical_det⟩
  let U := upperSL (-cert.l)
  have hL0 : 0≤localTransportConstant P a i*(q : ℝ)^4 :=
    mul_nonneg (localTransportConstant_pos P a i).le (by positivity)
  have hL : 0≤L := (mul_nonneg (mul_nonneg (by norm_num) hL0) hB).trans hheight
  have push (A : IntegerMatrix2) (hA : MatrixEntryBound A (localTransportConstant P a i*(q : ℝ)^4)) :
      MatrixEntryBound (A*M) L := entry_bound_mono (matrix_entry_bound_mul hL0 hA hb) hheight
  have act (β : SL(2,ℤ)) : IntegerAction (integralLabel β*g) (β.val*M) :=
    (integerAction_integralLabel β).mul hM
  have actV (r : ℤ) (β : SL(2,ℤ)) :
      IntegerAction (integralLabel (lowerSL N r)*(integralLabel β*g)) ((lowerSL N r*β).val*M) := by
    simpa only [integralLabel.map_mul,mul_assoc] using act (lowerSL N r*β)
  obtain ⟨j,hj,hfirstB,hfirstVB,⟨A,hA,hAB⟩,h0B,hrB,hFB,hnB⟩ :=
    certificate_common_heights P a i cert hqN
  have hcan : IntegerAction
      ((defectLabel N q (NeZero.pos N) hqN j)⁻¹*(integralLabel U*g)) (A*M) := by
    simpa only [mul_assoc] using hA.mul hM
  refine ⟨j,?_⟩
  intro w hw s hs ε Y H hε hY hre hlo him t x v
  have hwNorm : ‖w‖*‖w‖=1 := by simpa only [norm_mul,norm_one] using congrArg norm hw
  have hw1 : ‖w‖=1 := by nlinarith [norm_nonneg w]
  have hfirst := projective_lower_fricke_common_bound N (NeZero.pos N) 1 w
    (integralLabel (C*U)*g) (act (C*U)) (actV 1 (C*U)) hL (push _ hfirstB) (push _ hfirstVB)
    hY hs hε hre hlo him t x v
  have hsecond := projective_canonical_common_norm N q (NeZero.pos N) hqN j w hw
    (integralLabel U*g) hcan hL (push _ hAB) hY hs hε hre hlo him t x v
  rw [hw1,one_mul] at hsecond
  have hleft := congrArg (fun γ : SL(2,ℤ) =>
    ‖compactAction hs hε t x ((symbol (integralLabel γ)-1)*symbol (integralLabel U*g)) v‖) hj
  have hsecond' := hleft.trans_le hsecond
  have hthird := projective_lower_fricke_common_bound N (NeZero.pos N) cert.r w
    (integralLabel H₀*g) (act H₀) (actV cert.r H₀) hL (push _ h0B) (push _ hrB)
    hY hs hε hre hlo him t x v
  have hfourth := projective_lower_fricke_common_bound N (NeZero.pos N) (P.n a i) w
    (integralLabel (family N a i)*g) (act (family N a i)) (actV (P.n a i) (family N a i))
    hL (push _ hFB) (push _ hnB) hY hs hε hre hlo him t x v
  have heq := congrArg (fun T : Space →L[ℂ] Space => T v)
    (projective_prime_defect P a i cert g hs hε t x)
  rw [heq,_root_.sub_apply,_root_.sub_apply,_root_.add_apply]
  have triangle (u v w z : Space) : ‖u+v-w-z‖≤‖u‖+‖v‖+‖w‖+‖z‖ := by
    calc
      _ ≤ ‖u+v-w‖+‖z‖ := norm_sub_le _ _
      _ ≤ (‖u+v‖+‖w‖)+‖z‖ := add_le_add (norm_sub_le (u+v) w) le_rfl
      _ ≤ _ := add_le_add (add_le_add (norm_add_le u v) le_rfl) le_rfl
  exact ((triangle _ _ _ _).trans
    (add_le_add (add_le_add (add_le_add hfirst hsecond') hthird) hfourth)).trans_eq (by ring)

#print axioms projective_prime_rows_of_height
end QuantitativeEulerEndpointPrepared
