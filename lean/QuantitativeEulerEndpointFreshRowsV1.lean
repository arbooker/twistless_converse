module

public import QuantitativeEulerEndpointFreshRegionV1
public import AsymptoticObservationStackV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeHolomorphic QuantitativeArithmetic
open QuantitativeEulerDiamondDecode QuantitativeEulerDensityGenerators
open AsymptoticFreshCompactDefects AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open AsymptoticObservationStack AsymptoticCompactFamilyTranslation
open scoped Classical MatrixGroups

/-- Every certificate uses the same fixed preparation constant and the
actual shifted individual row occurring in fresh-prime averaging. -/
theorem compact_prime_fresh_rows_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) {d : ℤ} {q : ℕ} [Fact q.Prime]
    (cert : PolynomialPrimeCertificate
      (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K) (hqN : ¬q∣N) :
    let L := transportConstant P*(q : ℝ)^4
    ∃ j : Fin (q-1), ∀ (w : ℂ) (_hw : w*w=1)
      {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
      (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
      ‖(matrixCompactAction hs hε t x (matrixSymbol (family N a i).val)-
        matrixCompactAction hs hε t x 1) v‖≤
      (integerCompactDistortion L H)^t*
        (7*‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖+
          ‖AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
            (freshObservationRegion_compact L H hY) hε t j x v‖) := by
  let L := transportConstant P*(q : ℝ)^4
  have hheight : localTransportConstant P a i*(q : ℝ)^4≤L :=
    mul_le_mul_of_nonneg_right (localTransportConstant_le P a i) (by positivity)
  obtain ⟨j,hj⟩ := compact_prime_common_rows_of_height P a i cert hqN L hheight
  refine ⟨j,?_⟩
  intro w hw s hs ε Y H hε hY hre hlo him t x v
  have h := hj w hw hs hε hY hre hlo him t x v
  have hfricke := fricke_row_restrict_norm N (NeZero.pos N) w
    (commonImageRegion_compact L H hY) (freshObservationRegion_compact L H hY)
    (common_subset_fresh L Y H) hε t x v
  have hprime := prime_residual_restrict_norm N q (NeZero.pos N) hqN j w
    (commonImageRegion_compact L H hY)
    (shifted_compact (parameter q j) (freshObservationRegion_compact L H hY))
    (common_subset_fresh_shifted L Y H q j) hε t x v
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hfricke (by norm_num)) hprime)
    (by unfold integerCompactDistortion; positivity))

/-- The actual prepared residual is controlled by the full individual-row
stack, with explicit squared coefficient 50 and uniform C(P) q^4 height. -/
theorem compact_prime_fresh_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) {d : ℤ} {q : ℕ} [Fact q.Prime]
    (cert : PolynomialPrimeCertificate
      (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K) (hqN : ¬q∣N)
    (w : ℂ) (hw : w*w=1) {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ}
    (hε : 0<ε) (hY : 0<Y) (hre : ∀ z∈s, |z.re|≤1)
    (hlo : ∀ z∈s, Y≤z.im) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    let L := transportConstant P*(q : ℝ)^4
    ‖(matrixCompactAction hs hε t x (matrixSymbol (family N a i).val)-
      matrixCompactAction hs hε t x 1) v‖^2≤
    50*((integerCompactDistortion L H)^t)^2*
      (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
        ‖stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
          (freshObservationRegion_compact L H hY) hε t j x) v‖^2) := by
  obtain ⟨j,hj⟩ := compact_prime_fresh_rows_bound P a i cert hqN
  have h := hj w hw hs hε hY hre hlo him t x v
  have hrow := PiLp.norm_apply_le (p := 2)
    (stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
      (freshObservationRegion_compact (transportConstant P*(q : ℝ)^4) H hY) hε t j x) v) j
  have hD : 0≤(integerCompactDistortion (transportConstant P*(q : ℝ)^4) H)^t := by
    unfold integerCompactDistortion; positivity
  have hbound := h.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl hrow) hD)
  have scalar (a D F R : ℝ) (ha : 0≤a) (hD : 0≤D) (hF : 0≤F) (hR : 0≤R)
      (h : a≤D*(7*F+R)) : a^2≤50*D^2*(F^2+R^2) := by
    have hs := sq_le_sq₀ ha (mul_nonneg hD (by positivity)) |>.2 h
    have hc : (7*F+R)^2≤50*(F^2+R^2) := by nlinarith [sq_nonneg (F-7*R)]
    have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg D)
    nlinarith
  exact scalar _ _ _ _ (norm_nonneg _) hD (norm_nonneg _) (norm_nonneg _) hbound

/-- Good-prime observability uses the certificates supplied by the actual
preparation. No additional divisor or matrix-certificate hypothesis remains. -/
theorem good_prime_fresh_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (q : ℕ) [Fact q.Prime] (hqGood : P.Good q) :
    ∃ hqN : ¬q∣N, ∃ a : UnitResidue N, Nat.ModEq N q a.val.val ∧
      ∀ (i : Option (Generator N)) (w : ℂ) (_hw : w*w=1)
        {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      let L := transportConstant P*(q : ℝ)^4
      ‖(matrixCompactAction hs hε t x (matrixSymbol (family N a i).val)-
        matrixCompactAction hs hε t x 1) v‖^2≤
      50*((integerCompactDistortion L H)^t)^2*
        (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
          ‖stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
            (freshObservationRegion_compact L H hY) hε t j x) v‖^2) := by
  obtain ⟨_hex,hqN,_hthreshold,a,hqa,hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,a,hqa,?_⟩
  intro i w hw s hs ε Y H hε hY hre hlo him t x v
  obtain ⟨d,⟨cert⟩⟩ := hcert i
  exact compact_prime_fresh_stack_bound P a i cert hqN w hw hs hε hY hre hlo him t x v

#print axioms good_prime_fresh_stack_bound
#print axioms compact_prime_fresh_rows_bound
#print axioms compact_prime_fresh_stack_bound
end QuantitativeEulerEndpointPrepared
