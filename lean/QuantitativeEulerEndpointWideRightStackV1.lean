module

public import QuantitativeEulerEndpointWideRightRowsV1
public import QuantitativeEulerEndpointWideFreshRegionV1

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

/-- Right-multiplied certificates use the actual shifted individual rows
with their exact averaging cutoffs. -/
theorem compact_prime_wide_right_fresh_rows_of_height {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) {d : ℤ} {q : ℕ} [Fact q.Prime]
    (cert : PolynomialPrimeCertificate
      (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K) (hqN : ¬q∣N)
    (β : SL(2,ℤ)) {B : ℝ} (hB : 0≤B) (hβ : MatrixEntryBound β.val B)
    (L : ℝ) (hheight : 2*(localTransportConstant P a i*(q : ℝ)^4)*B≤L) :
    ∃ j : Fin (q-1), ∀ (w : ℂ) (_hw : w*w=1)
      {s : Set ℍ} (hs : IsCompact s) {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
      (_hre : ∀ z∈s, |z.re|≤R) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
      ‖matrixCompactAction hs hε t x
        ((matrixSymbol (family N a i).val-1)*matrixSymbol β.val) v‖≤
      (wideDistortion L R H)^t*
        (7*‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (wideFreshRegion_compact L R H hY) hε t x v‖+
          ‖AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
            (wideFreshRegion_compact L R H hY) hε t j x v‖) := by
  obtain ⟨j,hj⟩ := compact_prime_wide_right_rows_of_height P a i cert hqN β hB hβ L hheight
  refine ⟨j,?_⟩
  intro w hw s hs ε R Y H hε hY hre hlo him t x v
  have h := hj w hw hs hε hY hre hlo him t x v
  have hfricke := fricke_row_restrict_norm N (NeZero.pos N) w
    (wideImageRegion_compact L R H hY) (wideFreshRegion_compact L R H hY)
    (wide_subset_fresh L R Y H) hε t x v
  have hprime := prime_residual_restrict_norm N q (NeZero.pos N) hqN j w
    (wideImageRegion_compact L R H hY)
    (shifted_compact (parameter q j) (wideFreshRegion_compact L R H hY))
    (wide_subset_fresh_shifted L R Y H q j) hε t x v
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hfricke (by norm_num)) hprime)
    (by unfold wideDistortion; positivity))

/-- The right-multiplied prepared residual is controlled by the actual
individual-row stack with explicit squared coefficient 50. -/
theorem compact_prime_wide_right_stack_of_height {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) {d : ℤ} {q : ℕ} [Fact q.Prime]
    (cert : PolynomialPrimeCertificate
      (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K) (hqN : ¬q∣N)
    (β : SL(2,ℤ)) {B : ℝ} (hB : 0≤B) (hβ : MatrixEntryBound β.val B)
    (L : ℝ) (hheight : 2*(localTransportConstant P a i*(q : ℝ)^4)*B≤L)
    (w : ℂ) (hw : w*w=1) {s : Set ℍ} (hs : IsCompact s) {ε R Y H : ℝ}
    (hε : 0<ε) (hY : 0<Y) (hre : ∀ z∈s, |z.re|≤R)
    (hlo : ∀ z∈s, Y≤z.im) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖matrixCompactAction hs hε t x
      ((matrixSymbol (family N a i).val-1)*matrixSymbol β.val) v‖^2≤
    50*((wideDistortion L R H)^t)^2*
      (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (wideFreshRegion_compact L R H hY) hε t x v‖^2+
        ‖stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
          (wideFreshRegion_compact L R H hY) hε t j x) v‖^2) := by
  obtain ⟨j,hj⟩ := compact_prime_wide_right_fresh_rows_of_height P a i cert hqN β hB hβ L hheight
  have h := hj w hw hs hε hY hre hlo him t x v
  have hrow := PiLp.norm_apply_le (p := 2)
    (stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
      (wideFreshRegion_compact L R H hY) hε t j x) v) j
  have hD : 0≤(wideDistortion L R H)^t := by
    unfold wideDistortion; positivity
  have hbound := h.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl hrow) hD)
  have scalar (a D F R : ℝ) (ha : 0≤a) (hD : 0≤D) (hF : 0≤F) (hR : 0≤R)
      (h : a≤D*(7*F+R)) : a^2≤50*D^2*(F^2+R^2) := by
    have hs := sq_le_sq₀ ha (mul_nonneg hD (by positivity)) |>.2 h
    have hc : (7*F+R)^2≤50*(F^2+R^2) := by nlinarith [sq_nonneg (F-7*R)]
    have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg D)
    nlinarith
  exact scalar _ _ _ _ (norm_nonneg _) hD (norm_nonneg _) (norm_nonneg _) hbound

#print axioms compact_prime_wide_right_fresh_rows_of_height
#print axioms compact_prime_wide_right_stack_of_height
end QuantitativeEulerEndpointPrepared
