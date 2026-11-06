module

public import QuantitativeEulerEndpointImageV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeHolomorphic QuantitativeArithmetic
open QuantitativeEulerDiamondDecode QuantitativeEulerDensityGenerators
open QuantitativeArithmeticDiamondLabels AsymptoticCongruenceLabels
open AsymptoticFreshAveraging
open scoped Classical MatrixGroups

theorem entry_bound_mono {M : IntegerMatrix2} {B C : ℝ}
    (h : MatrixEntryBound M B) (hBC : B≤C) : MatrixEntryBound M C :=
  fun i j => (h i j).trans hBC

theorem lower_product_entry_bound (N : ℕ) (r : ℤ) (β : SL(2,ℤ)) {B : ℝ}
    (hb : MatrixEntryBound β.val B) :
    MatrixEntryBound (lowerSL N r*β).val (2*(1+(N : ℝ)*|(r : ℝ)|)*B) := by
  have hV : MatrixEntryBound (lowerSL N r).val (1+(N : ℝ)*|(r : ℝ)|) := by
    change MatrixEntryBound (lowerUnipotent (N : ℤ) r) _
    simpa only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)] using
      lowerUnipotent_entry_bound (N : ℤ) r
  exact matrix_entry_bound_mul (by positivity) hV hb

def preparationMatrix {N : ℕ} [NeZero N] {excluded : Finset ℕ} {threshold : ℕ}
    (P : Prepared N excluded threshold) (a : UnitResidue N) (i : Option (Generator N)) : SL(2,ℤ) :=
  ⟨certificateMatrix (P.Q a) (P.B a i) N (P.c a i) (P.D a i),
    by rw [certificate_det]; exact P.determinant a i⟩

/-- Depends only on the fixed preparation and its finite generator index,
not on the good prime, its divisor witness, or its certificate choices. -/
def localTransportConstant {N : ℕ} [NeZero N] {excluded : Finset ℕ} {threshold : ℕ}
    (P : Prepared N excluded threshold) (a : UnitResidue N) (i : Option (Generator N)) : ℝ :=
  1+4*(1+(N : ℝ))*P.K*(1+P.K)+
    2*(1+(N : ℝ)*P.K)*fixedMatrixHeight (preparationMatrix P a i).val+
    2*(1+(N : ℝ)*|(P.n a i : ℝ)|)*fixedMatrixHeight (family N a i).val

theorem localTransportConstant_pos {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) : 0<localTransportConstant P a i := by
  have hK := P.K_pos
  have h0 := fixedMatrixHeight_nonneg (preparationMatrix P a i).val
  have hF := fixedMatrixHeight_nonneg (family N a i).val
  unfold localTransportConstant
  positivity

/-- All seven actual multipliers in the prime identity have one O(q^4)
integral height. The inverse branch is composed before its height is taken. -/
theorem certificate_common_heights {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) {d : ℤ} {q : ℕ} [Fact q.Prime]
    (cert : PolynomialPrimeCertificate
      (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K) (hqN : ¬q∣N) :
    let H₀ := preparationMatrix P a i
    let C : SL(2,ℤ) := ⟨lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
      upperUnipotent cert.l,cert.canonical_det⟩
    let U := upperSL (-cert.l)
    let L := localTransportConstant P a i*(q : ℝ)^4
    ∃ j : Fin (q-1), C=swappedCanonical N q hqN j ∧
      MatrixEntryBound (C*U).val L ∧
      MatrixEntryBound (lowerSL N 1*(C*U)).val L ∧
      (∃ M : IntegerMatrix2,
        IntegerAction ((defectLabel N q (NeZero.pos N) hqN j)⁻¹*integralLabel U) M ∧
        MatrixEntryBound M L) ∧
      MatrixEntryBound H₀.val L ∧
      MatrixEntryBound (lowerSL N cert.r*H₀).val L ∧
      MatrixEntryBound (family N a i).val L ∧
      MatrixEntryBound (lowerSL N (P.n a i)*family N a i).val L := by
  let H₀ := preparationMatrix P a i
  let C : SL(2,ℤ) := ⟨lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
    upperUnipotent cert.l,cert.canonical_det⟩
  let U := upperSL (-cert.l)
  let A := 4*(1+(N : ℝ))*P.K*(1+P.K)
  let D := 2*(1+(N : ℝ)*P.K)*fixedMatrixHeight H₀.val
  let E := 2*(1+(N : ℝ)*|(P.n a i : ℝ)|)*fixedMatrixHeight (family N a i).val
  let L := localTransportConstant P a i*(q : ℝ)^4
  have hK := P.K_pos
  have h0 := fixedMatrixHeight_nonneg H₀.val
  have hF := fixedMatrixHeight_nonneg (family N a i).val
  have hA : 0≤A := by dsimp [A]; positivity
  have hD : 0≤D := by dsimp [D]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hAL : A≤localTransportConstant P a i := by
    change A≤1+A+D+E; linarith
  have hDL : D≤localTransportConstant P a i := by
    change D≤1+A+D+E; linarith
  have hEL : E≤localTransportConstant P a i := by
    change E≤1+A+D+E; linarith
  have hq : 1≤q := (Fact.out : q.Prime).one_lt.le
  have hqr : (1 : ℝ)≤q := by exact_mod_cast hq
  have hq2 : (1 : ℝ)≤(q : ℝ)^2 := by nlinarith
  have hq4 : (q : ℝ)≤(q : ℝ)^4 := by nlinarith [sq_nonneg ((q : ℝ)^2-1)]
  have h14 : (1 : ℝ)≤(q : ℝ)^4 := hqr.trans hq4
  have hA4 : A*(q : ℝ)^4≤L := mul_le_mul_of_nonneg_right hAL (by positivity)
  have hD4 : D*(q : ℝ)^4≤L := mul_le_mul_of_nonneg_right hDL (by positivity)
  have hE4 : E*(q : ℝ)^4≤L := mul_le_mul_of_nonneg_right hEL (by positivity)
  have hfirst := certificate_first_transport_height cert P.K_pos.le hq
  have hfirstL : MatrixEntryBound (C*U).val L := entry_bound_mono hfirst
    ((mul_le_mul_of_nonneg_right (show 2*P.K*(1+P.K)≤A by
      dsimp [A]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N)
        (mul_nonneg hK.le (show 0≤1+P.K by linarith))])
      (by positivity)).trans hA4)
  have hsecond := lower_product_entry_bound N 1 (C*U) hfirst
  have hsecondL : MatrixEntryBound (lowerSL N 1*(C*U)).val L := by
    apply entry_bound_mono hsecond
    convert hA4 using 1
    simp [A]
    ring
  obtain ⟨j,hj⟩ := QuantitativeEulerDensityGenerators.PolynomialPrimeCertificate.canonical_eq_observed cert hqN
  have hcan : MatrixEntryBound (swappedCanonical N q hqN j).val (P.K*(q : ℝ)^3) := by
    rw [←hj]; simpa only [Int.cast_natCast] using cert.canonical_height
  obtain ⟨hM,hMb⟩ := inverse_prime_branch_integer_bound N q (NeZero.pos N) hqN j hcan
  have hprod := matrix_entry_bound_mul (by positivity) hMb (certificate_translation_height cert hq)
  have hprodL : MatrixEntryBound
      (((integralFrickeMatrix N).adjugate*(swappedCanonical N q hqN j).val)*U.val) L := by
    apply entry_bound_mono hprod
    convert hA4 using 1
    dsimp [A]
    ring
  have h0D : fixedMatrixHeight H₀.val≤D := by
    dsimp [D]; nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) hK.le]
  have hFE : fixedMatrixHeight (family N a i).val≤E := by
    dsimp [E]; nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (abs_nonneg (P.n a i : ℝ))]
  have h0L : MatrixEntryBound H₀.val L := entry_bound_mono (fixedMatrixHeight_bounds _)
    (h0D.trans ((le_mul_of_one_le_right hD h14).trans hD4))
  have hFL : MatrixEntryBound (family N a i).val L := entry_bound_mono (fixedMatrixHeight_bounds _)
    (hFE.trans ((le_mul_of_one_le_right hE h14).trans hE4))
  have hr : |(cert.r : ℝ)|≤P.K*(q : ℝ) := by simpa only [Int.cast_natCast] using cert.r_bound
  have hrL : MatrixEntryBound (lowerSL N cert.r*H₀).val L := by
    apply entry_bound_mono (lower_product_entry_bound N cert.r H₀ (fixedMatrixHeight_bounds _))
    have hh : 1+(N : ℝ)*|(cert.r : ℝ)|≤(1+(N : ℝ)*P.K)*(q : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) N)]
    calc
      _ ≤ D*(q : ℝ) := by dsimp [D]; nlinarith [mul_le_mul_of_nonneg_right hh h0]
      _ ≤ D*(q : ℝ)^4 := mul_le_mul_of_nonneg_left hq4 hD
      _ ≤ L := hD4
  have hnL : MatrixEntryBound (lowerSL N (P.n a i)*family N a i).val L :=
    entry_bound_mono (lower_product_entry_bound N (P.n a i) (family N a i) (fixedMatrixHeight_bounds _))
      ((le_mul_of_one_le_right hE h14).trans hE4)
  exact ⟨j,hj,hfirstL,hsecondL,⟨_,hM.mul (integerAction_integralLabel U),hprodL⟩,h0L,hrL,hFL,hnL⟩

/-- A single constant for the entire finite prepared family. -/
def transportConstant {N : ℕ} [NeZero N] {excluded : Finset ℕ} {threshold : ℕ}
    (P : Prepared N excluded threshold) : ℝ :=
  1+∑ a : UnitResidue N, ∑ i : Option (Generator N), localTransportConstant P a i

theorem localTransportConstant_le {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) :
    localTransportConstant P a i≤transportConstant P := by
  have hinner := Finset.single_le_sum (fun j _ => (localTransportConstant_pos P a j).le)
    (Finset.mem_univ i)
  have houter : (∑ j, localTransportConstant P a j)≤
      ∑ b : UnitResidue N, ∑ j : Option (Generator N), localTransportConstant P b j := Finset.single_le_sum
    (fun b _ => Finset.sum_nonneg (fun j _ => (localTransportConstant_pos P b j).le))
    (Finset.mem_univ a)
  exact (hinner.trans houter).trans (by unfold transportConstant; linarith)

theorem transportConstant_pos {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold) :
    0<transportConstant P := by
  have hsum := Finset.sum_nonneg (fun a (_ : a∈(Finset.univ : Finset (UnitResidue N))) =>
    Finset.sum_nonneg (fun i (_ : i∈(Finset.univ : Finset (Option (Generator N)))) =>
      (localTransportConstant_pos P a i).le))
  unfold transportConstant
  linarith

#print axioms localTransportConstant_le
#print axioms transportConstant_pos
#print axioms localTransportConstant_pos
#print axioms certificate_common_heights
end QuantitativeEulerEndpointPrepared
