module

public import QuantitativeHolomorphicObservationRowBoundsV1
public import QuantitativeHolomorphicCertificateHeightV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane AsymptoticFiniteBranch AsymptoticCompactObservationCount
open AsymptoticSectorSigns FinitenessCertificate FinitenessGlobalHeight

def rowMatrixBase {N : ℕ} (_hN : 0<N) (r : Row N) : ℝ :=
  rowArithmeticHeight r

theorem rowMatrixBase_one_le {N : ℕ} (hN : 0<N) (r : Row N) :
    1 ≤ rowMatrixBase hN r := rowArithmeticHeight_one_le hN r

def quantifiedRowLength {N : ℕ} (hN : 0<N) (r : Row N) (Y H : ℝ) : ℕ :=
  rowBranchCount r*(2*integerCompactCutoff (rowMatrixBase hN r) Y H+1)

def quantifiedRowMass {N : ℕ} (hN : 0<N) (r : Row N) (Y H : ℝ) (t : ℕ) : ℝ :=
  (rowBranchCount r:ℝ)*(2*(integerCompactCutoff (rowMatrixBase hN r) Y H:ℝ)+1)*
    (integerCompactDistortion (rowMatrixBase hN r) H)^t

def quantifiedRowHeight {N : ℕ} (hN : 0<N) (r : Row N) (Y H : ℝ) : ℝ :=
  4*(1+(integerCompactCutoff (rowMatrixBase hN r) Y H:ℝ))*rowMatrixBase hN r

theorem quantifiedRowHeight_nonneg {N : ℕ} (hN : 0<N) (r : Row N) (Y H : ℝ) :
    0 ≤ quantifiedRowHeight hN r Y H := by
  unfold quantifiedRowHeight
  have hb := rowMatrixBase_one_le hN r
  positivity

def quantifiedRowExpression {N : ℕ} (hN : 0<N) (r : Row N) (e : Sector N)
    {s : Set UpperHalfPlane} (hs : IsCompact s) {Y H ε : ℝ} (hY : 0<Y) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H) (t : ℕ) : Expression :=
  Classical.choose (rowExpression_explicit_integer_bounds hN r
    e hs hY hε hre hlo hhi t)

theorem quantifiedRowExpression_spec {N : ℕ} (hN : 0<N) (r : Row N) (e : Sector N)
    {s : Set UpperHalfPlane} (hs : IsCompact s) {Y H ε : ℝ} (hY : 0<Y) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H) (t : ℕ) :
    let E := quantifiedRowExpression hN r e hs hY hε hre hlo hhi t
    (∀ m, holomorphicSum E m = holomorphicSum (rowExpression hN r e hs hε t) m) ∧
    (∀ z, regularSum E z = regularSum (rowExpression hN r e hs hε t) z) ∧
    E.length = quantifiedRowLength hN r Y H ∧
    expressionBound E ≤ quantifiedRowMass hN r Y H t ∧
    ExpressionMatrixBound E (quantifiedRowHeight hN r Y H) :=
  Classical.choose_spec (rowExpression_explicit_integer_bounds hN r
    e hs hY hε hre hlo hhi t)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

/-- The full counting filter with quantitative row representatives. Its
operators are exactly the original ones; only the finite branch expansion
and its explicit geometric certificates change. -/
def quantifiedCountFilterExpression (hN : 0<N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    {L U : ℝ} (hL : 0<L)
    (hre : ∀ i z, z∈s i → |z.re|≤1) (hlo : ∀ i z, z∈s i → L≤z.im)
    (hhi : ∀ i z, z∈s i → z.im≤U) (Y : ℝ) (j J n d : ℕ) : Expression :=
  observationFilterExpression qs
    (fun i => quantifiedRowExpression hN (r i) e (hs i) hL
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos (hre i) (hlo i) (hhi i)
      ((AsymptoticReconstructedCount.parameters A P).s+4))
    (normalizedReconstructionExpression (scaledCutCountExpression A hN P e Y j J) n)
    (fun i => rowBound hN (r i) (hs i) (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4)) d

theorem quantifiedCountFilterExpression_physical (hN : 0<N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    {L U : ℝ} (hL : 0<L)
    (hre : ∀ i z, z∈s i → |z.re|≤1) (hlo : ∀ i z, z∈s i → L≤z.im)
    (hhi : ∀ i z, z∈s i → z.im≤U) (Y : ℝ) (j J n d m : ℕ) :
    holomorphicSum (quantifiedCountFilterExpression A hN P e qs r s hs hL hre hlo hhi Y j J n d) m =
      holomorphicSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) m := by
  rw [quantifiedCountFilterExpression, countObservationFilterExpression,
    holomorphicSum_observationFilterExpression, holomorphicSum_observationFilterExpression]
  have he : (fun i => holomorphicSum (quantifiedRowExpression hN (r i) e (hs i) hL
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos (hre i) (hlo i) (hhi i)
      ((AsymptoticReconstructedCount.parameters A P).s+4)) m) =
      fun i => holomorphicSum (rowExpression hN (r i) e (hs i)
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+4)) m := by
    funext i
    exact (quantifiedRowExpression_spec hN (r i) e (hs i) hL _ (hre i) (hlo i) (hhi i) _).1 m
  rw [he]

theorem quantifiedCountFilterExpression_regular (hN : 0<N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    {L U : ℝ} (hL : 0<L)
    (hre : ∀ i z, z∈s i → |z.re|≤1) (hlo : ∀ i z, z∈s i → L≤z.im)
    (hhi : ∀ i z, z∈s i → z.im≤U) (Y : ℝ) (j J n d : ℕ) (z : UpperHalfPlane) :
    regularSum (quantifiedCountFilterExpression A hN P e qs r s hs hL hre hlo hhi Y j J n d) z =
      regularSum (countObservationFilterExpression A hN P e qs r s hs Y j J n d) z := by
  rw [quantifiedCountFilterExpression, countObservationFilterExpression,
    regularSum_observationFilterExpression, regularSum_observationFilterExpression]
  have he : (fun i => regularSum (quantifiedRowExpression hN (r i) e (hs i) hL
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos (hre i) (hlo i) (hhi i)
      ((AsymptoticReconstructedCount.parameters A P).s+4)) z) =
      fun i => regularSum (rowExpression hN (r i) e (hs i)
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+4)) z := by
    funext i
    exact (quantifiedRowExpression_spec hN (r i) e (hs i) hL _ (hre i) (hlo i) (hhi i) _).2.1 z
  rw [he]

#print axioms quantifiedRowExpression_spec
#print axioms quantifiedCountFilterExpression_physical
#print axioms quantifiedCountFilterExpression_regular

end QuantitativeHolomorphic
