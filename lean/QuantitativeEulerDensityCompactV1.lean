module

public import QuantitativeEulerDensityDecodeV1
public import QuantitativeEulerDiamondRegionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open AsymptoticCongruenceLabels AsymptoticOrbitDecode QuantitativeEulerDiamondDecode
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactBranch (cap)
open scoped MatrixGroups Classical

/-- Bounded compact realization of the additive integer matrix algebra.
Only determinant-one symbols enter; each is represented by the actual
integral projective branch operator. -/
def matrixCompactAction {s : Set ℍ} (hs : IsCompact s) {ε : ℝ}
    (hε : 0<ε) (t : ℕ) (x : ℍ) : MatrixAlgebra →+ (Space →L[ℂ] Space) :=
  (Finsupp.linearCombination ℤ (fun M : IntegerMatrix2 =>
    if h : M.det=1 then compactAction hs hε t x (symbol (integralLabel (⟨M,h⟩ : SL(2,ℤ))))
    else 0)).toAddMonoidHom.comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

theorem matrixCompactAction_symbol {s : Set ℍ} (hs : IsCompact s) {ε : ℝ}
    (hε : 0<ε) (t : ℕ) (x : ℍ) (M : IntegerMatrix2) :
    matrixCompactAction hs hε t x (matrixSymbol M)=
      if h : M.det=1 then compactAction hs hε t x (symbol (integralLabel (⟨M,h⟩ : SL(2,ℤ))))
      else 0 := by
  simp [matrixCompactAction,matrixSymbol]

theorem matrixCompactAction_integral {s : Set ℍ} (hs : IsCompact s) {ε : ℝ}
    (hε : 0<ε) (t : ℕ) (x : ℍ) (γ : SL(2,ℤ)) :
    matrixCompactAction hs hε t x (matrixSymbol γ.val)=
      compactAction hs hε t x (symbol (integralLabel γ)) := by
  rw [matrixCompactAction_symbol,dite_eq_left γ.property]
  rfl

/-- Exact coordinate formula, retaining the actual strip fold and cap. -/
theorem matrixCompactAction_decode {s : Set ℍ} (hs : IsCompact s) {ε : ℝ}
    (hε : 0<ε) (t : ℕ) (x : ℍ) (A : MatrixAlgebra) (v : Space) (a : G) :
    matrixCompactAction hs hε t x A v a=
      if a • x∈s then (cap ε t (a • x) : ℂ)*matrixDecodedEvaluation ε t x v a A else 0 := by
  induction A using MonoidAlgebra.induction_on with
  | of M =>
    change matrixCompactAction hs hε t x (matrixSymbol M) v a=
      if a • x∈s then (cap ε t (a • x) : ℂ)*matrixDecodedEvaluation ε t x v a (matrixSymbol M) else 0
    rw [matrixCompactAction_symbol]
    unfold matrixDecodedEvaluation
    rw [matrixEvaluation_symbol]
    by_cases hM : M.det=1
    · rw [dite_eq_left hM,dite_eq_left hM,compactAction_decode,decodedEvaluation_symbol]
    · simp only [dite_eq_right hM,_root_.zero_apply,lp.coeFn_zero,Pi.zero_apply,mul_zero,ite_self]
  | add A B hA hB =>
    simp only [map_add,_root_.add_apply,lp.coeFn_add,Pi.add_apply,hA,hB]
    by_cases ha : a • x∈s <;> simp [ha,mul_add]
  | smul c A hA =>
    simp only [map_zsmul,_root_.smul_apply]
    by_cases ha : a • x∈s <;> simp [ha,hA,zsmul_eq_mul,mul_left_comm]

theorem matrixCompactAction_periodic {s : Set ℍ} (hs : IsCompact s) {ε : ℝ}
    (hε : 0<ε) (t : ℕ) (x : ℍ) (j : ℤ) (M : IntegerMatrix2) :
    matrixCompactAction hs hε t x (matrixSymbol (upperUnipotent j)*matrixSymbol M)=
      matrixCompactAction hs hε t x (matrixSymbol M) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext a
  rw [matrixCompactAction_decode,matrixCompactAction_decode,matrixDecodedEvaluation_periodic]

/-- The original fresh-prime certificate identity is now an equality of
actual bounded compact operators, without a periodicity or vector-kernel
premise. This is the starting point for quantitative signed-telescope bounds. -/
theorem Prepared.compact_prime_defect {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) {d q : ℤ}
    (cert : PolynomialPrimeCertificate
      (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    let F := matrixCompactAction hs hε t x
    let H := certificateMatrix (P.Q a) (P.B a i) N (P.c a i) (P.D a i)
    let C := lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*upperUnipotent cert.l
    F (matrixSymbol (family N a i).val)-F 1 =
      F ((matrixSymbol (lowerUnipotent N 1)-1)*matrixSymbol C*matrixSymbol (upperUnipotent (-cert.l))) +
      F ((matrixSymbol C-1)*matrixSymbol (upperUnipotent (-cert.l))) -
      F ((matrixSymbol (lowerUnipotent N cert.r)-1)*matrixSymbol H) -
      F ((matrixSymbol (lowerUnipotent N (P.n a i))-1)*matrixSymbol (family N a i).val) :=
  P.prime_defect a i cert (matrixCompactAction hs hε t x)
    (matrixCompactAction_periodic hs hε t x)

#print axioms matrixCompactAction_decode
#print axioms matrixCompactAction_periodic
#print axioms Prepared.compact_prime_defect
end QuantitativeEulerDensityGenerators
