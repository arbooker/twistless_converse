module

public import QuantitativeEulerDensityDefectV1
public import QuantitativeEulerDiamondDecodeV1
public import AsymptoticCongruenceLabelsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open AsymptoticCongruenceLabels AsymptoticOrbitDecode
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups Classical

/-- Extend evaluation of actual integral projective labels additively to
the integer matrix algebra. Non-unimodular symbols are assigned zero;
no multiplicative realization of arbitrary singular matrices is asserted. -/
def matrixEvaluation (f : AsymptoticRationalGroup.Group → ℂ) : MatrixAlgebra →+ ℂ :=
  (Finsupp.linearCombination ℤ (fun M : IntegerMatrix2 =>
    if h : M.det=1 then f (integralLabel (⟨M,h⟩ : SL(2,ℤ))) else 0)).toAddMonoidHom.comp
      MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

theorem matrixEvaluation_symbol (f : AsymptoticRationalGroup.Group → ℂ)
    (M : IntegerMatrix2) :
    matrixEvaluation f (matrixSymbol M)=
      if h : M.det=1 then f (integralLabel (⟨M,h⟩ : SL(2,ℤ))) else 0 := by
  simp [matrixEvaluation,matrixSymbol]

theorem matrixEvaluation_integral (f : AsymptoticRationalGroup.Group → ℂ)
    (γ : SL(2,ℤ)) : matrixEvaluation f (matrixSymbol γ.val)=f (integralLabel γ) := by
  rw [matrixEvaluation_symbol,dite_eq_left γ.property]
  rfl

/-- The decoded strip vector automatically supplies the periodicity
required by the prepared arithmetic certificates, for every matrix symbol.
There is no approximate modularity premise on the vector. -/
def matrixDecodedEvaluation (ε : ℝ) (t : ℕ) (x : ℍ) (v : Space)
    (a : AsymptoticRationalGroup.Group) : MatrixAlgebra →+ ℂ :=
  matrixEvaluation (fun g => decode ε t x v (g*a))

theorem matrixDecodedEvaluation_periodic (ε : ℝ) (t : ℕ) (x : ℍ) (v : Space)
    (a : AsymptoticRationalGroup.Group) (j : ℤ) (M : IntegerMatrix2) :
    matrixDecodedEvaluation ε t x v a
      (matrixSymbol (upperUnipotent j)*matrixSymbol M)=
      matrixDecodedEvaluation ε t x v a (matrixSymbol M) := by
  rw [←matrixSymbol_mul]
  unfold matrixDecodedEvaluation
  rw [matrixEvaluation_symbol,matrixEvaluation_symbol]
  have hu : (upperUnipotent j).det=1 := (upperSL j).property
  have hd : (upperUnipotent j*M).det=M.det := by rw [Matrix.det_mul,hu,one_mul]
  by_cases hM : M.det=1
  · rw [dite_eq_left (hd.trans hM),dite_eq_left hM]
    have hl := integralLabel.map_mul (upperSL j) (⟨M,hM⟩ : SL(2,ℤ))
    rw [upper_label] at hl
    change integralLabel (⟨upperUnipotent j*M,hd.trans hM⟩ : SL(2,ℤ))=_ at hl
    rw [hl,mul_assoc]
    exact decode_periodic ε t x v (integralLabel ⟨M,hM⟩*a) j
  · rw [dite_eq_right (fun h => hM (hd.symm.trans h)),dite_eq_right hM]

/-- The preparation identity now applies to every actual decoded orbit
vector, with its periodicity discharged by the strip fold. -/
theorem Prepared.decoded_original_defect {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N))
    (ε : ℝ) (t : ℕ) (x : ℍ) (v : Space) (g : AsymptoticRationalGroup.Group) :
    let F := matrixDecodedEvaluation ε t x v g
    F (matrixSymbol (family N a i).val)-F 1 =
      F (matrixSymbol (certificateMatrix (P.Q a) (P.B a i) N (P.c a i) (P.D a i)))-F 1 -
        F ((matrixSymbol (lowerUnipotent N (P.n a i))-1)*matrixSymbol (family N a i).val) :=
  P.original_defect a i (matrixDecodedEvaluation ε t x v g)
    (matrixDecodedEvaluation_periodic ε t x v g)

/-- The full fresh-prime defect identity acts on arbitrary decoded vectors.
The certificate is the concrete arithmetic data supplied simultaneously by
Prepared.prime_data; no equation or invariance of the vector is required. -/
theorem Prepared.decoded_prime_defect {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) {d q : ℤ}
    (cert : PolynomialPrimeCertificate
      (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K)
    (ε : ℝ) (t : ℕ) (x : ℍ) (v : Space) (g : AsymptoticRationalGroup.Group) :
    let F := matrixDecodedEvaluation ε t x v g
    let H := certificateMatrix (P.Q a) (P.B a i) N (P.c a i) (P.D a i)
    let C := lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*upperUnipotent cert.l
    F (matrixSymbol (family N a i).val)-F 1 =
      F ((matrixSymbol (lowerUnipotent N 1)-1)*matrixSymbol C*matrixSymbol (upperUnipotent (-cert.l))) +
      F ((matrixSymbol C-1)*matrixSymbol (upperUnipotent (-cert.l))) -
      F ((matrixSymbol (lowerUnipotent N cert.r)-1)*matrixSymbol H) -
      F ((matrixSymbol (lowerUnipotent N (P.n a i))-1)*matrixSymbol (family N a i).val) :=
  P.prime_defect a i cert (matrixDecodedEvaluation ε t x v g)
    (matrixDecodedEvaluation_periodic ε t x v g)

#print axioms Prepared.decoded_prime_defect

#print axioms matrixDecodedEvaluation_periodic
#print axioms Prepared.decoded_original_defect
end QuantitativeEulerDensityGenerators
