module

public import QuantitativeEulerDensityPreparedV1
public import QuantitativeArithmeticShiftedCertificateDefectV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open QuantitativeArithmetic QuantitativeHolomorphic

variable {E : Type*} [AddCommGroup E]

def rightTranslate (F : MatrixAlgebra →+ E) (M : IntegerMatrix2) : MatrixAlgebra →+ E :=
  F.comp (AddMonoidHom.mulRight (matrixSymbol M))

theorem rightTranslate_periodic (F : MatrixAlgebra →+ E)
    (hperiod : ∀ (j : ℤ) (M : IntegerMatrix2),
      F (matrixSymbol (upperUnipotent j)*matrixSymbol M)=F (matrixSymbol M))
    (M : IntegerMatrix2) (j : ℤ) (A : IntegerMatrix2) :
    rightTranslate F M (matrixSymbol (upperUnipotent j)*matrixSymbol A)=
      rightTranslate F M (matrixSymbol A) := by
  change F ((matrixSymbol (upperUnipotent j)*matrixSymbol A)*matrixSymbol M)=
    F (matrixSymbol A*matrixSymbol M)
  simpa only [matrixSymbol_mul,mul_assoc] using hperiod j (A*M)

/-- Undoing the fixed preparation costs only the fixed lower-unipotent
defect. The upper shear disappears by actual periodicity. -/
theorem Prepared.original_defect {N : ℕ} [NeZero N] {excluded : Finset ℕ} {threshold : ℕ}
    (P : Prepared N excluded threshold) (a : UnitResidue N) (i : Option (Generator N))
    (F : MatrixAlgebra →+ E)
    (hperiod : ∀ (j : ℤ) (M : IntegerMatrix2),
      F (matrixSymbol (upperUnipotent j)*matrixSymbol M)=F (matrixSymbol M)) :
    F (matrixSymbol (family N a i).val)-F 1 =
      F (matrixSymbol (certificateMatrix (P.Q a) (P.B a i) N (P.c a i) (P.D a i)))-F 1 -
        F ((matrixSymbol (lowerUnipotent N (P.n a i))-1)*matrixSymbol (family N a i).val) := by
  have hs : F (matrixSymbol (certificateMatrix (P.Q a) (P.B a i) N (P.c a i) (P.D a i)))=
      F (matrixSymbol (lowerUnipotent N (P.n a i))*matrixSymbol (family N a i).val) := by
    rw [←P.shear a i,matrixSymbol_mul,matrixSymbol_mul,mul_assoc]
    simpa only [matrixSymbol_mul] using hperiod (P.t a i)
      (lowerUnipotent N (P.n a i)*(family N a i).val)
  rw [hs,sub_mul,one_mul,map_sub]
  abel

/-- The actual fixed branch defect is now expressed in its fresh canonical
prime matrix and two lower-unipotent defects. Both lower powers have the
signed telescopes already proved, with variable length O(q) and fixed length
respectively. This identity imposes no modularity or Fricke equation. -/
theorem Prepared.prime_defect {N : ℕ} [NeZero N] {excluded : Finset ℕ} {threshold : ℕ}
    (P : Prepared N excluded threshold) (a : UnitResidue N) (i : Option (Generator N))
    {d q : ℤ} (cert : PolynomialPrimeCertificate
      (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K)
    (F : MatrixAlgebra →+ E)
    (hperiod : ∀ (j : ℤ) (M : IntegerMatrix2),
      F (matrixSymbol (upperUnipotent j)*matrixSymbol M)=F (matrixSymbol M)) :
    let H := certificateMatrix (P.Q a) (P.B a i) N (P.c a i) (P.D a i)
    let C := lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
      upperUnipotent cert.l
    F (matrixSymbol (family N a i).val)-F 1 =
      F ((matrixSymbol (lowerUnipotent N 1)-1)*matrixSymbol C*matrixSymbol (upperUnipotent (-cert.l))) +
      F ((matrixSymbol C-1)*matrixSymbol (upperUnipotent (-cert.l))) -
      F ((matrixSymbol (lowerUnipotent N cert.r)-1)*matrixSymbol H) -
      F ((matrixSymbol (lowerUnipotent N (P.n a i))-1)*matrixSymbol (family N a i).val) := by
  dsimp
  rw [P.original_defect a i F hperiod,cert.periodic_defect_recovery F hperiod]

/-- Exact same-residue cancellation recovers a fixed Γ₁ generator defect
from two prepared branches. The second is evaluated after that generator;
rightTranslate_periodic supplies the required periodicity automatically. -/
theorem generator_defect (N : ℕ) [NeZero N] (a : UnitResidue N) (γ : Generator N)
    (F : MatrixAlgebra →+ E) :
    F (matrixSymbol γ.val.val)-F 1 =
      (F (matrixSymbol (family N a (some γ)).val)-F 1) -
        (rightTranslate F γ.val.val (matrixSymbol (family N a none).val)-
          rightTranslate F γ.val.val 1) := by
  change F (matrixSymbol γ.val.val)-F 1 =
    (F (matrixSymbol ((unitLift N a*γ.val).val))-F 1) -
      (F (matrixSymbol (unitLift N a).val*matrixSymbol γ.val.val)-F (1*matrixSymbol γ.val.val))
  rw [one_mul,←matrixSymbol_mul]
  change F (matrixSymbol γ.val.val)-F 1 =
    (F (matrixSymbol ((unitLift N a).val*γ.val.val))-F 1) -
      (F (matrixSymbol ((unitLift N a).val*γ.val.val))-F (matrixSymbol γ.val.val))
  abel

#print axioms rightTranslate_periodic
#print axioms Prepared.original_defect
#print axioms Prepared.prime_defect
#print axioms generator_defect
end QuantitativeEulerDensityGenerators
