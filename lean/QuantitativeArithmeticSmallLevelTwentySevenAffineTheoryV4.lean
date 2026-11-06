module

public import QuantitativeArithmeticQuadraticMatricesTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenAffineCertificateV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenAffine. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenAffineMatricesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenAffine
open Matrix UpperHalfPlane SmallLevelNormalized QuantitativeArithmeticQuadraticMatrices
open scoped MatrixGroups ModularForm

def rightMatrix (i : Fin 45) : Matrix (Fin 2) (Fin 2) ℤ :=
  match i.val with
  | 0 => !![1,-1;3,-1]
  | 1 => !![1,0;0,2]
  | 2 => !![1,0;3,1]
  | 3 => !![1,1;0,2]
  | 4 => !![2,0;-3,1]
  | 5 => !![2,0;6,1]
  | 6 => !![2,1;-6,-2]
  | 7 => !![2,1;0,1]
  | 8 => !![2,1;6,4]
  | 9 => !![2,2;-3,-2]
  | 10 => !![2,2;6,7]
  | 11 => !![2,3;-6,-8]
  | 12 => !![2,4;-3,-5]
  | 13 => !![2,4;0,1]
  | 14 => !![2,5;-6,-14]
  | 15 => !![4,1;-6,-1]
  | 16 => !![4,5;-6,-7]
  | 17 => !![4,9;-6,-13]
  | 18 => !![1,0;0,2]
  | 19 => !![1,1;0,2]
  | 20 => !![1,2;0,2]
  | 21 => !![2,0;-3,1]
  | 22 => !![2,1;-6,-2]
  | 23 => !![2,2;-3,-2]
  | 24 => !![2,3;-6,-8]
  | 25 => !![2,4;-3,-5]
  | 26 => !![2,5;-6,-14]
  | 27 => !![4,1;-6,-1]
  | 28 => !![4,5;-6,-7]
  | 29 => !![4,9;-6,-13]
  | 30 => !![1,0;0,1]
  | 31 => !![1,0;0,2]
  | 32 => !![1,1;-3,-1]
  | 33 => !![1,1;0,1]
  | 34 => !![1,2;-3,-4]
  | 35 => !![1,3;-3,-7]
  | 36 => !![2,1;-6,-2]
  | 37 => !![2,2;0,1]
  | 38 => !![2,3;-6,-8]
  | 39 => !![2,3;0,1]
  | 40 => !![2,4;0,1]
  | 41 => !![2,5;-6,-14]
  | 42 => !![1,0;3,1]
  | 43 => !![1,1;3,4]
  | _ => !![1,2;3,7]

def baseMatrix (i : Fin 10) : Matrix (Fin 2) (Fin 2) ℤ :=
  match i.val with
  | 0 => !![1,0;0,1]
  | 1 => !![1,1;0,1]
  | 2 => !![1,2;0,1]
  | 3 => !![1,0;3,1]
  | 4 => !![1,0;6,1]
  | 5 => !![1,1;3,4]
  | 6 => !![4,1;3,1]
  | 7 => !![1,0;0,2]
  | 8 => !![1,3;0,2]
  | _ => !![2,0;0,1]

theorem coordinateGL_valid : ∀ i : Fin 67, (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate i).det=1 ∨ (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate i).det=2 := by decide

def coordinateGL (i : Fin 67) : GL (Fin 2) ℝ := liftMatrix (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate i) (coordinateGL_valid i)

theorem coordinateGL_det (i : Fin 67) : (GeneralLinearGroup.det (coordinateGL i):ℝ)=1 := liftMatrix_det _ _

theorem rightGL_valid : ∀ i : Fin 45, (rightMatrix i).det=1 ∨ (rightMatrix i).det=2 := by decide

def rightGL (i : Fin 45) : GL (Fin 2) ℝ := liftMatrix (rightMatrix i) (rightGL_valid i)

theorem rightGL_det (i : Fin 45) : (GeneralLinearGroup.det (rightGL i):ℝ)=1 := liftMatrix_det _ _

theorem baseGL_valid : ∀ i : Fin 10, (baseMatrix i).det=1 ∨ (baseMatrix i).det=2 := by decide

def baseGL (i : Fin 10) : GL (Fin 2) ℝ := liftMatrix (baseMatrix i) (baseGL_valid i)

theorem baseGL_det (i : Fin 10) : (GeneralLinearGroup.det (baseGL i):ℝ)=1 := liftMatrix_det _ _

end QuantitativeArithmeticSmallLevelTwentySevenAffine
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenAffineProductsBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentySevenAffine
open Matrix UpperHalfPlane SmallLevelNormalized QuantitativeArithmeticQuadraticMatrices
open scoped MatrixGroups ModularForm

theorem product_0_0 : baseGL 0*rightGL 0=signed false (coordinateGL 0) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 0)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 0)
    (baseGL_valid 0) (rightGL_valid 0) (coordinateGL_valid 0) false (by decide)

theorem product_0_1 : baseGL 1*rightGL 0=signed false (coordinateGL 40) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 0)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 40)
    (baseGL_valid 1) (rightGL_valid 0) (coordinateGL_valid 40) false (by decide)

theorem product_0_2 : baseGL 2*rightGL 0=signed false (coordinateGL 54) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 0)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 54)
    (baseGL_valid 2) (rightGL_valid 0) (coordinateGL_valid 54) false (by decide)

theorem product_1_0 : baseGL 0*rightGL 1=signed false (coordinateGL 1) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 1)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 1)
    (baseGL_valid 0) (rightGL_valid 1) (coordinateGL_valid 1) false (by decide)

theorem product_1_1 : baseGL 1*rightGL 1=signed false (coordinateGL 9) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 1)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 9)
    (baseGL_valid 1) (rightGL_valid 1) (coordinateGL_valid 9) false (by decide)

theorem product_1_2 : baseGL 2*rightGL 1=signed false (coordinateGL 14) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 1)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 14)
    (baseGL_valid 2) (rightGL_valid 1) (coordinateGL_valid 14) false (by decide)

theorem product_2_0 : baseGL 0*rightGL 2=signed false (coordinateGL 2) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 2)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 2)
    (baseGL_valid 0) (rightGL_valid 2) (coordinateGL_valid 2) false (by decide)

theorem product_2_1 : baseGL 1*rightGL 2=signed false (coordinateGL 42) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 2)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 42)
    (baseGL_valid 1) (rightGL_valid 2) (coordinateGL_valid 42) false (by decide)

theorem product_2_2 : baseGL 2*rightGL 2=signed false (coordinateGL 55) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 2)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 55)
    (baseGL_valid 2) (rightGL_valid 2) (coordinateGL_valid 55) false (by decide)

theorem product_3_0 : baseGL 0*rightGL 3=signed false (coordinateGL 5) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 3)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 5)
    (baseGL_valid 0) (rightGL_valid 3) (coordinateGL_valid 5) false (by decide)

theorem product_3_1 : baseGL 1*rightGL 3=signed false (coordinateGL 13) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 3)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 13)
    (baseGL_valid 1) (rightGL_valid 3) (coordinateGL_valid 13) false (by decide)

theorem product_3_2 : baseGL 2*rightGL 3=signed false (coordinateGL 15) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 3)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 15)
    (baseGL_valid 2) (rightGL_valid 3) (coordinateGL_valid 15) false (by decide)

theorem product_4_0 : baseGL 0*rightGL 4=signed false (coordinateGL 16) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 4)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 16)
    (baseGL_valid 0) (rightGL_valid 4) (coordinateGL_valid 16) false (by decide)

theorem product_4_1 : baseGL 1*rightGL 4=signed true (coordinateGL 0) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 4)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 0)
    (baseGL_valid 1) (rightGL_valid 4) (coordinateGL_valid 0) true (by decide)

theorem product_4_2 : baseGL 2*rightGL 4=signed true (coordinateGL 40) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 4)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 40)
    (baseGL_valid 2) (rightGL_valid 4) (coordinateGL_valid 40) true (by decide)

theorem product_5_0 : baseGL 0*rightGL 5=signed false (coordinateGL 18) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 5)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 18)
    (baseGL_valid 0) (rightGL_valid 5) (coordinateGL_valid 18) false (by decide)

theorem product_5_1 : baseGL 1*rightGL 5=signed false (coordinateGL 56) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 5)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 56)
    (baseGL_valid 1) (rightGL_valid 5) (coordinateGL_valid 56) false (by decide)

theorem product_5_2 : baseGL 2*rightGL 5=signed false (coordinateGL 64) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 5)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 64)
    (baseGL_valid 2) (rightGL_valid 5) (coordinateGL_valid 64) false (by decide)

theorem product_6_0 : baseGL 0*rightGL 6=signed false (coordinateGL 20) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 6)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 20)
    (baseGL_valid 0) (rightGL_valid 6) (coordinateGL_valid 20) false (by decide)

theorem product_6_1 : baseGL 1*rightGL 6=signed true (coordinateGL 43) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 6)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 43)
    (baseGL_valid 1) (rightGL_valid 6) (coordinateGL_valid 43) true (by decide)

theorem product_6_2 : baseGL 2*rightGL 6=signed true (coordinateGL 61) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 6)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 61)
    (baseGL_valid 2) (rightGL_valid 6) (coordinateGL_valid 61) true (by decide)

theorem product_7_0 : baseGL 0*rightGL 7=signed false (coordinateGL 21) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 7)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 21)
    (baseGL_valid 0) (rightGL_valid 7) (coordinateGL_valid 21) false (by decide)

theorem product_7_1 : baseGL 1*rightGL 7=signed false (coordinateGL 24) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 7)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 24)
    (baseGL_valid 1) (rightGL_valid 7) (coordinateGL_valid 24) false (by decide)

theorem product_7_2 : baseGL 2*rightGL 7=signed false (coordinateGL 29) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 7)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 29)
    (baseGL_valid 2) (rightGL_valid 7) (coordinateGL_valid 29) false (by decide)

theorem product_8_0 : baseGL 0*rightGL 8=signed false (coordinateGL 22) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 8)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 22)
    (baseGL_valid 0) (rightGL_valid 8) (coordinateGL_valid 22) false (by decide)

theorem product_8_1 : baseGL 1*rightGL 8=signed false (coordinateGL 57) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 8)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 57)
    (baseGL_valid 1) (rightGL_valid 8) (coordinateGL_valid 57) false (by decide)

theorem product_8_2 : baseGL 2*rightGL 8=signed false (coordinateGL 65) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 8)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 65)
    (baseGL_valid 2) (rightGL_valid 8) (coordinateGL_valid 65) false (by decide)

theorem product_9_0 : baseGL 0*rightGL 9=signed false (coordinateGL 23) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 9)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 23)
    (baseGL_valid 0) (rightGL_valid 9) (coordinateGL_valid 23) false (by decide)

theorem product_9_1 : baseGL 1*rightGL 9=signed true (coordinateGL 3) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 9)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 3)
    (baseGL_valid 1) (rightGL_valid 9) (coordinateGL_valid 3) true (by decide)

theorem product_9_2 : baseGL 2*rightGL 9=signed true (coordinateGL 45) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 9)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 45)
    (baseGL_valid 2) (rightGL_valid 9) (coordinateGL_valid 45) true (by decide)

theorem product_10_0 : baseGL 0*rightGL 10=signed false (coordinateGL 26) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 10)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 26)
    (baseGL_valid 0) (rightGL_valid 10) (coordinateGL_valid 26) false (by decide)

theorem product_10_1 : baseGL 1*rightGL 10=signed false (coordinateGL 58) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 10)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 58)
    (baseGL_valid 1) (rightGL_valid 10) (coordinateGL_valid 58) false (by decide)

theorem product_10_2 : baseGL 2*rightGL 10=signed false (coordinateGL 66) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 10)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 66)
    (baseGL_valid 2) (rightGL_valid 10) (coordinateGL_valid 66) false (by decide)

theorem product_11_0 : baseGL 0*rightGL 11=signed false (coordinateGL 28) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 11)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 28)
    (baseGL_valid 0) (rightGL_valid 11) (coordinateGL_valid 28) false (by decide)

theorem product_11_1 : baseGL 1*rightGL 11=signed true (coordinateGL 48) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 11)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 48)
    (baseGL_valid 1) (rightGL_valid 11) (coordinateGL_valid 48) true (by decide)

theorem product_11_2 : baseGL 2*rightGL 11=signed true (coordinateGL 62) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 11)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 62)
    (baseGL_valid 2) (rightGL_valid 11) (coordinateGL_valid 62) true (by decide)

theorem product_12_0 : baseGL 0*rightGL 12=signed false (coordinateGL 31) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 12)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 31)
    (baseGL_valid 0) (rightGL_valid 12) (coordinateGL_valid 31) false (by decide)

theorem product_12_1 : baseGL 1*rightGL 12=signed true (coordinateGL 7) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 12)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 7)
    (baseGL_valid 1) (rightGL_valid 12) (coordinateGL_valid 7) true (by decide)

theorem product_12_2 : baseGL 2*rightGL 12=signed true (coordinateGL 50) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 12)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 50)
    (baseGL_valid 2) (rightGL_valid 12) (coordinateGL_valid 50) true (by decide)

theorem product_13_0 : baseGL 0*rightGL 13=signed false (coordinateGL 32) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 13)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 32)
    (baseGL_valid 0) (rightGL_valid 13) (coordinateGL_valid 32) false (by decide)

theorem product_13_1 : baseGL 1*rightGL 13=signed false (coordinateGL 37) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 13)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 37)
    (baseGL_valid 1) (rightGL_valid 13) (coordinateGL_valid 37) false (by decide)

theorem product_13_2 : baseGL 2*rightGL 13=signed false (coordinateGL 39) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 13)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 39)
    (baseGL_valid 2) (rightGL_valid 13) (coordinateGL_valid 39) false (by decide)

theorem product_14_0 : baseGL 0*rightGL 14=signed false (coordinateGL 36) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 14)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 36)
    (baseGL_valid 0) (rightGL_valid 14) (coordinateGL_valid 36) false (by decide)

theorem product_14_1 : baseGL 1*rightGL 14=signed true (coordinateGL 52) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 14)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 52)
    (baseGL_valid 1) (rightGL_valid 14) (coordinateGL_valid 52) true (by decide)

theorem product_14_2 : baseGL 2*rightGL 14=signed true (coordinateGL 63) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 14)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 63)
    (baseGL_valid 2) (rightGL_valid 14) (coordinateGL_valid 63) true (by decide)

theorem product_15_0 : baseGL 0*rightGL 15=signed false (coordinateGL 41) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 15)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 41)
    (baseGL_valid 0) (rightGL_valid 15) (coordinateGL_valid 41) false (by decide)

theorem product_15_1 : baseGL 1*rightGL 15=signed true (coordinateGL 18) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 15)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 18)
    (baseGL_valid 1) (rightGL_valid 15) (coordinateGL_valid 18) true (by decide)

theorem product_15_2 : baseGL 2*rightGL 15=signed true (coordinateGL 56) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 15)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 56)
    (baseGL_valid 2) (rightGL_valid 15) (coordinateGL_valid 56) true (by decide)

theorem product_16_0 : baseGL 0*rightGL 16=signed false (coordinateGL 46) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 16)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 46)
    (baseGL_valid 0) (rightGL_valid 16) (coordinateGL_valid 46) false (by decide)

theorem product_16_1 : baseGL 1*rightGL 16=signed true (coordinateGL 26) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 16)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 26)
    (baseGL_valid 1) (rightGL_valid 16) (coordinateGL_valid 26) true (by decide)

theorem product_16_2 : baseGL 2*rightGL 16=signed true (coordinateGL 58) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 16)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 58)
    (baseGL_valid 2) (rightGL_valid 16) (coordinateGL_valid 58) true (by decide)

theorem product_17_0 : baseGL 0*rightGL 17=signed false (coordinateGL 51) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 17)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 51)
    (baseGL_valid 0) (rightGL_valid 17) (coordinateGL_valid 51) false (by decide)

theorem product_17_1 : baseGL 1*rightGL 17=signed true (coordinateGL 34) := by
  exact lift_signed_mul (baseMatrix 1) (rightMatrix 17)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 34)
    (baseGL_valid 1) (rightGL_valid 17) (coordinateGL_valid 34) true (by decide)

theorem product_17_2 : baseGL 2*rightGL 17=signed true (coordinateGL 60) := by
  exact lift_signed_mul (baseMatrix 2) (rightMatrix 17)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 60)
    (baseGL_valid 2) (rightGL_valid 17) (coordinateGL_valid 60) true (by decide)

theorem product_18_0 : baseGL 0*rightGL 18=signed false (coordinateGL 1) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 18)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 1)
    (baseGL_valid 0) (rightGL_valid 18) (coordinateGL_valid 1) false (by decide)

theorem product_18_1 : baseGL 3*rightGL 18=signed false (coordinateGL 3) := by
  exact lift_signed_mul (baseMatrix 3) (rightMatrix 18)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 3)
    (baseGL_valid 3) (rightGL_valid 18) (coordinateGL_valid 3) false (by decide)

theorem product_18_2 : baseGL 4*rightGL 18=signed false (coordinateGL 4) := by
  exact lift_signed_mul (baseMatrix 4) (rightMatrix 18)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 4)
    (baseGL_valid 4) (rightGL_valid 18) (coordinateGL_valid 4) false (by decide)

theorem product_19_0 : baseGL 0*rightGL 19=signed false (coordinateGL 5) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 19)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 5)
    (baseGL_valid 0) (rightGL_valid 19) (coordinateGL_valid 5) false (by decide)

theorem product_19_1 : baseGL 3*rightGL 19=signed false (coordinateGL 7) := by
  exact lift_signed_mul (baseMatrix 3) (rightMatrix 19)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 7)
    (baseGL_valid 3) (rightGL_valid 19) (coordinateGL_valid 7) false (by decide)

theorem product_19_2 : baseGL 4*rightGL 19=signed false (coordinateGL 8) := by
  exact lift_signed_mul (baseMatrix 4) (rightMatrix 19)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 8)
    (baseGL_valid 4) (rightGL_valid 19) (coordinateGL_valid 8) false (by decide)

theorem product_20_0 : baseGL 0*rightGL 20=signed false (coordinateGL 9) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 20)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 9)
    (baseGL_valid 0) (rightGL_valid 20) (coordinateGL_valid 9) false (by decide)

theorem product_20_1 : baseGL 3*rightGL 20=signed false (coordinateGL 11) := by
  exact lift_signed_mul (baseMatrix 3) (rightMatrix 20)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 11)
    (baseGL_valid 3) (rightGL_valid 20) (coordinateGL_valid 11) false (by decide)

theorem product_20_2 : baseGL 4*rightGL 20=signed false (coordinateGL 12) := by
  exact lift_signed_mul (baseMatrix 4) (rightMatrix 20)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 12)
    (baseGL_valid 4) (rightGL_valid 20) (coordinateGL_valid 12) false (by decide)

theorem product_21_0 : baseGL 0*rightGL 21=signed false (coordinateGL 16) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 21)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 16)
    (baseGL_valid 0) (rightGL_valid 21) (coordinateGL_valid 16) false (by decide)

theorem product_21_1 : baseGL 3*rightGL 21=signed false (coordinateGL 17) := by
  exact lift_signed_mul (baseMatrix 3) (rightMatrix 21)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 17)
    (baseGL_valid 3) (rightGL_valid 21) (coordinateGL_valid 17) false (by decide)

theorem product_21_2 : baseGL 4*rightGL 21=signed false (coordinateGL 19) := by
  exact lift_signed_mul (baseMatrix 4) (rightMatrix 21)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 19)
    (baseGL_valid 4) (rightGL_valid 21) (coordinateGL_valid 19) false (by decide)

theorem product_22_0 : baseGL 0*rightGL 22=signed false (coordinateGL 20) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 22)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 20)
    (baseGL_valid 0) (rightGL_valid 22) (coordinateGL_valid 20) false (by decide)

theorem product_22_1 : baseGL 3*rightGL 22=signed false (coordinateGL 21) := by
  exact lift_signed_mul (baseMatrix 3) (rightMatrix 22)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 21)
    (baseGL_valid 3) (rightGL_valid 22) (coordinateGL_valid 21) false (by decide)

theorem product_22_2 : baseGL 4*rightGL 22=signed false (coordinateGL 22) := by
  exact lift_signed_mul (baseMatrix 4) (rightMatrix 22)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 22)
    (baseGL_valid 4) (rightGL_valid 22) (coordinateGL_valid 22) false (by decide)

theorem product_23_0 : baseGL 0*rightGL 23=signed false (coordinateGL 23) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 23)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 23)
    (baseGL_valid 0) (rightGL_valid 23) (coordinateGL_valid 23) false (by decide)

theorem product_23_1 : baseGL 3*rightGL 23=signed false (coordinateGL 25) := by
  exact lift_signed_mul (baseMatrix 3) (rightMatrix 23)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 25)
    (baseGL_valid 3) (rightGL_valid 23) (coordinateGL_valid 25) false (by decide)

theorem product_23_2 : baseGL 4*rightGL 23=signed false (coordinateGL 27) := by
  exact lift_signed_mul (baseMatrix 4) (rightMatrix 23)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 27)
    (baseGL_valid 4) (rightGL_valid 23) (coordinateGL_valid 27) false (by decide)

theorem product_24_0 : baseGL 0*rightGL 24=signed false (coordinateGL 28) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 24)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 28)
    (baseGL_valid 0) (rightGL_valid 24) (coordinateGL_valid 28) false (by decide)

theorem product_24_1 : baseGL 3*rightGL 24=signed false (coordinateGL 29) := by
  exact lift_signed_mul (baseMatrix 3) (rightMatrix 24)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 29)
    (baseGL_valid 3) (rightGL_valid 24) (coordinateGL_valid 29) false (by decide)

theorem product_24_2 : baseGL 4*rightGL 24=signed false (coordinateGL 30) := by
  exact lift_signed_mul (baseMatrix 4) (rightMatrix 24)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 30)
    (baseGL_valid 4) (rightGL_valid 24) (coordinateGL_valid 30) false (by decide)

theorem product_25_0 : baseGL 0*rightGL 25=signed false (coordinateGL 31) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 25)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 31)
    (baseGL_valid 0) (rightGL_valid 25) (coordinateGL_valid 31) false (by decide)

theorem product_25_1 : baseGL 3*rightGL 25=signed false (coordinateGL 33) := by
  exact lift_signed_mul (baseMatrix 3) (rightMatrix 25)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 33)
    (baseGL_valid 3) (rightGL_valid 25) (coordinateGL_valid 33) false (by decide)

theorem product_25_2 : baseGL 4*rightGL 25=signed false (coordinateGL 35) := by
  exact lift_signed_mul (baseMatrix 4) (rightMatrix 25)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 35)
    (baseGL_valid 4) (rightGL_valid 25) (coordinateGL_valid 35) false (by decide)

theorem product_26_0 : baseGL 0*rightGL 26=signed false (coordinateGL 36) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 26)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 36)
    (baseGL_valid 0) (rightGL_valid 26) (coordinateGL_valid 36) false (by decide)

theorem product_26_1 : baseGL 3*rightGL 26=signed false (coordinateGL 37) := by
  exact lift_signed_mul (baseMatrix 3) (rightMatrix 26)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 37)
    (baseGL_valid 3) (rightGL_valid 26) (coordinateGL_valid 37) false (by decide)

theorem product_26_2 : baseGL 4*rightGL 26=signed false (coordinateGL 38) := by
  exact lift_signed_mul (baseMatrix 4) (rightMatrix 26)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 38)
    (baseGL_valid 4) (rightGL_valid 26) (coordinateGL_valid 38) false (by decide)

theorem product_27_0 : baseGL 0*rightGL 27=signed false (coordinateGL 41) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 27)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 41)
    (baseGL_valid 0) (rightGL_valid 27) (coordinateGL_valid 41) false (by decide)

theorem product_27_1 : baseGL 3*rightGL 27=signed false (coordinateGL 43) := by
  exact lift_signed_mul (baseMatrix 3) (rightMatrix 27)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 43)
    (baseGL_valid 3) (rightGL_valid 27) (coordinateGL_valid 43) false (by decide)

theorem product_27_2 : baseGL 4*rightGL 27=signed false (coordinateGL 44) := by
  exact lift_signed_mul (baseMatrix 4) (rightMatrix 27)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 44)
    (baseGL_valid 4) (rightGL_valid 27) (coordinateGL_valid 44) false (by decide)

theorem product_28_0 : baseGL 0*rightGL 28=signed false (coordinateGL 46) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 28)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 46)
    (baseGL_valid 0) (rightGL_valid 28) (coordinateGL_valid 46) false (by decide)

theorem product_28_1 : baseGL 3*rightGL 28=signed false (coordinateGL 48) := by
  exact lift_signed_mul (baseMatrix 3) (rightMatrix 28)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 48)
    (baseGL_valid 3) (rightGL_valid 28) (coordinateGL_valid 48) false (by decide)

theorem product_28_2 : baseGL 4*rightGL 28=signed false (coordinateGL 49) := by
  exact lift_signed_mul (baseMatrix 4) (rightMatrix 28)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 49)
    (baseGL_valid 4) (rightGL_valid 28) (coordinateGL_valid 49) false (by decide)

theorem product_29_0 : baseGL 0*rightGL 29=signed false (coordinateGL 51) := by
  exact lift_signed_mul (baseMatrix 0) (rightMatrix 29)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 51)
    (baseGL_valid 0) (rightGL_valid 29) (coordinateGL_valid 51) false (by decide)

theorem product_29_1 : baseGL 3*rightGL 29=signed false (coordinateGL 52) := by
  exact lift_signed_mul (baseMatrix 3) (rightMatrix 29)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 52)
    (baseGL_valid 3) (rightGL_valid 29) (coordinateGL_valid 52) false (by decide)

theorem product_29_2 : baseGL 4*rightGL 29=signed false (coordinateGL 53) := by
  exact lift_signed_mul (baseMatrix 4) (rightMatrix 29)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 53)
    (baseGL_valid 4) (rightGL_valid 29) (coordinateGL_valid 53) false (by decide)

theorem product_30_0 : baseGL 5*rightGL 30=signed false (coordinateGL 6) := by
  exact lift_signed_mul (baseMatrix 5) (rightMatrix 30)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 6)
    (baseGL_valid 5) (rightGL_valid 30) (coordinateGL_valid 6) false (by decide)

theorem product_30_1 : baseGL 6*rightGL 30=signed false (coordinateGL 42) := by
  exact lift_signed_mul (baseMatrix 6) (rightMatrix 30)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 42)
    (baseGL_valid 6) (rightGL_valid 30) (coordinateGL_valid 42) false (by decide)

theorem product_31_0 : baseGL 5*rightGL 31=signed false (coordinateGL 11) := by
  exact lift_signed_mul (baseMatrix 5) (rightMatrix 31)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 11)
    (baseGL_valid 5) (rightGL_valid 31) (coordinateGL_valid 11) false (by decide)

theorem product_31_1 : baseGL 6*rightGL 31=signed false (coordinateGL 45) := by
  exact lift_signed_mul (baseMatrix 6) (rightMatrix 31)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 45)
    (baseGL_valid 6) (rightGL_valid 31) (coordinateGL_valid 45) false (by decide)

theorem product_32_0 : baseGL 5*rightGL 32=signed true (coordinateGL 19) := by
  exact lift_signed_mul (baseMatrix 5) (rightMatrix 32)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 19)
    (baseGL_valid 5) (rightGL_valid 32) (coordinateGL_valid 19) true (by decide)

theorem product_32_1 : baseGL 6*rightGL 32=signed false (coordinateGL 13) := by
  exact lift_signed_mul (baseMatrix 6) (rightMatrix 32)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 13)
    (baseGL_valid 6) (rightGL_valid 32) (coordinateGL_valid 13) false (by decide)

theorem product_33_0 : baseGL 5*rightGL 33=signed false (coordinateGL 10) := by
  exact lift_signed_mul (baseMatrix 5) (rightMatrix 33)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 10)
    (baseGL_valid 5) (rightGL_valid 33) (coordinateGL_valid 10) false (by decide)

theorem product_33_1 : baseGL 6*rightGL 33=signed false (coordinateGL 47) := by
  exact lift_signed_mul (baseMatrix 6) (rightMatrix 33)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 47)
    (baseGL_valid 6) (rightGL_valid 33) (coordinateGL_valid 47) false (by decide)

theorem product_34_0 : baseGL 5*rightGL 34=signed true (coordinateGL 27) := by
  exact lift_signed_mul (baseMatrix 5) (rightMatrix 34)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 27)
    (baseGL_valid 5) (rightGL_valid 34) (coordinateGL_valid 27) true (by decide)

theorem product_34_1 : baseGL 6*rightGL 34=signed false (coordinateGL 14) := by
  exact lift_signed_mul (baseMatrix 6) (rightMatrix 34)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 14)
    (baseGL_valid 6) (rightGL_valid 34) (coordinateGL_valid 14) false (by decide)

theorem product_35_0 : baseGL 5*rightGL 35=signed true (coordinateGL 35) := by
  exact lift_signed_mul (baseMatrix 5) (rightMatrix 35)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 35)
    (baseGL_valid 5) (rightGL_valid 35) (coordinateGL_valid 35) true (by decide)

theorem product_35_1 : baseGL 6*rightGL 35=signed false (coordinateGL 15) := by
  exact lift_signed_mul (baseMatrix 6) (rightMatrix 35)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 15)
    (baseGL_valid 6) (rightGL_valid 35) (coordinateGL_valid 15) false (by decide)

theorem product_36_0 : baseGL 5*rightGL 36=signed true (coordinateGL 44) := by
  exact lift_signed_mul (baseMatrix 5) (rightMatrix 36)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 44)
    (baseGL_valid 5) (rightGL_valid 36) (coordinateGL_valid 44) true (by decide)

theorem product_36_1 : baseGL 6*rightGL 36=signed false (coordinateGL 24) := by
  exact lift_signed_mul (baseMatrix 6) (rightMatrix 36)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 24)
    (baseGL_valid 6) (rightGL_valid 36) (coordinateGL_valid 24) false (by decide)

theorem product_37_0 : baseGL 5*rightGL 37=signed false (coordinateGL 30) := by
  exact lift_signed_mul (baseMatrix 5) (rightMatrix 37)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 30)
    (baseGL_valid 5) (rightGL_valid 37) (coordinateGL_valid 30) false (by decide)

theorem product_37_1 : baseGL 6*rightGL 37=signed false (coordinateGL 58) := by
  exact lift_signed_mul (baseMatrix 6) (rightMatrix 37)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 58)
    (baseGL_valid 6) (rightGL_valid 37) (coordinateGL_valid 58) false (by decide)

theorem product_38_0 : baseGL 5*rightGL 38=signed true (coordinateGL 49) := by
  exact lift_signed_mul (baseMatrix 5) (rightMatrix 38)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 49)
    (baseGL_valid 5) (rightGL_valid 38) (coordinateGL_valid 49) true (by decide)

theorem product_38_1 : baseGL 6*rightGL 38=signed false (coordinateGL 32) := by
  exact lift_signed_mul (baseMatrix 6) (rightMatrix 38)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 32)
    (baseGL_valid 6) (rightGL_valid 38) (coordinateGL_valid 32) false (by decide)

theorem product_39_0 : baseGL 5*rightGL 39=signed false (coordinateGL 34) := by
  exact lift_signed_mul (baseMatrix 5) (rightMatrix 39)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 34)
    (baseGL_valid 5) (rightGL_valid 39) (coordinateGL_valid 34) false (by decide)

theorem product_39_1 : baseGL 6*rightGL 39=signed false (coordinateGL 59) := by
  exact lift_signed_mul (baseMatrix 6) (rightMatrix 39)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 59)
    (baseGL_valid 6) (rightGL_valid 39) (coordinateGL_valid 59) false (by decide)

theorem product_40_0 : baseGL 5*rightGL 40=signed false (coordinateGL 38) := by
  exact lift_signed_mul (baseMatrix 5) (rightMatrix 40)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 38)
    (baseGL_valid 5) (rightGL_valid 40) (coordinateGL_valid 38) false (by decide)

theorem product_40_1 : baseGL 6*rightGL 40=signed false (coordinateGL 60) := by
  exact lift_signed_mul (baseMatrix 6) (rightMatrix 40)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 60)
    (baseGL_valid 6) (rightGL_valid 40) (coordinateGL_valid 60) false (by decide)

theorem product_41_0 : baseGL 5*rightGL 41=signed true (coordinateGL 53) := by
  exact lift_signed_mul (baseMatrix 5) (rightMatrix 41)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 53)
    (baseGL_valid 5) (rightGL_valid 41) (coordinateGL_valid 53) true (by decide)

theorem product_41_1 : baseGL 6*rightGL 41=signed false (coordinateGL 39) := by
  exact lift_signed_mul (baseMatrix 6) (rightMatrix 41)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 39)
    (baseGL_valid 6) (rightGL_valid 41) (coordinateGL_valid 39) false (by decide)

theorem product_42_0 : baseGL 7*rightGL 42=signed false (coordinateGL 4) := by
  exact lift_signed_mul (baseMatrix 7) (rightMatrix 42)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 4)
    (baseGL_valid 7) (rightGL_valid 42) (coordinateGL_valid 4) false (by decide)

theorem product_42_1 : baseGL 8*rightGL 42=signed false (coordinateGL 61) := by
  exact lift_signed_mul (baseMatrix 8) (rightMatrix 42)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 61)
    (baseGL_valid 8) (rightGL_valid 42) (coordinateGL_valid 61) false (by decide)

theorem product_42_2 : baseGL 9*rightGL 42=signed false (coordinateGL 17) := by
  exact lift_signed_mul (baseMatrix 9) (rightMatrix 42)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 17)
    (baseGL_valid 9) (rightGL_valid 42) (coordinateGL_valid 17) false (by decide)

theorem product_43_0 : baseGL 7*rightGL 43=signed false (coordinateGL 8) := by
  exact lift_signed_mul (baseMatrix 7) (rightMatrix 43)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 8)
    (baseGL_valid 7) (rightGL_valid 43) (coordinateGL_valid 8) false (by decide)

theorem product_43_1 : baseGL 8*rightGL 43=signed false (coordinateGL 62) := by
  exact lift_signed_mul (baseMatrix 8) (rightMatrix 43)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 62)
    (baseGL_valid 8) (rightGL_valid 43) (coordinateGL_valid 62) false (by decide)

theorem product_43_2 : baseGL 9*rightGL 43=signed false (coordinateGL 25) := by
  exact lift_signed_mul (baseMatrix 9) (rightMatrix 43)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 25)
    (baseGL_valid 9) (rightGL_valid 43) (coordinateGL_valid 25) false (by decide)

theorem product_44_0 : baseGL 7*rightGL 44=signed false (coordinateGL 12) := by
  exact lift_signed_mul (baseMatrix 7) (rightMatrix 44)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 12)
    (baseGL_valid 7) (rightGL_valid 44) (coordinateGL_valid 12) false (by decide)

theorem product_44_1 : baseGL 8*rightGL 44=signed false (coordinateGL 63) := by
  exact lift_signed_mul (baseMatrix 8) (rightMatrix 44)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 63)
    (baseGL_valid 8) (rightGL_valid 44) (coordinateGL_valid 63) false (by decide)

theorem product_44_2 : baseGL 9*rightGL 44=signed false (coordinateGL 33) := by
  exact lift_signed_mul (baseMatrix 9) (rightMatrix 44)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 33)
    (baseGL_valid 9) (rightGL_valid 44) (coordinateGL_valid 33) false (by decide)

end QuantitativeArithmeticSmallLevelTwentySevenAffine
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenAffineSourcesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenAffine
open Matrix UpperHalfPlane SmallLevelNormalized QuantitativeArithmeticQuadraticMatrices
open scoped MatrixGroups ModularForm

def baseSum (m : ℕ) (a : ℂ) (F : ℍ → ℂ) (i : Fin 4) : ℍ → ℂ :=
  match i.val with
  | 0 => (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)
  | 1 => (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 3)+(F ∣[((2*m:ℕ):ℤ)] baseGL 4)
  | 2 => (F ∣[((2*m:ℕ):ℤ)] baseGL 5)-(F ∣[((2*m:ℕ):ℤ)] baseGL 6)
  | _ => (F ∣[((2*m:ℕ):ℤ)] baseGL 7)+(F ∣[((2*m:ℕ):ℤ)] baseGL 8)+(F ∣[((2*m:ℕ):ℤ)] baseGL 9)-a • F

end QuantitativeArithmeticSmallLevelTwentySevenAffine
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenAffineSourceRowsBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentySevenAffine
open Matrix UpperHalfPlane SmallLevelNormalized QuantitativeArithmeticQuadraticMatrices
open scoped MatrixGroups ModularForm

theorem source_zero_0 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 0=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 0) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 0),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_0_0,product_0_1,product_0_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_1 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 1=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 1) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 1),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_1_0,product_1_1,product_1_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_2 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 2=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 2) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 2),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_2_0,product_2_1,product_2_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_3 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 3=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 3) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 3),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_3_0,product_3_1,product_3_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_4 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 4=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 4) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 4),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_4_0,product_4_1,product_4_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_5 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 5=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 5) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 5),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_5_0,product_5_1,product_5_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_6 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 6=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 6) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 6),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_6_0,product_6_1,product_6_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_7 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 7=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 7) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 7),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_7_0,product_7_1,product_7_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_8 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 8=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 8) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 8),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_8_0,product_8_1,product_8_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_9 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 9=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 9) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 9),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_9_0,product_9_1,product_9_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_10 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 10=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 10) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 10),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_10_0,product_10_1,product_10_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_11 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 11=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 11) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 11),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_11_0,product_11_1,product_11_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_12 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 12=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 12) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 12),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_12_0,product_12_1,product_12_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_13 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 13=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 13) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 13),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_13_0,product_13_1,product_13_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_14 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 14=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 14) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 14),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_14_0,product_14_1,product_14_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_15 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 15=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 15) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 15),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_15_0,product_15_1,product_15_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_16 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 16=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 16) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 16),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_16_0,product_16_1,product_16_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_17 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 0=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 17=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 1)+(F ∣[((2*m:ℕ):ℤ)] baseGL 2)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 17) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 17),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_17_0,product_17_1,product_17_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_18 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 1=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 18=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 3)+(F ∣[((2*m:ℕ):ℤ)] baseGL 4)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 18) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 18),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_18_0,product_18_1,product_18_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_19 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 1=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 19=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 3)+(F ∣[((2*m:ℕ):ℤ)] baseGL 4)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 19) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 19),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_19_0,product_19_1,product_19_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_20 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 1=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 20=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 3)+(F ∣[((2*m:ℕ):ℤ)] baseGL 4)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 20) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 20),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_20_0,product_20_1,product_20_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_21 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 1=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 21=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 3)+(F ∣[((2*m:ℕ):ℤ)] baseGL 4)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 21) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 21),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_21_0,product_21_1,product_21_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_22 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 1=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 22=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 3)+(F ∣[((2*m:ℕ):ℤ)] baseGL 4)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 22) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 22),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_22_0,product_22_1,product_22_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_23 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 1=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 23=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 3)+(F ∣[((2*m:ℕ):ℤ)] baseGL 4)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 23) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 23),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_23_0,product_23_1,product_23_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_24 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 1=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 24=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 3)+(F ∣[((2*m:ℕ):ℤ)] baseGL 4)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 24) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 24),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_24_0,product_24_1,product_24_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_25 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 1=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 25=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 3)+(F ∣[((2*m:ℕ):ℤ)] baseGL 4)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 25) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 25),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_25_0,product_25_1,product_25_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_26 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 1=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 26=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 3)+(F ∣[((2*m:ℕ):ℤ)] baseGL 4)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 26) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 26),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_26_0,product_26_1,product_26_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_27 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 1=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 27=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 3)+(F ∣[((2*m:ℕ):ℤ)] baseGL 4)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 27) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 27),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_27_0,product_27_1,product_27_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_28 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 1=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 28=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 3)+(F ∣[((2*m:ℕ):ℤ)] baseGL 4)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 28) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 28),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_28_0,product_28_1,product_28_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_29 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 1=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 29=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 0)+(F ∣[((2*m:ℕ):ℤ)] baseGL 3)+(F ∣[((2*m:ℕ):ℤ)] baseGL 4)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 29) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 29),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_29_0,product_29_1,product_29_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_30 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 2=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 30=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 5)-(F ∣[((2*m:ℕ):ℤ)] baseGL 6)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 30) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 30),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_30_0,product_30_1,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_31 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 2=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 31=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 5)-(F ∣[((2*m:ℕ):ℤ)] baseGL 6)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 31) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 31),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_31_0,product_31_1,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_32 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 2=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 32=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 5)-(F ∣[((2*m:ℕ):ℤ)] baseGL 6)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 32) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 32),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_32_0,product_32_1,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_33 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 2=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 33=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 5)-(F ∣[((2*m:ℕ):ℤ)] baseGL 6)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 33) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 33),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_33_0,product_33_1,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_34 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 2=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 34=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 5)-(F ∣[((2*m:ℕ):ℤ)] baseGL 6)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 34) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 34),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_34_0,product_34_1,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_35 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 2=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 35=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 5)-(F ∣[((2*m:ℕ):ℤ)] baseGL 6)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 35) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 35),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_35_0,product_35_1,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_36 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 2=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 36=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 5)-(F ∣[((2*m:ℕ):ℤ)] baseGL 6)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 36) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 36),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_36_0,product_36_1,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_37 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 2=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 37=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 5)-(F ∣[((2*m:ℕ):ℤ)] baseGL 6)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 37) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 37),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_37_0,product_37_1,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_38 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 2=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 38=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 5)-(F ∣[((2*m:ℕ):ℤ)] baseGL 6)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 38) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 38),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_38_0,product_38_1,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_39 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 2=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 39=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 5)-(F ∣[((2*m:ℕ):ℤ)] baseGL 6)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 39) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 39),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_39_0,product_39_1,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_40 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 2=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 40=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 5)-(F ∣[((2*m:ℕ):ℤ)] baseGL 6)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 40) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 40),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_40_0,product_40_1,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_41 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 2=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 41=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 5)-(F ∣[((2*m:ℕ):ℤ)] baseGL 6)=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 41) z) h
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 41),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_41_0,product_41_1,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_42 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 3=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 42=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 7)+(F ∣[((2*m:ℕ):ℤ)] baseGL 8)+(F ∣[((2*m:ℕ):ℤ)] baseGL 9)-a • F=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 42) z) h
  have hr : rightGL 42=coordinateGL 2 := rfl
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 42),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_42_0,product_42_1,product_42_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  simp only [hr] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_43 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 3=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 43=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 7)+(F ∣[((2*m:ℕ):ℤ)] baseGL 8)+(F ∣[((2*m:ℕ):ℤ)] baseGL 9)-a • F=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 43) z) h
  have hr : rightGL 43=coordinateGL 6 := rfl
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 43),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_43_0,product_43_1,product_43_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  simp only [hr] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

theorem source_zero_44 (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : baseSum m a F 3=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) 44=0 := by
  change (F ∣[((2*m:ℕ):ℤ)] baseGL 7)+(F ∣[((2*m:ℕ):ℤ)] baseGL 8)+(F ∣[((2*m:ℕ):ℤ)] baseGL 9)-a • F=0 at h
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[((2*m:ℕ):ℤ)] rightGL 44) z) h
  have hr : rightGL 44=coordinateGL 10 := rfl
  simp only [baseSum,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,
    det_one_smul _ (rightGL_det 44),SlashAction.zero_slash,
    ← SlashAction.slash_mul,product_44_0,product_44_1,product_44_2,signed_slash,
    Pi.add_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
  simp only [hr] at hh
  convert hh using 1 <;>
    norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow] <;> ring

end QuantitativeArithmeticSmallLevelTwentySevenAffine
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenAffineTheoryV4 -/
section
/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenAffine. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenAffineSlashV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenAffine
open Matrix UpperHalfPlane SmallLevelNormalized QuantitativeArithmeticQuadraticMatrices
open scoped MatrixGroups ModularForm

/-- The45 equations in the saved certificate follow by right translation
from just the two cubic traces, the commutator, and the original Hecke law. -/
theorem all_source_zero (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : ∀ i : Fin 4, baseSum m a F i=0) (z : ℍ) (i : Fin 45) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.sourceRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z) i=0 := by
  fin_cases i
  · exact source_zero_0 m a F (h 0) z
  · exact source_zero_1 m a F (h 0) z
  · exact source_zero_2 m a F (h 0) z
  · exact source_zero_3 m a F (h 0) z
  · exact source_zero_4 m a F (h 0) z
  · exact source_zero_5 m a F (h 0) z
  · exact source_zero_6 m a F (h 0) z
  · exact source_zero_7 m a F (h 0) z
  · exact source_zero_8 m a F (h 0) z
  · exact source_zero_9 m a F (h 0) z
  · exact source_zero_10 m a F (h 0) z
  · exact source_zero_11 m a F (h 0) z
  · exact source_zero_12 m a F (h 0) z
  · exact source_zero_13 m a F (h 0) z
  · exact source_zero_14 m a F (h 0) z
  · exact source_zero_15 m a F (h 0) z
  · exact source_zero_16 m a F (h 0) z
  · exact source_zero_17 m a F (h 0) z
  · exact source_zero_18 m a F (h 1) z
  · exact source_zero_19 m a F (h 1) z
  · exact source_zero_20 m a F (h 1) z
  · exact source_zero_21 m a F (h 1) z
  · exact source_zero_22 m a F (h 1) z
  · exact source_zero_23 m a F (h 1) z
  · exact source_zero_24 m a F (h 1) z
  · exact source_zero_25 m a F (h 1) z
  · exact source_zero_26 m a F (h 1) z
  · exact source_zero_27 m a F (h 1) z
  · exact source_zero_28 m a F (h 1) z
  · exact source_zero_29 m a F (h 1) z
  · exact source_zero_30 m a F (h 2) z
  · exact source_zero_31 m a F (h 2) z
  · exact source_zero_32 m a F (h 2) z
  · exact source_zero_33 m a F (h 2) z
  · exact source_zero_34 m a F (h 2) z
  · exact source_zero_35 m a F (h 2) z
  · exact source_zero_36 m a F (h 2) z
  · exact source_zero_37 m a F (h 2) z
  · exact source_zero_38 m a F (h 2) z
  · exact source_zero_39 m a F (h 2) z
  · exact source_zero_40 m a F (h 2) z
  · exact source_zero_41 m a F (h 2) z
  · exact source_zero_42 m a F (h 3) z
  · exact source_zero_43 m a F (h 3) z
  · exact source_zero_44 m a F (h 3) z

/-- The affine certificate now applies to actual even-weight slash actions. -/
theorem affine_target_zero (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : ∀ i : Fin 4, baseSum m a F i=0) (z : ℍ) :
    QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.targetRow a
      (fun j => (F ∣[((2*m:ℕ):ℤ)] coordinateGL j) z)=0 :=
  QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.target_zero a _
    (all_source_zero m a F h z)
#print axioms all_source_zero
#print axioms affine_target_zero

end QuantitativeArithmeticSmallLevelTwentySevenAffine
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenAffineDefectV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenAffine
open Matrix UpperHalfPlane SmallLevelNormalized QuantitativeArithmeticQuadraticMatrices
open scoped MatrixGroups ModularForm

def defectMatrix (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℤ :=
  match i.val with
  | 0 => !![4,5;3,4]
  | _ => !![7,2;3,1]

theorem defectGL_valid : ∀ i : Fin 2, (defectMatrix i).det=1 ∨ (defectMatrix i).det=2 := by decide

def defectGL (i : Fin 2) : GL (Fin 2) ℝ := liftMatrix (defectMatrix i) (defectGL_valid i)

def affineMatrix (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℤ :=
  match i.val with
  | 0 => !![1,-1;0,2]
  | 1 => !![2,0;0,1]
  | 2 => !![2,1;0,1]
  | _ => !![2,2;0,1]

theorem affineGL_valid : ∀ i : Fin 4, (affineMatrix i).det=1 ∨ (affineMatrix i).det=2 := by decide

def affineGL (i : Fin 4) : GL (Fin 2) ℝ := liftMatrix (affineMatrix i) (affineGL_valid i)

theorem defect_coordinate_0 : defectGL 0=coordinateGL 47 := rfl

theorem target_product_0_0 : defectGL 0*affineGL 0=signed false (coordinateGL 50) := by
  exact lift_signed_mul (defectMatrix 0) (affineMatrix 0)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 50)
    (defectGL_valid 0) (affineGL_valid 0) (coordinateGL_valid 50) false (by decide)

theorem target_product_0_1 : defectGL 0*affineGL 1=signed false (coordinateGL 57) := by
  exact lift_signed_mul (defectMatrix 0) (affineMatrix 1)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 57)
    (defectGL_valid 0) (affineGL_valid 1) (coordinateGL_valid 57) false (by decide)

theorem target_product_0_2 : defectGL 0*affineGL 2=signed false (coordinateGL 58) := by
  exact lift_signed_mul (defectMatrix 0) (affineMatrix 2)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 58)
    (defectGL_valid 0) (affineGL_valid 2) (coordinateGL_valid 58) false (by decide)

theorem target_product_0_3 : defectGL 0*affineGL 3=signed false (coordinateGL 59) := by
  exact lift_signed_mul (defectMatrix 0) (affineMatrix 3)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 59)
    (defectGL_valid 0) (affineGL_valid 3) (coordinateGL_valid 59) false (by decide)

theorem defect_coordinate_1 : defectGL 1=coordinateGL 55 := rfl

theorem target_product_1_0 : defectGL 1*affineGL 0=signed false (coordinateGL 54) := by
  exact lift_signed_mul (defectMatrix 1) (affineMatrix 0)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 54)
    (defectGL_valid 1) (affineGL_valid 0) (coordinateGL_valid 54) false (by decide)

theorem target_product_1_1 : defectGL 1*affineGL 1=signed false (coordinateGL 64) := by
  exact lift_signed_mul (defectMatrix 1) (affineMatrix 1)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 64)
    (defectGL_valid 1) (affineGL_valid 1) (coordinateGL_valid 64) false (by decide)

theorem target_product_1_2 : defectGL 1*affineGL 2=signed false (coordinateGL 65) := by
  exact lift_signed_mul (defectMatrix 1) (affineMatrix 2)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 65)
    (defectGL_valid 1) (affineGL_valid 2) (coordinateGL_valid 65) false (by decide)

theorem target_product_1_3 : defectGL 1*affineGL 3=signed false (coordinateGL 66) := by
  exact lift_signed_mul (defectMatrix 1) (affineMatrix 3)
    (QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.coordinate 66)
    (defectGL_valid 1) (affineGL_valid 3) (coordinateGL_valid 66) false (by decide)

def defect (m : ℕ) (F : ℍ → ℂ) : ℍ → ℂ :=
  (F ∣[((2*m:ℕ):ℤ)] defectGL 0)-(F ∣[((2*m:ℕ):ℤ)] defectGL 1)

/-- The exact affine Hecke recurrence, with arbitrary complex eigenvalue,
follows from the original four operator relations on the single function. -/
theorem affine_defect (m : ℕ) (a : ℂ) (F : ℍ → ℂ)
    (h : ∀ i : Fin 4, baseSum m a F i=0) :
    a • defect m F=(defect m F ∣[((2*m:ℕ):ℤ)] affineGL 0)-
      (defect m F ∣[((2*m:ℕ):ℤ)] affineGL 1)+
      (defect m F ∣[((2*m:ℕ):ℤ)] affineGL 2)-
      (defect m F ∣[((2*m:ℕ):ℤ)] affineGL 3) := by
  funext z
  have hh := affine_target_zero m a F h z
  simp only [defect,SlashAction.add_slash,sub_eq_add_neg,SlashAction.neg_slash,← SlashAction.slash_mul,
    target_product_0_0,
    target_product_0_1,
    target_product_0_2,
    target_product_0_3,
    target_product_1_0,
    target_product_1_1,
    target_product_1_2,
    target_product_1_3,
    signed_slash,Pi.smul_apply,
    smul_eq_mul,Pi.neg_apply,Pi.sub_apply,Pi.add_apply]
  rw [defect_coordinate_0,defect_coordinate_1]
  norm_num [QuantitativeArithmeticSmallLevelTwentySevenAffineCertificate.targetRow] at hh
  norm_num only [Nat.cast_mul,Nat.cast_ofNat]
  linear_combination hh
#print axioms affine_defect
end QuantitativeArithmeticSmallLevelTwentySevenAffine
end
end
end
