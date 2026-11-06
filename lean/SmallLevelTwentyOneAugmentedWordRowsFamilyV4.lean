module
public import SmallLevelTwentyOneAugmentedWordDataV1
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace SmallLevelTwentyOneKnownWords
open Matrix

def augmentedRow000 : WordCertificate where
  row :=
    { word := augmentedWord000
      source := 0
      target := -1
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 84
  slope := 42
  count := 1
  powers := (2, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord000_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord000_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow000

def augmentedRow001 : WordCertificate where
  row :=
    { word := augmentedWord001
      source := 0
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := 21
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord001_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord001_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow001

def augmentedRow002 : WordCertificate where
  row :=
    { word := augmentedWord002
      source := 1
      target := -84
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/84)
  slope := (1/2)
  count := 1
  powers := (-2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow002

def augmentedRow003 : WordCertificate where
  row :=
    { word := augmentedWord002
      source := 2
      target := -42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := 1
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow003

def augmentedRow004 : WordCertificate where
  row :=
    { word := augmentedWord002
      source := 3
      target := -28
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/28)
  slope := (3/2)
  count := 1
  powers := (-2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow004

def augmentedRow005 : WordCertificate where
  row :=
    { word := augmentedWord002
      source := 4
      target := -21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (4/21)
  slope := 2
  count := 1
  powers := (2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow005

def augmentedRow006 : WordCertificate where
  row :=
    { word := augmentedWord002
      source := 6
      target := -14
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := 3
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow006

def augmentedRow007 : WordCertificate where
  row :=
    { word := augmentedWord002
      source := 7
      target := -12
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/12)
  slope := (7/2)
  count := 1
  powers := (-2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow007

def augmentedRow008 : WordCertificate where
  row :=
    { word := augmentedWord002
      source := 12
      target := -7
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (12/7)
  slope := 6
  count := 1
  powers := (2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow008

def augmentedRow009 : WordCertificate where
  row :=
    { word := augmentedWord002
      source := 14
      target := -6
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := 7
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow009

def augmentedRow010 : WordCertificate where
  row :=
    { word := augmentedWord002
      source := 21
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (21/4)
  slope := (21/2)
  count := 1
  powers := (-2, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow010

def augmentedRow011 : WordCertificate where
  row :=
    { word := augmentedWord002
      source := 28
      target := -3
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (28/3)
  slope := 14
  count := 1
  powers := (2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord002_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow011

def augmentedRow012 : WordCertificate where
  row :=
    { word := augmentedWord003
      source := 0
      target := 2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := -21
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow012

def augmentedRow013 : WordCertificate where
  row :=
    { word := augmentedWord003
      source := 14
      target := 3
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (28/3)
  slope := -14
  count := 1
  powers := (2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow013

def augmentedRow014 : WordCertificate where
  row :=
    { word := augmentedWord003
      source := 21
      target := 4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (21/4)
  slope := (-21/2)
  count := 1
  powers := (-2, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow014

def augmentedRow015 : WordCertificate where
  row :=
    { word := augmentedWord003
      source := 28
      target := 6
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := -7
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow015

def augmentedRow016 : WordCertificate where
  row :=
    { word := augmentedWord003
      source := 30
      target := 7
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (12/7)
  slope := -6
  count := 1
  powers := (2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow016

def augmentedRow017 : WordCertificate where
  row :=
    { word := augmentedWord003
      source := 35
      target := 12
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/12)
  slope := (-7/2)
  count := 1
  powers := (-2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow017

def augmentedRow018 : WordCertificate where
  row :=
    { word := augmentedWord003
      source := 36
      target := 14
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := -3
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow018

def augmentedRow019 : WordCertificate where
  row :=
    { word := augmentedWord003
      source := 38
      target := 21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (4/21)
  slope := -2
  count := 1
  powers := (2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow019

def augmentedRow020 : WordCertificate where
  row :=
    { word := augmentedWord003
      source := 39
      target := 28
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/28)
  slope := (-3/2)
  count := 1
  powers := (-2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow020

def augmentedRow021 : WordCertificate where
  row :=
    { word := augmentedWord003
      source := 40
      target := 42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := -1
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow021

def augmentedRow022 : WordCertificate where
  row :=
    { word := augmentedWord003
      source := 41
      target := 84
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/84)
  slope := (-1/2)
  count := 1
  powers := (-2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord003_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow022

def augmentedRow023 : WordCertificate where
  row :=
    { word := augmentedWord004
      source := 0
      target := 1
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 84
  slope := -42
  count := 1
  powers := (2, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord004_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord004_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow023



def augmentedRow024 : WordCertificate where
  row :=
    { word := augmentedWord005
      source := 40
      target := -1
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord005_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord005_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow024

def augmentedRow025 : WordCertificate where
  row :=
    { word := augmentedWord006
      source := 36
      target := 3
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord006_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord006_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow025

def augmentedRow026 : WordCertificate where
  row :=
    { word := augmentedWord006
      source := 38
      target := 4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord006_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord006_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow026

def augmentedRow027 : WordCertificate where
  row :=
    { word := augmentedWord006
      source := 39
      target := 6
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord006_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord006_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow027

def augmentedRow028 : WordCertificate where
  row :=
    { word := augmentedWord006
      source := 41
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord006_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord006_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow028

def augmentedRow029 : WordCertificate where
  row :=
    { word := augmentedWord007
      source := 40
      target := 2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -42
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord007_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord007_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow029

def augmentedRow030 : WordCertificate where
  row :=
    { word := augmentedWord008
      source := 1
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (63/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord008_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord008_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow030

def augmentedRow031 : WordCertificate where
  row :=
    { word := augmentedWord008
      source := 2
      target := -1
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 126
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord008_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord008_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow031

def augmentedRow032 : WordCertificate where
  row :=
    { word := augmentedWord009
      source := 2
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 42
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord009_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord009_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow032

def augmentedRow033 : WordCertificate where
  row :=
    { word := augmentedWord010
      source := 1
      target := 2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord010_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord010_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow033

def augmentedRow034 : WordCertificate where
  row :=
    { word := augmentedWord010
      source := 3
      target := -6
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord010_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord010_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow034

def augmentedRow035 : WordCertificate where
  row :=
    { word := augmentedWord010
      source := 4
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord010_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord010_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow035

def augmentedRow036 : WordCertificate where
  row :=
    { word := augmentedWord010
      source := 6
      target := -3
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord010_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord010_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow036

def augmentedRow037 : WordCertificate where
  row :=
    { word := augmentedWord011
      source := 2
      target := 1
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord011_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord011_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow037

def augmentedRow038 : WordCertificate where
  row :=
    { word := augmentedWord012
      source := 21
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-105/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord012_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord012_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow038

def augmentedRow039 : WordCertificate where
  row :=
    { word := augmentedWord012
      source := 22
      target := -1
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 210
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord012_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord012_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow039

def augmentedRow040 : WordCertificate where
  row :=
    { word := augmentedWord013
      source := 20
      target := -1
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -126
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord013_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord013_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow040

def augmentedRow041 : WordCertificate where
  row :=
    { word := augmentedWord013
      source := 21
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-63/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord013_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord013_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow041

def augmentedRow042 : WordCertificate where
  row :=
    { word := augmentedWord013
      source := 22
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 63
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord013_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord013_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow042

def augmentedRow043 : WordCertificate where
  row :=
    { word := augmentedWord014
      source := 18
      target := -3
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord014_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord014_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow043

def augmentedRow044 : WordCertificate where
  row :=
    { word := augmentedWord014
      source := 20
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord014_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord014_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow044

def augmentedRow045 : WordCertificate where
  row :=
    { word := augmentedWord014
      source := 21
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord014_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord014_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow045

def augmentedRow046 : WordCertificate where
  row :=
    { word := augmentedWord014
      source := 23
      target := -8
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord014_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord014_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow046

def augmentedRow047 : WordCertificate where
  row :=
    { word := augmentedWord014
      source := 24
      target := -6
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord014_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord014_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow047



def augmentedRow048 : WordCertificate where
  row :=
    { word := augmentedWord014
      source := 26
      target := -5
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord014_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord014_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow048

def augmentedRow049 : WordCertificate where
  row :=
    { word := augmentedWord015
      source := 16
      target := 5
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord015_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord015_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow049

def augmentedRow050 : WordCertificate where
  row :=
    { word := augmentedWord015
      source := 18
      target := 6
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord015_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord015_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow050

def augmentedRow051 : WordCertificate where
  row :=
    { word := augmentedWord015
      source := 19
      target := 8
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord015_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord015_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow051

def augmentedRow052 : WordCertificate where
  row :=
    { word := augmentedWord015
      source := 21
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord015_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord015_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow052

def augmentedRow053 : WordCertificate where
  row :=
    { word := augmentedWord015
      source := 22
      target := 2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord015_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord015_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow053

def augmentedRow054 : WordCertificate where
  row :=
    { word := augmentedWord015
      source := 24
      target := 3
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord015_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord015_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow054

def augmentedRow055 : WordCertificate where
  row :=
    { word := augmentedWord016
      source := 20
      target := 2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -63
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord016_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord016_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow055

def augmentedRow056 : WordCertificate where
  row :=
    { word := augmentedWord016
      source := 21
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (63/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord016_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord016_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow056

def augmentedRow057 : WordCertificate where
  row :=
    { word := augmentedWord016
      source := 22
      target := 1
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 126
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord016_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord016_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow057

def augmentedRow058 : WordCertificate where
  row :=
    { word := augmentedWord017
      source := 34
      target := -19
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord017_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord017_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow058

def augmentedRow059 : WordCertificate where
  row :=
    { word := augmentedWord017
      source := 36
      target := -18
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord017_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord017_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow059

def augmentedRow060 : WordCertificate where
  row :=
    { word := augmentedWord017
      source := 37
      target := -16
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord017_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord017_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow060

def augmentedRow061 : WordCertificate where
  row :=
    { word := augmentedWord017
      source := 39
      target := -24
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord017_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord017_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow061

def augmentedRow062 : WordCertificate where
  row :=
    { word := augmentedWord017
      source := 40
      target := -22
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord017_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord017_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow062

def augmentedRow063 : WordCertificate where
  row :=
    { word := augmentedWord018
      source := 4
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -189
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord018_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord018_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow063

def augmentedRow064 : WordCertificate where
  row :=
    { word := augmentedWord019
      source := 0
      target := 21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord019_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord019_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow064

def augmentedRow065 : WordCertificate where
  row :=
    { word := augmentedWord019
      source := 2
      target := 22
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord019_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord019_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow065

def augmentedRow066 : WordCertificate where
  row :=
    { word := augmentedWord019
      source := 3
      target := 24
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord019_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord019_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow066

def augmentedRow067 : WordCertificate where
  row :=
    { word := augmentedWord019
      source := 5
      target := 16
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord019_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord019_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow067

def augmentedRow068 : WordCertificate where
  row :=
    { word := augmentedWord019
      source := 6
      target := 18
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord019_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord019_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow068

def augmentedRow069 : WordCertificate where
  row :=
    { word := augmentedWord019
      source := 8
      target := 19
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord019_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord019_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow069

def augmentedRow070 : WordCertificate where
  row :=
    { word := augmentedWord020
      source := 4
      target := 2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -231
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord020_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord020_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow070

def augmentedRow071 : WordCertificate where
  row :=
    { word := augmentedWord021
      source := 0
      target := -21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord021_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord021_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow071



def augmentedRow072 : WordCertificate where
  row :=
    { word := augmentedWord022
      source := 38
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -210
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord022_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord022_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow072

def augmentedRow073 : WordCertificate where
  row :=
    { word := augmentedWord023
      source := 34
      target := 23
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord023_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord023_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow073

def augmentedRow074 : WordCertificate where
  row :=
    { word := augmentedWord023
      source := 36
      target := 24
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord023_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord023_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow074

def augmentedRow075 : WordCertificate where
  row :=
    { word := augmentedWord023
      source := 37
      target := 26
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord023_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord023_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow075

def augmentedRow076 : WordCertificate where
  row :=
    { word := augmentedWord023
      source := 39
      target := 18
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord023_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord023_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow076

def augmentedRow077 : WordCertificate where
  row :=
    { word := augmentedWord023
      source := 40
      target := 20
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord023_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord023_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow077

def augmentedRow078 : WordCertificate where
  row :=
    { word := augmentedWord024
      source := 38
      target := 2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -252
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord024_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord024_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow078

def augmentedRow079 : WordCertificate where
  row :=
    { word := augmentedWord025
      source := 0
      target := -21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord025_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord025_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow079

def augmentedRow080 : WordCertificate where
  row :=
    { word := augmentedWord025
      source := 2
      target := -20
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord025_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord025_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow080

def augmentedRow081 : WordCertificate where
  row :=
    { word := augmentedWord025
      source := 3
      target := -18
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord025_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord025_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow081

def augmentedRow082 : WordCertificate where
  row :=
    { word := augmentedWord025
      source := 5
      target := -26
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord025_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord025_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow082

def augmentedRow083 : WordCertificate where
  row :=
    { word := augmentedWord025
      source := 6
      target := -24
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord025_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord025_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow083

def augmentedRow084 : WordCertificate where
  row :=
    { word := augmentedWord025
      source := 8
      target := -23
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord025_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord025_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow084

def augmentedRow085 : WordCertificate where
  row :=
    { word := augmentedWord026
      source := 0
      target := 21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord026_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord026_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow085

def augmentedRow086 : WordCertificate where
  row :=
    { word := augmentedWord027
      source := 22
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -168
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord027_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord027_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow086

def augmentedRow087 : WordCertificate where
  row :=
    { word := augmentedWord028
      source := 20
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 189
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord028_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord028_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow087

def augmentedRow088 : WordCertificate where
  row :=
    { word := augmentedWord029
      source := 40
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 210
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord029_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord029_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow088

def augmentedRow089 : WordCertificate where
  row :=
    { word := augmentedWord030
      source := 22
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -378
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord030_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord030_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow089

def augmentedRow090 : WordCertificate where
  row :=
    { word := augmentedWord031
      source := 18
      target := 39
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord031_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord031_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow090

def augmentedRow091 : WordCertificate where
  row :=
    { word := augmentedWord031
      source := 20
      target := 40
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord031_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord031_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow091

def augmentedRow092 : WordCertificate where
  row :=
    { word := augmentedWord031
      source := 21
      target := 42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord031_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord031_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow092

def augmentedRow093 : WordCertificate where
  row :=
    { word := augmentedWord031
      source := 23
      target := 34
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord031_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord031_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow093

def augmentedRow094 : WordCertificate where
  row :=
    { word := augmentedWord031
      source := 24
      target := 36
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord031_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord031_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow094

def augmentedRow095 : WordCertificate where
  row :=
    { word := augmentedWord031
      source := 26
      target := 37
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord031_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord031_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow095



def augmentedRow096 : WordCertificate where
  row :=
    { word := augmentedWord032
      source := 22
      target := 2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -420
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord032_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord032_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow096

def augmentedRow097 : WordCertificate where
  row :=
    { word := augmentedWord033
      source := 16
      target := -37
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord033_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord033_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow097

def augmentedRow098 : WordCertificate where
  row :=
    { word := augmentedWord033
      source := 18
      target := -36
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord033_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord033_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow098

def augmentedRow099 : WordCertificate where
  row :=
    { word := augmentedWord033
      source := 19
      target := -34
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord033_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord033_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow099

def augmentedRow100 : WordCertificate where
  row :=
    { word := augmentedWord033
      source := 21
      target := -42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord033_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord033_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow100

def augmentedRow101 : WordCertificate where
  row :=
    { word := augmentedWord033
      source := 22
      target := -40
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord033_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord033_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow101

def augmentedRow102 : WordCertificate where
  row :=
    { word := augmentedWord033
      source := 24
      target := -39
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord033_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord033_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow102

def augmentedRow103 : WordCertificate where
  row :=
    { word := augmentedWord034
      source := 2
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -189
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord034_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord034_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow103

def augmentedRow104 : WordCertificate where
  row :=
    { word := augmentedWord035
      source := 40
      target := 41
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord035_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord035_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow104

def augmentedRow105 : WordCertificate where
  row :=
    { word := augmentedWord036
      source := 36
      target := -39
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord036_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord036_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow105

def augmentedRow106 : WordCertificate where
  row :=
    { word := augmentedWord036
      source := 38
      target := -38
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord036_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord036_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow106

def augmentedRow107 : WordCertificate where
  row :=
    { word := augmentedWord036
      source := 39
      target := -36
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord036_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord036_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow107

def augmentedRow108 : WordCertificate where
  row :=
    { word := augmentedWord036
      source := 41
      target := -44
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord036_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord036_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow108

def augmentedRow109 : WordCertificate where
  row :=
    { word := augmentedWord037
      source := 2
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -399
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord037_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord037_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow109

def augmentedRow110 : WordCertificate where
  row :=
    { word := augmentedWord038
      source := 1
      target := 44
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord038_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord038_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow110

def augmentedRow111 : WordCertificate where
  row :=
    { word := augmentedWord038
      source := 3
      target := 36
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord038_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord038_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow111

def augmentedRow112 : WordCertificate where
  row :=
    { word := augmentedWord038
      source := 4
      target := 38
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord038_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord038_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow112

def augmentedRow113 : WordCertificate where
  row :=
    { word := augmentedWord038
      source := 6
      target := 39
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord038_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord038_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow113

def augmentedRow114 : WordCertificate where
  row :=
    { word := augmentedWord039
      source := 2
      target := -41
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord039_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord039_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow114

def augmentedRow115 : WordCertificate where
  row :=
    { word := augmentedWord040
      source := 0
      target := 44
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := -21
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow115

def augmentedRow116 : WordCertificate where
  row :=
    { word := augmentedWord040
      source := 14
      target := 45
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (28/3)
  slope := -14
  count := 1
  powers := (2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow116

def augmentedRow117 : WordCertificate where
  row :=
    { word := augmentedWord040
      source := 21
      target := 46
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (21/4)
  slope := (-21/2)
  count := 1
  powers := (-2, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow117

def augmentedRow118 : WordCertificate where
  row :=
    { word := augmentedWord040
      source := 28
      target := 48
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := -7
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow118

def augmentedRow119 : WordCertificate where
  row :=
    { word := augmentedWord040
      source := 30
      target := 49
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (12/7)
  slope := -6
  count := 1
  powers := (2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow119



def augmentedRow120 : WordCertificate where
  row :=
    { word := augmentedWord040
      source := 35
      target := 54
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/12)
  slope := (-7/2)
  count := 1
  powers := (-2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow120

def augmentedRow121 : WordCertificate where
  row :=
    { word := augmentedWord040
      source := 36
      target := 56
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := -3
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow121

def augmentedRow122 : WordCertificate where
  row :=
    { word := augmentedWord040
      source := 38
      target := 63
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (4/21)
  slope := -2
  count := 1
  powers := (2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow122

def augmentedRow123 : WordCertificate where
  row :=
    { word := augmentedWord040
      source := 39
      target := 70
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/28)
  slope := (-3/2)
  count := 1
  powers := (-2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow123

def augmentedRow124 : WordCertificate where
  row :=
    { word := augmentedWord040
      source := 40
      target := 84
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := -1
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow124

def augmentedRow125 : WordCertificate where
  row :=
    { word := augmentedWord040
      source := 41
      target := 126
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/84)
  slope := (-1/2)
  count := 1
  powers := (-2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord040_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow125

def augmentedRow126 : WordCertificate where
  row :=
    { word := augmentedWord041
      source := 0
      target := -40
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := -21
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow126

def augmentedRow127 : WordCertificate where
  row :=
    { word := augmentedWord041
      source := 14
      target := -39
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (28/3)
  slope := -14
  count := 1
  powers := (2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow127

def augmentedRow128 : WordCertificate where
  row :=
    { word := augmentedWord041
      source := 21
      target := -38
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (21/4)
  slope := (-21/2)
  count := 1
  powers := (-2, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow128

def augmentedRow129 : WordCertificate where
  row :=
    { word := augmentedWord041
      source := 28
      target := -36
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := -7
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow129

def augmentedRow130 : WordCertificate where
  row :=
    { word := augmentedWord041
      source := 30
      target := -35
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (12/7)
  slope := -6
  count := 1
  powers := (2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow130

def augmentedRow131 : WordCertificate where
  row :=
    { word := augmentedWord041
      source := 35
      target := -30
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/12)
  slope := (-7/2)
  count := 1
  powers := (-2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow131

def augmentedRow132 : WordCertificate where
  row :=
    { word := augmentedWord041
      source := 36
      target := -28
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := -3
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow132

def augmentedRow133 : WordCertificate where
  row :=
    { word := augmentedWord041
      source := 38
      target := -21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (4/21)
  slope := -2
  count := 1
  powers := (2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow133

def augmentedRow134 : WordCertificate where
  row :=
    { word := augmentedWord041
      source := 39
      target := -14
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/28)
  slope := (-3/2)
  count := 1
  powers := (-2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow134

def augmentedRow135 : WordCertificate where
  row :=
    { word := augmentedWord041
      source := 40
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := -1
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow135

def augmentedRow136 : WordCertificate where
  row :=
    { word := augmentedWord041
      source := 41
      target := 42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/84)
  slope := (-1/2)
  count := 1
  powers := (-2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord041_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow136

def augmentedRow137 : WordCertificate where
  row :=
    { word := augmentedWord042
      source := 38
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := -11
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord042_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord042_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow137

def augmentedRow138 : WordCertificate where
  row :=
    { word := augmentedWord043
      source := 21
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (21/4)
  slope := (-399/2)
  count := 1
  powers := (-2, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord043_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord043_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow138

def augmentedRow139 : WordCertificate where
  row :=
    { word := augmentedWord043
      source := 22
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := -19
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord043_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord043_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow139

def augmentedRow140 : WordCertificate where
  row :=
    { word := augmentedWord044
      source := 0
      target := 22
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := -42
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow140

def augmentedRow141 : WordCertificate where
  row :=
    { word := augmentedWord044
      source := 14
      target := 24
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := -14
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow141

def augmentedRow142 : WordCertificate where
  row :=
    { word := augmentedWord044
      source := 18
      target := 28
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := -6
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow142

def augmentedRow143 : WordCertificate where
  row :=
    { word := augmentedWord044
      source := 20
      target := 42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := -2
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow143



def augmentedRow144 : WordCertificate where
  row :=
    { word := augmentedWord044
      source := 22
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := 2
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow144

def augmentedRow145 : WordCertificate where
  row :=
    { word := augmentedWord044
      source := 24
      target := 14
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := 6
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow145

def augmentedRow146 : WordCertificate where
  row :=
    { word := augmentedWord044
      source := 28
      target := 18
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := 14
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord044_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow146

def augmentedRow147 : WordCertificate where
  row :=
    { word := augmentedWord045
      source := 21
      target := 2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (21/4)
  slope := (-483/2)
  count := 1
  powers := (-2, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord045_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord045_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow147

def augmentedRow148 : WordCertificate where
  row :=
    { word := augmentedWord045
      source := 22
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := 23
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord045_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord045_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow148

def augmentedRow149 : WordCertificate where
  row :=
    { word := augmentedWord046
      source := 0
      target := -20
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := -42
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow149

def augmentedRow150 : WordCertificate where
  row :=
    { word := augmentedWord046
      source := 14
      target := -18
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := -14
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow150

def augmentedRow151 : WordCertificate where
  row :=
    { word := augmentedWord046
      source := 18
      target := -14
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := -6
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow151

def augmentedRow152 : WordCertificate where
  row :=
    { word := augmentedWord046
      source := 20
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := -2
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow152

def augmentedRow153 : WordCertificate where
  row :=
    { word := augmentedWord046
      source := 22
      target := -42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := 2
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow153

def augmentedRow154 : WordCertificate where
  row :=
    { word := augmentedWord046
      source := 24
      target := -28
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := 6
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow154

def augmentedRow155 : WordCertificate where
  row :=
    { word := augmentedWord046
      source := 28
      target := -24
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := 14
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord046_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow155

def augmentedRow156 : WordCertificate where
  row :=
    { word := augmentedWord047
      source := 0
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := -210
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord047_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord047_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow156

def augmentedRow157 : WordCertificate where
  row :=
    { word := augmentedWord047
      source := 4
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := -10
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord047_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord047_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow157

def augmentedRow158 : WordCertificate where
  row :=
    { word := augmentedWord048
      source := 0
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := -420
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord048_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord048_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow158

def augmentedRow159 : WordCertificate where
  row :=
    { word := augmentedWord048
      source := 2
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := -20
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord048_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord048_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow159

def augmentedRow160 : WordCertificate where
  row :=
    { word := augmentedWord049
      source := 1
      target := -42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/84)
  slope := (1/2)
  count := 1
  powers := (-2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow160

def augmentedRow161 : WordCertificate where
  row :=
    { word := augmentedWord049
      source := 2
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := 1
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow161

def augmentedRow162 : WordCertificate where
  row :=
    { word := augmentedWord049
      source := 3
      target := 14
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/28)
  slope := (3/2)
  count := 1
  powers := (-2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow162

def augmentedRow163 : WordCertificate where
  row :=
    { word := augmentedWord049
      source := 4
      target := 21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (4/21)
  slope := 2
  count := 1
  powers := (2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow163

def augmentedRow164 : WordCertificate where
  row :=
    { word := augmentedWord049
      source := 6
      target := 28
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := 3
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow164

def augmentedRow165 : WordCertificate where
  row :=
    { word := augmentedWord049
      source := 7
      target := 30
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/12)
  slope := (7/2)
  count := 1
  powers := (-2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow165

def augmentedRow166 : WordCertificate where
  row :=
    { word := augmentedWord049
      source := 12
      target := 35
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (12/7)
  slope := 6
  count := 1
  powers := (2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow166

def augmentedRow167 : WordCertificate where
  row :=
    { word := augmentedWord049
      source := 14
      target := 36
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := 7
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow167



def augmentedRow168 : WordCertificate where
  row :=
    { word := augmentedWord049
      source := 21
      target := 38
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (21/4)
  slope := (21/2)
  count := 1
  powers := (-2, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow168

def augmentedRow169 : WordCertificate where
  row :=
    { word := augmentedWord049
      source := 28
      target := 39
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (28/3)
  slope := 14
  count := 1
  powers := (2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord049_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow169

def augmentedRow170 : WordCertificate where
  row :=
    { word := augmentedWord050
      source := 0
      target := 2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := -462
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord050_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord050_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow170

def augmentedRow171 : WordCertificate where
  row :=
    { word := augmentedWord050
      source := 2
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := 22
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord050_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord050_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow171

def augmentedRow172 : WordCertificate where
  row :=
    { word := augmentedWord051
      source := 0
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := 462
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord051_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord051_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow172

def augmentedRow173 : WordCertificate where
  row :=
    { word := augmentedWord052
      source := 1
      target := -126
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/84)
  slope := (1/2)
  count := 1
  powers := (-2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow173

def augmentedRow174 : WordCertificate where
  row :=
    { word := augmentedWord052
      source := 2
      target := -84
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := 1
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow174

def augmentedRow175 : WordCertificate where
  row :=
    { word := augmentedWord052
      source := 3
      target := -70
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/28)
  slope := (3/2)
  count := 1
  powers := (-2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow175

def augmentedRow176 : WordCertificate where
  row :=
    { word := augmentedWord052
      source := 4
      target := -63
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (4/21)
  slope := 2
  count := 1
  powers := (2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow176

def augmentedRow177 : WordCertificate where
  row :=
    { word := augmentedWord052
      source := 6
      target := -56
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := 3
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow177

def augmentedRow178 : WordCertificate where
  row :=
    { word := augmentedWord052
      source := 7
      target := -54
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/12)
  slope := (7/2)
  count := 1
  powers := (-2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow178

def augmentedRow179 : WordCertificate where
  row :=
    { word := augmentedWord052
      source := 12
      target := -49
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (12/7)
  slope := 6
  count := 1
  powers := (2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow179

def augmentedRow180 : WordCertificate where
  row :=
    { word := augmentedWord052
      source := 14
      target := -48
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := 7
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow180

def augmentedRow181 : WordCertificate where
  row :=
    { word := augmentedWord052
      source := 21
      target := -46
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (21/4)
  slope := (21/2)
  count := 1
  powers := (-2, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow181

def augmentedRow182 : WordCertificate where
  row :=
    { word := augmentedWord052
      source := 28
      target := -45
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (28/3)
  slope := 14
  count := 1
  powers := (2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord052_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow182

def augmentedRow183 : WordCertificate where
  row :=
    { word := augmentedWord053
      source := 0
      target := 2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := 420
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord053_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord053_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow183

def augmentedRow184 : WordCertificate where
  row :=
    { word := augmentedWord054
      source := 0
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := 231
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord054_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord054_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow184

def augmentedRow185 : WordCertificate where
  row :=
    { word := augmentedWord055
      source := 0
      target := 4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := 210
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord055_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord055_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow185

def augmentedRow186 : WordCertificate where
  row :=
    { word := augmentedWord056
      source := 0
      target := 20
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := 42
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord056_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord056_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow186

def augmentedRow187 : WordCertificate where
  row :=
    { word := augmentedWord057
      source := 0
      target := 40
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := 21
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord057_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord057_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow187

def augmentedRow188 : WordCertificate where
  row :=
    { word := augmentedWord058
      source := 0
      target := -44
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := 21
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord058_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord058_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow188

def augmentedRow189 : WordCertificate where
  row :=
    { word := augmentedWord059
      source := 40
      target := -43
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord059_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord059_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow189

def augmentedRow190 : WordCertificate where
  row :=
    { word := augmentedWord060
      source := 36
      target := 45
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord060_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord060_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow190

def augmentedRow191 : WordCertificate where
  row :=
    { word := augmentedWord060
      source := 38
      target := 46
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord060_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord060_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow191



def augmentedRow192 : WordCertificate where
  row :=
    { word := augmentedWord060
      source := 39
      target := 48
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord060_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord060_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow192

def augmentedRow193 : WordCertificate where
  row :=
    { word := augmentedWord060
      source := 41
      target := 40
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord060_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord060_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow193

def augmentedRow194 : WordCertificate where
  row :=
    { word := augmentedWord061
      source := 2
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 483
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord061_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord061_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow194

def augmentedRow195 : WordCertificate where
  row :=
    { word := augmentedWord062
      source := 1
      target := -40
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord062_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord062_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow195

def augmentedRow196 : WordCertificate where
  row :=
    { word := augmentedWord062
      source := 3
      target := -48
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord062_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord062_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow196

def augmentedRow197 : WordCertificate where
  row :=
    { word := augmentedWord062
      source := 4
      target := -46
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord062_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord062_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow197

def augmentedRow198 : WordCertificate where
  row :=
    { word := augmentedWord062
      source := 6
      target := -45
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord062_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord062_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow198

def augmentedRow199 : WordCertificate where
  row :=
    { word := augmentedWord063
      source := 2
      target := 43
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord063_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord063_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow199

def augmentedRow200 : WordCertificate where
  row :=
    { word := augmentedWord064
      source := 22
      target := -2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 504
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord064_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord064_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow200

def augmentedRow201 : WordCertificate where
  row :=
    { word := augmentedWord065
      source := 18
      target := -45
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord065_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord065_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow201

def augmentedRow202 : WordCertificate where
  row :=
    { word := augmentedWord065
      source := 20
      target := -44
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord065_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord065_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow202

def augmentedRow203 : WordCertificate where
  row :=
    { word := augmentedWord065
      source := 21
      target := -42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord065_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord065_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow203

def augmentedRow204 : WordCertificate where
  row :=
    { word := augmentedWord065
      source := 23
      target := -50
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord065_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord065_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow204

def augmentedRow205 : WordCertificate where
  row :=
    { word := augmentedWord065
      source := 24
      target := -48
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord065_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord065_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow205

def augmentedRow206 : WordCertificate where
  row :=
    { word := augmentedWord065
      source := 26
      target := -47
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord065_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord065_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow206

def augmentedRow207 : WordCertificate where
  row :=
    { word := augmentedWord066
      source := 22
      target := 2
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 462
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord066_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord066_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow207

def augmentedRow208 : WordCertificate where
  row :=
    { word := augmentedWord067
      source := 16
      target := 47
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord067_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord067_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow208

def augmentedRow209 : WordCertificate where
  row :=
    { word := augmentedWord067
      source := 18
      target := 48
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord067_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord067_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow209

def augmentedRow210 : WordCertificate where
  row :=
    { word := augmentedWord067
      source := 19
      target := 50
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord067_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord067_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow210

def augmentedRow211 : WordCertificate where
  row :=
    { word := augmentedWord067
      source := 21
      target := 42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord067_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord067_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow211

def augmentedRow212 : WordCertificate where
  row :=
    { word := augmentedWord067
      source := 22
      target := 44
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord067_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord067_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow212

def augmentedRow213 : WordCertificate where
  row :=
    { word := augmentedWord067
      source := 24
      target := 45
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord067_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord067_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow213

def augmentedRow214 : WordCertificate where
  row :=
    { word := augmentedWord068
      source := 2
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 252
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord068_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord068_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow214

def augmentedRow215 : WordCertificate where
  row :=
    { word := augmentedWord069
      source := 2
      target := 4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 231
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord069_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord069_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow215



def augmentedRow216 : WordCertificate where
  row :=
    { word := augmentedWord070
      source := 22
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 273
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord070_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord070_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow216

def augmentedRow217 : WordCertificate where
  row :=
    { word := augmentedWord071
      source := 22
      target := 4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 252
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord071_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord071_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow217

def augmentedRow218 : WordCertificate where
  row :=
    { word := augmentedWord072
      source := 0
      target := 63
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord072_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord072_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow218

def augmentedRow219 : WordCertificate where
  row :=
    { word := augmentedWord072
      source := 2
      target := 64
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord072_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord072_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow219

def augmentedRow220 : WordCertificate where
  row :=
    { word := augmentedWord072
      source := 3
      target := 66
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord072_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord072_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow220

def augmentedRow221 : WordCertificate where
  row :=
    { word := augmentedWord072
      source := 5
      target := 58
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord072_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord072_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow221

def augmentedRow222 : WordCertificate where
  row :=
    { word := augmentedWord072
      source := 6
      target := 60
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord072_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord072_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow222

def augmentedRow223 : WordCertificate where
  row :=
    { word := augmentedWord072
      source := 8
      target := 61
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord072_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord072_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow223

def augmentedRow224 : WordCertificate where
  row :=
    { word := augmentedWord073
      source := 0
      target := 21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -126
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord073_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord073_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow224

def augmentedRow225 : WordCertificate where
  row :=
    { word := augmentedWord073
      source := 1
      target := 22
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-63/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord073_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord073_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow225

def augmentedRow226 : WordCertificate where
  row :=
    { word := augmentedWord073
      source := 2
      target := 20
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 63
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord073_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord073_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow226

def augmentedRow227 : WordCertificate where
  row :=
    { word := augmentedWord074
      source := 0
      target := -21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 126
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord074_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord074_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow227

def augmentedRow228 : WordCertificate where
  row :=
    { word := augmentedWord075
      source := 0
      target := -63
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord075_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord075_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow228

def augmentedRow229 : WordCertificate where
  row :=
    { word := augmentedWord076
      source := 40
      target := 22
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -63
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord076_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord076_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow229

def augmentedRow230 : WordCertificate where
  row :=
    { word := augmentedWord076
      source := 41
      target := 20
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (63/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord076_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord076_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow230

def augmentedRow231 : WordCertificate where
  row :=
    { word := augmentedWord077
      source := 34
      target := 65
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord077_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord077_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow231

def augmentedRow232 : WordCertificate where
  row :=
    { word := augmentedWord077
      source := 36
      target := 66
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord077_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord077_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow232

def augmentedRow233 : WordCertificate where
  row :=
    { word := augmentedWord077
      source := 37
      target := 68
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord077_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord077_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow233

def augmentedRow234 : WordCertificate where
  row :=
    { word := augmentedWord077
      source := 39
      target := 60
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord077_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord077_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow234

def augmentedRow235 : WordCertificate where
  row :=
    { word := augmentedWord077
      source := 40
      target := 62
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord077_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord077_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow235

def augmentedRow236 : WordCertificate where
  row :=
    { word := augmentedWord078
      source := 0
      target := 21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 126
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord078_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord078_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow236

def augmentedRow237 : WordCertificate where
  row :=
    { word := augmentedWord079
      source := 0
      target := 63
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord079_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord079_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow237

def augmentedRow238 : WordCertificate where
  row :=
    { word := augmentedWord080
      source := 18
      target := 81
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord080_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord080_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow238

def augmentedRow239 : WordCertificate where
  row :=
    { word := augmentedWord080
      source := 20
      target := 82
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord080_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord080_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow239



def augmentedRow240 : WordCertificate where
  row :=
    { word := augmentedWord080
      source := 21
      target := 84
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord080_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord080_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow240

def augmentedRow241 : WordCertificate where
  row :=
    { word := augmentedWord080
      source := 23
      target := 76
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord080_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord080_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow241

def augmentedRow242 : WordCertificate where
  row :=
    { word := augmentedWord080
      source := 24
      target := 78
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord080_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord080_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow242

def augmentedRow243 : WordCertificate where
  row :=
    { word := augmentedWord080
      source := 26
      target := 79
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord080_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord080_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow243

def augmentedRow244 : WordCertificate where
  row :=
    { word := augmentedWord081
      source := 22
      target := 20
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 84
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord081_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord081_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow244

def augmentedRow245 : WordCertificate where
  row :=
    { word := augmentedWord082
      source := 1
      target := 86
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord082_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord082_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow245

def augmentedRow246 : WordCertificate where
  row :=
    { word := augmentedWord082
      source := 3
      target := 78
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord082_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord082_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow246

def augmentedRow247 : WordCertificate where
  row :=
    { word := augmentedWord082
      source := 4
      target := 80
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord082_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord082_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow247

def augmentedRow248 : WordCertificate where
  row :=
    { word := augmentedWord082
      source := 6
      target := 81
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord082_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord082_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow248

def augmentedRow249 : WordCertificate where
  row :=
    { word := augmentedWord083
      source := 2
      target := 40
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 42
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord083_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord083_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow249

def augmentedRow250 : WordCertificate where
  row :=
    { word := augmentedWord084
      source := 2
      target := -83
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord084_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord084_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow250

def augmentedRow251 : WordCertificate where
  row :=
    { word := augmentedWord085
      source := 1
      target := 0
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/84)
  slope := (1/2)
  count := 1
  powers := (-2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow251

def augmentedRow252 : WordCertificate where
  row :=
    { word := augmentedWord085
      source := 2
      target := 42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := 1
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow252

def augmentedRow253 : WordCertificate where
  row :=
    { word := augmentedWord085
      source := 3
      target := 56
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/28)
  slope := (3/2)
  count := 1
  powers := (-2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow253

def augmentedRow254 : WordCertificate where
  row :=
    { word := augmentedWord085
      source := 4
      target := 63
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (4/21)
  slope := 2
  count := 1
  powers := (2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow254

def augmentedRow255 : WordCertificate where
  row :=
    { word := augmentedWord085
      source := 6
      target := 70
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := 3
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow255

def augmentedRow256 : WordCertificate where
  row :=
    { word := augmentedWord085
      source := 7
      target := 72
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/12)
  slope := (7/2)
  count := 1
  powers := (-2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow256

def augmentedRow257 : WordCertificate where
  row :=
    { word := augmentedWord085
      source := 12
      target := 77
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (12/7)
  slope := 6
  count := 1
  powers := (2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow257

def augmentedRow258 : WordCertificate where
  row :=
    { word := augmentedWord085
      source := 14
      target := 78
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := 7
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow258

def augmentedRow259 : WordCertificate where
  row :=
    { word := augmentedWord085
      source := 21
      target := 80
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (21/4)
  slope := (21/2)
  count := 1
  powers := (-2, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow259

def augmentedRow260 : WordCertificate where
  row :=
    { word := augmentedWord085
      source := 28
      target := 81
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (28/3)
  slope := 14
  count := 1
  powers := (2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord085_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow260

def augmentedRow261 : WordCertificate where
  row :=
    { word := augmentedWord086
      source := 1
      target := -168
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/84)
  slope := (1/2)
  count := 1
  powers := (-2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow261

def augmentedRow262 : WordCertificate where
  row :=
    { word := augmentedWord086
      source := 2
      target := -126
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := 1
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow262

def augmentedRow263 : WordCertificate where
  row :=
    { word := augmentedWord086
      source := 3
      target := -112
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/28)
  slope := (3/2)
  count := 1
  powers := (-2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow263



def augmentedRow264 : WordCertificate where
  row :=
    { word := augmentedWord086
      source := 4
      target := -105
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (4/21)
  slope := 2
  count := 1
  powers := (2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow264

def augmentedRow265 : WordCertificate where
  row :=
    { word := augmentedWord086
      source := 6
      target := -98
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := 3
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow265

def augmentedRow266 : WordCertificate where
  row :=
    { word := augmentedWord086
      source := 7
      target := -96
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/12)
  slope := (7/2)
  count := 1
  powers := (-2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow266

def augmentedRow267 : WordCertificate where
  row :=
    { word := augmentedWord086
      source := 12
      target := -91
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (12/7)
  slope := 6
  count := 1
  powers := (2, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow267

def augmentedRow268 : WordCertificate where
  row :=
    { word := augmentedWord086
      source := 14
      target := -90
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := 7
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow268

def augmentedRow269 : WordCertificate where
  row :=
    { word := augmentedWord086
      source := 21
      target := -88
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (21/4)
  slope := (21/2)
  count := 1
  powers := (-2, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow269

def augmentedRow270 : WordCertificate where
  row :=
    { word := augmentedWord086
      source := 28
      target := -87
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (28/3)
  slope := 14
  count := 1
  powers := (2, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord086_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow270

def augmentedRow271 : WordCertificate where
  row :=
    { word := augmentedWord087
      source := 20
      target := 22
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -84
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord087_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord087_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow271

def augmentedRow272 : WordCertificate where
  row :=
    { word := augmentedWord088
      source := 1
      target := -82
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord088_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord088_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow272

def augmentedRow273 : WordCertificate where
  row :=
    { word := augmentedWord088
      source := 3
      target := -90
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord088_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord088_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow273

def augmentedRow274 : WordCertificate where
  row :=
    { word := augmentedWord088
      source := 4
      target := -88
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord088_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord088_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow274

def augmentedRow275 : WordCertificate where
  row :=
    { word := augmentedWord088
      source := 6
      target := -87
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord088_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord088_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow275

def augmentedRow276 : WordCertificate where
  row :=
    { word := augmentedWord089
      source := 2
      target := -44
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 42
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord089_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord089_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow276

def augmentedRow277 : WordCertificate where
  row :=
    { word := augmentedWord090
      source := 2
      target := 85
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord090_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord090_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow277

def augmentedRow278 : WordCertificate where
  row :=
    { word := augmentedWord091
      source := 18
      target := -87
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord091_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord091_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow278

def augmentedRow279 : WordCertificate where
  row :=
    { word := augmentedWord091
      source := 20
      target := -86
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord091_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord091_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow279

def augmentedRow280 : WordCertificate where
  row :=
    { word := augmentedWord091
      source := 21
      target := -84
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord091_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord091_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow280

def augmentedRow281 : WordCertificate where
  row :=
    { word := augmentedWord091
      source := 23
      target := -92
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (21/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord091_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord091_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow281

def augmentedRow282 : WordCertificate where
  row :=
    { word := augmentedWord091
      source := 24
      target := -90
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 21
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord091_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord091_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow282

def augmentedRow283 : WordCertificate where
  row :=
    { word := augmentedWord091
      source := 26
      target := -89
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord091_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord091_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow283

def augmentedRow284 : WordCertificate where
  row :=
    { word := augmentedWord092
      source := 1
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (483/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord092_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord092_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow284

def augmentedRow285 : WordCertificate where
  row :=
    { word := augmentedWord093
      source := 0
      target := 21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 210
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord093_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord093_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow285

def augmentedRow286 : WordCertificate where
  row :=
    { word := augmentedWord094
      source := 0
      target := 105
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 42
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord094_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord094_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow286

def augmentedRow287 : WordCertificate where
  row :=
    { word := augmentedWord095
      source := 20
      target := 41
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -126
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord095_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord095_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow287



def augmentedRow288 : WordCertificate where
  row :=
    { word := augmentedWord095
      source := 21
      target := 42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-63/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord095_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord095_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow288

def augmentedRow289 : WordCertificate where
  row :=
    { word := augmentedWord095
      source := 22
      target := 40
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 63
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord095_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord095_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow289

def augmentedRow290 : WordCertificate where
  row :=
    { word := augmentedWord096
      source := 0
      target := 64
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := -42
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow290

def augmentedRow291 : WordCertificate where
  row :=
    { word := augmentedWord096
      source := 14
      target := 66
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := -14
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow291

def augmentedRow292 : WordCertificate where
  row :=
    { word := augmentedWord096
      source := 18
      target := 70
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := -6
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow292

def augmentedRow293 : WordCertificate where
  row :=
    { word := augmentedWord096
      source := 20
      target := 84
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := -2
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow293

def augmentedRow294 : WordCertificate where
  row :=
    { word := augmentedWord096
      source := 22
      target := 42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/21)
  slope := 2
  count := 1
  powers := (0, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow294

def augmentedRow295 : WordCertificate where
  row :=
    { word := augmentedWord096
      source := 24
      target := 56
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (3/7)
  slope := 6
  count := 1
  powers := (0, 1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow295

def augmentedRow296 : WordCertificate where
  row :=
    { word := augmentedWord096
      source := 28
      target := 60
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (7/3)
  slope := 14
  count := 1
  powers := (0, -1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord096_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow296

def augmentedRow297 : WordCertificate where
  row :=
    { word := augmentedWord097
      source := 0
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := 672
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord097_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord097_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow297

def augmentedRow298 : WordCertificate where
  row :=
    { word := augmentedWord098
      source := 20
      target := -43
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := -126
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord098_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord098_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow298

def augmentedRow299 : WordCertificate where
  row :=
    { word := augmentedWord098
      source := 21
      target := -42
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (1/4)
  slope := (-63/2)
  count := 0
  powers := (-2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord098_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord098_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow299

def augmentedRow300 : WordCertificate where
  row :=
    { word := augmentedWord098
      source := 22
      target := -44
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 63
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord098_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord098_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow300

def augmentedRow301 : WordCertificate where
  row :=
    { word := augmentedWord099
      source := 2
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 693
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord099_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord099_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow301

def augmentedRow302 : WordCertificate where
  row :=
    { word := augmentedWord100
      source := 22
      target := -4
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 714
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord100_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord100_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow302

def augmentedRow303 : WordCertificate where
  row :=
    { word := augmentedWord101
      source := 0
      target := 63
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 4
  slope := 126
  count := 0
  powers := (2, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord101_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord101_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow303

def augmentedRow304 : WordCertificate where
  row :=
    { word := augmentedWord102
      source := 4
      target := 22
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -252
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord102_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord102_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow304

def augmentedRow305 : WordCertificate where
  row :=
    { word := augmentedWord103
      source := 38
      target := 22
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -273
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord103_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord103_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow305

def augmentedRow306 : WordCertificate where
  row :=
    { word := augmentedWord104
      source := 0
      target := 22
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := 399
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord104_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord104_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow306

def augmentedRow307 : WordCertificate where
  row :=
    { word := augmentedWord105
      source := 0
      target := 38
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := 231
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord105_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord105_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow307

def augmentedRow308 : WordCertificate where
  row :=
    { word := augmentedWord106
      source := 2
      target := 22
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 420
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord106_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord106_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow308

def augmentedRow309 : WordCertificate where
  row :=
    { word := augmentedWord107
      source := 2
      target := 38
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 252
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord107_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord107_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow309

def augmentedRow310 : WordCertificate where
  row :=
    { word := augmentedWord108
      source := 2
      target := 22
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := -462
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord108_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord108_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow310

def augmentedRow311 : WordCertificate where
  row :=
    { word := augmentedWord109
      source := 22
      target := 38
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 273
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord109_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord109_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow311



def augmentedRow312 : WordCertificate where
  row :=
    { word := augmentedWord110
      source := 0
      target := 22
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := -483
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord110_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord110_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow312

def augmentedRow313 : WordCertificate where
  row :=
    { word := augmentedWord110
      source := 2
      target := 21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (4/21)
  slope := 46
  count := 1
  powers := (2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord110_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord110_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow313

def augmentedRow314 : WordCertificate where
  row :=
    { word := augmentedWord111
      source := 0
      target := -46
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 21
  slope := 231
  count := 1
  powers := (0, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord111_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord111_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow314

def augmentedRow315 : WordCertificate where
  row :=
    { word := augmentedWord112
      source := 21
      target := 22
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (21/4)
  slope := (-525/2)
  count := 1
  powers := (-2, 1, 1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord112_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord112_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow315

def augmentedRow316 : WordCertificate where
  row :=
    { word := augmentedWord112
      source := 22
      target := 21
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := (4/21)
  slope := 50
  count := 1
  powers := (2, -1, -1)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord112_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord112_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow316

def augmentedRow317 : WordCertificate where
  row :=
    { word := augmentedWord113
      source := 2
      target := -46
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 252
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord113_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord113_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow317

def augmentedRow318 : WordCertificate where
  row :=
    { word := augmentedWord114
      source := 22
      target := -46
      nonaffine := by decide
      denominator := by decide
      closed := by decide }
  rate := 1
  slope := 273
  count := 0
  powers := (0, 0, 0)
  rate_eq := by norm_num [rationalRate,integerDen,augmentedWord114_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [rationalDerivative,integerDen,augmentedWord114_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms augmentedRow318

end SmallLevelTwentyOneKnownWords
end
