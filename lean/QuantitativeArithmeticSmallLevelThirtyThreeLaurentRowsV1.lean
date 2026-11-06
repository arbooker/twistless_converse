module
public import QuantitativeArithmeticSmallLevelThirtyThreeGridAssemblyV1
public import QuantitativeArithmeticSmallLevelThirtyThreeLeadingRatesV1
public import QuantitativeArithmeticSmallLevelThirtyThreeWordParityV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex SmallLevelPrimeRates  FinitenessNormalizedTwistProduct

def primeParameter (p : ℕ) (X Y Z : ℂ) : ℂ :=
  if p=2 then X else if p=3 then Y else Z

def primeEigenvalue (p : ℕ) (a u v : ℂ) : ℂ :=
  if p=2 then a else if p=3 then u else v

def laurentHecke (X Y Z a u v : ℂ) (w : Fin 66→ℂ) (i : Fin 61) : ℂ :=
  (∑ j∈Finset.range (gridHeckeP i),w (gridIndex (gridHeckeT i+(j:ℤ)*(66/gridHeckeP i:ℕ))))-
    primeEigenvalue (gridHeckeP i) a u v*(primeParameter (gridHeckeP i) X Y Z)⁻¹*
      w (gridIndex ((gridHeckeP i:ℤ)*gridHeckeT i))+
    (if gridHeckeP i∣33 then 0 else ((primeParameter (gridHeckeP i) X Y Z)⁻¹)^2*
      w (gridIndex ((gridHeckeP i:ℤ)^2*gridHeckeT i)))

def laurentRows (X Y Z η a u v : ℂ) (w : Fin 66→ℂ) : GridSource→ℂ
  | .word i => w (groupIndex i)-
      (η^(frickeCount (sourceWord (groupSource i))%2)*(-u)^(threeCount (sourceWord (groupSource i))%2))*
      monomial (groupPowers i) X Y Z*w (gridIndex (groupTarget i))
  | .taylor i => gridSample (gridTaylorQ i) (gridTaylorT i) w-
      ((if 3∣gridTaylorQ i then -u else 1)*(if 11∣gridTaylorQ i then -v else 1))*η*
        monomial (taylorPowers i) X Y Z*gridSample (gridTaylorQ i) (gridTaylorPartner i) w
  | .entire i => gridSample (gridEntireQ i) 0 w
  | .hecke i => laurentHecke X Y Z a u v w i
  | .infinity i => w (gridInfinityIndex i)

theorem primeParameter_actual (m : ℕ) (s : ℂ) (i : Fin 61) :
    primeParameter (gridHeckeP i) (parameter 2 m s) (parameter 3 m s)
      (parameter 11 m s)=parameter (gridHeckeP i) m s := by
  fin_cases i <;> rfl

theorem primeEigenvalue_actual (f : ℕ→ℂ) (i : Fin 61) :
    primeEigenvalue (gridHeckeP i) (badParameter f 2) (badParameter f 3)
      (badParameter f 11)=(Real.sqrt (gridHeckeP i):ℂ)*f (gridHeckeP i) := by
  fin_cases i <;> rfl

/-- The polynomial rows are precisely the original physical leading rows. -/
theorem leadingRows_laurent (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (ε s : ℂ) (hε : ε=1 ∨ ε= -1) (v : Fin 66→ℂ) (i : GridSource) :
    gridLeadingRows m f ε s v i=
      laurentRows (parameter 2 m s) (parameter 3 m s) (parameter 11 m s)
        (phase m ε) (badParameter f 2) (badParameter f 3) (badParameter f 11) v i := by
  cases i with
  | word i =>
    have hu : -badParameter f 3=1 ∨ -badParameter f 3= -1 := by
      simpa only [root_three] using root_unit hf.toEulerData 3
    simp only [gridLeadingRows,gridGroupLeading,laurentRows,matrixScalar_leading,phase]
    rw [character_parities _ _ (grid_physical_sign m hε) hu]
  | taylor i =>
    simp only [gridLeadingRows,gridRamanujanLeading,laurentRows,taylorScalar_leading,grid_ramanujan_root]
  | entire i => rfl
  | infinity i => rfl
  | hecke i =>
    simp only [gridLeadingRows,laurentRows,laurentHecke,gridHeckeLeading,
      primeParameter_actual,primeEigenvalue_actual]

#print axioms leadingRows_laurent
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
