module
public import SmallLevelTwentySixGridAssemblyV1
public import SmallLevelTwentySixGridRatesV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex SmallLevelPrimeRates SmallLevelFourPrimeRates FinitenessNormalizedTwistProduct

/-- Four physical prime parameters; the last branch is used only at p=5. -/
def primeParameter (p : ℕ) (X Y Z W : ℂ) : ℂ :=
  if p=2 then X else if p=3 then Y else if p=13 then Z else W

def primeEigenvalue (p : ℕ) (σ₂ σ₁₃ a b : ℂ) : ℂ :=
  if p=2 then σ₂ else if p=3 then a else if p=13 then σ₁₃ else b

def laurentHecke (X Y Z W σ₂ σ₁₃ a b : ℂ) (v : Fin 780→ℂ) (i : Fin 51) : ℂ :=
  (∑ j∈Finset.range (gridHeckeP i),v (gridIndex (gridHeckeT i+(j:ℤ)*(780/gridHeckeP i:ℕ))))-
    primeEigenvalue (gridHeckeP i) σ₂ σ₁₃ a b*(primeParameter (gridHeckeP i) X Y Z W)⁻¹*
      v (gridIndex ((gridHeckeP i:ℤ)*gridHeckeT i))+
    (if gridHeckeP i∣26 then 0 else ((primeParameter (gridHeckeP i) X Y Z W)⁻¹)^2*
      v (gridIndex ((gridHeckeP i:ℤ)^2*gridHeckeT i)))

def laurentRows (X Y Z W η σ₂ σ₁₃ a b : ℂ) (v : Fin 780→ℂ) : GridSource→ℂ
  | .word i => v (gridGroupIndex i)-gridWordSign (-σ₂) η (sourceWord (gridGroupSource i))*
      monomial (groupPowers i) X Y Z W*v (gridGroupTarget i)
  | .taylor i => gridSample (gridTaylorQ i) (gridTaylorT i) v-
      ((if 2∣gridTaylorQ i then -σ₂ else 1)*(if 13∣gridTaylorQ i then -σ₁₃ else 1))*η*
        monomial (taylorPowers i) X Y Z W*gridSample (gridTaylorQ i) (gridTaylorPartner i) v
  | .entire i => gridSample (gridEntireQ i) 0 v
  | .hecke i => laurentHecke X Y Z W σ₂ σ₁₃ a b v i
  | .infinity i => v (gridInfinityIndex i)

theorem primeParameter_actual (m : ℕ) (s : ℂ) (i : Fin 51) :
    primeParameter (gridHeckeP i) (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s)=parameter (gridHeckeP i) m s := by
  fin_cases i <;> rfl

theorem primeEigenvalue_actual (f : ℕ→ℂ) (i : Fin 51) :
    primeEigenvalue (gridHeckeP i) (badParameter f 2) (badParameter f 13)
      (badParameter f 3) (badParameter f 5)=(Real.sqrt (gridHeckeP i):ℂ)*f (gridHeckeP i) := by
  fin_cases i <;> rfl

/-- The formal Laurent source system is exactly the original leading system
on the physical exponential curve, for arbitrary original coefficients. -/
theorem leadingRows_laurent (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 780→ℂ) (i : GridSource) :
    gridLeadingRows m f ε s v i=
      laurentRows (parameter 2 m s) (parameter 3 m s) (parameter 13 m s) (parameter 5 m s)
        (phase m ε) (badParameter f 2) (badParameter f 13) (badParameter f 3) (badParameter f 5) v i := by
  cases i with
  | word i =>
    simp only [gridLeadingRows,gridGroupLeading,laurentRows,matrixScalar_leading,phase]
  | taylor i =>
    simp only [gridLeadingRows,gridRamanujanLeading,laurentRows,taylorScalar_leading,grid_ramanujan_root]
  | entire i => rfl
  | infinity i => rfl
  | hecke i =>
    simp only [gridLeadingRows,laurentRows,laurentHecke,gridHeckeLeading,
      primeParameter_actual,primeEigenvalue_actual]

#print axioms leadingRows_laurent
end SmallLevelTwentySixGrid
