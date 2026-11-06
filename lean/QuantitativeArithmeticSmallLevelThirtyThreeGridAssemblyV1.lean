module
public import QuantitativeArithmeticSmallLevelThirtyThreeGridMatrixSystemV1
public import QuantitativeArithmeticSmallLevelThirtyThreeGridEntireRowsV1
public import QuantitativeArithmeticSmallLevelThirtyThreeHeckeSystemV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Set SmallLevelAdditive SmallLevelTaylor FinitenessRamanujanSum SmallLevelPrimeRates

inductive GridSource where
  | word : Fin 588→GridSource
  | taylor : Fin 72→GridSource
  | entire : Fin 8→GridSource
  | hecke : Fin 61→GridSource
  | infinity : Fin 46→GridSource
  deriving DecidableEq, Fintype

def gridIndex (t : ℤ) : Fin 66 :=
  ⟨(t%66).toNat,by have h:=Int.emod_lt_of_pos t (by decide : (0:ℤ)<66); omega⟩

def gridSample (q : ℕ) (t : ℤ) (w : Fin 66→ℂ) : ℂ :=
  ∑ j∈residues q,w (gridIndex (t+(j:ℤ)*(66/q:ℕ)))

def gridVector (k : ℕ) (f : ℕ→ℂ) (s : ℂ) : Fin 66→ℂ :=
  fun j => grid k f 66 (j:ℕ) s

theorem gridVector_index (k : ℕ) (f : ℕ→ℂ) (s : ℂ) (t : ℤ) :
    gridVector k f s (gridIndex t)=grid k f 66 t s := by
  unfold gridVector
  have he : ((gridIndex t).val:ℤ)=t%66:=Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  rw [he]
  simpa only [Nat.cast_ofNat] using grid_mod k f (by decide : 0<66) t s

theorem gridSample_grid (k : ℕ) (f : ℕ→ℂ) (q : ℕ) (t : ℤ) (s : ℂ) :
    gridSample q t (gridVector k f s)=gridSum k f 66 q t s := by
  unfold gridSample gridSum
  simp_rw [gridVector_index]

theorem gridSample_add (q : ℕ) (t : ℤ) (w v : Fin 66→ℂ) :
    gridSample q t (w+v)=gridSample q t w+gridSample q t v := by
  simp [gridSample,Finset.sum_add_distrib]

theorem gridSample_smul (q : ℕ) (t : ℤ) (c : ℂ) (w : Fin 66→ℂ) :
    gridSample q t (c • w)=c*gridSample q t w := by
  simp [gridSample,Finset.mul_sum]


def gridGroupLeading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 66→ℂ) (i : Fin 588) : ℂ :=
  v (groupIndex i)-gridMatrixScalar m f (ε*I^(2*m)) i 0 s*v (gridIndex (groupTarget i))

def gridRamanujanLeading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 66→ℂ) (i : Fin 72) : ℂ :=
  gridSample (gridTaylorQ i) (gridTaylorT i) v-
    gridTaylorCoefficient m f ε i 0 s*gridSample (gridTaylorQ i) (gridTaylorPartner i) v

def gridHeckeLeading (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 66→ℂ) (i : Fin 61) : ℂ :=
  (∑ j∈Finset.range (gridHeckeP i),v (gridIndex (gridHeckeT i+(j:ℤ)*(66/gridHeckeP i:ℕ))))-
    ((Real.sqrt (gridHeckeP i):ℂ)*f (gridHeckeP i))*(parameter (gridHeckeP i) m s)⁻¹*
      v (gridIndex ((gridHeckeP i:ℤ)*gridHeckeT i))+
    (if gridHeckeP i∣33 then 0 else ((parameter (gridHeckeP i) m s)⁻¹)^2*
      v (gridIndex ((gridHeckeP i:ℤ)^2*gridHeckeT i)))

def gridLeadingRows (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 66→ℂ) : GridSource→ℂ
  | .word i => gridGroupLeading m f ε s v i
  | .taylor i => gridRamanujanLeading m f ε s v i
  | .entire i => gridSample (gridEntireQ i) 0 v
  | .hecke i => gridHeckeLeading m f s v i
  | .infinity i => v (gridInfinityIndex i)

def gridShiftRows (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (v : Fin 66→ℂ) : GridSource→ℂ
  | .word i => gridMatrixScalar m f (ε*I^(2*m)) i (n+1) s*v (gridIndex (groupTarget i))
  | .taylor i => gridTaylorCoefficient m f ε i (n+1) s*gridSample (gridTaylorQ i) (gridTaylorPartner i) v
  | .entire _ => 0
  | .hecke _ => 0
  | .infinity _ => 0

theorem gridHeckeLeading_grid (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (i : Fin 61) :
    gridHeckeLeading m f s (gridVector (2*m) f s) i=gridHeckeRow m f i s := by
  simp only [gridHeckeLeading,gridHeckeRow,gridVector_index]

#print axioms gridVector_index
#print axioms gridSample_grid
#print axioms gridHeckeLeading_grid
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
