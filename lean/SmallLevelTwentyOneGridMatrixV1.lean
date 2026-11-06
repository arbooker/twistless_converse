module

public import SmallLevelTwentyOneAuxiliaryRowsV1
public import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Matrix SmallLevelTaylor SmallLevelAdditive FinitenessRamanujanSum

def gridIndex (t : ℤ) : Fin 42 :=
  ⟨(t%42).toNat,by have h := Int.emod_lt_of_pos t (by decide : (0:ℤ)<42); omega⟩

def sampleSum (q : ℕ) (t : ℤ) (w : Fin 42 → ℂ) : ℂ :=
  ∑ j∈residues q, w (gridIndex (t+(j:ℤ)*(42/q:ℕ)))

def gridVector (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : Fin 42 → ℂ :=
  fun j => grid k f 42 (j:ℕ) s

theorem sampleSum_grid (k : ℕ) (f : ℕ → ℂ) (q : ℕ) (t : ℤ) (s : ℂ) :
    sampleSum q t (gridVector k f s)=gridSum k f 42 q t s := by
  unfold sampleSum gridSum gridVector
  apply Finset.sum_congr rfl
  intro j _
  have he : ((gridIndex (t+(j:ℤ)*(42/q:ℕ)):Fin 42).val:ℤ)=
      (t+(j:ℤ)*(42/q:ℕ))%42 := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  rw [he]
  simpa only [Nat.cast_ofNat] using grid_mod k f (by decide : 0<42) (t+(j:ℤ)*(42/q:ℕ)) s

theorem sampleSum_add (q : ℕ) (t : ℤ) (w z : Fin 42 → ℂ) :
    sampleSum q t (w+z)=sampleSum q t w+sampleSum q t z := by
  simp [sampleSum,Finset.sum_add_distrib]

theorem sampleSum_smul (q : ℕ) (t : ℤ) (c : ℂ) (w : Fin 42 → ℂ) :
    sampleSum q t (c • w)=c*sampleSum q t w := by
  simp [sampleSum,Finset.mul_sum]

def taylorLeading (k : ℕ) (f : ℕ → ℂ) (ε : ℂ) (s : ℂ) (w : Fin 42 → ℂ) (i : Fin 28) : ℂ :=
  sampleSum (rowQ i) (rowT i) w-rowCoefficient k f ε i 0 s*sampleSum (rowQ i) (rowPartner i) w

def heckeLeading (m : ℕ) (f : ℕ → ℂ) (s : ℂ) (w : Fin 42 → ℂ) (i : Fin 10) : ℂ :=
  w (gridIndex (heckeSpecs i))+w (gridIndex (heckeSpecs i+21))-
    ((Real.sqrt 2:ℂ)*f 2)*(2:ℂ)^((m:ℂ)-s)*w (gridIndex (2*heckeSpecs i))+
    ((2:ℂ)^((m:ℂ)-s))^2*w (gridIndex (4*heckeSpecs i))

/-- Exact interleaving of the four Ramanujan, twenty-eight Taylor and ten
Hecke rows in the written determinant certificate. -/
def leadingRows (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (w : Fin 42 → ℂ) : Fin 42 → ℂ :=
  let T := taylorLeading (2*m) f ε s w
  let H := heckeLeading m f s w
  ![sampleSum 1 0 w,T 0,T 1,T 2,T 3,T 4,T 5,T 6,T 7,T 8,T 9,T 10,T 11,
    sampleSum 2 0 w,T 12,T 13,T 14,T 15,sampleSum 3 0 w,T 16,T 17,T 18,T 19,T 20,T 21,
    sampleSum 6 0 w,T 22,T 23,T 24,T 25,T 26,T 27,
    H 0,H 1,H 2,H 3,H 4,H 5,H 6,H 7,H 8,H 9]

def leadingLinear (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : (Fin 42 → ℂ) →ₗ[ℂ] (Fin 42 → ℂ) where
  toFun := leadingRows m f ε s
  map_add' := by
    intro w z
    funext i
    fin_cases i <;> simp [leadingRows,taylorLeading,heckeLeading,sampleSum_add,Pi.add_apply] <;> ring
  map_smul' := by
    intro c w
    funext i
    fin_cases i <;> simp [leadingRows,taylorLeading,heckeLeading,sampleSum_smul,Pi.smul_apply,smul_eq_mul] <;> ring

def leadingMatrix (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : Matrix (Fin 42) (Fin 42) ℂ :=
  (leadingLinear m f ε s).toMatrix'

theorem leadingMatrix_mulVec (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (w : Fin 42 → ℂ) :
    leadingMatrix m f ε s *ᵥ w=leadingRows m f ε s w := LinearMap.toMatrix'_mulVec _ _

theorem leadingMatrix_apply (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (i j : Fin 42) :
    leadingMatrix m f ε s i j=leadingRows m f ε s (Pi.single j 1) i := LinearMap.toMatrix'_apply _ _ _

#print axioms sampleSum_grid
#print axioms leadingMatrix_mulVec
end SmallLevelTwentyOne
