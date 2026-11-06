module

public import SmallLevelTwentyOneGridMatrixV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Matrix SmallLevelTaylor SmallLevelAdditive

def assemble (R : Fin 4 → ℂ) (T : Fin 28 → ℂ) (H : Fin 10 → ℂ) : Fin 42 → ℂ :=
  ![R 0,T 0,T 1,T 2,T 3,T 4,T 5,T 6,T 7,T 8,T 9,T 10,T 11,
    R 1,T 12,T 13,T 14,T 15,R 2,T 16,T 17,T 18,T 19,T 20,T 21,
    R 3,T 22,T 23,T 24,T 25,T 26,T 27,H 0,H 1,H 2,H 3,H 4,H 5,H 6,H 7,H 8,H 9]

def shiftRows (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (w : Fin 42 → ℂ) : Fin 42 → ℂ :=
  assemble 0 (fun i => rowCoefficient (2*m) f ε i (n+1) s*sampleSum (rowQ i) (rowPartner i) w) 0

def shiftLinear (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : (Fin 42 → ℂ) →ₗ[ℂ] (Fin 42 → ℂ) where
  toFun := shiftRows m f ε n s
  map_add' := by
    intro w z
    funext i
    fin_cases i <;> simp [shiftRows,assemble,sampleSum_add,Pi.add_apply,mul_add]
  map_smul' := by
    intro c w
    funext i
    fin_cases i <;> simp [shiftRows,assemble,sampleSum_smul,Pi.smul_apply,smul_eq_mul] <;> ring

def shiftMatrix (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin 42) (Fin 42) ℂ :=
  (shiftLinear m f ε n s).toMatrix'

theorem shiftMatrix_mulVec (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (w : Fin 42 → ℂ) :
    shiftMatrix m f ε n s *ᵥ w=shiftRows m f ε n s w := LinearMap.toMatrix'_mulVec _ _

theorem shiftMatrix_apply (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (i j : Fin 42) :
    shiftMatrix m f ε n s i j=shiftRows m f ε n s (Pi.single j 1) i := LinearMap.toMatrix'_apply _ _ _

def errorVector (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (M : ℕ) (s : ℂ) : Fin 42 → ℂ :=
  assemble (fun i => ramanujanEntire 21 (2*m) f (entireSpecs i) s)
    (fun i => rowError (2*m) f ε i M s) 0

theorem gridVector_index (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (t : ℤ) :
    gridVector k f s (gridIndex t)=grid k f 42 t s := by
  unfold gridVector
  have he : ((gridIndex t).val:ℤ)=t%42 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  rw [he]
  simpa only [Nat.cast_ofNat] using grid_mod k f (by decide : 0<42) t s

theorem leadingMatrix_analytic (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (x : ℂ) (i j : Fin 42) :
    AnalyticAt ℂ (fun s => leadingMatrix m f ε s i j) x := by
  have hT (a : Fin 28) := rowCoefficient_analytic (2*m) f ε a 0 x
  have hX := hecke_parameter_analytic (by decide : 0<2) m x
  simp only [leadingMatrix_apply]
  fin_cases i <;> dsimp [leadingRows,taylorLeading,heckeLeading] <;> fun_prop

theorem shiftMatrix_analytic (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (x : ℂ) (i j : Fin 42) :
    AnalyticAt ℂ (fun s => shiftMatrix m f ε n s i j) x := by
  have hT (a : Fin 28) := rowCoefficient_analytic (2*m) f ε a (n+1) x
  simp only [shiftMatrix_apply]
  fin_cases i <;> dsimp [shiftRows,assemble] <;> fun_prop

#print axioms leadingMatrix_analytic
#print axioms shiftMatrix_analytic
end SmallLevelTwentyOne
