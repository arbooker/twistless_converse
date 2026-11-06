module

public import SmallLevelThirtyFourGridTheoryV4
public import SmallLevelThirtyFourUnitMMPRowsV1

/-! Consolidated chapter: SmallLevelThirtyFourGridMMP. Original declarations and local scopes are retained. -/

/-! ## SmallLevelThirtyFourGridMMPEntireBindingBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourGridMMP
open SmallLevelThirtyFourGrid
open Complex SmallLevelPrimeRates SmallLevelFourPrimeRates SmallLevelThirtyFourUnitMMP

theorem entire_binding_0 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 189 =
      gridLeadingRows m f ε s v (.entire 0) := by
  norm_num [sourceRows,sourceRowsPart11,gridLeadingRows,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridEntireQ,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms entire_binding_0

theorem entire_binding_1 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 202 =
      gridLeadingRows m f ε s v (.entire 1) := by
  norm_num [sourceRows,sourceRowsPart12,gridLeadingRows,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridEntireQ,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms entire_binding_1

theorem entire_binding_2 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 211 =
      gridLeadingRows m f ε s v (.entire 2) := by
  norm_num [sourceRows,sourceRowsPart13,gridLeadingRows,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridEntireQ,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms entire_binding_2

theorem entire_binding_3 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 217 =
      gridLeadingRows m f ε s v (.entire 3) := by
  norm_num [sourceRows,sourceRowsPart13,gridLeadingRows,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridEntireQ,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms entire_binding_3

theorem entire_binding_4 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 218 =
      gridLeadingRows m f ε s v (.entire 4) := by
  norm_num [sourceRows,sourceRowsPart13,gridLeadingRows,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridEntireQ,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms entire_binding_4

theorem entire_binding_5 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 238 =
      gridLeadingRows m f ε s v (.entire 5) := by
  norm_num [sourceRows,sourceRowsPart14,gridLeadingRows,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridEntireQ,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms entire_binding_5

theorem entire_binding_6 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 247 =
      gridLeadingRows m f ε s v (.entire 6) := by
  norm_num [sourceRows,sourceRowsPart15,gridLeadingRows,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridEntireQ,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms entire_binding_6

theorem entire_binding_7 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 250 =
      gridLeadingRows m f ε s v (.entire 7) := by
  norm_num [sourceRows,sourceRowsPart15,gridLeadingRows,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridEntireQ,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms entire_binding_7

theorem entire_binding_8 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 255 =
      gridLeadingRows m f ε s v (.entire 8) := by
  norm_num [sourceRows,sourceRowsPart15,gridLeadingRows,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridEntireQ,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms entire_binding_8

theorem entire_binding_9 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 256 =
      gridLeadingRows m f ε s v (.entire 9) := by
  norm_num [sourceRows,sourceRowsPart16,gridLeadingRows,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridEntireQ,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms entire_binding_9

end SmallLevelThirtyFourGridMMP
end
end

/-! ## SmallLevelThirtyFourGridMMPHeckeBindingBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourGridMMP
open SmallLevelThirtyFourGrid
open Complex SmallLevelPrimeRates SmallLevelThirtyFourUnitMMP

theorem hecke_binding_0 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 259 =
      gridHeckeLeading m f s v 0 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 0=2 from rfl,
    show gridHeckeT 0=(2:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart16,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring

#print axioms hecke_binding_0

theorem hecke_binding_1 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 260 =
      gridHeckeLeading m f s v 1 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 1=2 from rfl,
    show gridHeckeT 1=(4:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart16,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring

#print axioms hecke_binding_1

theorem hecke_binding_2 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 261 =
      gridHeckeLeading m f s v 2 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 2=2 from rfl,
    show gridHeckeT 2=(7:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart16,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring

#print axioms hecke_binding_2

theorem hecke_binding_3 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 262 =
      gridHeckeLeading m f s v 3 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 3=2 from rfl,
    show gridHeckeT 3=(8:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart16,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring

#print axioms hecke_binding_3

theorem hecke_binding_4 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 263 =
      gridHeckeLeading m f s v 4 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 4=2 from rfl,
    show gridHeckeT 4=(9:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart16,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring

#print axioms hecke_binding_4

theorem hecke_binding_5 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 264 =
      gridHeckeLeading m f s v 5 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 5=2 from rfl,
    show gridHeckeT 5=(11:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart16,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring

#print axioms hecke_binding_5

theorem hecke_binding_6 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 265 =
      gridHeckeLeading m f s v 6 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 6=2 from rfl,
    show gridHeckeT 6=(12:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart16,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring

#print axioms hecke_binding_6

theorem hecke_binding_7 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 266 =
      gridHeckeLeading m f s v 7 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 7=2 from rfl,
    show gridHeckeT 7=(13:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart16,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring

#print axioms hecke_binding_7

theorem hecke_binding_8 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 267 =
      gridHeckeLeading m f s v 8 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 8=2 from rfl,
    show gridHeckeT 8=(14:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart16,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_8

theorem hecke_binding_9 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 268 =
      gridHeckeLeading m f s v 9 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 9=2 from rfl,
    show gridHeckeT 9=(18:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart16,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_9

theorem hecke_binding_10 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 269 =
      gridHeckeLeading m f s v 10 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 10=2 from rfl,
    show gridHeckeT 10=(21:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart16,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_10

theorem hecke_binding_11 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 270 =
      gridHeckeLeading m f s v 11 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 11=2 from rfl,
    show gridHeckeT 11=(22:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart16,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_11

theorem hecke_binding_12 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 271 =
      gridHeckeLeading m f s v 12 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 12=2 from rfl,
    show gridHeckeT 12=(24:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart16,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_12

theorem hecke_binding_13 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 272 =
      gridHeckeLeading m f s v 13 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 13=2 from rfl,
    show gridHeckeT 13=(25:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_13

theorem hecke_binding_14 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 273 =
      gridHeckeLeading m f s v 14 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 14=2 from rfl,
    show gridHeckeT 14=(27:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_14

theorem hecke_binding_15 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 274 =
      gridHeckeLeading m f s v 15 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 15=2 from rfl,
    show gridHeckeT 15=(31:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_15

theorem hecke_binding_16 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 275 =
      gridHeckeLeading m f s v 16 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 16=2 from rfl,
    show gridHeckeT 16=(33:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_16

theorem hecke_binding_17 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 276 =
      gridHeckeLeading m f s v 17 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 17=2 from rfl,
    show gridHeckeT 17=(34:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_17

theorem hecke_binding_18 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 277 =
      gridHeckeLeading m f s v 18 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 18=2 from rfl,
    show gridHeckeT 18=(35:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_18

theorem hecke_binding_19 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 278 =
      gridHeckeLeading m f s v 19 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 19=2 from rfl,
    show gridHeckeT 19=(36:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_19

theorem hecke_binding_20 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 279 =
      gridHeckeLeading m f s v 20 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 20=2 from rfl,
    show gridHeckeT 20=(37:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_20

theorem hecke_binding_21 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 280 =
      gridHeckeLeading m f s v 21 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 21=2 from rfl,
    show gridHeckeT 21=(39:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_21

theorem hecke_binding_22 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 281 =
      gridHeckeLeading m f s v 22 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 22=2 from rfl,
    show gridHeckeT 22=(40:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_22

theorem hecke_binding_23 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 282 =
      gridHeckeLeading m f s v 23 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 23=2 from rfl,
    show gridHeckeT 23=(41:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_23

theorem hecke_binding_24 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 283 =
      gridHeckeLeading m f s v 24 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 24=2 from rfl,
    show gridHeckeT 24=(42:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_24

theorem hecke_binding_25 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 284 =
      gridHeckeLeading m f s v 25 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 25=2 from rfl,
    show gridHeckeT 25=(43:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_25

theorem hecke_binding_26 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 285 =
      gridHeckeLeading m f s v 26 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 26=2 from rfl,
    show gridHeckeT 26=(44:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_26

theorem hecke_binding_27 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 286 =
      gridHeckeLeading m f s v 27 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 27=2 from rfl,
    show gridHeckeT 27=(45:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_27

theorem hecke_binding_28 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 287 =
      gridHeckeLeading m f s v 28 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 28=2 from rfl,
    show gridHeckeT 28=(48:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart17,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_28

theorem hecke_binding_29 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 288 =
      gridHeckeLeading m f s v 29 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 29=2 from rfl,
    show gridHeckeT 29=(50:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_29

theorem hecke_binding_30 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 289 =
      gridHeckeLeading m f s v 30 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 30=2 from rfl,
    show gridHeckeT 30=(51:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_30

theorem hecke_binding_31 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 290 =
      gridHeckeLeading m f s v 31 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 31=2 from rfl,
    show gridHeckeT 31=(54:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_31

theorem hecke_binding_32 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 291 =
      gridHeckeLeading m f s v 32 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 32=2 from rfl,
    show gridHeckeT 32=(55:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_32

theorem hecke_binding_33 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 292 =
      gridHeckeLeading m f s v 33 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 33=2 from rfl,
    show gridHeckeT 33=(57:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_33

theorem hecke_binding_34 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 293 =
      gridHeckeLeading m f s v 34 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 34=2 from rfl,
    show gridHeckeT 34=(60:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_34

theorem hecke_binding_35 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 294 =
      gridHeckeLeading m f s v 35 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 35=2 from rfl,
    show gridHeckeT 35=(63:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_35

theorem hecke_binding_36 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 295 =
      gridHeckeLeading m f s v 36 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 36=2 from rfl,
    show gridHeckeT 36=(65:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_36

theorem hecke_binding_37 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 296 =
      gridHeckeLeading m f s v 37 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 37=2 from rfl,
    show gridHeckeT 37=(66:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_37

theorem hecke_binding_38 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 297 =
      gridHeckeLeading m f s v 38 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 38=2 from rfl,
    show gridHeckeT 38=(69:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_38

theorem hecke_binding_39 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 298 =
      gridHeckeLeading m f s v 39 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 39=2 from rfl,
    show gridHeckeT 39=(70:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_39

theorem hecke_binding_40 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 299 =
      gridHeckeLeading m f s v 40 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 40=2 from rfl,
    show gridHeckeT 40=(71:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_40

theorem hecke_binding_41 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 300 =
      gridHeckeLeading m f s v 41 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 41=2 from rfl,
    show gridHeckeT 41=(72:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_41

theorem hecke_binding_42 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 301 =
      gridHeckeLeading m f s v 42 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 42=2 from rfl,
    show gridHeckeT 42=(74:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_42

theorem hecke_binding_43 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 302 =
      gridHeckeLeading m f s v 43 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 43=2 from rfl,
    show gridHeckeT 43=(75:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_43

theorem hecke_binding_44 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 303 =
      gridHeckeLeading m f s v 44 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 44=2 from rfl,
    show gridHeckeT 44=(77:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart18,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_44

theorem hecke_binding_45 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 304 =
      gridHeckeLeading m f s v 45 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 45=2 from rfl,
    show gridHeckeT 45=(78:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_45

theorem hecke_binding_46 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 305 =
      gridHeckeLeading m f s v 46 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 46=2 from rfl,
    show gridHeckeT 46=(79:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_46

theorem hecke_binding_47 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 306 =
      gridHeckeLeading m f s v 47 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 47=2 from rfl,
    show gridHeckeT 47=(80:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_47

theorem hecke_binding_48 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 307 =
      gridHeckeLeading m f s v 48 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 48=2 from rfl,
    show gridHeckeT 48=(81:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_48

theorem hecke_binding_49 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 308 =
      gridHeckeLeading m f s v 49 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 49=2 from rfl,
    show gridHeckeT 49=(82:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_49

theorem hecke_binding_50 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 309 =
      gridHeckeLeading m f s v 50 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 50=2 from rfl,
    show gridHeckeT 50=(83:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_50

theorem hecke_binding_51 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 310 =
      gridHeckeLeading m f s v 51 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 51=2 from rfl,
    show gridHeckeT 51=(84:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_51

theorem hecke_binding_52 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 311 =
      gridHeckeLeading m f s v 52 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 52=2 from rfl,
    show gridHeckeT 52=(85:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_52

theorem hecke_binding_53 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 312 =
      gridHeckeLeading m f s v 53 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 53=2 from rfl,
    show gridHeckeT 53=(86:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_53

theorem hecke_binding_54 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 313 =
      gridHeckeLeading m f s v 54 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 54=2 from rfl,
    show gridHeckeT 54=(87:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_54

theorem hecke_binding_55 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 314 =
      gridHeckeLeading m f s v 55 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 55=2 from rfl,
    show gridHeckeT 55=(88:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_55

theorem hecke_binding_56 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 315 =
      gridHeckeLeading m f s v 56 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 56=2 from rfl,
    show gridHeckeT 56=(89:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_56

theorem hecke_binding_57 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 316 =
      gridHeckeLeading m f s v 57 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 57=2 from rfl,
    show gridHeckeT 57=(90:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_57

theorem hecke_binding_58 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 317 =
      gridHeckeLeading m f s v 58 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 58=2 from rfl,
    show gridHeckeT 58=(91:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_58

theorem hecke_binding_59 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 318 =
      gridHeckeLeading m f s v 59 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 59=2 from rfl,
    show gridHeckeT 59=(92:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_59

theorem hecke_binding_60 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 319 =
      gridHeckeLeading m f s v 60 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 60=2 from rfl,
    show gridHeckeT 60=(93:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart19,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_60

theorem hecke_binding_61 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 320 =
      gridHeckeLeading m f s v 61 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 61=2 from rfl,
    show gridHeckeT 61=(95:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_61

theorem hecke_binding_62 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 321 =
      gridHeckeLeading m f s v 62 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 62=2 from rfl,
    show gridHeckeT 62=(96:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_62

theorem hecke_binding_63 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 322 =
      gridHeckeLeading m f s v 63 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 63=2 from rfl,
    show gridHeckeT 63=(98:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_63

theorem hecke_binding_64 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 323 =
      gridHeckeLeading m f s v 64 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 64=2 from rfl,
    show gridHeckeT 64=(99:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_64

theorem hecke_binding_65 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 324 =
      gridHeckeLeading m f s v 65 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 65=2 from rfl,
    show gridHeckeT 65=(100:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_65

theorem hecke_binding_66 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 325 =
      gridHeckeLeading m f s v 66 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 66=2 from rfl,
    show gridHeckeT 66=(101:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_66

theorem hecke_binding_67 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 326 =
      gridHeckeLeading m f s v 67 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 67=2 from rfl,
    show gridHeckeT 67=(107:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_67

theorem hecke_binding_68 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 327 =
      gridHeckeLeading m f s v 68 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 68=2 from rfl,
    show gridHeckeT 68=(108:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_68

theorem hecke_binding_69 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 328 =
      gridHeckeLeading m f s v 69 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 69=2 from rfl,
    show gridHeckeT 69=(111:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_69

theorem hecke_binding_70 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 329 =
      gridHeckeLeading m f s v 70 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 70=2 from rfl,
    show gridHeckeT 70=(114:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_70

theorem hecke_binding_71 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 330 =
      gridHeckeLeading m f s v 71 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 71=2 from rfl,
    show gridHeckeT 71=(115:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_71

theorem hecke_binding_72 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 331 =
      gridHeckeLeading m f s v 72 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 72=2 from rfl,
    show gridHeckeT 72=(116:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_72

theorem hecke_binding_73 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 332 =
      gridHeckeLeading m f s v 73 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 73=2 from rfl,
    show gridHeckeT 73=(117:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_73

theorem hecke_binding_74 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 333 =
      gridHeckeLeading m f s v 74 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 74=2 from rfl,
    show gridHeckeT 74=(119:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_74

theorem hecke_binding_75 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 334 =
      gridHeckeLeading m f s v 75 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 75=2 from rfl,
    show gridHeckeT 75=(120:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_75

theorem hecke_binding_76 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 335 =
      gridHeckeLeading m f s v 76 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 76=2 from rfl,
    show gridHeckeT 76=(122:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart20,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_76

theorem hecke_binding_77 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 336 =
      gridHeckeLeading m f s v 77 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 77=2 from rfl,
    show gridHeckeT 77=(123:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_77

theorem hecke_binding_78 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 337 =
      gridHeckeLeading m f s v 78 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 78=2 from rfl,
    show gridHeckeT 78=(125:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_78

theorem hecke_binding_79 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 338 =
      gridHeckeLeading m f s v 79 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 79=2 from rfl,
    show gridHeckeT 79=(126:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_79

theorem hecke_binding_80 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 339 =
      gridHeckeLeading m f s v 80 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 80=2 from rfl,
    show gridHeckeT 80=(127:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_80

theorem hecke_binding_81 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 340 =
      gridHeckeLeading m f s v 81 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 81=2 from rfl,
    show gridHeckeT 81=(128:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_81

theorem hecke_binding_82 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 341 =
      gridHeckeLeading m f s v 82 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 82=2 from rfl,
    show gridHeckeT 82=(129:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_82

theorem hecke_binding_83 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 342 =
      gridHeckeLeading m f s v 83 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 83=2 from rfl,
    show gridHeckeT 83=(130:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_83

theorem hecke_binding_84 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 343 =
      gridHeckeLeading m f s v 84 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 84=2 from rfl,
    show gridHeckeT 84=(132:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_84

theorem hecke_binding_85 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 344 =
      gridHeckeLeading m f s v 85 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 85=2 from rfl,
    show gridHeckeT 85=(133:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_85

theorem hecke_binding_86 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 345 =
      gridHeckeLeading m f s v 86 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 86=2 from rfl,
    show gridHeckeT 86=(136:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_86

theorem hecke_binding_87 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 346 =
      gridHeckeLeading m f s v 87 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 87=2 from rfl,
    show gridHeckeT 87=(138:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_87

theorem hecke_binding_88 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 347 =
      gridHeckeLeading m f s v 88 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 88=2 from rfl,
    show gridHeckeT 88=(139:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_88

theorem hecke_binding_89 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 348 =
      gridHeckeLeading m f s v 89 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 89=2 from rfl,
    show gridHeckeT 89=(140:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_89

theorem hecke_binding_90 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 349 =
      gridHeckeLeading m f s v 90 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 90=2 from rfl,
    show gridHeckeT 90=(141:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_90

theorem hecke_binding_91 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 350 =
      gridHeckeLeading m f s v 91 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 91=2 from rfl,
    show gridHeckeT 91=(144:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_91

theorem hecke_binding_92 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 351 =
      gridHeckeLeading m f s v 92 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 92=2 from rfl,
    show gridHeckeT 92=(145:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart21,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_92

theorem hecke_binding_93 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 352 =
      gridHeckeLeading m f s v 93 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 93=2 from rfl,
    show gridHeckeT 93=(147:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_93

theorem hecke_binding_94 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 353 =
      gridHeckeLeading m f s v 94 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 94=2 from rfl,
    show gridHeckeT 94=(148:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_94

theorem hecke_binding_95 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 354 =
      gridHeckeLeading m f s v 95 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 95=2 from rfl,
    show gridHeckeT 95=(150:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_95

theorem hecke_binding_96 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 355 =
      gridHeckeLeading m f s v 96 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 96=2 from rfl,
    show gridHeckeT 96=(154:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_96

theorem hecke_binding_97 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 356 =
      gridHeckeLeading m f s v 97 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 97=2 from rfl,
    show gridHeckeT 97=(155:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_97

theorem hecke_binding_98 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 357 =
      gridHeckeLeading m f s v 98 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 98=2 from rfl,
    show gridHeckeT 98=(156:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_98

theorem hecke_binding_99 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 358 =
      gridHeckeLeading m f s v 99 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 99=2 from rfl,
    show gridHeckeT 99=(157:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_99

theorem hecke_binding_100 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 359 =
      gridHeckeLeading m f s v 100 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 100=2 from rfl,
    show gridHeckeT 100=(159:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_100

theorem hecke_binding_101 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 360 =
      gridHeckeLeading m f s v 101 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 101=2 from rfl,
    show gridHeckeT 101=(160:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_101

theorem hecke_binding_102 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 361 =
      gridHeckeLeading m f s v 102 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 102=2 from rfl,
    show gridHeckeT 102=(162:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_102

theorem hecke_binding_103 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 362 =
      gridHeckeLeading m f s v 103 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 103=2 from rfl,
    show gridHeckeT 103=(163:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_103

theorem hecke_binding_104 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 363 =
      gridHeckeLeading m f s v 104 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 104=2 from rfl,
    show gridHeckeT 104=(164:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_104

theorem hecke_binding_105 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 364 =
      gridHeckeLeading m f s v 105 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 105=2 from rfl,
    show gridHeckeT 105=(166:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_105

theorem hecke_binding_106 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 365 =
      gridHeckeLeading m f s v 106 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 106=2 from rfl,
    show gridHeckeT 106=(167:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_106

theorem hecke_binding_107 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 366 =
      gridHeckeLeading m f s v 107 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 107=2 from rfl,
    show gridHeckeT 107=(168:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_107

theorem hecke_binding_108 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 367 =
      gridHeckeLeading m f s v 108 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 108=2 from rfl,
    show gridHeckeT 108=(169:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart22,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_108

theorem hecke_binding_109 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 368 =
      gridHeckeLeading m f s v 109 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 109=2 from rfl,
    show gridHeckeT 109=(170:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_109

theorem hecke_binding_110 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 369 =
      gridHeckeLeading m f s v 110 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 110=2 from rfl,
    show gridHeckeT 110=(171:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_110

theorem hecke_binding_111 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 370 =
      gridHeckeLeading m f s v 111 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 111=2 from rfl,
    show gridHeckeT 111=(172:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_111

theorem hecke_binding_112 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 371 =
      gridHeckeLeading m f s v 112 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 112=2 from rfl,
    show gridHeckeT 112=(173:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_112

theorem hecke_binding_113 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 372 =
      gridHeckeLeading m f s v 113 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 113=2 from rfl,
    show gridHeckeT 113=(174:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_113

theorem hecke_binding_114 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 373 =
      gridHeckeLeading m f s v 114 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 114=2 from rfl,
    show gridHeckeT 114=(175:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_114

theorem hecke_binding_115 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 374 =
      gridHeckeLeading m f s v 115 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 115=2 from rfl,
    show gridHeckeT 115=(176:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_115

theorem hecke_binding_116 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 375 =
      gridHeckeLeading m f s v 116 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 116=2 from rfl,
    show gridHeckeT 116=(177:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_116

theorem hecke_binding_117 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 376 =
      gridHeckeLeading m f s v 117 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 117=2 from rfl,
    show gridHeckeT 117=(178:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_117

theorem hecke_binding_118 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 377 =
      gridHeckeLeading m f s v 118 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 118=2 from rfl,
    show gridHeckeT 118=(181:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_118

theorem hecke_binding_119 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 378 =
      gridHeckeLeading m f s v 119 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 119=2 from rfl,
    show gridHeckeT 119=(183:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_119

theorem hecke_binding_120 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 379 =
      gridHeckeLeading m f s v 120 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 120=2 from rfl,
    show gridHeckeT 120=(184:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_120

theorem hecke_binding_121 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 380 =
      gridHeckeLeading m f s v 121 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 121=2 from rfl,
    show gridHeckeT 121=(185:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_121

theorem hecke_binding_122 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 381 =
      gridHeckeLeading m f s v 122 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 122=2 from rfl,
    show gridHeckeT 122=(186:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_122

theorem hecke_binding_123 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 382 =
      gridHeckeLeading m f s v 123 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 123=2 from rfl,
    show gridHeckeT 123=(187:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_123

theorem hecke_binding_124 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 383 =
      gridHeckeLeading m f s v 124 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 124=2 from rfl,
    show gridHeckeT 124=(189:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart23,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_124

theorem hecke_binding_125 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 384 =
      gridHeckeLeading m f s v 125 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 125=2 from rfl,
    show gridHeckeT 125=(190:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_125

theorem hecke_binding_126 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 385 =
      gridHeckeLeading m f s v 126 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 126=2 from rfl,
    show gridHeckeT 126=(192:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_126

theorem hecke_binding_127 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 386 =
      gridHeckeLeading m f s v 127 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 127=2 from rfl,
    show gridHeckeT 127=(198:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_127

theorem hecke_binding_128 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 387 =
      gridHeckeLeading m f s v 128 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 128=2 from rfl,
    show gridHeckeT 128=(200:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_128

theorem hecke_binding_129 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 388 =
      gridHeckeLeading m f s v 129 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 129=2 from rfl,
    show gridHeckeT 129=(201:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_129

theorem hecke_binding_130 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 389 =
      gridHeckeLeading m f s v 130 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 130=2 from rfl,
    show gridHeckeT 130=(205:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_130

theorem hecke_binding_131 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 390 =
      gridHeckeLeading m f s v 131 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 131=2 from rfl,
    show gridHeckeT 131=(207:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_131

theorem hecke_binding_132 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 391 =
      gridHeckeLeading m f s v 132 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 132=2 from rfl,
    show gridHeckeT 132=(210:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_132

theorem hecke_binding_133 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 392 =
      gridHeckeLeading m f s v 133 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 133=2 from rfl,
    show gridHeckeT 133=(211:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_133

theorem hecke_binding_134 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 393 =
      gridHeckeLeading m f s v 134 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 134=2 from rfl,
    show gridHeckeT 134=(212:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_134

theorem hecke_binding_135 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 394 =
      gridHeckeLeading m f s v 135 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 135=2 from rfl,
    show gridHeckeT 135=(213:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_135

theorem hecke_binding_136 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 395 =
      gridHeckeLeading m f s v 136 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 136=2 from rfl,
    show gridHeckeT 136=(214:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_136

theorem hecke_binding_137 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 396 =
      gridHeckeLeading m f s v 137 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 137=2 from rfl,
    show gridHeckeT 137=(216:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_137

theorem hecke_binding_138 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 397 =
      gridHeckeLeading m f s v 138 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 138=2 from rfl,
    show gridHeckeT 138=(218:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_138

theorem hecke_binding_139 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 398 =
      gridHeckeLeading m f s v 139 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 139=2 from rfl,
    show gridHeckeT 139=(219:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_139

theorem hecke_binding_140 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 399 =
      gridHeckeLeading m f s v 140 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 140=2 from rfl,
    show gridHeckeT 140=(220:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart24,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_140

theorem hecke_binding_141 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 400 =
      gridHeckeLeading m f s v 141 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 141=2 from rfl,
    show gridHeckeT 141=(221:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_141

theorem hecke_binding_142 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 401 =
      gridHeckeLeading m f s v 142 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 142=2 from rfl,
    show gridHeckeT 142=(222:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_142

theorem hecke_binding_143 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 402 =
      gridHeckeLeading m f s v 143 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 143=2 from rfl,
    show gridHeckeT 143=(224:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_143

theorem hecke_binding_144 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 403 =
      gridHeckeLeading m f s v 144 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 144=2 from rfl,
    show gridHeckeT 144=(228:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_144

theorem hecke_binding_145 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 404 =
      gridHeckeLeading m f s v 145 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 145=2 from rfl,
    show gridHeckeT 145=(233:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_145

theorem hecke_binding_146 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 405 =
      gridHeckeLeading m f s v 146 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 146=2 from rfl,
    show gridHeckeT 146=(234:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_146

theorem hecke_binding_147 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 406 =
      gridHeckeLeading m f s v 147 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 147=2 from rfl,
    show gridHeckeT 147=(235:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_147

theorem hecke_binding_148 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 407 =
      gridHeckeLeading m f s v 148 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 148=2 from rfl,
    show gridHeckeT 148=(241:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_148

theorem hecke_binding_149 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 408 =
      gridHeckeLeading m f s v 149 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 149=2 from rfl,
    show gridHeckeT 149=(242:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_149

theorem hecke_binding_150 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 409 =
      gridHeckeLeading m f s v 150 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 150=2 from rfl,
    show gridHeckeT 150=(244:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_150

theorem hecke_binding_151 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 410 =
      gridHeckeLeading m f s v 151 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 151=2 from rfl,
    show gridHeckeT 151=(246:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_151

theorem hecke_binding_152 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 411 =
      gridHeckeLeading m f s v 152 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 152=2 from rfl,
    show gridHeckeT 152=(248:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_152

theorem hecke_binding_153 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 412 =
      gridHeckeLeading m f s v 153 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 153=2 from rfl,
    show gridHeckeT 153=(251:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_153

theorem hecke_binding_154 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 413 =
      gridHeckeLeading m f s v 154 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 154=2 from rfl,
    show gridHeckeT 154=(253:ℤ) from rfl]
  rw [h2]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 2 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_154

theorem hecke_binding_155 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 414 =
      gridHeckeLeading m f s v 155 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 155=3 from rfl,
    show gridHeckeT 155=(3:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_155

theorem hecke_binding_156 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 415 =
      gridHeckeLeading m f s v 156 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 156=3 from rfl,
    show gridHeckeT 156=(6:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart25,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_156

theorem hecke_binding_157 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 416 =
      gridHeckeLeading m f s v 157 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 157=3 from rfl,
    show gridHeckeT 157=(7:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_157

theorem hecke_binding_158 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 417 =
      gridHeckeLeading m f s v 158 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 158=3 from rfl,
    show gridHeckeT 158=(8:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_158

theorem hecke_binding_159 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 418 =
      gridHeckeLeading m f s v 159 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 159=3 from rfl,
    show gridHeckeT 159=(11:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_159

theorem hecke_binding_160 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 419 =
      gridHeckeLeading m f s v 160 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 160=3 from rfl,
    show gridHeckeT 160=(12:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_160

theorem hecke_binding_161 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 420 =
      gridHeckeLeading m f s v 161 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 161=3 from rfl,
    show gridHeckeT 161=(13:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_161

theorem hecke_binding_162 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 421 =
      gridHeckeLeading m f s v 162 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 162=3 from rfl,
    show gridHeckeT 162=(14:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_162

theorem hecke_binding_163 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 422 =
      gridHeckeLeading m f s v 163 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 163=3 from rfl,
    show gridHeckeT 163=(15:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_163

theorem hecke_binding_164 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 423 =
      gridHeckeLeading m f s v 164 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 164=3 from rfl,
    show gridHeckeT 164=(16:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_164

theorem hecke_binding_165 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 424 =
      gridHeckeLeading m f s v 165 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 165=3 from rfl,
    show gridHeckeT 165=(17:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_165

theorem hecke_binding_166 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 425 =
      gridHeckeLeading m f s v 166 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 166=3 from rfl,
    show gridHeckeT 166=(19:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_166

theorem hecke_binding_167 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 426 =
      gridHeckeLeading m f s v 167 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 167=3 from rfl,
    show gridHeckeT 167=(22:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_167

theorem hecke_binding_168 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 427 =
      gridHeckeLeading m f s v 168 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 168=3 from rfl,
    show gridHeckeT 168=(26:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_168

theorem hecke_binding_169 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 428 =
      gridHeckeLeading m f s v 169 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 169=3 from rfl,
    show gridHeckeT 169=(28:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_169

theorem hecke_binding_170 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 429 =
      gridHeckeLeading m f s v 170 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 170=3 from rfl,
    show gridHeckeT 170=(29:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_170

theorem hecke_binding_171 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 430 =
      gridHeckeLeading m f s v 171 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 171=3 from rfl,
    show gridHeckeT 171=(30:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_171

theorem hecke_binding_172 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 431 =
      gridHeckeLeading m f s v 172 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 172=3 from rfl,
    show gridHeckeT 172=(31:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart26,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_172

theorem hecke_binding_173 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 432 =
      gridHeckeLeading m f s v 173 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 173=3 from rfl,
    show gridHeckeT 173=(32:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_173

theorem hecke_binding_174 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 433 =
      gridHeckeLeading m f s v 174 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 174=3 from rfl,
    show gridHeckeT 174=(34:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_174

theorem hecke_binding_175 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 434 =
      gridHeckeLeading m f s v 175 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 175=3 from rfl,
    show gridHeckeT 175=(35:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_175

theorem hecke_binding_176 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 435 =
      gridHeckeLeading m f s v 176 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 176=3 from rfl,
    show gridHeckeT 176=(37:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_176

theorem hecke_binding_177 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 436 =
      gridHeckeLeading m f s v 177 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 177=3 from rfl,
    show gridHeckeT 177=(40:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_177

theorem hecke_binding_178 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 437 =
      gridHeckeLeading m f s v 178 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 178=3 from rfl,
    show gridHeckeT 178=(41:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_178

theorem hecke_binding_179 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 438 =
      gridHeckeLeading m f s v 179 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 179=3 from rfl,
    show gridHeckeT 179=(42:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_179

theorem hecke_binding_180 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 439 =
      gridHeckeLeading m f s v 180 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 180=3 from rfl,
    show gridHeckeT 180=(43:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_180

theorem hecke_binding_181 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 440 =
      gridHeckeLeading m f s v 181 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 181=3 from rfl,
    show gridHeckeT 181=(44:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_181

theorem hecke_binding_182 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 441 =
      gridHeckeLeading m f s v 182 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 182=3 from rfl,
    show gridHeckeT 182=(45:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_182

theorem hecke_binding_183 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 442 =
      gridHeckeLeading m f s v 183 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 183=3 from rfl,
    show gridHeckeT 183=(48:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_183

theorem hecke_binding_184 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 443 =
      gridHeckeLeading m f s v 184 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 184=3 from rfl,
    show gridHeckeT 184=(51:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_184

theorem hecke_binding_185 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 444 =
      gridHeckeLeading m f s v 185 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 185=3 from rfl,
    show gridHeckeT 185=(54:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_185

theorem hecke_binding_186 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 445 =
      gridHeckeLeading m f s v 186 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 186=3 from rfl,
    show gridHeckeT 186=(62:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_186

theorem hecke_binding_187 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 446 =
      gridHeckeLeading m f s v 187 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 187=3 from rfl,
    show gridHeckeT 187=(63:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_187

theorem hecke_binding_188 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 447 =
      gridHeckeLeading m f s v 188 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 188=3 from rfl,
    show gridHeckeT 188=(65:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart27,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_188

theorem hecke_binding_189 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 448 =
      gridHeckeLeading m f s v 189 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 189=3 from rfl,
    show gridHeckeT 189=(69:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_189

theorem hecke_binding_190 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 449 =
      gridHeckeLeading m f s v 190 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 190=3 from rfl,
    show gridHeckeT 190=(70:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_190

theorem hecke_binding_191 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 450 =
      gridHeckeLeading m f s v 191 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 191=3 from rfl,
    show gridHeckeT 191=(71:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_191

theorem hecke_binding_192 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 451 =
      gridHeckeLeading m f s v 192 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 192=3 from rfl,
    show gridHeckeT 192=(72:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_192

theorem hecke_binding_193 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 452 =
      gridHeckeLeading m f s v 193 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 193=3 from rfl,
    show gridHeckeT 193=(74:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_193

theorem hecke_binding_194 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 453 =
      gridHeckeLeading m f s v 194 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 194=3 from rfl,
    show gridHeckeT 194=(75:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_194

theorem hecke_binding_195 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 454 =
      gridHeckeLeading m f s v 195 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 195=3 from rfl,
    show gridHeckeT 195=(76:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_195

theorem hecke_binding_196 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 455 =
      gridHeckeLeading m f s v 196 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 196=3 from rfl,
    show gridHeckeT 196=(77:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_196

theorem hecke_binding_197 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 456 =
      gridHeckeLeading m f s v 197 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 197=3 from rfl,
    show gridHeckeT 197=(78:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_197

theorem hecke_binding_198 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 457 =
      gridHeckeLeading m f s v 198 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 198=3 from rfl,
    show gridHeckeT 198=(79:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_198

theorem hecke_binding_199 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 458 =
      gridHeckeLeading m f s v 199 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 199=3 from rfl,
    show gridHeckeT 199=(81:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_199

theorem hecke_binding_200 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 459 =
      gridHeckeLeading m f s v 200 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 200=3 from rfl,
    show gridHeckeT 200=(82:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_200

theorem hecke_binding_201 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 460 =
      gridHeckeLeading m f s v 201 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 201=3 from rfl,
    show gridHeckeT 201=(88:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_201

theorem hecke_binding_202 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 461 =
      gridHeckeLeading m f s v 202 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 202=3 from rfl,
    show gridHeckeT 202=(89:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_202

theorem hecke_binding_203 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 462 =
      gridHeckeLeading m f s v 203 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 203=3 from rfl,
    show gridHeckeT 203=(91:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_203

theorem hecke_binding_204 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 463 =
      gridHeckeLeading m f s v 204 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 204=3 from rfl,
    show gridHeckeT 204=(92:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart28,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_204

theorem hecke_binding_205 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 464 =
      gridHeckeLeading m f s v 205 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 205=3 from rfl,
    show gridHeckeT 205=(94:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_205

theorem hecke_binding_206 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 465 =
      gridHeckeLeading m f s v 206 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 206=3 from rfl,
    show gridHeckeT 206=(99:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_206

theorem hecke_binding_207 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 466 =
      gridHeckeLeading m f s v 207 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 207=3 from rfl,
    show gridHeckeT 207=(100:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_207

theorem hecke_binding_208 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 467 =
      gridHeckeLeading m f s v 208 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 208=3 from rfl,
    show gridHeckeT 208=(101:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_208

theorem hecke_binding_209 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 468 =
      gridHeckeLeading m f s v 209 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 209=3 from rfl,
    show gridHeckeT 209=(108:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_209

theorem hecke_binding_210 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 469 =
      gridHeckeLeading m f s v 210 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 210=3 from rfl,
    show gridHeckeT 210=(116:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_210

theorem hecke_binding_211 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 470 =
      gridHeckeLeading m f s v 211 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 211=3 from rfl,
    show gridHeckeT 211=(122:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_211

theorem hecke_binding_212 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 471 =
      gridHeckeLeading m f s v 212 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 212=3 from rfl,
    show gridHeckeT 212=(125:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_212

theorem hecke_binding_213 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 472 =
      gridHeckeLeading m f s v 213 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 213=3 from rfl,
    show gridHeckeT 213=(126:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_213

theorem hecke_binding_214 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 473 =
      gridHeckeLeading m f s v 214 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 214=3 from rfl,
    show gridHeckeT 214=(129:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_214

theorem hecke_binding_215 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 474 =
      gridHeckeLeading m f s v 215 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 215=3 from rfl,
    show gridHeckeT 215=(130:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_215

theorem hecke_binding_216 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 475 =
      gridHeckeLeading m f s v 216 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 216=3 from rfl,
    show gridHeckeT 216=(133:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_216

theorem hecke_binding_217 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 476 =
      gridHeckeLeading m f s v 217 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 217=3 from rfl,
    show gridHeckeT 217=(135:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_217

theorem hecke_binding_218 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 477 =
      gridHeckeLeading m f s v 218 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 218=3 from rfl,
    show gridHeckeT 218=(138:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_218

theorem hecke_binding_219 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 478 =
      gridHeckeLeading m f s v 219 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 219=3 from rfl,
    show gridHeckeT 219=(139:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_219

theorem hecke_binding_220 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 479 =
      gridHeckeLeading m f s v 220 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 220=3 from rfl,
    show gridHeckeT 220=(140:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart29,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_220

theorem hecke_binding_221 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 480 =
      gridHeckeLeading m f s v 221 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 221=3 from rfl,
    show gridHeckeT 221=(141:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_221

theorem hecke_binding_222 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 481 =
      gridHeckeLeading m f s v 222 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 222=3 from rfl,
    show gridHeckeT 222=(142:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_222

theorem hecke_binding_223 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 482 =
      gridHeckeLeading m f s v 223 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 223=3 from rfl,
    show gridHeckeT 223=(144:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_223

theorem hecke_binding_224 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 483 =
      gridHeckeLeading m f s v 224 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 224=3 from rfl,
    show gridHeckeT 224=(148:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_224

theorem hecke_binding_225 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 484 =
      gridHeckeLeading m f s v 225 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 225=3 from rfl,
    show gridHeckeT 225=(151:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_225

theorem hecke_binding_226 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 485 =
      gridHeckeLeading m f s v 226 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 226=3 from rfl,
    show gridHeckeT 226=(154:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_226

theorem hecke_binding_227 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 486 =
      gridHeckeLeading m f s v 227 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 227=3 from rfl,
    show gridHeckeT 227=(155:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_227

theorem hecke_binding_228 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 487 =
      gridHeckeLeading m f s v 228 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 228=3 from rfl,
    show gridHeckeT 228=(156:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_228

theorem hecke_binding_229 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 488 =
      gridHeckeLeading m f s v 229 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 229=3 from rfl,
    show gridHeckeT 229=(158:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_229

theorem hecke_binding_230 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 489 =
      gridHeckeLeading m f s v 230 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 230=3 from rfl,
    show gridHeckeT 230=(159:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_230

theorem hecke_binding_231 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 490 =
      gridHeckeLeading m f s v 231 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 231=3 from rfl,
    show gridHeckeT 231=(162:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_231

theorem hecke_binding_232 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 491 =
      gridHeckeLeading m f s v 232 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 232=3 from rfl,
    show gridHeckeT 232=(164:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_232

theorem hecke_binding_233 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 492 =
      gridHeckeLeading m f s v 233 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 233=3 from rfl,
    show gridHeckeT 233=(167:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 3 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_233

theorem hecke_binding_234 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 493 =
      gridHeckeLeading m f s v 234 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 234=5 from rfl,
    show gridHeckeT 234=(8:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_234

theorem hecke_binding_235 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 494 =
      gridHeckeLeading m f s v 235 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 235=5 from rfl,
    show gridHeckeT 235=(9:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_235

theorem hecke_binding_236 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 495 =
      gridHeckeLeading m f s v 236 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 236=5 from rfl,
    show gridHeckeT 236=(12:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart30,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_236

theorem hecke_binding_237 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 496 =
      gridHeckeLeading m f s v 237 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 237=5 from rfl,
    show gridHeckeT 237=(14:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_237

theorem hecke_binding_238 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 497 =
      gridHeckeLeading m f s v 238 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 238=5 from rfl,
    show gridHeckeT 238=(15:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_238

theorem hecke_binding_239 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 498 =
      gridHeckeLeading m f s v 239 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 239=5 from rfl,
    show gridHeckeT 239=(17:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_239

theorem hecke_binding_240 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 499 =
      gridHeckeLeading m f s v 240 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 240=5 from rfl,
    show gridHeckeT 240=(18:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_240

theorem hecke_binding_241 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 500 =
      gridHeckeLeading m f s v 241 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 241=5 from rfl,
    show gridHeckeT 241=(20:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_241

theorem hecke_binding_242 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 501 =
      gridHeckeLeading m f s v 242 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 242=5 from rfl,
    show gridHeckeT 242=(21:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_242

theorem hecke_binding_243 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 502 =
      gridHeckeLeading m f s v 243 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 243=5 from rfl,
    show gridHeckeT 243=(24:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_243

theorem hecke_binding_244 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 503 =
      gridHeckeLeading m f s v 244 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 244=5 from rfl,
    show gridHeckeT 244=(26:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_244

theorem hecke_binding_245 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 504 =
      gridHeckeLeading m f s v 245 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 245=5 from rfl,
    show gridHeckeT 245=(27:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_245

theorem hecke_binding_246 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 505 =
      gridHeckeLeading m f s v 246 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 246=5 from rfl,
    show gridHeckeT 246=(28:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_246

theorem hecke_binding_247 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 506 =
      gridHeckeLeading m f s v 247 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 247=5 from rfl,
    show gridHeckeT 247=(30:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_247

theorem hecke_binding_248 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 507 =
      gridHeckeLeading m f s v 248 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 248=5 from rfl,
    show gridHeckeT 248=(31:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_248

theorem hecke_binding_249 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 508 =
      gridHeckeLeading m f s v 249 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 249=5 from rfl,
    show gridHeckeT 249=(33:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_249

theorem hecke_binding_250 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 509 =
      gridHeckeLeading m f s v 250 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 250=5 from rfl,
    show gridHeckeT 250=(34:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_250

theorem hecke_binding_251 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 510 =
      gridHeckeLeading m f s v 251 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 251=5 from rfl,
    show gridHeckeT 251=(36:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_251

theorem hecke_binding_252 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 511 =
      gridHeckeLeading m f s v 252 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 252=5 from rfl,
    show gridHeckeT 252=(37:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart31,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_252

theorem hecke_binding_253 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 512 =
      gridHeckeLeading m f s v 253 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 253=5 from rfl,
    show gridHeckeT 253=(39:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_253

theorem hecke_binding_254 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 513 =
      gridHeckeLeading m f s v 254 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 254=5 from rfl,
    show gridHeckeT 254=(40:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_254

theorem hecke_binding_255 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 514 =
      gridHeckeLeading m f s v 255 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 255=5 from rfl,
    show gridHeckeT 255=(42:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_255

theorem hecke_binding_256 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 515 =
      gridHeckeLeading m f s v 256 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 256=5 from rfl,
    show gridHeckeT 256=(45:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_256

theorem hecke_binding_257 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 516 =
      gridHeckeLeading m f s v 257 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 257=5 from rfl,
    show gridHeckeT 257=(48:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_257

theorem hecke_binding_258 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 517 =
      gridHeckeLeading m f s v 258 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 258=5 from rfl,
    show gridHeckeT 258=(57:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_258

theorem hecke_binding_259 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 518 =
      gridHeckeLeading m f s v 259 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 259=5 from rfl,
    show gridHeckeT 259=(60:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_259

theorem hecke_binding_260 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 519 =
      gridHeckeLeading m f s v 260 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 260=5 from rfl,
    show gridHeckeT 260=(62:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_260

theorem hecke_binding_261 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 520 =
      gridHeckeLeading m f s v 261 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 261=5 from rfl,
    show gridHeckeT 261=(63:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_261

theorem hecke_binding_262 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 521 =
      gridHeckeLeading m f s v 262 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 262=5 from rfl,
    show gridHeckeT 262=(65:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_262

theorem hecke_binding_263 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 522 =
      gridHeckeLeading m f s v 263 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 263=5 from rfl,
    show gridHeckeT 263=(66:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_263

theorem hecke_binding_264 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 523 =
      gridHeckeLeading m f s v 264 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 264=5 from rfl,
    show gridHeckeT 264=(68:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_264

theorem hecke_binding_265 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 524 =
      gridHeckeLeading m f s v 265 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 265=5 from rfl,
    show gridHeckeT 265=(69:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_265

theorem hecke_binding_266 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 525 =
      gridHeckeLeading m f s v 266 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 266=5 from rfl,
    show gridHeckeT 266=(71:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_266

theorem hecke_binding_267 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 526 =
      gridHeckeLeading m f s v 267 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 267=5 from rfl,
    show gridHeckeT 267=(72:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_267

theorem hecke_binding_268 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 527 =
      gridHeckeLeading m f s v 268 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 268=5 from rfl,
    show gridHeckeT 268=(74:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart32,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_268

theorem hecke_binding_269 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 528 =
      gridHeckeLeading m f s v 269 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 269=5 from rfl,
    show gridHeckeT 269=(75:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_269

theorem hecke_binding_270 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 529 =
      gridHeckeLeading m f s v 270 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 270=5 from rfl,
    show gridHeckeT 270=(76:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_270

theorem hecke_binding_271 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 530 =
      gridHeckeLeading m f s v 271 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 271=5 from rfl,
    show gridHeckeT 271=(81:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_271

theorem hecke_binding_272 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 531 =
      gridHeckeLeading m f s v 272 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 272=5 from rfl,
    show gridHeckeT 272=(82:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_272

theorem hecke_binding_273 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 532 =
      gridHeckeLeading m f s v 273 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 273=5 from rfl,
    show gridHeckeT 273=(84:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_273

theorem hecke_binding_274 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 533 =
      gridHeckeLeading m f s v 274 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 274=5 from rfl,
    show gridHeckeT 274=(85:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_274

theorem hecke_binding_275 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 534 =
      gridHeckeLeading m f s v 275 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 275=5 from rfl,
    show gridHeckeT 275=(87:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_275

theorem hecke_binding_276 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 535 =
      gridHeckeLeading m f s v 276 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 276=5 from rfl,
    show gridHeckeT 276=(88:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_276

theorem hecke_binding_277 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 536 =
      gridHeckeLeading m f s v 277 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 277=5 from rfl,
    show gridHeckeT 277=(90:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_277

theorem hecke_binding_278 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 537 =
      gridHeckeLeading m f s v 278 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 278=5 from rfl,
    show gridHeckeT 278=(93:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_278

theorem hecke_binding_279 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 538 =
      gridHeckeLeading m f s v 279 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 279=5 from rfl,
    show gridHeckeT 279=(94:ℤ) from rfl]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 5 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_279

theorem hecke_binding_280 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 539 =
      gridHeckeLeading m f s v 280 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 280=17 from rfl,
    show gridHeckeT 280=(5:ℤ) from rfl]
  rw [h17]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 17 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_280

theorem hecke_binding_281 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 540 =
      gridHeckeLeading m f s v 281 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 281=17 from rfl,
    show gridHeckeT 281=(6:ℤ) from rfl]
  rw [h17]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 17 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_281

theorem hecke_binding_282 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 541 =
      gridHeckeLeading m f s v 282 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 282=17 from rfl,
    show gridHeckeT 282=(9:ℤ) from rfl]
  rw [h17]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 17 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_282

theorem hecke_binding_283 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 542 =
      gridHeckeLeading m f s v 283 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 283=17 from rfl,
    show gridHeckeT 283=(12:ℤ) from rfl]
  rw [h17]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 17 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_283

theorem hecke_binding_284 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 543 =
      gridHeckeLeading m f s v 284 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 284=17 from rfl,
    show gridHeckeT 284=(18:ℤ) from rfl]
  rw [h17]
  norm_num [sourceRows,sourceRowsPart33,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 17 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_284

theorem hecke_binding_285 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 544 =
      gridHeckeLeading m f s v 285 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 285=17 from rfl,
    show gridHeckeT 285=(21:ℤ) from rfl]
  rw [h17]
  norm_num [sourceRows,sourceRowsPart34,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 17 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_285

theorem hecke_binding_286 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 510→ℂ)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 545 =
      gridHeckeLeading m f s v 286 := by
  simp only [Nat.cast_ofNat,gridHeckeLeading,show gridHeckeP 286=17 from rfl,
    show gridHeckeT 286=(24:ℤ) from rfl]
  rw [h17]
  norm_num [sourceRows,sourceRowsPart34,gridIndex,Finset.sum_range_succ] <;>
  field_simp [parameter_ne_zero 17 m (by decide) s]
  <;> ring <;> simp

#print axioms hecke_binding_286

end SmallLevelThirtyFourGridMMP
end
end

/-! ## SmallLevelThirtyFourGridMMPTaylorBindingBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourGridMMP
open SmallLevelThirtyFourGrid
open Complex SmallLevelPrimeRates SmallLevelFourPrimeRates SmallLevelThirtyFourUnitMMP

theorem taylor_binding_0 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 190 =
      gridLeadingRows m f ε s v (.taylor 0) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart11,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms taylor_binding_0

theorem taylor_binding_1 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 191 =
      gridLeadingRows m f ε s v (.taylor 1) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart11,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms taylor_binding_1

theorem taylor_binding_2 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 192 =
      gridLeadingRows m f ε s v (.taylor 2) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms taylor_binding_2

theorem taylor_binding_3 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 193 =
      gridLeadingRows m f ε s v (.taylor 3) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms taylor_binding_3

theorem taylor_binding_4 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 194 =
      gridLeadingRows m f ε s v (.taylor 4) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_4

theorem taylor_binding_5 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 195 =
      gridLeadingRows m f ε s v (.taylor 5) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_5

theorem taylor_binding_6 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 196 =
      gridLeadingRows m f ε s v (.taylor 6) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_6

theorem taylor_binding_7 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 197 =
      gridLeadingRows m f ε s v (.taylor 7) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_7

theorem taylor_binding_8 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 198 =
      gridLeadingRows m f ε s v (.taylor 8) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_8

theorem taylor_binding_9 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 199 =
      gridLeadingRows m f ε s v (.taylor 9) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_9

theorem taylor_binding_10 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 200 =
      gridLeadingRows m f ε s v (.taylor 10) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_10

theorem taylor_binding_11 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 201 =
      gridLeadingRows m f ε s v (.taylor 11) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_11

theorem taylor_binding_12 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 203 =
      gridLeadingRows m f ε s v (.taylor 12) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_12

theorem taylor_binding_13 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 204 =
      gridLeadingRows m f ε s v (.taylor 13) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_13

theorem taylor_binding_14 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 205 =
      gridLeadingRows m f ε s v (.taylor 14) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_14

theorem taylor_binding_15 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 206 =
      gridLeadingRows m f ε s v (.taylor 15) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_15

theorem taylor_binding_16 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 207 =
      gridLeadingRows m f ε s v (.taylor 16) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_16

theorem taylor_binding_17 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 208 =
      gridLeadingRows m f ε s v (.taylor 17) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart13,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_17

theorem taylor_binding_18 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 209 =
      gridLeadingRows m f ε s v (.taylor 18) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart13,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_18

theorem taylor_binding_19 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 210 =
      gridLeadingRows m f ε s v (.taylor 19) := by
  simp only [gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart13,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_19

theorem taylor_binding_20 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 212 =
      gridLeadingRows m f ε s v (.taylor 20) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart13,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_20

theorem taylor_binding_21 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 213 =
      gridLeadingRows m f ε s v (.taylor 21) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart13,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_21

theorem taylor_binding_22 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 214 =
      gridLeadingRows m f ε s v (.taylor 22) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart13,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_22

theorem taylor_binding_23 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 215 =
      gridLeadingRows m f ε s v (.taylor 23) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart13,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_23

theorem taylor_binding_24 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 216 =
      gridLeadingRows m f ε s v (.taylor 24) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart13,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_24

theorem taylor_binding_25 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 219 =
      gridLeadingRows m f ε s v (.taylor 25) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart13,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_25

theorem taylor_binding_26 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 220 =
      gridLeadingRows m f ε s v (.taylor 26) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart13,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_26

theorem taylor_binding_27 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 221 =
      gridLeadingRows m f ε s v (.taylor 27) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart13,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_27

theorem taylor_binding_28 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 222 =
      gridLeadingRows m f ε s v (.taylor 28) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart13,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_28

theorem taylor_binding_29 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 223 =
      gridLeadingRows m f ε s v (.taylor 29) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart13,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_29

theorem taylor_binding_30 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 224 =
      gridLeadingRows m f ε s v (.taylor 30) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_30

theorem taylor_binding_31 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 225 =
      gridLeadingRows m f ε s v (.taylor 31) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_31

theorem taylor_binding_32 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 226 =
      gridLeadingRows m f ε s v (.taylor 32) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_32

theorem taylor_binding_33 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 227 =
      gridLeadingRows m f ε s v (.taylor 33) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_33

theorem taylor_binding_34 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 228 =
      gridLeadingRows m f ε s v (.taylor 34) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_34

theorem taylor_binding_35 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 229 =
      gridLeadingRows m f ε s v (.taylor 35) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_35

theorem taylor_binding_36 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 230 =
      gridLeadingRows m f ε s v (.taylor 36) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_36

theorem taylor_binding_37 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 231 =
      gridLeadingRows m f ε s v (.taylor 37) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_37

theorem taylor_binding_38 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 232 =
      gridLeadingRows m f ε s v (.taylor 38) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_38

theorem taylor_binding_39 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 233 =
      gridLeadingRows m f ε s v (.taylor 39) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_39

theorem taylor_binding_40 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 234 =
      gridLeadingRows m f ε s v (.taylor 40) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_40

theorem taylor_binding_41 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 235 =
      gridLeadingRows m f ε s v (.taylor 41) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_41

theorem taylor_binding_42 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 236 =
      gridLeadingRows m f ε s v (.taylor 42) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_42

theorem taylor_binding_43 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 237 =
      gridLeadingRows m f ε s v (.taylor 43) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_43

theorem taylor_binding_44 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 239 =
      gridLeadingRows m f ε s v (.taylor 44) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_44

theorem taylor_binding_45 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 240 =
      gridLeadingRows m f ε s v (.taylor 45) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart15,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_45

theorem taylor_binding_46 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 241 =
      gridLeadingRows m f ε s v (.taylor 46) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart15,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_46

theorem taylor_binding_47 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 242 =
      gridLeadingRows m f ε s v (.taylor 47) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart15,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_47

theorem taylor_binding_48 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 243 =
      gridLeadingRows m f ε s v (.taylor 48) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart15,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_48

theorem taylor_binding_49 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 244 =
      gridLeadingRows m f ε s v (.taylor 49) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart15,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_49

theorem taylor_binding_50 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 245 =
      gridLeadingRows m f ε s v (.taylor 50) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart15,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_50

theorem taylor_binding_51 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 246 =
      gridLeadingRows m f ε s v (.taylor 51) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart15,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_51

theorem taylor_binding_52 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 248 =
      gridLeadingRows m f ε s v (.taylor 52) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart15,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_52

theorem taylor_binding_53 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 249 =
      gridLeadingRows m f ε s v (.taylor 53) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart15,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_53

theorem taylor_binding_54 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 251 =
      gridLeadingRows m f ε s v (.taylor 54) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart15,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_54

theorem taylor_binding_55 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 252 =
      gridLeadingRows m f ε s v (.taylor 55) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart15,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_55

theorem taylor_binding_56 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 253 =
      gridLeadingRows m f ε s v (.taylor 56) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart15,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_56

theorem taylor_binding_57 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 254 =
      gridLeadingRows m f ε s v (.taylor 57) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart15,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_57

theorem taylor_binding_58 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 257 =
      gridLeadingRows m f ε s v (.taylor 58) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart16,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_58

theorem taylor_binding_59 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 258 =
      gridLeadingRows m f ε s v (.taylor 59) := by
  simp only [Nat.cast_ofNat,gridLeadingRows,gridRamanujanLeading,taylorScalar_leading,grid_ramanujan_root,badParameter,h2,h17,hη]
  norm_num [sourceRows,sourceRowsPart16,gridSample,gridIndex,FinitenessRamanujanSum.residues,gridTaylorQ,gridTaylorSpecs,gridTaylorT,gridTaylorPartner,gridTaylorD,gridTaylorL,taylorPowers,SmallLevelFourPrimeRates.monomial,Finset.sum_filter,Finset.sum_range_succ] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms taylor_binding_59

end SmallLevelThirtyFourGridMMP
end
end

/-! ## SmallLevelThirtyFourGridMMPWordBindingBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourGridMMP
open SmallLevelThirtyFourGrid
open Complex SmallLevelPrimeRates SmallLevelFourPrimeRates SmallLevelThirtyFourUnitMMP

theorem word_binding_0 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 0 =
      gridLeadingRows m f ε s v (.word 0) := by
  change _ = v (gridGroupIndex 0)-gridMatrixScalar m f (ε*I^(2*m)) 0 0 s*v (gridGroupTarget 0)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 0=75 from rfl,show gridGroupTarget 0=423 from rfl,
    show gridGroupSource 0=50 from rfl,show sourceWord 50=[(4,false),(4,false)] from rfl,
    show groupPowers 0=((0,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_0

theorem word_binding_1 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 1 =
      gridLeadingRows m f ε s v (.word 1) := by
  change _ = v (gridGroupIndex 1)-gridMatrixScalar m f (ε*I^(2*m)) 1 0 s*v (gridGroupTarget 1)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 1=85 from rfl,show gridGroupTarget 1=425 from rfl,
    show gridGroupSource 1=50 from rfl,show sourceWord 50=[(4,false),(4,false)] from rfl,
    show groupPowers 1=((0,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_1

theorem word_binding_2 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 2 =
      gridLeadingRows m f ε s v (.word 2) := by
  change _ = v (gridGroupIndex 2)-gridMatrixScalar m f (ε*I^(2*m)) 2 0 s*v (gridGroupTarget 2)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 2=87 from rfl,show gridGroupTarget 2=435 from rfl,
    show gridGroupSource 2=50 from rfl,show sourceWord 50=[(4,false),(4,false)] from rfl,
    show groupPowers 2=((0,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_2

theorem word_binding_3 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 3 =
      gridLeadingRows m f ε s v (.word 3) := by
  change _ = v (gridGroupIndex 3)-gridMatrixScalar m f (ε*I^(2*m)) 3 0 s*v (gridGroupTarget 3)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 3=88 from rfl,show gridGroupTarget 3=410 from rfl,
    show gridGroupSource 3=50 from rfl,show sourceWord 50=[(4,false),(4,false)] from rfl,
    show groupPowers 3=((0,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_3

theorem word_binding_4 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 4 =
      gridLeadingRows m f ε s v (.word 4) := by
  change _ = v (gridGroupIndex 4)-gridMatrixScalar m f (ε*I^(2*m)) 4 0 s*v (gridGroupTarget 4)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 4=90 from rfl,show gridGroupTarget 4=420 from rfl,
    show gridGroupSource 4=50 from rfl,show sourceWord 50=[(4,false),(4,false)] from rfl,
    show groupPowers 4=((0,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_4

theorem word_binding_5 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 5 =
      gridLeadingRows m f ε s v (.word 5) := by
  change _ = v (gridGroupIndex 5)-gridMatrixScalar m f (ε*I^(2*m)) 5 0 s*v (gridGroupTarget 5)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 5=100 from rfl,show gridGroupTarget 5=422 from rfl,
    show gridGroupSource 5=50 from rfl,show sourceWord 50=[(4,false),(4,false)] from rfl,
    show groupPowers 5=((0,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_5

theorem word_binding_6 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 6 =
      gridLeadingRows m f ε s v (.word 6) := by
  change _ = v (gridGroupIndex 6)-gridMatrixScalar m f (ε*I^(2*m)) 6 0 s*v (gridGroupTarget 6)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 6=75 from rfl,show gridGroupTarget 6=498 from rfl,
    show gridGroupSource 6=19 from rfl,show sourceWord 19=[(1,true),(4,false)] from rfl,
    show groupPowers 6=((-1,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_6

theorem word_binding_7 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 7 =
      gridLeadingRows m f ε s v (.word 7) := by
  change _ = v (gridGroupIndex 7)-gridMatrixScalar m f (ε*I^(2*m)) 7 0 s*v (gridGroupTarget 7)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 7=85 from rfl,show gridGroupTarget 7=0 from rfl,
    show gridGroupSource 7=19 from rfl,show sourceWord 19=[(1,true),(4,false)] from rfl,
    show groupPowers 7=((-1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_7

theorem word_binding_8 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 8 =
      gridLeadingRows m f ε s v (.word 8) := by
  change _ = v (gridGroupIndex 8)-gridMatrixScalar m f (ε*I^(2*m)) 8 0 s*v (gridGroupTarget 8)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 8=86 from rfl,show gridGroupTarget 8=465 from rfl,
    show gridGroupSource 8=19 from rfl,show sourceWord 19=[(1,true),(4,false)] from rfl,
    show groupPowers 8=((1,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_8

theorem word_binding_9 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 9 =
      gridLeadingRows m f ε s v (.word 9) := by
  change _ = v (gridGroupIndex 9)-gridMatrixScalar m f (ε*I^(2*m)) 9 0 s*v (gridGroupTarget 9)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 9=87 from rfl,show gridGroupTarget 9=490 from rfl,
    show gridGroupSource 9=19 from rfl,show sourceWord 19=[(1,true),(4,false)] from rfl,
    show groupPowers 9=((-1,2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_9

theorem word_binding_10 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 10 =
      gridLeadingRows m f ε s v (.word 10) := by
  change _ = v (gridGroupIndex 10)-gridMatrixScalar m f (ε*I^(2*m)) 10 0 s*v (gridGroupTarget 10)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 10=90 from rfl,show gridGroupTarget 10=495 from rfl,
    show gridGroupSource 10=19 from rfl,show sourceWord 19=[(1,true),(4,false)] from rfl,
    show groupPowers 10=((1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_10

theorem word_binding_11 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 11 =
      gridLeadingRows m f ε s v (.word 11) := by
  change _ = v (gridGroupIndex 11)-gridMatrixScalar m f (ε*I^(2*m)) 11 0 s*v (gridGroupTarget 11)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 11=150 from rfl,show gridGroupTarget 11=497 from rfl,
    show gridGroupSource 11=19 from rfl,show sourceWord 19=[(1,true),(4,false)] from rfl,
    show groupPowers 11=((1,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_11

theorem word_binding_12 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 12 =
      gridLeadingRows m f ε s v (.word 12) := by
  change _ = v (gridGroupIndex 12)-gridMatrixScalar m f (ε*I^(2*m)) 12 0 s*v (gridGroupTarget 12)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 12=280 from rfl,show gridGroupTarget 12=87 from rfl,
    show gridGroupSource 12=53 from rfl,show sourceWord 53=[(4,true),(4,true),(2,false)] from rfl,
    show groupPowers 12=((1,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_12

theorem word_binding_13 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 13 =
      gridLeadingRows m f ε s v (.word 13) := by
  change _ = v (gridGroupIndex 13)-gridMatrixScalar m f (ε*I^(2*m)) 13 0 s*v (gridGroupTarget 13)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 13=66 from rfl,show gridGroupTarget 13=19 from rfl,
    show gridGroupSource 13=0 from rfl,show sourceWord 0=[(0,false),(1,false),(4,false)] from rfl,
    show groupPowers 13=((1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_13

theorem word_binding_14 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 14 =
      gridLeadingRows m f ε s v (.word 14) := by
  change _ = v (gridGroupIndex 14)-gridMatrixScalar m f (ε*I^(2*m)) 14 0 s*v (gridGroupTarget 14)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 14=75 from rfl,show gridGroupTarget 14=20 from rfl,
    show gridGroupSource 14=0 from rfl,show sourceWord 0=[(0,false),(1,false),(4,false)] from rfl,
    show groupPowers 14=((-1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_14

theorem word_binding_15 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 15 =
      gridLeadingRows m f ε s v (.word 15) := by
  change _ = v (gridGroupIndex 15)-gridMatrixScalar m f (ε*I^(2*m)) 15 0 s*v (gridGroupTarget 15)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 15=78 from rfl,show gridGroupTarget 15=21 from rfl,
    show gridGroupSource 15=0 from rfl,show sourceWord 0=[(0,false),(1,false),(4,false)] from rfl,
    show groupPowers 15=((1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart0,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_15

theorem word_binding_16 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 16 =
      gridLeadingRows m f ε s v (.word 16) := by
  change _ = v (gridGroupIndex 16)-gridMatrixScalar m f (ε*I^(2*m)) 16 0 s*v (gridGroupTarget 16)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 16=81 from rfl,show gridGroupTarget 16=24 from rfl,
    show gridGroupSource 16=0 from rfl,show sourceWord 0=[(0,false),(1,false),(4,false)] from rfl,
    show groupPowers 16=((-1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_16

theorem word_binding_17 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 17 =
      gridLeadingRows m f ε s v (.word 17) := by
  change _ = v (gridGroupIndex 17)-gridMatrixScalar m f (ε*I^(2*m)) 17 0 s*v (gridGroupTarget 17)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 17=82 from rfl,show gridGroupTarget 17=27 from rfl,
    show gridGroupSource 17=0 from rfl,show sourceWord 0=[(0,false),(1,false),(4,false)] from rfl,
    show groupPowers 17=((1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_17

theorem word_binding_18 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 18 =
      gridLeadingRows m f ε s v (.word 18) := by
  change _ = v (gridGroupIndex 18)-gridMatrixScalar m f (ε*I^(2*m)) 18 0 s*v (gridGroupTarget 18)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 18=83 from rfl,show gridGroupTarget 18=36 from rfl,
    show gridGroupSource 18=0 from rfl,show sourceWord 0=[(0,false),(1,false),(4,false)] from rfl,
    show groupPowers 18=((-1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_18

theorem word_binding_19 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 20 =
      gridLeadingRows m f ε s v (.word 19) := by
  change _ = v (gridGroupIndex 19)-gridMatrixScalar m f (ε*I^(2*m)) 19 0 s*v (gridGroupTarget 19)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 19=86 from rfl,show gridGroupTarget 19=9 from rfl,
    show gridGroupSource 19=0 from rfl,show sourceWord 0=[(0,false),(1,false),(4,false)] from rfl,
    show groupPowers 19=((1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_19

theorem word_binding_20 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 21 =
      gridLeadingRows m f ε s v (.word 20) := by
  change _ = v (gridGroupIndex 20)-gridMatrixScalar m f (ε*I^(2*m)) 20 0 s*v (gridGroupTarget 20)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 20=87 from rfl,show gridGroupTarget 20=12 from rfl,
    show gridGroupSource 20=0 from rfl,show sourceWord 0=[(0,false),(1,false),(4,false)] from rfl,
    show groupPowers 20=((-1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_20

theorem word_binding_21 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 22 =
      gridLeadingRows m f ε s v (.word 21) := by
  change _ = v (gridGroupIndex 21)-gridMatrixScalar m f (ε*I^(2*m)) 21 0 s*v (gridGroupTarget 21)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 21=90 from rfl,show gridGroupTarget 21=15 from rfl,
    show gridGroupSource 21=0 from rfl,show sourceWord 0=[(0,false),(1,false),(4,false)] from rfl,
    show groupPowers 21=((1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_21

theorem word_binding_22 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 23 =
      gridLeadingRows m f ε s v (.word 22) := by
  change _ = v (gridGroupIndex 22)-gridMatrixScalar m f (ε*I^(2*m)) 22 0 s*v (gridGroupTarget 22)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 22=93 from rfl,show gridGroupTarget 22=16 from rfl,
    show gridGroupSource 22=0 from rfl,show sourceWord 0=[(0,false),(1,false),(4,false)] from rfl,
    show groupPowers 22=((-1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_22

theorem word_binding_23 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 24 =
      gridLeadingRows m f ε s v (.word 23) := by
  change _ = v (gridGroupIndex 23)-gridMatrixScalar m f (ε*I^(2*m)) 23 0 s*v (gridGroupTarget 23)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 23=102 from rfl,show gridGroupTarget 23=17 from rfl,
    show gridGroupSource 23=0 from rfl,show sourceWord 0=[(0,false),(1,false),(4,false)] from rfl,
    show groupPowers 23=((1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms word_binding_23

theorem word_binding_24 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 25 =
      gridLeadingRows m f ε s v (.word 24) := by
  change _ = v (gridGroupIndex 24)-gridMatrixScalar m f (ε*I^(2*m)) 24 0 s*v (gridGroupTarget 24)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 24=0 from rfl,show gridGroupTarget 24=480 from rfl,
    show gridGroupSource 24=4 from rfl,show sourceWord 4=[(0,false),(2,false),(3,false)] from rfl,
    show groupPowers 24=((0,0,1,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_24

theorem word_binding_25 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 26 =
      gridLeadingRows m f ε s v (.word 25) := by
  change _ = v (gridGroupIndex 25)-gridMatrixScalar m f (ε*I^(2*m)) 25 0 s*v (gridGroupTarget 25)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 25=255 from rfl,show gridGroupTarget 25=495 from rfl,
    show gridGroupSource 25=35 from rfl,show sourceWord 35=[(3,false),(0,false),(2,false)] from rfl,
    show groupPowers 25=((0,0,1,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_25

theorem word_binding_26 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 27 =
      gridLeadingRows m f ε s v (.word 26) := by
  change _ = v (gridGroupIndex 26)-gridMatrixScalar m f (ε*I^(2*m)) 26 0 s*v (gridGroupTarget 26)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 26=270 from rfl,show gridGroupTarget 26=0 from rfl,
    show gridGroupSource 26=35 from rfl,show sourceWord 35=[(3,false),(0,false),(2,false)] from rfl,
    show groupPowers 26=((0,0,-1,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_26

theorem word_binding_27 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 28 =
      gridLeadingRows m f ε s v (.word 27) := by
  change _ = v (gridGroupIndex 27)-gridMatrixScalar m f (ε*I^(2*m)) 27 0 s*v (gridGroupTarget 27)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 27=271 from rfl,show gridGroupTarget 27=255 from rfl,
    show gridGroupSource 27=35 from rfl,show sourceWord 35=[(3,false),(0,false),(2,false)] from rfl,
    show groupPowers 27=((0,-2,-1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_27

theorem word_binding_28 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 29 =
      gridLeadingRows m f ε s v (.word 28) := by
  change _ = v (gridGroupIndex 28)-gridMatrixScalar m f (ε*I^(2*m)) 28 0 s*v (gridGroupTarget 28)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 28=272 from rfl,show gridGroupTarget 28=480 from rfl,
    show gridGroupSource 28=35 from rfl,show sourceWord 35=[(3,false),(0,false),(2,false)] from rfl,
    show groupPowers 28=((0,-2,1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_28

theorem word_binding_29 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 30 =
      gridLeadingRows m f ε s v (.word 29) := by
  change _ = v (gridGroupIndex 29)-gridMatrixScalar m f (ε*I^(2*m)) 29 0 s*v (gridGroupTarget 29)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 29=285 from rfl,show gridGroupTarget 29=493 from rfl,
    show gridGroupSource 29=35 from rfl,show sourceWord 35=[(3,false),(0,false),(2,false)] from rfl,
    show groupPowers 29=((0,2,-1,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_29

theorem word_binding_30 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 31 =
      gridLeadingRows m f ε s v (.word 30) := by
  change _ = v (gridGroupIndex 30)-gridMatrixScalar m f (ε*I^(2*m)) 30 0 s*v (gridGroupTarget 30)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 30=260 from rfl,show gridGroupTarget 30=32 from rfl,
    show gridGroupSource 30=13 from rfl,show sourceWord 13=[(1,false),(2,false),(2,false)] from rfl,
    show groupPowers 30=((0,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart1,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_30

theorem word_binding_31 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 32 =
      gridLeadingRows m f ε s v (.word 31) := by
  change _ = v (gridGroupIndex 31)-gridMatrixScalar m f (ε*I^(2*m)) 31 0 s*v (gridGroupTarget 31)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 31=268 from rfl,show gridGroupTarget 31=40 from rfl,
    show gridGroupSource 31=13 from rfl,show sourceWord 13=[(1,false),(2,false),(2,false)] from rfl,
    show groupPowers 31=((0,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_31

theorem word_binding_32 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 33 =
      gridLeadingRows m f ε s v (.word 32) := by
  change _ = v (gridGroupIndex 32)-gridMatrixScalar m f (ε*I^(2*m)) 32 0 s*v (gridGroupTarget 32)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 32=270 from rfl,show gridGroupTarget 32=30 from rfl,
    show gridGroupSource 32=13 from rfl,show sourceWord 13=[(1,false),(2,false),(2,false)] from rfl,
    show groupPowers 32=((0,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_32

theorem word_binding_33 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 34 =
      gridLeadingRows m f ε s v (.word 33) := by
  change _ = v (gridGroupIndex 33)-gridMatrixScalar m f (ε*I^(2*m)) 33 0 s*v (gridGroupTarget 33)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 33=276 from rfl,show gridGroupTarget 33=483 from rfl,
    show gridGroupSource 33=26 from rfl,show sourceWord 26=[(2,false),(4,true),(2,false)] from rfl,
    show groupPowers 33=((1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_33

theorem word_binding_34 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 35 =
      gridLeadingRows m f ε s v (.word 34) := by
  change _ = v (gridGroupIndex 34)-gridMatrixScalar m f (ε*I^(2*m)) 34 0 s*v (gridGroupTarget 34)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 34=277 from rfl,show gridGroupTarget 34=486 from rfl,
    show gridGroupSource 34=26 from rfl,show sourceWord 26=[(2,false),(4,true),(2,false)] from rfl,
    show groupPowers 34=((-1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_34

theorem word_binding_35 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 36 =
      gridLeadingRows m f ε s v (.word 35) := by
  change _ = v (gridGroupIndex 35)-gridMatrixScalar m f (ε*I^(2*m)) 35 0 s*v (gridGroupTarget 35)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 35=279 from rfl,show gridGroupTarget 35=482 from rfl,
    show gridGroupSource 35=26 from rfl,show sourceWord 26=[(2,false),(4,true),(2,false)] from rfl,
    show groupPowers 35=((-1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_35

theorem word_binding_36 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 37 =
      gridLeadingRows m f ε s v (.word 36) := by
  change _ = v (gridGroupIndex 36)-gridMatrixScalar m f (ε*I^(2*m)) 36 0 s*v (gridGroupTarget 36)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 36=60 from rfl,show gridGroupTarget 36=87 from rfl,
    show gridGroupSource 36=51 from rfl,show sourceWord 51=[(4,true)] from rfl,
    show groupPowers 36=((1,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_36

theorem word_binding_37 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 38 =
      gridLeadingRows m f ε s v (.word 37) := by
  change _ = v (gridGroupIndex 37)-gridMatrixScalar m f (ε*I^(2*m)) 37 0 s*v (gridGroupTarget 37)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 37=135 from rfl,show gridGroupTarget 37=88 from rfl,
    show gridGroupSource 37=51 from rfl,show sourceWord 51=[(4,true)] from rfl,
    show groupPowers 37=((-1,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_37

theorem word_binding_38 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 39 =
      gridLeadingRows m f ε s v (.word 38) := by
  change _ = v (gridGroupIndex 38)-gridMatrixScalar m f (ε*I^(2*m)) 38 0 s*v (gridGroupTarget 38)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 38=360 from rfl,show gridGroupTarget 38=89 from rfl,
    show gridGroupSource 38=51 from rfl,show sourceWord 51=[(4,true)] from rfl,
    show groupPowers 38=((1,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_38

theorem word_binding_39 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 40 =
      gridLeadingRows m f ε s v (.word 39) := by
  change _ = v (gridGroupIndex 39)-gridMatrixScalar m f (ε*I^(2*m)) 39 0 s*v (gridGroupTarget 39)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 39=90 from rfl,show gridGroupTarget 39=18 from rfl,
    show gridGroupSource 39=14 from rfl,show sourceWord 14=[(1,false),(4,false),(4,false)] from rfl,
    show groupPowers 39=((0,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_39

theorem word_binding_40 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 41 =
      gridLeadingRows m f ε s v (.word 40) := by
  change _ = v (gridGroupIndex 40)-gridMatrixScalar m f (ε*I^(2*m)) 40 0 s*v (gridGroupTarget 40)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 40=450 from rfl,show gridGroupTarget 40=261 from rfl,
    show gridGroupSource 40=29 from rfl,show sourceWord 29=[(2,true),(1,false),(0,true)] from rfl,
    show groupPowers 40=((1,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_40

theorem word_binding_41 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 42 =
      gridLeadingRows m f ε s v (.word 41) := by
  change _ = v (gridGroupIndex 41)-gridMatrixScalar m f (ε*I^(2*m)) 41 0 s*v (gridGroupTarget 41)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 41=475 from rfl,show gridGroupTarget 41=262 from rfl,
    show gridGroupSource 41=29 from rfl,show sourceWord 29=[(2,true),(1,false),(0,true)] from rfl,
    show groupPowers 41=((-1,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_41

theorem word_binding_42 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 43 =
      gridLeadingRows m f ε s v (.word 42) := by
  change _ = v (gridGroupIndex 42)-gridMatrixScalar m f (ε*I^(2*m)) 42 0 s*v (gridGroupTarget 42)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 42=490 from rfl,show gridGroupTarget 42=265 from rfl,
    show gridGroupSource 42=29 from rfl,show sourceWord 29=[(2,true),(1,false),(0,true)] from rfl,
    show groupPowers 42=((1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_42

theorem word_binding_43 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 44 =
      gridLeadingRows m f ε s v (.word 43) := by
  change _ = v (gridGroupIndex 43)-gridMatrixScalar m f (ε*I^(2*m)) 43 0 s*v (gridGroupTarget 43)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 43=495 from rfl,show gridGroupTarget 43=270 from rfl,
    show gridGroupSource 43=29 from rfl,show sourceWord 29=[(2,true),(1,false),(0,true)] from rfl,
    show groupPowers 43=((-1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_43

theorem word_binding_44 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 45 =
      gridLeadingRows m f ε s v (.word 44) := by
  change _ = v (gridGroupIndex 44)-gridMatrixScalar m f (ε*I^(2*m)) 44 0 s*v (gridGroupTarget 44)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 44=498 from rfl,show gridGroupTarget 44=285 from rfl,
    show gridGroupSource 44=29 from rfl,show sourceWord 29=[(2,true),(1,false),(0,true)] from rfl,
    show groupPowers 44=((1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_44

theorem word_binding_45 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 46 =
      gridLeadingRows m f ε s v (.word 45) := by
  change _ = v (gridGroupIndex 45)-gridMatrixScalar m f (ε*I^(2*m)) 45 0 s*v (gridGroupTarget 45)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 45=499 from rfl,show gridGroupTarget 45=310 from rfl,
    show gridGroupSource 45=29 from rfl,show sourceWord 29=[(2,true),(1,false),(0,true)] from rfl,
    show groupPowers 45=((-1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart2,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_45

theorem word_binding_46 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 48 =
      gridLeadingRows m f ε s v (.word 46) := by
  change _ = v (gridGroupIndex 46)-gridMatrixScalar m f (ε*I^(2*m)) 46 0 s*v (gridGroupTarget 46)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 46=501 from rfl,show gridGroupTarget 46=210 from rfl,
    show gridGroupSource 46=29 from rfl,show sourceWord 29=[(2,true),(1,false),(0,true)] from rfl,
    show groupPowers 46=((-1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_46

theorem word_binding_47 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 49 =
      gridLeadingRows m f ε s v (.word 47) := by
  change _ = v (gridGroupIndex 47)-gridMatrixScalar m f (ε*I^(2*m)) 47 0 s*v (gridGroupTarget 47)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 47=502 from rfl,show gridGroupTarget 47=235 from rfl,
    show gridGroupSource 47=29 from rfl,show sourceWord 29=[(2,true),(1,false),(0,true)] from rfl,
    show groupPowers 47=((1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_47

theorem word_binding_48 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 50 =
      gridLeadingRows m f ε s v (.word 48) := by
  change _ = v (gridGroupIndex 48)-gridMatrixScalar m f (ε*I^(2*m)) 48 0 s*v (gridGroupTarget 48)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 48=505 from rfl,show gridGroupTarget 48=250 from rfl,
    show gridGroupSource 48=29 from rfl,show sourceWord 29=[(2,true),(1,false),(0,true)] from rfl,
    show groupPowers 48=((-1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_48

theorem word_binding_49 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 51 =
      gridLeadingRows m f ε s v (.word 49) := by
  change _ = v (gridGroupIndex 49)-gridMatrixScalar m f (ε*I^(2*m)) 49 0 s*v (gridGroupTarget 49)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 49=15 from rfl,show gridGroupTarget 49=426 from rfl,
    show gridGroupSource 49=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 49=((-1,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_49

theorem word_binding_50 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 52 =
      gridLeadingRows m f ε s v (.word 50) := by
  change _ = v (gridGroupIndex 50)-gridMatrixScalar m f (ε*I^(2*m)) 50 0 s*v (gridGroupTarget 50)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 50=40 from rfl,show gridGroupTarget 50=429 from rfl,
    show gridGroupSource 50=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 50=((1,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_50

theorem word_binding_51 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 53 =
      gridLeadingRows m f ε s v (.word 51) := by
  change _ = v (gridGroupIndex 51)-gridMatrixScalar m f (ε*I^(2*m)) 51 0 s*v (gridGroupTarget 51)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 51=45 from rfl,show gridGroupTarget 51=430 from rfl,
    show gridGroupSource 51=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 51=((-1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_51

theorem word_binding_52 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 54 =
      gridLeadingRows m f ε s v (.word 52) := by
  change _ = v (gridGroupIndex 52)-gridMatrixScalar m f (ε*I^(2*m)) 52 0 s*v (gridGroupTarget 52)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 52=65 from rfl,show gridGroupTarget 52=438 from rfl,
    show gridGroupSource 52=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 52=((-1,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_52

theorem word_binding_53 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 55 =
      gridLeadingRows m f ε s v (.word 53) := by
  change _ = v (gridGroupIndex 53)-gridMatrixScalar m f (ε*I^(2*m)) 53 0 s*v (gridGroupTarget 53)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 53=72 from rfl,show gridGroupTarget 53=445 from rfl,
    show gridGroupSource 53=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 53=((1,2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_53

theorem word_binding_54 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 56 =
      gridLeadingRows m f ε s v (.word 54) := by
  change _ = v (gridGroupIndex 54)-gridMatrixScalar m f (ε*I^(2*m)) 54 0 s*v (gridGroupTarget 54)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 54=75 from rfl,show gridGroupTarget 54=450 from rfl,
    show gridGroupSource 54=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 54=((-1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_54

theorem word_binding_55 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 57 =
      gridLeadingRows m f ε s v (.word 55) := by
  change _ = v (gridGroupIndex 55)-gridMatrixScalar m f (ε*I^(2*m)) 55 0 s*v (gridGroupTarget 55)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 55=80 from rfl,show gridGroupTarget 55=465 from rfl,
    show gridGroupSource 55=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 55=((1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_55

theorem word_binding_56 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 58 =
      gridLeadingRows m f ε s v (.word 56) := by
  change _ = v (gridGroupIndex 56)-gridMatrixScalar m f (ε*I^(2*m)) 56 0 s*v (gridGroupTarget 56)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 56=81 from rfl,show gridGroupTarget 56=470 from rfl,
    show gridGroupSource 56=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 56=((-1,2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_56

theorem word_binding_57 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 59 =
      gridLeadingRows m f ε s v (.word 57) := by
  change _ = v (gridGroupIndex 57)-gridMatrixScalar m f (ε*I^(2*m)) 57 0 s*v (gridGroupTarget 57)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 57=84 from rfl,show gridGroupTarget 57=495 from rfl,
    show gridGroupSource 57=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 57=((1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_57

theorem word_binding_58 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 60 =
      gridLeadingRows m f ε s v (.word 58) := by
  change _ = v (gridGroupIndex 58)-gridMatrixScalar m f (ε*I^(2*m)) 58 0 s*v (gridGroupTarget 58)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 58=91 from rfl,show gridGroupTarget 58=480 from rfl,
    show gridGroupSource 58=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 58=((-1,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_58

theorem word_binding_59 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 61 =
      gridLeadingRows m f ε s v (.word 59) := by
  change _ = v (gridGroupIndex 59)-gridMatrixScalar m f (ε*I^(2*m)) 59 0 s*v (gridGroupTarget 59)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 59=92 from rfl,show gridGroupTarget 59=195 from rfl,
    show gridGroupSource 59=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 59=((1,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_59

theorem word_binding_60 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 62 =
      gridLeadingRows m f ε s v (.word 60) := by
  change _ = v (gridGroupIndex 60)-gridMatrixScalar m f (ε*I^(2*m)) 60 0 s*v (gridGroupTarget 60)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 60=93 from rfl,show gridGroupTarget 60=270 from rfl,
    show gridGroupSource 60=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 60=((-1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_60

theorem word_binding_61 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 63 =
      gridLeadingRows m f ε s v (.word 61) := by
  change _ = v (gridGroupIndex 61)-gridMatrixScalar m f (ε*I^(2*m)) 61 0 s*v (gridGroupTarget 61)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 61=95 from rfl,show gridGroupTarget 61=330 from rfl,
    show gridGroupSource 61=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 61=((-1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart3,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_61

theorem word_binding_62 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 64 =
      gridLeadingRows m f ε s v (.word 62) := by
  change _ = v (gridGroupIndex 62)-gridMatrixScalar m f (ε*I^(2*m)) 62 0 s*v (gridGroupTarget 62)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 62=96 from rfl,show gridGroupTarget 62=345 from rfl,
    show gridGroupSource 62=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 62=((1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_62

theorem word_binding_63 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 65 =
      gridLeadingRows m f ε s v (.word 63) := by
  change _ = v (gridGroupIndex 63)-gridMatrixScalar m f (ε*I^(2*m)) 63 0 s*v (gridGroupTarget 63)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 63=99 from rfl,show gridGroupTarget 63=370 from rfl,
    show gridGroupSource 63=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 63=((-1,2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_63

theorem word_binding_64 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 66 =
      gridLeadingRows m f ε s v (.word 64) := by
  change _ = v (gridGroupIndex 64)-gridMatrixScalar m f (ε*I^(2*m)) 64 0 s*v (gridGroupTarget 64)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 64=100 from rfl,show gridGroupTarget 64=375 from rfl,
    show gridGroupSource 64=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 64=((1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_64

theorem word_binding_65 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 67 =
      gridLeadingRows m f ε s v (.word 65) := by
  change _ = v (gridGroupIndex 65)-gridMatrixScalar m f (ε*I^(2*m)) 65 0 s*v (gridGroupTarget 65)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 65=105 from rfl,show gridGroupTarget 65=390 from rfl,
    show gridGroupSource 65=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 65=((-1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_65

theorem word_binding_66 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 68 =
      gridLeadingRows m f ε s v (.word 66) := by
  change _ = v (gridGroupIndex 66)-gridMatrixScalar m f (ε*I^(2*m)) 66 0 s*v (gridGroupTarget 66)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 66=108 from rfl,show gridGroupTarget 66=395 from rfl,
    show gridGroupSource 66=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 66=((1,2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_66

theorem word_binding_67 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 69 =
      gridLeadingRows m f ε s v (.word 67) := by
  change _ = v (gridGroupIndex 67)-gridMatrixScalar m f (ε*I^(2*m)) 67 0 s*v (gridGroupTarget 67)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 67=115 from rfl,show gridGroupTarget 67=402 from rfl,
    show gridGroupSource 67=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 67=((-1,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_67

theorem word_binding_68 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 70 =
      gridLeadingRows m f ε s v (.word 68) := by
  change _ = v (gridGroupIndex 68)-gridMatrixScalar m f (ε*I^(2*m)) 68 0 s*v (gridGroupTarget 68)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 68=120 from rfl,show gridGroupTarget 68=405 from rfl,
    show gridGroupSource 68=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 68=((1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_68

theorem word_binding_69 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 71 =
      gridLeadingRows m f ε s v (.word 69) := by
  change _ = v (gridGroupIndex 69)-gridMatrixScalar m f (ε*I^(2*m)) 69 0 s*v (gridGroupTarget 69)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 69=140 from rfl,show gridGroupTarget 69=411 from rfl,
    show gridGroupSource 69=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 69=((1,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_69

theorem word_binding_70 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 72 =
      gridLeadingRows m f ε s v (.word 70) := by
  change _ = v (gridGroupIndex 70)-gridMatrixScalar m f (ε*I^(2*m)) 70 0 s*v (gridGroupTarget 70)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 70=165 from rfl,show gridGroupTarget 70=414 from rfl,
    show gridGroupSource 70=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 70=((-1,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_70

theorem word_binding_71 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 73 =
      gridLeadingRows m f ε s v (.word 71) := by
  change _ = v (gridGroupIndex 71)-gridMatrixScalar m f (ε*I^(2*m)) 71 0 s*v (gridGroupTarget 71)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 71=180 from rfl,show gridGroupTarget 71=415 from rfl,
    show gridGroupSource 71=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 71=((1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_71

theorem word_binding_72 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 74 =
      gridLeadingRows m f ε s v (.word 72) := by
  change _ = v (gridGroupIndex 72)-gridMatrixScalar m f (ε*I^(2*m)) 72 0 s*v (gridGroupTarget 72)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 72=240 from rfl,show gridGroupTarget 72=417 from rfl,
    show gridGroupSource 72=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 72=((1,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_72

theorem word_binding_73 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 75 =
      gridLeadingRows m f ε s v (.word 73) := by
  change _ = v (gridGroupIndex 73)-gridMatrixScalar m f (ε*I^(2*m)) 73 0 s*v (gridGroupTarget 73)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 73=315 from rfl,show gridGroupTarget 73=418 from rfl,
    show gridGroupSource 73=45 from rfl,show sourceWord 45=[(4,false)] from rfl,
    show groupPowers 73=((-1,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_73

theorem word_binding_74 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 76 =
      gridLeadingRows m f ε s v (.word 74) := by
  change _ = v (gridGroupIndex 74)-gridMatrixScalar m f (ε*I^(2*m)) 74 0 s*v (gridGroupTarget 74)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 74=419 from rfl,show gridGroupTarget 74=30 from rfl,
    show gridGroupSource 74=10 from rfl,show sourceWord 10=[(0,true),(4,true),(0,true)] from rfl,
    show groupPowers 74=((-1,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_74

theorem word_binding_75 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 77 =
      gridLeadingRows m f ε s v (.word 75) := by
  change _ = v (gridGroupIndex 75)-gridMatrixScalar m f (ε*I^(2*m)) 75 0 s*v (gridGroupTarget 75)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 75=421 from rfl,show gridGroupTarget 75=150 from rfl,
    show gridGroupSource 75=10 from rfl,show sourceWord 10=[(0,true),(4,true),(0,true)] from rfl,
    show groupPowers 75=((-1,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_75

theorem word_binding_76 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 78 =
      gridLeadingRows m f ε s v (.word 76) := by
  change _ = v (gridGroupIndex 76)-gridMatrixScalar m f (ε*I^(2*m)) 76 0 s*v (gridGroupTarget 76)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 76=210 from rfl,show gridGroupTarget 76=424 from rfl,
    show gridGroupSource 76=47 from rfl,show sourceWord 47=[(4,false),(2,false)] from rfl,
    show groupPowers 76=((0,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_76

theorem word_binding_77 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 79 =
      gridLeadingRows m f ε s v (.word 77) := by
  change _ = v (gridGroupIndex 77)-gridMatrixScalar m f (ε*I^(2*m)) 77 0 s*v (gridGroupTarget 77)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 77=260 from rfl,show gridGroupTarget 77=426 from rfl,
    show gridGroupSource 77=47 from rfl,show sourceWord 47=[(4,false),(2,false)] from rfl,
    show groupPowers 77=((0,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart4,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_77

theorem word_binding_78 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 80 =
      gridLeadingRows m f ε s v (.word 78) := by
  change _ = v (gridGroupIndex 78)-gridMatrixScalar m f (ε*I^(2*m)) 78 0 s*v (gridGroupTarget 78)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 78=264 from rfl,show gridGroupTarget 78=430 from rfl,
    show gridGroupSource 78=47 from rfl,show sourceWord 47=[(4,false),(2,false)] from rfl,
    show groupPowers 78=((0,2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_78

theorem word_binding_79 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 81 =
      gridLeadingRows m f ε s v (.word 79) := by
  change _ = v (gridGroupIndex 79)-gridMatrixScalar m f (ε*I^(2*m)) 79 0 s*v (gridGroupTarget 79)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 79=266 from rfl,show gridGroupTarget 79=480 from rfl,
    show gridGroupSource 79=47 from rfl,show sourceWord 47=[(4,false),(2,false)] from rfl,
    show groupPowers 79=((0,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_79

theorem word_binding_80 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 82 =
      gridLeadingRows m f ε s v (.word 80) := by
  change _ = v (gridGroupIndex 80)-gridMatrixScalar m f (ε*I^(2*m)) 80 0 s*v (gridGroupTarget 80)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 80=267 from rfl,show gridGroupTarget 80=405 from rfl,
    show gridGroupSource 80=47 from rfl,show sourceWord 47=[(4,false),(2,false)] from rfl,
    show groupPowers 80=((0,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_80

theorem word_binding_81 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 83 =
      gridLeadingRows m f ε s v (.word 81) := by
  change _ = v (gridGroupIndex 81)-gridMatrixScalar m f (ε*I^(2*m)) 81 0 s*v (gridGroupTarget 81)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 81=475 from rfl,show gridGroupTarget 81=89 from rfl,
    show gridGroupSource 81=52 from rfl,show sourceWord 52=[(4,true),(2,true),(0,true)] from rfl,
    show groupPowers 81=((0,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_81

theorem word_binding_82 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 84 =
      gridLeadingRows m f ε s v (.word 82) := by
  change _ = v (gridGroupIndex 82)-gridMatrixScalar m f (ε*I^(2*m)) 82 0 s*v (gridGroupTarget 82)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 82=481 from rfl,show gridGroupTarget 82=95 from rfl,
    show gridGroupSource 82=52 from rfl,show sourceWord 52=[(4,true),(2,true),(0,true)] from rfl,
    show groupPowers 82=((0,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_82

theorem word_binding_83 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 85 =
      gridLeadingRows m f ε s v (.word 83) := by
  change _ = v (gridGroupIndex 83)-gridMatrixScalar m f (ε*I^(2*m)) 83 0 s*v (gridGroupTarget 83)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 83=102 from rfl,show gridGroupTarget 83=265 from rfl,
    show gridGroupSource 83=41 from rfl,show sourceWord 41=[(3,false),(2,false),(4,false)] from rfl,
    show groupPowers 83=((1,2,1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_83

theorem word_binding_84 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 86 =
      gridLeadingRows m f ε s v (.word 84) := by
  change _ = v (gridGroupIndex 84)-gridMatrixScalar m f (ε*I^(2*m)) 84 0 s*v (gridGroupTarget 84)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 84=276 from rfl,show gridGroupTarget 84=267 from rfl,
    show gridGroupSource 84=34 from rfl,show sourceWord 34=[(2,true),(4,true),(2,false)] from rfl,
    show groupPowers 84=((1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_84

theorem word_binding_85 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 87 =
      gridLeadingRows m f ε s v (.word 85) := by
  change _ = v (gridGroupIndex 85)-gridMatrixScalar m f (ε*I^(2*m)) 85 0 s*v (gridGroupTarget 85)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 85=277 from rfl,show gridGroupTarget 85=268 from rfl,
    show gridGroupSource 85=34 from rfl,show sourceWord 34=[(2,true),(4,true),(2,false)] from rfl,
    show groupPowers 85=((-1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_85

theorem word_binding_86 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 89 =
      gridLeadingRows m f ε s v (.word 86) := by
  change _ = v (gridGroupIndex 86)-gridMatrixScalar m f (ε*I^(2*m)) 86 0 s*v (gridGroupTarget 86)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 86=279 from rfl,show gridGroupTarget 86=264 from rfl,
    show gridGroupSource 86=34 from rfl,show sourceWord 34=[(2,true),(4,true),(2,false)] from rfl,
    show groupPowers 86=((-1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_86

theorem word_binding_87 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 90 =
      gridLeadingRows m f ε s v (.word 87) := by
  change _ = v (gridGroupIndex 87)-gridMatrixScalar m f (ε*I^(2*m)) 87 0 s*v (gridGroupTarget 87)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 87=170 from rfl,show gridGroupTarget 87=86 from rfl,
    show gridGroupSource 87=43 from rfl,show sourceWord 43=[(3,false),(4,false),(0,true)] from rfl,
    show groupPowers 87=((0,0,1,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_87

theorem word_binding_88 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 91 =
      gridLeadingRows m f ε s v (.word 88) := by
  change _ = v (gridGroupIndex 88)-gridMatrixScalar m f (ε*I^(2*m)) 88 0 s*v (gridGroupTarget 88)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 88=340 from rfl,show gridGroupTarget 88=430 from rfl,
    show gridGroupSource 88=44 from rfl,show sourceWord 44=[(3,false),(4,true),(0,true)] from rfl,
    show groupPowers 88=((0,0,1,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_88

theorem word_binding_89 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 92 =
      gridLeadingRows m f ε s v (.word 89) := by
  change _ = v (gridGroupIndex 89)-gridMatrixScalar m f (ε*I^(2*m)) 89 0 s*v (gridGroupTarget 89)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 89=400 from rfl,show gridGroupTarget 89=442 from rfl,
    show gridGroupSource 89=44 from rfl,show sourceWord 44=[(3,false),(4,true),(0,true)] from rfl,
    show groupPowers 89=((0,0,-1,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_89

theorem word_binding_90 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 93 =
      gridLeadingRows m f ε s v (.word 90) := by
  change _ = v (gridGroupIndex 90)-gridMatrixScalar m f (ε*I^(2*m)) 90 0 s*v (gridGroupTarget 90)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 90=408 from rfl,show gridGroupTarget 90=450 from rfl,
    show gridGroupSource 90=44 from rfl,show sourceWord 44=[(3,false),(4,true),(0,true)] from rfl,
    show groupPowers 90=((0,0,1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_90

theorem word_binding_91 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 94 =
      gridLeadingRows m f ε s v (.word 91) := by
  change _ = v (gridGroupIndex 91)-gridMatrixScalar m f (ε*I^(2*m)) 91 0 s*v (gridGroupTarget 91)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 91=424 from rfl,show gridGroupTarget 91=340 from rfl,
    show gridGroupSource 91=44 from rfl,show sourceWord 44=[(3,false),(4,true),(0,true)] from rfl,
    show groupPowers 91=((0,0,-1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_91

theorem word_binding_92 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 95 =
      gridLeadingRows m f ε s v (.word 92) := by
  change _ = v (gridGroupIndex 92)-gridMatrixScalar m f (ε*I^(2*m)) 92 0 s*v (gridGroupTarget 92)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 92=417 from rfl,show gridGroupTarget 92=494 from rfl,
    show gridGroupSource 92=20 from rfl,show sourceWord 20=[(1,true),(4,true),(0,true)] from rfl,
    show groupPowers 92=((-1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart5,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_92

theorem word_binding_93 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 96 =
      gridLeadingRows m f ε s v (.word 93) := by
  change _ = v (gridGroupIndex 93)-gridMatrixScalar m f (ε*I^(2*m)) 93 0 s*v (gridGroupTarget 93)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 93=427 from rfl,show gridGroupTarget 93=474 from rfl,
    show gridGroupSource 93=20 from rfl,show sourceWord 20=[(1,true),(4,true),(0,true)] from rfl,
    show groupPowers 93=((-1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_93

theorem word_binding_94 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 97 =
      gridLeadingRows m f ε s v (.word 94) := by
  change _ = v (gridGroupIndex 94)-gridMatrixScalar m f (ε*I^(2*m)) 94 0 s*v (gridGroupTarget 94)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 94=428 from rfl,show gridGroupTarget 94=483 from rfl,
    show gridGroupSource 94=20 from rfl,show sourceWord 20=[(1,true),(4,true),(0,true)] from rfl,
    show groupPowers 94=((1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_94

theorem word_binding_95 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 98 =
      gridLeadingRows m f ε s v (.word 95) := by
  change _ = v (gridGroupIndex 95)-gridMatrixScalar m f (ε*I^(2*m)) 95 0 s*v (gridGroupTarget 95)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 95=432 from rfl,show gridGroupTarget 95=489 from rfl,
    show gridGroupSource 95=20 from rfl,show sourceWord 20=[(1,true),(4,true),(0,true)] from rfl,
    show groupPowers 95=((1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_95

theorem word_binding_96 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 99 =
      gridLeadingRows m f ε s v (.word 96) := by
  change _ = v (gridGroupIndex 96)-gridMatrixScalar m f (ε*I^(2*m)) 96 0 s*v (gridGroupTarget 96)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 96=444 from rfl,show gridGroupTarget 96=491 from rfl,
    show gridGroupSource 96=20 from rfl,show sourceWord 20=[(1,true),(4,true),(0,true)] from rfl,
    show groupPowers 96=((1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_96

theorem word_binding_97 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 100 =
      gridLeadingRows m f ε s v (.word 97) := by
  change _ = v (gridGroupIndex 97)-gridMatrixScalar m f (ε*I^(2*m)) 97 0 s*v (gridGroupTarget 97)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 97=240 from rfl,show gridGroupTarget 97=478 from rfl,
    show gridGroupSource 97=22 from rfl,show sourceWord 22=[(2,false),(0,false),(2,false)] from rfl,
    show groupPowers 97=((0,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_97

theorem word_binding_98 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 101 =
      gridLeadingRows m f ε s v (.word 98) := by
  change _ = v (gridGroupIndex 98)-gridMatrixScalar m f (ε*I^(2*m)) 98 0 s*v (gridGroupTarget 98)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 98=494 from rfl,show gridGroupTarget 98=495 from rfl,
    show gridGroupSource 98=25 from rfl,show sourceWord 25=[(2,false),(1,false),(0,true)] from rfl,
    show groupPowers 98=((1,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_98

theorem word_binding_99 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 102 =
      gridLeadingRows m f ε s v (.word 99) := by
  change _ = v (gridGroupIndex 99)-gridMatrixScalar m f (ε*I^(2*m)) 99 0 s*v (gridGroupTarget 99)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 99=81 from rfl,show gridGroupTarget 99=418 from rfl,
    show gridGroupSource 99=49 from rfl,show sourceWord 49=[(4,false),(2,true),(4,false)] from rfl,
    show groupPowers 99=((-1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_99

theorem word_binding_100 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 103 =
      gridLeadingRows m f ε s v (.word 100) := by
  change _ = v (gridGroupIndex 100)-gridMatrixScalar m f (ε*I^(2*m)) 100 0 s*v (gridGroupTarget 100)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 100=83 from rfl,show gridGroupTarget 100=414 from rfl,
    show gridGroupSource 100=49 from rfl,show sourceWord 49=[(4,false),(2,true),(4,false)] from rfl,
    show groupPowers 100=((-1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_100

theorem word_binding_101 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 104 =
      gridLeadingRows m f ε s v (.word 101) := by
  change _ = v (gridGroupIndex 101)-gridMatrixScalar m f (ε*I^(2*m)) 101 0 s*v (gridGroupTarget 101)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 101=30 from rfl,show gridGroupTarget 101=232 from rfl,
    show gridGroupSource 101=33 from rfl,show sourceWord 33=[(2,true),(1,true),(4,true)] from rfl,
    show groupPowers 101=((0,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_101

theorem word_binding_102 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 105 =
      gridLeadingRows m f ε s v (.word 102) := by
  change _ = v (gridGroupIndex 102)-gridMatrixScalar m f (ε*I^(2*m)) 102 0 s*v (gridGroupTarget 102)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 102=18 from rfl,show gridGroupTarget 102=269 from rfl,
    show gridGroupSource 102=28 from rfl,show sourceWord 28=[(2,true),(0,false),(1,true)] from rfl,
    show groupPowers 102=((1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_102

theorem word_binding_103 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 106 =
      gridLeadingRows m f ε s v (.word 103) := by
  change _ = v (gridGroupIndex 103)-gridMatrixScalar m f (ε*I^(2*m)) 103 0 s*v (gridGroupTarget 103)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 103=476 from rfl,show gridGroupTarget 103=490 from rfl,
    show gridGroupSource 103=42 from rfl,show sourceWord 42=[(3,false),(2,true),(0,true)] from rfl,
    show groupPowers 103=((0,0,1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_103

theorem word_binding_104 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 107 =
      gridLeadingRows m f ε s v (.word 104) := by
  change _ = v (gridGroupIndex 104)-gridMatrixScalar m f (ε*I^(2*m)) 104 0 s*v (gridGroupTarget 104)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 104=51 from rfl,show gridGroupTarget 104=13 from rfl,
    show gridGroupSource 104=37 from rfl,show sourceWord 37=[(3,false),(0,true),(4,false)] from rfl,
    show groupPowers 104=((0,2,1,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_104

theorem word_binding_105 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 108 =
      gridLeadingRows m f ε s v (.word 105) := by
  change _ = v (gridGroupIndex 105)-gridMatrixScalar m f (ε*I^(2*m)) 105 0 s*v (gridGroupTarget 105)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 105=89 from rfl,show gridGroupTarget 105=51 from rfl,
    show gridGroupSource 105=37 from rfl,show sourceWord 37=[(3,false),(0,true),(4,false)] from rfl,
    show groupPowers 105=((0,-2,-1,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_105

theorem word_binding_106 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 109 =
      gridLeadingRows m f ε s v (.word 106) := by
  change _ = v (gridGroupIndex 106)-gridMatrixScalar m f (ε*I^(2*m)) 106 0 s*v (gridGroupTarget 106)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 106=195 from rfl,show gridGroupTarget 106=268 from rfl,
    show gridGroupSource 106=27 from rfl,show sourceWord 27=[(2,true)] from rfl,
    show groupPowers 106=((-1,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_106

theorem word_binding_107 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 110 =
      gridLeadingRows m f ε s v (.word 107) := by
  change _ = v (gridGroupIndex 107)-gridMatrixScalar m f (ε*I^(2*m)) 107 0 s*v (gridGroupTarget 107)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 107=255 from rfl,show gridGroupTarget 107=10 from rfl,
    show gridGroupSource 107=36 from rfl,show sourceWord 36=[(3,false),(0,true),(0,true)] from rfl,
    show groupPowers 107=((-1,2,1,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_107

theorem word_binding_108 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 111 =
      gridLeadingRows m f ε s v (.word 108) := by
  change _ = v (gridGroupIndex 108)-gridMatrixScalar m f (ε*I^(2*m)) 108 0 s*v (gridGroupTarget 108)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 108=1 from rfl,show gridGroupTarget 108=0 from rfl,
    show gridGroupSource 108=38 from rfl,show sourceWord 38=[(3,false),(1,true)] from rfl,
    show groupPowers 108=((-1,-2,-1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart6,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_108

theorem word_binding_109 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 112 =
      gridLeadingRows m f ε s v (.word 109) := by
  change _ = v (gridGroupIndex 109)-gridMatrixScalar m f (ε*I^(2*m)) 109 0 s*v (gridGroupTarget 109)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 109=2 from rfl,show gridGroupTarget 109=255 from rfl,
    show gridGroupSource 109=38 from rfl,show sourceWord 38=[(3,false),(1,true)] from rfl,
    show groupPowers 109=((1,-2,-1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_109

theorem word_binding_110 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 113 =
      gridLeadingRows m f ε s v (.word 110) := by
  change _ = v (gridGroupIndex 110)-gridMatrixScalar m f (ε*I^(2*m)) 110 0 s*v (gridGroupTarget 110)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 110=3 from rfl,show gridGroupTarget 110=0 from rfl,
    show gridGroupSource 110=38 from rfl,show sourceWord 38=[(3,false),(1,true)] from rfl,
    show groupPowers 110=((-1,0,-1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_110

theorem word_binding_111 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 114 =
      gridLeadingRows m f ε s v (.word 111) := by
  change _ = v (gridGroupIndex 111)-gridMatrixScalar m f (ε*I^(2*m)) 111 0 s*v (gridGroupTarget 111)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 111=5 from rfl,show gridGroupTarget 111=0 from rfl,
    show gridGroupSource 111=38 from rfl,show sourceWord 38=[(3,false),(1,true)] from rfl,
    show groupPowers 111=((-1,-2,-1,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_111

theorem word_binding_112 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 115 =
      gridLeadingRows m f ε s v (.word 112) := by
  change _ = v (gridGroupIndex 112)-gridMatrixScalar m f (ε*I^(2*m)) 112 0 s*v (gridGroupTarget 112)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 112=6 from rfl,show gridGroupTarget 112=255 from rfl,
    show gridGroupSource 112=38 from rfl,show sourceWord 38=[(3,false),(1,true)] from rfl,
    show groupPowers 112=((1,0,-1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_112

theorem word_binding_113 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 116 =
      gridLeadingRows m f ε s v (.word 113) := by
  change _ = v (gridGroupIndex 113)-gridMatrixScalar m f (ε*I^(2*m)) 113 0 s*v (gridGroupTarget 113)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 113=25 from rfl,show gridGroupTarget 113=204 from rfl,
    show gridGroupSource 113=38 from rfl,show sourceWord 38=[(3,false),(1,true)] from rfl,
    show groupPowers 113=((-1,-2,-1,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_113

theorem word_binding_114 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 117 =
      gridLeadingRows m f ε s v (.word 114) := by
  change _ = v (gridGroupIndex 114)-gridMatrixScalar m f (ε*I^(2*m)) 114 0 s*v (gridGroupTarget 114)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 114=34 from rfl,show gridGroupTarget 114=285 from rfl,
    show gridGroupSource 114=38 from rfl,show sourceWord 38=[(3,false),(1,true)] from rfl,
    show groupPowers 114=((1,-2,1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_114

theorem word_binding_115 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 118 =
      gridLeadingRows m f ε s v (.word 115) := by
  change _ = v (gridGroupIndex 115)-gridMatrixScalar m f (ε*I^(2*m)) 115 0 s*v (gridGroupTarget 115)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 115=50 from rfl,show gridGroupTarget 115=357 from rfl,
    show gridGroupSource 115=38 from rfl,show sourceWord 38=[(3,false),(1,true)] from rfl,
    show groupPowers 115=((1,-2,-1,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_115

theorem word_binding_116 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 119 =
      gridLeadingRows m f ε s v (.word 116) := by
  change _ = v (gridGroupIndex 116)-gridMatrixScalar m f (ε*I^(2*m)) 116 0 s*v (gridGroupTarget 116)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 116=150 from rfl,show gridGroupTarget 116=459 from rfl,
    show gridGroupSource 116=38 from rfl,show sourceWord 38=[(3,false),(1,true)] from rfl,
    show groupPowers 116=((1,0,-1,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_116

theorem word_binding_117 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 120 =
      gridLeadingRows m f ε s v (.word 117) := by
  change _ = v (gridGroupIndex 117)-gridMatrixScalar m f (ε*I^(2*m)) 117 0 s*v (gridGroupTarget 117)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 117=153 from rfl,show gridGroupTarget 117=460 from rfl,
    show gridGroupSource 117=38 from rfl,show sourceWord 38=[(3,false),(1,true)] from rfl,
    show groupPowers 117=((-1,2,1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_117

theorem word_binding_118 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 121 =
      gridLeadingRows m f ε s v (.word 118) := by
  change _ = v (gridGroupIndex 118)-gridMatrixScalar m f (ε*I^(2*m)) 118 0 s*v (gridGroupTarget 118)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 118=225 from rfl,show gridGroupTarget 118=476 from rfl,
    show gridGroupSource 118=38 from rfl,show sourceWord 38=[(3,false),(1,true)] from rfl,
    show groupPowers 118=((-1,2,-1,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_118

theorem word_binding_119 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 122 =
      gridLeadingRows m f ε s v (.word 119) := by
  change _ = v (gridGroupIndex 119)-gridMatrixScalar m f (ε*I^(2*m)) 119 0 s*v (gridGroupTarget 119)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 119=306 from rfl,show gridGroupTarget 119=485 from rfl,
    show gridGroupSource 119=38 from rfl,show sourceWord 38=[(3,false),(1,true)] from rfl,
    show groupPowers 119=((1,2,1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_119

theorem word_binding_120 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 123 =
      gridLeadingRows m f ε s v (.word 120) := by
  change _ = v (gridGroupIndex 120)-gridMatrixScalar m f (ε*I^(2*m)) 120 0 s*v (gridGroupTarget 120)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 120=425 from rfl,show gridGroupTarget 120=492 from rfl,
    show gridGroupSource 120=38 from rfl,show sourceWord 38=[(3,false),(1,true)] from rfl,
    show groupPowers 120=((-1,-2,1,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_120

theorem word_binding_121 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 124 =
      gridLeadingRows m f ε s v (.word 121) := by
  change _ = v (gridGroupIndex 121)-gridMatrixScalar m f (ε*I^(2*m)) 121 0 s*v (gridGroupTarget 121)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 121=7 from rfl,show gridGroupTarget 121=105 from rfl,
    show gridGroupSource 121=2 from rfl,show sourceWord 2=[(0,false),(1,true),(1,true)] from rfl,
    show groupPowers 121=((0,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_121

theorem word_binding_122 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 125 =
      gridLeadingRows m f ε s v (.word 122) := by
  change _ = v (gridGroupIndex 122)-gridMatrixScalar m f (ε*I^(2*m)) 122 0 s*v (gridGroupTarget 122)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 122=8 from rfl,show gridGroupTarget 122=390 from rfl,
    show gridGroupSource 122=2 from rfl,show sourceWord 2=[(0,false),(1,true),(1,true)] from rfl,
    show groupPowers 122=((0,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_122

theorem word_binding_123 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 126 =
      gridLeadingRows m f ε s v (.word 123) := by
  change _ = v (gridGroupIndex 123)-gridMatrixScalar m f (ε*I^(2*m)) 123 0 s*v (gridGroupTarget 123)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 123=120 from rfl,show gridGroupTarget 123=502 from rfl,
    show gridGroupSource 123=2 from rfl,show sourceWord 2=[(0,false),(1,true),(1,true)] from rfl,
    show groupPowers 123=((0,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_123

theorem word_binding_124 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 127 =
      gridLeadingRows m f ε s v (.word 124) := by
  change _ = v (gridGroupIndex 124)-gridMatrixScalar m f (ε*I^(2*m)) 124 0 s*v (gridGroupTarget 124)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 124=33 from rfl,show gridGroupTarget 124=425 from rfl,
    show gridGroupSource 124=23 from rfl,show sourceWord 23=[(2,false),(0,false),(3,false)] from rfl,
    show groupPowers 124=((0,2,-1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart7,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_124

theorem word_binding_125 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 128 =
      gridLeadingRows m f ε s v (.word 125) := by
  change _ = v (gridGroupIndex 125)-gridMatrixScalar m f (ε*I^(2*m)) 125 0 s*v (gridGroupTarget 125)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 125=35 from rfl,show gridGroupTarget 125=459 from rfl,
    show gridGroupSource 125=23 from rfl,show sourceWord 23=[(2,false),(0,false),(3,false)] from rfl,
    show groupPowers 125=((0,-2,-1,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_125

theorem word_binding_126 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 129 =
      gridLeadingRows m f ε s v (.word 126) := by
  change _ = v (gridGroupIndex 126)-gridMatrixScalar m f (ε*I^(2*m)) 126 0 s*v (gridGroupTarget 126)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 126=85 from rfl,show gridGroupTarget 126=477 from rfl,
    show gridGroupSource 126=23 from rfl,show sourceWord 23=[(2,false),(0,false),(3,false)] from rfl,
    show groupPowers 126=((0,-2,1,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_126

theorem word_binding_127 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 130 =
      gridLeadingRows m f ε s v (.word 127) := by
  change _ = v (gridGroupIndex 127)-gridMatrixScalar m f (ε*I^(2*m)) 127 0 s*v (gridGroupTarget 127)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 127=180 from rfl,show gridGroupTarget 127=485 from rfl,
    show gridGroupSource 127=6 from rfl,show sourceWord 6=[(0,true),(0,true),(2,false)] from rfl,
    show groupPowers 127=((1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_127

theorem word_binding_128 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 131 =
      gridLeadingRows m f ε s v (.word 128) := by
  change _ = v (gridGroupIndex 128)-gridMatrixScalar m f (ε*I^(2*m)) 128 0 s*v (gridGroupTarget 128)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 128=220 from rfl,show gridGroupTarget 128=489 from rfl,
    show gridGroupSource 128=6 from rfl,show sourceWord 6=[(0,true),(0,true),(2,false)] from rfl,
    show groupPowers 128=((1,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_128

theorem word_binding_129 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 132 =
      gridLeadingRows m f ε s v (.word 129) := by
  change _ = v (gridGroupIndex 129)-gridMatrixScalar m f (ε*I^(2*m)) 129 0 s*v (gridGroupTarget 129)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 129=245 from rfl,show gridGroupTarget 129=498 from rfl,
    show gridGroupSource 129=6 from rfl,show sourceWord 6=[(0,true),(0,true),(2,false)] from rfl,
    show groupPowers 129=((-1,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_129

theorem word_binding_130 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 133 =
      gridLeadingRows m f ε s v (.word 130) := by
  change _ = v (gridGroupIndex 130)-gridMatrixScalar m f (ε*I^(2*m)) 130 0 s*v (gridGroupTarget 130)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 130=252 from rfl,show gridGroupTarget 130=505 from rfl,
    show gridGroupSource 130=6 from rfl,show sourceWord 6=[(0,true),(0,true),(2,false)] from rfl,
    show groupPowers 130=((1,2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_130

theorem word_binding_131 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 134 =
      gridLeadingRows m f ε s v (.word 131) := by
  change _ = v (gridGroupIndex 131)-gridMatrixScalar m f (ε*I^(2*m)) 131 0 s*v (gridGroupTarget 131)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 131=273 from rfl,show gridGroupTarget 131=330 from rfl,
    show gridGroupSource 131=6 from rfl,show sourceWord 6=[(0,true),(0,true),(2,false)] from rfl,
    show groupPowers 131=((-1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_131

theorem word_binding_132 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 135 =
      gridLeadingRows m f ε s v (.word 132) := by
  change _ = v (gridGroupIndex 132)-gridMatrixScalar m f (ε*I^(2*m)) 132 0 s*v (gridGroupTarget 132)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 132=275 from rfl,show gridGroupTarget 132=390 from rfl,
    show gridGroupSource 132=6 from rfl,show sourceWord 6=[(0,true),(0,true),(2,false)] from rfl,
    show groupPowers 132=((-1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_132

theorem word_binding_133 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 136 =
      gridLeadingRows m f ε s v (.word 133) := by
  change _ = v (gridGroupIndex 133)-gridMatrixScalar m f (ε*I^(2*m)) 133 0 s*v (gridGroupTarget 133)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 133=288 from rfl,show gridGroupTarget 133=455 from rfl,
    show gridGroupSource 133=6 from rfl,show sourceWord 6=[(0,true),(0,true),(2,false)] from rfl,
    show groupPowers 133=((1,2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_133

theorem word_binding_134 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 137 =
      gridLeadingRows m f ε s v (.word 134) := by
  change _ = v (gridGroupIndex 134)-gridMatrixScalar m f (ε*I^(2*m)) 134 0 s*v (gridGroupTarget 134)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 134=295 from rfl,show gridGroupTarget 134=462 from rfl,
    show gridGroupSource 134=6 from rfl,show sourceWord 6=[(0,true),(0,true),(2,false)] from rfl,
    show groupPowers 134=((-1,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_134

theorem word_binding_135 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 138 =
      gridLeadingRows m f ε s v (.word 135) := by
  change _ = v (gridGroupIndex 135)-gridMatrixScalar m f (ε*I^(2*m)) 135 0 s*v (gridGroupTarget 135)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 135=300 from rfl,show gridGroupTarget 135=465 from rfl,
    show gridGroupSource 135=6 from rfl,show sourceWord 6=[(0,true),(0,true),(2,false)] from rfl,
    show groupPowers 135=((1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_135

theorem word_binding_136 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 139 =
      gridLeadingRows m f ε s v (.word 136) := by
  change _ = v (gridGroupIndex 136)-gridMatrixScalar m f (ε*I^(2*m)) 136 0 s*v (gridGroupTarget 136)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 136=320 from rfl,show gridGroupTarget 136=471 from rfl,
    show gridGroupSource 136=6 from rfl,show sourceWord 6=[(0,true),(0,true),(2,false)] from rfl,
    show groupPowers 136=((1,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_136

theorem word_binding_137 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 140 =
      gridLeadingRows m f ε s v (.word 137) := by
  change _ = v (gridGroupIndex 137)-gridMatrixScalar m f (ε*I^(2*m)) 137 0 s*v (gridGroupTarget 137)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 137=345 from rfl,show gridGroupTarget 137=474 from rfl,
    show gridGroupSource 137=6 from rfl,show sourceWord 6=[(0,true),(0,true),(2,false)] from rfl,
    show groupPowers 137=((-1,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_137

theorem word_binding_138 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 141 =
      gridLeadingRows m f ε s v (.word 138) := by
  change _ = v (gridGroupIndex 138)-gridMatrixScalar m f (ε*I^(2*m)) 138 0 s*v (gridGroupTarget 138)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 138=190 from rfl,show gridGroupTarget 138=39 from rfl,
    show gridGroupSource 138=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 138=((1,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_138

theorem word_binding_139 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 142 =
      gridLeadingRows m f ε s v (.word 139) := by
  change _ = v (gridGroupIndex 139)-gridMatrixScalar m f (ε*I^(2*m)) 139 0 s*v (gridGroupTarget 139)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 139=215 from rfl,show gridGroupTarget 139=48 from rfl,
    show gridGroupSource 139=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 139=((-1,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_139

theorem word_binding_140 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 143 =
      gridLeadingRows m f ε s v (.word 140) := by
  change _ = v (gridGroupIndex 140)-gridMatrixScalar m f (ε*I^(2*m)) 140 0 s*v (gridGroupTarget 140)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 140=222 from rfl,show gridGroupTarget 140=55 from rfl,
    show gridGroupSource 140=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 140=((1,2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart8,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_140

theorem word_binding_141 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 144 =
      gridLeadingRows m f ε s v (.word 141) := by
  change _ = v (gridGroupIndex 141)-gridMatrixScalar m f (ε*I^(2*m)) 141 0 s*v (gridGroupTarget 141)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 141=230 from rfl,show gridGroupTarget 141=75 from rfl,
    show gridGroupSource 141=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 141=((1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_141

theorem word_binding_142 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 145 =
      gridLeadingRows m f ε s v (.word 142) := by
  change _ = v (gridGroupIndex 142)-gridMatrixScalar m f (ε*I^(2*m)) 142 0 s*v (gridGroupTarget 142)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 142=231 from rfl,show gridGroupTarget 142=80 from rfl,
    show gridGroupSource 142=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 142=((-1,2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_142

theorem word_binding_143 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 146 =
      gridLeadingRows m f ε s v (.word 143) := by
  change _ = v (gridGroupIndex 143)-gridMatrixScalar m f (ε*I^(2*m)) 143 0 s*v (gridGroupTarget 143)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 143=234 from rfl,show gridGroupTarget 143=105 from rfl,
    show gridGroupSource 143=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 143=((1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_143

theorem word_binding_144 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 147 =
      gridLeadingRows m f ε s v (.word 144) := by
  change _ = v (gridGroupIndex 144)-gridMatrixScalar m f (ε*I^(2*m)) 144 0 s*v (gridGroupTarget 144)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 144=237 from rfl,show gridGroupTarget 144=180 from rfl,
    show gridGroupSource 144=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 144=((-1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_144

theorem word_binding_145 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 148 =
      gridLeadingRows m f ε s v (.word 145) := by
  change _ = v (gridGroupIndex 145)-gridMatrixScalar m f (ε*I^(2*m)) 145 0 s*v (gridGroupTarget 145)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 145=238 from rfl,show gridGroupTarget 145=255 from rfl,
    show gridGroupSource 145=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 145=((1,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_145

theorem word_binding_146 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 149 =
      gridLeadingRows m f ε s v (.word 146) := by
  change _ = v (gridGroupIndex 146)-gridMatrixScalar m f (ε*I^(2*m)) 146 0 s*v (gridGroupTarget 146)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 146=239 from rfl,show gridGroupTarget 146=480 from rfl,
    show gridGroupSource 146=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 146=((-1,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_146

theorem word_binding_147 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 150 =
      gridLeadingRows m f ε s v (.word 147) := by
  change _ = v (gridGroupIndex 147)-gridMatrixScalar m f (ε*I^(2*m)) 147 0 s*v (gridGroupTarget 147)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 147=241 from rfl,show gridGroupTarget 147=90 from rfl,
    show gridGroupSource 147=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 147=((-1,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_147

theorem word_binding_148 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 151 =
      gridLeadingRows m f ε s v (.word 148) := by
  change _ = v (gridGroupIndex 148)-gridMatrixScalar m f (ε*I^(2*m)) 148 0 s*v (gridGroupTarget 148)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 148=242 from rfl,show gridGroupTarget 148=315 from rfl,
    show gridGroupSource 148=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 148=((1,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_148

theorem word_binding_149 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 152 =
      gridLeadingRows m f ε s v (.word 149) := by
  change _ = v (gridGroupIndex 149)-gridMatrixScalar m f (ε*I^(2*m)) 149 0 s*v (gridGroupTarget 149)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 149=243 from rfl,show gridGroupTarget 149=390 from rfl,
    show gridGroupSource 149=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 149=((-1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_149

theorem word_binding_150 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 153 =
      gridLeadingRows m f ε s v (.word 150) := by
  change _ = v (gridGroupIndex 150)-gridMatrixScalar m f (ε*I^(2*m)) 150 0 s*v (gridGroupTarget 150)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 150=246 from rfl,show gridGroupTarget 150=465 from rfl,
    show gridGroupSource 150=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 150=((1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_150

theorem word_binding_151 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 154 =
      gridLeadingRows m f ε s v (.word 151) := by
  change _ = v (gridGroupIndex 151)-gridMatrixScalar m f (ε*I^(2*m)) 151 0 s*v (gridGroupTarget 151)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 151=249 from rfl,show gridGroupTarget 151=490 from rfl,
    show gridGroupSource 151=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 151=((-1,2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_151

theorem word_binding_152 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 155 =
      gridLeadingRows m f ε s v (.word 152) := by
  change _ = v (gridGroupIndex 152)-gridMatrixScalar m f (ε*I^(2*m)) 152 0 s*v (gridGroupTarget 152)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 152=250 from rfl,show gridGroupTarget 152=495 from rfl,
    show gridGroupSource 152=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 152=((1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_152

theorem word_binding_153 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 156 =
      gridLeadingRows m f ε s v (.word 153) := by
  change _ = v (gridGroupIndex 153)-gridMatrixScalar m f (ε*I^(2*m)) 153 0 s*v (gridGroupTarget 153)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 153=258 from rfl,show gridGroupTarget 153=5 from rfl,
    show gridGroupSource 153=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 153=((1,2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_153

theorem word_binding_154 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 157 =
      gridLeadingRows m f ε s v (.word 154) := by
  change _ = v (gridGroupIndex 154)-gridMatrixScalar m f (ε*I^(2*m)) 154 0 s*v (gridGroupTarget 154)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 154=290 from rfl,show gridGroupTarget 154=21 from rfl,
    show gridGroupSource 154=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 154=((1,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_154

theorem word_binding_155 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 158 =
      gridLeadingRows m f ε s v (.word 155) := by
  change _ = v (gridGroupIndex 155)-gridMatrixScalar m f (ε*I^(2*m)) 155 0 s*v (gridGroupTarget 155)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 155=330 from rfl,show gridGroupTarget 155=25 from rfl,
    show gridGroupSource 155=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 155=((1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_155

theorem word_binding_156 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 159 =
      gridLeadingRows m f ε s v (.word 156) := by
  change _ = v (gridGroupIndex 156)-gridMatrixScalar m f (ε*I^(2*m)) 156 0 s*v (gridGroupTarget 156)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 156=390 from rfl,show gridGroupTarget 156=27 from rfl,
    show gridGroupSource 156=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 156=((1,0,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart9,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_156

theorem word_binding_157 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 160 =
      gridLeadingRows m f ε s v (.word 157) := by
  change _ = v (gridGroupIndex 157)-gridMatrixScalar m f (ε*I^(2*m)) 157 0 s*v (gridGroupTarget 157)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 157=465 from rfl,show gridGroupTarget 157=28 from rfl,
    show gridGroupSource 157=12 from rfl,show sourceWord 12=[(1,false),(2,false)] from rfl,
    show groupPowers 157=((-1,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_157

theorem word_binding_158 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 161 =
      gridLeadingRows m f ε s v (.word 158) := by
  change _ = v (gridGroupIndex 158)-gridMatrixScalar m f (ε*I^(2*m)) 158 0 s*v (gridGroupTarget 158)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 158=14 from rfl,show gridGroupTarget 158=479 from rfl,
    show gridGroupSource 158=21 from rfl,show sourceWord 21=[(2,false),(0,false),(1,true)] from rfl,
    show groupPowers 158=((1,0,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_158

theorem word_binding_159 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 162 =
      gridLeadingRows m f ε s v (.word 159) := by
  change _ = v (gridGroupIndex 159)-gridMatrixScalar m f (ε*I^(2*m)) 159 0 s*v (gridGroupTarget 159)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 159=68 from rfl,show gridGroupTarget 159=110 from rfl,
    show gridGroupSource 159=40 from rfl,show sourceWord 40=[(3,false),(1,true),(4,false)] from rfl,
    show groupPowers 159=((0,0,1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_159

theorem word_binding_160 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 163 =
      gridLeadingRows m f ε s v (.word 160) := by
  change _ = v (gridGroupIndex 160)-gridMatrixScalar m f (ε*I^(2*m)) 160 0 s*v (gridGroupTarget 160)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 160=70 from rfl,show gridGroupTarget 160=282 from rfl,
    show gridGroupSource 160=9 from rfl,show sourceWord 9=[(0,true),(2,true),(4,false)] from rfl,
    show groupPowers 160=((0,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_160

theorem word_binding_161 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 164 =
      gridLeadingRows m f ε s v (.word 161) := by
  change _ = v (gridGroupIndex 161)-gridMatrixScalar m f (ε*I^(2*m)) 161 0 s*v (gridGroupTarget 161)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 161=479 from rfl,show gridGroupTarget 161=210 from rfl,
    show gridGroupSource 161=5 from rfl,show sourceWord 5=[(0,false),(2,true),(0,true)] from rfl,
    show groupPowers 161=((-1,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_161

theorem word_binding_162 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 165 =
      gridLeadingRows m f ε s v (.word 162) := by
  change _ = v (gridGroupIndex 162)-gridMatrixScalar m f (ε*I^(2*m)) 162 0 s*v (gridGroupTarget 162)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 162=29 from rfl,show gridGroupTarget 162=180 from rfl,
    show gridGroupSource 162=8 from rfl,show sourceWord 8=[(0,true),(2,true),(1,true)] from rfl,
    show groupPowers 162=((-1,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_162

theorem word_binding_163 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 166 =
      gridLeadingRows m f ε s v (.word 163) := by
  change _ = v (gridGroupIndex 163)-gridMatrixScalar m f (ε*I^(2*m)) 163 0 s*v (gridGroupTarget 163)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 163=31 from rfl,show gridGroupTarget 163=300 from rfl,
    show gridGroupSource 163=8 from rfl,show sourceWord 8=[(0,true),(2,true),(1,true)] from rfl,
    show groupPowers 163=((-1,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_163

theorem word_binding_164 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 167 =
      gridLeadingRows m f ε s v (.word 164) := by
  change _ = v (gridGroupIndex 164)-gridMatrixScalar m f (ε*I^(2*m)) 164 0 s*v (gridGroupTarget 164)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 164=259 from rfl,show gridGroupTarget 164=40 from rfl,
    show gridGroupSource 164=3 from rfl,show sourceWord 3=[(0,false),(1,true),(2,false)] from rfl,
    show groupPowers 164=((-1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_164

theorem word_binding_165 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 168 =
      gridLeadingRows m f ε s v (.word 165) := by
  change _ = v (gridGroupIndex 165)-gridMatrixScalar m f (ε*I^(2*m)) 165 0 s*v (gridGroupTarget 165)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 165=135 from rfl,show gridGroupTarget 165=263 from rfl,
    show gridGroupSource 165=30 from rfl,show sourceWord 30=[(2,true),(1,false),(2,false)] from rfl,
    show groupPowers 165=((0,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_165

theorem word_binding_166 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 169 =
      gridLeadingRows m f ε s v (.word 166) := by
  change _ = v (gridGroupIndex 166)-gridMatrixScalar m f (ε*I^(2*m)) 166 0 s*v (gridGroupTarget 166)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 166=247 from rfl,show gridGroupTarget 166=375 from rfl,
    show gridGroupSource 166=30 from rfl,show sourceWord 30=[(2,true),(1,false),(2,false)] from rfl,
    show groupPowers 166=((0,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_166

theorem word_binding_167 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 170 =
      gridLeadingRows m f ε s v (.word 167) := by
  change _ = v (gridGroupIndex 167)-gridMatrixScalar m f (ε*I^(2*m)) 167 0 s*v (gridGroupTarget 167)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 167=248 from rfl,show gridGroupTarget 167=150 from rfl,
    show gridGroupSource 167=30 from rfl,show sourceWord 30=[(2,true),(1,false),(2,false)] from rfl,
    show groupPowers 167=((0,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_167

theorem word_binding_168 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 171 =
      gridLeadingRows m f ε s v (.word 168) := by
  change _ = v (gridGroupIndex 168)-gridMatrixScalar m f (ε*I^(2*m)) 168 0 s*v (gridGroupTarget 168)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 168=300 from rfl,show gridGroupTarget 168=496 from rfl,
    show gridGroupSource 168=1 from rfl,show sourceWord 1=[(0,false),(1,true),(0,true)] from rfl,
    show groupPowers 168=((0,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_168

theorem word_binding_169 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 172 =
      gridLeadingRows m f ε s v (.word 169) := by
  change _ = v (gridGroupIndex 169)-gridMatrixScalar m f (ε*I^(2*m)) 169 0 s*v (gridGroupTarget 169)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 169=500 from rfl,show gridGroupTarget 169=504 from rfl,
    show gridGroupSource 169=1 from rfl,show sourceWord 1=[(0,false),(1,true),(0,true)] from rfl,
    show groupPowers 169=((0,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_169

theorem word_binding_170 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 173 =
      gridLeadingRows m f ε s v (.word 170) := by
  change _ = v (gridGroupIndex 170)-gridMatrixScalar m f (ε*I^(2*m)) 170 0 s*v (gridGroupTarget 170)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 170=120 from rfl,show gridGroupTarget 170=503 from rfl,
    show gridGroupSource 170=18 from rfl,show sourceWord 18=[(1,true),(1,true),(4,false)] from rfl,
    show groupPowers 170=((1,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_170

theorem word_binding_171 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 174 =
      gridLeadingRows m f ε s v (.word 171) := by
  change _ = v (gridGroupIndex 171)-gridMatrixScalar m f (ε*I^(2*m)) 171 0 s*v (gridGroupTarget 171)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 171=228 from rfl,show gridGroupTarget 171=440 from rfl,
    show gridGroupSource 171=46 from rfl,show sourceWord 46=[(4,false),(1,false),(2,false)] from rfl,
    show groupPowers 171=((0,2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_171

theorem word_binding_172 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 175 =
      gridLeadingRows m f ε s v (.word 172) := by
  change _ = v (gridGroupIndex 172)-gridMatrixScalar m f (ε*I^(2*m)) 172 0 s*v (gridGroupTarget 172)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 172=233 from rfl,show gridGroupTarget 172=315 from rfl,
    show gridGroupSource 172=46 from rfl,show sourceWord 46=[(4,false),(1,false),(2,false)] from rfl,
    show groupPowers 172=((0,-2,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart10,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_172

theorem word_binding_173 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 176 =
      gridLeadingRows m f ε s v (.word 173) := by
  change _ = v (gridGroupIndex 173)-gridMatrixScalar m f (ε*I^(2*m)) 173 0 s*v (gridGroupTarget 173)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 173=30 from rfl,show gridGroupTarget 173=244 from rfl,
    show gridGroupSource 173=32 from rfl,show sourceWord 32=[(2,true),(1,true),(4,false)] from rfl,
    show groupPowers 173=((0,2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart11,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_173

theorem word_binding_174 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 177 =
      gridLeadingRows m f ε s v (.word 174) := by
  change _ = v (gridGroupIndex 174)-gridMatrixScalar m f (ε*I^(2*m)) 174 0 s*v (gridGroupTarget 174)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 174=94 from rfl,show gridGroupTarget 174=468 from rfl,
    show gridGroupSource 174=24 from rfl,show sourceWord 24=[(2,false),(0,false),(4,false)] from rfl,
    show groupPowers 174=((0,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart11,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_174

theorem word_binding_175 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 178 =
      gridLeadingRows m f ε s v (.word 175) := by
  change _ = v (gridGroupIndex 175)-gridMatrixScalar m f (ε*I^(2*m)) 175 0 s*v (gridGroupTarget 175)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 175=11 from rfl,show gridGroupTarget 175=200 from rfl,
    show gridGroupSource 175=31 from rfl,show sourceWord 31=[(2,true),(1,true),(1,true)] from rfl,
    show groupPowers 175=((-1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart11,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_175

theorem word_binding_176 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 179 =
      gridLeadingRows m f ε s v (.word 176) := by
  change _ = v (gridGroupIndex 176)-gridMatrixScalar m f (ε*I^(2*m)) 176 0 s*v (gridGroupTarget 176)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 176=505 from rfl,show gridGroupTarget 176=507 from rfl,
    show gridGroupSource 176=15 from rfl,show sourceWord 15=[(1,true),(1,true),(0,true)] from rfl,
    show groupPowers 176=((0,-2,0,2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart11,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_176

theorem word_binding_177 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 180 =
      gridLeadingRows m f ε s v (.word 177) := by
  change _ = v (gridGroupIndex 177)-gridMatrixScalar m f (ε*I^(2*m)) 177 0 s*v (gridGroupTarget 177)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 177=254 from rfl,show gridGroupTarget 177=0 from rfl,
    show gridGroupSource 177=39 from rfl,show sourceWord 39=[(3,false),(1,true),(2,false)] from rfl,
    show groupPowers 177=((0,-2,-1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart11,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_177

theorem word_binding_178 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 181 =
      gridLeadingRows m f ε s v (.word 178) := by
  change _ = v (gridGroupIndex 178)-gridMatrixScalar m f (ε*I^(2*m)) 178 0 s*v (gridGroupTarget 178)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 178=256 from rfl,show gridGroupTarget 178=0 from rfl,
    show gridGroupSource 178=39 from rfl,show sourceWord 39=[(3,false),(1,true),(2,false)] from rfl,
    show groupPowers 178=((0,-2,-1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart11,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_178

theorem word_binding_179 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 182 =
      gridLeadingRows m f ε s v (.word 179) := by
  change _ = v (gridGroupIndex 179)-gridMatrixScalar m f (ε*I^(2*m)) 179 0 s*v (gridGroupTarget 179)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 179=249 from rfl,show gridGroupTarget 179=506 from rfl,
    show gridGroupSource 179=17 from rfl,show sourceWord 17=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 179=((-1,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart11,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_179

theorem word_binding_180 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 183 =
      gridLeadingRows m f ε s v (.word 180) := by
  change _ = v (gridGroupIndex 180)-gridMatrixScalar m f (ε*I^(2*m)) 180 0 s*v (gridGroupTarget 180)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 180=257 from rfl,show gridGroupTarget 180=12 from rfl,
    show gridGroupSource 180=17 from rfl,show sourceWord 17=[(1,true),(1,true),(2,false)] from rfl,
    show groupPowers 180=((-1,-2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart11,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_180

theorem word_binding_181 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 184 =
      gridLeadingRows m f ε s v (.word 181) := by
  change _ = v (gridGroupIndex 181)-gridMatrixScalar m f (ε*I^(2*m)) 181 0 s*v (gridGroupTarget 181)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 181=508 from rfl,show gridGroupTarget 181=255 from rfl,
    show gridGroupSource 181=7 from rfl,show sourceWord 7=[(0,true),(1,false),(3,false)] from rfl,
    show groupPowers 181=((1,-2,-1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart11,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_181

theorem word_binding_182 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 185 =
      gridLeadingRows m f ε s v (.word 182) := by
  change _ = v (gridGroupIndex 182)-gridMatrixScalar m f (ε*I^(2*m)) 182 0 s*v (gridGroupTarget 182)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 182=509 from rfl,show gridGroupTarget 182=0 from rfl,
    show gridGroupSource 182=7 from rfl,show sourceWord 7=[(0,true),(1,false),(3,false)] from rfl,
    show groupPowers 182=((-1,-2,-1,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart11,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_182

theorem word_binding_183 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 186 =
      gridLeadingRows m f ε s v (.word 183) := by
  change _ = v (gridGroupIndex 183)-gridMatrixScalar m f (ε*I^(2*m)) 183 0 s*v (gridGroupTarget 183)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 183=251 from rfl,show gridGroupTarget 183=470 from rfl,
    show gridGroupSource 183=11 from rfl,show sourceWord 11=[(1,false),(1,false),(2,false)] from rfl,
    show groupPowers 183=((-1,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart11,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_183

theorem word_binding_184 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 187 =
      gridLeadingRows m f ε s v (.word 184) := by
  change _ = v (gridGroupIndex 184)-gridMatrixScalar m f (ε*I^(2*m)) 184 0 s*v (gridGroupTarget 184)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 184=4 from rfl,show gridGroupTarget 184=20 from rfl,
    show gridGroupSource 184=16 from rfl,show sourceWord 16=[(1,true),(1,true),(1,true)] from rfl,
    show groupPowers 184=((0,0,0,-2):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart11,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_184

theorem word_binding_185 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 188 =
      gridLeadingRows m f ε s v (.word 185) := by
  change _ = v (gridGroupIndex 185)-gridMatrixScalar m f (ε*I^(2*m)) 185 0 s*v (gridGroupTarget 185)
  rw [matrixScalar_leading]
  rw [show gridGroupIndex 185=42 from rfl,show gridGroupTarget 185=416 from rfl,
    show gridGroupSource 185=48 from rfl,show sourceWord 48=[(4,false),(2,true),(1,true)] from rfl,
    show groupPowers 185=((0,2,0,0):ℤ×ℤ×ℤ×ℤ) from rfl]
  simp only [root_two,badParameter,Nat.cast_ofNat,h2,hη]
  norm_num [sourceRows,sourceRowsPart11,gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring <;> simp

#print axioms word_binding_185

end SmallLevelThirtyFourGridMMP
end
end

/-! ## SmallLevelThirtyFourGridMMPTheoryV4 -/
section
/-! Consolidated chapter: SmallLevelThirtyFourGridMMP. Original declarations and local scopes are retained. -/

/-! ## SmallLevelThirtyFourGridMMPInfinityBindingPart00V1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGridMMP
open SmallLevelThirtyFourGrid
open Complex SmallLevelPrimeRates SmallLevelFourPrimeRates SmallLevelThirtyFourUnitMMP

theorem infinity_binding_0 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 19 =
      gridLeadingRows m f ε s v (.infinity 0) := by
  norm_num [sourceRows,sourceRowsPart1,gridLeadingRows,gridInfinityIndex] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms infinity_binding_0

theorem infinity_binding_1 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 47 =
      gridLeadingRows m f ε s v (.infinity 1) := by
  norm_num [sourceRows,sourceRowsPart2,gridLeadingRows,gridInfinityIndex] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms infinity_binding_1

theorem infinity_binding_2 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v 88 =
      gridLeadingRows m f ε s v (.infinity 2) := by
  norm_num [sourceRows,sourceRowsPart5,gridLeadingRows,gridInfinityIndex] <;>
    field_simp [parameter_ne_zero 2 m (by decide) s,parameter_ne_zero 3 m (by decide) s,
      parameter_ne_zero 17 m (by decide) s,parameter_ne_zero 5 m (by decide) s] <;> ring

#print axioms infinity_binding_2

end SmallLevelThirtyFourGridMMP
end
end

/-! ## SmallLevelThirtyFourGridMMPSourceBindingV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGridMMP
open SmallLevelThirtyFourGrid
open Complex SmallLevelPrimeRates SmallLevelThirtyFourUnitMMP
/-- The exact finite source matrix evaluated on the physical exponential curve.
The three sign hypotheses select the MMP case; no pole or rank assumption is used. -/
theorem original_leading_binding (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 510→ℂ)
    (hη : ε*I^(2*m) = -1)
    (h2 : (Real.sqrt 2:ℂ)*f 2 = -1) (h17 : (Real.sqrt 17:ℂ)*f 17 = 1)
    (i : Fin 546) :
    sourceRows (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s)
      ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 5:ℂ)*f 5) v i =
      gridLeadingRows m f ε s v (selectedSource i) := by
  fin_cases i
  · exact word_binding_0 m f ε s v hη h2 h17
  · exact word_binding_1 m f ε s v hη h2 h17
  · exact word_binding_2 m f ε s v hη h2 h17
  · exact word_binding_3 m f ε s v hη h2 h17
  · exact word_binding_4 m f ε s v hη h2 h17
  · exact word_binding_5 m f ε s v hη h2 h17
  · exact word_binding_6 m f ε s v hη h2 h17
  · exact word_binding_7 m f ε s v hη h2 h17
  · exact word_binding_8 m f ε s v hη h2 h17
  · exact word_binding_9 m f ε s v hη h2 h17
  · exact word_binding_10 m f ε s v hη h2 h17
  · exact word_binding_11 m f ε s v hη h2 h17
  · exact word_binding_12 m f ε s v hη h2 h17
  · exact word_binding_13 m f ε s v hη h2 h17
  · exact word_binding_14 m f ε s v hη h2 h17
  · exact word_binding_15 m f ε s v hη h2 h17
  · exact word_binding_16 m f ε s v hη h2 h17
  · exact word_binding_17 m f ε s v hη h2 h17
  · exact word_binding_18 m f ε s v hη h2 h17
  · exact infinity_binding_0 m f ε s v hη h2 h17
  · exact word_binding_19 m f ε s v hη h2 h17
  · exact word_binding_20 m f ε s v hη h2 h17
  · exact word_binding_21 m f ε s v hη h2 h17
  · exact word_binding_22 m f ε s v hη h2 h17
  · exact word_binding_23 m f ε s v hη h2 h17
  · exact word_binding_24 m f ε s v hη h2 h17
  · exact word_binding_25 m f ε s v hη h2 h17
  · exact word_binding_26 m f ε s v hη h2 h17
  · exact word_binding_27 m f ε s v hη h2 h17
  · exact word_binding_28 m f ε s v hη h2 h17
  · exact word_binding_29 m f ε s v hη h2 h17
  · exact word_binding_30 m f ε s v hη h2 h17
  · exact word_binding_31 m f ε s v hη h2 h17
  · exact word_binding_32 m f ε s v hη h2 h17
  · exact word_binding_33 m f ε s v hη h2 h17
  · exact word_binding_34 m f ε s v hη h2 h17
  · exact word_binding_35 m f ε s v hη h2 h17
  · exact word_binding_36 m f ε s v hη h2 h17
  · exact word_binding_37 m f ε s v hη h2 h17
  · exact word_binding_38 m f ε s v hη h2 h17
  · exact word_binding_39 m f ε s v hη h2 h17
  · exact word_binding_40 m f ε s v hη h2 h17
  · exact word_binding_41 m f ε s v hη h2 h17
  · exact word_binding_42 m f ε s v hη h2 h17
  · exact word_binding_43 m f ε s v hη h2 h17
  · exact word_binding_44 m f ε s v hη h2 h17
  · exact word_binding_45 m f ε s v hη h2 h17
  · exact infinity_binding_1 m f ε s v hη h2 h17
  · exact word_binding_46 m f ε s v hη h2 h17
  · exact word_binding_47 m f ε s v hη h2 h17
  · exact word_binding_48 m f ε s v hη h2 h17
  · exact word_binding_49 m f ε s v hη h2 h17
  · exact word_binding_50 m f ε s v hη h2 h17
  · exact word_binding_51 m f ε s v hη h2 h17
  · exact word_binding_52 m f ε s v hη h2 h17
  · exact word_binding_53 m f ε s v hη h2 h17
  · exact word_binding_54 m f ε s v hη h2 h17
  · exact word_binding_55 m f ε s v hη h2 h17
  · exact word_binding_56 m f ε s v hη h2 h17
  · exact word_binding_57 m f ε s v hη h2 h17
  · exact word_binding_58 m f ε s v hη h2 h17
  · exact word_binding_59 m f ε s v hη h2 h17
  · exact word_binding_60 m f ε s v hη h2 h17
  · exact word_binding_61 m f ε s v hη h2 h17
  · exact word_binding_62 m f ε s v hη h2 h17
  · exact word_binding_63 m f ε s v hη h2 h17
  · exact word_binding_64 m f ε s v hη h2 h17
  · exact word_binding_65 m f ε s v hη h2 h17
  · exact word_binding_66 m f ε s v hη h2 h17
  · exact word_binding_67 m f ε s v hη h2 h17
  · exact word_binding_68 m f ε s v hη h2 h17
  · exact word_binding_69 m f ε s v hη h2 h17
  · exact word_binding_70 m f ε s v hη h2 h17
  · exact word_binding_71 m f ε s v hη h2 h17
  · exact word_binding_72 m f ε s v hη h2 h17
  · exact word_binding_73 m f ε s v hη h2 h17
  · exact word_binding_74 m f ε s v hη h2 h17
  · exact word_binding_75 m f ε s v hη h2 h17
  · exact word_binding_76 m f ε s v hη h2 h17
  · exact word_binding_77 m f ε s v hη h2 h17
  · exact word_binding_78 m f ε s v hη h2 h17
  · exact word_binding_79 m f ε s v hη h2 h17
  · exact word_binding_80 m f ε s v hη h2 h17
  · exact word_binding_81 m f ε s v hη h2 h17
  · exact word_binding_82 m f ε s v hη h2 h17
  · exact word_binding_83 m f ε s v hη h2 h17
  · exact word_binding_84 m f ε s v hη h2 h17
  · exact word_binding_85 m f ε s v hη h2 h17
  · exact infinity_binding_2 m f ε s v hη h2 h17
  · exact word_binding_86 m f ε s v hη h2 h17
  · exact word_binding_87 m f ε s v hη h2 h17
  · exact word_binding_88 m f ε s v hη h2 h17
  · exact word_binding_89 m f ε s v hη h2 h17
  · exact word_binding_90 m f ε s v hη h2 h17
  · exact word_binding_91 m f ε s v hη h2 h17
  · exact word_binding_92 m f ε s v hη h2 h17
  · exact word_binding_93 m f ε s v hη h2 h17
  · exact word_binding_94 m f ε s v hη h2 h17
  · exact word_binding_95 m f ε s v hη h2 h17
  · exact word_binding_96 m f ε s v hη h2 h17
  · exact word_binding_97 m f ε s v hη h2 h17
  · exact word_binding_98 m f ε s v hη h2 h17
  · exact word_binding_99 m f ε s v hη h2 h17
  · exact word_binding_100 m f ε s v hη h2 h17
  · exact word_binding_101 m f ε s v hη h2 h17
  · exact word_binding_102 m f ε s v hη h2 h17
  · exact word_binding_103 m f ε s v hη h2 h17
  · exact word_binding_104 m f ε s v hη h2 h17
  · exact word_binding_105 m f ε s v hη h2 h17
  · exact word_binding_106 m f ε s v hη h2 h17
  · exact word_binding_107 m f ε s v hη h2 h17
  · exact word_binding_108 m f ε s v hη h2 h17
  · exact word_binding_109 m f ε s v hη h2 h17
  · exact word_binding_110 m f ε s v hη h2 h17
  · exact word_binding_111 m f ε s v hη h2 h17
  · exact word_binding_112 m f ε s v hη h2 h17
  · exact word_binding_113 m f ε s v hη h2 h17
  · exact word_binding_114 m f ε s v hη h2 h17
  · exact word_binding_115 m f ε s v hη h2 h17
  · exact word_binding_116 m f ε s v hη h2 h17
  · exact word_binding_117 m f ε s v hη h2 h17
  · exact word_binding_118 m f ε s v hη h2 h17
  · exact word_binding_119 m f ε s v hη h2 h17
  · exact word_binding_120 m f ε s v hη h2 h17
  · exact word_binding_121 m f ε s v hη h2 h17
  · exact word_binding_122 m f ε s v hη h2 h17
  · exact word_binding_123 m f ε s v hη h2 h17
  · exact word_binding_124 m f ε s v hη h2 h17
  · exact word_binding_125 m f ε s v hη h2 h17
  · exact word_binding_126 m f ε s v hη h2 h17
  · exact word_binding_127 m f ε s v hη h2 h17
  · exact word_binding_128 m f ε s v hη h2 h17
  · exact word_binding_129 m f ε s v hη h2 h17
  · exact word_binding_130 m f ε s v hη h2 h17
  · exact word_binding_131 m f ε s v hη h2 h17
  · exact word_binding_132 m f ε s v hη h2 h17
  · exact word_binding_133 m f ε s v hη h2 h17
  · exact word_binding_134 m f ε s v hη h2 h17
  · exact word_binding_135 m f ε s v hη h2 h17
  · exact word_binding_136 m f ε s v hη h2 h17
  · exact word_binding_137 m f ε s v hη h2 h17
  · exact word_binding_138 m f ε s v hη h2 h17
  · exact word_binding_139 m f ε s v hη h2 h17
  · exact word_binding_140 m f ε s v hη h2 h17
  · exact word_binding_141 m f ε s v hη h2 h17
  · exact word_binding_142 m f ε s v hη h2 h17
  · exact word_binding_143 m f ε s v hη h2 h17
  · exact word_binding_144 m f ε s v hη h2 h17
  · exact word_binding_145 m f ε s v hη h2 h17
  · exact word_binding_146 m f ε s v hη h2 h17
  · exact word_binding_147 m f ε s v hη h2 h17
  · exact word_binding_148 m f ε s v hη h2 h17
  · exact word_binding_149 m f ε s v hη h2 h17
  · exact word_binding_150 m f ε s v hη h2 h17
  · exact word_binding_151 m f ε s v hη h2 h17
  · exact word_binding_152 m f ε s v hη h2 h17
  · exact word_binding_153 m f ε s v hη h2 h17
  · exact word_binding_154 m f ε s v hη h2 h17
  · exact word_binding_155 m f ε s v hη h2 h17
  · exact word_binding_156 m f ε s v hη h2 h17
  · exact word_binding_157 m f ε s v hη h2 h17
  · exact word_binding_158 m f ε s v hη h2 h17
  · exact word_binding_159 m f ε s v hη h2 h17
  · exact word_binding_160 m f ε s v hη h2 h17
  · exact word_binding_161 m f ε s v hη h2 h17
  · exact word_binding_162 m f ε s v hη h2 h17
  · exact word_binding_163 m f ε s v hη h2 h17
  · exact word_binding_164 m f ε s v hη h2 h17
  · exact word_binding_165 m f ε s v hη h2 h17
  · exact word_binding_166 m f ε s v hη h2 h17
  · exact word_binding_167 m f ε s v hη h2 h17
  · exact word_binding_168 m f ε s v hη h2 h17
  · exact word_binding_169 m f ε s v hη h2 h17
  · exact word_binding_170 m f ε s v hη h2 h17
  · exact word_binding_171 m f ε s v hη h2 h17
  · exact word_binding_172 m f ε s v hη h2 h17
  · exact word_binding_173 m f ε s v hη h2 h17
  · exact word_binding_174 m f ε s v hη h2 h17
  · exact word_binding_175 m f ε s v hη h2 h17
  · exact word_binding_176 m f ε s v hη h2 h17
  · exact word_binding_177 m f ε s v hη h2 h17
  · exact word_binding_178 m f ε s v hη h2 h17
  · exact word_binding_179 m f ε s v hη h2 h17
  · exact word_binding_180 m f ε s v hη h2 h17
  · exact word_binding_181 m f ε s v hη h2 h17
  · exact word_binding_182 m f ε s v hη h2 h17
  · exact word_binding_183 m f ε s v hη h2 h17
  · exact word_binding_184 m f ε s v hη h2 h17
  · exact word_binding_185 m f ε s v hη h2 h17
  · exact entire_binding_0 m f ε s v hη h2 h17
  · exact taylor_binding_0 m f ε s v hη h2 h17
  · exact taylor_binding_1 m f ε s v hη h2 h17
  · exact taylor_binding_2 m f ε s v hη h2 h17
  · exact taylor_binding_3 m f ε s v hη h2 h17
  · exact taylor_binding_4 m f ε s v hη h2 h17
  · exact taylor_binding_5 m f ε s v hη h2 h17
  · exact taylor_binding_6 m f ε s v hη h2 h17
  · exact taylor_binding_7 m f ε s v hη h2 h17
  · exact taylor_binding_8 m f ε s v hη h2 h17
  · exact taylor_binding_9 m f ε s v hη h2 h17
  · exact taylor_binding_10 m f ε s v hη h2 h17
  · exact taylor_binding_11 m f ε s v hη h2 h17
  · exact entire_binding_1 m f ε s v hη h2 h17
  · exact taylor_binding_12 m f ε s v hη h2 h17
  · exact taylor_binding_13 m f ε s v hη h2 h17
  · exact taylor_binding_14 m f ε s v hη h2 h17
  · exact taylor_binding_15 m f ε s v hη h2 h17
  · exact taylor_binding_16 m f ε s v hη h2 h17
  · exact taylor_binding_17 m f ε s v hη h2 h17
  · exact taylor_binding_18 m f ε s v hη h2 h17
  · exact taylor_binding_19 m f ε s v hη h2 h17
  · exact entire_binding_2 m f ε s v hη h2 h17
  · exact taylor_binding_20 m f ε s v hη h2 h17
  · exact taylor_binding_21 m f ε s v hη h2 h17
  · exact taylor_binding_22 m f ε s v hη h2 h17
  · exact taylor_binding_23 m f ε s v hη h2 h17
  · exact taylor_binding_24 m f ε s v hη h2 h17
  · exact entire_binding_3 m f ε s v hη h2 h17
  · exact entire_binding_4 m f ε s v hη h2 h17
  · exact taylor_binding_25 m f ε s v hη h2 h17
  · exact taylor_binding_26 m f ε s v hη h2 h17
  · exact taylor_binding_27 m f ε s v hη h2 h17
  · exact taylor_binding_28 m f ε s v hη h2 h17
  · exact taylor_binding_29 m f ε s v hη h2 h17
  · exact taylor_binding_30 m f ε s v hη h2 h17
  · exact taylor_binding_31 m f ε s v hη h2 h17
  · exact taylor_binding_32 m f ε s v hη h2 h17
  · exact taylor_binding_33 m f ε s v hη h2 h17
  · exact taylor_binding_34 m f ε s v hη h2 h17
  · exact taylor_binding_35 m f ε s v hη h2 h17
  · exact taylor_binding_36 m f ε s v hη h2 h17
  · exact taylor_binding_37 m f ε s v hη h2 h17
  · exact taylor_binding_38 m f ε s v hη h2 h17
  · exact taylor_binding_39 m f ε s v hη h2 h17
  · exact taylor_binding_40 m f ε s v hη h2 h17
  · exact taylor_binding_41 m f ε s v hη h2 h17
  · exact taylor_binding_42 m f ε s v hη h2 h17
  · exact taylor_binding_43 m f ε s v hη h2 h17
  · exact entire_binding_5 m f ε s v hη h2 h17
  · exact taylor_binding_44 m f ε s v hη h2 h17
  · exact taylor_binding_45 m f ε s v hη h2 h17
  · exact taylor_binding_46 m f ε s v hη h2 h17
  · exact taylor_binding_47 m f ε s v hη h2 h17
  · exact taylor_binding_48 m f ε s v hη h2 h17
  · exact taylor_binding_49 m f ε s v hη h2 h17
  · exact taylor_binding_50 m f ε s v hη h2 h17
  · exact taylor_binding_51 m f ε s v hη h2 h17
  · exact entire_binding_6 m f ε s v hη h2 h17
  · exact taylor_binding_52 m f ε s v hη h2 h17
  · exact taylor_binding_53 m f ε s v hη h2 h17
  · exact entire_binding_7 m f ε s v hη h2 h17
  · exact taylor_binding_54 m f ε s v hη h2 h17
  · exact taylor_binding_55 m f ε s v hη h2 h17
  · exact taylor_binding_56 m f ε s v hη h2 h17
  · exact taylor_binding_57 m f ε s v hη h2 h17
  · exact entire_binding_8 m f ε s v hη h2 h17
  · exact entire_binding_9 m f ε s v hη h2 h17
  · exact taylor_binding_58 m f ε s v hη h2 h17
  · exact taylor_binding_59 m f ε s v hη h2 h17
  · exact hecke_binding_0 m f s v h2 h17
  · exact hecke_binding_1 m f s v h2 h17
  · exact hecke_binding_2 m f s v h2 h17
  · exact hecke_binding_3 m f s v h2 h17
  · exact hecke_binding_4 m f s v h2 h17
  · exact hecke_binding_5 m f s v h2 h17
  · exact hecke_binding_6 m f s v h2 h17
  · exact hecke_binding_7 m f s v h2 h17
  · exact hecke_binding_8 m f s v h2 h17
  · exact hecke_binding_9 m f s v h2 h17
  · exact hecke_binding_10 m f s v h2 h17
  · exact hecke_binding_11 m f s v h2 h17
  · exact hecke_binding_12 m f s v h2 h17
  · exact hecke_binding_13 m f s v h2 h17
  · exact hecke_binding_14 m f s v h2 h17
  · exact hecke_binding_15 m f s v h2 h17
  · exact hecke_binding_16 m f s v h2 h17
  · exact hecke_binding_17 m f s v h2 h17
  · exact hecke_binding_18 m f s v h2 h17
  · exact hecke_binding_19 m f s v h2 h17
  · exact hecke_binding_20 m f s v h2 h17
  · exact hecke_binding_21 m f s v h2 h17
  · exact hecke_binding_22 m f s v h2 h17
  · exact hecke_binding_23 m f s v h2 h17
  · exact hecke_binding_24 m f s v h2 h17
  · exact hecke_binding_25 m f s v h2 h17
  · exact hecke_binding_26 m f s v h2 h17
  · exact hecke_binding_27 m f s v h2 h17
  · exact hecke_binding_28 m f s v h2 h17
  · exact hecke_binding_29 m f s v h2 h17
  · exact hecke_binding_30 m f s v h2 h17
  · exact hecke_binding_31 m f s v h2 h17
  · exact hecke_binding_32 m f s v h2 h17
  · exact hecke_binding_33 m f s v h2 h17
  · exact hecke_binding_34 m f s v h2 h17
  · exact hecke_binding_35 m f s v h2 h17
  · exact hecke_binding_36 m f s v h2 h17
  · exact hecke_binding_37 m f s v h2 h17
  · exact hecke_binding_38 m f s v h2 h17
  · exact hecke_binding_39 m f s v h2 h17
  · exact hecke_binding_40 m f s v h2 h17
  · exact hecke_binding_41 m f s v h2 h17
  · exact hecke_binding_42 m f s v h2 h17
  · exact hecke_binding_43 m f s v h2 h17
  · exact hecke_binding_44 m f s v h2 h17
  · exact hecke_binding_45 m f s v h2 h17
  · exact hecke_binding_46 m f s v h2 h17
  · exact hecke_binding_47 m f s v h2 h17
  · exact hecke_binding_48 m f s v h2 h17
  · exact hecke_binding_49 m f s v h2 h17
  · exact hecke_binding_50 m f s v h2 h17
  · exact hecke_binding_51 m f s v h2 h17
  · exact hecke_binding_52 m f s v h2 h17
  · exact hecke_binding_53 m f s v h2 h17
  · exact hecke_binding_54 m f s v h2 h17
  · exact hecke_binding_55 m f s v h2 h17
  · exact hecke_binding_56 m f s v h2 h17
  · exact hecke_binding_57 m f s v h2 h17
  · exact hecke_binding_58 m f s v h2 h17
  · exact hecke_binding_59 m f s v h2 h17
  · exact hecke_binding_60 m f s v h2 h17
  · exact hecke_binding_61 m f s v h2 h17
  · exact hecke_binding_62 m f s v h2 h17
  · exact hecke_binding_63 m f s v h2 h17
  · exact hecke_binding_64 m f s v h2 h17
  · exact hecke_binding_65 m f s v h2 h17
  · exact hecke_binding_66 m f s v h2 h17
  · exact hecke_binding_67 m f s v h2 h17
  · exact hecke_binding_68 m f s v h2 h17
  · exact hecke_binding_69 m f s v h2 h17
  · exact hecke_binding_70 m f s v h2 h17
  · exact hecke_binding_71 m f s v h2 h17
  · exact hecke_binding_72 m f s v h2 h17
  · exact hecke_binding_73 m f s v h2 h17
  · exact hecke_binding_74 m f s v h2 h17
  · exact hecke_binding_75 m f s v h2 h17
  · exact hecke_binding_76 m f s v h2 h17
  · exact hecke_binding_77 m f s v h2 h17
  · exact hecke_binding_78 m f s v h2 h17
  · exact hecke_binding_79 m f s v h2 h17
  · exact hecke_binding_80 m f s v h2 h17
  · exact hecke_binding_81 m f s v h2 h17
  · exact hecke_binding_82 m f s v h2 h17
  · exact hecke_binding_83 m f s v h2 h17
  · exact hecke_binding_84 m f s v h2 h17
  · exact hecke_binding_85 m f s v h2 h17
  · exact hecke_binding_86 m f s v h2 h17
  · exact hecke_binding_87 m f s v h2 h17
  · exact hecke_binding_88 m f s v h2 h17
  · exact hecke_binding_89 m f s v h2 h17
  · exact hecke_binding_90 m f s v h2 h17
  · exact hecke_binding_91 m f s v h2 h17
  · exact hecke_binding_92 m f s v h2 h17
  · exact hecke_binding_93 m f s v h2 h17
  · exact hecke_binding_94 m f s v h2 h17
  · exact hecke_binding_95 m f s v h2 h17
  · exact hecke_binding_96 m f s v h2 h17
  · exact hecke_binding_97 m f s v h2 h17
  · exact hecke_binding_98 m f s v h2 h17
  · exact hecke_binding_99 m f s v h2 h17
  · exact hecke_binding_100 m f s v h2 h17
  · exact hecke_binding_101 m f s v h2 h17
  · exact hecke_binding_102 m f s v h2 h17
  · exact hecke_binding_103 m f s v h2 h17
  · exact hecke_binding_104 m f s v h2 h17
  · exact hecke_binding_105 m f s v h2 h17
  · exact hecke_binding_106 m f s v h2 h17
  · exact hecke_binding_107 m f s v h2 h17
  · exact hecke_binding_108 m f s v h2 h17
  · exact hecke_binding_109 m f s v h2 h17
  · exact hecke_binding_110 m f s v h2 h17
  · exact hecke_binding_111 m f s v h2 h17
  · exact hecke_binding_112 m f s v h2 h17
  · exact hecke_binding_113 m f s v h2 h17
  · exact hecke_binding_114 m f s v h2 h17
  · exact hecke_binding_115 m f s v h2 h17
  · exact hecke_binding_116 m f s v h2 h17
  · exact hecke_binding_117 m f s v h2 h17
  · exact hecke_binding_118 m f s v h2 h17
  · exact hecke_binding_119 m f s v h2 h17
  · exact hecke_binding_120 m f s v h2 h17
  · exact hecke_binding_121 m f s v h2 h17
  · exact hecke_binding_122 m f s v h2 h17
  · exact hecke_binding_123 m f s v h2 h17
  · exact hecke_binding_124 m f s v h2 h17
  · exact hecke_binding_125 m f s v h2 h17
  · exact hecke_binding_126 m f s v h2 h17
  · exact hecke_binding_127 m f s v h2 h17
  · exact hecke_binding_128 m f s v h2 h17
  · exact hecke_binding_129 m f s v h2 h17
  · exact hecke_binding_130 m f s v h2 h17
  · exact hecke_binding_131 m f s v h2 h17
  · exact hecke_binding_132 m f s v h2 h17
  · exact hecke_binding_133 m f s v h2 h17
  · exact hecke_binding_134 m f s v h2 h17
  · exact hecke_binding_135 m f s v h2 h17
  · exact hecke_binding_136 m f s v h2 h17
  · exact hecke_binding_137 m f s v h2 h17
  · exact hecke_binding_138 m f s v h2 h17
  · exact hecke_binding_139 m f s v h2 h17
  · exact hecke_binding_140 m f s v h2 h17
  · exact hecke_binding_141 m f s v h2 h17
  · exact hecke_binding_142 m f s v h2 h17
  · exact hecke_binding_143 m f s v h2 h17
  · exact hecke_binding_144 m f s v h2 h17
  · exact hecke_binding_145 m f s v h2 h17
  · exact hecke_binding_146 m f s v h2 h17
  · exact hecke_binding_147 m f s v h2 h17
  · exact hecke_binding_148 m f s v h2 h17
  · exact hecke_binding_149 m f s v h2 h17
  · exact hecke_binding_150 m f s v h2 h17
  · exact hecke_binding_151 m f s v h2 h17
  · exact hecke_binding_152 m f s v h2 h17
  · exact hecke_binding_153 m f s v h2 h17
  · exact hecke_binding_154 m f s v h2 h17
  · exact hecke_binding_155 m f s v h2 h17
  · exact hecke_binding_156 m f s v h2 h17
  · exact hecke_binding_157 m f s v h2 h17
  · exact hecke_binding_158 m f s v h2 h17
  · exact hecke_binding_159 m f s v h2 h17
  · exact hecke_binding_160 m f s v h2 h17
  · exact hecke_binding_161 m f s v h2 h17
  · exact hecke_binding_162 m f s v h2 h17
  · exact hecke_binding_163 m f s v h2 h17
  · exact hecke_binding_164 m f s v h2 h17
  · exact hecke_binding_165 m f s v h2 h17
  · exact hecke_binding_166 m f s v h2 h17
  · exact hecke_binding_167 m f s v h2 h17
  · exact hecke_binding_168 m f s v h2 h17
  · exact hecke_binding_169 m f s v h2 h17
  · exact hecke_binding_170 m f s v h2 h17
  · exact hecke_binding_171 m f s v h2 h17
  · exact hecke_binding_172 m f s v h2 h17
  · exact hecke_binding_173 m f s v h2 h17
  · exact hecke_binding_174 m f s v h2 h17
  · exact hecke_binding_175 m f s v h2 h17
  · exact hecke_binding_176 m f s v h2 h17
  · exact hecke_binding_177 m f s v h2 h17
  · exact hecke_binding_178 m f s v h2 h17
  · exact hecke_binding_179 m f s v h2 h17
  · exact hecke_binding_180 m f s v h2 h17
  · exact hecke_binding_181 m f s v h2 h17
  · exact hecke_binding_182 m f s v h2 h17
  · exact hecke_binding_183 m f s v h2 h17
  · exact hecke_binding_184 m f s v h2 h17
  · exact hecke_binding_185 m f s v h2 h17
  · exact hecke_binding_186 m f s v h2 h17
  · exact hecke_binding_187 m f s v h2 h17
  · exact hecke_binding_188 m f s v h2 h17
  · exact hecke_binding_189 m f s v h2 h17
  · exact hecke_binding_190 m f s v h2 h17
  · exact hecke_binding_191 m f s v h2 h17
  · exact hecke_binding_192 m f s v h2 h17
  · exact hecke_binding_193 m f s v h2 h17
  · exact hecke_binding_194 m f s v h2 h17
  · exact hecke_binding_195 m f s v h2 h17
  · exact hecke_binding_196 m f s v h2 h17
  · exact hecke_binding_197 m f s v h2 h17
  · exact hecke_binding_198 m f s v h2 h17
  · exact hecke_binding_199 m f s v h2 h17
  · exact hecke_binding_200 m f s v h2 h17
  · exact hecke_binding_201 m f s v h2 h17
  · exact hecke_binding_202 m f s v h2 h17
  · exact hecke_binding_203 m f s v h2 h17
  · exact hecke_binding_204 m f s v h2 h17
  · exact hecke_binding_205 m f s v h2 h17
  · exact hecke_binding_206 m f s v h2 h17
  · exact hecke_binding_207 m f s v h2 h17
  · exact hecke_binding_208 m f s v h2 h17
  · exact hecke_binding_209 m f s v h2 h17
  · exact hecke_binding_210 m f s v h2 h17
  · exact hecke_binding_211 m f s v h2 h17
  · exact hecke_binding_212 m f s v h2 h17
  · exact hecke_binding_213 m f s v h2 h17
  · exact hecke_binding_214 m f s v h2 h17
  · exact hecke_binding_215 m f s v h2 h17
  · exact hecke_binding_216 m f s v h2 h17
  · exact hecke_binding_217 m f s v h2 h17
  · exact hecke_binding_218 m f s v h2 h17
  · exact hecke_binding_219 m f s v h2 h17
  · exact hecke_binding_220 m f s v h2 h17
  · exact hecke_binding_221 m f s v h2 h17
  · exact hecke_binding_222 m f s v h2 h17
  · exact hecke_binding_223 m f s v h2 h17
  · exact hecke_binding_224 m f s v h2 h17
  · exact hecke_binding_225 m f s v h2 h17
  · exact hecke_binding_226 m f s v h2 h17
  · exact hecke_binding_227 m f s v h2 h17
  · exact hecke_binding_228 m f s v h2 h17
  · exact hecke_binding_229 m f s v h2 h17
  · exact hecke_binding_230 m f s v h2 h17
  · exact hecke_binding_231 m f s v h2 h17
  · exact hecke_binding_232 m f s v h2 h17
  · exact hecke_binding_233 m f s v h2 h17
  · exact hecke_binding_234 m f s v h2 h17
  · exact hecke_binding_235 m f s v h2 h17
  · exact hecke_binding_236 m f s v h2 h17
  · exact hecke_binding_237 m f s v h2 h17
  · exact hecke_binding_238 m f s v h2 h17
  · exact hecke_binding_239 m f s v h2 h17
  · exact hecke_binding_240 m f s v h2 h17
  · exact hecke_binding_241 m f s v h2 h17
  · exact hecke_binding_242 m f s v h2 h17
  · exact hecke_binding_243 m f s v h2 h17
  · exact hecke_binding_244 m f s v h2 h17
  · exact hecke_binding_245 m f s v h2 h17
  · exact hecke_binding_246 m f s v h2 h17
  · exact hecke_binding_247 m f s v h2 h17
  · exact hecke_binding_248 m f s v h2 h17
  · exact hecke_binding_249 m f s v h2 h17
  · exact hecke_binding_250 m f s v h2 h17
  · exact hecke_binding_251 m f s v h2 h17
  · exact hecke_binding_252 m f s v h2 h17
  · exact hecke_binding_253 m f s v h2 h17
  · exact hecke_binding_254 m f s v h2 h17
  · exact hecke_binding_255 m f s v h2 h17
  · exact hecke_binding_256 m f s v h2 h17
  · exact hecke_binding_257 m f s v h2 h17
  · exact hecke_binding_258 m f s v h2 h17
  · exact hecke_binding_259 m f s v h2 h17
  · exact hecke_binding_260 m f s v h2 h17
  · exact hecke_binding_261 m f s v h2 h17
  · exact hecke_binding_262 m f s v h2 h17
  · exact hecke_binding_263 m f s v h2 h17
  · exact hecke_binding_264 m f s v h2 h17
  · exact hecke_binding_265 m f s v h2 h17
  · exact hecke_binding_266 m f s v h2 h17
  · exact hecke_binding_267 m f s v h2 h17
  · exact hecke_binding_268 m f s v h2 h17
  · exact hecke_binding_269 m f s v h2 h17
  · exact hecke_binding_270 m f s v h2 h17
  · exact hecke_binding_271 m f s v h2 h17
  · exact hecke_binding_272 m f s v h2 h17
  · exact hecke_binding_273 m f s v h2 h17
  · exact hecke_binding_274 m f s v h2 h17
  · exact hecke_binding_275 m f s v h2 h17
  · exact hecke_binding_276 m f s v h2 h17
  · exact hecke_binding_277 m f s v h2 h17
  · exact hecke_binding_278 m f s v h2 h17
  · exact hecke_binding_279 m f s v h2 h17
  · exact hecke_binding_280 m f s v h2 h17
  · exact hecke_binding_281 m f s v h2 h17
  · exact hecke_binding_282 m f s v h2 h17
  · exact hecke_binding_283 m f s v h2 h17
  · exact hecke_binding_284 m f s v h2 h17
  · exact hecke_binding_285 m f s v h2 h17
  · exact hecke_binding_286 m f s v h2 h17

#print axioms original_leading_binding

end SmallLevelThirtyFourGridMMP
end
end
end
