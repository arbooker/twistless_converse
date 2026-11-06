module
public import QuantitativeArithmeticSmallLevelThirtyThreeGridGeometryRealV1
public import QuantitativeArithmeticSmallLevelThirtyThreeWordEntireV1
public import QuantitativeArithmeticSmallLevelThirtyThreeGridCoherentFrickeV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Matrix Complex Set SmallLevelAdditive SmallLevelTaylor
open SmallLevelOriginal SmallLevelNormalized FinitenessOriginalInput
open scoped MatrixGroups ModularForm

def gridEntireQ : Fin 8→ℕ := ![1,2,3,6,11,22,33,66]

theorem gridEntireQ_valid (i : Fin 8) : 0<gridEntireQ i ∧ gridEntireQ i∣66 := by
  fin_cases i <;> decide

/-- The eight unshifted Ramanujan sources are entire and agree with the grid sums. -/
theorem grid_ramanujan_entire (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : IsSolution 33 (2*m) f) (i : Fin 8) :
    (∀ s : ℂ,AnalyticAt ℂ (ramanujanEntire 33 (2*m) f (gridEntireQ i)) s) ∧
    ∃ B : ℝ,∀ s : ℂ,B<s.re →
      ramanujanEntire 33 (2*m) f (gridEntireQ i) s=gridSum (2*m) f 66 (gridEntireQ i) 0 s := by
  obtain ⟨ha,B,hB⟩:=original_ramanujan_entire (by decide : 0<33) (by omega : 0<2*m)
    hf (gridEntireQ_valid i).1
  refine ⟨ha,B,?_⟩
  intro s hs
  rw [hB s hs]
  simpa only [gridSum,Int.cast_zero,zero_div] using
    ramanujanAdditive_grid (2*m) f (by decide : 0<66)
      (gridEntireQ_valid i).1 (gridEntireQ_valid i).2 (0:ℤ) s

theorem source_scale_ne_zero (i : Fin 223) :
    wordScale (sourceWord i)*(sourceScale i:ℝ)≠0 := by
  intro h
  have hd:=value_det (sourceWord i)
  change (value (sourceWord i)).val.det=1 at hd
  rw [source_coordinates,h,zero_smul] at hd
  norm_num at hd

theorem source_word_nonaffine (i : Fin 223) :
    (value (sourceWord i)).val 1 0≠0 := by
  rw [source_coordinates]
  change (wordScale (sourceWord i)*(sourceScale i:ℝ))*(sourceMatrix i 1 0:ℝ)≠0
  exact mul_ne_zero (source_scale_ne_zero i) (by exact_mod_cast source_nonaffine i)

def gridInfinitySource (i : Fin 46) : Fin 223 := (infinitySpecs i).1
def gridInfinityIndex (i : Fin 46) : Fin 66 := (infinitySpecs i).2

theorem gridInfinity_geometry (i : Fin 46) :
    (sourceMatrix (gridInfinitySource i) 1 0:ℝ)*((gridInfinityIndex i:ℕ):ℝ)/66+
      (sourceMatrix (gridInfinitySource i) 1 1:ℝ)=0 := infinity_geometry_real i

/-- All source-to-infinity rows come from original Fourier laws. -/
theorem grid_infinity_entire_of_fricke (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : IsSolution 33 (2*m) f) {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] (fricke 33 (by decide))=η • fourierFunction (2*m) f)
    (i : Fin 46) :
    Differentiable ℂ (sourceEntire m f (((gridInfinityIndex i:ℕ):ℝ)/66)) := by
  apply word_source_entire_of_fricke m hm hf hη hW (sourceWord (gridInfinitySource i))
    _ (source_word_nonaffine _)
  rw [source_coordinates]
  change (wordScale _*(sourceScale _:ℝ))*(sourceMatrix _ 1 0:ℝ)*
    (((gridInfinityIndex i:ℕ):ℝ)/66)+(wordScale _*(sourceScale _:ℝ))*(sourceMatrix _ 1 1:ℝ)=0
  have hh:=gridInfinity_geometry i
  rw [mul_div_assoc] at hh
  linear_combination (wordScale (sourceWord (gridInfinitySource i))*(sourceScale (gridInfinitySource i):ℝ))*hh

#print axioms grid_ramanujan_entire
#print axioms grid_infinity_entire_of_fricke
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
