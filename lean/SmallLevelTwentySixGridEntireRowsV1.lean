module
public import SmallLevelTwentySixGridSourceMatricesV1
public import SmallLevelTwentySixGridWordEntireV1
public import SmallLevelTwentySixGridCoherentFrickeV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Matrix Complex Set SmallLevelAdditive SmallLevelTaylor
open SmallLevelOriginal SmallLevelNormalized FinitenessOriginalInput
open SmallLevelTwentySixTwelfth (W)
open scoped MatrixGroups ModularForm

def gridEntireQ : Fin 11→ℕ := ![3,4,5,6,10,13,15,20,30,39,78]

theorem gridEntireQ_valid (i : Fin 11) : 0<gridEntireQ i ∧ gridEntireQ i∣780 := by
  fin_cases i <;> decide

/-- The11 unshifted Ramanujan sources are entire and agree with the grid sums. -/
theorem grid_ramanujan_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : IsSolution 26 (2*m) f) (i : Fin 11) :
    (∀ s : ℂ,AnalyticAt ℂ (ramanujanEntire 26 (2*m) f (gridEntireQ i)) s) ∧
    ∃ B : ℝ,∀ s : ℂ,B<s.re →
      ramanujanEntire 26 (2*m) f (gridEntireQ i) s=gridSum (2*m) f 780 (gridEntireQ i) 0 s := by
  obtain ⟨ha,B,hB⟩:=original_ramanujan_entire (by decide : 0<26) (by omega : 0<2*m)
    hf (gridEntireQ_valid i).1
  refine ⟨ha,B,?_⟩
  intro s hs
  rw [hB s hs]
  simpa only [gridSum,Int.cast_zero,zero_div] using
    ramanujanAdditive_grid (2*m) f (by decide : 0<780)
      (gridEntireQ_valid i).1 (gridEntireQ_valid i).2 (0:ℤ) s

theorem source_scale_ne_zero (i : Fin 27) :
    wordScale (sourceWord i)*(sourceMultiple i:ℝ)≠0 := by
  intro h
  have hd:=gridWord_det (sourceWord i)
  change (gridWord (sourceWord i)).val.det=1 at hd
  rw [source_coordinates,h,zero_smul] at hd
  norm_num at hd

theorem source_word_nonaffine (i : Fin 27) :
    (gridWord (sourceWord i)).val 1 0≠0 := by
  rw [source_coordinates]
  change (wordScale (sourceWord i)*(sourceMultiple i:ℝ))*(sourceRaw i 1 0:ℝ)≠0
  exact mul_ne_zero (source_scale_ne_zero i) (by exact_mod_cast source_nonaffine i)

def gridInfinitySource : Fin 2→Fin 27 := ![21,12]
def gridInfinityIndex : Fin 2→Fin 780 := ![0,396]

theorem gridInfinity_geometry (i : Fin 2) :
    (sourceRaw (gridInfinitySource i) 1 0:ℝ)*((gridInfinityIndex i:ℕ):ℝ)/780+
      (sourceRaw (gridInfinitySource i) 1 1:ℝ)=0 := by
  fin_cases i <;> norm_num [gridInfinitySource,gridInfinityIndex,sourceRaw]

/-- Both source-to-infinity rows come from original Fourier laws. -/
theorem grid_infinity_entire_of_fricke (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : IsSolution 26 (2*m) f) {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=η • fourierFunction (2*m) f)
    (i : Fin 2) :
    Differentiable ℂ (sourceEntire m f (((gridInfinityIndex i:ℕ):ℝ)/780)) := by
  apply word_source_entire_of_fricke m hm hf hη hW (sourceWord (gridInfinitySource i))
    _ (source_word_nonaffine _)
  rw [source_coordinates]
  change (wordScale _*(sourceMultiple _:ℝ))*(sourceRaw _ 1 0:ℝ)*
    (((gridInfinityIndex i:ℕ):ℝ)/780)+(wordScale _*(sourceMultiple _:ℝ))*(sourceRaw _ 1 1:ℝ)=0
  have hh:=gridInfinity_geometry i
  rw [mul_div_assoc] at hh
  linear_combination (wordScale (sourceWord (gridInfinitySource i))*(sourceMultiple (gridInfinitySource i):ℝ))*hh

#print axioms grid_ramanujan_entire
#print axioms grid_infinity_entire_of_fricke
end SmallLevelTwentySixGrid
