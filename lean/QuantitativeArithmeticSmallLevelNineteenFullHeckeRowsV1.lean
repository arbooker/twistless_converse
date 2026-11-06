module
public import QuantitativeArithmeticSmallLevelNineteenGridAnalyticTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenGridHeckeV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenFullHecke
open Complex SmallLevelAdditive SmallLevelTaylor
open QuantitativeArithmeticSmallLevelNineteenGridAnalytic

def ramifiedRow (t m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 114→ℂ) : ℂ :=
  (∑ j∈Finset.range 19, v (gridIndex ((t+j*(114/19):ℕ):ℤ)))-
    ((Real.sqrt 19:ℂ)*f 19)*(19:ℂ)^((m:ℂ)-s)*v (gridIndex ((19*t:ℕ):ℤ))

theorem original_ramified_grid {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    ∃ B : ℝ, ∀ t : ℕ, ∀ s : ℂ, B<s.re →
      ramifiedRow t m f s (gridVector (2*m) f s)=0 := by
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelNineteenGridHecke.normalized_ramified_row
    hm hf (by decide : Nat.Prime 19) (by decide : 19∣19)
  refine ⟨B,?_⟩
  intro t s hs
  have he := hB ((t:ℝ)/114) s hs
  simp_rw [grid_hecke_coordinate (by decide : 0<19) (by decide : 19∣114)] at he
  have h1 : (19:ℝ)*((t:ℝ)/114)=((19*t:ℕ):ℝ)/114 := by push_cast; ring
  norm_num only [Nat.cast_ofNat] at he
  rw [h1] at he
  simpa only [ramifiedRow,gridVector_index,grid,Nat.cast_ofNat,Int.cast_natCast] using he

def specs : Fin 101 → ℕ × ℕ :=
  ![(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(2,15),(2,16),(2,17),(2,18),(2,19),(2,20),(2,21),(2,22),(2,23),(2,24),(2,25),(2,26),(2,27),(2,28),(2,29),(2,30),(2,31),(2,32),(2,33),(2,34),(2,35),(2,36),(2,37),(2,38),(2,39),(2,40),(2,41),(2,42),(2,43),(2,44),(2,45),(2,46),(2,47),(2,48),(2,49),(2,50),(2,51),(2,52),(2,53),(2,54),(2,55),(2,56),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(3,13),(3,14),(3,15),(3,16),(3,17),(3,18),(3,19),(3,20),(3,21),(3,22),(3,23),(3,24),(3,25),(3,26),(3,27),(3,28),(3,29),(3,30),(3,31),(3,32),(3,33),(3,34),(3,35),(3,36),(3,37),(19,0),(19,1),(19,2),(19,3),(19,4),(19,5)]

theorem specs_valid (i : Fin 101) : (specs i).1.Prime ∧ (specs i).1∣114 ∧
    ((specs i).1=19 ∨ ¬(specs i).1∣19) := by revert i; decide

def row (i : Fin 101) (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 114→ℂ) : ℂ :=
  if (specs i).1=19 then ramifiedRow (specs i).2 m f s v
  else heckeRow (specs i).1 (specs i).2 m f s v

/-- All 101 complete Hecke rows, including the six ramified rows at19. -/
theorem original_rows {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) (i : Fin 101) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → row i m f s (gridVector (2*m) f s)=0 := by
  by_cases hp : (specs i).1=19
  · obtain ⟨B,hB⟩ := original_ramified_grid hm hf
    exact ⟨B,fun s hs => by simpa [row,hp] using hB (specs i).2 s hs⟩
  · have hg : ¬(specs i).1∣19 := (specs_valid i).2.2.resolve_left hp
    obtain ⟨B,hB⟩ := original_grid_hecke hf (specs_valid i).1 hg (specs_valid i).2.1
    exact ⟨B,fun s hs => by simpa [row,hp] using hB (specs i).2 s hs⟩

theorem row_analytic (i : Fin 101) (m : ℕ) (f : ℕ→ℂ) (v : Fin 114→ℂ) (x : ℂ) :
    AnalyticAt ℂ (fun s => row i m f s v) x := by
  unfold row
  split_ifs
  · unfold ramifiedRow
    have hp := hecke_parameter_analytic (by decide : 0<19) m x
    exact analyticAt_const.sub ((analyticAt_const.mul hp).mul analyticAt_const)
  · unfold heckeRow
    have hp := hecke_parameter_analytic (specs_valid i).1.pos m x
    exact (analyticAt_const.sub ((analyticAt_const.mul hp).mul analyticAt_const)).add
      ((hp.pow 2).mul analyticAt_const)

#print axioms original_ramified_grid
#print axioms original_rows
end QuantitativeArithmeticSmallLevelNineteenFullHecke
