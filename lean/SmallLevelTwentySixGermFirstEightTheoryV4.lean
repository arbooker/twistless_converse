module

public import SmallLevelLaurentTwoCoordinateGermsV1
public import SmallLevelTwentySixGermPrimitiveSparseMMMFamilyV4
public import SmallLevelTwentySixSecondChartTheoryV4

/-! Consolidated chapter: SmallLevelTwentySixGermFirstEight. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixGermFirstEightV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermFirstEight
open QuantitativeArithmeticSevenLaurentRows SmallLevelTwentySixSecondChart

theorem second_column_0 (X Y Z W A B : ℂ) (v : ℕ→ℂ) (hv : v 0=0) :
    eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData=
      source0 0 A 0 Y 1 1 X 0*v 1 := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData,SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData0,source0,hv]
  ring

theorem second_column_1 (X Y Z W A B : ℂ) (v : ℕ→ℂ) (hv : v 0=0) :
    eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row01.primitiveData=
      source1 0 A 0 Y 1 1 X 0*v 1 := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row01.primitiveData,SmallLevelTwentySixGermPrimitiveSparseMMM.Row01.primitiveData0,source1,hv]
  ring

theorem second_column_2 (X Y Z W A B : ℂ) (v : ℕ→ℂ) (hv : v 0=0) :
    eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData=
      source2 0 A 0 Y 1 1 X 0*v 1 := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData,SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData0,source2,hv]
  ring

theorem second_column_3 (X Y Z W A B : ℂ) (v : ℕ→ℂ) (hv : v 0=0) :
    eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData=
      source3 0 A 0 Y 1 1 X 0*v 1 := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData,SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData0,source3,hv]
  ring

theorem second_column_4 (X Y Z W A B : ℂ) (v : ℕ→ℂ) (hv : v 0=0) :
    eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData=
      source4 0 A 0 Y 1 1 X 0*v 1 := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData,SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData0,source4,hv]
  ring

theorem second_column_5 (X Y Z W A B : ℂ) (v : ℕ→ℂ) (hv : v 0=0) :
    eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row05.primitiveData=
      source5 0 A 0 Y 1 1 X 0*v 1 := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row05.primitiveData,SmallLevelTwentySixGermPrimitiveSparseMMM.Row05.primitiveData0,source5,hv]
  ring

theorem second_column_6 (X Y Z W A B : ℂ) (v : ℕ→ℂ) (hv : v 0=0) :
    eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData=
      source6 0 A 0 Y 1 1 X 0*v 1 := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData,SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData0,source6,hv]
  ring

theorem second_column_7 (X Y Z W A B : ℂ) (v : ℕ→ℂ) (hv : v 0=0) :
    eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row07.primitiveData=
      source7 0 A 0 Y 1 1 X 0*v 1 := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row07.primitiveData,SmallLevelTwentySixGermPrimitiveSparseMMM.Row07.primitiveData0,source7,hv]
  ring

/-- In the actual first eight primitive rows, the second coordinate
cannot carry a nonzero kernel vector with vanishing first coordinate. -/
theorem second_chart_excluded (X Y Z W A B : ℂ) (v : ℕ→ℂ)
    (hX : X≠0) (hY : Y≠0) (hv0 : v 0=0)
    (h0 : eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData=0)
    (h1 : eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row01.primitiveData=0)
    (h2 : eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData=0)
    (h3 : eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData=0)
    (h4 : eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData=0)
    (h5 : eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row05.primitiveData=0)
    (h6 : eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData=0)
    (h7 : eval X Y Z W A B 1 v SmallLevelTwentySixGermPrimitiveSparseMMM.Row07.primitiveData=0)
    : v 1=0 := by
  by_contra hv1
  apply no_first_eight A Y X hX hY
  · exact (mul_eq_zero.mp ((second_column_0 X Y Z W A B v hv0).symm.trans h0)).resolve_right hv1
  · exact (mul_eq_zero.mp ((second_column_1 X Y Z W A B v hv0).symm.trans h1)).resolve_right hv1
  · exact (mul_eq_zero.mp ((second_column_2 X Y Z W A B v hv0).symm.trans h2)).resolve_right hv1
  · exact (mul_eq_zero.mp ((second_column_3 X Y Z W A B v hv0).symm.trans h3)).resolve_right hv1
  · exact (mul_eq_zero.mp ((second_column_4 X Y Z W A B v hv0).symm.trans h4)).resolve_right hv1
  · exact (mul_eq_zero.mp ((second_column_5 X Y Z W A B v hv0).symm.trans h5)).resolve_right hv1
  · exact (mul_eq_zero.mp ((second_column_6 X Y Z W A B v hv0).symm.trans h6)).resolve_right hv1
  · exact (mul_eq_zero.mp ((second_column_7 X Y Z W A B v hv0).symm.trans h7)).resolve_right hv1

#print axioms second_chart_excluded
end SmallLevelTwentySixGermFirstEight
end
end

/-! ## SmallLevelTwentySixGermFirstEightKernelV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 16384
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermFirstEight
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm

def rows : Fin 8→Poly :=
  ![SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row01.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row05.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row07.primitiveData]

theorem rows_support : ∀ i : Fin 8,∀ t∈rows i,t.2.1=0 ∨ t.2.1=1 := by
  decide +kernel

theorem first_coordinate_ne_zero (X Y Z W A B : ℂ) (v : Fin 2→ℂ)
    (hX : X≠0) (hY : Y≠0) (hv : v≠0)
    (hrows : ∀ i,eval X Y Z W A B 1 (fun j => if j=0 then v 0 else v 1) (rows i)=0) :
    v 0≠0 := by
  intro hv0
  have hv1 : v 1=0 := second_chart_excluded X Y Z W A B
    (fun j => if j=0 then v 0 else v 1) hX hY (by simpa using hv0)
    (hrows 0) (hrows 1) (hrows 2) (hrows 3) (hrows 4) (hrows 5) (hrows 6) (hrows 7)
  apply hv
  funext i
  fin_cases i
  · exact hv0
  · exact hv1

/-- A pole detected in the two top coordinates lies in the first chart.
This uses the actual first eight primitive polynomials. -/
theorem pole_first_chart (X Y Z W A B : ℂ→ℂ) (F : Fin 2→ℂ→ℂ) (s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (hw : W s≠0)
    (hF : ∀ i,MeromorphicAt (F i) s) (hpole : ∃ i,meromorphicOrderAt (F i) s<0)
    (hrows : ∀ i,HasAnalyticGerm (fun z => eval (X z) (Y z) (Z z) (W z)
      (A z) (B z) 1 (fun j => if j=0 then F 0 z else F 1 z) (rows i)) s) :
    ∃ v : Fin 2→ℂ,v 0≠0 ∧ ∀ i,eval (X s) (Y s) (Z s) (W s) (A s) (B s) 1
      (fun j => if j=0 then v 0 else v 1) (rows i)=0 := by
  obtain ⟨v,hv,hvr⟩ := SmallLevelLaurentTwoCoordinateGerms.leading_kernel
    X Y Z W A B (fun _ => 1) F rows s hX hY hZ hW hA hB analyticAt_const
    hx hy hz hw hF hpole rows_support hrows
  exact ⟨v,first_coordinate_ne_zero (X s) (Y s) (Z s) (W s) (A s) (B s) v hx hy hv hvr,hvr⟩

#print axioms rows_support
#print axioms first_coordinate_ne_zero
#print axioms pole_first_chart
end SmallLevelTwentySixGermFirstEight
end
end
