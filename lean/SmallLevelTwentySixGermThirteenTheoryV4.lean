module

public import SmallLevelTwentySixGermFourteenDataV1
public import SmallLevelTwentySixIntegerRowIndexOriginalGermSeriesV4

/-! Consolidated chapter: SmallLevelTwentySixGermThirteen. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixGermThirteenDataV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermThirteen
open QuantitativeArithmeticSevenLaurentRows
open SmallLevelTwentySixGermDAG SmallLevelTwentySixGermSources

/-- Keep the eleven small rows and syzygies87/89; omit syzygy88. -/
def embedding (i : Fin 13) : Fin 14 :=
  if h : i.val<12 then ⟨i.val,by omega⟩ else 13

def rows (i : Fin 13) : Poly := SmallLevelTwentySixGermFourteen.rows (embedding i)

theorem rows_support (i : Fin 13) : ∀ t∈rows i,t.2.1=0 ∨ t.2.1=1 :=
  SmallLevelTwentySixGermFourteen.rows_support (embedding i)

theorem first_eight (i : Fin 8) :
    rows ⟨i.val,by omega⟩=SmallLevelTwentySixGermFirstEight.rows i := by
  have hi : i.val<12 := by omega
  simpa only [rows,embedding,dite_eq_left hi] using SmallLevelTwentySixGermFourteen.first_eight i

def primitiveIndex (i : Fin 11) : Fin 90 :=
  if h : i.val<10 then ⟨i.val,by omega⟩ else 29

theorem rows_primitive : ∀ i : Fin 11,
    rows ⟨i.val,by omega⟩=primitiveRows (primitiveIndex i) := by decide +kernel

theorem row_eleven : rows 11=
    SmallLevelIntegerLaurentGerm.toRat SmallLevelTwentySixIntegerRow87Transpose.outputData := by
  decide +kernel

theorem row_twelve : rows 12=
    SmallLevelIntegerLaurentGerm.toRat SmallLevelTwentySixIntegerRow89Transpose.outputData := by
  decide +kernel

theorem eval_replay_top (m : ℕ) (G : ℂ→Fin 320→ℂ) (z X Y Z W A B : ℂ)
    (i : Fin 13) :
    eval X Y Z W A B 1 (replayVector m G z) (rows i)=
      eval X Y Z W A B 1 (fun j => if j=0 then G z (topIndex 0) else G z (topIndex 1))
        (rows i) :=
  SmallLevelTwentySixGermFourteen.eval_replay_top m G z X Y Z W A B (embedding i)

#print axioms rows_support
#print axioms rows_primitive
#print axioms eval_replay_top
end SmallLevelTwentySixGermThirteen
end
end

/-! ## SmallLevelTwentySixGermThirteenKernelV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermThirteen
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm

theorem first_coordinate_ne_zero (X Y Z W A B : ℂ) (v : Fin 2→ℂ)
    (hX : X≠0) (hY : Y≠0) (hv : v≠0)
    (hrows : ∀ i,eval X Y Z W A B 1 (fun j => if j=0 then v 0 else v 1) (rows i)=0) :
    v 0≠0 := by
  apply SmallLevelTwentySixGermFirstEight.first_coordinate_ne_zero X Y Z W A B v hX hY hv
  intro i
  simpa only [first_eight i] using hrows ⟨i.val,by omega⟩

/-- A pole detected in the two top coordinates lies in the first chart.
This uses the fourteen rows on one common leading vector. -/
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

#print axioms first_coordinate_ne_zero
#print axioms pole_first_chart
end SmallLevelTwentySixGermThirteen
end
end

/-! ## SmallLevelTwentySixGermThirteenOriginalChartV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermThirteen
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGermDAG SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)

theorem original_rows_germs {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v) (i : Fin 13) :
    HasAnalyticGerm (fun z => eval (u*parameter 2 m z) ((parameter 3 m z)^2)
      (v*parameter 13 m z) ((parameter 5 m z)^2)
      (badParameter f 3*parameter 3 m z) (badParameter f 5*parameter 5 m z)
      1 (replayVector m S.G z) (rows i)) x := by
  by_cases h11 : i=11
  · subst i
    rw [row_eleven]
    simpa only [SmallLevelIntegerLaurentGerm.eval_toRat] using
      SmallLevelTwentySixIntegerRow87Transpose.original_output_germ S x u v hu hv hshift hx hx1 hη hs2 hs13
  by_cases h12 : i=12
  · subst i
    rw [row_twelve]
    simpa only [SmallLevelIntegerLaurentGerm.eval_toRat] using
      SmallLevelTwentySixIntegerRow89Transpose.original_output_germ S x u v hu hv hshift hx hx1 hη hs2 hs13
  have hi : i.val<11 := by
    have hi13:=i.isLt
    by_contra hn
    have he : i.val=11 ∨ i.val=12 := by omega
    rcases he with he|he
    · exact h11 (Fin.ext he)
    · exact h12 (Fin.ext he)
  let j : Fin 11:=⟨i.val,hi⟩
  have hrow : rows i=primitiveRows (primitiveIndex j) := rows_primitive j
  rw [hrow]
  exact signed_original_primitive_germs S x u v hu hv hshift hx hx1 hη hs2 hs13 (primitiveIndex j)

/-- The thirteen elimination equations share one normalized leading vector.
The two large rows are the integer polynomial syzygies87 and89 of original rows. -/
theorem original_top_chart {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v)
    (hpole : ∃ i : Fin 2,meromorphicOrderAt (fun z => S.G z (topIndex i)) x<0) :
    ∃ θ : ℂ,∀ i : Fin 13,
      eval (u*parameter 2 m x) ((parameter 3 m x)^2)
      (v*parameter 13 m x) ((parameter 5 m x)^2)
      (badParameter f 3*parameter 3 m x) (badParameter f 5*parameter 5 m x)
        1 (fun j => if j=0 then 1 else θ) (rows i)=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have hY:=pow_ne_zero 2 (parameter_ne_zero 3 m (by decide) x)
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) x)
  have hW:=pow_ne_zero 2 (parameter_ne_zero 5 m (by decide) x)
  have hg : ∀ i,HasAnalyticGerm (fun z => eval (u*parameter 2 m z) ((parameter 3 m z)^2)
      (v*parameter 13 m z) ((parameter 5 m z)^2)
      (badParameter f 3*parameter 3 m z) (badParameter f 5*parameter 5 m z)
      1 (fun j => if j=0 then S.G z (topIndex 0) else S.G z (topIndex 1)) (rows i)) x := by
    intro i
    apply (original_rows_germs S x u v hu hv hshift hx hx1 hη hs2 hs13 i).congr
    apply Filter.Eventually.of_forall
    intro z
    exact eval_replay_top m S.G z _ _ _ _ _ _ i
  obtain ⟨w,hw0,hwr⟩:=pole_first_chart
    (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
    (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
    (fun z => badParameter f 3*parameter 3 m z)
    (fun z => badParameter f 5*parameter 5 m z)
    (fun i z => S.G z (topIndex i)) x
    (analyticAt_const.mul (parameter_analytic 2 m (by decide) x))
    ((parameter_analytic 3 m (by decide) x).pow 2)
    (analyticAt_const.mul (parameter_analytic 13 m (by decide) x))
    ((parameter_analytic 5 m (by decide) x).pow 2)
    (analyticAt_const.mul (parameter_analytic 3 m (by decide) x))
    (analyticAt_const.mul (parameter_analytic 5 m (by decide) x))
    hX hY hZ hW (fun i => (S.meromorphic (topIndex i) x).meromorphicAt)
    hpole hg
  exact SmallLevelLaurentProjectiveChart.normalize_first _ _ _ _ _ _ _ rows w hw0 hwr

theorem original_full_chart {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (x u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) x<0) :
    ∃ θ : ℂ,∀ i : Fin 13,
      eval (u*parameter 2 m x) ((parameter 3 m x)^2)
        (v*parameter 13 m x) ((parameter 5 m x)^2)
        (badParameter f 3*parameter 3 m x) (badParameter f 5*parameter 5 m x)
        1 (fun j => if j=0 then 1 else θ) (rows i)=0 := by
  have hG := S.grid_G_eq T
  have htshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => T.G z j) (x+n) := by
    simpa only [hG] using hshift
  have htpole : ∃ j,meromorphicOrderAt (fun z => T.G z j) x<0 := by
    simpa only [hG] using hpole
  have htop := T.pole_in_replay_top x u v hu hv htshift hη hs2 hs13 htpole
  have hstop : ∃ i : Fin 2,meromorphicOrderAt (fun z => S.G z (topIndex i)) x<0 := by
    simpa only [hG,topIndex,SmallLevelTwentySixGrid.replayTopIndex] using htop
  exact original_top_chart S x u v hu hv hshift hx hx1 hη hs2 hs13 hstop

#print axioms original_full_chart
#print axioms rows_support
#print axioms original_rows_germs
#print axioms original_top_chart
end SmallLevelTwentySixGermThirteen
end
end
