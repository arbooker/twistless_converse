module
public import SmallLevelTwentySixGermFirstEightTheoryV4
public import SmallLevelTwentySixGermDAGSignedPrimitiveGermsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGermSources SmallLevelPrimeRates QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGrid (phase badParameter)
open QuantitativeArithmeticSevenLaurentRows SmallLevelFiniteGridSupport
open SmallLevelTwentySixUnitMMM (support support_injective)

def topIndex : Fin 2→Fin 320 := ![110,222]

theorem replayVector_top (m : ℕ) (G : ℂ→Fin 320→ℂ) (z : ℂ) (i : Fin 2) :
    replayVector m G z i=G z (topIndex i) := by
  fin_cases i
  · change extend support (G z) (support 110)=G z 110
    exact extend_at support support_injective (G z) 110
  · change extend support (G z) (support 222)=G z 222
    exact extend_at support support_injective (G z) 222

theorem first_eight_rows (i : Fin 8) :
    primitiveRows ⟨i.val,lt_trans i.isLt (by decide)⟩=SmallLevelTwentySixGermFirstEight.rows i := by
  fin_cases i <;> rfl

theorem eval_first_eight_top (m : ℕ) (G : ℂ→Fin 320→ℂ) (z X Y Z W A B : ℂ)
    (i : Fin 8) :
    eval X Y Z W A B 1 (replayVector m G z) (SmallLevelTwentySixGermFirstEight.rows i)=
      eval X Y Z W A B 1 (fun j => if j=0 then G z (topIndex 0) else G z (topIndex 1))
        (SmallLevelTwentySixGermFirstEight.rows i) := by
  rw [SmallLevelLaurentTwoCoordinateGerms.eval_two_coordinates X Y Z W A B 1 _ _
    (SmallLevelTwentySixGermFirstEight.rows_support i)]
  rw [SmallLevelLaurentTwoCoordinateGerms.eval_two_coordinates X Y Z W A B 1 _ _
    (SmallLevelTwentySixGermFirstEight.rows_support i)]
  have h0 : replayVector m G z 0=G z (topIndex 0) := by
    simpa using replayVector_top m G z (0 : Fin 2)
  have h1 : replayVector m G z 1=G z (topIndex 1) := by
    simpa using replayVector_top m G z (1 : Fin 2)
  rw [h0,h1]
  simp

/-- A pole in either actual top continuation gives a first-chart kernel
of the primitive rows, using only the original continued source equations. -/
theorem original_top_first_chart {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v)
    (hpole : ∃ i : Fin 2,meromorphicOrderAt (fun z => S.G z (topIndex i)) x<0) :
    ∃ w : Fin 2→ℂ,w 0≠0 ∧ ∀ i : Fin 8,
      eval (u*parameter 2 m x) ((parameter 3 m x)^2)
        (v*parameter 13 m x) ((parameter 5 m x)^2)
        (badParameter f 3*parameter 3 m x) (badParameter f 5*parameter 5 m x)
        1 (fun j => if j=0 then w 0 else w 1) (SmallLevelTwentySixGermFirstEight.rows i)=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  apply SmallLevelTwentySixGermFirstEight.pole_first_chart
    (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
    (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
    (fun z => badParameter f 3*parameter 3 m z)
    (fun z => badParameter f 5*parameter 5 m z) (fun i z => S.G z (topIndex i)) x
  · exact analyticAt_const.mul (parameter_analytic 2 m (by decide) x)
  · exact (parameter_analytic 3 m (by decide) x).pow 2
  · exact analyticAt_const.mul (parameter_analytic 13 m (by decide) x)
  · exact (parameter_analytic 5 m (by decide) x).pow 2
  · exact analyticAt_const.mul (parameter_analytic 3 m (by decide) x)
  · exact analyticAt_const.mul (parameter_analytic 5 m (by decide) x)
  · exact mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  · exact pow_ne_zero 2 (parameter_ne_zero 3 m (by decide) x)
  · exact mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) x)
  · exact pow_ne_zero 2 (parameter_ne_zero 5 m (by decide) x)
  · exact fun i => (S.meromorphic (topIndex i) x).meromorphicAt
  · exact hpole
  · intro i
    have hg := signed_original_primitive_germs S x u v hu hv hshift hx hx1 hη hs2 hs13
      ⟨i.val,lt_trans i.isLt (by decide)⟩
    rw [first_eight_rows i] at hg
    apply hg.congr
    apply Filter.Eventually.of_forall
    intro z
    exact eval_first_eight_top m S.G z _ _ _ _ _ _ i

#print axioms replayVector_top
#print axioms original_top_first_chart
end SmallLevelTwentySixGermDAG
