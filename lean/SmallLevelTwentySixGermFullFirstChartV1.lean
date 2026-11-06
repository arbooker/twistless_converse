module
public import SmallLevelLaurentProjectiveChartV1
public import SmallLevelTwentySixCompatiblePoleSystemsV1
public import SmallLevelTwentySixGridTopPoleV1
public import SmallLevelTwentySixGermOriginalFirstChartV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)
open QuantitativeArithmeticSevenLaurentRows

/-- Every highest pole of the original grid, away from the two Taylor
normalization points, gives a normalized first-chart solution. Both source
systems are actual original continuations, with a common Fricke witness. -/
theorem original_full_first_chart {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (x u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) x<0) :
    ∃ θ : ℂ,∀ i : Fin 8,
      eval (u*parameter 2 m x) ((parameter 3 m x)^2)
        (v*parameter 13 m x) ((parameter 5 m x)^2)
        (badParameter f 3*parameter 3 m x) (badParameter f 5*parameter 5 m x)
        1 (fun j => if j=0 then 1 else θ) (SmallLevelTwentySixGermFirstEight.rows i)=0 := by
  have hG := S.grid_G_eq T
  have htshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => T.G z j) (x+n) := by
    simpa only [hG] using hshift
  have htpole : ∃ j,meromorphicOrderAt (fun z => T.G z j) x<0 := by
    simpa only [hG] using hpole
  have htop := T.pole_in_replay_top x u v hu hv htshift hη hs2 hs13 htpole
  have hstop : ∃ i : Fin 2,meromorphicOrderAt (fun z => S.G z (topIndex i)) x<0 := by
    simpa only [hG,topIndex,SmallLevelTwentySixGrid.replayTopIndex] using htop
  obtain ⟨w,hw,hwr⟩ := original_top_first_chart S x u v hu hv hshift hx hx1 hη hs2 hs13 hstop
  exact SmallLevelLaurentProjectiveChart.normalize_first _ _ _ _ _ _ _
    SmallLevelTwentySixGermFirstEight.rows w hw hwr

#print axioms original_full_first_chart
end SmallLevelTwentySixGermDAG
