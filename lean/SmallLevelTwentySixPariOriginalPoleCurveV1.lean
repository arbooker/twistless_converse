module
public import SmallLevelTwentySixPariFirstChartTheoryV4
public import SmallLevelTwentySixGermFullFirstChartV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariFirstChart

def curve (x y : ℂ) : ℂ := lowCurve x y 0 0 0 0 0

end SmallLevelTwentySixPariFirstChart
namespace SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)
open SmallLevelTwentySixPariFirstChart

/-- Every original pole under the established normalization conditions lies
on the union of the exceptional coefficient locus and the low-degree curve. -/
theorem original_pole_low_curve_product {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (x u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) x<0) :
    constantTerm (u*parameter 2 m x) ((parameter 3 m x)^2)*
      curve (u*parameter 2 m x) ((parameter 3 m x)^2)=0 := by
  obtain ⟨θ,hθ⟩:=original_full_first_chart S T x u v hu hv hshift hx hx1 hη hs2 hs13 hpole
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hX : u*parameter 2 m x≠0 := mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have h:=source_low_curve_product (u*parameter 2 m x) ((parameter 3 m x)^2)
    (v*parameter 13 m x) ((parameter 5 m x)^2)
    (badParameter f 3*parameter 3 m x) (badParameter f 5*parameter 5 m x) θ hX
    (hθ 0) (hθ 2) (hθ 3)
  exact h

#print axioms original_pole_low_curve_product
end SmallLevelTwentySixGermDAG
