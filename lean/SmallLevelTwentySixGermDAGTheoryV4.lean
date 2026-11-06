module

public import QuantitativeArithmeticSmallLevelTwentySixExceptionalTheoryV4
public import SmallLevelTwentySixGermFullFirstChartV1
public import SmallLevelTwentySixGermThirteenTheoryV4
public import SmallLevelTwentySixPariFirstChartTheoryV4
public import SmallLevelTwentySixPariGenericEliminationTheoryV4
public import SmallLevelTwentySixPariRawThirteenV1
public import SmallLevelTwentySixPariRemainderFamilyV4
public import SmallLevelTwentySixPariSourceBridgeTheoryV4
public import SmallLevelTwentySixPariSourcePivotsTheoryV4
public import SmallLevelTwentySixSource89SmallBridgeV1

/-! Consolidated chapter: SmallLevelTwentySixGermDAG. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixPariOriginalPoleFactorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)

/-- A direct exceptional-factor exclusion for the actual original pole system. -/
theorem original_pole_x_ne_two {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (x u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) x<0) : u*parameter 2 m x≠2 := by
  obtain ⟨θ,hθ⟩:=original_full_first_chart S T x u v hu hv hshift hx hx1 hη hs2 hs13 hpole
  apply SmallLevelTwentySixPariFirstChart.first_chart_x_ne_two
    (u*parameter 2 m x) ((parameter 3 m x)^2)
    (v*parameter 13 m x) ((parameter 5 m x)^2)
    (badParameter f 3*parameter 3 m x) (badParameter f 5*parameter 5 m x) θ
  exact hθ 0

#print axioms original_pole_x_ne_two
end SmallLevelTwentySixGermDAG
end
end

/-! ## SmallLevelTwentySixPariOriginalPoleExclusionSmallV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)
open SmallLevelTwentySixPariFirstChart

/-- Exclusion of a rightmost original pole in the signed MMM family, away
from the two Taylor normalization points. All polynomial premises come from
one common leading vector for the original thirteen germ equations. -/
theorem original_signed_mmm_no_pole_small {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (s u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) (hs1 : s≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) s<0) : False := by
  obtain ⟨θ,hθ⟩:=SmallLevelTwentySixGermThirteen.original_full_chart
    S T s u v hu hv hshift hs hs1 hη hs2 hs13 hpole
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) s)
  have hY:=pow_ne_zero 2 (parameter_ne_zero 3 m (by decide) s)
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) s)
  have hW:=pow_ne_zero 2 (parameter_ne_zero 5 m (by decide) s)
  have hc:=QuantitativeArithmeticSmallLevelTwentySixExceptional.original_pole_constant_ne_zero
    S T s u v hu hv hshift hs hs1 hη hs2 hs13 hpole
  obtain ⟨hq,hl,hcurve⟩:=SmallLevelTwentySixPariSourcePivots.thirteen_low_equations
    _ _ _ _ _ _ θ hX hθ
  have hlc:= (mul_eq_zero.mp hcurve).resolve_left hc
  have hraw:=SmallLevelTwentySixPariRawThirteen.raw_rows_zero
    _ _ _ _ _ _ θ hX hY hZ hW hθ
  have hr87:=SmallLevelTwentySixPariSourceBridge.source87_resultant_zero
    _ _ _ _ _ _ θ hX (hraw 0) (hraw 4) (hraw 6) (hraw 8) (hraw 11)
  have hr89:=SmallLevelTwentySixSource89SmallBridge.source89_resultant_zero
    _ _ _ _ _ _ θ hX (hraw 0) (hraw 4) (hraw 6) (hraw 8) (hraw 12)
  have h87:=SmallLevelTwentySixPariRemainder87.generic_remainder_zero
    _ _ _ _ _ _ θ hq hl hc hr87
  have h89:=SmallLevelTwentySixPariRemainder89.generic_remainder_zero
    _ _ _ _ _ _ θ hq hl hc hr89
  exact SmallLevelTwentySixPariGenericElimination.no_signed_reduced_rows m s u
    (v*parameter 13 m s) ((parameter 5 m s)^2)
    (badParameter f 3*parameter 3 m s) (badParameter f 5*parameter 5 m s) θ hu
    (original_pole_x_ne_two S T s u v hu hv hshift hs hs1 hη hs2 hs13 hpole)
    hlc h87 h89

#print axioms original_signed_mmm_no_pole_small
end SmallLevelTwentySixGermDAG
end
end
