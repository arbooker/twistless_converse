module
public import QuantitativeArithmeticSmallLevelTwentySixMMPEightRowsV1
public import QuantitativeArithmeticSmallLevelTwentySixMMPLowCurveTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySixMMPReducedSystemExclusionV1
public import SmallLevelTwentySixMMPPariSourceChainTheoryV4
public import SmallLevelTwentySixMMPPariTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPOriginalPoleExclusion
open SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)
open SmallLevelTwentySixMMPPari

/-- Exclude a rightmost original MMP pole away from the Taylor normalization
points. All polynomial equations are derived from the original germ systems. -/
theorem original_signed_mmp_no_pole {m : ℕ} {f : ℕ → ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (s u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) (hs1 : s≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13=v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) s<0) : False := by
  obtain ⟨θ,hsmall,h6,h7⟩ :=
    QuantitativeArithmeticSmallLevelTwentySixMMPEightRows.original_scalar_system
      S T s u v hu hv hshift hs hs1 hη hs2 hs13 hpole
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hx := mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) s)
  have hx2 : u*parameter 2 m s≠2 := by
    apply parameter_x_ne_two _ _ _ _ _ _ (fun j : ℕ => if j=0 then 1 else θ)
    · left
      norm_num
    · intro i
      exact hsmall ⟨i.val, by omega⟩
  have hc := QuantitativeArithmeticSmallLevelTwentySixMMPExceptional.original_constant_ne_zero
    S T s u v hu hv hshift hs hs1 hη hs2 hs13 hpole
  have hcc : c00 (u*parameter 2 m s) ((parameter 3 m s)^2)
      (v*parameter 13 m s) ((parameter 5 m s)^2)
      (badParameter f 3*parameter 3 m s) (badParameter f 5*parameter 5 m s)≠0 := by
    rw [SmallLevelTwentySixMMPPariExceptional.constant_binding]
    exact hc
  obtain ⟨hfirst,hsecond⟩ := SmallLevelTwentySixMMPPariSourceChain.reduced_equations
    _ _ _ _ _ _ θ hx hx2 hcc hsmall h6 h7
  have hlow := QuantitativeArithmeticSmallLevelTwentySixMMPLowCurve.original_low_curve
    S T s u v hu hv hshift hs hs1 hη hs2 hs13 hpole
  exact QuantitativeArithmeticSmallLevelTwentySixMMPReducedSystem.no_signed_parameters
    m s u (v*parameter 13 m s) ((parameter 5 m s)^2)
    (badParameter f 3*parameter 3 m s) (badParameter f 5*parameter 5 m s) θ
    hu hx2 hlow hfirst hsecond

#print axioms original_signed_mmp_no_pole
end QuantitativeArithmeticSmallLevelTwentySixMMPOriginalPoleExclusion
