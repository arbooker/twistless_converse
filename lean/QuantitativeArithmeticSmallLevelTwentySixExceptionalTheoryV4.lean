module

public import SmallLevelTwentySixExceptionalSevenPhysicalTheoryV4
public import SmallLevelTwentySixPariOriginalPoleCurveV1
public import SmallLevelTwentySixRootTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySixExceptional. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySixExceptionalRowsV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixExceptional
open SmallLevelTwentySixPariFirstChart QuantitativeArithmeticSevenLaurentRows

def thetaMultiplier (x y : ℂ) : ℂ :=
  -30*(350*x^6+1500*x^5*y-1450*x^5-675*x^4*y^2-7650*x^4*y-60*x^4+
    4050*x^3*y^2+13065*x^3*y-5930*x^3-8775*x^2*y^2-4095*x^2*y+21418*x^2+
    8100*x*y^2-10920*x*y-20160*x-2700*y^2+8100*y-5400)

/-- A polynomial identity, with no division by a potentially zero coefficient. -/
theorem theta_certificate (x y z w a b : ℂ) :
    thetaMultiplier x y*constantTerm x y+
      3375*(x-2)^3*(x-1)*(2*x^2+3*x*y-6*x-3*y+3)*
        SmallLevelTwentySixPariIdentity004.p2 x y z w a b 0+
      (-30375)*(x-2)^3*(x-1)*(x*y-y+1)*source3 x y z w a b 0=
      (-26)*x^2*SmallLevelTwentySixExceptionalCurve.extraFactor7 x y := by
  unfold thetaMultiplier constantTerm SmallLevelTwentySixPariIdentity004.p2 source3
    SmallLevelTwentySixExceptionalCurve.extraFactor7
  ring

def linearMultiplier (x y : ℂ) : ℂ :=
  60*x*(1427*x^4+735*x^3*y-3064*x^3-2880*x^2*y-5683*x^2+
    3495*x*y+10800*x-1350*y-2700)

theorem linear_certificate (x y z w b θ : ℂ) :
    linearMultiplier x y*constantTerm x y+
      (-10530)*x*(x-2)^2*(x-1)*(x+5)*
        SmallLevelTwentySixPariIdentity004.p2 x y z w ((9*x+5)/5) b θ+
      4860*x*(x-2)^2*(x-1)*(9*x+5*y+10)*source3 x y z w ((9*x+5)/5) b θ=
      26*x^2*SmallLevelTwentySixPariFinalFactors.factor6 x := by
  unfold linearMultiplier constantTerm SmallLevelTwentySixPariIdentity004.p2 source3
    SmallLevelTwentySixPariFinalFactors.factor6
  ring

/-- On the exceptional coefficient locus, three actual primitive rows force
one of the two factors already excluded by the physical norm estimates. -/
theorem exceptional_branches (x y z w a b θ : ℂ) (hx : x≠0)
    (hc : constantTerm x y=0)
    (h0 : eval x y z w a b 1 (fun i => if i=0 then 1 else θ)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData=0)
    (h2 : eval x y z w a b 1 (fun i => if i=0 then 1 else θ)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData=0)
    (h3 : eval x y z w a b 1 (fun i => if i=0 then 1 else θ)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData=0) :
    SmallLevelTwentySixPariFinalFactors.factor6 x=0 ∨
      SmallLevelTwentySixExceptionalCurve.extraFactor7 x y=0 := by
  have hs := exceptional_split x y z w a b θ h0 hc
  rw [source2_binding] at h2
  rw [source3_binding] at h3
  rcases hs with hl|rfl
  · have hx2 := (constant_zero_avoids_one_two x y hc).2
    have hi : (x-2)*(5*a-9*x-5)=10*linearTerm x a := by
      unfold linearTerm
      ring
    rw [hl,mul_zero] at hi
    have ha0 := (mul_eq_zero.mp hi).resolve_left (sub_ne_zero.mpr hx2)
    have ha : a=(9*x+5)/5 := by linear_combination ha0/5
    rw [ha] at h2 h3
    have he := linear_certificate x y z w b θ
    rw [hc,h2,h3] at he
    simp only [mul_zero,zero_add] at he
    exact Or.inl ((mul_eq_zero.mp he.symm).resolve_left
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)))
  · have he := theta_certificate x y z w a b
    rw [hc,h2,h3] at he
    simp only [mul_zero,zero_add] at he
    exact Or.inr ((mul_eq_zero.mp he.symm).resolve_left
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)))

#print axioms theta_certificate
#print axioms linear_certificate
#print axioms exceptional_branches
end QuantitativeArithmeticSmallLevelTwentySixExceptional
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixOriginalExceptionalV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixExceptional
open SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)
open SmallLevelTwentySixGermDAG SmallLevelTwentySixPariFirstChart

/-- The exceptional coefficient is nonzero at every original highest pole
away from the two Taylor normalization points. No additional source equations
or elimination consequences are assumed. -/
theorem original_pole_constant_ne_zero {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (x u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) x<0) :
    constantTerm (u*parameter 2 m x) ((parameter 3 m x)^2)≠0 := by
  intro hc
  obtain ⟨θ,hθ⟩ := original_full_first_chart S T x u v hu hv hshift hx hx1 hη hs2 hs13 hpole
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hun : ‖u‖=1 := by rcases hu with rfl|rfl <;> norm_num
  have hX : u*parameter 2 m x≠0 := mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have he := exceptional_branches (u*parameter 2 m x) ((parameter 3 m x)^2)
    (v*parameter 13 m x) ((parameter 5 m x)^2)
    (badParameter f 3*parameter 3 m x) (badParameter f 5*parameter 5 m x) θ
    hX hc (hθ 0) (hθ 2) (hθ 3)
  apply SmallLevelTwentySixExceptionalSevenPhysical.no_signed_exceptional_branches (x-(m:ℂ)) u hun
  · rw [SmallLevelTwentySixRoot.parameter_three_squared] at hc
    simpa only [parameter,Nat.cast_ofNat] using hc
  · rw [SmallLevelTwentySixRoot.parameter_three_squared] at he
    simpa only [parameter,Nat.cast_ofNat] using he

/-- Consequently every such original pole lies on the low-degree curve
itself, rather than merely the union with an exceptional coefficient locus. -/
theorem original_pole_low_curve {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (x u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) x<0) :
    curve (u*parameter 2 m x) ((parameter 3 m x)^2)=0 :=
  (mul_eq_zero.mp (original_pole_low_curve_product S T x u v hu hv hshift hx hx1 hη hs2 hs13 hpole)).resolve_left
    (original_pole_constant_ne_zero S T x u v hu hv hshift hx hx1 hη hs2 hs13 hpole)

#print axioms original_pole_constant_ne_zero
#print axioms original_pole_low_curve
end QuantitativeArithmeticSmallLevelTwentySixExceptional
end
end
