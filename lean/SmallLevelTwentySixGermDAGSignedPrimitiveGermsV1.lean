module
public import SmallLevelTwentySixGermDAGSignedInputGermsV1
public import SmallLevelTwentySixGermDAGPrimitiveGermsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGermSources SmallLevelPrimeRates QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGrid (phase badParameter)
open QuantitativeArithmeticSevenLaurentRows SmallLevelLaurentPhysicalSubstitution

/-- All ninety primitive polynomial rows are analytic germs of the actual
continued functions in the MMM chart. Lower layers may have arbitrary
pole orders; no primitive-row or elimination assertion is a hypothesis. -/
theorem signed_original_primitive_germs {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v)
    (i : Fin 90) :
    HasAnalyticGerm (fun z => eval (u*parameter 2 m z) ((parameter 3 m z)^2)
      (v*parameter 13 m z) ((parameter 5 m z)^2)
      (badParameter f 3*parameter 3 m z) (badParameter f 5*parameter 5 m z)
      1 (replayVector m S.G z) (primitiveRows i)) x := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  apply unit_normalization_germ (fun z => u*parameter 2 m z) (parameter 3 m)
    (fun z => v*parameter 13 m z) (parameter 5 m)
    (badParameter f 3) (badParameter f 5) x (normalizationCoefficient i) (normalizationExponent i)
    (replayVector m S.G) (rawRows i) (primitiveRows i)
    (normalizationCoefficient_ne_zero i) (normalization_certificate i)
  · exact analyticAt_const.mul (parameter_analytic 2 m (by decide) x)
  · exact parameter_analytic 3 m (by decide) x
  · exact analyticAt_const.mul (parameter_analytic 13 m (by decide) x)
  · exact parameter_analytic 5 m (by decide) x
  · exact fun z => mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) z)
  · exact parameter_ne_zero 3 m (by decide)
  · exact fun z => mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) z)
  · exact parameter_ne_zero 5 m (by decide)
  · obtain ⟨p,hd,hperm⟩ := rawRows_derived i
    have hh := signed_original_derived_germ S x u v hu hv hshift hx hx1 hη hs2 hs13 hd
    apply hh.congr
    apply Filter.Eventually.of_forall
    intro z
    dsimp only
    unfold eval
    exact (hperm.map _).sum_eq

#print axioms signed_original_primitive_germs
end SmallLevelTwentySixGermDAG
