module
public import SmallLevelLaurentPhysicalSubstitutionTheoryV4
public import SmallLevelTwentySixGermDAGRawGermsV1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGermSources SmallLevelPrimeRates QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGrid (phase badParameter)
open QuantitativeArithmeticSevenLaurentRows SmallLevelLaurentPhysicalSubstitution

def primitiveRows : Fin 90→Poly :=
  ![SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row01.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row05.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row07.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row08.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row09.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row10.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row11.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row12.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row13.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row14.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row15.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row16.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row17.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row18.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row19.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row20.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row21.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row22.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row23.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row24.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row25.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row26.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row27.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row28.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row29.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row30.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row31.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row32.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row33.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row34.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row35.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row36.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row37.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row38.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row39.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row40.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row41.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row42.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row43.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row44.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row45.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row46.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row47.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row48.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row49.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row50.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row51.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row52.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row53.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row54.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row55.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row56.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row57.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row58.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row59.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row60.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row61.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row62.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row63.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row64.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row65.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row66.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row67.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row68.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row69.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row70.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row71.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row72.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row73.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row74.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row75.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row76.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row77.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row78.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row79.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row80.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row81.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row82.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row83.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row84.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row85.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row86.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row87.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row88.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row89.primitiveData]

def normalizationCoefficient : Fin 90→ℚ :=
  ![(-32448/5),936,1,(-936),2,104,2,480,2,(-2),109512,(-109512),68445000,1752192,(-5000),6480000,(-109512),(-13520000),(-68445000),(-21632),5000,(-109512),(-13520000),109512,21632,845000,(-6480000),(-109512),6480000,104,(-405000),(-1752192),27378,(-101250),1752192,(-78),936,(-234),(-234),(-936),(-468),(-144),104,(-200),(-208),208,200,(-400),104,(-800),1280,(-832/5),405000,(-21632),(-200),(-416),416,200,(8112/5),(-384000),(-200),400,12168,(-1600/9),(-21632),(-1752192),109512,109512,438048,41472,1752192,(-10816),(-160000),43264,40000,10816,(-40000),(-43264),160000,(-10816),640000,(-1024000),(86528/5),40000,173056,(-173056),(-40000),40000,(-160000),(2560000/81)]

def normalizationExponent : Fin 90→ℤ×ℤ×ℤ×ℤ :=
  ![(-4,0,0,0),(-4,-2,0,0),(-1,-2,0,0),(-4,-2,0,0),(-3,-2,1,-2),(-4,0,0,0),(-2,-2,1,-2),(-5,-2,1,-2),(-5,0,1,-2),(-3,-2,1,-2),(-3,-2,0,0),(-3,-2,0,0),(-3,-2,0,-2),(-5,-2,0,0),(-3,0,1,-2),(-5,-2,1,-2),(-3,-2,0,0),(-5,0,0,-2),(-3,-2,0,-2),(-5,0,0,0),(-3,0,1,-2),(-3,-2,0,0),(-5,0,0,-2),(-3,-2,0,0),(-5,0,0,0),(-3,0,0,-2),(-5,-2,1,-2),(-3,-2,0,0),(-5,-2,1,-2),(-4,-2,0,0),(-3,-2,1,-2),(-5,-2,0,0),(-2,-2,0,0),(-2,-2,1,-2),(-5,-2,0,0),(-2,-2,0,0),(-4,-2,0,0),(-2,-2,0,0),(-2,-2,0,0),(-4,-2,0,0),(-3,-2,0,0),(-5,-2,1,0),(-3,-2,0,0),(-3,-2,1,-2),(-4,-2,0,0),(-4,-2,0,0),(-3,-2,1,-2),(-4,-2,1,-2),(-3,-2,0,0),(-5,-2,1,-2),(-5,-2,1,-2),(-3,-2,0,0),(-3,-2,1,-2),(-5,0,0,0),(-3,-2,1,-2),(-5,-2,0,0),(-5,-2,0,0),(-3,-2,1,-2),(-3,-2,0,0),(-6,-2,1,-2),(-3,-2,1,-2),(-4,-2,1,-2),(-3,-2,0,0),(-6,0,1,-2),(-5,-2,0,0),(-5,-2,0,0),(-3,-2,0,0),(-3,-2,0,0),(-4,-2,0,0),(-6,-2,1,0),(-5,-2,0,0),(-4,-2,0,0),(-5,-2,1,-2),(-5,-2,0,0),(-4,-2,1,-2),(-4,-2,0,0),(-4,-2,1,-2),(-5,-2,0,0),(-5,-2,1,-2),(-4,-2,0,0),(-6,-2,1,-2),(-6,-2,1,-2),(-4,-2,0,0),(-4,-2,1,-2),(-6,-2,0,0),(-6,-2,0,0),(-4,-2,1,-2),(-4,-2,1,-2),(-5,-2,1,-2),(-7,0,1,-2)]

theorem normalizationCoefficient_ne_zero : ∀ i : Fin 90,normalizationCoefficient i≠0 := by
  decide +kernel

theorem normalization_certificate (i : Fin 90) :
    rawRows i=shift (normalizationCoefficient i)
      ((normalizationExponent i).1,(normalizationExponent i).2.1,
        (normalizationExponent i).2.2.1,(normalizationExponent i).2.2.2,0,0,0)
      (physicalRows (primitiveRows i)) := by
  fin_cases i
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row01.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row05.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row07.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row08.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row09.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row10.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row11.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row12.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row13.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row14.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row15.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row16.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row17.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row18.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row19.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row20.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row21.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row22.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row23.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row24.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row25.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row26.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row27.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row28.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row29.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row30.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row31.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row32.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row33.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row34.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row35.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row36.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row37.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row38.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row39.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row40.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row41.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row42.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row43.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row44.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row45.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row46.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row47.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row48.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row49.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row50.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row51.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row52.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row53.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row54.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row55.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row56.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row57.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row58.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row59.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row60.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row61.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row62.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row63.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row64.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row65.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row66.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row67.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row68.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row69.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row70.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row71.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row72.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row73.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row74.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row75.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row76.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row77.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row78.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row79.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row80.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row81.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row82.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row83.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row84.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row85.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row86.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row87.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row88.normalized_data
  · exact SmallLevelTwentySixGermPrimitiveSparseMMM.Row89.normalized_data

/-- All ninety primitive polynomial rows are analytic germs of the actual
continued functions in the MMM chart. Lower layers may have arbitrary
pole orders; no primitive-row or elimination assertion is a hypothesis. -/
theorem original_primitive_germs {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -1) (hs2 : badParameter f 2= -1) (hs13 : badParameter f 13= -1)
    (i : Fin 90) :
    HasAnalyticGerm (fun z => eval (parameter 2 m z) ((parameter 3 m z)^2)
      (parameter 13 m z) ((parameter 5 m z)^2)
      (badParameter f 3*parameter 3 m z) (badParameter f 5*parameter 5 m z)
      1 (replayVector m S.G z) (primitiveRows i)) x := by
  apply unit_normalization_germ (parameter 2 m) (parameter 3 m) (parameter 13 m) (parameter 5 m)
    (badParameter f 3) (badParameter f 5) x (normalizationCoefficient i) (normalizationExponent i)
    (replayVector m S.G) (rawRows i) (primitiveRows i)
    (normalizationCoefficient_ne_zero i) (normalization_certificate i)
  · exact parameter_analytic 2 m (by decide) x
  · exact parameter_analytic 3 m (by decide) x
  · exact parameter_analytic 13 m (by decide) x
  · exact parameter_analytic 5 m (by decide) x
  · exact parameter_ne_zero 2 m (by decide)
  · exact parameter_ne_zero 3 m (by decide)
  · exact parameter_ne_zero 13 m (by decide)
  · exact parameter_ne_zero 5 m (by decide)
  · exact original_raw_germs S x hshift hx hx1 hη hs2 hs13 i

#print axioms normalization_certificate
#print axioms original_primitive_germs
end SmallLevelTwentySixGermDAG
