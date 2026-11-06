module
public import SmallLevelTwentySixMMPPariTheoryV4
public import SmallLevelTwentySixExceptionalCurveV1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelTwentySixMMPPariExceptional
open SmallLevelTwentySixMMPPari
def e0p0 (x y z w a b u : ℂ) : ℂ := (((-1)*y)*x+((1)*y+(-1)))
def e0p1 (x y z w a b u : ℂ) : ℂ := ((((-5/132)*x+((-25/297)*y+(25/132)))*x+((25/99)*y+(-35/66)))*x+((-50/297)*y+((13/99)*a+(1))))
def e0p2 (x y z w a b u : ℂ) : ℂ := (13/99)
def e0p3 (x y z w a b u : ℂ) : ℂ := ((((-1)*x+(1))*x+(((1)*y+((1)*a+(1)))*y))*x+(((-1)*y+((-1)*a))*y+((1)*a+(1))))
def e0p4 (x y z w a b u : ℂ) : ℂ := ((((((5/132)*y)*x+(((25/297)*y+(-5/22))*y+(-37/396)))*x+(((-100/297)*y+(955/1188))*y+(-23/396)))*x+(((164/297)*y+(-109/66))*y+(35/66)))*x+(((-89/297)*y+(347/297))*y+(-86/99)))
theorem identity0 (x y z w a b u : ℂ) :
    e0p0 x y z w a b u*e0p1 x y z w a b u+
      e0p2 x y z w a b u*e0p3 x y z w a b u=e0p4 x y z w a b u := by
  unfold e0p0 e0p1 e0p2 e0p3 e0p4
  ring
#print axioms identity0
def e1p0 (x y z w a b u : ℂ) : ℂ := (((((((-65/7128)*x+((25/594)*y+(65/792)))*x+((-175/594)*y+(-2287/7128)))*x+((257/297)*y+(1931/7128)))*x+((-71/54)*y+(1027/1485)))*x+((595/594)*y+(-14107/8910)))*x+((-89/297)*y+(86/99)))
def e1p1 (x y z w a b u : ℂ) : ℂ := ((((-1/3)*x+((-1/2)*y+(5/3)))*x+((3/2)*y+(-127/30)))*x+((-1)*y+(1)))
def e1p2 (x y z w a b u : ℂ) : ℂ := (((((1/4)*x+(-3/2))*x+(13/4))*x+(-3))*x+(1))
def e1p3 (x y z w a b u : ℂ) : ℂ := ((((((5/132)*y)*x+(((25/297)*y+(-5/22))*y+(-37/396)))*x+(((-100/297)*y+(955/1188))*y+(-23/396)))*x+(((164/297)*y+(-109/66))*y+(35/66)))*x+(((-89/297)*y+(347/297))*y+(-86/99)))
def e1p4 (x y z w a b u : ℂ) : ℂ := ((((((((((65/21384)*x+(-455/10692))*x+(923/3564))*x+(-208/243))*x+(168649/106920))*x+(-12623/17820))*x+(-165581/66825))*x+(26546/6075))*x+(-9464/4455))*x)
theorem identity1 (x y z w a b u : ℂ) :
    e1p0 x y z w a b u*e1p1 x y z w a b u+
      e1p2 x y z w a b u*e1p3 x y z w a b u=e1p4 x y z w a b u := by
  unfold e1p0 e1p1 e1p2 e1p3 e1p4
  ring
#print axioms identity1
def e2p0 (x y z w a b u : ℂ) : ℂ := (((-1)*y+((-1)*a+(-1)))*x+(((1)*a+(-1))*y+((1)*a^2+(-1))))
def e2p1 (x y z w a b u : ℂ) : ℂ := ((((-5/132)*x+((-25/297)*y+((-5/33)*u+(25/132))))*x+((25/99)*y+(((7/66)*u)*a+((13/33)*u+(-35/66)))))*x+((-50/297)*y+(((-7/33)*u+(13/99))*a+((-2/11)*u+(1)))))
def e2p2 (x y z w a b u : ℂ) : ℂ := (((-5/33)*x+((7/66)*a+(13/33)))*x+((-7/33)*a+(-2/11)))
def e2p3 (x y z w a b u : ℂ) : ℂ := ((((-1)*x+(1))*x+(((1)*y+((1)*a+((1)*u+(1))))*y+(((1)*u)*a+((1)*u))))*x+(((-1)*y+(((-1)*u+(-1))*a+((1)*u)))*y+((((-1)*u)*a+(1))*a+((1)*u+(1)))))
def e2p4 (x y z w a b u : ℂ) : ℂ := ((((((5/33)*x+((5/132)*y+((-3/44)*a+(-67/132))))*x+(((-20/297)*y+((-125/1188)*a+(-65/297)))*y+(((-5/132)*a+(17/132))*a+(14/33))))*x+((((13/594)*a+(112/297))*y+(((13/594)*a+(233/396))*a+(673/1188)))*y+(((25/132)*a+(1/6))*a+(1/132))))*x+((((-13/198)*a+(-196/297))*y+(((-13/198)*a+(-761/594))*a+(-437/594)))*y+(((-5/9)*a+(-125/198))*a+(-5/66))))*x+((((13/297)*a+(104/297))*y+(((52/297)*a+(104/99))*a+(-247/297)))*y+((((13/99)*a+(26/33))*a+(-52/99))*a+(-13/11))))
theorem identity2 (x y z w a b u : ℂ) :
    e2p0 x y z w a b u*e2p1 x y z w a b u+
      e2p2 x y z w a b u*e2p3 x y z w a b u=e2p4 x y z w a b u := by
  unfold e2p0 e2p1 e2p2 e2p3 e2p4
  ring
#print axioms identity2
def e3p0 (x y z w a b u : ℂ) : ℂ := (((((((3/88)*x+((391/23760)*y+((5/528)*a+(-43/176))))*x+(((-13/2376)*y+((-13/2376)*a+(-4487/23760)))*y+((-15/176)*a+(8221/13200))))*x+(((91/2376)*y+((91/2376)*a+(2423/2970)))*y+((152/495)*a+(-16361/19800))))*x+(((-13/132)*y+((-13/99)*a+(-10871/5940)))*y+(((-13/396)*a+(-731/990))*a+(4079/4950))))*x+(((65/594)*y+((13/54)*a+(3352/1485)))*y+(((13/99)*a+(613/495))*a+(-307/990))))*x+(((-13/297)*y+((-52/297)*a+(-364/297)))*y+(((-13/99)*a+(-91/99))*a+(-13/33))))
def e3p1 (x y z w a b u : ℂ) : ℂ := (((-9/10)*x+((1/2)*a+(13/10)))*x+((-1)*a+(1)))
def e3p2 (x y z w a b u : ℂ) : ℂ := ((((1/8)*x+(-3/4))*x+(3/2))*x+(-1))
def e3p3 (x y z w a b u : ℂ) : ℂ := ((((((5/33)*x+((5/132)*y+((-3/44)*a+(-67/132))))*x+(((-20/297)*y+((-125/1188)*a+(-65/297)))*y+(((-5/132)*a+(17/132))*a+(14/33))))*x+((((13/594)*a+(112/297))*y+(((13/594)*a+(233/396))*a+(673/1188)))*y+(((25/132)*a+(1/6))*a+(1/132))))*x+((((-13/198)*a+(-196/297))*y+(((-13/198)*a+(-761/594))*a+(-437/594)))*y+(((-5/9)*a+(-125/198))*a+(-5/66))))*x+((((13/297)*a+(104/297))*y+(((52/297)*a+(104/99))*a+(-247/297)))*y+((((13/99)*a+(26/33))*a+(-52/99))*a+(-13/11))))
def e3p4 (x y z w a b u : ℂ) : ℂ := (((((((((-31/2640)*x+((-133/13200)*y+(23/264)))*x+(((-83/23760)*y+(4027/29700))*y+(-6041/33000)))*x+(((37/660)*y+(-554/825))*y+(5207/66000)))*x+(((-7921/23760)*y+(194339/118800))*y+(-6361/99000)))*x+(((2921/2970)*y+(-6173/2970))*y+(167/8250)))*x+(((-1531/990)*y+(5747/4950))*y+(1271/825)))*x+(((1838/1485)*y+(226/1485))*y+(-1247/495)))*x+(((-13/33)*y+(-13/33))*y+(26/33)))
theorem identity3 (x y z w a b u : ℂ) :
    e3p0 x y z w a b u*e3p1 x y z w a b u+
      e3p2 x y z w a b u*e3p3 x y z w a b u=e3p4 x y z w a b u := by
  unfold e3p0 e3p1 e3p2 e3p3 e3p4
  ring
#print axioms identity3
def e4p0 (x y z w a b u : ℂ) : ℂ := ((((((((((-251/64800)*x+((-83/47520)*y+(41627/712800)))*x+((527/15840)*y+(-78377/237600)))*x+((-12083/47520)*y+(39751/47520)))*x+((9959/9504)*y+(-1289/2376)))*x+((-12269/4752)*y+(-127879/59400)))*x+((23297/5940)*y+(24221/4050)))*x+((-18/5)*y+(-27163/4050)))*x+((5431/2970)*y+(602/165)))*x+((-13/33)*y+(-26/33)))
def e4p1 (x y z w a b u : ℂ) : ℂ := ((((-1/3)*x+((-1/2)*y+(5/3)))*x+((3/2)*y+(-127/30)))*x+((-1)*y+(1)))
def e4p2 (x y z w a b u : ℂ) : ℂ := (((((1/4)*x+(-3/2))*x+(13/4))*x+(-3))*x+(1))
def e4p3 (x y z w a b u : ℂ) : ℂ := (((((((((-31/2640)*x+((-133/13200)*y+(23/264)))*x+(((-83/23760)*y+(4027/29700))*y+(-6041/33000)))*x+(((37/660)*y+(-554/825))*y+(5207/66000)))*x+(((-7921/23760)*y+(194339/118800))*y+(-6361/99000)))*x+(((2921/2970)*y+(-6173/2970))*y+(167/8250)))*x+(((-1531/990)*y+(5747/4950))*y+(1271/825)))*x+(((1838/1485)*y+(226/1485))*y+(-1247/495)))*x+(((-13/33)*y+(-13/33))*y+(26/33)))
def e4p4 (x y z w a b u : ℂ) : ℂ := (((((((((((((-7033/4276800)*x+(3601/267300))*x+(19409/2138400))*x+(-998699/2138400))*x+(2890277/1425600))*x+(-87347/28512))*x+(-727649/267300))*x+(194285/10692))*x+(-753467/24300))*x+(324961/12150))*x+(-52598/4455))*x+(208/99))*x)
theorem identity4 (x y z w a b u : ℂ) :
    e4p0 x y z w a b u*e4p1 x y z w a b u+
      e4p2 x y z w a b u*e4p3 x y z w a b u=e4p4 x y z w a b u := by
  unfold e4p0 e4p1 e4p2 e4p3 e4p4
  ring
#print axioms identity4
theorem binding0_1 (x y z w a b u : ℂ) : e0p1 x y z w a b u=c10 x y z w a b := by
  unfold e0p1 c10
  ring
theorem binding0_3 (x y z w a b u : ℂ) : e0p3 x y z w a b u=c30 x y z w a b := by
  unfold e0p3 c30
  ring
theorem binding1_1 (x y z w a b u : ℂ) : e1p1 x y z w a b u=c00 x y z w a b := by
  unfold e1p1 c00
  ring
theorem binding1_3 (x y z w a b u : ℂ) : e1p3 x y z w a b u=e0p4 x y z w a b u := by
  unfold e1p3 e0p4
  ring
theorem binding2_1 (x y z w a b u : ℂ) : e2p1 x y z w a b u=c10 x y z w a b+c11 x y z w a b*u := by
  unfold e2p1 c10 c11
  ring
theorem binding2_3 (x y z w a b u : ℂ) : e2p3 x y z w a b u=c30 x y z w a b+c31 x y z w a b*u := by
  unfold e2p3 c30 c31
  ring
theorem binding3_1 (x y z w a b u : ℂ) : e3p1 x y z w a b u=c01 x y z w a b := by
  unfold e3p1 c01
  ring
theorem binding3_3 (x y z w a b u : ℂ) : e3p3 x y z w a b u=e2p4 x y z w a b u := by
  unfold e3p3 e2p4
  ring
theorem binding4_1 (x y z w a b u : ℂ) : e4p1 x y z w a b u=c00 x y z w a b := by
  unfold e4p1 c00
  ring
theorem binding4_3 (x y z w a b u : ℂ) : e4p3 x y z w a b u=e3p4 x y z w a b u := by
  unfold e4p3 e3p4
  ring
theorem constant_binding (x y z w a b : ℂ) :
    c00 x y z w a b=SmallLevelTwentySixPariFirstChart.constantTerm x y := by
  unfold c00 SmallLevelTwentySixPariFirstChart.constantTerm
  ring

theorem factorization0 (x y z w a b u : ℂ) :
    e1p4 x y z w a b u=(13/534600:ℂ)*(x-1)*x*
      SmallLevelTwentySixExceptionalCurve.extraFactor7 x y := by
  unfold e1p4 SmallLevelTwentySixExceptionalCurve.extraFactor7
  ring

theorem factorization1 (x y z w a b u : ℂ) :
    e4p4 x y z w a b u=(-13/4276800:ℂ)*(x-2)^4*(x-1)*x*
      SmallLevelTwentySixPariFinalFactors.factor6 x := by
  unfold e4p4 SmallLevelTwentySixPariFinalFactors.factor6
  ring
#print axioms constant_binding
#print axioms factorization0
#print axioms factorization1
end SmallLevelTwentySixMMPPariExceptional
