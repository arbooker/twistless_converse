module

public import QuantitativeArithmeticSmallLevelTwentySixMMPExceptionalTheoryV4
public import SmallLevelTwentySixMMPPariTheoryV4
public import SmallLevelTwentySixPariFirstChartTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySixMMPLowCurve. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySixMMPLowCurveIdentitiesV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPLowCurve
open SmallLevelTwentySixMMPPari
def r0p0 (x y z w a b u : ℂ) : ℂ := (2/11:ℂ) + (7/33:ℂ)*a + (-13/33:ℂ)*x + (-7/66:ℂ)*x*a + (5/33:ℂ)*x^2
def r0p1 (x y z w a b u : ℂ) : ℂ := (1/1:ℂ) + (1/1:ℂ)*u + (-1/1:ℂ)*a*u + (-1/1:ℂ)*y + (-127/30:ℂ)*x + (13/10:ℂ)*x*u + (1/2:ℂ)*x*a*u + (3/2:ℂ)*x*y + (5/3:ℂ)*x^2 + (-9/10:ℂ)*x^2*u + (-1/2:ℂ)*x^2*y + (-1/3:ℂ)*x^3
def r0p2 (x y z w a b u : ℂ) : ℂ := (1/1:ℂ) + (-1/1:ℂ)*a + (13/10:ℂ)*x + (1/2:ℂ)*x*a + (-9/10:ℂ)*x^2
def r0p3 (x y z w a b u : ℂ) : ℂ := (1/1:ℂ) + (13/99:ℂ)*a + (-2/11:ℂ)*u + (-7/33:ℂ)*a*u + (-50/297:ℂ)*y + (-35/66:ℂ)*x + (13/33:ℂ)*x*u + (7/66:ℂ)*x*a*u + (25/99:ℂ)*x*y + (25/132:ℂ)*x^2 + (-5/33:ℂ)*x^2*u + (-25/297:ℂ)*x^2*y + (-5/132:ℂ)*x^3
def r0p4 (x y z w a b u : ℂ) : ℂ := (13/11:ℂ) + (-65/99:ℂ)*a + (-13/99:ℂ)*a^2 + (-104/297:ℂ)*y + (-13/297:ℂ)*y*a + (-13/33:ℂ)*x + (13/66:ℂ)*x*a + (13/198:ℂ)*x*a^2 + (208/297:ℂ)*x*y + (26/297:ℂ)*x*y*a + (13/18:ℂ)*x^2 + (91/396:ℂ)*x^2*a + (-130/297:ℂ)*x^2*y + (-65/1188:ℂ)*x^2*y*a + (-533/792:ℂ)*x^3 + (-91/792:ℂ)*x^3*a + (26/297:ℂ)*x^3*y + (13/1188:ℂ)*x^3*y*a + (65/396:ℂ)*x^4 + (13/792:ℂ)*x^4*a + (-13/792:ℂ)*x^5
theorem identity0 (x y z w a b u : ℂ) :
    r0p0 x y z w a b u*r0p1 x y z w a b u+
    r0p2 x y z w a b u*r0p3 x y z w a b u=r0p4 x y z w a b u := by
  unfold r0p0 r0p1 r0p2 r0p3 r0p4
  ring
#print axioms identity0
def r1p0 (x y z w a b u : ℂ) : ℂ := (-1/1:ℂ) + (1/1:ℂ)*a^2 + (-1/1:ℂ)*y + (1/1:ℂ)*y*a + (-1/1:ℂ)*x + (-1/1:ℂ)*x*a + (-1/1:ℂ)*x*y
def r1p1 (x y z w a b u : ℂ) : ℂ := (1/1:ℂ) + (1/1:ℂ)*u + (-1/1:ℂ)*a*u + (-1/1:ℂ)*y + (-127/30:ℂ)*x + (13/10:ℂ)*x*u + (1/2:ℂ)*x*a*u + (3/2:ℂ)*x*y + (5/3:ℂ)*x^2 + (-9/10:ℂ)*x^2*u + (-1/2:ℂ)*x^2*y + (-1/3:ℂ)*x^3
def r1p2 (x y z w a b u : ℂ) : ℂ := (1/1:ℂ) + (-1/1:ℂ)*a + (13/10:ℂ)*x + (1/2:ℂ)*x*a + (-9/10:ℂ)*x^2
def r1p3 (x y z w a b u : ℂ) : ℂ := (1/1:ℂ) + (1/1:ℂ)*a + (1/1:ℂ)*u + (-1/1:ℂ)*a^2*u + (-1/1:ℂ)*y*a + (1/1:ℂ)*y*u + (-1/1:ℂ)*y*a*u + (-1/1:ℂ)*y^2 + (1/1:ℂ)*x*u + (1/1:ℂ)*x*a*u + (1/1:ℂ)*x*y + (1/1:ℂ)*x*y*a + (1/1:ℂ)*x*y*u + (1/1:ℂ)*x*y^2 + (1/1:ℂ)*x^2 + (-1/1:ℂ)*x^3
def r1p4 (x y z w a b u : ℂ) : ℂ := (68/15:ℂ)*x + (4/5:ℂ)*x*a + (-56/15:ℂ)*x*a^2 + (56/15:ℂ)*x*y + (-68/15:ℂ)*x*y*a + (-4/5:ℂ)*x*y^2 + (8/3:ℂ)*x^2 + (7/3:ℂ)*x^2*a + (5/3:ℂ)*x^2*a^2 + (43/15:ℂ)*x^2*y + (43/15:ℂ)*x^2*y*a + (6/5:ℂ)*x^2*y^2 + (-31/30:ℂ)*x^3 + (-1/6:ℂ)*x^3*a + (-1/3:ℂ)*x^3*a^2 + (-26/15:ℂ)*x^3*y + (-11/15:ℂ)*x^3*y*a + (-2/5:ℂ)*x^3*y^2 + (-28/15:ℂ)*x^4 + (-1/6:ℂ)*x^4*a + (1/3:ℂ)*x^4*y + (9/10:ℂ)*x^5
theorem identity1 (x y z w a b u : ℂ) :
    r1p0 x y z w a b u*r1p1 x y z w a b u+
    r1p2 x y z w a b u*r1p3 x y z w a b u=r1p4 x y z w a b u := by
  unfold r1p0 r1p1 r1p2 r1p3 r1p4
  ring
#print axioms identity1
def r2p0 (x y z w a b u : ℂ) : ℂ := (271856/22275:ℂ)*x^2 + (212576/22275:ℂ)*x^2*a + (349024/66825:ℂ)*x^2*y + (-107744/66825:ℂ)*x^2*y*a + (-104624/66825:ℂ)*x^2*y^2 + (-178984/7425:ℂ)*x^3 + (-4108/405:ℂ)*x^3*a + (10192/13365:ℂ)*x^3*y + (4316/2475:ℂ)*x^3*y*a + (33904/22275:ℂ)*x^3*y^2 + (198497/7425:ℂ)*x^4 + (37076/22275:ℂ)*x^4*a + (-777803/66825:ℂ)*x^4*y + (-806/2673:ℂ)*x^4*y*a + (364/2673:ℂ)*x^4*y^2 + (-465998/22275:ℂ)*x^5 + (44993/14850:ℂ)*x^5*a + (1719731/133650:ℂ)*x^5*y + (-2483/5346:ℂ)*x^5*y*a + (-24817/26730:ℂ)*x^5*y^2 + (540839/44550:ℂ)*x^6 + (-1417/550:ℂ)*x^6*a + (-981383/133650:ℂ)*x^6*y + (3757/10692:ℂ)*x^6*y*a + (6799/10692:ℂ)*x^6*y^2 + (-38974/7425:ℂ)*x^7 + (4043/3960:ℂ)*x^7*a + (27781/10692:ℂ)*x^7*y + (-5993/53460:ℂ)*x^7*y*a + (-2275/10692:ℂ)*x^7*y^2 + (7787/4752:ℂ)*x^8 + (-8411/35640:ℂ)*x^8*a + (-157547/267300:ℂ)*x^8*y + (65/3564:ℂ)*x^8*y*a + (221/5940:ℂ)*x^8*y^2 + (-25181/71280:ℂ)*x^9 + (221/7128:ℂ)*x^9*a + (845/10692:ℂ)*x^9*y + (-13/10692:ℂ)*x^9*y*a + (-13/4860:ℂ)*x^9*y^2 + (221/4752:ℂ)*x^10 + (-13/7128:ℂ)*x^10*a + (-247/53460:ℂ)*x^10*y + (-13/4752:ℂ)*x^11
def r2p1 (x y z w a b u : ℂ) : ℂ := (13/11:ℂ) + (-65/99:ℂ)*a + (-13/99:ℂ)*a^2 + (-104/297:ℂ)*y + (-13/297:ℂ)*y*a + (-13/33:ℂ)*x + (13/66:ℂ)*x*a + (13/198:ℂ)*x*a^2 + (208/297:ℂ)*x*y + (26/297:ℂ)*x*y*a + (13/18:ℂ)*x^2 + (91/396:ℂ)*x^2*a + (-130/297:ℂ)*x^2*y + (-65/1188:ℂ)*x^2*y*a + (-533/792:ℂ)*x^3 + (-91/792:ℂ)*x^3*a + (26/297:ℂ)*x^3*y + (13/1188:ℂ)*x^3*y*a + (65/396:ℂ)*x^4 + (13/792:ℂ)*x^4*a + (-13/792:ℂ)*x^5
def r2p2 (x y z w a b u : ℂ) : ℂ := (-106808/49005:ℂ)*x + (-49348/147015:ℂ)*x*a + (179816/441045:ℂ)*x*y + (25012/441045:ℂ)*x*y*a + (1352/264627:ℂ)*x*y^2 + (66079/29403:ℂ)*x^2 + (55094/147015:ℂ)*x^2*a + (-2197/4455:ℂ)*x^2*y + (-9464/147015:ℂ)*x^2*y*a + (-1352/88209:ℂ)*x^2*y^2 + (-48841/294030:ℂ)*x^3 + (-3887/98010:ℂ)*x^3*a + (77402/441045:ℂ)*x^3*y + (2197/294030:ℂ)*x^3*y*a + (6929/529254:ℂ)*x^3*y^2 + (-285779/588060:ℂ)*x^4 + (-25181/196020:ℂ)*x^4*a + (-124891/1764180:ℂ)*x^4*y + (1183/58806:ℂ)*x^4*y*a + (169/39204:ℂ)*x^4*y^2 + (-169/49005:ℂ)*x^5 + (3211/35640:ℂ)*x^5*a + (6422/49005:ℂ)*x^5*y + (-2873/235224:ℂ)*x^5*y*a + (-10309/705672:ℂ)*x^5*y^2 + (3887/14256:ℂ)*x^6 + (-23153/784080:ℂ)*x^6*a + (-3887/32670:ℂ)*x^6*y + (169/58806:ℂ)*x^6*y*a + (4901/470448:ℂ)*x^6*y^2 + (-181337/940896:ℂ)*x^7 + (1183/235224:ℂ)*x^7*a + (390559/7056720:ℂ)*x^7*y + (-169/705672:ℂ)*x^7*y*a + (-15041/4234032:ℂ)*x^7*y^2 + (647101/9408960:ℂ)*x^8 + (-169/470448:ℂ)*x^8*a + (-11323/784080:ℂ)*x^8*y + (845/1411344:ℂ)*x^8*y^2 + (-15041/1045440:ℂ)*x^9 + (2873/1411344:ℂ)*x^9*y + (-169/4234032:ℂ)*x^9*y^2 + (3211/1881792:ℂ)*x^10 + (-169/1411344:ℂ)*x^10*y + (-169/1881792:ℂ)*x^11
def r2p3 (x y z w a b u : ℂ) : ℂ := (68/15:ℂ)*x + (4/5:ℂ)*x*a + (-56/15:ℂ)*x*a^2 + (56/15:ℂ)*x*y + (-68/15:ℂ)*x*y*a + (-4/5:ℂ)*x*y^2 + (8/3:ℂ)*x^2 + (7/3:ℂ)*x^2*a + (5/3:ℂ)*x^2*a^2 + (43/15:ℂ)*x^2*y + (43/15:ℂ)*x^2*y*a + (6/5:ℂ)*x^2*y^2 + (-31/30:ℂ)*x^3 + (-1/6:ℂ)*x^3*a + (-1/3:ℂ)*x^3*a^2 + (-26/15:ℂ)*x^3*y + (-11/15:ℂ)*x^3*y*a + (-2/5:ℂ)*x^3*y^2 + (-28/15:ℂ)*x^4 + (-1/6:ℂ)*x^4*a + (1/3:ℂ)*x^4*y + (9/10:ℂ)*x^5
def r2p4 (x y z w a b u : ℂ) : ℂ := (667888/147015:ℂ)*x^2 + (-1936064/441045:ℂ)*x^2*y + (-516464/1323135:ℂ)*x^2*y^2 + (319072/1323135:ℂ)*x^2*y^3 + (-5408/1323135:ℂ)*x^2*y^4 + (-63775868/2205225:ℂ)*x^3 + (22262708/1323135:ℂ)*x^3*y + (13194844/19847025:ℂ)*x^3*y^2 + (-15644668/19847025:ℂ)*x^3*y^3 + (2704/147015:ℂ)*x^3*y^4 + (4687891/81675:ℂ)*x^4 + (-219706084/6615675:ℂ)*x^4*y + (5419661/1804275:ℂ)*x^4*y^2 + (15964754/19847025:ℂ)*x^4*y^3 + (-338/10935:ℂ)*x^4*y^4 + (-18164627/294030:ℂ)*x^5 + (628211363/13231350:ℂ)*x^5*y + (-48299017/4410450:ℂ)*x^5*y^2 + (240487/1470150:ℂ)*x^5*y^3 + (2704/147015:ℂ)*x^5*y^4 + (465968659/8820900:ℂ)*x^6 + (-1412598161/26462700:ℂ)*x^6*y + (1266022433/79388100:ℂ)*x^6*y^2 + (-8149687/7217100:ℂ)*x^6*y^3 + (15379/1323135:ℂ)*x^6*y^4 + (-21651097/490050:ℂ)*x^7 + (606966373/13231350:ℂ)*x^7*y + (-433196179/31755240:ℂ)*x^7*y^2 + (192566543/158776200:ℂ)*x^7*y^3 + (-1352/49005:ℂ)*x^7*y^4 + (1137877507/35283600:ℂ)*x^8 + (-21322054/735075:ℂ)*x^8*y + (407731597/52925400:ℂ)*x^8*y^2 + (-75976147/105850800:ℂ)*x^8*y^3 + (224263/10585080:ℂ)*x^8*y^4 + (-1256909953/70567200:ℂ)*x^9 + (559138021/42340320:ℂ)*x^9*y + (-953200729/317552400:ℂ)*x^9*y^2 + (85891039/317552400:ℂ)*x^9*y^3 + (-5239/588060:ℂ)*x^9*y^4 + (199040257/28226880:ℂ)*x^10 + (-1797718403/423403200:ℂ)*x^10*y + (512771857/635104800:ℂ)*x^10*y^2 + (-211757/3175524:ℂ)*x^10*y^3 + (2873/1323135:ℂ)*x^10*y^4 + (-68340389/35283600:ℂ)*x^11 + (391762787/423403200:ℂ)*x^11*y + (-276653/1924560:ℂ)*x^11*y^2 + (550771/52925400:ℂ)*x^11*y^3 + (-169/588060:ℂ)*x^11*y^4 + (24325691/70567200:ℂ)*x^12 + (-12950977/105850800:ℂ)*x^12*y + (220207/14434200:ℂ)*x^12*y^2 + (-58643/63510480:ℂ)*x^12*y^3 + (169/10585080:ℂ)*x^12*y^4 + (-1108133/35283600:ℂ)*x^13 + (1342367/211701600:ℂ)*x^13*y + (-1183/1587762:ℂ)*x^13*y^2 + (2197/63510480:ℂ)*x^13*y^3 + (-108329/141134400:ℂ)*x^14 + (169/348480:ℂ)*x^14*y + (169/42340320:ℂ)*x^14*y^2 + (6929/14113440:ℂ)*x^15 + (-5239/84680640:ℂ)*x^15*y + (-169/4704480:ℂ)*x^16
theorem identity2 (x y z w a b u : ℂ) :
    r2p0 x y z w a b u*r2p1 x y z w a b u+
    r2p2 x y z w a b u*r2p3 x y z w a b u=r2p4 x y z w a b u := by
  unfold r2p0 r2p1 r2p2 r2p3 r2p4
  ring
#print axioms identity2
theorem binding0_1 (x y z w a b u : ℂ) :
    r0p1 x y z w a b u=c00 x y z w a b+c01 x y z w a b*u := by
  unfold r0p1 c00 c01
  ring
theorem binding0_3 (x y z w a b u : ℂ) :
    r0p3 x y z w a b u=c10 x y z w a b+c11 x y z w a b*u := by
  unfold r0p3 c10 c11
  ring
theorem binding1_1 (x y z w a b u : ℂ) :
    r1p1 x y z w a b u=c00 x y z w a b+c01 x y z w a b*u := by
  unfold r1p1 c00 c01
  ring
theorem binding1_3 (x y z w a b u : ℂ) :
    r1p3 x y z w a b u=c30 x y z w a b+c31 x y z w a b*u := by
  unfold r1p3 c30 c31
  ring
theorem binding2_1 (x y z w a b u : ℂ) :
    r2p1 x y z w a b u=r0p4 x y z w a b u := by
  unfold r2p1 r0p4
  ring
theorem binding2_3 (x y z w a b u : ℂ) :
    r2p3 x y z w a b u=r1p4 x y z w a b u := by
  unfold r2p3 r1p4
  ring
theorem resultant_zero (x y z w a b u : ℂ)
    (h0 : c00 x y z w a b+c01 x y z w a b*u=0)
    (h1 : c10 x y z w a b+c11 x y z w a b*u=0)
    (h3 : c30 x y z w a b+c31 x y z w a b*u=0) :
    r2p4 x y z w a b u=0 := by
  have hr0 := identity0 x y z w a b u
  rw [binding0_1,binding0_3,h0,h1,mul_zero,mul_zero,zero_add] at hr0
  have hr1 := identity1 x y z w a b u
  rw [binding1_1,binding1_3,h0,h3,mul_zero,mul_zero,zero_add] at hr1
  have hr2 := identity2 x y z w a b u
  rw [binding2_1,binding2_3,←hr0,←hr1,mul_zero,mul_zero,zero_add] at hr2
  exact hr2.symm
#print axioms resultant_zero
theorem resultant_factorization (x y z w a b u : ℂ) :
    r2p4 x y z w a b u=(-65/8712:ℂ)*x^2*(x-2)^2*
      SmallLevelTwentySixPariFirstChart.constantTerm x y*
      SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b u := by
  unfold r2p4 SmallLevelTwentySixPariFirstChart.constantTerm
    SmallLevelTwentySixPariFirstChart.lowCurve SmallLevelTwentySixPariIdentity007.p1
  ring
#print axioms resultant_factorization
end QuantitativeArithmeticSmallLevelTwentySixMMPLowCurve
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixMMPOriginalLowCurveV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPLowCurve
open SmallLevelTwentySixMMPPari

theorem low_curve_zero (x y z w a b θ : ℂ) (hx : x≠0)
    (hc : SmallLevelTwentySixPariFirstChart.constantTerm x y≠0)
    (h0 : c00 x y z w a b+c01 x y z w a b*θ=0)
    (h1 : c10 x y z w a b+c11 x y z w a b*θ=0)
    (h3 : c30 x y z w a b+c31 x y z w a b*θ=0) :
    SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b θ=0 := by
  have hx2 : x-2≠0 := by
    intro h
    have he : x=2 := sub_eq_zero.mp h
    subst x
    have he : c00 2 y z w a b+c01 2 y z w a b*θ=(-52/15:ℂ) := by
      unfold c00 c01
      ring
    rw [he] at h0
    norm_num at h0
  have hr := resultant_zero x y z w a b θ h0 h1 h3
  rw [resultant_factorization] at hr
  exact (mul_eq_zero.mp hr).resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 2 hx)) (pow_ne_zero 2 hx2)) hc)

open QuantitativeArithmeticSevenLaurentRows
open SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)
open QuantitativeArithmeticSmallLevelTwentySixMMPPrimitive
open QuantitativeArithmeticSmallLevelTwentySixMMPOriginalChart

/-- Every original MMP pole satisfies the same low-degree curve as the MMM
branch. The exceptional constant is excluded by its checked physical argument. -/
theorem original_low_curve {m : ℕ} {f : ℕ → ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (s u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) (hs1 : s≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13=v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) s<0) :
    SmallLevelTwentySixPariFirstChart.lowCurve
      (u*parameter 2 m s) ((parameter 3 m s)^2) 0 0 0 0 0=0 := by
  obtain ⟨θ,hθ⟩ := original_first_chart S T s u v hu hv hshift hs hs1 hη hs2 hs13
    hpole (fun i : Fin 0 => Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
  have h0 := hθ (Sum.inl 0)
  have h1 := hθ (Sum.inl 1)
  have h3 := hθ (Sum.inl 3)
  change eval _ _ _ _ _ _ 1 _ (primitiveRows 0)=0 at h0
  change eval _ _ _ _ _ _ 1 _ (primitiveRows 1)=0 at h1
  change eval _ _ _ _ _ _ 1 _ (primitiveRows 3)=0 at h3
  rw [small_row_0] at h0
  rw [small_row_1] at h1
  rw [small_row_3] at h3
  norm_num only [ite_true,ite_false,mul_one] at h0 h1 h3
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hX := mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) s)
  have hc := QuantitativeArithmeticSmallLevelTwentySixMMPExceptional.original_constant_ne_zero
    S T s u v hu hv hshift hs hs1 hη hs2 hs13 hpole
  exact low_curve_zero _ _ _ _ _ _ θ hX hc h0 h1 h3

#print axioms low_curve_zero
#print axioms original_low_curve
end QuantitativeArithmeticSmallLevelTwentySixMMPLowCurve
end
end
