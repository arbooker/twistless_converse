module

public import Mathlib.Tactic

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive.PositiveChart.MinimalSix. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFivePositiveMinimalSixDataV1 -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.PositiveChart.MinimalSix
def input0 (u B a y x : ℂ) : ℂ := ((((48)*x)*B+(((-96)*x)*a))*u+((((18)*x+(-72))*x^2)*B+(((((108)*x)*a+(((54)*x+(192))*x+(48)))*a+(((32)*x)*y+((((27)*x+(-216))*x+(336))*x+(-48))))*a+(((64)*x+(-48))*y+(((-96)*x+(-1056))*x+(48))))))
def input1 (u B a y x : ℂ) : ℂ := ((((48)*x)*B+((((16)*x+(16))*y+((-96)*x))*a+(((32)*x+(32))*y)))*u+((((-32)*y+((-108)*x+(48)))*a+((-64)*y+(((-54)*x+(-408))*x+(-48))))*a+(((12)*x^2+(-240))*y+((((-27)*x+(-96))*x+(-480))*x+(48)))))
def input2 (u B a y x : ℂ) : ℂ := (((((16)*x+(32))*x)*B+(((32)*y+((-112)*x))*a+(((32)*x+(32))*y)))*u+((((-16)*y+((-108)*x+(32)))*a+((-64)*y+(((-54)*x+(-408))*x+(-32))))*a+((((12)*x+(-16))*x+(-224))*y+((((-27)*x+(-128))*x+(-432))*x+(32)))))
def input3 (u B a y x : ℂ) : ℂ := (((((1)*x+(-1))*x)*a+(((1)*x+(-1))*y+((1)*x)))*u+(((-1)*y+((1)*x))*a+((((1)*x+(-1))*x+(-1))*x)))
def input4 (u B a y x : ℂ) : ℂ := ((((1)*a+(-1))*B+(((-1)*y+(1))*a+((1)*y+(-1))))*u+(((1)*x+(-1))*B+((-2)*a+(((-1)*x+(-1))*y+((1)*x+(3))))))
def input5 (u B a y x : ℂ) : ℂ := ((((48)*a+(96))*a)*u+((((-18)*x+(72))*x)*B+((((-108)*a+((-54)*x+(-192)))*a+((-32)*y+(((-27)*x+(264))*x+(-336))))*a+((-64)*y+((96)*x+(960))))))
def target0 (u B a y x : ℂ) : ℂ := ((((-24936192)*B+((24936192)*y+(-24936192)))*u+(((4751040)*y+((-8857824)*x+(-93177024)))*B+(((-36253056)*y+((58842672)*x+(16624128)))*a+(((-2972928)*y+(((-6297552)*x+(-22321248))*x+(27422784)))*y+(((7688592)*x+(15290304))*x+(6567744))))))*u+((((-1433376)*x)*B+((((3344544)*a+(35311104))*a+((8975328)*y+((23491776)*x+(48082560))))*a+((((-3836448)*x+(8484800))*x+(15726688))*y+((((-4293828)*x+(23384160))*x+(-50721504))*x+(84508512)))))*B+((((175392)*a+((13803696)*y+(((-2305800)*x+(89250684))*x+(-20364672))))*a+(((-6939168)*y+(((4340952)*x+(20757088))*x+(86539584)))*y+((((-2586276)*x+(18723942))*x+(225805080))*x+(-59267328))))*a+(((((3981600)*x+(-2126048))*x+(-19557152))*y+((((2095632)*x+(-18444060))*x+(65781424))*x+(215382656)))*y+(((((-1173690)*x+(10704987))*x+(39680016))*x+(215625360))*x+(6096864))))))
def target1 (u B a y x : ℂ) : ℂ := ((((1632)*y+((-3024)*x))*B+(((-2832)*y+((-432)*x))*a+((((1296)*x+(4752))*x+(-1296))*y+(((-432)*x+(1296))*x))))*u+((((1632)*y+((-1632)*x))*a+((((288)*x+(-1152))*x)*y+((((-1686)*x+(4008))*x+(768))*x)))*B+(((((3792)*y+(-2496))*a+((4704)*y+(((-2916)*x+(4212))*x+(1968))))*a+(((512)*y+(((1740)*x+(-8016))*x+(7536)))*y+((((-1458)*x+(-8706))*x+(-4392))*x+(-1968))))*a+(((-608)*y+((((-108)*x+(-972))*x+(-13008))*x+(-18384)))*y+(((((-729)*x+(-729))*x+(-11232))*x+(17472))*x+(-528))))))
def target2 (u B a y x : ℂ) : ℂ := (((((1264)*x)*B+((-368)*y+((9344)*x)))*B+(((6624)*y+((-26112)*x))*a+((((-1296)*x+(10416))*x+(13936))*y+(((432)*x+(-3824))*x))))*u+((((1264)*a+((-368)*y+((1632)*x+(-1264))))*a+((((-288)*x+(1152))*x+(-1264))*y+((((-1000)*x+(5472))*x+(-4560))*x+(1264))))*B+((((-2560)*a+((-11024)*y+(((2916)*x+(-27280))*x+(13200))))*a+(((-512)*y+(((-160)*x+(5488))*x+(-13856)))*y+((((1458)*x+(3176))*x+(-150448))*x+(-13200))))*a+(((-656)*y+((((108)*x+(3184))*x+(2896))*x+(-66304)))*y+(((((729)*x+(-9936))*x+(-16576))*x+(-105952))*x+(10640))))))
def target3 (u B a y x : ℂ) : ℂ := ((((7826688)*B+((-7826688)*y+(7826688)))*u+(((-1018752)*y+((2177664)*x+(28045632)))*B+(((10745952)*y+((-18556272)*x+(-5217792)))*a+(((849408)*y+(((2201616)*x+(7886784))*x+(-7423200)))*y+(((-2516112)*x+(-4741536))*x+(-3261120))))))*u+(((((477792)*x+(-9783360))*a+((-2353536)*y+((-9917376)*x+(-12392256))))*a+((((1328544)*x+(-2369056))*x+(-4378496))*y+((((905688)*x+(-6415056))*x+(15404160))*x+(-35872320))))*B+((((483840)*a+((-4218768)*y+(((105840)*x+(-28383372))*x+(7436448))))*a+(((2280960)*y+(((-925344)*x+(-6364992))*x+(-28498368)))*y+((((530712)*x+(-6778854))*x+(-75642456))*x+(19956960))))*a+(((((-1274112)*x+(695200))*x+(5631232))*y+((((-677376)*x+(5623740))*x+(-23827696))*x+(-66476128)))*y+(((((265356)*x+(-3529251))*x+(-13942512))*x+(-63008496))*x+(-6428640))))))
def target4 (u B a y x : ℂ) : ℂ := ((((48)*x)*B+(((-96)*x)*a))*u+((((18)*x+(-72))*x^2)*B+(((((108)*x)*a+(((54)*x+(192))*x+(48)))*a+(((32)*x)*y+((((27)*x+(-216))*x+(336))*x+(-48))))*a+(((64)*x+(-48))*y+(((-96)*x+(-1056))*x+(48))))))
def target5 (u B a y x : ℂ) : ℂ := (((((1264)*x+(-368))*y+((6816)*x))*B+(((6624)*y+((-26112)*x))*a+((((-1296)*x+(11680))*x+(13936))*y+(((432)*x+(-5088))*x))))*u+((((-368)*y+((368)*x))*a+((((-288)*x+(1152))*x)*y+((((-1000)*x+(6736))*x+(-3296))*x)))*B+((((-2560)*a+((-9760)*y+(((2916)*x+(-29808))*x+(11936))))*a+(((-512)*y+(((-160)*x+(4224))*x+(-15120)))*y+((((1458)*x+(3176))*x+(-149184))*x+(-11936))))*a+(((-1920)*y+((((108)*x+(1920))*x+(-896))*x+(-63776)))*y+(((((729)*x+(-9936))*x+(-15312))*x+(-99632))*x+(9376))))))
def target6 (u B a y x : ℂ) : ℂ := ((((48)*x)*B+((((16)*x+(16))*y+((-96)*x))*a+(((32)*x+(32))*y)))*u+((((-32)*y+((-108)*x+(48)))*a+((-64)*y+(((-54)*x+(-408))*x+(-48))))*a+(((12)*x^2+(-240))*y+((((-27)*x+(-96))*x+(-480))*x+(48)))))
def target7 (u B a y x : ℂ) : ℂ := ((((-224)*y+((1456)*x))*B+(((240)*y+((208)*x))*a+((((-624)*x+(-2288))*x+(624))*y+(((208)*x+(-624))*x))))*u+((((-224)*y+((224)*x))*a+((((72)*x+(-288))*x)*y+((((250)*x+(-1368))*x+(192))*x)))*B+((((640)*a+(((632)*x+(544))*y+(((1404)*x+(-2028))*x+(176))))*a+(((128)*y+(((40)*x+(208))*x+(304)))*y+((((702)*x+(3630))*x+(3800))*x+(-176))))*a+(((480)*y+((((52)*x+(468))*x+(4016))*x+(-2384)))*y+(((((351)*x+(351))*x+(5408))*x+(-9536))*x+(816))))))
def target8 (u B a y x : ℂ) : ℂ := ((((896)*y+((9344)*x))*B+(((9152)*y+((-34960)*x))*a+((((1264)*x+(-1264))*y+(((-32)*x+(12944))*x+(17728)))*y+(((-832)*x+(-5088))*x))))*u+((((896)*y+((-896)*x))*a+((((-288)*x+(1152))*x)*y+((((-1000)*x+(5472))*x+(-768))*x)))*B+((((-2560)*a+((-11024)*y+(((2916)*x+(-38340))*x+(14464))))*a+(((-1776)*y+(((-160)*x+(5488))*x+(-18912)))*y+((((1458)*x+(-3618))*x+(-180152))*x+(-14464))))*a+(((-1920)*y+((((108)*x+(1604))*x+(-2160))*x+(-81472)))*y+(((((729)*x+(-12069))*x+(-21632))*x+(-136288))*x+(11904))))))
def target9 (u B a y x : ℂ) : ℂ := (((((16)*x+(32))*x)*B+(((32)*y+((-112)*x))*a+(((32)*x+(32))*y)))*u+((((-16)*y+((-108)*x+(32)))*a+((-64)*y+(((-54)*x+(-408))*x+(-32))))*a+((((12)*x+(-16))*x+(-224))*y+((((-27)*x+(-128))*x+(-432))*x+(32)))))
def target10 (u B a y x : ℂ) : ℂ := ((((19839744)*B+((-19839744)*y+(19839744)))*u+(((-1825152)*y+((5022720)*x+(70455360)))*B+(((27809376)*y+((-50304912)*x+(-13226496)))*a+(((1486464)*y+(((6166512)*x+(22584000))*x+(-17098848)))*y+(((-6795504)*x+(-12766944))*x+(-8903616))))))*u+(((((557424)*x+(-796320))*x)*B+(((-22994688)*a+((-5589344)*y+((-29018976)*x+(-31094400))))*a+((((2975616)*x+(-6492544))*x+(-12293664))*y+((((2388708)*x+(-15787872))*x+(35897184))*x+(-95338464)))))*B+((((967680)*a+((-13052400)*y+(((-266112)*x+(-71201940))*x+(21251040))))*a+(((5444192)*y+(((-2806272)*x+(-13546528))*x+(-73486880)))*y+((((1300320)*x+(-21465450))*x+(-202975560))*x+(49462176))))*a+(((((-3424176)*x+(1984480))*x+(15941792))*y+((((-1772820)*x+(13844052))*x+(-59381520))*x+(-172032608)))*y+(((((530712)*x+(-9615969))*x+(-39712272))*x+(-174838992))*x+(-17392512))))))
def target11 (u B a y x : ℂ) : ℂ := (((((1)*x+(-1))*x)*a+(((1)*x+(-1))*y+((1)*x)))*u+(((-1)*y+((1)*x))*a+((((1)*x+(-1))*x+(-1))*x)))
def target12 (u B a y x : ℂ) : ℂ := ((((-11520)*B+((11520)*y+(-11520)))*u+(((768)*y+((-1344)*x+(-41280)))*B+(((-16032)*y+((29232)*x+(7680)))*a+(((-768)*y+(((-4176)*x+(-15360))*x+(10656)))*y+(((4176)*x+(7008))*x+(4800))))))*u+((((14400)*a+((3456)*y+(((432)*x+(16896))*x+(18240))))*a+((((-2016)*x+(3488))*x+(7168))*y+((((-1080)*x+(7920))*x+(-19968))*x+(52800))))*B+((((7056)*y+(((1728)*x+(42012))*x+(-11232)))*a+(((-3456)*y+(((1296)*x+(7872))*x+(43008)))*y+(((15102)*x+(124728))*x+(-29088))))*a+(((((2016)*x+(-1184))*x+(-8960))*y+((((1080)*x+(-7596))*x+(38576))*x+(100256)))*y+((((5967)*x+(27504))*x+(88560))*x+(9888))))))
def target13 (u B a y x : ℂ) : ℂ := ((((1)*a+(-1))*B+(((-1)*y+(1))*a+((1)*y+(-1))))*u+(((1)*x+(-1))*B+((-2)*a+(((-1)*x+(-1))*y+((1)*x+(3))))))
def target14 (u B a y x : ℂ) : ℂ := ((((48)*a+(96))*a)*u+((((-18)*x+(72))*x)*B+((((-108)*a+((-54)*x+(-192)))*a+((-32)*y+(((-27)*x+(264))*x+(-336))))*a+((-64)*y+((96)*x+(960))))))
def target (u B a y x : ℂ) (i : ℕ) : ℂ := match i with
  | 0 => target0 u B a y x
  | 1 => target1 u B a y x
  | 2 => target2 u B a y x
  | 3 => target3 u B a y x
  | 4 => target4 u B a y x
  | 5 => target5 u B a y x
  | 6 => target6 u B a y x
  | 7 => target7 u B a y x
  | 8 => target8 u B a y x
  | 9 => target9 u B a y x
  | 10 => target10 u B a y x
  | 11 => target11 u B a y x
  | 12 => target12 u B a y x
  | 13 => target13 u B a y x
  | 14 => target14 u B a y x
  | _ => 0
end QuantitativeArithmeticSmallLevelTwentyFive.PositiveChart.MinimalSix
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFivePositiveMinimalSixBundleV4 -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentyFive.PositiveChart.MinimalSix

def row0_0 (u B a y x : ℂ) : ℂ := ((((48)*x)*B+(((-96)*x)*a))*u+((((18)*x+(-72))*x^2)*B+(((((108)*x)*a+(((54)*x+(192))*x+(48)))*a+(((32)*x)*y+((((27)*x+(-216))*x+(336))*x+(-48))))*a+(((64)*x+(-48))*y+(((-96)*x+(-1056))*x+(48))))))
theorem row0_0_identity (u B a y x : ℂ) :
  ((1))*input0 u B a y x=((1))*row0_0 u B a y x := by
  simp only [input0, row0_0] <;> ring
theorem row0_0_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row0_0 u B a y x=0 := by
  have he := (row0_0_identity u B a y x).symm
  have hz : ((1))*row0_0 u B a y x=0 := by
    simpa only [h0,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_0_zero
def row0_1 (u B a y x : ℂ) : ℂ := ((((48)*x)*B+((((16)*x+(16))*y+((-96)*x))*a+(((32)*x+(32))*y)))*u+((((-32)*y+((-108)*x+(48)))*a+((-64)*y+(((-54)*x+(-408))*x+(-48))))*a+(((12)*x^2+(-240))*y+((((-27)*x+(-96))*x+(-480))*x+(48)))))
theorem row0_1_identity (u B a y x : ℂ) :
  ((1))*input1 u B a y x=((1))*row0_1 u B a y x := by
  simp only [input1, row0_1] <;> ring
theorem row0_1_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row0_1 u B a y x=0 := by
  have he := (row0_1_identity u B a y x).symm
  have hz : ((1))*row0_1 u B a y x=0 := by
    simpa only [h1,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_1_zero
def row0_2 (u B a y x : ℂ) : ℂ := (((((16)*x+(32))*x)*B+(((32)*y+((-112)*x))*a+(((32)*x+(32))*y)))*u+((((-16)*y+((-108)*x+(32)))*a+((-64)*y+(((-54)*x+(-408))*x+(-32))))*a+((((12)*x+(-16))*x+(-224))*y+((((-27)*x+(-128))*x+(-432))*x+(32)))))
theorem row0_2_identity (u B a y x : ℂ) :
  ((1))*input2 u B a y x=((1))*row0_2 u B a y x := by
  simp only [input2, row0_2] <;> ring
theorem row0_2_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row0_2 u B a y x=0 := by
  have he := (row0_2_identity u B a y x).symm
  have hz : ((1))*row0_2 u B a y x=0 := by
    simpa only [h2,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_2_zero
def row0_3 (u B a y x : ℂ) : ℂ := (((((1)*x+(-1))*x)*a+(((1)*x+(-1))*y+((1)*x)))*u+(((-1)*y+((1)*x))*a+((((1)*x+(-1))*x+(-1))*x)))
theorem row0_3_identity (u B a y x : ℂ) :
  ((1))*input3 u B a y x=((1))*row0_3 u B a y x := by
  simp only [input3, row0_3] <;> ring
theorem row0_3_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row0_3 u B a y x=0 := by
  have he := (row0_3_identity u B a y x).symm
  have hz : ((1))*row0_3 u B a y x=0 := by
    simpa only [h3,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_3_zero
def row0_4 (u B a y x : ℂ) : ℂ := ((((1)*a+(-1))*B+(((-1)*y+(1))*a+((1)*y+(-1))))*u+(((1)*x+(-1))*B+((-2)*a+(((-1)*x+(-1))*y+((1)*x+(3))))))
theorem row0_4_identity (u B a y x : ℂ) :
  ((1))*input4 u B a y x=((1))*row0_4 u B a y x := by
  simp only [input4, row0_4] <;> ring
theorem row0_4_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row0_4 u B a y x=0 := by
  have he := (row0_4_identity u B a y x).symm
  have hz : ((1))*row0_4 u B a y x=0 := by
    simpa only [h4,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_4_zero
def row0_5 (u B a y x : ℂ) : ℂ := ((((48)*a+(96))*a)*u+((((-18)*x+(72))*x)*B+((((-108)*a+((-54)*x+(-192)))*a+((-32)*y+(((-27)*x+(264))*x+(-336))))*a+((-64)*y+((96)*x+(960))))))
theorem row0_5_identity (u B a y x : ℂ) :
  ((1))*input5 u B a y x=((1))*row0_5 u B a y x := by
  simp only [input5, row0_5] <;> ring
theorem row0_5_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row0_5 u B a y x=0 := by
  have he := (row0_5_identity u B a y x).symm
  have hz : ((1))*row0_5 u B a y x=0 := by
    simpa only [h5,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_5_zero

def row1_0 (u B a y x : ℂ) : ℂ := (((((768)*x)*B+(((-1536)*x)*a))*u+(((576)*x)*B+((((1728)*x)*a^2+((4096)*y+((-10272)*x+(-2304))))*a+((((-144)*x+(144))*y+(((-720)*x+(6768))*x+(1232)))*y+(((-1968)*x+(-15024))*x+(768))))))*u+((((288)*x+(-1152))*x)*B+((((1728)*a+((-1712)*y+(((972)*x+(-13212))*x+(3648))))*a+(((144)*y+((864)*x+(-9104)))*y+((((-378)*x+(-5934))*x+(-50712))*x+(4800))))*a+(((((-252)*x+(1884))*x+(720))*x+(-22784))*y+(((((-189)*x+(477))*x+(-12192))*x+(-49872))*x+(-14784))))))
theorem row1_0_identity (u B a y x : ℂ) :
  (((16)*u+(-82)))*row0_0 u B a y x+
  (((9)*x+(40)))*row0_1 u B a y x+
  (((-18)*x+(81)))*row0_2 u B a y x+
  (((-864)*a+((-144)*y+((-432)*x+(1872)))))*row0_3 u B a y x+
  (((-82)*x+(-16)))*row0_5 u B a y x=((1))*row1_0 u B a y x := by
  simp only [row0_0, row0_1, row0_2, row0_3, row0_5, row1_0] <;> ring
theorem row1_0_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_0 u B a y x=0 := by
  have z0_0 := row0_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_1 := row0_1_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_2 := row0_2_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_3 := row0_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_5 := row0_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_0_identity u B a y x).symm
  have hz : ((1))*row1_0 u B a y x=0 := by
    simpa only [z0_0, z0_1, z0_2, z0_3, z0_5,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_0_zero
def row1_3 (u B a y x : ℂ) : ℂ := (((((4032)*x)*B+((((1344)*x+(1344))*y+((-8064)*x))*a+(((2688)*x+(2688))*y)))*u+((((-1728)*x+(1728))*y+((-1296)*x))*B+(((-15552)*y+((9144)*x+(-12096)))*a+((((-432)*x+(432))*y+(((1872)*x+(-19224))*x+(-48888)))*y+((((-2268)*x+(-8064))*x+(-28008))*x+(4032))))))*u+((((1728)*y+((-1728)*x))*a+((((288)*x+(-1152))*x)*y+((((216)*x+(-9720))*x+(864))*x)))*B+((((12528)*a+((16464)*y+(((-2916)*x+(55404))*x+(7920))))*a+(((944)*y+(((1728)*x+(-4656))*x+(19944)))*y+((((-1458)*x+(11718))*x+(259056))*x+(36432))))*a+(((1024)*y+((((-108)*x+(-2484))*x+(5808))*x+(124368)))*y+(((((-729)*x+(22761))*x+(31752))*x+(134280))*x+(-85392))))))
theorem row1_3_identity (u B a y x : ℂ) :
  ((549))*row0_0 u B a y x+
  (((84)*u+((27)*x+(-594))))*row0_1 u B a y x+
  (((108)*a+(-81)))*row0_2 u B a y x+
  (((-1728)*B+((-432)*y+(7128))))*row0_3 u B a y x+
  (((-16)*y+((441)*x+(-84))))*row0_5 u B a y x+
  (((-5184)*x))*row0_4 u B a y x=((1))*row1_3 u B a y x := by
  simp only [row0_0, row0_1, row0_2, row0_3, row0_5, row0_4, row1_3] <;> ring
theorem row1_3_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_3 u B a y x=0 := by
  have z0_0 := row0_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_1 := row0_1_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_2 := row0_2_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_3 := row0_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_5 := row0_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_4 := row0_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_3_identity u B a y x).symm
  have hz : ((1))*row1_3 u B a y x=0 := by
    simpa only [z0_0, z0_1, z0_2, z0_3, z0_5, z0_4,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_3_zero
def row1_4 (u B a y x : ℂ) : ℂ := (((((48)*x)*B+((((16)*x)*y)*a+(((32)*x+(48))*y+((192)*x))))*B+((((16)*y+(80))*y+((-480)*x))*a+(((-16)*y+((288)*x+(208)))*y+((-96)*x))))*u+(((((-32)*y+((-108)*x+(48)))*a+((-64)*y+(((-54)*x+(-408))*x+(-48))))*a+((((12)*x+(-16))*x+(-224))*y+(((-27)*x^2+(-576))*x+(48))))*B+((((-192)*y+((-648)*x+(288)))*a+((-352)*y+(((-324)*x+(-2640))*x+(-288))))*a+((((16)*x+(16))*y+(((-24)*x+(-112))*x+(-1488)))*y+((((-162)*x+(-480))*x+(-2592))*x+(288))))))
theorem row1_4_identity (u B a y x : ℂ) :
  (((1)*B+(6)))*row0_1 u B a y x+
  (((-16)*y+((96)*x)))*row0_4 u B a y x=((1))*row1_4 u B a y x := by
  simp only [row0_1, row0_4, row1_4] <;> ring
theorem row1_4_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_4 u B a y x=0 := by
  have z0_1 := row0_1_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_4 := row0_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_4_identity u B a y x).symm
  have hz : ((1))*row1_4 u B a y x=0 := by
    simpa only [z0_1, z0_4,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_4_zero
def row1_5 (u B a y x : ℂ) : ℂ := (((((64)*x+(-64))*y+((-7680)*x))*B+(((((896)*x)*y)*a+((-7488)*y+((29136)*x)))*a+((((-432)*x+(432))*y+(((864)*x+(-12112))*x+(-15232)))*y+((5088)*x))))*u+((((-64)*y+((64)*x))*a+((((288)*x+(-1152))*x)*y+((((1000)*x+(-6304))*x+(2432))*x)))*B+((((2560)*a+((11088)*y+(((-2916)*x+(32724))*x+(-12800))))*a+(((944)*y+(((1056)*x+(-4656))*x+(15520)))*y+((((-1458)*x+(-854))*x+(159768))*x+(12800))))*a+(((1024)*y+((((-108)*x+(-1812))*x+(-464))*x+(70720)))*y+(((((-729)*x+(10665))*x+(17472))*x+(112160))*x+(-10240))))))
theorem row1_5_identity (u B a y x : ℂ) :
  ((464))*row0_0 u B a y x+
  (((168)*a+((81)*x+(-942))))*row0_1 u B a y x+
  (((-12)*a+(-243)))*row0_2 u B a y x+
  (((192)*B+((-1296)*y+(7776))))*row0_3 u B a y x+
  (((-48)*y+((308)*x)))*row0_5 u B a y x+
  (((-7488)*x))*row0_4 u B a y x=((3))*row1_5 u B a y x := by
  simp only [row0_0, row0_1, row0_2, row0_3, row0_5, row0_4, row1_5] <;> ring
theorem row1_5_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_5 u B a y x=0 := by
  have z0_0 := row0_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_1 := row0_1_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_2 := row0_2_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_3 := row0_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_5 := row0_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_4 := row0_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_5_identity u B a y x).symm
  have hz : ((3))*row1_5 u B a y x=0 := by
    simpa only [z0_0, z0_1, z0_2, z0_3, z0_5, z0_4,mul_zero,add_zero] using he
  have hu : ((3):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_5_zero
def row1_8 (u B a y x : ℂ) : ℂ := ((((((2688)*x+(5376))*x)*B+(((5376)*y+((-18816)*x))*a+(((5376)*x+(5376))*y)))*u+((((-1728)*x+(1728))*y+((7776)*x))*B+(((-20928)*y+((-29664)*x+(-16128)))*a+((((-432)*x+(432))*y+(((2880)*x+(-17376))*x+(-70896)))*y+((((-4536)*x+(-21504))*x+(-55728))*x+(5376))))))*u+((((1728)*y+((-1728)*x))*a+((((288)*x+(-1152))*x)*y+((((216)*x+(-9216))*x+(-1152))*x)))*B+((((15552)*a+((16464)*y+(((-2916)*x+(56916))*x+(22368))))*a+(((944)*y+(((1728)*x+(-4656))*x+(16304)))*y+((((-1458)*x+(21546))*x+(256200))*x+(36768))))*a+(((1024)*y+((((-108)*x+(-2484))*x+(5808))*x+(117088)))*y+(((((-729)*x+(27297))*x+(27216))*x+(108912))*x+(-103200))))))
theorem row1_8_identity (u B a y x : ℂ) :
  ((738))*row0_0 u B a y x+
  (((27)*x+(-594)))*row0_1 u B a y x+
  (((168)*u+((108)*a+(-81))))*row0_2 u B a y x+
  (((-1728)*B+((-432)*y+(11664))))*row0_3 u B a y x+
  (((-16)*y+((630)*x+(-112))))*row0_5 u B a y x+
  (((-5184)*x))*row0_4 u B a y x=((1))*row1_8 u B a y x := by
  simp only [row0_0, row0_1, row0_2, row0_3, row0_5, row0_4, row1_8] <;> ring
theorem row1_8_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_8 u B a y x=0 := by
  have z0_0 := row0_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_1 := row0_1_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_2 := row0_2_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_3 := row0_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_5 := row0_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_4 := row0_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_8_identity u B a y x).symm
  have hz : ((1))*row1_8 u B a y x=0 := by
    simpa only [z0_0, z0_1, z0_2, z0_3, z0_5, z0_4,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_8_zero
def row1_10 (u B a y x : ℂ) : ℂ := ((((((1)*x+(-1))*x)*a+(((1)*x+(-1))*y+((1)*x)))*u+(((-1)*y+((1)*x))*a+((((1)*x+(-1))*x+(-1))*x)))*u)
theorem row1_10_identity (u B a y x : ℂ) :
  (((1)*u))*row0_3 u B a y x=((1))*row1_10 u B a y x := by
  simp only [row0_3, row1_10] <;> ring
theorem row1_10_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_10 u B a y x=0 := by
  have z0_3 := row0_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_10_identity u B a y x).symm
  have hz : ((1))*row1_10 u B a y x=0 := by
    simpa only [z0_3,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_10_zero

def row1_11 (u B a y x : ℂ) : ℂ := (((((16)*x^2)*a+(((16)*x+(-16))*y+((48)*x)))*B+(((16)*y+((-80)*x))*a+(((48)*x+(32))*y+((-16)*x))))*u+((((-16)*y+((16)*x))*a+(((16)*x^2+(-32))*x))*B+((((-32)*y+((-108)*x+(48)))*a+((-64)*y+(((-54)*x+(-440))*x+(-48))))*a+((((-4)*x+(-16))*x+(-240))*y+((((-27)*x+(-80))*x+(-432))*x+(48))))))
theorem row1_11_identity (u B a y x : ℂ) :
  ((1))*row0_1 u B a y x+
  (((16)*B))*row0_3 u B a y x+
  (((16)*x))*row0_4 u B a y x=((1))*row1_11 u B a y x := by
  simp only [row0_1, row0_3, row0_4, row1_11] <;> ring
theorem row1_11_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_11 u B a y x=0 := by
  have z0_1 := row0_1_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_3 := row0_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_4 := row0_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_11_identity u B a y x).symm
  have hz : ((1))*row1_11 u B a y x=0 := by
    simpa only [z0_1, z0_3, z0_4,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_11_zero
def row1_12 (u B a y x : ℂ) : ℂ := ((((-32)*x)*B+((((16)*x^2)*a+((-32)*y+((112)*x)))*a+(((-32)*x+(-32))*y)))*u+((((16)*y+((124)*x+(-32)))*a+((64)*y+((((16)*x+(54))*x+(392))*x+(32))))*a+(((-12)*x^2+(224))*y+((((27)*x+(96))*x+(448))*x+(-32)))))
theorem row1_12_identity (u B a y x : ℂ) :
  ((1))*row0_0 u B a y x+
  ((-3))*row0_1 u B a y x+
  (((48)*a))*row0_3 u B a y x+
  (((1)*x))*row0_5 u B a y x=((3))*row1_12 u B a y x := by
  simp only [row0_0, row0_1, row0_3, row0_5, row1_12] <;> ring
theorem row1_12_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_12 u B a y x=0 := by
  have z0_0 := row0_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_1 := row0_1_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_3 := row0_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_5 := row0_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_12_identity u B a y x).symm
  have hz : ((3))*row1_12 u B a y x=0 := by
    simpa only [z0_0, z0_1, z0_3, z0_5,mul_zero,add_zero] using he
  have hu : ((3):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_12_zero
def row1_18 (u B a y x : ℂ) : ℂ := (((((1)*a+(-1))*B+(((-1)*y+(1))*a+((1)*y+(-1))))*u+(((1)*x+(-1))*B+((-2)*a+(((-1)*x+(-1))*y+((1)*x+(3))))))*u)
theorem row1_18_identity (u B a y x : ℂ) :
  (((1)*u))*row0_4 u B a y x=((1))*row1_18 u B a y x := by
  simp only [row0_4, row1_18] <;> ring
theorem row1_18_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_18 u B a y x=0 := by
  have z0_4 := row0_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_18_identity u B a y x).symm
  have hz : ((1))*row1_18 u B a y x=0 := by
    simpa only [z0_4,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_18_zero
def row1_19 (u B a y x : ℂ) : ℂ := ((((1)*a+(-1))*B^2+((((-1)*y+(2))*y+(-1))*a+(((1)*y+(-2))*y+(1))))*u+((((1)*x+(-1))*B+((-2)*a+((-2)*y+(4))))*B+(((-2)*y+(2))*a+((((-1)*x+(-1))*y+((2)*x+(4)))*y+((-1)*x+(-3))))))
theorem row1_19_identity (u B a y x : ℂ) :
  (((1)*B+((1)*y+(-1))))*row0_4 u B a y x=((1))*row1_19 u B a y x := by
  simp only [row0_4, row1_19] <;> ring
theorem row1_19_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_19 u B a y x=0 := by
  have z0_4 := row0_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_19_identity u B a y x).symm
  have hz : ((1))*row1_19 u B a y x=0 := by
    simpa only [z0_4,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_19_zero
def row1_20 (u B a y x : ℂ) : ℂ := (((((384)*a+(768))*a)*u+(((1728)*x)*B+(((32)*y+((24)*x+(-3072)))*a+(((504)*x+(-440))*y+((984)*x+(7680))))))*u+(((((-324)*x+(1296))*x)*a+((((162)*x+(-576))*x+(-288))*x))*B+(((((-1944)*a+(-3024))*a+((-720)*y+((5724)*x+(-4128))))*a+(((288)*x+(-1816))*y+((((243)*x+(-1890))*x+(240))*x+(17472))))*a+((((108)*x+(432))*x+(-2624))*y+((((-27)*x+(-2232))*x+(-14856))*x+(-2688))))))
theorem row1_20_identity (u B a y x : ℂ) :
  ((18))*row0_0 u B a y x+
  ((9))*row0_2 u B a y x+
  ((216))*row0_3 u B a y x+
  (((8)*u+((18)*a+((9)*x+(-4)))))*row0_5 u B a y x=((1))*row1_20 u B a y x := by
  simp only [row0_0, row0_2, row0_3, row0_5, row1_20] <;> ring
theorem row1_20_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_20 u B a y x=0 := by
  have z0_0 := row0_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_2 := row0_2_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_3 := row0_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_5 := row0_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_20_identity u B a y x).symm
  have hz : ((1))*row1_20 u B a y x=0 := by
    simpa only [z0_0, z0_2, z0_3, z0_5,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_20_zero
def row1_22 (u B a y x : ℂ) : ℂ := ((((48)*x)*B+(((96)*a^2+((-96)*x+(-384)))*a))*u+(((((-36)*x+(144))*x)*a+(((18)*x^2+(-288))*x))*B+(((((-216)*a+(48))*a+((-64)*y+((936)*x+(144))))*a+(((32)*x)*y+((((27)*x+(-108))*x+(-528))*x+(3216))))*a+(((64)*x+(208))*y+(((-96)*x+(-1440))*x+(-3792))))))
theorem row1_22_identity (u B a y x : ℂ) :
  ((1))*row0_0 u B a y x+
  (((2)*a+(-4)))*row0_5 u B a y x=((1))*row1_22 u B a y x := by
  simp only [row0_0, row0_5, row1_22] <;> ring
theorem row1_22_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_22 u B a y x=0 := by
  have z0_0 := row0_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_5 := row0_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_22_identity u B a y x).symm
  have hz : ((1))*row1_22 u B a y x=0 := by
    simpa only [z0_0, z0_5,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_22_zero

def row1_23 (u B a y x : ℂ) : ℂ := (((((-1728)*x+(1728))*y+((-10368)*x+(-8064)))*B+(((-15552)*y+((47952)*x))*a+((((-432)*x+(432))*y+(((864)*x+(-23760))*x+(-16128)))*y+((7776)*x+(-8064)))))*u+(((((1008)*x+(-4032))*x)*B+((((6048)*a+((3024)*x+(10752)))*a+((3520)*y+(((1512)*x+(-13824))*x+(16128))))*a+((((288)*x+(-1152))*x+(3584))*y+((((216)*x+(-10224))*x+(5568))*x+(-61824)))))*B+((((9504)*a+((16464)*y+(((-2916)*x+(53892))*x+(-11904))))*a+(((944)*y+(((1728)*x+(-7344))*x+(20896)))*y+((((-1458)*x+(1890))*x+(264600))*x+(28032))))*a+(((1024)*y+((((-108)*x+(-2484))*x+(-2256))*x+(123584)))*y+(((((-729)*x+(18225))*x+(36288))*x+(167712))*x+(-43392))))))
theorem row1_23_identity (u B a y x : ℂ) :
  ((360))*row0_0 u B a y x+
  (((27)*x+(-594)))*row0_1 u B a y x+
  (((108)*a+(-81)))*row0_2 u B a y x+
  (((-1728)*B+((-432)*y+(2592))))*row0_3 u B a y x+
  (((2688)*a+((-5184)*x+(8064))))*row0_4 u B a y x+
  (((-56)*B+((-16)*y+((252)*x+(-56)))))*row0_5 u B a y x=((1))*row1_23 u B a y x := by
  simp only [row0_0, row0_1, row0_2, row0_3, row0_4, row0_5, row1_23] <;> ring
theorem row1_23_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_23 u B a y x=0 := by
  have z0_0 := row0_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_1 := row0_1_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_2 := row0_2_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_3 := row0_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_4 := row0_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_5 := row0_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_23_identity u B a y x).symm
  have hz : ((1))*row1_23 u B a y x=0 := by
    simpa only [z0_0, z0_1, z0_2, z0_3, z0_4, z0_5,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_23_zero
def row1_24 (u B a y x : ℂ) : ℂ := (((((1)*y)*a+((-1)*y))*B+((((-1)*y+(1))*y)*a+(((1)*y+(-1))*y)))*u+((((1)*x+(-1))*y)*B+(((-2)*y)*a+((((-1)*x+(-1))*y+((1)*x+(3)))*y))))
theorem row1_24_identity (u B a y x : ℂ) :
  (((1)*y))*row0_4 u B a y x=((1))*row1_24 u B a y x := by
  simp only [row0_4, row1_24] <;> ring
theorem row1_24_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_24 u B a y x=0 := by
  have z0_4 := row0_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_24_identity u B a y x).symm
  have hz : ((1))*row1_24 u B a y x=0 := by
    simpa only [z0_4,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_24_zero
def row1_25 (u B a y x : ℂ) : ℂ := (((((-1728)*x+(1728))*y+((-10368)*x))*B+((((2688)*y)*a+((-10176)*y+((47952)*x)))*a+((((-432)*x+(432))*y+(((864)*x+(-23760))*x+(-24192)))*y+((7776)*x))))*u+((((1728)*y+((-1728)*x))*a+((((288)*x+(-1152))*x)*y+((((216)*x+(-11232))*x+(6912))*x)))*B+((((3456)*a+((16464)*y+(((-2916)*x+(50868))*x+(-17280))))*a+(((944)*y+(((1728)*x+(-4656))*x+(21792)))*y+((((-1458)*x+(378))*x+(276696))*x+(17280))))*a+(((1024)*y+((((-108)*x+(-2484))*x+(5808))*x+(128064)))*y+(((((-729)*x+(18225))*x+(36288))*x+(165024))*x+(-13824))))))
theorem row1_25_identity (u B a y x : ℂ) :
  ((360))*row0_0 u B a y x+
  (((27)*x+(-594)))*row0_1 u B a y x+
  (((108)*a+(-81)))*row0_2 u B a y x+
  (((-1728)*B+((-432)*y+(2592))))*row0_3 u B a y x+
  (((-16)*y+((252)*x)))*row0_5 u B a y x+
  (((-5184)*x))*row0_4 u B a y x=((1))*row1_25 u B a y x := by
  simp only [row0_0, row0_1, row0_2, row0_3, row0_5, row0_4, row1_25] <;> ring
theorem row1_25_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_25 u B a y x=0 := by
  have z0_0 := row0_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_1 := row0_1_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_2 := row0_2_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_3 := row0_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_5 := row0_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_4 := row0_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_25_identity u B a y x).symm
  have hz : ((1))*row1_25 u B a y x=0 := by
    simpa only [z0_0, z0_1, z0_2, z0_3, z0_5, z0_4,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_25_zero
def row1_26 (u B a y x : ℂ) : ℂ := (((((-384)*x+(384))*y+((-6336)*x))*B+(((-6144)*y+((19728)*x))*a+((((-432)*x+(432))*y+(((864)*x+(-6288))*x+(-10752)))*y+((3744)*x))))*u+((((384)*y+((-384)*x))*a+((((288)*x+(-1152))*x)*y+((((48)*x+(-2496))*x+(1536))*x)))*B+(((((1344)*y+(768))*a+((8400)*y+(((-2916)*x+(23652))*x+(-7872))))*a+(((944)*y+(((720)*x+(-6000))*x+(13728)))*y+((((-1458)*x+(-2814))*x+(105336))*x+(7872))))*a+(((1024)*y+((((-108)*x+(-1476))*x+(-3600))*x+(40704)))*y+(((((-729)*x+(6885))*x+(8064))*x+(83040))*x+(-7104))))))
theorem row1_26_identity (u B a y x : ℂ) :
  ((80))*row0_0 u B a y x+
  (((27)*x+(-174)))*row0_1 u B a y x+
  (((24)*a+(-81)))*row0_2 u B a y x+
  (((-384)*B+((-432)*y+(2592))))*row0_3 u B a y x+
  (((-16)*y+((56)*x)))*row0_5 u B a y x+
  (((-1152)*x))*row0_4 u B a y x=((1))*row1_26 u B a y x := by
  simp only [row0_0, row0_1, row0_2, row0_3, row0_5, row0_4, row1_26] <;> ring
theorem row1_26_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_26 u B a y x=0 := by
  have z0_0 := row0_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_1 := row0_1_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_2 := row0_2_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_3 := row0_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_5 := row0_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_4 := row0_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_26_identity u B a y x).symm
  have hz : ((1))*row1_26 u B a y x=0 := by
    simpa only [z0_0, z0_1, z0_2, z0_3, z0_5, z0_4,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_26_zero
def row1_27 (u B a y x : ℂ) : ℂ := (((((16)*x)*a+((32)*x))*B+(((16)*y+((-80)*x))*a+(((48)*x+(32))*y+((-16)*x))))*u+((((16)*x+(-16))*x)*B+((((-32)*y+((-108)*x+(48)))*a+((-64)*y+(((-54)*x+(-440))*x+(-48))))*a+((((-4)*x+(-16))*x+(-240))*y+((((-27)*x+(-80))*x+(-432))*x+(48))))))
theorem row1_27_identity (u B a y x : ℂ) :
  ((1))*row0_1 u B a y x+
  (((16)*x))*row0_4 u B a y x=((1))*row1_27 u B a y x := by
  simp only [row0_1, row0_4, row1_27] <;> ring
theorem row1_27_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_27 u B a y x=0 := by
  have z0_1 := row0_1_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_4 := row0_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_27_identity u B a y x).symm
  have hz : ((1))*row1_27 u B a y x=0 := by
    simpa only [z0_1, z0_4,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_27_zero
def row1_28 (u B a y x : ℂ) : ℂ := ((((1)*x)*B+(((1)*x)*a^2))*u+(((1)*a+((1)*x^2+(-1)))*a+((-1)*y+((-2)*x+(1)))))
theorem row1_28_identity (u B a y x : ℂ) :
  ((1))*row0_0 u B a y x+
  (((1)*x))*row0_5 u B a y x=((48))*row1_28 u B a y x := by
  simp only [row0_0, row0_5, row1_28] <;> ring
theorem row1_28_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_28 u B a y x=0 := by
  have z0_0 := row0_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_5 := row0_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_28_identity u B a y x).symm
  have hz : ((48))*row1_28 u B a y x=0 := by
    simpa only [z0_0, z0_5,mul_zero,add_zero] using he
  have hu : ((48):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_28_zero

def row1_29 (u B a y x : ℂ) : ℂ := ((((48)*x)*B+(((-96)*x)*a))*u+((((18)*x+(-72))*x^2)*B+(((((108)*x)*a+(((54)*x+(192))*x+(48)))*a+(((32)*x)*y+((((27)*x+(-216))*x+(336))*x+(-48))))*a+(((64)*x+(-48))*y+(((-96)*x+(-1056))*x+(48))))))
theorem row1_29_identity (u B a y x : ℂ) :
  ((1))*row0_0 u B a y x=((1))*row1_29 u B a y x := by
  simp only [row0_0, row1_29] <;> ring
theorem row1_29_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_29 u B a y x=0 := by
  have z0_0 := row0_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_29_identity u B a y x).symm
  have hz : ((1))*row1_29 u B a y x=0 := by
    simpa only [z0_0,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_29_zero
def row1_30 (u B a y x : ℂ) : ℂ := ((((48)*x)*B+((((16)*x+(16))*y+((-96)*x))*a+(((32)*x+(32))*y)))*u+((((-32)*y+((-108)*x+(48)))*a+((-64)*y+(((-54)*x+(-408))*x+(-48))))*a+(((12)*x^2+(-240))*y+((((-27)*x+(-96))*x+(-480))*x+(48)))))
theorem row1_30_identity (u B a y x : ℂ) :
  ((1))*row0_1 u B a y x=((1))*row1_30 u B a y x := by
  simp only [row0_1, row1_30] <;> ring
theorem row1_30_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_30 u B a y x=0 := by
  have z0_1 := row0_1_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_30_identity u B a y x).symm
  have hz : ((1))*row1_30 u B a y x=0 := by
    simpa only [z0_1,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_30_zero
def row1_31 (u B a y x : ℂ) : ℂ := ((((192)*x)*B+(((128)*y+((-432)*x))*a+((((16)*x+(-16))*y+(((-32)*x+(48))*x+(256)))*y+((-96)*x))))*u+(((((32)*x+(-112))*y+(((108)*x+(-588))*x+(192)))*a+(((-16)*y+((80)*x+(-224)))*y+((((54)*x+(138))*x+(-2088))*x+(-192))))*a+(((((4)*x+(44))*x+(176))*x+(-1152))*y+((((27)*x+(-135))*x^2+(-2208))*x+(192)))))
theorem row1_31_identity (u B a y x : ℂ) :
  (((-1)*x+(2)))*row0_1 u B a y x+
  ((3))*row0_2 u B a y x+
  (((16)*y+(-96)))*row0_3 u B a y x=((1))*row1_31 u B a y x := by
  simp only [row0_1, row0_2, row0_3, row1_31] <;> ring
theorem row1_31_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_31 u B a y x=0 := by
  have z0_1 := row0_1_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_2 := row0_2_zero u B a y x h0 h1 h2 h3 h4 h5
  have z0_3 := row0_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_31_identity u B a y x).symm
  have hz : ((1))*row1_31 u B a y x=0 := by
    simpa only [z0_1, z0_2, z0_3,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_31_zero
def row1_32 (u B a y x : ℂ) : ℂ := (((((16)*x+(32))*x)*B+(((32)*y+((-112)*x))*a+(((32)*x+(32))*y)))*u+((((-16)*y+((-108)*x+(32)))*a+((-64)*y+(((-54)*x+(-408))*x+(-32))))*a+((((12)*x+(-16))*x+(-224))*y+((((-27)*x+(-128))*x+(-432))*x+(32)))))
theorem row1_32_identity (u B a y x : ℂ) :
  ((1))*row0_2 u B a y x=((1))*row1_32 u B a y x := by
  simp only [row0_2, row1_32] <;> ring
theorem row1_32_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_32 u B a y x=0 := by
  have z0_2 := row0_2_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_32_identity u B a y x).symm
  have hz : ((1))*row1_32 u B a y x=0 := by
    simpa only [z0_2,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_32_zero
def row1_33 (u B a y x : ℂ) : ℂ := (((((1)*x+(-1))*x)*a+(((1)*x+(-1))*y+((1)*x)))*u+(((-1)*y+((1)*x))*a+((((1)*x+(-1))*x+(-1))*x)))
theorem row1_33_identity (u B a y x : ℂ) :
  ((1))*row0_3 u B a y x=((1))*row1_33 u B a y x := by
  simp only [row0_3, row1_33] <;> ring
theorem row1_33_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_33 u B a y x=0 := by
  have z0_3 := row0_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_33_identity u B a y x).symm
  have hz : ((1))*row1_33 u B a y x=0 := by
    simpa only [z0_3,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_33_zero
def row1_34 (u B a y x : ℂ) : ℂ := ((((1)*a+(-1))*B+(((-1)*y+(1))*a+((1)*y+(-1))))*u+(((1)*x+(-1))*B+((-2)*a+(((-1)*x+(-1))*y+((1)*x+(3))))))
theorem row1_34_identity (u B a y x : ℂ) :
  ((1))*row0_4 u B a y x=((1))*row1_34 u B a y x := by
  simp only [row0_4, row1_34] <;> ring
theorem row1_34_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_34 u B a y x=0 := by
  have z0_4 := row0_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_34_identity u B a y x).symm
  have hz : ((1))*row1_34 u B a y x=0 := by
    simpa only [z0_4,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_34_zero

def row1_35 (u B a y x : ℂ) : ℂ := ((((48)*a+(96))*a)*u+((((-18)*x+(72))*x)*B+((((-108)*a+((-54)*x+(-192)))*a+((-32)*y+(((-27)*x+(264))*x+(-336))))*a+((-64)*y+((96)*x+(960))))))
theorem row1_35_identity (u B a y x : ℂ) :
  ((1))*row0_5 u B a y x=((1))*row1_35 u B a y x := by
  simp only [row0_5, row1_35] <;> ring
theorem row1_35_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row1_35 u B a y x=0 := by
  have z0_5 := row0_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row1_35_identity u B a y x).symm
  have hz : ((1))*row1_35 u B a y x=0 := by
    simpa only [z0_5,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_35_zero
def row2_1 (u B a y x : ℂ) : ℂ := ((((((2548224)*x)*B+(83909376))*B+(((5096448)*y+((-5096448)*x))*a+(((15289344)*x+(-73716480))*y+((-5096448)*x+(83909376)))))*u+((((5733504)*x)*a^3+((((-477792)*x+(477792))*y+(-38006976))*y+((15301056)*x+(303223488))))*B+((((18368448)*y+(-150895584))*y+((534315600)*x+(-63584256)))*a+(((37480128)*y+(((-13856112)*x+(-558831360))*x+(-537762336)))*y+((((-8600256)*x+(4171248))*x+(148369440))*x+(-29865792))))))*u+(((((3225096)*x^2+(-104886720))*a+(((477792)*y+((2866752)*x+(-58969152)))*y+((((-1254204)*x+(2229696))*x+(-97898304))*x+(-130308288))))*a+(((((-836136)*x+(30880752))*x+(-82989056))*x+(-56141824))*y+(((((-627102)*x+(62216532))*x+(-404835840))*x+(251481984))*x+(-384584640))))*B+((((162255744)*a+(((-8069376)*y+(280109040))*y+(((72820944)*x+(553424868))*x+(-173373408))))*a+(((34322880)*y+(((-18765432)*x+(-372089952))*x+(205058304)))*y+((((36410472)*x+(325977930))*x+(4363877064))*x+(492538464))))*a+(((((-8095920)*x+(7851968))*x+(55106816))*y+((((-10037412)*x+(33510012))*x+(-5152304))*x+(1146308896)))*y+(((((18205236)*x+(281411037))*x+(878300496))*x+(1583858736))*x+(-236938848))))))
theorem row2_1_identity (u B a y x : ℂ) :
  (((4459392)*u+((-7073976)*B+((-24047415)*a+((-49610232)*x+(226022664))))))*row1_31 u B a y x+
  (((-13378176)*u+((21221928)*B+((-110518128)*a+((4180680)*y+((6689088)*x+(-1439324460)))))))*row1_32 u B a y x+
  (((428101632)*u+((-631116864)*B+((-8755100928)*a+((-3401356224)*y+((-80269056)*x+(20460900096)))))))*row1_33 u B a y x+
  (((-2349462528)*u+((-462927360)*a+((-219430400)*y+((-9801533952)*x+(9593638656))))))*row1_34 u B a y x+
  (((16315712)*u+((9644320)*B+((36710352)*a+((-31089856)*y+((-5740224)*x+(-34117888)))))))*row1_35 u B a y x+
  (((-5945856)*u+((-60387600)*B+((13378176)*a+((47753832)*y+((-44590392)*x))))))*row1_29 u B a y x+
  (((92904)*B))*row1_0 u B a y x+
  (((2039464)*B+((-2039464)*y)))*row1_20 u B a y x+
  (((-783154176)*a+((142700544)*x)))*row1_18 u B a y x+
  (((655542)*a+((750579)*x)))*row1_23 u B a y x+
  (((-2949939)*a+((-3264804)*x)))*row1_26 u B a y x+
  (((-71350272)*y))*row1_10 u B a y x+
  (((7073976)*y))*row1_11 u B a y x+
  (((-37901304)*y))*row1_12 u B a y x+
  (((-30827328)*y+((288387372)*x)))*row1_30 u B a y x+
  (((53088)*x))*row1_3 u B a y x+
  (((-7073976)*x))*row1_4 u B a y x+
  (((676809)*x))*row1_5 u B a y x+
  (((6689088)*x))*row1_22 u B a y x+
  (((-53088)*x))*row1_25 u B a y x+
  (((149962932)*x))*row1_27 u B a y x+
  (((8594562816)*x))*row1_28 u B a y x=((28))*row2_1 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_29, row1_0, row1_20, row1_18, row1_23, row1_26, row1_10, row1_11, row1_12, row1_30, row1_3, row1_4, row1_5, row1_22, row1_25, row1_27, row1_28, row2_1] <;> ring
theorem row2_1_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_1 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_0 := row1_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_10 := row1_10_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_3 := row1_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_25 := row1_25_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_1_identity u B a y x).symm
  have hz : ((28))*row2_1 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_29, z1_0, z1_20, z1_18, z1_23, z1_26, z1_10, z1_11, z1_12, z1_30, z1_3, z1_4, z1_5, z1_22, z1_25, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((28):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_1_zero
def row2_7 (u B a y x : ℂ) : ℂ := ((((((62431488)*x)*B+((((20810496)*x)*y)*a+((68377344)*y+(-254822400))))*B+((((20810496)*y+(-2256452352))*y+((1088091648)*x))*a+(((-20810496)*y+((154592256)*x+(-4171867392)))*y+((2140508160)*x+(-254822400)))))*u+(((((-26756352)*x+(26756352))*y+(-3087882048))*y+((-20713190400)*x+(-850682112)))*B+((((-955331200)*y+(6127189248))*y+((21359239440)*x+(101504256)))*a+(((-1984136192)*y+((((-1381296672)*x+(9654494688))*x+(34105577712))*x+(-10224731856)))*y+((((1224103104)*x+(-23415919200))*x+(-4146174576))*x+(219147264))))))*u+((((318528000)*a+(((26756352)*y+(((23571072)*x+(27469248))*x+(-2659780416)))*y+((((87913728)*x+(-449306496))*x+(3050189568))*x+(465900288))))*a+(((((4459392)*x+(-17837568))*x)*y+((((-102884544)*x+(608452128))*x+(-1305086848))*x+(39639040)))*y+(((((-365510880)*x+(6893005128))*x+(-5844924000))*x+(-7547381568))*x+(1167936000))))*B+(((((229340160)*a+(-1341251136))*a+(((645423680)*y+(6076940960))*y+(((-27087799140)*x+(7178835144))*x+(-16822511424))))*a+((((7927808)*y+(((26756352)*x+(-295877120))*x+(1388076160)))*y+(((3516928920)*x+(1457199200))*x+(-14443493392)))*y+((((-6291017010)*x+(-116751651060))*x+(49767559968))*x+(16079704128))))*a+((((15855616)*y+((((10033632)*x+(-283182768))*x+(-553146624))*x+(10005591040)))*y+(((((-330273720)*x+(3579661104))*x+(-2197575480))*x+(-27430429728))*x+(10407397696)))*y+(((((-1895007393)*x+(10917443682))*x+(-95660869728))*x+(-20933086512))*x+(-18342456768))))))
theorem row2_7_identity (u B a y x : ℂ) :
  (((20810496)*u+((-35396424)*B+((1960648956)*a+((1267878717)*x+(-13811142240))))))*row1_31 u B a y x+
  (((-2029023360)*u+((-16722720)*B+((-11186433888)*a+((159741792)*y+((-1430396436)*x+(66835784568)))))))*row1_32 u B a y x+
  (((64928747520)*u+((76068827520)*B+((410160576000)*a+((251392178688)*y+((-36897009408)*x+(-743006322240)))))))*row1_33 u B a y x+
  (((7135027200)*u+((-558910464)*a+((388462592)*y+((132313171200)*x+(-29134694400))))))*row1_34 u B a y x+
  (((-49548800)*u+((11643968)*B+((-111484800)*a+((-600630464)*y+((-7855496544)*x+(90426560)))))))*row1_35 u B a y x+
  (((1335340160)*u+((129879792)*B+((-2949887808)*a+((-794566864)*y+((-262038672)*x))))))*row1_29 u B a y x+
  (((433552)*B+((247744)*x)))*row1_3 u B a y x+
  (((-166483968)*B+((-332967936)*y)))*row1_10 u B a y x+
  (((-6193600)*B+((5326496)*y+((3034864)*x))))*row1_20 u B a y x+
  (((-1950984)*B+((7704396)*a+((17167005)*x))))*row1_26 u B a y x+
  (((2508408)*a+((20493324)*x)))*row1_5 u B a y x+
  (((61936)*a))*row1_8 u B a y x+
  (((-4424831712)*a+((-1147626144)*y)))*row1_12 u B a y x+
  (((2378342400)*a+((-582693888)*y+((2996711424)*x))))*row1_18 u B a y x+
  (((-1990800)*a+((433552)*y+((-1323882)*x))))*row1_23 u B a y x+
  (((-1300656)*y+((40970664)*x)))*row1_0 u B a y x+
  (((-5574240)*y))*row1_11 u B a y x+
  (((-1776002256)*y+((-12245849952)*x)))*row1_30 u B a y x+
  (((5574240)*x))*row1_4 u B a y x+
  (((-1502257680)*x))*row1_22 u B a y x+
  (((-535127040)*x))*row1_24 u B a y x+
  (((-247744)*x))*row1_25 u B a y x+
  (((6432132168)*x))*row1_27 u B a y x+
  (((-484516478208)*x))*row1_28 u B a y x=((28))*row2_7 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_29, row1_3, row1_10, row1_20, row1_26, row1_5, row1_8, row1_12, row1_18, row1_23, row1_0, row1_11, row1_30, row1_4, row1_22, row1_24, row1_25, row1_27, row1_28, row2_7] <;> ring
theorem row2_7_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_7 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_3 := row1_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_10 := row1_10_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_8 := row1_8_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_0 := row1_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_24 := row1_24_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_25 := row1_25_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_7_identity u B a y x).symm
  have hz : ((28))*row2_7 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_29, z1_3, z1_10, z1_20, z1_26, z1_5, z1_8, z1_12, z1_18, z1_23, z1_0, z1_11, z1_30, z1_4, z1_22, z1_24, z1_25, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((28):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_7_zero
def row2_9 (u B a y x : ℂ) : ℂ := ((((-6370560)*B+(((((2972928)*x)*y)*a+((-14864640)*y+((44593920)*x)))*a+(((-38648064)*x+(-23358720))*y+((8918784)*x+(-6370560)))))*u+(((-7500000)*y+((116088336)*x+(-22827840)))*B+((((-657280)*y+(242544912))*y+((-460441968)*x+(93434880)))*a+(((-1739264)*y+(((-5738400)*x+(436592928))*x+(500461680)))*y+((((25084080)*x+(31111200))*x+(-89355792))*x+(-6264384))))))*u+((((7963200)*a+((((-79632)*x+(147888))*x+(-6013536))*y+((((-59724)*x+(6381936))*x+(2934432))*x+(10086720))))*a+(((((159264)*x+(-5254272))*x+(15938336))*x+(3963904))*y+(((((477792)*x+(-8142744))*x+(144690528))*x+(-38629056))*x+(29198400))))*B+(((((19111680)*a+(-107932800))*a+(((1178048)*y+(-244958640))*y+(((2937492)*x+(-1045952844))*x+(150021360))))*a+((((283136)*x+(-5781504))*y+(((-18413784)*x+(82044080))*x+(-447740640)))*y+((((-6175926)*x+(-329855574))*x+(-4285804824))*x+(-681644592))))*a+(((((125136)*x+(1197008))*x+(1722320))*y+((((-7921080)*x+(59978892))*x+(-100196592))*x+(-2115361792)))*y+(((((853821)*x+(-259466031))*x+(-829544784))*x+(-2891073744))*x+(892133616))))))
theorem row2_9_identity (u B a y x : ℂ) :
  (((-26013120)*u+((278712)*B+((-9158688)*a+((10570581)*x+(-311452932))))))*row1_31 u B a y x+
  (((78039360)*u+((-836136)*B+((-51710232)*a+((-597240)*y+((-46823616)*x+(2169244140)))))))*row1_32 u B a y x+
  (((-2497259520)*u+((573105792)*B+((15656944128)*a+((5122125120)*y+((561883392)*x+(-30487516416)))))))*row1_33 u B a y x+
  (((356751360)*u+((59458560)*a+((27747328)*y+((5159121408)*x+(-1456734720))))))*row1_34 u B a y x+
  (((-2477440)*u+((-1238720)*B+((-5574240)*a+((10400768)*y+((-133407008)*x+(46575872)))))))*row1_35 u B a y x+
  (((41620992)*u+((10591056)*B+((-46823616)*a+((-4653712)*y+((28389816)*x))))))*row1_29 u B a y x+
  (((-309680)*B+((-123872)*y+((2601312)*x))))*row1_20 u B a y x+
  (((123872)*a+((-309680)*x)))*row1_3 u B a y x+
  (((118917120)*a+((-499451904)*x)))*row1_18 u B a y x+
  (((-99540)*a+((-139356)*x)))*row1_23 u B a y x+
  (((-179172)*a+((592023)*x)))*row1_26 u B a y x+
  (((416209920)*y))*row1_10 u B a y x+
  (((-278712)*y))*row1_11 u B a y x+
  (((3425184)*y))*row1_12 u B a y x+
  (((3027024)*y+((-337892772)*x)))*row1_30 u B a y x+
  (((278712)*x))*row1_4 u B a y x+
  (((-61164)*x))*row1_5 u B a y x+
  (((-46823616)*x))*row1_22 u B a y x+
  (((-26756352)*x))*row1_24 u B a y x+
  (((309680)*x))*row1_25 u B a y x+
  (((15891120)*x))*row1_27 u B a y x+
  (((-15095060736)*x))*row1_28 u B a y x=((56))*row2_9 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_29, row1_20, row1_3, row1_18, row1_23, row1_26, row1_10, row1_11, row1_12, row1_30, row1_4, row1_5, row1_22, row1_24, row1_25, row1_27, row1_28, row2_9] <;> ring
theorem row2_9_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_9 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_3 := row1_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_10 := row1_10_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_24 := row1_24_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_25 := row1_25_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_9_identity u B a y x).symm
  have hz : ((56))*row2_9 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_29, z1_20, z1_3, z1_18, z1_23, z1_26, z1_10, z1_11, z1_12, z1_30, z1_4, z1_5, z1_22, z1_24, z1_25, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((56):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_9_zero
def row2_10 (u B a y x : ℂ) : ℂ := (((((8918784)*y+(1731518208))*B+(((517289472)*y+((-147159936)*x))*a+(((-80269056)*x+(-661264128))*y+((-535127040)*x+(1731518208)))))*u+(((((93647232)*x)*y)*a^2+((((-40134528)*x+(40134528))*y+(2204858304))*y+((1890744912)*x+(6579195840))))*B+((((-810486912)*y+(13906460208))*y+((-58365830376)*x+(-975969792)))*a+(((-2206109760)*y+((((345324168)*x+(1717985376))*x+(31005354192))*x+(23966252568)))*y+((((-270908064)*x+(2958632520))*x+(-6821619480))*x+(-364714560))))))*u+((((((31215744)*x+(-124862976))*x)*y+((((105353136)*x+(-749177856))*x+(468236160))*x))*B+((((-316059408)*x^2+(-3225733056))*a+(((95629184)*y+(((107264304)*x+(-504275328))*x+(2311883712)))*y+((((-182934612)*x+(-1592275968))*x+(-2438657856))*x+(-2928864960))))*a+(((((-1114848)*x+(4459392))*x+(110989312))*y+((((21819168)*x+(-1455900720))*x+(5255402016))*x+(-1058362368)))*y+(((((35774676)*x+(-5233622748))*x+(21866151648))*x+(-2696532288))*x+(-5345218368)))))*B+(((((-57335040)*a+(-9751942464))*a+(((1169710656)*y+(-22983643296))*y+(((3133648188)*x+(-49524381924))*x+(22096506288))))*a+((((-1981952)*y+(((-6689088)*x+(87842944))*x+(-1160768704)))*y+(((481607040)*x+(24761004488))*x+(-28132136328)))*y+((((-503926434)*x+(9545426286))*x+(-329914942896))*x+(-17899581360))))*a+((((-3963904)*y+((((-2508408)*x+(-24848976))*x+(692861600))*x+(16480960)))*y+(((((82568430)*x+(11248584))*x+(1860003828))*x+(-15707069360))*x+(-110909588208)))*y+(((((-429970599)*x+(-24670291257))*x+(-39052266672))*x+(-98191564824))*x+(12751005552))))))
theorem row2_10_identity (u B a y x : ℂ) :
  (((-93647232)*u+((-238391664)*B+((-20924641500)*a+((-16864773345)*x+(-52811462760))))))*row1_31 u B a y x+
  (((2247533568)*u+((-268120944)*B+((53266787952)*a+((-901115712)*y+((1373492736)*x+(358260892248)))))))*row1_32 u B a y x+
  (((-71921074176)*u+((-421921753344)*B+((1696278882816)*a+((1091931792000)*y+((38208070656)*x+(-5584690715520)))))))*row1_33 u B a y x+
  (((-193930039296)*u+((-46306326528)*a+((3329679360)*y+((106173795840)*x+(749927033856))))))*row1_34 u B a y x+
  (((1346736384)*u+((964715136)*B+((3030156864)*a+((6882919680)*y+((34389054560)*x+(-2235641856)))))))*row1_35 u B a y x+
  (((-1165387776)*u+((-5583530400)*B+((2949887808)*a+((11599692496)*y+((14075433456)*x))))))*row1_29 u B a y x+
  (((-998903808)*B+((1498355712)*y)))*row1_10 u B a y x+
  (((168342048)*B+((-173544672)*y+((18209184)*x))))*row1_20 u B a y x+
  (((655530624)*a+((89373648)*x)))*row1_4 u B a y x+
  (((-2508408)*a+((-264443646)*x)))*row1_5 u B a y x+
  (((371616)*a))*row1_8 u B a y x+
  (((4424831712)*a+((14808844176)*y)))*row1_12 u B a y x+
  (((-64643346432)*a+((-2996711424)*x)))*row1_18 u B a y x+
  (((54109944)*a+((3468416)*y+((84356832)*x))))*row1_23 u B a y x+
  (((-251019972)*a+((-433912397)*x)))*row1_26 u B a y x+
  (((1300656)*y+((-40970664)*x)))*row1_0 u B a y x+
  (((-89373648)*y))*row1_11 u B a y x+
  (((-3901968)*y+((1114848)*x)))*row1_25 u B a y x+
  (((12052913376)*y+((-99393315336)*x)))*row1_30 u B a y x+
  (((-1114848)*x))*row1_3 u B a y x+
  (((-31465469952)*x))*row1_19 u B a y x+
  (((1311061248)*x))*row1_22 u B a y x+
  (((-23063975424)*x))*row1_24 u B a y x+
  (((-26896678368)*x))*row1_27 u B a y x+
  (((-1623234041856)*x))*row1_28 u B a y x=((112))*row2_10 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_29, row1_10, row1_20, row1_4, row1_5, row1_8, row1_12, row1_18, row1_23, row1_26, row1_0, row1_11, row1_25, row1_30, row1_3, row1_19, row1_22, row1_24, row1_27, row1_28, row2_10] <;> ring
theorem row2_10_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_10 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_10 := row1_10_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_8 := row1_8_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_0 := row1_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_25 := row1_25_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_3 := row1_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_19 := row1_19_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_24 := row1_24_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_10_identity u B a y x).symm
  have hz : ((112))*row2_10 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_29, z1_10, z1_20, z1_4, z1_5, z1_8, z1_12, z1_18, z1_23, z1_26, z1_0, z1_11, z1_25, z1_30, z1_3, z1_19, z1_22, z1_24, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((112):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_10_zero
def row2_23 (u B a y x : ℂ) : ℂ := ((((((212352)*x^2)*a+(-6370560))*B+(((-1274112)*y+((3397632)*x))*a+(((-2123520)*x+(4671744))*y+((424704)*x+(-6370560)))))*u+(((2076000)*y+((119280)*x+(-22827840)))*B+((((-444928)*y+(11620848))*y+((-34566000)*x+(8494080)))*a+(((-1314560)*y+(((1124400)*x+(41494224))*x+(41050224)))*y+((((1433376)*x+(2898960))*x+(1518768))*x+(2229696))))))*u+((((7963200)*a+((((-79632)*x+(147888))*x+(3562464))*y+((((-59724)*x+(3196656))*x+(6099552))*x+(10086720))))*a+(((((159264)*x+(-2655648))*x+(5543840))*x+(3963904))*y+(((((477792)*x+(-5454912))*x+(32248128))*x+(-18215040))*x+(29198400))))*B+((((-13235904)*a+(((222464)*y+(-20192560))*y+(((-3306312)*x+(-69823284))*x+(14540112))))*a+((((283136)*x+(-3072896))*y+(((-1472832)*x+(15466912))*x+(-16099360)))*y+((((-6908868)*x+(-15203586))*x+(-351544872))*x+(-62000784))))*a+(((((841824)*x+(241424))*x+(-6258800))*y+((((-554112)*x+(-2722236))*x+(-16408496))*x+(-118603616)))*y+(((((-707130)*x+(-25158657))*x+(-81376944))*x+(-110027280))*x+(52905744))))))
theorem row2_23_identity (u B a y x : ℂ) :
  (((-1486464)*u+((278712)*B+((421596)*a+((9610083)*x+(-29590428))))))*row1_31 u B a y x+
  (((4459392)*u+((-836136)*B+((14813736)*a+((-597240)*y+((-2787120)*x+(198591540)))))))*row1_32 u B a y x+
  (((-142700544)*u+((36849792)*B+((1235928960)*a+((425030592)*y+((33445440)*x+(-2704450560)))))))*row1_33 u B a y x+
  (((356751360)*u+((59458560)*a+((27747328)*y+((1698181632)*x+(-1456734720))))))*row1_34 u B a y x+
  (((-2477440)*u+((-1238720)*B+((-5574240)*a+((3802624)*y+((-5213600)*x+(6936832)))))))*row1_35 u B a y x+
  (((2477440)*u+((10591056)*B+((-1672272)*a+((-7429072)*y+((7521696)*x))))))*row1_29 u B a y x+
  (((-309680)*B+((247744)*y+((216776)*x))))*row1_20 u B a y x+
  (((4424)*a))*row1_8 u B a y x+
  (((118917120)*a+((-23783424)*x)))*row1_18 u B a y x+
  (((-99540)*a+((-139356)*x)))*row1_23 u B a y x+
  (((358344)*a+((586941)*x)))*row1_26 u B a y x+
  (((23783424)*y))*row1_10 u B a y x+
  (((-278712)*y))*row1_11 u B a y x+
  (((5132736)*y))*row1_12 u B a y x+
  (((4734576)*y+((-40492956)*x)))*row1_30 u B a y x+
  (((-17696)*x))*row1_3 u B a y x+
  (((278712)*x))*row1_4 u B a y x+
  (((-91656)*x))*row1_5 u B a y x+
  (((-2787120)*x))*row1_22 u B a y x+
  (((-26756352)*x))*row1_24 u B a y x+
  (((17696)*x))*row1_25 u B a y x+
  (((-17116848)*x))*row1_27 u B a y x+
  (((-1209172608)*x))*row1_28 u B a y x=((56))*row2_23 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_29, row1_20, row1_8, row1_18, row1_23, row1_26, row1_10, row1_11, row1_12, row1_30, row1_3, row1_4, row1_5, row1_22, row1_24, row1_25, row1_27, row1_28, row2_23] <;> ring
theorem row2_23_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_23 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_8 := row1_8_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_10 := row1_10_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_3 := row1_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_24 := row1_24_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_25 := row1_25_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_23_identity u B a y x).symm
  have hz : ((56))*row2_23 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_29, z1_20, z1_8, z1_18, z1_23, z1_26, z1_10, z1_11, z1_12, z1_30, z1_3, z1_4, z1_5, z1_22, z1_24, z1_25, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((56):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_23_zero

def row2_25 (u B a y x : ℂ) : ℂ := ((((((15168)*x^2)*a+((-30336)*y+((45504)*x)))*a+(((-30336)*x+(-30336))*y))*u+(((-4608)*y+((71664)*x))*B+(((320576)*y+((-468096)*x))*a+((((-49944)*x+(498168))*x+(538480))*y+((((25596)*x+(-7368))*x+(-321072))*x)))))*u+((((-4608)*y+((4608)*x))*a+((((-144)*x+(576))*x)*y+((((3924)*x+(93744))*x+(-83808))*x)))*B+((((-74592)*a+((-250096)*y+(((-28404)*x+(-1172412))*x+(220848))))*a+(((-256)*y+(((-8928)*x+(57096))*x+(-573200)))*y+((((-14202)*x+(-650478))*x+(-4516920))*x+(-220848))))*a+(((4096)*y+((((-9900)*x+(60684))*x+(-71232))*x+(-2286864)))*y+(((((-22269)*x+(-204759))*x+(-883608))*x+(-3963792))*x+(146256))))))
theorem row2_25_identity (u B a y x : ℂ) :
  (((-6636)*u+((2016)*a+((1134)*x+(-92323)))))*row1_31 u B a y x+
  (((19908)*u+((-14868)*a+((-14931)*x+(617925)))))*row1_32 u B a y x+
  (((-637056)*u+((64512)*B+((4368672)*a+((1477168)*y+((-212352)*x+(-8851584)))))))*row1_33 u B a y x+
  (((13272)*u+((-19908)*a+((-672)*y+((7938)*x)))))*row1_29 u B a y x+
  (((212352)*a+((106176)*y)))*row1_10 u B a y x+
  (((-2016)*y))*row1_12 u B a y x+
  (((-2016)*y+((-88291)*x)))*row1_30 u B a y x+
  (((112)*y+((-59360)*x)))*row1_35 u B a y x+
  (((-79)*x))*row1_3 u B a y x+
  (((36)*x))*row1_5 u B a y x+
  (((553)*x))*row1_20 u B a y x+
  (((-14931)*x))*row1_22 u B a y x+
  (((79)*x))*row1_25 u B a y x+
  (((6)*x))*row1_26 u B a y x+
  (((10836)*x))*row1_27 u B a y x+
  (((-4368672)*x))*row1_28 u B a y x+
  (((1108800)*x))*row1_34 u B a y x=((14))*row2_25 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_29, row1_10, row1_12, row1_30, row1_35, row1_3, row1_5, row1_20, row1_22, row1_25, row1_26, row1_27, row1_28, row1_34, row2_25] <;> ring
theorem row2_25_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_25 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_10 := row1_10_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_3 := row1_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_25 := row1_25_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_25_identity u B a y x).symm
  have hz : ((14))*row2_25 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_29, z1_10, z1_12, z1_30, z1_35, z1_3, z1_5, z1_20, z1_22, z1_25, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((14):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_25_zero
def row2_26 (u B a y x : ℂ) : ℂ := ((((-910080)*B+((910080)*y+(-910080)))*u+((((68256)*x^2)*a^2+((305184)*y+((-739920)*x+(-3261120))))*B+((((-136512)*y+(31632))*y+((-2549376)*x+(606720)))*a+(((-333696)*y+(((117216)*x+(2678448))*x+(3056688)))*y+(((44352)*x+(-23088))*x+(379200))))))*u+((((1137600)*a+((517536)*y+((((68256)*x+(-34128))*x+(1090272))*x+(1440960))))*a+((((-281736)*x+(765440))*x+(566272))*y+((((-442314)*x+(3020904))*x+(-2177088))*x+(4171200))))*B+((((-1088640)*a+(((68256)*y+(-1460016))*y+(((-545292)*x+(-108216))*x+(656208))))*a+(((-354240)*y+(((196452)*x+(3168960))*x+(969360)))*y+((((-272646)*x+(-672912))*x+(-20124480))*x+(-3841488))))*a+(((((108072)*x+(-93536))*x+(-568736))*y+((((112050)*x+(-525888))*x+(1198976))*x+(-651952)))*y+(((((-136323)*x+(-1554768))*x+(-4227696))*x+(78192))*x+(1236048))))))
theorem row2_26_identity (u B a y x : ℂ) :
  (((19908)*B+((278775)*a+((719523)*x+(-1216530)))))*row1_31 u B a y x+
  (((-59724)*B+((1226988)*a+(7518042))))*row1_32 u B a y x+
  (((2390976)*B+((35368704)*a+((15960672)*y+(-106751232)))))*row1_33 u B a y x+
  (((25482240)*u+((4247040)*a+((1981952)*y+((99445248)*x+(-104052480))))))*row1_34 u B a y x+
  (((-176960)*u+((-88480)*B+((-398160)*a+((278992)*y+((61740)*x+(353920)))))))*row1_35 u B a y x+
  (((-22120)*B+((22120)*y)))*row1_20 u B a y x+
  (((756504)*B+((-625464)*y+((393120)*x))))*row1_29 u B a y x+
  (((119448)*a+((-19908)*y)))*row1_11 u B a y x+
  (((8494080)*a))*row1_18 u B a y x+
  (((-7110)*a+((-9954)*x)))*row1_23 u B a y x+
  (((31995)*a+((43623)*x)))*row1_26 u B a y x+
  (((393120)*y))*row1_12 u B a y x+
  (((253764)*y+((-1783782)*x)))*row1_30 u B a y x+
  (((19908)*x))*row1_4 u B a y x+
  (((-7020)*x))*row1_5 u B a y x+
  (((-1911168)*x))*row1_24 u B a y x+
  (((-1376424)*x))*row1_27 u B a y x+
  (((-35368704)*x))*row1_28 u B a y x=((28))*row2_26 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_20, row1_29, row1_11, row1_18, row1_23, row1_26, row1_12, row1_30, row1_4, row1_5, row1_24, row1_27, row1_28, row2_26] <;> ring
theorem row2_26_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_26 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_24 := row1_24_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_26_identity u B a y x).symm
  have hz : ((28))*row2_26 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_20, z1_29, z1_11, z1_18, z1_23, z1_26, z1_12, z1_30, z1_4, z1_5, z1_24, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((28):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_26_zero
def row2_59 (u B a y x : ℂ) : ℂ := ((((((16)*y)*a+((-16)*y))*B+((((-16)*y+(16))*y)*a+(((16)*y+(-16))*y)))*u+(((32)*x)*B+(((-112)*x)*a+(((-32)*y+(((16)*x+(32))*x+(96)))*y+((-16)*x^2)))))*u+((((16)*y+((-16)*x))*a+(((-16)*x+(32))*x))*B+((((-16)*y+((-108)*x+(32)))*a+(((-16)*y+((16)*x+(-48)))*y+(((-86)*x+(-392))*x+(-32))))*a+((((-4)*x+(-16))*x+(-224))*y+((((-27)*x+(-80))*x+(-464))*x+(32))))))
theorem row2_59_identity (u B a y x : ℂ) :
  ((1))*row1_32 u B a y x+
  (((-16)*B+((16)*y+(-16))))*row1_33 u B a y x+
  (((16)*y))*row1_18 u B a y x+
  (((1)*x))*row1_27 u B a y x+
  (((-1)*x))*row1_30 u B a y x+
  (((-16)*x))*row1_34 u B a y x=((1))*row2_59 u B a y x := by
  simp only [row1_32, row1_33, row1_18, row1_27, row1_30, row1_34, row2_59] <;> ring
theorem row2_59_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_59 u B a y x=0 := by
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_59_identity u B a y x).symm
  have hz : ((1))*row2_59 u B a y x=0 := by
    simpa only [z1_32, z1_33, z1_18, z1_27, z1_30, z1_34,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_59_zero
def row2_65 (u B a y x : ℂ) : ℂ := ((((25482240)*B+((-25482240)*y+(25482240)))*u+(((-22446912)*y+((120464400)*x+(91311360)))*B+((((2593728)*y+(52302288))*y+((-43508304)*x+(-16988160)))*a+(((6886272)*y+(((-39751056)*x+(-147354096))*x+(10674000)))*y+(((10914480)*x+(-47221296))*x+(-10617600))))))*u+((((-31852800)*a+((((1433376)*x+(-4095360))*x+(-28392768))*y+((((238896)*x+(-13105152))*x+(-12803520))*x+(-40346880))))*a+(((((-1194480)*x+(12227832))*x+(-19677536))*x+(-15855616))*y+(((((-2329236)*x+(26287398))*x+(-132311016))*x+(63656448))*x+(-116793600))))*B+((((((6689088)*y+(3822336))*a+(53338752))*a+(((1251360)*y+(8488800))*y+(((92545524)*x+(-127410588))*x+(28014480))))*a+((((-2123520)*x+(15463872))*y+(((1994148)*x+(-12963744))*x+(-152696976)))*y+((((62637138)*x+(216778446))*x+(67761624))*x+(64995696))))*a+(((((-3486744)*x+(-3266176))*x+(37276352))*y+((((2166930)*x+(58497876))*x+(279272752))*x+(-233895824)))*y+(((((24330861)*x+(16707519))*x+(342681408))*x+(-931637088))*x+(34635792))))))
theorem row2_65_identity (u B a y x : ℂ) :
  (((-2229696)*B+((19185264)*a+((-56666547)*x+(267331176)))))*row1_31 u B a y x+
  (((6689088)*B+((-242813088)*a+((11467008)*y+(-1386141624)))))*row1_32 u B a y x+
  (((1289207808)*B+((-6323304960)*a+((-3747268224)*y+(17319439872)))))*row1_33 u B a y x+
  (((-2854010880)*u+((-475668480)*a+((-221978624)*y+((-12997039104)*x+(11653877760))))))*row1_34 u B a y x+
  (((19819520)*u+((9909760)*B+((44593920)*a+((-28517440)*y+((-55166160)*x+(-39639040)))))))*row1_35 u B a y x+
  (((2477440)*B+((-2477440)*y)))*row1_20 u B a y x+
  (((-84728448)*B+((48444816)*y+((-79387056)*x))))*row1_29 u B a y x+
  (((-951336960)*a))*row1_18 u B a y x+
  (((796320)*a+((1114848)*x)))*row1_23 u B a y x+
  (((-3026016)*a+((-4349679)*x)))*row1_26 u B a y x+
  (((2229696)*y))*row1_11 u B a y x+
  (((-63619920)*y))*row1_12 u B a y x+
  (((-63779184)*y+((392978376)*x)))*row1_30 u B a y x+
  (((-2229696)*x))*row1_4 u B a y x+
  (((1136070)*x))*row1_5 u B a y x+
  (((214050816)*x))*row1_24 u B a y x+
  (((162237600)*x))*row1_27 u B a y x+
  (((6323304960)*x))*row1_28 u B a y x=((112))*row2_65 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_20, row1_29, row1_18, row1_23, row1_26, row1_11, row1_12, row1_30, row1_4, row1_5, row1_24, row1_27, row1_28, row2_65] <;> ring
theorem row2_65_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_65 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_24 := row1_24_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_65_identity u B a y x).symm
  have hz : ((112))*row2_65 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_20, z1_29, z1_18, z1_23, z1_26, z1_11, z1_12, z1_30, z1_4, z1_5, z1_24, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((112):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_65_zero
def row2_70 (u B a y x : ℂ) : ℂ := ((((((2528)*x)*a)*B+((-9952)*y+((-8624)*x)))*B+((((2528)*y+(-64816))*y+((256624)*x))*a+(((12640)*y+(((-11472)*x+(-173520))*x+(-125040)))*y+(((8880)*x+(39088))*x))))*u+(((((2528)*x+(-2528))*x)*B+(((2528)*a+((-9952)*y+((7424)*x+(-2528))))*a+((((4824)*x+(-24352))*x+(-2528))*y+((((16750)*x+(-99240))*x+(30560))*x+(2528)))))*B+((((42880)*a+(((-5056)*y+(104704))*y+(((8748)*x+(231316))*x+(-96912))))*a+(((6048)*y+(((-5852)*x+(-111200))*x+(136656)))*y+((((4374)*x+(72886))*x+(1524920))*x+(96912))))*a+(((((-632)*x+(-2528))*x+(-3232))*y+((((-3942)*x+(-4668))*x+(66832))*x+(530416)))*y+(((((2187)*x+(104571))*x+(271328))*x+(635200))*x+(-54032))))))
theorem row2_70_identity (u B a y x : ℂ) :
  (((157584)*a+((118503)*x+(733992))))*row1_31 u B a y x+
  (((-495264)*a+(-4971288)))*row1_32 u B a y x+
  (((3343872)*B+((-27503616)*a+((-14292096)*y+(70834176)))))*row1_33 u B a y x+
  (((17696)*B+((-70224)*y+((-157584)*x))))*row1_29 u B a y x+
  (((-157584)*y))*row1_12 u B a y x+
  (((-104496)*y+((1208424)*x)))*row1_30 u B a y x+
  (((-90048)*y+((-310352)*x)))*row1_35 u B a y x+
  (((2814)*x))*row1_5 u B a y x+
  (((849408)*x))*row1_19 u B a y x+
  (((-316)*x))*row1_23 u B a y x+
  (((1891)*x))*row1_26 u B a y x+
  (((286272)*x))*row1_27 u B a y x+
  (((27503616)*x))*row1_28 u B a y x+
  (((-9364992)*x))*row1_34 u B a y x=((336))*row2_70 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_29, row1_12, row1_30, row1_35, row1_5, row1_19, row1_23, row1_26, row1_27, row1_28, row1_34, row2_70] <;> ring
theorem row2_70_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_70 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_19 := row1_19_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_70_identity u B a y x).symm
  have hz : ((336))*row2_70 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_29, z1_12, z1_30, z1_35, z1_5, z1_19, z1_23, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((336):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_70_zero
def row2_75 (u B a y x : ℂ) : ℂ := ((((16128)*y+((-157920)*x))*B+(((-17280)*y+((398352)*x))*a+((((44928)*x+(-40032))*x+(-44928))*y+(((-14976)*x+(44928))*x))))*u+((((16128)*y+((((25596)*x+(-102384))*x+(-16128))*x))*a+((((-5184)*x+(20736))*x)*y+(((((-12798)*x+(-12312))*x+(212256))*x+(54432))*x)))*B+((((((153576)*x)*a+(22176))*a+((63216)*y+(((-681264)*x+(334668))*x+(-202272))))*a+(((-9216)*y+(((-25632)*x+(-4864))*x+(114624)))*y+(((((-19197)*x+(34776))*x+(160974))*x+(-1651992))*x+(202272))))*a+(((-34560)*y+((((-3744)*x+(-36540))*x+(-382688))*x+(702528)))*y+(((((-25272)*x+(32319))*x+(740640))*x+(4038720))*x+(-180096))))))
theorem row2_75_identity (u B a y x : ℂ) :
  (((-1008)*a+((-567)*x+(-8862))))*row1_31 u B a y x+
  (((3168)*a+(41916)))*row1_32 u B a y x+
  (((-32256)*B+((140160)*a+((141792)*y+(-837504)))))*row1_33 u B a y x+
  (((2844)*a+((336)*y+((-414)*x))))*row1_29 u B a y x+
  (((1008)*y))*row1_12 u B a y x+
  (((1008)*y+((-10878)*x)))*row1_30 u B a y x+
  (((576)*y+((6928)*x)))*row1_35 u B a y x+
  (((-18)*x))*row1_5 u B a y x+
  (((-3)*x))*row1_26 u B a y x+
  (((-1152)*x))*row1_27 u B a y x+
  (((-140160)*x))*row1_28 u B a y x+
  (((-76608)*x))*row1_34 u B a y x=((2))*row2_75 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_29, row1_12, row1_30, row1_35, row1_5, row1_26, row1_27, row1_28, row1_34, row2_75] <;> ring
theorem row2_75_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_75 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_75_identity u B a y x).symm
  have hz : ((2))*row2_75 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_29, z1_12, z1_30, z1_35, z1_5, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((2):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_75_zero

def row2_76 (u B a y x : ℂ) : ℂ := ((((((212352)*x+(-212352))*y+(6370560))*B+(((1486464)*y+((-3185280)*x))*a+(((2760576)*x+(-4247040))*y+((-637056)*x+(6370560)))))*u+(((-2055840)*y+((-1789872)*x+(22827840)))*B+((((232576)*y+(-16655472))*y+((44006424)*x+(-8494080)))*a+(((1526912)*y+(((-937416)*x+(-52740144))*x+(-48032472)))*y+((((-1791720)*x+(-2271144))*x+(6631416))*x+(-2229696))))))*u+((((-7963200)*a+((((79632)*x+(-147888))*x+(-3329952))*y+((((59724)*x+(-3196656))*x+(-6332064))*x+(-10086720))))*a+(((((-159264)*x+(2626416))*x+(-5214560))*x+(-4176256))*y+(((((-477792)*x+(5229540))*x+(-33975504))*x+(20207520))*x+(-29198400))))*B+((((14551008)*a+(((-222464)*y+(24386848))*y+(((4946076)*x+(90282576))*x+(-18628560))))*a+((((-283136)*x+(3020928))*y+(((1704336)*x+(-15449608))*x+(27013816)))*y+((((7728750)*x+(29692704))*x+(428006040))*x+(66089232))))*a+(((((-841824)*x+(-453776))*x+(5710000))*y+((((588300)*x+(2220336))*x+(19679792))*x+(160484672)))*y+(((((1117071)*x+(28140048))*x+(101761392))*x+(181103880))*x+(-55679088))))))
theorem row2_76_identity (u B a y x : ℂ) :
  (((929040)*u+((-139356)*B+((-414246)*a+((-4919481)*x+(17717574))))))*row1_31 u B a y x+
  (((-2787120)*u+((418068)*B+((-6289668)*a+((298620)*y+((1440012)*x+(-119256606)))))))*row1_32 u B a y x+
  (((89187840)*u+((-24935232)*B+((-771484224)*a+((-259273056)*y+((-16722720)*x+(1579809504)))))))*row1_33 u B a y x+
  (((-178375680)*u+((-29729280)*a+((-7927808)*y+((-898369920)*x+(728367360))))))*row1_34 u B a y x+
  (((1238720)*u+((619360)*B+((2787120)*a+((-1855840)*y+((4364920)*x+(-3468416)))))))*row1_35 u B a y x+
  (((-1610336)*u+((-5295528)*B+((1672272)*a+((3782352)*y+((-3975468)*x))))))*row1_29 u B a y x+
  (((5945856)*B+((-14864640)*y)))*row1_10 u B a y x+
  (((154840)*B+((-123872)*y+((-108388)*x))))*row1_20 u B a y x+
  (((-2212)*a))*row1_8 u B a y x+
  (((-59458560)*a+((17837568)*x)))*row1_18 u B a y x+
  (((49770)*a+((69678)*x)))*row1_23 u B a y x+
  (((-179172)*a+((-294076)*x)))*row1_26 u B a y x+
  (((139356)*y))*row1_11 u B a y x+
  (((-2362920)*y))*row1_12 u B a y x+
  (((-2163840)*y+((22761942)*x)))*row1_30 u B a y x+
  (((11060)*x))*row1_3 u B a y x+
  (((-139356)*x))*row1_4 u B a y x+
  (((42195)*x))*row1_5 u B a y x+
  (((1811628)*x))*row1_22 u B a y x+
  (((13378176)*x))*row1_24 u B a y x+
  (((-11060)*x))*row1_25 u B a y x+
  (((7848120)*x))*row1_27 u B a y x+
  (((758106048)*x))*row1_28 u B a y x=((28))*row2_76 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_29, row1_10, row1_20, row1_8, row1_18, row1_23, row1_26, row1_11, row1_12, row1_30, row1_3, row1_4, row1_5, row1_22, row1_24, row1_25, row1_27, row1_28, row2_76] <;> ring
theorem row2_76_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_76 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_10 := row1_10_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_8 := row1_8_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_3 := row1_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_24 := row1_24_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_25 := row1_25_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_76_identity u B a y x).symm
  have hz : ((28))*row2_76 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_29, z1_10, z1_20, z1_8, z1_18, z1_23, z1_26, z1_11, z1_12, z1_30, z1_3, z1_4, z1_5, z1_22, z1_24, z1_25, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((28):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_76_zero
def row2_77 (u B a y x : ℂ) : ℂ := (((((-17837568)*y+(345284352))*B+(((-1034578944)*y+((294319872)*x))*a+(((160538112)*x+(-2485792512))*y+((1070254080)*x+(345284352)))))*u+(((((13378176)*x+(-13378176))*y)*B+((((-10033632)*x+(10033632))*y+(-1743809280))*y+((-9297887088)*x+(1201593792))))*B+((((-305483520)*y+(1322401968))*y+((18256826448)*x+(-586940928)))*a+(((-587502144)*y+((((-690648336)*x+(4145927040))*x+(9676504080))*x+(-9362482848)))*y+((((541816128)*x+(-11637860592))*x+(-1909259904))*x+(-143868480))))))*u+(((((-13378176)*y+((13378176)*x))*a+((((-2229696)*x+(8918784))*x)*y+((((-1672272)*x+(91417536))*x+(-71350272))*x)))*B+((((22575672)*x^2+(-330525888))*a+(((6069728)*y+(((6211296)*x+(35288352))*x+(-1838447488)))*y+((((61097652)*x+(-414177408))*x+(928589952))*x+(-528862656))))*a+(((((2229696)*x+(-8918784))*x+(-7927808))*y+((((-66214008)*x+(682962744))*x+(-1716843808))*x+(-420173824)))*y+(((((-223935138)*x+(4258567902))*x+(-8067324408))*x+(-1325696256))*x+(-1829306304)))))*B+(((((114670080)*a+(1317186048))*a+(((158953056)*y+(6476743248))*y+(((-12549191436)*x+(12159701616))*x+(-11227834512))))*a+((((3963904)*y+(((13378176)*x+(-175685888))*x+(1041234048)))*y+(((1695756612)*x+(-3105251344))*x+(-3571821760)))*y+((((-2133094662)*x+(-54858986652))*x+(78659811552))*x+(14736101904))))*a+((((7927808)*y+((((5016816)*x+(-212570040))*x+(-346808736))*x+(5321050912)))*y+(((((-165136860)*x+(1692827898))*x+(-473711400))*x+(-9379074720))*x+(21443685744)))*y+(((((-710532567)*x+(9451772658))*x+(-34803638256))*x+(906036480))*x+(-14078481168))))))
theorem row2_77_identity (u B a y x : ℂ) :
  (((187294464)*u+((-315316176)*B+((5421065412)*a+((2563438563)*x+(-17538175032))))))*row1_31 u B a y x+
  (((-4495067136)*u+((700124544)*B+((-29023006656)*a+((537993792)*y+((-2746985472)*x+(67710438264)))))))*row1_32 u B a y x+
  (((143842148352)*u+((166448427264)*B+((444650605056)*a+((323187801216)*y+((-76416141312)*x+(-589418635008)))))))*row1_33 u B a y x+
  (((-38671847424)*u+((-5113436160)*a+((-9267607552)*y+((-61693298688)*x+(161905658880))))))*row1_34 u B a y x+
  (((268554496)*u+((106529920)*B+((604247616)*a+((-2509226944)*y+((-18171312880)*x+(-897824256)))))))*row1_35 u B a y x+
  (((2330775552)*u+((-929040000)*B+((-5899775616)*a+((-1398299504)*y+((-2969096592)*x))))))*row1_29 u B a y x+
  (((1997807616)*B+((-2996711424)*y)))*row1_10 u B a y x+
  (((33569312)*B+((-23164064)*y+((-36418368)*x))))*row1_20 u B a y x+
  (((-3901968)*B+((-33505164)*a+((-16709633)*x))))*row1_26 u B a y x+
  (((5016816)*a+((79212822)*x)))*row1_5 u B a y x+
  (((-743232)*a))*row1_8 u B a y x+
  (((-8849663424)*a+((-4435918032)*y)))*row1_12 u B a y x+
  (((-12890615808)*a+((5993422848)*x)))*row1_18 u B a y x+
  (((10790136)*a+((867104)*y+((11194932)*x))))*row1_23 u B a y x+
  (((-2601312)*y+((81941328)*x)))*row1_0 u B a y x+
  (((233374848)*y))*row1_11 u B a y x+
  (((-5424735120)*y+((-8267621544)*x)))*row1_30 u B a y x+
  (((2229696)*x))*row1_3 u B a y x+
  (((-233374848)*x))*row1_4 u B a y x+
  (((-2622122496)*x))*row1_22 u B a y x+
  (((4173990912)*x))*row1_24 u B a y x+
  (((-2229696)*x))*row1_25 u B a y x+
  (((18619979952)*x))*row1_27 u B a y x+
  (((-590740286976)*x))*row1_28 u B a y x=((112))*row2_77 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_29, row1_10, row1_20, row1_26, row1_5, row1_8, row1_12, row1_18, row1_23, row1_0, row1_11, row1_30, row1_3, row1_4, row1_22, row1_24, row1_25, row1_27, row1_28, row2_77] <;> ring
theorem row2_77_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_77 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_10 := row1_10_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_8 := row1_8_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_0 := row1_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_3 := row1_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_24 := row1_24_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_25 := row1_25_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_77_identity u B a y x).symm
  have hz : ((112))*row2_77 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_29, z1_10, z1_20, z1_26, z1_5, z1_8, z1_12, z1_18, z1_23, z1_0, z1_11, z1_30, z1_3, z1_4, z1_22, z1_24, z1_25, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((112):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_77_zero
def row2_78 (u B a y x : ℂ) : ℂ := ((((((30336)*x+(30336))*y)*a+(((60672)*x+(60672))*y))*u+(((22464)*y+((-350784)*x))*B+(((-889728)*y+((1843992)*x))*a+((((87768)*x+(-1564704))*x+(-1331544))*y+((((-51192)*x+(69336))*x+(1225368))*x)))))*u+((((22464)*y+((-22464)*x))*a+((((-720)*x+(2880))*x)*y+((((-20196)*x+(-282096))*x+(263520))*x)))*B+((((218592)*a+((746640)*y+(((96876)*x+(3500388))*x+(-787968))))*a+(((-1280)*y+(((34992)*x+(-108888))*x+(1786152)))*y+((((48438)*x+(1777698))*x+(13517136))*x+(787968))))*a+(((-25024)*y+((((30132)*x+(-178164))*x+(235392))*x+(7082016)))*y+(((((24219)*x+(566001))*x+(2837952))*x+(12183624))*x+(-569376))))))
theorem row2_78_identity (u B a y x : ℂ) :
  (((53088)*u+((-39312)*a+((-22113)*x+(885360)))))*row1_31 u B a y x+
  (((-159264)*u+((260064)*a+((119448)*x+(-6308568)))))*row1_32 u B a y x+
  (((5096448)*u+((-1257984)*B+((-47045376)*a+((-14165760)*y+(78958656))))))*row1_33 u B a y x+
  (((-106176)*u+((238896)*a+((13104)*y+((-80136)*x)))))*row1_29 u B a y x+
  (((-849408)*y))*row1_10 u B a y x+
  (((39312)*y))*row1_12 u B a y x+
  (((39312)*y+((806736)*x)))*row1_30 u B a y x+
  (((2240)*y+((467376)*x)))*row1_35 u B a y x+
  (((632)*x))*row1_3 u B a y x+
  (((-702)*x))*row1_5 u B a y x+
  (((119448)*x))*row1_22 u B a y x+
  (((-632)*x))*row1_25 u B a y x+
  (((-117)*x))*row1_26 u B a y x+
  (((-181440)*x))*row1_27 u B a y x+
  (((47045376)*x))*row1_28 u B a y x+
  (((-13499136)*x))*row1_34 u B a y x=((56))*row2_78 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_29, row1_10, row1_12, row1_30, row1_35, row1_3, row1_5, row1_22, row1_25, row1_26, row1_27, row1_28, row1_34, row2_78] <;> ring
theorem row2_78_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_78 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_10 := row1_10_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_3 := row1_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_25 := row1_25_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_78_identity u B a y x).symm
  have hz : ((56))*row2_78 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_29, z1_10, z1_12, z1_30, z1_35, z1_3, z1_5, z1_22, z1_25, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((56):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_78_zero
def row2_81 (u B a y x : ℂ) : ℂ := ((((910080)*B+((-910080)*y+(910080)))*u+(((((22752)*x+(-22752))*y+(-541056))*y+((1579152)*x+(3261120)))*B+((((273024)*y+(-1155408))*y+((6920640)*x+(-606720)))*a+(((743232)*y+(((-694656)*x+(-6805488))*x+(-5072976)))*y+(((299808)*x+(560496))*x+(-379200))))))*u+((((((45504)*x)*y+((153576)*x^2+(-1137600)))*a+(((-22752)*y+((113760)*x+(-753408)))*y+((((76788)*x+(614304))*x+(-854400))*x+(-1440960))))*a+(((((5688)*x+(431496))*x+(-1068704))*x+(-566272))*y+(((((38394)*x+(883314))*x+(-4910760))*x+(2834304))*x+(-4171200))))*B+((((2217600)*a+(((-204768)*y+(3557232))*y+(((1332612)*x+(2810376))*x+(-2074896))))*a+(((443520)*y+(((-433044)*x+(-6442368))*x+(1136784)))*y+((((666306)*x+(3413160))*x+(48760608))*x+(5260176))))*a+(((((-85320)*x+(2528))*x+(95840))*y+((((-236466)*x+(509616))*x+(788800))*x+(8232112)))*y+(((((333153)*x+(3556116))*x+(11059920))*x+(4282416))*x+(-1525776))))))
theorem row2_81_identity (u B a y x : ℂ) :
  (((-318528)*B+((28980)*a+((-1965789)*x+(12153960)))))*row1_31 u B a y x+
  (((1433376)*B+((-8537760)*a+((318528)*y+(-74813256)))))*row1_32 u B a y x+
  (((-6080256)*B+((-398329344)*a+((-205930368)*y+(1086801408)))))*row1_33 u B a y x+
  (((-101928960)*u+((-16988160)*a+((-7927808)*y+((-474872832)*x+(416209920))))))*row1_34 u B a y x+
  (((707840)*u+((353920)*B+((1592640)*a+((-1906240)*y+((-2974608)*x+(-1415680)))))))*row1_35 u B a y x+
  (((88480)*B+((-88480)*y)))*row1_20 u B a y x+
  (((-2866752)*B+((1961232)*y+((-2716560)*x))))*row1_29 u B a y x+
  (((-33976320)*a))*row1_18 u B a y x+
  (((28440)*a+((36972)*x)))*row1_23 u B a y x+
  (((-127980)*a+((-158289)*x)))*row1_26 u B a y x+
  (((477792)*y))*row1_11 u B a y x+
  (((-2716560)*y))*row1_12 u B a y x+
  (((-2238768)*y+((18303768)*x)))*row1_30 u B a y x+
  (((-477792)*x))*row1_4 u B a y x+
  (((48510)*x))*row1_5 u B a y x+
  (((8917776)*x))*row1_27 u B a y x+
  (((398329344)*x))*row1_28 u B a y x=((112))*row2_81 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_20, row1_29, row1_18, row1_23, row1_26, row1_11, row1_12, row1_30, row1_4, row1_5, row1_27, row1_28, row2_81] <;> ring
theorem row2_81_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_81 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_81_identity u B a y x).symm
  have hz : ((112))*row2_81 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_20, z1_29, z1_18, z1_23, z1_26, z1_11, z1_12, z1_30, z1_4, z1_5, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((112):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_81_zero
def row2_83 (u B a y x : ℂ) : ℂ := (((((121344)*y+((-45504)*x))*a+((((15168)*x+(-15168))*y+(((-30336)*x+(45504))*x+(242688)))*y+((-91008)*x)))*u+(((27456)*y+((-424944)*x))*B+((((-15168)*y+(-1472544))*y+((2752416)*x))*a+(((((3792)*x+(94632))*x+(-2945736))*x+(-2075952))*y+(((((25596)*x+(-127980))*x+(460152))*x+(1674000))*x)))))*u+((((27456)*y+((-27456)*x))*a+((((-7200)*x+(28800))*x)*y+((((-55968)*x+(-401664))*x+(435840))*x)))*B+((((380928)*a+((1281648)*y+(((252072)*x+(6020676))*x+(-1186800))))*a+(((-12800)*y+(((27600)*x+(-82104))*x+(3550512)))*y+((((23652)*x+(3619074))*x+(22429512))*x+(1186800))))*a+(((-53056)*y+((((62424)*x+(-294228))*x+(488256))*x+(12085872)))*y+(((((11826)*x+(510237))*x+(5542200))*x+(21575760))*x+(-805872))))))
theorem row2_83_identity (u B a y x : ℂ) :
  (((53088)*u+((-101136)*a+((2835)*x+(1759716)))))*row1_31 u B a y x+
  (((556752)*a+((238896)*x+(-11968572))))*row1_32 u B a y x+
  (((-1537536)*B+((-93104256)*a+((-28155456)*y+((2866752)*x+(132781824))))))*row1_33 u B a y x+
  (((-212352)*u+((477792)*a+((-1680)*y+((-137760)*x)))))*row1_29 u B a y x+
  (((101136)*y))*row1_12 u B a y x+
  (((101136)*y+((1557444)*x)))*row1_30 u B a y x+
  (((22400)*y+((904512)*x)))*row1_35 u B a y x+
  (((-1806)*x))*row1_5 u B a y x+
  (((238896)*x))*row1_22 u B a y x+
  (((-632)*x))*row1_25 u B a y x+
  (((2543)*x))*row1_26 u B a y x+
  (((-460656)*x))*row1_27 u B a y x+
  (((98837760)*x))*row1_28 u B a y x+
  (((-22869504)*x))*row1_34 u B a y x=((56))*row2_83 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_29, row1_12, row1_30, row1_35, row1_5, row1_22, row1_25, row1_26, row1_27, row1_28, row1_34, row2_83] <;> ring
theorem row2_83_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_83 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_25 := row1_25_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_83_identity u B a y x).symm
  have hz : ((56))*row2_83 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_29, z1_12, z1_30, z1_35, z1_5, z1_22, z1_25, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((56):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_83_zero
def row2_86 (u B a y x : ℂ) : ℂ := (((((-17837568)*y+(496903680))*B+(((-713502720)*y+((133781760)*x))*a+(((160538112)*x+(-1995259392))*y+((749177856)*x+(496903680)))))*u+(((-1302159456)*y+((-6444530064)*x+(1780571520)))*B+((((-290194176)*y+(1728543984))*y+((10460574432)*x+(-688020480)))*a+(((((3344544)*x+(-3344544))*y+(-472566624))*y+((((-493320240)*x+(3134164176))*x+(8153534352))*x+(-6357292128)))*y+((((361210752)*x+(-8517945696))*x+(-1968119712))*x+(-171368064))))))*u+((((-621129600)*a+((((19589472)*x+(-28019088))*x+(-1400266080))*y+((((49809816)*x+(-588332592))*x+(770854752))*x+(-786764160))))*a+(((((-60639768)*x+(578910600))*x+(-1130187360))*x+(-327022080))*y+(((((-193625208)*x+(3190507818))*x+(-5765912904))*x+(-837462720))*x+(-2277475200))))*B+(((((114670080)*a+(788338176))*a+(((151308384)*y+(3941310096))*y+(((-8941178412)*x+(7447240716))*x+(-7253235408))))*a+((((-3344544)*y+((-111148576)*x+(898398432)))*y+(((1548750228)*x+(-1531958000))*x+(-4437116400)))*y+((((-1178602326)*x+(-40758366678))*x+(46296970104))*x+(11220820176))))*a+((((((5852952)*x+(-188255736))*x+(-262814672))*x+(4070644944))*y+(((((-112669326)*x+(1248524346))*x+(-17225412))*x+(-6595371952))*x+(11072865984)))*y+(((((-560006541)*x+(6165943965))*x+(-25932115680))*x+(-6986872320))*x+(-10729350096))))))
theorem row2_86_identity (u B a y x : ℂ) :
  (((46823616)*u+((-10869768)*B+((796915518)*a+((94256568)*x+(-3561140898))))))*row1_31 u B a y x+
  (((-842825088)*u+((32609304)*B+((-5016602976)*a+((88092900)*y+((-476040096)*x+(14946946854)))))))*row1_32 u B a y x+
  (((26970402816)*u+((29989886976)*B+((94001104512)*a+((68645935008)*y+((-14047084800)*x+(-147624517824)))))))*row1_33 u B a y x+
  (((-13913303040)*u+((-2318883840)*a+((-582693888)*y+((-34853610624)*x+(56812654080))))))*row1_34 u B a y x+
  (((96620160)*u+((48310080)*B+((217395360)*a+((-436255344)*y+((-2911053740)*x+(-276482304)))))))*row1_35 u B a y x+
  (((395399424)*u+((-413051184)*B+((-1053531360)*a+((-4201120)*y+((-506567292)*x))))))*row1_29 u B a y x+
  (((499451904)*B+((-749177856)*y)))*row1_10 u B a y x+
  (((12077520)*B+((-9476208)*y+((-9104592)*x))))*row1_20 u B a y x+
  (((1254204)*a+((12899109)*x)))*row1_5 u B a y x+
  (((-185808)*a))*row1_8 u B a y x+
  (((-1580297040)*a+((-722350104)*y)))*row1_12 u B a y x+
  (((-4637767680)*a+((1498355712)*x)))*row1_18 u B a y x+
  (((3882060)*a+((5434884)*x)))*row1_23 u B a y x+
  (((-13706658)*a+((-18636589)*x)))*row1_26 u B a y x+
  (((-650328)*y+((14632380)*x)))*row1_0 u B a y x+
  (((10869768)*y))*row1_11 u B a y x+
  (((-957244596)*y+((-2200293186)*x)))*row1_30 u B a y x+
  (((557424)*x))*row1_3 u B a y x+
  (((-10869768)*x))*row1_4 u B a y x+
  (((-444824352)*x))*row1_22 u B a y x+
  (((1043497728)*x))*row1_24 u B a y x+
  (((-557424)*x))*row1_25 u B a y x+
  (((3142235040)*x))*row1_27 u B a y x+
  (((-120409623936)*x))*row1_28 u B a y x=((28))*row2_86 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_29, row1_10, row1_20, row1_5, row1_8, row1_12, row1_18, row1_23, row1_26, row1_0, row1_11, row1_30, row1_3, row1_4, row1_22, row1_24, row1_25, row1_27, row1_28, row2_86] <;> ring
theorem row2_86_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_86 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_10 := row1_10_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_8 := row1_8_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_0 := row1_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_3 := row1_3_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_24 := row1_24_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_25 := row1_25_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_86_identity u B a y x).symm
  have hz : ((28))*row2_86 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_29, z1_10, z1_20, z1_5, z1_8, z1_12, z1_18, z1_23, z1_26, z1_0, z1_11, z1_30, z1_3, z1_4, z1_22, z1_24, z1_25, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((28):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_86_zero

def row2_87 (u B a y x : ℂ) : ℂ := (((((15168)*x^2)*B+(((30336)*y+((-45504)*x))*a+(((30336)*x+(30336))*y)))*u+(((4608)*y+((-86832)*x))*B+(((-320576)*y+((468096)*x))*a+((((34776)*x+(-513336))*x+(-523312))*y+((((-25596)*x+(-38136))*x+(321072))*x)))))*u+((((4608)*y+((-4608)*x))*a+((((144)*x+(-576))*x)*y+((((-3924)*x+(-93744))*x+(83808))*x)))*B+((((74592)*a+((250096)*y+(((28404)*x+(1172412))*x+(-236016))))*a+(((256)*y+(((8928)*x+(-41928))*x+(588368)))*y+((((14202)*x+(620142))*x+(4501752))*x+(236016))))*a+(((-4096)*y+((((9900)*x+(-60684))*x+(71232))*x+(2302032)))*y+(((((7101)*x+(204759))*x+(913944))*x+(4009296))*x+(-161424))))))
theorem row2_87_identity (u B a y x : ℂ) :
  (((-2016)*a+((-1134)*x+(85687))))*row1_31 u B a y x+
  (((13272)*u+((14868)*a+((9954)*x+(-584745)))))*row1_32 u B a y x+
  (((-64512)*B+((-4156320)*a+((-1370992)*y+((238896)*x+(8002176))))))*row1_33 u B a y x+
  (((-8848)*u+((19908)*a+((672)*y+((-7938)*x)))))*row1_29 u B a y x+
  (((2016)*y))*row1_12 u B a y x+
  (((2016)*y+((81655)*x)))*row1_30 u B a y x+
  (((-112)*y+((35028)*x)))*row1_35 u B a y x+
  (((-36)*x))*row1_5 u B a y x+
  (((9954)*x))*row1_22 u B a y x+
  (((-6)*x))*row1_26 u B a y x+
  (((-10836)*x))*row1_27 u B a y x+
  (((4634112)*x))*row1_28 u B a y x+
  (((-1108800)*x))*row1_34 u B a y x=((14))*row2_87 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_29, row1_12, row1_30, row1_35, row1_5, row1_22, row1_26, row1_27, row1_28, row1_34, row2_87] <;> ring
theorem row2_87_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_87 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_87_identity u B a y x).symm
  have hz : ((14))*row2_87 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_29, z1_12, z1_30, z1_35, z1_5, z1_22, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((14):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_87_zero
def row2_88 (u B a y x : ℂ) : ℂ := ((((182016)*B+((-182016)*y+(182016)))*u+((((17696)*x^2)*B+((-57120)*y+((138704)*x+(652224))))*B+((((35392)*y+(-77840))*y+((749504)*x+(-121344)))*a+(((70784)*y+(((-26400)*x+(-671920))*x+(-735792)))*y+(((-3840)*x+(38064))*x+(-75840))))))*u+((((-227520)*a+((-117792)*y+((-279104)*x+(-288192))))*a+((((65128)*x+(-199840))*x+(-131456))*y+((((103250)*x+(-743208))*x+(420576))*x+(-834240))))*B+((((264320)*a+(((-17696)*y+(390256))*y+(((102060)*x+(218824))*x+(-215504))))*a+(((78144)*y+(((-43204)*x+(-747072))*x+(-76688)))*y+((((51030)*x+(116216))*x+(5464416))*x+(852560))))*a+(((((-22120)*x+(22752))*x+(122400))*y+((((-26082)*x+(83632))*x+(-218432))*x+(577712)))*y+(((((25515)*x+(411588))*x+(1049136))*x+(499536))*x+(-284880))))))
theorem row2_88_identity (u B a y x : ℂ) :
  (((-212352)*B+((-641172)*a+((-1573803)*x+(3776472)))))*row1_31 u B a y x+
  (((1008672)*B+((-3052896)*a+(-23579640))))*row1_32 u B a y x+
  (((-19455744)*B+((-126927360)*a+((-54052992)*y+(342236160)))))*row1_33 u B a y x+
  (((-61157376)*u+((-10192896)*a+((-6795264)*y+((-234404352)*x+(249725952))))))*row1_34 u B a y x+
  (((424704)*u+((212352)*B+((955584)*a+((-767424)*y+((-547568)*x+(-849408)))))))*row1_35 u B a y x+
  (((53088)*B+((-53088)*y)))*row1_20 u B a y x+
  (((-1734208)*B+((1410416)*y+((-971376)*x))))*row1_29 u B a y x+
  (((-20385792)*a))*row1_18 u B a y x+
  (((17064)*a+((22436)*x)))*row1_23 u B a y x+
  (((-76788)*a+((-98071)*x)))*row1_26 u B a y x+
  (((212352)*y))*row1_11 u B a y x+
  (((-971376)*y))*row1_12 u B a y x+
  (((-759024)*y+((5321064)*x)))*row1_30 u B a y x+
  (((-212352)*x))*row1_4 u B a y x+
  (((17346)*x))*row1_5 u B a y x+
  (((4268880)*x))*row1_27 u B a y x+
  (((126927360)*x))*row1_28 u B a y x=((336))*row2_88 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_20, row1_29, row1_18, row1_23, row1_26, row1_11, row1_12, row1_30, row1_4, row1_5, row1_27, row1_28, row2_88] <;> ring
theorem row2_88_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_88 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_88_identity u B a y x).symm
  have hz : ((336))*row2_88 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_20, z1_29, z1_18, z1_23, z1_26, z1_11, z1_12, z1_30, z1_4, z1_5, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((336):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_88_zero
def row2_89 (u B a y x : ℂ) : ℂ := ((((((1)*x+(-1))*x)*a+(((1)*x+(-1))*y+((1)*x)))*u+(((-1)*y+((1)*x))*a+((((1)*x+(-1))*x+(-1))*x)))*u)
theorem row2_89_identity (u B a y x : ℂ) :
  (((1)*u))*row1_33 u B a y x=((1))*row2_89 u B a y x := by
  simp only [row1_33, row2_89] <;> ring
theorem row2_89_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_89 u B a y x=0 := by
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_89_identity u B a y x).symm
  have hz : ((1))*row2_89 u B a y x=0 := by
    simpa only [z1_33,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_89_zero
def row2_92 (u B a y x : ℂ) : ℂ := (((((1274112)*y+((-637056)*x))*a+((2548224)*y+((-1274112)*x)))*u+(((1990272)*y+((13239408)*x))*B+((((409536)*y+(-722352))*y+((-24267768)*x))*a+(((819072)*y+((((836136)*x+(-5560272))*x+(-13289040))*x+(12080616)))*y+((((-716688)*x+(13200984))*x+(31032))*x)))))*u+(((((-68256)*x+(1990272))*y+(((68256)*x+(-1990272))*x))*a+(((((79632)*x+(-755928))*x+(1749600))*x)*y+(((((358344)*x+(-5333502))*x+(7461192))*x+(3171648))*x)))*B+(((((358344)*x^2+(-808896))*a+(((-204768)*y+(-8742528))*y+(((16432488)*x+(-15001260))*x+(14857200))))*a+((((141568)*x+(-1187136))*y+(((-2384532)*x+(4057208))*x+(1602024)))*y+((((2084580)*x+(70755054))*x+(-100728096))*x+(-14857200))))*a+(((((153576)*x+(351392))*x+(-6070944))*y+(((((179172)*x+(-2143170))*x+(1961364))*x+(15332848))*x+(-31309392)))*y+((((((-44793)*x+(1500174))*x+(-11691009))*x+(41162448))*x+(-24994152))*x+(14048304))))))
theorem row2_92_identity (u B a y x : ℂ) :
  (((-5506032)*a+((-3395763)*x+(24291288))))*row1_31 u B a y x+
  (((4459392)*u+((30205056)*a+((-477792)*y+((3344544)*x+(-96578664))))))*row1_32 u B a y x+
  (((-142700544)*u+((-222910464)*B+((-545814528)*a+((-434528640)*y+((80269056)*x+(918820224)))))))*row1_33 u B a y x+
  (((-2972928)*u+((6689088)*a+((2012304)*y+((2533104)*x)))))*row1_29 u B a y x+
  (((10033632)*a+((3594864)*y)))*row1_12 u B a y x+
  (((5506032)*y+((16145976)*x)))*row1_30 u B a y x+
  (((2721600)*y+((21444752)*x)))*row1_35 u B a y x+
  (((-92904)*x))*row1_0 u B a y x+
  (((-64194)*x))*row1_5 u B a y x+
  (((3344544)*x))*row1_22 u B a y x+
  (((-30607)*x))*row1_26 u B a y x+
  (((-16273152)*x))*row1_27 u B a y x+
  (((706352640)*x))*row1_28 u B a y x+
  (((-132314112)*x))*row1_34 u B a y x=((112))*row2_92 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_29, row1_12, row1_30, row1_35, row1_0, row1_5, row1_22, row1_26, row1_27, row1_28, row1_34, row2_92] <;> ring
theorem row2_92_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_92 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_0 := row1_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_92_identity u B a y x).symm
  have hz : ((112))*row2_92 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_29, z1_12, z1_30, z1_35, z1_0, z1_5, z1_22, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((112):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_92_zero
def row2_93 (u B a y x : ℂ) : ℂ := (((((2528)*x^2+(-8160))*y+((27760)*x))*B+((((5056)*y+(-38928))*y+((143728)*x))*a+(((10112)*y+(((-11536)*x+(-124880))*x+(-74416)))*y+(((7216)*x+(23856))*x))))*u+((((-8160)*y+((8160)*x))*a+((((4248)*x+(-16992))*x)*y+((((14750)*x+(-85768))*x+(21440))*x)))*B+((((37760)*a+(((-2528)*y+(67488))*y+(((14580)*x+(98388))*x+(-47760))))*a+(((2496)*y+(((-6172)*x+(-97696))*x+(68496)))*y+((((7290)*x+(40054))*x+(968696))*x+(47760))))*a+(((((1896)*x+(-2528))*x+(-7072))*y+((((-3726)*x+(-8412))*x+(52400))*x+(256240)))*y+(((((3645)*x+(67635))*x+(187616))*x+(155328))*x+(-10000))))))
theorem row2_93_identity (u B a y x : ℂ) :
  (((19824)*a+((11151)*x+(105240))))*row1_31 u B a y x+
  (((-62304)*a+((7584)*y+(-646440))))*row1_32 u B a y x+
  (((391680)*B+((-3353088)*a+((-1926528)*y+(9827328)))))*row1_33 u B a y x+
  (((-19824)*y))*row1_12 u B a y x+
  (((-6608)*y+((-19824)*x)))*row1_29 u B a y x+
  (((-19824)*y+((160056)*x)))*row1_30 u B a y x+
  (((-11328)*y+((-36816)*x)))*row1_35 u B a y x+
  (((354)*x))*row1_5 u B a y x+
  (((59)*x))*row1_26 u B a y x+
  (((37824)*x))*row1_27 u B a y x+
  (((3353088)*x))*row1_28 u B a y x+
  (((-1420800)*x))*row1_34 u B a y x=((48))*row2_93 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_12, row1_29, row1_30, row1_35, row1_5, row1_26, row1_27, row1_28, row1_34, row2_93] <;> ring
theorem row2_93_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_93 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_93_identity u B a y x).symm
  have hz : ((48))*row2_93 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_12, z1_29, z1_30, z1_35, z1_5, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((48):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_93_zero
def row2_94 (u B a y x : ℂ) : ℂ := ((((-896)*y+((-5552)*x))*B+((((1264)*x^2+(-7888))*y+((27376)*x))*a+((((32)*x+(-9152))*x+(-15200))*y+(((832)*x+(5088))*x))))*u+((((-896)*y+((896)*x))*a+((((288)*x+(-1152))*x)*y+((((1000)*x+(-5472))*x+(768))*x)))*B+((((2560)*a+((8496)*y+(((-2916)*x+(29808))*x+(-10672))))*a+(((512)*y+(((160)*x+(-4224))*x+(13856)))*y+((((-1458)*x+(-648))*x+(147920))*x+(10672))))*a+(((1920)*y+((((1156)*x+(-1920))*x+(896))*x+(62512)))*y+(((((-729)*x+(9936))*x+(14048))*x+(98368))*x+(-8112))))))
theorem row2_94_identity (u B a y x : ℂ) :
  (((336)*a+((189)*x+(1374))))*row1_31 u B a y x+
  (((-1056)*a+(-11286)))*row1_32 u B a y x+
  (((10752)*B+((-56832)*a+((-21984)*y+(172992)))))*row1_33 u B a y x+
  (((-336)*y))*row1_12 u B a y x+
  (((-112)*y+((-336)*x)))*row1_29 u B a y x+
  (((-336)*y+((2994)*x)))*row1_30 u B a y x+
  (((-192)*y+((-624)*x)))*row1_35 u B a y x+
  (((6)*x))*row1_5 u B a y x+
  (((1)*x))*row1_26 u B a y x+
  (((384)*x))*row1_27 u B a y x+
  (((56832)*x))*row1_28 u B a y x+
  (((-19968)*x))*row1_34 u B a y x=((12))*row2_94 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_12, row1_29, row1_30, row1_35, row1_5, row1_26, row1_27, row1_28, row1_34, row2_94] <;> ring
theorem row2_94_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_94 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_94_identity u B a y x).symm
  have hz : ((12))*row2_94 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_12, z1_29, z1_30, z1_35, z1_5, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((12):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_94_zero

def row2_95 (u B a y x : ℂ) : ℂ := ((((-19008)*y+((2091600)*x))*B+((((409536)*y+(-1610736))*y+((5577264)*x))*a+(((819072)*y+(((-1806480)*x+(-6692016))*x+(-286704)))*y+(((602160)*x+(-555120))*x))))*u+(((((-68256)*x+(-19008))*y+(((68256)*x+(19008))*x))*a+(((((79632)*x+(-178344))*x+(-560736))*x)*y+(((((298620)*x+(-1231026))*x+(-2079528))*x+(1208064))*x)))*B+((((1246080)*a+(((-204768)*y+((238896)*x^2+(1354944)))*y+(((958932)*x+(-412476))*x+(-400560))))*a+((((141568)*x+(-160320))*y+(((-1227516)*x+(-6019936))*x+(2381712)))*y+((((-834462)*x+(13932078))*x+(21903000))*x+(400560))))*a+(((((153576)*x+(351392))*x+(-2008032))*y+((((-604542)*x+(765204))*x+(672496))*x+(4140624)))*y+(((((1016145)*x+(1745631))*x+(6638784))*x+(2334912))*x+(845520))))))
theorem row2_95_identity (u B a y x : ℂ) :
  (((1526448)*a+((1396143)*x+(10200456))))*row1_31 u B a y x+
  (((-4797408)*a+((-477792)*y+(-58243416))))*row1_32 u B a y x+
  (((2128896)*B+((-224211456)*a+((-209075328)*y+(779638272)))))*row1_33 u B a y x+
  (((-3437616)*y))*row1_12 u B a y x+
  (((-331856)*y+((-1526448)*x)))*row1_29 u B a y x+
  (((-1526448)*y+((16120104)*x)))*row1_30 u B a y x+
  (((-872256)*y+((-2126992)*x)))*row1_35 u B a y x+
  (((61386)*x))*row1_5 u B a y x+
  (((-9677)*x))*row1_26 u B a y x+
  (((4664352)*x))*row1_27 u B a y x+
  (((224211456)*x))*row1_28 u B a y x+
  (((-137432064)*x))*row1_34 u B a y x=((112))*row2_95 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_12, row1_29, row1_30, row1_35, row1_5, row1_26, row1_27, row1_28, row1_34, row2_95] <;> ring
theorem row2_95_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_95 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_95_identity u B a y x).symm
  have hz : ((112))*row2_95 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_12, z1_29, z1_30, z1_35, z1_5, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((112):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_95_zero
def row2_96 (u B a y x : ℂ) : ℂ := (((((819072)*y+((-409536)*x))*a+((1638144)*y+((-819072)*x)))*u+(((1251936)*y+((7999272)*x))*B+((((204768)*y+(-406632))*y+((-15550308)*x))*a+((((17064)*x^2+(392472))*y+((((503388)*x+(-3383568))*x+(-7793448))*x+(7430580)))*y+((((-460728)*x+(8326020))*x+(168588))*x)))))*u+(((((-34128)*x+(1251936))*y+(((34128)*x+(-1251936))*x))*a+(((((39816)*x+(-450756))*x+(1165968))*x)*y+(((((149310)*x+(-3065493))*x+(4908876))*x+(1892256))*x)))*B+((((-611616)*a+(((-102384)*y+(-5484360))*y+(((9694836)*x+(-8770692))*x+(9222504))))*a+((((53720)*x+(-740040))*y+(((-1335090)*x+(3342700))*x+(1191396)))*y+((((2219562)*x+(41995056))*x+(-63351204))*x+(-9222504))))*a+(((((76788)*x+(175696))*x+(-3551088))*y+(((((119448)*x+(-1233177))*x+(1133688))*x+(9466784))*x+(-18788376)))*y+(((((751437)*x+(-6997752))*x+(27523056))*x+(-13337268))*x+(8610888))))))
theorem row2_96_identity (u B a y x : ℂ) :
  (((-7303632)*a+((-4406913)*x+(28764792))))*row1_31 u B a y x+
  (((5733504)*u+((39540480)*a+((-477792)*y+((4300128)*x+(-112312536))))))*row1_32 u B a y x+
  (((-183472128)*u+((-280433664)*B+((-673505280)*a+((-502282368)*y+((103203072)*x+(1004502912)))))))*row1_33 u B a y x+
  (((-3822336)*u+((8600256)*a+((2611504)*y+((3003504)*x)))))*row1_29 u B a y x+
  (((12900384)*a+((5392464)*y)))*row1_12 u B a y x+
  (((7303632)*y+((16785384)*x)))*row1_30 u B a y x+
  (((3627456)*y+((27786416)*x)))*row1_35 u B a y x+
  (((-119448)*x))*row1_0 u B a y x+
  (((-96294)*x))*row1_5 u B a y x+
  (((4300128)*x))*row1_22 u B a y x+
  (((-35957)*x))*row1_26 u B a y x+
  (((-22013376)*x))*row1_27 u B a y x+
  (((879911424)*x))*row1_28 u B a y x+
  (((-143431680)*x))*row1_34 u B a y x=((224))*row2_96 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_29, row1_12, row1_30, row1_35, row1_0, row1_5, row1_22, row1_26, row1_27, row1_28, row1_34, row2_96] <;> ring
theorem row2_96_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_96 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_0 := row1_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_96_identity u B a y x).symm
  have hz : ((224))*row2_96 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_29, z1_12, z1_30, z1_35, z1_0, z1_5, z1_22, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((224):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_96_zero
def row2_97 (u B a y x : ℂ) : ℂ := ((((-448)*y+(((1264)*x^2+(-9728))*x))*B+(((-7104)*y+((24432)*x))*a+((((1280)*x+(-3312))*x+(-17712))*y+(((416)*x+(7600))*x))))*u+((((-448)*y+((448)*x))*a+((((144)*x+(-576))*x)*y+((((500)*x+(-2736))*x+(384))*x)))*B+((((1280)*a+((8672)*y+(((-5724)*x+(32600))*x+(-12288))))*a+(((256)*y+(((80)*x+(-4640))*x+(11984)))*y+((((-2862)*x+(-7908))*x+(142848))*x+(12288))))*a+(((960)*y+((((1052)*x+(-4120))*x+(-7136))*x+(68544)))*y+(((((-1431)*x+(7970))*x+(3232))*x+(118704))*x+(-11008))))))
theorem row2_97_identity (u B a y x : ℂ) :
  (((336)*a+((189)*x+(-48))))*row1_31 u B a y x+
  (((-1056)*a+((1896)*x+(-7968))))*row1_32 u B a y x+
  (((10752)*B+((-56832)*a+((768)*y+(157824)))))*row1_33 u B a y x+
  (((-336)*y))*row1_12 u B a y x+
  (((-112)*y+((-336)*x)))*row1_29 u B a y x+
  (((-336)*y+((624)*x)))*row1_30 u B a y x+
  (((-192)*y+((-624)*x)))*row1_35 u B a y x+
  (((6)*x))*row1_5 u B a y x+
  (((1)*x))*row1_26 u B a y x+
  (((384)*x))*row1_27 u B a y x+
  (((56832)*x))*row1_28 u B a y x+
  (((-19968)*x))*row1_34 u B a y x=((24))*row2_97 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_12, row1_29, row1_30, row1_35, row1_5, row1_26, row1_27, row1_28, row1_34, row2_97] <;> ring
theorem row2_97_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_97 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_97_identity u B a y x).symm
  have hz : ((24))*row2_97 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_12, z1_29, z1_30, z1_35, z1_5, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((24):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_97_zero
def row2_99 (u B a y x : ℂ) : ℂ := (((((-1274112)*y+((637056)*x))*a+((-2548224)*y+((1274112)*x)))*u+(((-1990272)*y+((-13557936)*x))*B+((((-409536)*y+(403824))*y+((25064088)*x))*a+(((-819072)*y+((((-836136)*x+(5560272))*x+(13289040))*x+(-12717672)))*y+((((716688)*x+(-13200984))*x+(287496))*x)))))*u+(((((68256)*x+(-1990272))*y+(((-68256)*x+(1990272))*x))*a+(((((-79632)*x+(755928))*x+(-1749600))*x)*y+(((((-298620)*x+(5094606))*x+(-7461192))*x+(-3171648))*x)))*B+((((808896)*a+(((204768)*y+(8901792))*y+((((179172)*x+(-15795432))*x+(16235556))*x+(-15175728))))*a+((((-141568)*x+(1187136))*y+(((2490708)*x+(-4057208))*x+(-1283496)))*y+(((((89586)*x+(-2801268))*x+(-69102690))*x+(104948592))*x+(15175728))))*a+(((((-153576)*x+(-351392))*x+(6070944))*y+(((((-179172)*x+(2143170))*x+(-1868460))*x+(-15332848))*x+(33539088)))*y+((((((44793)*x+(-1500174))*x+(11959767))*x+(-43710672))*x+(29135016))*x+(-14366832))))))
theorem row2_99_identity (u B a y x : ℂ) :
  (((5506032)*a+((3395763)*x+(-24291288))))*row1_31 u B a y x+
  (((-4459392)*u+((-30205056)*a+((477792)*y+((-3344544)*x+(95463816))))))*row1_32 u B a y x+
  (((142700544)*u+((222910464)*B+((545814528)*a+((434528640)*y+((-80269056)*x+(-883145088)))))))*row1_33 u B a y x+
  (((2972928)*u+((-6689088)*a+((-2012304)*y+((-2161488)*x)))))*row1_29 u B a y x+
  (((-10033632)*a+((-3594864)*y)))*row1_12 u B a y x+
  (((-5506032)*y+((-16145976)*x)))*row1_30 u B a y x+
  (((-2721600)*y+((-21444752)*x)))*row1_35 u B a y x+
  (((92904)*x))*row1_0 u B a y x+
  (((64194)*x))*row1_5 u B a y x+
  (((-3344544)*x))*row1_22 u B a y x+
  (((30607)*x))*row1_26 u B a y x+
  (((16273152)*x))*row1_27 u B a y x+
  (((-706352640)*x))*row1_28 u B a y x+
  (((132314112)*x))*row1_34 u B a y x=((112))*row2_99 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_29, row1_12, row1_30, row1_35, row1_0, row1_5, row1_22, row1_26, row1_27, row1_28, row1_34, row2_99] <;> ring
theorem row2_99_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_99 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_0 := row1_0_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_99_identity u B a y x).symm
  have hz : ((112))*row2_99 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_29, z1_12, z1_30, z1_35, z1_0, z1_5, z1_22, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((112):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_99_zero
def row2_100 (u B a y x : ℂ) : ℂ := ((((-70848)*y+((1010352)*x))*B+((((136512)*y+(-260496))*y+((1145424)*x))*a+(((273024)*y+(((-797040)*x+(-2308176))*x+(524016)))*y+(((265680)*x+(-592272))*x))))*u+(((((136512)*x+(-70848))*y+(((-136512)*x+(70848))*x))*a+((((44712)*x+(-178848))*x)*y+(((((-59724)*x+(-231534))*x+(-531000))*x+(255744))*x)))*B+((((397440)*a+(((-68256)*y+(64800))*y+(((837756)*x+(-646980))*x+(215472))))*a+(((-57024)*y+((((119448)*x+(-410292))*x+(-2177632))*x+(803088)))*y+((((-178362)*x+(6170418))*x+(3478440))*x+(-215472))))*a+(((((51192)*x+(-136512))*x+(-452736))*y+((((-185274)*x+(171180))*x+(2931280))*x+(-835824)))*y+(((((448335)*x+(333153))*x+(2804736))*x+(-3821088))*x+(612912))))))
theorem row2_100_identity (u B a y x : ℂ) :
  (((486864)*a+((1080135)*x+(3527160))))*row1_31 u B a y x+
  (((-1530144)*a+((955584)*y+(-19017768))))*row1_32 u B a y x+
  (((7934976)*B+((-78951936)*a+((-71723904)*y+(235694592)))))*row1_33 u B a y x+
  (((-9072)*y))*row1_12 u B a y x+
  (((-640080)*y+((-486864)*x)))*row1_29 u B a y x+
  (((-486864)*y+((5456472)*x)))*row1_30 u B a y x+
  (((-278208)*y+((-833392)*x)))*row1_35 u B a y x+
  (((162)*x))*row1_5 u B a y x+
  (((39843)*x))*row1_26 u B a y x+
  (((1034208)*x))*row1_27 u B a y x+
  (((78951936)*x))*row1_28 u B a y x+
  (((-36578304)*x))*row1_34 u B a y x=((112))*row2_100 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_12, row1_29, row1_30, row1_35, row1_5, row1_26, row1_27, row1_28, row1_34, row2_100] <;> ring
theorem row2_100_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_100 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_100_identity u B a y x).symm
  have hz : ((112))*row2_100 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_12, z1_29, z1_30, z1_35, z1_5, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((112):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_100_zero
def row2_101 (u B a y x : ℂ) : ℂ := (((((1)*a+(-1))*B+(((-1)*y+(1))*a+((1)*y+(-1))))*u+(((1)*x+(-1))*B+((-2)*a+(((-1)*x+(-1))*y+((1)*x+(3))))))*u)
theorem row2_101_identity (u B a y x : ℂ) :
  (((1)*u))*row1_34 u B a y x=((1))*row2_101 u B a y x := by
  simp only [row1_34, row2_101] <;> ring
theorem row2_101_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_101 u B a y x=0 := by
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_101_identity u B a y x).symm
  have hz : ((1))*row2_101 u B a y x=0 := by
    simpa only [z1_34,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_101_zero

def row2_102 (u B a y x : ℂ) : ℂ := ((((1)*a+(-1))*B^2+((((-1)*y+(2))*y+(-1))*a+(((1)*y+(-2))*y+(1))))*u+((((1)*x+(-1))*B+((-2)*a+((-2)*y+(4))))*B+(((-2)*y+(2))*a+((((-1)*x+(-1))*y+((2)*x+(4)))*y+((-1)*x+(-3))))))
theorem row2_102_identity (u B a y x : ℂ) :
  (((1)*B+((1)*y+(-1))))*row1_34 u B a y x=((1))*row2_102 u B a y x := by
  simp only [row1_34, row2_102] <;> ring
theorem row2_102_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_102 u B a y x=0 := by
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_102_identity u B a y x).symm
  have hz : ((1))*row2_102 u B a y x=0 := by
    simpa only [z1_34,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_102_zero
def row2_103 (u B a y x : ℂ) : ℂ := (((((384)*a+(768))*a)*u+(((1728)*x)*B+(((32)*y+((24)*x+(-3072)))*a+(((504)*x+(-440))*y+((984)*x+(7680))))))*u+(((((-324)*x+(1296))*x)*a+((((162)*x+(-576))*x+(-288))*x))*B+(((((-1944)*a+(-3024))*a+((-720)*y+((5724)*x+(-4128))))*a+(((288)*x+(-1816))*y+((((243)*x+(-1890))*x+(240))*x+(17472))))*a+((((108)*x+(432))*x+(-2624))*y+((((-27)*x+(-2232))*x+(-14856))*x+(-2688))))))
theorem row2_103_identity (u B a y x : ℂ) :
  ((27))*row1_31 u B a y x+
  ((-126))*row1_32 u B a y x+
  (((-864)*a+((-432)*y+(2808))))*row1_33 u B a y x+
  (((8)*u+((18)*a+((-9)*x+(-4)))))*row1_35 u B a y x+
  (((864)*x))*row1_28 u B a y x+
  (((27)*x))*row1_30 u B a y x=((1))*row2_103 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_35, row1_28, row1_30, row2_103] <;> ring
theorem row2_103_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_103 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_103_identity u B a y x).symm
  have hz : ((1))*row2_103 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_35, z1_28, z1_30,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_103_zero
def row2_106 (u B a y x : ℂ) : ℂ := ((((-364032)*B+((364032)*y+(-364032)))*u+(((208992)*y+((-273936)*x+(-1622976)))*B+(((-603120)*y+((609840)*x+(242688)))*a+(((-106176)*y+(((-9360)*x+(18768))*x+(737424)))*y+(((63792)*x+(180240))*x+(-166848))))))*u+(((((39816)*x+(-159264))*x)*B+((((238896)*a+(879744))*a+((241856)*y+((-394800)*x+(1213440))))*a+((((-61488)*x+(142304))*x+(245216))*y+((((-136080)*x+(542592))*x+(-1058880))*x+(-773568)))))*B+((((81648)*a+((53664)*y+(((-183708)*x+(1289196))*x+(63312))))*a+(((-106784)*y+(((109620)*x+(515040))*x+(932336)))*y+((((-91854)*x+(-195822))*x+(1630680))*x+(-700368))))*a+(((((39816)*x+(-10112))*x+(-258240))*y+((((23058)*x+(-328572))*x+(457136))*x+(3096432)))*y+(((((-45927)*x+(77787))*x+(-2304))*x+(2913312))*x+(-806832))))))
theorem row2_106_identity (u B a y x : ℂ) :
  (((79632)*B+((715176)*a+((1141371)*x+(489384)))))*row1_31 u B a y x+
  (((-238896)*B+((1608768)*a+(-3052728))))*row1_32 u B a y x+
  (((6322176)*B+((-38513664)*a+((-18023040)*y+(64770048)))))*row1_33 u B a y x+
  (((40771584)*u+((18686976)*a+((-1415680)*y+((125862912)*x+(-130808832))))))*row1_34 u B a y x+
  (((-283136)*u+((-389312)*B+((-637056)*a+((276416)*y+((-605808)*x+(318528)))))))*row1_35 u B a y x+
  (((-35392)*B+((35392)*y)))*row1_20 u B a y x+
  (((1114848)*B+((-994896)*y+((359856)*x))))*row1_29 u B a y x+
  (((13590528)*a))*row1_18 u B a y x+
  (((-11376)*a+((-14220)*x)))*row1_23 u B a y x+
  (((51192)*a+((62919)*x)))*row1_26 u B a y x+
  (((-79632)*y))*row1_11 u B a y x+
  (((359856)*y))*row1_12 u B a y x+
  (((280224)*y+((406728)*x)))*row1_30 u B a y x+
  (((79632)*x))*row1_4 u B a y x+
  (((-6426)*x))*row1_5 u B a y x+
  (((-2003904)*x))*row1_27 u B a y x+
  (((38513664)*x))*row1_28 u B a y x=((112))*row2_106 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_20, row1_29, row1_18, row1_23, row1_26, row1_11, row1_12, row1_30, row1_4, row1_5, row1_27, row1_28, row2_106] <;> ring
theorem row2_106_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_106 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_106_identity u B a y x).symm
  have hz : ((112))*row2_106 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_20, z1_29, z1_18, z1_23, z1_26, z1_11, z1_12, z1_30, z1_4, z1_5, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((112):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_106_zero
def row2_107 (u B a y x : ℂ) : ℂ := (((((1)*y)*a+((-1)*y))*B+((((-1)*y+(1))*y)*a+(((1)*y+(-1))*y)))*u+((((1)*x+(-1))*y)*B+(((-2)*y)*a+((((-1)*x+(-1))*y+((1)*x+(3)))*y))))
theorem row2_107_identity (u B a y x : ℂ) :
  (((1)*y))*row1_34 u B a y x=((1))*row2_107 u B a y x := by
  simp only [row1_34, row2_107] <;> ring
theorem row2_107_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_107 u B a y x=0 := by
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_107_identity u B a y x).symm
  have hz : ((1))*row2_107 u B a y x=0 := by
    simpa only [z1_34,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_107_zero
def row2_108 (u B a y x : ℂ) : ℂ := ((((2160)*y+((3024)*x))*B+((((3792)*y)*a+((2832)*y+((432)*x)))*a+((((-1296)*x+(-4752))*x+(1296))*y+(((432)*x+(-1296))*x))))*u+((((2160)*y+((-2160)*x))*a+((((-288)*x+(1152))*x)*y+((((-2106)*x+(-216))*x+(3024))*x)))*B+((((-1296)*a+((-912)*y+(((2916)*x+(-4212))*x+(5616))))*a+(((-512)*y+(((2052)*x+(4224))*x+(-7536)))*y+((((1458)*x+(4914))*x+(15768))*x+(-5616))))*a+(((-3184)*y+((((108)*x+(972))*x+(5424))*x+(18384)))*y+(((((729)*x+(729))*x+(11232))*x+(-25056))*x+(4320))))))
theorem row2_108_identity (u B a y x : ℂ) :
  (((-15120)*a+((-8505)*x+(36288))))*row1_31 u B a y x+
  (((81648)*a+(-187488)))*row1_32 u B a y x+
  (((-483840)*B+((-2903040)*a+((-580608)*y+(2999808)))))*row1_33 u B a y x+
  (((15120)*y))*row1_12 u B a y x+
  (((5040)*y+((15120)*x)))*row1_29 u B a y x+
  (((15120)*y+((6048)*x)))*row1_30 u B a y x+
  (((3584)*y+((-6048)*x)))*row1_35 u B a y x+
  (((-270)*x))*row1_5 u B a y x+
  (((-45)*x))*row1_26 u B a y x+
  (((-51408)*x))*row1_27 u B a y x+
  (((2903040)*x))*row1_28 u B a y x+
  (((-193536)*x))*row1_34 u B a y x=((224))*row2_108 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_12, row1_29, row1_30, row1_35, row1_5, row1_26, row1_27, row1_28, row1_34, row2_108] <;> ring
theorem row2_108_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_108 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_108_identity u B a y x).symm
  have hz : ((224))*row2_108 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_12, z1_29, z1_30, z1_35, z1_5, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((224):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_108_zero
def row2_109 (u B a y x : ℂ) : ℂ := ((((-2304)*B+((2304)*y+(-2304)))*u+(((-192)*x+(-8256))*B+(((-3360)*y+((6384)*x+(1536)))*a+((((-912)*x+(-3456))*x+(1824))*y+(((912)*x+(1632))*x+(960))))))*u+(((((224)*y+(2880))*a+((544)*y+((4704)*x+(3648))))*a+((((-224)*x+(352))*x+(1888))*y+(((1584)*x+(-3648))*x+(10560))))*B+(((((-224)*y+(1712))*y+((9420)*x+(-2400)))*a+(((-544)*y+((352)*x+(9056)))*y+(((4038)*x+(27192))*x+(-5664))))*a+(((((224)*x+(-288))*x+(-1952))*y+(((-1244)*x+(7856))*x+(20992)))*y+((((1539)*x+(5808))*x+(20208))*x+(1824))))))
theorem row2_109_identity (u B a y x : ℂ) :
  (((28)*B+((1701)*a+((2457)*x+(1456)))))*row1_31 u B a y x+
  (((-84)*B+(-9324)))*row1_32 u B a y x+
  (((28224)*B+((-45696)*a+((-48832)*y+(153216)))))*row1_33 u B a y x+
  (((64512)*u+((10752)*a+((896)*y+((198912)*x+(-263424))))))*row1_34 u B a y x+
  (((-448)*u+((-224)*B+((-1008)*a+((224)*y+((-1456)*x+(896)))))))*row1_35 u B a y x+
  (((-56)*B+((56)*y)))*row1_20 u B a y x+
  (((1960)*B+((-1960)*y)))*row1_29 u B a y x+
  (((21504)*a))*row1_18 u B a y x+
  (((-18)*a+((-26)*x)))*row1_23 u B a y x+
  (((81)*a+((117)*x)))*row1_26 u B a y x+
  (((-28)*y))*row1_11 u B a y x+
  (((-28)*y+((3052)*x)))*row1_30 u B a y x+
  (((28)*x))*row1_4 u B a y x+
  (((-1764)*x))*row1_27 u B a y x+
  (((45696)*x))*row1_28 u B a y x=((28))*row2_109 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_20, row1_29, row1_18, row1_23, row1_26, row1_11, row1_30, row1_4, row1_27, row1_28, row2_109] <;> ring
theorem row2_109_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_109 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_109_identity u B a y x).symm
  have hz : ((28))*row2_109 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_20, z1_29, z1_18, z1_23, z1_26, z1_11, z1_30, z1_4, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((28):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_109_zero

def row2_110 (u B a y x : ℂ) : ℂ := ((((1632)*y+((-3024)*x))*B+(((-2832)*y+((-432)*x))*a+((((1296)*x+(4752))*x+(-1296))*y+(((-432)*x+(1296))*x))))*u+((((1632)*y+((-1632)*x))*a+((((288)*x+(-1152))*x)*y+((((-1686)*x+(4008))*x+(768))*x)))*B+(((((3792)*y+(-2496))*a+((4704)*y+(((-2916)*x+(4212))*x+(1968))))*a+(((512)*y+(((1740)*x+(-8016))*x+(7536)))*y+((((-1458)*x+(-8706))*x+(-4392))*x+(-1968))))*a+(((-608)*y+((((-108)*x+(-972))*x+(-13008))*x+(-18384)))*y+(((((-729)*x+(-729))*x+(-11232))*x+(17472))*x+(-528))))))
theorem row2_110_identity (u B a y x : ℂ) :
  (((-5712)*a+((-3213)*x+(-4872))))*row1_31 u B a y x+
  (((25536)*a+(27384)))*row1_32 u B a y x+
  (((-182784)*B+((-247296)*a+((77952)*y+(-225792)))))*row1_33 u B a y x+
  (((5712)*y))*row1_12 u B a y x+
  (((1904)*y+((5712)*x)))*row1_29 u B a y x+
  (((5712)*y+((-16296)*x)))*row1_30 u B a y x+
  (((-1792)*y+((3024)*x)))*row1_35 u B a y x+
  (((-102)*x))*row1_5 u B a y x+
  (((-17)*x))*row1_26 u B a y x+
  (((-14112)*x))*row1_27 u B a y x+
  (((247296)*x))*row1_28 u B a y x+
  (((96768)*x))*row1_34 u B a y x=((112))*row2_110 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_12, row1_29, row1_30, row1_35, row1_5, row1_26, row1_27, row1_28, row1_34, row2_110] <;> ring
theorem row2_110_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_110 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_110_identity u B a y x).symm
  have hz : ((112))*row2_110 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_12, z1_29, z1_30, z1_35, z1_5, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((112):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_110_zero
def row2_111 (u B a y x : ℂ) : ℂ := (((((30336)*x)*B+(((-60672)*x)*a))*u+(((4032)*y+((201312)*x))*B+(((271232)*y+((-904344)*x+(-91008)))*a+((((-28584)*x+(530352))*x+(264952))*y+(((-81480)*x+(-684600))*x+(30336))))))*u+((((4032)*y+((-4032)*x))*a+((((-1296)*x+(5184))*x)*y+((((-4500)*x+(104256))*x+(-117216))*x)))*B+((((-11520)*a+((-253744)*y+(((-16740)*x+(-1155132))*x+(482208))))*a+(((-2304)*y+(((-720)*x+(58824))*x+(-649480)))*y+((((-8370)*x+(-481038))*x+(-4554336))*x+(-148512))))*a+(((-8640)*y+((((-9468)*x+(64572))*x+(-49536))*x+(-2290432)))*y+(((((-4185)*x+(-150651))*x+(-920208))*x+(-4426152))*x+(-325632))))))
theorem row2_111_identity (u B a y x : ℂ) :
  (((-1008)*a+((-567)*x+(-18184))))*row1_31 u B a y x+
  (((3168)*a+((-5688)*x+(179376))))*row1_32 u B a y x+
  (((-32256)*B+((1141248)*a+((290944)*y+((-136512)*x+(-1277376))))))*row1_33 u B a y x+
  (((576)*y+((-20880)*x+(-5056))))*row1_35 u B a y x+
  (((5056)*u+((-11376)*a+((336)*y+((6696)*x)))))*row1_29 u B a y x+
  (((1008)*y))*row1_12 u B a y x+
  (((1008)*y+((-20200)*x)))*row1_30 u B a y x+
  (((-18)*x))*row1_5 u B a y x+
  (((-5688)*x))*row1_22 u B a y x+
  (((-3)*x))*row1_26 u B a y x+
  (((-1152)*x))*row1_27 u B a y x+
  (((-1414272)*x))*row1_28 u B a y x+
  (((605952)*x))*row1_34 u B a y x=((8))*row2_111 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_35, row1_29, row1_12, row1_30, row1_5, row1_22, row1_26, row1_27, row1_28, row1_34, row2_111] <;> ring
theorem row2_111_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_111 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_22 := row1_22_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_111_identity u B a y x).symm
  have hz : ((8))*row2_111 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_35, z1_29, z1_12, z1_30, z1_5, z1_22, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((8):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_111_zero
def row2_112 (u B a y x : ℂ) : ℂ := (((((1264)*x)*B+((-368)*y+((9344)*x)))*B+(((6624)*y+((-26112)*x))*a+((((-1296)*x+(10416))*x+(13936))*y+(((432)*x+(-3824))*x))))*u+((((1264)*a+((-368)*y+((1632)*x+(-1264))))*a+((((-288)*x+(1152))*x+(-1264))*y+((((-1000)*x+(5472))*x+(-4560))*x+(1264))))*B+((((-2560)*a+((-11024)*y+(((2916)*x+(-27280))*x+(13200))))*a+(((-512)*y+(((-160)*x+(5488))*x+(-13856)))*y+((((1458)*x+(3176))*x+(-150448))*x+(-13200))))*a+(((-656)*y+((((108)*x+(3184))*x+(2896))*x+(-66304)))*y+(((((729)*x+(-9936))*x+(-16576))*x+(-105952))*x+(10640))))))
theorem row2_112_identity (u B a y x : ℂ) :
  (((-9408)*a+((9639)*x+(-11928))))*row1_31 u B a y x+
  (((29568)*a+(183288)))*row1_32 u B a y x+
  (((123648)*B+((1166592)*a+((190848)*y+(-1870848)))))*row1_33 u B a y x+
  (((8848)*B+((-5712)*y+((9408)*x))))*row1_29 u B a y x+
  (((9408)*y))*row1_12 u B a y x+
  (((9408)*y+((-30744)*x)))*row1_30 u B a y x+
  (((5376)*y+((8624)*x)))*row1_35 u B a y x+
  (((-168)*x))*row1_5 u B a y x+
  (((-158)*x))*row1_23 u B a y x+
  (((683)*x))*row1_26 u B a y x+
  (((-37296)*x))*row1_27 u B a y x+
  (((-1166592)*x))*row1_28 u B a y x+
  (((1833216)*x))*row1_34 u B a y x=((336))*row2_112 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_29, row1_12, row1_30, row1_35, row1_5, row1_23, row1_26, row1_27, row1_28, row1_34, row2_112] <;> ring
theorem row2_112_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_112 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_112_identity u B a y x).symm
  have hz : ((336))*row2_112 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_29, z1_12, z1_30, z1_35, z1_5, z1_23, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((336):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_112_zero
def row2_113 (u B a y x : ℂ) : ℂ := (((((16)*x)*a+((32)*x))*B+(((16)*y+((-80)*x))*a+(((48)*x+(32))*y+((-16)*x))))*u+((((16)*x+(-16))*x)*B+((((-32)*y+((-108)*x+(48)))*a+((-64)*y+(((-54)*x+(-440))*x+(-48))))*a+((((-4)*x+(-16))*x+(-240))*y+((((-27)*x+(-80))*x+(-432))*x+(48))))))
theorem row2_113_identity (u B a y x : ℂ) :
  ((1))*row1_31 u B a y x+
  ((-3))*row1_32 u B a y x+
  (((-16)*y+(96)))*row1_33 u B a y x+
  (((1)*x))*row1_30 u B a y x+
  (((32)*x))*row1_34 u B a y x=((2))*row2_113 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_30, row1_34, row2_113] <;> ring
theorem row2_113_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_113 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_113_identity u B a y x).symm
  have hz : ((2))*row2_113 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_30, z1_34,mul_zero,add_zero] using he
  have hu : ((2):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_113_zero
def row2_114 (u B a y x : ℂ) : ℂ := ((((1)*x)*B+(((1)*x)*a^2))*u+(((1)*a+((1)*x^2+(-1)))*a+((-1)*y+((-2)*x+(1)))))
theorem row2_114_identity (u B a y x : ℂ) :
  ((1))*row1_31 u B a y x+
  ((-5))*row1_32 u B a y x+
  (((-32)*a+((-16)*y+(96))))*row1_33 u B a y x+
  (((32)*x))*row1_28 u B a y x+
  (((1)*x))*row1_30 u B a y x=((32))*row2_114 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_28, row1_30, row2_114] <;> ring
theorem row2_114_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_114 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_114_identity u B a y x).symm
  have hz : ((32))*row2_114 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_28, z1_30,mul_zero,add_zero] using he
  have hu : ((32):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_114_zero
def row2_115 (u B a y x : ℂ) : ℂ := ((((364032)*B+((-364032)*y+(364032)))*u+(((-148512)*y+((358608)*x+(1304448)))*B+(((470064)*y+((-597744)*x+(-242688)))*a+(((106176)*y+(((-26928)*x+(-151824))*x+(-382608)))*y+(((-51696)*x+(-216528))*x+(-151680))))))*u+(((((119448)*x+(-455040))*a+((-110592)*y+(((59724)*x+(-143472))*x+(-576384))))*a+((((53424)*x+(-110048))*x+(-103648))*y+((((77112)*x+(-508824))*x+(1090464))*x+(-1668480))))*B+((((120960)*a+((-79200)*y+(((265356)*x+(-1287684))*x+(306288))))*a+(((92448)*y+(((-52164)*x+(-502944))*x+(-1178736)))*y+((((132678)*x+(393138))*x+(-1666968))*x+(967824))))*a+(((((-39816)*x+(10112))*x+(169088))*y+((((-20034)*x+(355788))*x+(-623792))*x+(-2758640)))*y+(((((66339)*x+(-57375))*x+(316800))*x+(-3508704))*x+(-240144))))))
theorem row2_115_identity (u B a y x : ℂ) :
  (((-79632)*B+((-926856)*a+((-1260441)*x+(18648)))))*row1_31 u B a y x+
  (((238896)*B+((-465696)*a+(427896))))*row1_32 u B a y x+
  (((-13095936)*B+((-2128896)*a+((9894528)*y+(-22772736)))))*row1_33 u B a y x+
  (((-40771584)*u+((-6795264)*a+((1415680)*y+((-128572416)*x+(166483968))))))*row1_34 u B a y x+
  (((283136)*u+((141568)*B+((637056)*a+((-226240)*y+((521136)*x+(-566272)))))))*row1_35 u B a y x+
  (((35392)*B+((-35392)*y)))*row1_20 u B a y x+
  (((-1114848)*B+((1065456)*y+((-148176)*x))))*row1_29 u B a y x+
  (((-13590528)*a))*row1_18 u B a y x+
  (((11376)*a+((14220)*x)))*row1_23 u B a y x+
  (((-51192)*a+((-63549)*x)))*row1_26 u B a y x+
  (((79632)*y))*row1_11 u B a y x+
  (((-148176)*y))*row1_12 u B a y x+
  (((-68544)*y+((-322056)*x)))*row1_30 u B a y x+
  (((-79632)*x))*row1_4 u B a y x+
  (((2646)*x))*row1_5 u B a y x+
  (((1284192)*x))*row1_27 u B a y x+
  (((2128896)*x))*row1_28 u B a y x=((112))*row2_115 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_34, row1_35, row1_20, row1_29, row1_18, row1_23, row1_26, row1_11, row1_12, row1_30, row1_4, row1_5, row1_27, row1_28, row2_115] <;> ring
theorem row2_115_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_115 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_20 := row1_20_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_18 := row1_18_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_23 := row1_23_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_11 := row1_11_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_4 := row1_4_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_115_identity u B a y x).symm
  have hz : ((112))*row2_115 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_34, z1_35, z1_20, z1_29, z1_18, z1_23, z1_26, z1_11, z1_12, z1_30, z1_4, z1_5, z1_27, z1_28,mul_zero,add_zero] using he
  have hu : ((112):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_115_zero

def row2_116 (u B a y x : ℂ) : ℂ := ((((48)*x)*B+(((-96)*x)*a))*u+((((18)*x+(-72))*x^2)*B+(((((108)*x)*a+(((54)*x+(192))*x+(48)))*a+(((32)*x)*y+((((27)*x+(-216))*x+(336))*x+(-48))))*a+(((64)*x+(-48))*y+(((-96)*x+(-1056))*x+(48))))))
theorem row2_116_identity (u B a y x : ℂ) :
  ((3))*row1_31 u B a y x+
  ((-15))*row1_32 u B a y x+
  (((-96)*a+((-48)*y+(288))))*row1_33 u B a y x+
  (((96)*x))*row1_28 u B a y x+
  (((3)*x))*row1_30 u B a y x+
  (((-2)*x))*row1_35 u B a y x=((2))*row2_116 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_28, row1_30, row1_35, row2_116] <;> ring
theorem row2_116_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_116 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_116_identity u B a y x).symm
  have hz : ((2))*row2_116 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_28, z1_30, z1_35,mul_zero,add_zero] using he
  have hu : ((2):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_116_zero
def row2_117 (u B a y x : ℂ) : ℂ := (((((1264)*x+(-368))*y+((6816)*x))*B+(((6624)*y+((-26112)*x))*a+((((-1296)*x+(11680))*x+(13936))*y+(((432)*x+(-5088))*x))))*u+((((-368)*y+((368)*x))*a+((((-288)*x+(1152))*x)*y+((((-1000)*x+(6736))*x+(-3296))*x)))*B+((((-2560)*a+((-9760)*y+(((2916)*x+(-29808))*x+(11936))))*a+(((-512)*y+(((-160)*x+(4224))*x+(-15120)))*y+((((1458)*x+(3176))*x+(-149184))*x+(-11936))))*a+(((-1920)*y+((((108)*x+(1920))*x+(-896))*x+(-63776)))*y+(((((729)*x+(-9936))*x+(-15312))*x+(-99632))*x+(9376))))))
theorem row2_117_identity (u B a y x : ℂ) :
  (((-336)*a+((-189)*x+(-900))))*row1_31 u B a y x+
  (((1056)*a+(8916)))*row1_32 u B a y x+
  (((4416)*B+((56832)*a+((14400)*y+(-112320)))))*row1_33 u B a y x+
  (((336)*y))*row1_12 u B a y x+
  (((112)*y+((336)*x)))*row1_29 u B a y x+
  (((336)*y+((-1572)*x)))*row1_30 u B a y x+
  (((192)*y+((624)*x)))*row1_35 u B a y x+
  (((-6)*x))*row1_5 u B a y x+
  (((-1)*x))*row1_26 u B a y x+
  (((-1332)*x))*row1_27 u B a y x+
  (((-56832)*x))*row1_28 u B a y x+
  (((35136)*x))*row1_34 u B a y x=((12))*row2_117 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_12, row1_29, row1_30, row1_35, row1_5, row1_26, row1_27, row1_28, row1_34, row2_117] <;> ring
theorem row2_117_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_117 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_117_identity u B a y x).symm
  have hz : ((12))*row2_117 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_12, z1_29, z1_30, z1_35, z1_5, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((12):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_117_zero
def row2_118 (u B a y x : ℂ) : ℂ := ((((48)*x)*B+((((16)*x+(16))*y+((-96)*x))*a+(((32)*x+(32))*y)))*u+((((-32)*y+((-108)*x+(48)))*a+((-64)*y+(((-54)*x+(-408))*x+(-48))))*a+(((12)*x^2+(-240))*y+((((-27)*x+(-96))*x+(-480))*x+(48)))))
theorem row2_118_identity (u B a y x : ℂ) :
  ((1))*row1_31 u B a y x+
  ((-3))*row1_32 u B a y x+
  (((-16)*y+(96)))*row1_33 u B a y x+
  (((1)*x))*row1_30 u B a y x=((2))*row2_118 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_30, row2_118] <;> ring
theorem row2_118_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_118 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_118_identity u B a y x).symm
  have hz : ((2))*row2_118 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_30,mul_zero,add_zero] using he
  have hu : ((2):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_118_zero
def row2_119 (u B a y x : ℂ) : ℂ := ((((-224)*y+((1456)*x))*B+(((240)*y+((208)*x))*a+((((-624)*x+(-2288))*x+(624))*y+(((208)*x+(-624))*x))))*u+((((-224)*y+((224)*x))*a+((((72)*x+(-288))*x)*y+((((250)*x+(-1368))*x+(192))*x)))*B+((((640)*a+(((632)*x+(544))*y+(((1404)*x+(-2028))*x+(176))))*a+(((128)*y+(((40)*x+(208))*x+(304)))*y+((((702)*x+(3630))*x+(3800))*x+(-176))))*a+(((480)*y+((((52)*x+(468))*x+(4016))*x+(-2384)))*y+(((((351)*x+(351))*x+(5408))*x+(-9536))*x+(816))))))
theorem row2_119_identity (u B a y x : ℂ) :
  (((336)*a+((189)*x+(1848))))*row1_31 u B a y x+
  (((-1056)*a+(-9864)))*row1_32 u B a y x+
  (((10752)*B+((-56832)*a+((-29568)*y+(127488)))))*row1_33 u B a y x+
  (((-336)*y))*row1_12 u B a y x+
  (((-112)*y+((-336)*x)))*row1_29 u B a y x+
  (((-336)*y+((2520)*x)))*row1_30 u B a y x+
  (((-192)*y+((-624)*x)))*row1_35 u B a y x+
  (((6)*x))*row1_5 u B a y x+
  (((1)*x))*row1_26 u B a y x+
  (((384)*x))*row1_27 u B a y x+
  (((56832)*x))*row1_28 u B a y x+
  (((-19968)*x))*row1_34 u B a y x=((48))*row2_119 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_12, row1_29, row1_30, row1_35, row1_5, row1_26, row1_27, row1_28, row1_34, row2_119] <;> ring
theorem row2_119_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_119 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_119_identity u B a y x).symm
  have hz : ((48))*row2_119 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_12, z1_29, z1_30, z1_35, z1_5, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((48):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_119_zero
def row2_120 (u B a y x : ℂ) : ℂ := ((((896)*y+((9344)*x))*B+(((9152)*y+((-34960)*x))*a+((((1264)*x+(-1264))*y+(((-32)*x+(12944))*x+(17728)))*y+(((-832)*x+(-5088))*x))))*u+((((896)*y+((-896)*x))*a+((((-288)*x+(1152))*x)*y+((((-1000)*x+(5472))*x+(-768))*x)))*B+((((-2560)*a+((-11024)*y+(((2916)*x+(-38340))*x+(14464))))*a+(((-1776)*y+(((-160)*x+(5488))*x+(-18912)))*y+((((1458)*x+(-3618))*x+(-180152))*x+(-14464))))*a+(((-1920)*y+((((108)*x+(1604))*x+(-2160))*x+(-81472)))*y+(((((729)*x+(-12069))*x+(-21632))*x+(-136288))*x+(11904))))))
theorem row2_120_identity (u B a y x : ℂ) :
  (((-336)*a+((-189)*x+(-900))))*row1_31 u B a y x+
  (((1056)*a+(9864)))*row1_32 u B a y x+
  (((-10752)*B+((56832)*a+((29568)*y+(-127488)))))*row1_33 u B a y x+
  (((336)*y))*row1_12 u B a y x+
  (((112)*y+((336)*x)))*row1_29 u B a y x+
  (((336)*y+((-2520)*x)))*row1_30 u B a y x+
  (((192)*y+((624)*x)))*row1_35 u B a y x+
  (((-6)*x))*row1_5 u B a y x+
  (((-1)*x))*row1_26 u B a y x+
  (((-384)*x))*row1_27 u B a y x+
  (((-56832)*x))*row1_28 u B a y x+
  (((19968)*x))*row1_34 u B a y x=((12))*row2_120 u B a y x := by
  simp only [row1_31, row1_32, row1_33, row1_12, row1_29, row1_30, row1_35, row1_5, row1_26, row1_27, row1_28, row1_34, row2_120] <;> ring
theorem row2_120_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_120 u B a y x=0 := by
  have z1_31 := row1_31_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_12 := row1_12_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_29 := row1_29_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_30 := row1_30_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_5 := row1_5_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_26 := row1_26_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_27 := row1_27_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_28 := row1_28_zero u B a y x h0 h1 h2 h3 h4 h5
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_120_identity u B a y x).symm
  have hz : ((12))*row2_120 u B a y x=0 := by
    simpa only [z1_31, z1_32, z1_33, z1_12, z1_29, z1_30, z1_35, z1_5, z1_26, z1_27, z1_28, z1_34,mul_zero,add_zero] using he
  have hu : ((12):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_120_zero
def row2_121 (u B a y x : ℂ) : ℂ := (((((16)*x+(32))*x)*B+(((32)*y+((-112)*x))*a+(((32)*x+(32))*y)))*u+((((-16)*y+((-108)*x+(32)))*a+((-64)*y+(((-54)*x+(-408))*x+(-32))))*a+((((12)*x+(-16))*x+(-224))*y+((((-27)*x+(-128))*x+(-432))*x+(32)))))
theorem row2_121_identity (u B a y x : ℂ) :
  ((1))*row1_32 u B a y x=((1))*row2_121 u B a y x := by
  simp only [row1_32, row2_121] <;> ring
theorem row2_121_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_121 u B a y x=0 := by
  have z1_32 := row1_32_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_121_identity u B a y x).symm
  have hz : ((1))*row2_121 u B a y x=0 := by
    simpa only [z1_32,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_121_zero

def row2_122 (u B a y x : ℂ) : ℂ := (((((1)*x+(-1))*x)*a+(((1)*x+(-1))*y+((1)*x)))*u+(((-1)*y+((1)*x))*a+((((1)*x+(-1))*x+(-1))*x)))
theorem row2_122_identity (u B a y x : ℂ) :
  ((1))*row1_33 u B a y x=((1))*row2_122 u B a y x := by
  simp only [row1_33, row2_122] <;> ring
theorem row2_122_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_122 u B a y x=0 := by
  have z1_33 := row1_33_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_122_identity u B a y x).symm
  have hz : ((1))*row2_122 u B a y x=0 := by
    simpa only [z1_33,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_122_zero
def row2_123 (u B a y x : ℂ) : ℂ := ((((1)*a+(-1))*B+(((-1)*y+(1))*a+((1)*y+(-1))))*u+(((1)*x+(-1))*B+((-2)*a+(((-1)*x+(-1))*y+((1)*x+(3))))))
theorem row2_123_identity (u B a y x : ℂ) :
  ((1))*row1_34 u B a y x=((1))*row2_123 u B a y x := by
  simp only [row1_34, row2_123] <;> ring
theorem row2_123_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_123 u B a y x=0 := by
  have z1_34 := row1_34_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_123_identity u B a y x).symm
  have hz : ((1))*row2_123 u B a y x=0 := by
    simpa only [z1_34,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_123_zero
def row2_124 (u B a y x : ℂ) : ℂ := ((((48)*a+(96))*a)*u+((((-18)*x+(72))*x)*B+((((-108)*a+((-54)*x+(-192)))*a+((-32)*y+(((-27)*x+(264))*x+(-336))))*a+((-64)*y+((96)*x+(960))))))
theorem row2_124_identity (u B a y x : ℂ) :
  ((1))*row1_35 u B a y x=((1))*row2_124 u B a y x := by
  simp only [row1_35, row2_124] <;> ring
theorem row2_124_zero (u B a y x : ℂ) 
    (h0 : input0 u B a y x=0)
    (h1 : input1 u B a y x=0)
    (h2 : input2 u B a y x=0)
    (h3 : input3 u B a y x=0)
    (h4 : input4 u B a y x=0)
    (h5 : input5 u B a y x=0)
    : row2_124 u B a y x=0 := by
  have z1_35 := row1_35_zero u B a y x h0 h1 h2 h3 h4 h5
  have he := (row2_124_identity u B a y x).symm
  have hz : ((1))*row2_124 u B a y x=0 := by
    simpa only [z1_35,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_124_zero

end QuantitativeArithmeticSmallLevelTwentyFive.PositiveChart.MinimalSix
end
end
