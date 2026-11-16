module

public import Mathlib
public meta import QuantitativeArithmeticCompactCommandsV1
public meta import SmallLevelCertificateBatchCommandV1
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.NegativeSecondAlgebra
certificate_batch {
def input0 (B A Y X : ℂ) : ℂ := (((((1)*Y)*A+((1)*Y+((1)*X^2)))*A+(((-1)*X)*Y+(((-1)*X+(1))*X)))*A+(((-1)*X)*Y+(((-2)*X+(1))*X)))
def input1 (B A Y X : ℂ) : ℂ := ((((1)*Y)*A+((((1)*X^2+(-1))*X)*Y+(((-1)*X+(1))*X^2)))*A+((((-1)*X)*Y+((-1)*X^2))*Y+((((2)*X+(-3))*X+(1))*X)))
def input2 (B A Y X : ℂ) : ℂ := ((((((24)*X)*Y)*A+((24)*X^3))*A+((((-90)*X+(336))*X^2)*Y+(((-48)*X+(24))*X^2)))*B+((((((-492)*X+(-456))*Y)*A+(((((-48)*X+(-270))*X+(-888))*X+(-336))*Y+(((96)*X+(-456))*X^2)))*A+((((-112)*X)*Y+((((-231)*X+(1320))*X+(-1176))*X))*Y+((((-72)*X+(672))*X+(-456))*X)))*A+((((-224)*X)*Y+(((552)*X+(5040))*X))*Y+((((-240)*X+(792))*X+(-336))*X))))
def input3 (B A Y X : ℂ) : ℂ := ((((((1)*X+(-1))*X^3)*Y)*A)*B+((((((((-1)*X+(1))*X+(-1))*Y)*A+(((((-1)*X+(-1))*X^2+(1))*X)*Y+(((2)*X+(-1))*X^2)))*A+(((((2)*X+(1))*X)*Y+(((-3)*X+(1))*X))*Y+(((((-1)*X+(-4))*X+(4))*X+(-1))*X)))*A+(((((-1)*X+(-1))*X^3)*Y+((((3)*X+(4))*X+(-1))*X^2))*Y+((-1)*X^4)))*A+(((((-1)*X+(-1))*X^2)*Y+(((-2)*X+(2))*X^3))*Y+((((6)*X+(-5))*X+(1))*X^2))))
def input4 (B A Y X : ℂ) : ℂ := (((((((128)*X+(64))*Y+(((492)*X+(-72))*X))*Y)*A+((((224)*X)*Y+(((((48)*X+(478))*X+(2032))*X+(-144))*X))*Y+(((-96)*X+(-72))*X^3)))*A+((((((-60)*X+(-16))*X+(896))*X)*Y+(((((231)*X+(448))*X+(1784))*X+(64))*X))*Y+((((72)*X+(-96))*X+(-72))*X^2)))*A+((((120)*X+(144))*X^2)*Y+((((240)*X+(168))*X+(-144))*X^2)))
compact_certificate def row0_0 (B A Y X : ℂ) : ℂ := (((((1)*Y)*A+((1)*Y+((1)*X^2)))*A+(((-1)*X)*Y+(((-1)*X+(1))*X)))*A+(((-1)*X)*Y+(((-2)*X+(1))*X)))
compact_certificate theorem row0_0_identity (B A Y X : ℂ) :
  ((1))*input0 B A Y X=((1))*row0_0 B A Y X := by
  simp only [input0, row0_0] <;> ring
compact_certificate theorem row0_0_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row0_0 B A Y X=0 := by
  have he := (row0_0_identity B A Y X).symm
  have hz : ((1))*row0_0 B A Y X=0 := by
    simpa only [h0,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_0_zero
compact_certificate def row0_1 (B A Y X : ℂ) : ℂ := ((((1)*Y)*A+((((1)*X^2+(-1))*X)*Y+(((-1)*X+(1))*X^2)))*A+((((-1)*X)*Y+((-1)*X^2))*Y+((((2)*X+(-3))*X+(1))*X)))
compact_certificate theorem row0_1_identity (B A Y X : ℂ) :
  ((1))*input1 B A Y X=((1))*row0_1 B A Y X := by
  simp only [input1, row0_1] <;> ring
compact_certificate theorem row0_1_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row0_1 B A Y X=0 := by
  have he := (row0_1_identity B A Y X).symm
  have hz : ((1))*row0_1 B A Y X=0 := by
    simpa only [h1,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_1_zero
compact_certificate def row0_2 (B A Y X : ℂ) : ℂ := ((((((-24)*X)*Y)*A+((-24)*X^3))*A+((((90)*X+(-336))*X^2)*Y+(((48)*X+(-24))*X^2)))*B+((((((492)*X+(456))*Y)*A+(((((48)*X+(270))*X+(888))*X+(336))*Y+(((-96)*X+(456))*X^2)))*A+((((112)*X)*Y+((((231)*X+(-1320))*X+(1176))*X))*Y+((((72)*X+(-672))*X+(456))*X)))*A+((((224)*X)*Y+(((-552)*X+(-5040))*X))*Y+((((240)*X+(-792))*X+(336))*X))))
compact_certificate theorem row0_2_identity (B A Y X : ℂ) :
  ((1))*input2 B A Y X=((-1))*row0_2 B A Y X := by
  simp only [input2, row0_2] <;> ring
compact_certificate theorem row0_2_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row0_2 B A Y X=0 := by
  have he := (row0_2_identity B A Y X).symm
  have hz : ((-1))*row0_2 B A Y X=0 := by
    simpa only [h2,mul_zero,add_zero] using he
  have hu : ((-1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_2_zero
compact_certificate def row0_3 (B A Y X : ℂ) : ℂ := ((((((-1)*X+(1))*X^3)*Y)*A)*B+((((((((1)*X+(-1))*X+(1))*Y)*A+(((((1)*X+(1))*X^2+(-1))*X)*Y+(((-2)*X+(1))*X^2)))*A+(((((-2)*X+(-1))*X)*Y+(((3)*X+(-1))*X))*Y+(((((1)*X+(4))*X+(-4))*X+(1))*X)))*A+(((((1)*X+(1))*X^3)*Y+((((-3)*X+(-4))*X+(1))*X^2))*Y+((1)*X^4)))*A+(((((1)*X+(1))*X^2)*Y+(((2)*X+(-2))*X^3))*Y+((((-6)*X+(5))*X+(-1))*X^2))))
compact_certificate theorem row0_3_identity (B A Y X : ℂ) :
  ((1))*input3 B A Y X=((-1))*row0_3 B A Y X := by
  simp only [input3, row0_3] <;> ring
compact_certificate theorem row0_3_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row0_3 B A Y X=0 := by
  have he := (row0_3_identity B A Y X).symm
  have hz : ((-1))*row0_3 B A Y X=0 := by
    simpa only [h3,mul_zero,add_zero] using he
  have hu : ((-1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_3_zero
compact_certificate def row0_4 (B A Y X : ℂ) : ℂ := (((((((128)*X+(64))*Y+(((492)*X+(-72))*X))*Y)*A+((((224)*X)*Y+(((((48)*X+(478))*X+(2032))*X+(-144))*X))*Y+(((-96)*X+(-72))*X^3)))*A+((((((-60)*X+(-16))*X+(896))*X)*Y+(((((231)*X+(448))*X+(1784))*X+(64))*X))*Y+((((72)*X+(-96))*X+(-72))*X^2)))*A+((((120)*X+(144))*X^2)*Y+((((240)*X+(168))*X+(-144))*X^2)))
compact_certificate theorem row0_4_identity (B A Y X : ℂ) :
  ((1))*input4 B A Y X=((1))*row0_4 B A Y X := by
  simp only [input4, row0_4] <;> ring
compact_certificate theorem row0_4_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row0_4 B A Y X=0 := by
  have he := (row0_4_identity B A Y X).symm
  have hz : ((1))*row0_4 B A Y X=0 := by
    simpa only [h4,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_4_zero
compact_certificate def row1_2 (B A Y X : ℂ) : ℂ := (((((((91776)*X)*Y+((339516)*X^2+(-91776)))*Y)*A+(((91776)*X)*Y+((((339516)*X+(91776))*X+(-91776))*X^2)))*A+((((((-344160)*X+(1284864))*X+(91776))*X)*Y+((((-1273185)*X+(4569672))*X+(183552))*X^2))*Y+(((((-679032)*X+(155964))*X+(275328))*X+(-91776))*X)))*B+((((((((49152)*X+(24576))*Y+((188928)*X^2))*Y+((377856)*X^2))*Y)*A+(((((86016)*X)*Y+((((18432)*X^2+(-252192))*X+(-110160))*X+(1110534)))*Y+(((16789644)*X+(4067712))*X+(-19787670)))*Y+(((-73728)*X+(3649032))*X^3)))*A+(((((((-23040)*X+(-6144))*X+(-84224))*X)*Y+((((88704)*X^2+(3909696))*X+(10144578))*X))*Y+(((9659670)*X+(19787670))*X))*Y+((((260352)*X+(16483590))*X+(-16138638))*X^2)))*A+(((((-2462758)*X)*Y+((((46080)*X+(-2403798))*X+(41920446))*X))*Y+(((((92160)*X+(12162780))*X+(85934436))*X+(-2538498))*X))*Y+(((((-225792)*X+(-47597868))*X+(63430722))*X+(-19787670))*X))))
compact_certificate theorem row1_2_identity (B A Y X : ℂ) :
  (((1578432)*Y+((15049296)*X+(7298064))))*row0_0 B A Y X+
  (((-183552)*B+((-7298064)*A+((3212364)*Y+((-410112)*X+(-46873404))))))*row0_1 B A Y X+
  (((768)*Y+(29829)))*row0_4 B A Y X+
  (((-7648)*Y+((-28293)*X)))*row0_2 B A Y X=((2))*row1_2 B A Y X := by
  simp only [row0_0, row0_1, row0_4, row0_2, row1_2] <;> ring
compact_certificate theorem row1_2_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_2 B A Y X=0 := by
  have z0_0 := row0_0_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_1 := row0_1_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_4 := row0_4_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_2 := row0_2_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_2_identity B A Y X).symm
  have hz : ((2))*row1_2 B A Y X=0 := by
    simpa only [z0_0, z0_1, z0_4, z0_2,mul_zero,add_zero] using he
  have hu : ((2):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_2_zero
compact_certificate def row1_3 (B A Y X : ℂ) : ℂ := (((((((5904)*X)*Y)*A+(((5448)*X^2+(22140))*Y+((5904)*X^3)))*A+((((82656)*X+(-22140))*X)*Y+((((5448)*X+(-33948))*X+(28044))*X^2)))*A+((((-22140)*X)*Y+((((-20430)*X+(76272))*X+(-22140))*X^2))*Y+(((((-10896)*X+(49728))*X+(-66420))*X+(22140))*X)))*B+(((((((-121032)*X)*Y)*A+((((3072)*X^2)*Y+((-185736)*X^2))*Y+((23616)*X^3)))*A+(((((5376)*X+(-30240))*X+(432))*Y+((((1152)*X^3+(96072))*X+(-185547))*X+(-442020)))*Y+(((((-2304)*X+(21216))*X+(125652))*X+(23616))*X^2)))*A+((((((-1440)*X^2+(-3728))*X+(-141372))*X)*Y+((((5544)*X^3+(-592773))*X+(1569684))*X))*Y+(((((1728)*X+(-63969))*X+(303873))*X+(-269136))*X^2)))*A+(((((336)*X)*Y+(((-94969)*X+(336648))*X))*Y+(((((2880)*X+(82191))*X+(1158144))*X+(105036))*X))*Y+((((((5760)*X+(35586))*X+(-1276083))*X+(1512465))*X+(-442020))*X))))
compact_certificate theorem row1_3_identity (B A Y X : ℂ) :
  (((112176)*A+((768)*Y+((321096)*X+(-104604)))))*row0_0 B A Y X+
  (((22140)*B+((75084)*A+((-336)*Y+((44457)*X+(-337416))))))*row0_1 B A Y X+
  (((24)*X+(-12)))*row0_4 B A Y X+
  (((-246)*A+((-227)*X)))*row0_2 B A Y X=((1))*row1_3 B A Y X := by
  simp only [row0_0, row0_1, row0_4, row0_2, row1_3] <;> ring
compact_certificate theorem row1_3_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_3 B A Y X=0 := by
  have z0_0 := row0_0_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_1 := row0_1_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_4 := row0_4_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_2 := row0_2_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_3_identity B A Y X).symm
  have hz : ((1))*row1_3 B A Y X=0 := by
    simpa only [z0_0, z0_1, z0_4, z0_2,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_3_zero
compact_certificate def row1_4 (B A Y X : ℂ) : ℂ := (((((((41280)*X)*Y)*A+((((-5760)*X)*Y+((-8028)*X^2+(169776)))*Y+((41280)*X^3)))*A+(((((9216)*X^2+(577920))*X+(-169776))*X)*Y+((((-8028)*X+(-252336))*X+(211056))*X^2)))*A+((((((21600)*X+(-80640))*X+(-169776))*X)*Y+((((30105)*X+(-100872))*X+(-175536))*X^2))*Y+(((((16056)*X+(331524))*X+(-509328))*X+(169776))*X)))*B+((((((((24576)*X+(12288))*Y+(((85248)*X+(-850848))*X))*Y)*A+(((-528864)*X^2)*Y+(((-18432)*X+(169728))*X^3)))*A+(((((80160)*X+(-80176))*X+(-69990))*Y+(((405588)*X+(-1858284))*X+(-254778)))*Y+((((93312)*X+(521064))*X+(169728))*X^2)))*A+(((((26880)*X)*Y+((((-9216)*X^2+(-259200))*X+(-1925618))*X))*Y+(((-3472074)*X+(8130042))*X))*Y+((((-215460)*X+(-716610))*X+(624174))*X^2)))*A+(((((175494)*X)*Y+((((-9216)*X+(-130830))*X+(-1987134))*X))*Y+(((((-18432)*X+(-688896))*X+(-3743268))*X+(991218))*X))*Y+(((((205128)*X+(-2072256))*X+(1494402))*X+(-254778))*X))))
compact_certificate theorem row1_4_identity (B A Y X : ℂ) :
  (((1587072)*A+((-57792)*Y+((2605296)*X+(-2122416)))))*row0_0 B A Y X+
  (((339552)*B+((1691184)*A+((-243468)*Y+((371592)*X+(1612860))))))*row0_1 B A Y X+
  ((-18432))*row0_3 B A Y X+
  (((384)*A+(-2517)))*row0_4 B A Y X+
  (((-3440)*A+((480)*Y+((669)*X))))*row0_2 B A Y X=((2))*row1_4 B A Y X := by
  simp only [row0_0, row0_1, row0_3, row0_4, row0_2, row1_4] <;> ring
compact_certificate theorem row1_4_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_4 B A Y X=0 := by
  have z0_0 := row0_0_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_1 := row0_1_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_3 := row0_3_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_4 := row0_4_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_2 := row0_2_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_4_identity B A Y X).symm
  have hz : ((2))*row1_4 B A Y X=0 := by
    simpa only [z0_0, z0_1, z0_3, z0_4, z0_2,mul_zero,add_zero] using he
  have hu : ((2):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_4_zero
compact_certificate def row1_6 (B A Y X : ℂ) : ℂ := (((((((-24)*X)*Y)*A+((-90)*Y+((-24)*X^3)))*A+((((-336)*X+(90))*X)*Y+(((138)*X+(-114))*X^2)))*A+((((90)*X)*Y+((90)*X^2))*Y+((((-180)*X+(270))*X+(-90))*X)))*B+(((((((492)*X)*Y)*A+((((48)*X+(270))*X^2)*Y+((-96)*X^3)))*A+((((112)*X)*Y+(((-1320)*X+(975))*X+(351)))*Y+(((-585)*X+(-96))*X^2)))*A+((((455)*X)*Y+(((567)*X+(-4935))*X))*Y+(((666)*X+(-426))*X^2)))*A+((((888)*X+(-351))*X)*Y+((((1776)*X+(-1590))*X+(351))*X))))
compact_certificate theorem row1_6_identity (B A Y X : ℂ) :
  (((-456)*A+((-888)*X+(351))))*row0_0 B A Y X+
  (((-90)*B+((-231)*A)))*row0_1 B A Y X+
  (((1)*A))*row0_2 B A Y X=((1))*row1_6 B A Y X := by
  simp only [row0_0, row0_1, row0_2, row1_6] <;> ring
compact_certificate theorem row1_6_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_6 B A Y X=0 := by
  have z0_0 := row0_0_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_1 := row0_1_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_2 := row0_2_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_6_identity B A Y X).symm
  have hz : ((1))*row1_6 B A Y X=0 := by
    simpa only [z0_0, z0_1, z0_2,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_6_zero
compact_certificate def row1_7 (B A Y X : ℂ) : ℂ := (((((((-384)*X)*Y+((-1476)*X^2+(384)))*Y)*A+(((-384)*X)*Y+((((-1476)*X+(-384))*X+(384))*X^2)))*A+((((((1440)*X+(-5376))*X+(-384))*X)*Y+((((5535)*X+(-19896))*X+(-768))*X^2))*Y+(((((2952)*X+(-708))*X+(-1152))*X+(384))*X)))*B+((((((((768)*X+(4320))*X+(432))*X+(-5370))*Y+(((-66420)*X+(-17280))*X+(85866)))*Y+((-14328)*X^3))*A+(((((1792)*X)*Y+(((-13248)*X+(-39870))*X))*Y+(((-34026)*X+(-85866))*X))*Y+(((-74490)*X+(71538))*X^2)))*A+(((((10970)*X)*Y+(((12330)*X+(-177474))*X))*Y+((((-52260)*X+(-370332))*X+(8958))*X))*Y+((((206292)*X+(-274878))*X+(85866))*X))))
compact_certificate theorem row1_7_identity (B A Y X : ℂ) :
  (((-6720)*Y+((-64944)*X+(-28656))))*row0_0 B A Y X+
  (((768)*B+((28656)*A+((-14772)*Y+(200388)))))*row0_1 B A Y X+
  ((-123))*row0_4 B A Y X+
  (((32)*Y+((123)*X)))*row0_2 B A Y X=((2))*row1_7 B A Y X := by
  simp only [row0_0, row0_1, row0_4, row0_2, row1_7] <;> ring
compact_certificate theorem row1_7_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_7 B A Y X=0 := by
  have z0_0 := row0_0_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_1 := row0_1_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_4 := row0_4_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_2 := row0_2_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_7_identity B A Y X).symm
  have hz : ((2))*row1_7 B A Y X=0 := by
    simpa only [z0_0, z0_1, z0_4, z0_2,mul_zero,add_zero] using he
  have hu : ((2):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_7_zero
compact_certificate def row1_8 (B A Y X : ℂ) : ℂ := ((((((-24)*X^2)*Y)*A+((-24)*X^4))*A+((((90)*X+(-336))*X^3)*Y+(((48)*X+(-24))*X^3)))*B+((((((492)*X^2)*Y)*A+(((((48)*X^2+(888))*X+(-81))*X+(1590))*Y+(((-96)*X+(270))*X^3)))*A+(((((112)*X+(270))*X)*Y+(((2133)*X+(-1590))*X))*Y+((((303)*X+(-2307))*X+(1860))*X^2)))*A+(((((455)*X+(-1320))*X)*Y+((((-321)*X+(-5904))*X+(-270))*X))*Y+(((((-222)*X+(3453))*X+(-4851))*X+(1590))*X))))
compact_certificate theorem row1_8_identity (B A Y X : ℂ) :
  (((-456)*X+(270)))*row0_0 B A Y X+
  (((-270)*A+((-231)*X+(1320))))*row0_1 B A Y X+
  (((1)*X))*row0_2 B A Y X=((1))*row1_8 B A Y X := by
  simp only [row0_0, row0_1, row0_2, row1_8] <;> ring
compact_certificate theorem row1_8_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_8 B A Y X=0 := by
  have z0_0 := row0_0_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_1 := row0_1_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_2 := row0_2_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_8_identity B A Y X).symm
  have hz : ((1))*row1_8 B A Y X=0 := by
    simpa only [z0_0, z0_1, z0_2,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_8_zero
compact_certificate def row1_9 (B A Y X : ℂ) : ℂ := ((((((12)*X^2)*Y)*A+((12)*X^4))*A+((((-45)*X+(168))*X^3)*Y+(((-24)*X+(12))*X^3)))*B+((((((64)*X)*Y^2)*A+((((112)*X+(-2))*Y+(((540)*X+(128))*X+(-750)))*Y+((104)*X^3)))*A+(((((-64)*X+(554))*X)*Y+(((206)*X+(750))*X))*Y+(((670)*X+(-646))*X^2)))*A+(((((-30)*X)*Y+(((-142)*X+(886))*X))*Y+((((396)*X+(3156))*X+(-106))*X))*Y+((((-1756)*X+(2378))*X+(-750))*X))))
compact_certificate theorem row1_9_identity (B A Y X : ℂ) :
  (((-64)*Y+((528)*X+(208))))*row0_0 B A Y X+
  (((-208)*A+((60)*Y+(-1708))))*row0_1 B A Y X+
  ((1))*row0_4 B A Y X+
  (((-1)*X))*row0_2 B A Y X=((2))*row1_9 B A Y X := by
  simp only [row0_0, row0_1, row0_4, row0_2, row1_9] <;> ring
compact_certificate theorem row1_9_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_9 B A Y X=0 := by
  have z0_0 := row0_0_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_1 := row0_1_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_4 := row0_4_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_2 := row0_2_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_9_identity B A Y X).symm
  have hz : ((2))*row1_9 B A Y X=0 := by
    simpa only [z0_0, z0_1, z0_4, z0_2,mul_zero,add_zero] using he
  have hu : ((2):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_9_zero

compact_certificate def row1_10 (B A Y X : ℂ) : ℂ := (((((1)*Y)*A+((((1)*X^2+(-1))*X)*Y+(((-1)*X+(1))*X^2)))*A+((((-1)*X)*Y+((-1)*X^2))*Y+((((2)*X+(-3))*X+(1))*X)))*B)
compact_certificate theorem row1_10_identity (B A Y X : ℂ) :
  (((1)*B))*row0_1 B A Y X=((1))*row1_10 B A Y X := by
  simp only [row0_1, row1_10] <;> ring
compact_certificate theorem row1_10_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_10 B A Y X=0 := by
  have z0_1 := row0_1_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_10_identity B A Y X).symm
  have hz : ((1))*row1_10 B A Y X=0 := by
    simpa only [z0_1,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_10_zero
compact_certificate def row1_11 (B A Y X : ℂ) : ℂ := ((((((1)*X^2+(-1))*X+(-1))*Y+((-1)*X^3))*A+((((-1)*X)*Y+(((-1)*X+(1))*X))*Y+(((2)*X+(-2))*X^2)))*A+(((1)*X)*Y+(((2)*X+(-1))*X)))
compact_certificate theorem row1_11_identity (B A Y X : ℂ) :
  ((-1))*row0_0 B A Y X+
  (((1)*A))*row0_1 B A Y X=((1))*row1_11 B A Y X := by
  simp only [row0_0, row0_1, row1_11] <;> ring
compact_certificate theorem row1_11_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_11 B A Y X=0 := by
  have z0_0 := row0_0_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_1 := row0_1_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_11_identity B A Y X).symm
  have hz : ((1))*row1_11 B A Y X=0 := by
    simpa only [z0_0, z0_1,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_11_zero
compact_certificate def row1_12 (B A Y X : ℂ) : ℂ := (((((1)*Y+(1))*Y)*A+(((((1)*X^2+(-1))*X)*Y+(((1)*X+(-1))*X))*Y+(((-1)*X+(1))*X^2)))*A+(((((-1)*X)*Y+(((-1)*X+(-1))*X))*Y+((((2)*X+(-4))*X+(1))*X))*Y+((((2)*X+(-3))*X+(1))*X)))
compact_certificate theorem row1_12_identity (B A Y X : ℂ) :
  (((1)*Y+(1)))*row0_1 B A Y X=((1))*row1_12 B A Y X := by
  simp only [row0_1, row1_12] <;> ring
compact_certificate theorem row1_12_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_12 B A Y X=0 := by
  have z0_1 := row0_1_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_12_identity B A Y X).symm
  have hz : ((1))*row1_12 B A Y X=0 := by
    simpa only [z0_1,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_12_zero
compact_certificate def row1_14 (B A Y X : ℂ) : ℂ := ((((((1)*Y)*A+((1)*Y+((1)*X^2)))*A+(((-1)*X)*Y+(((-1)*X+(1))*X)))*A+(((-1)*X)*Y+(((-2)*X+(1))*X)))*B)
compact_certificate theorem row1_14_identity (B A Y X : ℂ) :
  (((1)*B))*row0_0 B A Y X=((1))*row1_14 B A Y X := by
  simp only [row0_0, row1_14] <;> ring
compact_certificate theorem row1_14_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_14 B A Y X=0 := by
  have z0_0 := row0_0_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_14_identity B A Y X).symm
  have hz : ((1))*row1_14 B A Y X=0 := by
    simpa only [z0_0,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_14_zero
compact_certificate def row1_15 (B A Y X : ℂ) : ℂ := ((((((1)*Y)*A+((1)*X^2))*A+(((-1)*X+(-1))*Y+(((-2)*X+(1))*X)))*A+((-1)*X^2))*A+(((1)*X)*Y+(((2)*X+(-1))*X)))
compact_certificate theorem row1_15_identity (B A Y X : ℂ) :
  (((1)*A+(-1)))*row0_0 B A Y X=((1))*row1_15 B A Y X := by
  simp only [row0_0, row1_15] <;> ring
compact_certificate theorem row1_15_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_15 B A Y X=0 := by
  have z0_0 := row0_0_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_15_identity B A Y X).symm
  have hz : ((1))*row1_15 B A Y X=0 := by
    simpa only [z0_0,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_15_zero
compact_certificate def row1_17 (B A Y X : ℂ) : ℂ := ((((((24)*X)*Y)*A+((24)*X^3))*A+((((-90)*X+(336))*X^2)*Y+(((-48)*X+(24))*X^2)))*B+((((((-270)*X+(-444))*X+(303))*Y+((540)*X^3))*A+((((-160)*X)*Y+(((780)*X+(-1815))*X))*Y+(((-699)*X+(843))*X^2)))*A+((((-455)*X)*Y+(((-171)*X+(4632))*X))*Y+((((-762)*X+(-225))*X+(303))*X))))
compact_certificate theorem row1_17_identity (B A Y X : ℂ) :
  (((492)*X+(408)))*row0_0 B A Y X+
  (((48)*A+(231)))*row0_1 B A Y X+
  ((-1))*row0_2 B A Y X=((1))*row1_17 B A Y X := by
  simp only [row0_0, row0_1, row0_2, row1_17] <;> ring
compact_certificate theorem row1_17_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_17 B A Y X=0 := by
  have z0_0 := row0_0_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_1 := row0_1_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z0_2 := row0_2_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_17_identity B A Y X).symm
  have hz : ((1))*row1_17 B A Y X=0 := by
    simpa only [z0_0, z0_1, z0_2,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_17_zero
compact_certificate def row1_19 (B A Y X : ℂ) : ℂ := ((((1)*Y)*A+((((1)*X^2+(-1))*X)*Y+(((-1)*X+(1))*X^2)))*A+((((-1)*X)*Y+((-1)*X^2))*Y+((((2)*X+(-3))*X+(1))*X)))
compact_certificate theorem row1_19_identity (B A Y X : ℂ) :
  ((1))*row0_1 B A Y X=((1))*row1_19 B A Y X := by
  simp only [row0_1, row1_19] <;> ring
compact_certificate theorem row1_19_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_19 B A Y X=0 := by
  have z0_1 := row0_1_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_19_identity B A Y X).symm
  have hz : ((1))*row1_19 B A Y X=0 := by
    simpa only [z0_1,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_19_zero
compact_certificate def row1_20 (B A Y X : ℂ) : ℂ := (((((1)*Y)*A+((1)*Y+((1)*X^2)))*A+(((-1)*X)*Y+(((-1)*X+(1))*X)))*A+(((-1)*X)*Y+(((-2)*X+(1))*X)))
compact_certificate theorem row1_20_identity (B A Y X : ℂ) :
  ((1))*row0_0 B A Y X=((1))*row1_20 B A Y X := by
  simp only [row0_0, row1_20] <;> ring
compact_certificate theorem row1_20_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row1_20 B A Y X=0 := by
  have z0_0 := row0_0_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row1_20_identity B A Y X).symm
  have hz : ((1))*row1_20 B A Y X=0 := by
    simpa only [z0_0,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_20_zero
compact_certificate def row2_17 (B A Y X : ℂ) : ℂ := (((((((4320)*X^2)*Y)*A+((-61020)*Y+((4320)*X^4)))*A+((((7560)*X+(61020))*X)*Y+((((-33480)*X+(65340))*X+(-61020))*X^2)))*A+(((((-24840)*X+(61020))*X)*Y+(((60210)*X+(-254340))*X^2))*Y+(((((49680)*X+(-146880))*X+(183060))*X+(-61020))*X)))*B+(((((((-79920)*X^2)*Y)*A+((17280)*X^4))*A+(((((-37440)*X+(-47064))*X+(-9664))*Y+(((541614)*X+(592130))*X+(-47221)))*Y+((-42970)*X^3)))*A+(((((-32300)*X+(676490))*X)*Y+(((841266)*X+(1941541))*X))*Y+((((26124)*X+(-135469))*X+(-107471))*X^2)))*A+((((((8640)*X+(-6720))*X)*Y+((((17280)*X+(76544))*X+(555775))*X))*Y+((((102004)*X+(231615))*X+(-4735434))*X))*Y+(((((-190488)*X+(676302))*X+(-196087))*X+(-47221))*X))))
compact_certificate theorem row2_17_identity (B A Y X : ℂ) :
  ((-3330))*row1_4 B A Y X+
  (((3675129)*A+(-6562986)))*row1_9 B A Y X+
  (((6047280)*A+((-799200)*Y+((2167608)*X+(-3356640)))))*row1_17 B A Y X+
  (((348611040)*B+((2112511680)*A+(-3308023776))))*row1_19 B A Y X+
  (((111973968)*Y+((2181470940)*X+(-1613293536))))*row1_20 B A Y X+
  (((19483)*A))*row1_7 B A Y X+
  (((-968220)*A))*row1_8 B A Y X+
  (((-7481472)*A+((-28055520)*Y+((175371480)*X))))*row1_10 B A Y X+
  (((-291345288)*A))*row1_11 B A Y X+
  (((-311728)*Y+((968220)*X)))*row1_6 B A Y X+
  (((40919040)*Y+((-2833323840)*X)))*row1_15 B A Y X+
  (((-30689280)*X))*row1_12 B A Y X+
  (((-7672320)*X))*row1_14 B A Y X=((3552))*row2_17 B A Y X := by
  simp only [row1_4, row1_9, row1_17, row1_19, row1_20, row1_7, row1_8, row1_10, row1_11, row1_6, row1_15, row1_12, row1_14, row2_17] <;> ring
compact_certificate theorem row2_17_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_17 B A Y X=0 := by
  have z1_4 := row1_4_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_9 := row1_9_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_17 := row1_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_7 := row1_7_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_8 := row1_8_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_10 := row1_10_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_11 := row1_11_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_6 := row1_6_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_15 := row1_15_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_12 := row1_12_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_14 := row1_14_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_17_identity B A Y X).symm
  have hz : ((3552))*row2_17 B A Y X=0 := by
    simpa only [z1_4, z1_9, z1_17, z1_19, z1_20, z1_7, z1_8, z1_10, z1_11, z1_6, z1_15, z1_12, z1_14,mul_zero,add_zero] using he
  have hu : ((3552):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_17_zero
compact_certificate def row2_20 (B A Y X : ℂ) : ℂ := ((((((24)*X^3+(-24))*Y+((-24)*X^3))*A+((((-24)*X)*Y+(((-24)*X+(24))*X))*Y+(((72)*X+(-48))*X^2)))*A+(((((-90)*X+(336))*X+(24))*X)*Y+((((-48)*X+(72))*X+(-24))*X)))*B+((((((-270)*X+(-444))*X+(303))*Y+((540)*X^3))*A+((((-160)*X)*Y+(((780)*X+(-1815))*X))*Y+(((-699)*X+(843))*X^2)))*A+((((-455)*X)*Y+(((-171)*X+(4632))*X))*Y+((((-762)*X+(-225))*X+(303))*X))))
compact_certificate theorem row2_20_identity (B A Y X : ℂ) :
  ((1))*row1_17 B A Y X+
  (((-24)*B))*row1_20 B A Y X+
  (((24)*A))*row1_10 B A Y X=((1))*row2_20 B A Y X := by
  simp only [row1_17, row1_20, row1_10, row2_20] <;> ring
compact_certificate theorem row2_20_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_20 B A Y X=0 := by
  have z1_17 := row1_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_10 := row1_10_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_20_identity B A Y X).symm
  have hz : ((1))*row2_20 B A Y X=0 := by
    simpa only [z1_17, z1_20, z1_10,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_20_zero
compact_certificate def row2_21 (B A Y X : ℂ) : ℂ := (((((180)*Y)*A+((((720)*X+(-180))*X)*Y+(((-180)*X+(180))*X^2)))*A+((((-180)*X)*Y+(((-180)*X+(540))*X^2))*Y+((((360)*X+(-540))*X+(180))*X)))*B+((((((1080)*X^3)*Y)*A+((((-1304)*X+(-4))*Y+(((2004)*X+(-1375))*X+(914)))*Y+((4160)*X^3)))*A+(((((160)*X+(20))*X)*Y+(((1491)*X+(6406))*X))*Y+((((159)*X+(-5329))*X+(5074))*X^2)))*A+(((((-60)*X)*Y+(((299)*X+(-330))*X))*Y+((((679)*X+(-1950))*X+(8436))*X))*Y+(((((-318)*X+(-5823))*X+(1163))*X+(914))*X))))
compact_certificate theorem row2_21_identity (B A Y X : ℂ) :
  (((-246)*A+(444)))*row1_9 B A Y X+
  (((444)*A+((-222)*X+(444))))*row1_17 B A Y X+
  (((39960)*B+((-219420)*A+(264624))))*row1_19 B A Y X+
  (((-11232)*Y+((484281)*X+(136752))))*row1_20 B A Y X+
  (((-2)*A))*row1_7 B A Y X+
  (((135)*A))*row1_8 B A Y X+
  (((768)*A+((2880)*Y+((-12150)*X))))*row1_10 B A Y X+
  (((279282)*A))*row1_11 B A Y X+
  (((32)*Y+((-135)*X)))*row1_6 B A Y X+
  (((-10656)*X))*row1_14 B A Y X=((222))*row2_21 B A Y X := by
  simp only [row1_9, row1_17, row1_19, row1_20, row1_7, row1_8, row1_10, row1_11, row1_6, row1_14, row2_21] <;> ring
compact_certificate theorem row2_21_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_21 B A Y X=0 := by
  have z1_9 := row1_9_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_17 := row1_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_7 := row1_7_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_8 := row1_8_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_10 := row1_10_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_11 := row1_11_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_6 := row1_6_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_14 := row1_14_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_21_identity B A Y X).symm
  have hz : ((222))*row2_21 B A Y X=0 := by
    simpa only [z1_9, z1_17, z1_19, z1_20, z1_7, z1_8, z1_10, z1_11, z1_6, z1_14,mul_zero,add_zero] using he
  have hu : ((222):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_21_zero
compact_certificate def row2_23 (B A Y X : ℂ) : ℂ := (((((((1)*X^2+(-1))*X+(-1))*Y+((-1)*X+(-3)))*Y+((-1)*X^3))*A+(((((-1)*X)*Y+((-1)*X^2))*Y+(((-3)*X+(3))*X))*Y+(((4)*X+(-4))*X^2)))*A+((((3)*X)*Y+((4)*X^2))*Y+((((-4)*X+(8))*X+(-3))*X)))
compact_certificate theorem row2_23_identity (B A Y X : ℂ) :
  (((1)*A+(-2)))*row1_19 B A Y X+
  ((-1))*row1_20 B A Y X+
  (((1)*Y))*row1_11 B A Y X=((1))*row2_23 B A Y X := by
  simp only [row1_19, row1_20, row1_11, row2_23] <;> ring
compact_certificate theorem row2_23_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_23 B A Y X=0 := by
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_11 := row1_11_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_23_identity B A Y X).symm
  have hz : ((1))*row2_23 B A Y X=0 := by
    simpa only [z1_19, z1_20, z1_11,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_23_zero

compact_certificate def row2_24 (B A Y X : ℂ) : ℂ := ((((((1)*Y+(1))*Y+(1))*Y)*A+((((((1)*X^2+(-1))*X)*Y+(((1)*X+(-1))*X))*Y+(((1)*X+(-1))*X))*Y+(((-1)*X+(1))*X^2)))*A+((((((-1)*X)*Y+(((-1)*X+(-1))*X))*Y+(((2)*X+(-4))*X^2))*Y+((((2)*X+(-4))*X+(1))*X))*Y+((((2)*X+(-3))*X+(1))*X)))
compact_certificate theorem row2_24_identity (B A Y X : ℂ) :
  ((1))*row1_19 B A Y X+
  (((1)*Y))*row1_12 B A Y X=((1))*row2_24 B A Y X := by
  simp only [row1_19, row1_12, row2_24] <;> ring
compact_certificate theorem row2_24_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_24 B A Y X=0 := by
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_12 := row1_12_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_24_identity B A Y X).symm
  have hz : ((1))*row2_24 B A Y X=0 := by
    simpa only [z1_19, z1_12,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_24_zero
compact_certificate def row2_27 (B A Y X : ℂ) : ℂ := ((((((1)*X)*Y+((1)*X+(-1)))*Y)*A+(((((1)*X^2+(-1))*X^2)*Y+(((-1)*X+(1))*X))*Y+((((-1)*X+(2))*X+(-1))*X^2)))*A+(((((-1)*X^2)*Y+((((-1)*X+(-1))*X+(1))*X))*Y+((((2)*X+(-4))*X+(2))*X^2))*Y+(((((2)*X+(-5))*X+(4))*X+(-1))*X)))
compact_certificate theorem row2_27_identity (B A Y X : ℂ) :
  ((-1))*row1_19 B A Y X+
  (((1)*X))*row1_12 B A Y X=((1))*row2_27 B A Y X := by
  simp only [row1_19, row1_12, row2_27] <;> ring
compact_certificate theorem row2_27_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_27 B A Y X=0 := by
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_12 := row1_12_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_27_identity B A Y X).symm
  have hz : ((1))*row2_27 B A Y X=0 := by
    simpa only [z1_19, z1_12,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_27_zero
compact_certificate def row2_28 (B A Y X : ℂ) : ℂ := (((((1)*X^2+(1))*Y)*A+((((1)*X^4+(-1))*X)*Y+(((((-1)*X+(1))*X+(-1))*X+(1))*X^2)))*A+(((((-1)*X^2+(-1))*X)*Y+(((-1)*X^2+(-1))*X^2))*Y+((((((2)*X+(-3))*X+(3))*X+(-3))*X+(1))*X)))
compact_certificate theorem row2_28_identity (B A Y X : ℂ) :
  (((5732736)*Y+((1023504)*X+(27648))))*row1_19 B A Y X+
  (((16)*Y))*row1_3 B A Y X+
  (((3936)*Y))*row1_6 B A Y X+
  (((384)*Y+((29829)*X)))*row1_9 B A Y X+
  (((-252192)*Y+((-339456)*X)))*row1_11 B A Y X+
  (((-6144)*Y))*row1_12 B A Y X+
  (((-1)*X))*row1_2 B A Y X+
  (((768)*X))*row1_8 B A Y X+
  (((-91776)*X))*row1_10 B A Y X=((27648))*row2_28 B A Y X := by
  simp only [row1_19, row1_3, row1_6, row1_9, row1_11, row1_12, row1_2, row1_8, row1_10, row2_28] <;> ring
compact_certificate theorem row2_28_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_28 B A Y X=0 := by
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_3 := row1_3_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_6 := row1_6_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_9 := row1_9_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_11 := row1_11_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_12 := row1_12_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_2 := row1_2_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_8 := row1_8_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_10 := row1_10_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_28_identity B A Y X).symm
  have hz : ((27648))*row2_28 B A Y X=0 := by
    simpa only [z1_19, z1_3, z1_6, z1_9, z1_11, z1_12, z1_2, z1_8, z1_10,mul_zero,add_zero] using he
  have hu : ((27648):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_28_zero
compact_certificate def row2_29 (B A Y X : ℂ) : ℂ := ((((((1)*Y)*A+((1)*Y+((1)*X^2)))*A+(((-1)*X)*Y+(((-1)*X+(1))*X)))*A+(((-1)*X)*Y+(((-2)*X+(1))*X)))*B^2)
compact_certificate theorem row2_29_identity (B A Y X : ℂ) :
  (((1)*B))*row1_14 B A Y X=((1))*row2_29 B A Y X := by
  simp only [row1_14, row2_29] <;> ring
compact_certificate theorem row2_29_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_29 B A Y X=0 := by
  have z1_14 := row1_14_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_29_identity B A Y X).symm
  have hz : ((1))*row2_29 B A Y X=0 := by
    simpa only [z1_14,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_29_zero
compact_certificate def row2_30 (B A Y X : ℂ) : ℂ := (((((((24)*Y)*A+((24)*X^2))*A+((-24)*Y+(((-48)*X+(24))*X)))*A+(((24)*X+(-24))*X^2))*A+(((((-90)*X+(336))*X+(24))*X)*Y+((((-48)*X+(72))*X+(-24))*X)))*B+((((((-270)*X+(-444))*X+(303))*Y+((540)*X^3))*A+((((-160)*X)*Y+(((780)*X+(-1815))*X))*Y+(((-699)*X+(843))*X^2)))*A+((((-455)*X)*Y+(((-171)*X+(4632))*X))*Y+((((-762)*X+(-225))*X+(303))*X))))
compact_certificate theorem row2_30_identity (B A Y X : ℂ) :
  ((1))*row1_17 B A Y X+
  (((-24)*B))*row1_20 B A Y X+
  (((24)*A))*row1_14 B A Y X=((1))*row2_30 B A Y X := by
  simp only [row1_17, row1_20, row1_14, row2_30] <;> ring
compact_certificate theorem row2_30_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_30 B A Y X=0 := by
  have z1_17 := row1_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_14 := row1_14_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_30_identity B A Y X).symm
  have hz : ((1))*row2_30 B A Y X=0 := by
    simpa only [z1_17, z1_20, z1_14,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_30_zero
compact_certificate def row2_31 (B A Y X : ℂ) : ℂ := (((((((1)*Y)*A+((1)*X^2))*A+(((-2)*X+(1))*X))*A+(((1)*X+(1))*Y+((1)*X^3)))*A+(((-1)*X^2)*Y+(((-1)*X+(2))*X^2)))*A+((((-1)*X+(-1))*X)*Y+((((-2)*X+(-1))*X+(1))*X)))
compact_certificate theorem row2_31_identity (B A Y X : ℂ) :
  (((1)*X+(1)))*row1_20 B A Y X+
  (((1)*A))*row1_15 B A Y X=((1))*row2_31 B A Y X := by
  simp only [row1_20, row1_15, row2_31] <;> ring
compact_certificate theorem row2_31_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_31 B A Y X=0 := by
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_15 := row1_15_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_31_identity B A Y X).symm
  have hz : ((1))*row2_31 B A Y X=0 := by
    simpa only [z1_20, z1_15,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_31_zero
compact_certificate def row2_33 (B A Y X : ℂ) : ℂ := (((((540)*Y^2)*A^2+((((-636)*X+(-536))*Y+(((-3144)*X+(445))*X+(166)))*Y+((-350)*X^3)))*A+(((((-160)*X+(-1250))*X)*Y+(((-2781)*X+(-166))*X))*Y+((((-159)*X+(439))*X+(-184))*X^2)))*A+(((((60)*X)*Y+(((-299)*X+(-40))*X))*Y+((((-679)*X+(720))*X+(-186))*X))*Y+(((((318)*X+(363))*X+(-593))*X+(166))*X)))
compact_certificate theorem row2_33_identity (B A Y X : ℂ) :
  (((246)*A+(-444)))*row1_9 B A Y X+
  (((219420)*A+(-264624)))*row1_19 B A Y X+
  (((11232)*Y+((-47385)*X+(-31524))))*row1_20 B A Y X+
  (((2)*A))*row1_7 B A Y X+
  (((-135)*A))*row1_8 B A Y X+
  (((-768)*A+((-2880)*Y+((12150)*X))))*row1_10 B A Y X+
  (((-39522)*A))*row1_11 B A Y X+
  (((-32)*Y+((135)*X)))*row1_6 B A Y X+
  (((119880)*Y))*row1_15 B A Y X+
  (((222)*X))*row1_17 B A Y X=((222))*row2_33 B A Y X := by
  simp only [row1_9, row1_19, row1_20, row1_7, row1_8, row1_10, row1_11, row1_6, row1_15, row1_17, row2_33] <;> ring
compact_certificate theorem row2_33_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_33 B A Y X=0 := by
  have z1_9 := row1_9_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_7 := row1_7_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_8 := row1_8_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_10 := row1_10_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_11 := row1_11_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_6 := row1_6_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_15 := row1_15_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_17 := row1_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_33_identity B A Y X).symm
  have hz : ((222))*row2_33 B A Y X=0 := by
    simpa only [z1_9, z1_19, z1_20, z1_7, z1_8, z1_10, z1_11, z1_6, z1_15, z1_17,mul_zero,add_zero] using he
  have hu : ((222):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_33_zero
compact_certificate def row2_35 (B A Y X : ℂ) : ℂ := (((((((48)*X)*Y)*A+((48)*X^3))*A+((((-180)*X+(672))*X^2)*Y+(((-96)*X+(48))*X^2)))*B+((((606)*Y+((1080)*X^3))*A+((((-320)*X)*Y+(((1560)*X+(-3630))*X))*Y+((((540)*X+(-510))*X+(1686))*X^2)))*A+((((-910)*X)*Y+(((((-2025)*X+(4230))*X+(12090))*X+(9264))*X))*Y+(((((-1080)*X+(-2760))*X+(438))*X+(606))*X))))*B+((((((2160)*X+(-90))*Y+(((14310)*X+(-13548))*X+(-28299)))*Y+((21780)*X^3))*A+((((16130)*X)*Y+(((32370)*X+(-27645))*X))*Y+(((12927)*X+(-6519))*X^2)))*A+(((((-1350)*X)*Y+(((-3510)*X+(25915))*X))*Y+((((23580)*X+(135693))*X+(169494))*X))*Y+((((-112974)*X+(113085))*X+(-28299))*X))))
compact_certificate theorem row2_35_identity (B A Y X : ℂ) :
  (((-1845)*A+(3330)))*row1_9 B A Y X+
  (((148)*B+(2738)))*row1_17 B A Y X+
  (((140400)*A+(-213120)))*row1_19 B A Y X+
  (((-84240)*Y+(-213120)))*row1_20 B A Y X+
  (((-15)*A))*row1_7 B A Y X+
  (((5760)*A+((21600)*Y)))*row1_10 B A Y X+
  (((23040)*A))*row1_11 B A Y X+
  (((240)*Y))*row1_6 B A Y X=((74))*row2_35 B A Y X := by
  simp only [row1_9, row1_17, row1_19, row1_20, row1_7, row1_10, row1_11, row1_6, row2_35] <;> ring
compact_certificate theorem row2_35_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_35 B A Y X=0 := by
  have z1_9 := row1_9_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_17 := row1_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_7 := row1_7_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_10 := row1_10_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_11 := row1_11_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_6 := row1_6_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_35_identity B A Y X).symm
  have hz : ((74))*row2_35 B A Y X=0 := by
    simpa only [z1_9, z1_17, z1_19, z1_20, z1_7, z1_10, z1_11, z1_6,mul_zero,add_zero] using he
  have hu : ((74):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_35_zero
compact_certificate def row2_36 (B A Y X : ℂ) : ℂ := (((((((24)*X)*Y)*A+((24)*X^3))*A+(((-24)*X^2)*Y+(((-48)*X+(24))*X^2)))*A+((((90)*X+(-360))*X^2)*Y))*B+((((((270)*X+(444))*X+(-303))*Y+((-540)*X^3))*A+((((160)*X)*Y+(((-780)*X+(1815))*X))*Y+(((699)*X+(-843))*X^2)))*A+((((455)*X)*Y+(((171)*X+(-4632))*X))*Y+((((762)*X+(225))*X+(-303))*X))))
compact_certificate theorem row2_36_identity (B A Y X : ℂ) :
  ((-1))*row1_17 B A Y X+
  (((24)*X))*row1_14 B A Y X=((1))*row2_36 B A Y X := by
  simp only [row1_17, row1_14, row2_36] <;> ring
compact_certificate theorem row2_36_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_36 B A Y X=0 := by
  have z1_17 := row1_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_14 := row1_14_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_36_identity B A Y X).symm
  have hz : ((1))*row2_36 B A Y X=0 := by
    simpa only [z1_17, z1_14,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_36_zero
compact_certificate def row2_37 (B A Y X : ℂ) : ℂ := (((((-180)*Y)*A+((((-720)*X+(180))*X)*Y+(((180)*X+(-180))*X^2)))*A+((((180)*X)*Y+(((180)*X+(-540))*X^2))*Y+((((-360)*X+(540))*X+(-180))*X)))*B+((((((1080)*X)*Y)*A^2+((((224)*X+(4))*Y+(((-4164)*X+(2455))*X+(166)))*Y+((-3080)*X^3)))*A+(((((-160)*X+(-20))*X)*Y+(((-2571)*X+(-6406))*X))*Y+((((-159)*X+(3169))*X+(-2914))*X^2)))*A+(((((60)*X)*Y+(((-299)*X+(330))*X))*Y+((((-679)*X+(1950))*X+(-9516))*X))*Y+(((((318)*X+(5823))*X+(-3323))*X+(166))*X))))
compact_certificate theorem row2_37_identity (B A Y X : ℂ) :
  (((246)*A+(-444)))*row1_9 B A Y X+
  (((-444)*A+((222)*X+(-444))))*row1_17 B A Y X+
  (((-39960)*B+((219420)*A+(-264624))))*row1_19 B A Y X+
  (((11232)*Y+((-244521)*X+(103008))))*row1_20 B A Y X+
  (((2)*A))*row1_7 B A Y X+
  (((-135)*A))*row1_8 B A Y X+
  (((-768)*A+((-2880)*Y+((12150)*X))))*row1_10 B A Y X+
  (((-39522)*A))*row1_11 B A Y X+
  (((-32)*Y+((135)*X)))*row1_6 B A Y X+
  (((10656)*X))*row1_14 B A Y X+
  (((239760)*X))*row1_15 B A Y X=((222))*row2_37 B A Y X := by
  simp only [row1_9, row1_17, row1_19, row1_20, row1_7, row1_8, row1_10, row1_11, row1_6, row1_14, row1_15, row2_37] <;> ring
compact_certificate theorem row2_37_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_37 B A Y X=0 := by
  have z1_9 := row1_9_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_17 := row1_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_7 := row1_7_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_8 := row1_8_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_10 := row1_10_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_11 := row1_11_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_6 := row1_6_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_14 := row1_14_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_15 := row1_15_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_37_identity B A Y X).symm
  have hz : ((222))*row2_37 B A Y X=0 := by
    simpa only [z1_9, z1_17, z1_19, z1_20, z1_7, z1_8, z1_10, z1_11, z1_6, z1_14, z1_15,mul_zero,add_zero] using he
  have hu : ((222):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_37_zero
compact_certificate def row2_39 (B A Y X : ℂ) : ℂ := ((((((1)*X)*Y^2)*A+((((1)*X)*Y+((1)*X+(2)))*Y+((1)*X^3)))*A+(((((-1)*X+(1))*X)*Y+(((2)*X+(-2))*X))*Y+(((-3)*X+(3))*X^2)))*A+(((((-1)*X+(-1))*X)*Y+(((-2)*X^2+(-1))*X))*Y+((((2)*X+(-5))*X+(2))*X)))
compact_certificate theorem row2_39_identity (B A Y X : ℂ) :
  (((-9360)*A+(14208)))*row1_19 B A Y X+
  (((5616)*Y+(14208)))*row1_20 B A Y X+
  (((1)*A))*row1_7 B A Y X+
  (((123)*A))*row1_9 B A Y X+
  (((-384)*A+((-1440)*Y)))*row1_10 B A Y X+
  (((-1536)*A))*row1_11 B A Y X+
  (((-16)*Y))*row1_6 B A Y X=((14208))*row2_39 B A Y X := by
  simp only [row1_19, row1_20, row1_7, row1_9, row1_10, row1_11, row1_6, row2_39] <;> ring
compact_certificate theorem row2_39_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_39 B A Y X=0 := by
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_7 := row1_7_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_9 := row1_9_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_10 := row1_10_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_11 := row1_11_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_6 := row1_6_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_39_identity B A Y X).symm
  have hz : ((14208))*row2_39 B A Y X=0 := by
    simpa only [z1_19, z1_20, z1_7, z1_9, z1_10, z1_11, z1_6,mul_zero,add_zero] using he
  have hu : ((14208):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_39_zero
compact_certificate def row2_40 (B A Y X : ℂ) : ℂ := ((((((12)*X^2)*Y)*A+((12)*X^4))*A+((((-45)*X+(168))*X^3)*Y+(((-24)*X+(12))*X^3)))*B+((((((48)*X+(-2))*Y+(((540)*X+(64))*X+(-878)))*Y+((40)*X^3))*A+((((490)*X)*Y+(((78)*X+(878))*X))*Y+(((862)*X+(-838))*X^2)))*A+(((((-30)*X)*Y+(((-78)*X+(950))*X))*Y+((((524)*X+(3156))*X+(-42))*X))*Y+((((-1884)*X+(2698))*X+(-878))*X))))
compact_certificate theorem row2_40_identity (B A Y X : ℂ) :
  (((-123)*A+(222)))*row1_9 B A Y X+
  (((9360)*A+(-14208)))*row1_19 B A Y X+
  (((-5616)*Y+(-14208)))*row1_20 B A Y X+
  (((-1)*A))*row1_7 B A Y X+
  (((384)*A+((1440)*Y)))*row1_10 B A Y X+
  (((1536)*A))*row1_11 B A Y X+
  (((16)*Y))*row1_6 B A Y X=((222))*row2_40 B A Y X := by
  simp only [row1_9, row1_19, row1_20, row1_7, row1_10, row1_11, row1_6, row2_40] <;> ring
compact_certificate theorem row2_40_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_40 B A Y X=0 := by
  have z1_9 := row1_9_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_7 := row1_7_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_10 := row1_10_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_11 := row1_11_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_6 := row1_6_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_40_identity B A Y X).symm
  have hz : ((222))*row2_40 B A Y X=0 := by
    simpa only [z1_9, z1_19, z1_20, z1_7, z1_10, z1_11, z1_6,mul_zero,add_zero] using he
  have hu : ((222):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_40_zero

compact_certificate def row2_41 (B A Y X : ℂ) : ℂ := ((((((540)*X^2)*Y)*A+((((96)*X+(-4))*Y+(((2064)*X+(95))*X+(-166)))*Y+((350)*X^3)))*A+(((((160)*X+(1250))*X)*Y+(((2241)*X+(166))*X))*Y+((((159)*X+(-439))*X+(184))*X^2)))*A+(((((-60)*X)*Y+(((299)*X+(580))*X))*Y+((((679)*X+(360))*X+(-354))*X))*Y+(((((-318)*X+(-363))*X+(593))*X+(-166))*X)))
compact_certificate theorem row2_41_identity (B A Y X : ℂ) :
  (((-246)*A+(444)))*row1_9 B A Y X+
  (((-219420)*A+(264624)))*row1_19 B A Y X+
  (((-11232)*Y+((47385)*X+(31524))))*row1_20 B A Y X+
  (((-2)*A))*row1_7 B A Y X+
  (((135)*A))*row1_8 B A Y X+
  (((768)*A+((2880)*Y+((-12150)*X))))*row1_10 B A Y X+
  (((39522)*A))*row1_11 B A Y X+
  (((32)*Y+((-135)*X)))*row1_6 B A Y X+
  (((-222)*X))*row1_17 B A Y X=((222))*row2_41 B A Y X := by
  simp only [row1_9, row1_19, row1_20, row1_7, row1_8, row1_10, row1_11, row1_6, row1_17, row2_41] <;> ring
compact_certificate theorem row2_41_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_41 B A Y X=0 := by
  have z1_9 := row1_9_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_7 := row1_7_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_8 := row1_8_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_10 := row1_10_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_11 := row1_11_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_6 := row1_6_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_17 := row1_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_41_identity B A Y X).symm
  have hz : ((222))*row2_41 B A Y X=0 := by
    simpa only [z1_9, z1_19, z1_20, z1_7, z1_8, z1_10, z1_11, z1_6, z1_17,mul_zero,add_zero] using he
  have hu : ((222):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_41_zero
compact_certificate def row2_42 (B A Y X : ℂ) : ℂ := (((((180)*Y)*A+((((720)*X+(-180))*X)*Y+(((-180)*X+(180))*X^2)))*A+((((-180)*X)*Y+(((-180)*X+(540))*X^2))*Y+((((360)*X+(-540))*X+(180))*X)))*B+(((((1080)*X^3)*A+((((-224)*X+(-4))*Y+(((3084)*X+(-3535))*X+(-166)))*Y+(((920)*X+(1080))*X^2)))*A+(((((160)*X+(20))*X)*Y+(((2571)*X+(6406))*X))*Y+((((159)*X+(-4249))*X+(2914))*X^2)))*A+(((((-60)*X)*Y+(((299)*X+(-330))*X))*Y+((((679)*X+(-870))*X+(9516))*X))*Y+(((((-318)*X+(-3663))*X+(2243))*X+(-166))*X))))
compact_certificate theorem row2_42_identity (B A Y X : ℂ) :
  (((-246)*A+(444)))*row1_9 B A Y X+
  (((444)*A+((-222)*X+(444))))*row1_17 B A Y X+
  (((39960)*B+((-219420)*A+(264624))))*row1_19 B A Y X+
  (((-11232)*Y+((244521)*X+(-103008))))*row1_20 B A Y X+
  (((-2)*A))*row1_7 B A Y X+
  (((135)*A))*row1_8 B A Y X+
  (((768)*A+((2880)*Y+((-12150)*X))))*row1_10 B A Y X+
  (((39522)*A))*row1_11 B A Y X+
  (((32)*Y+((-135)*X)))*row1_6 B A Y X+
  (((-10656)*X))*row1_14 B A Y X=((222))*row2_42 B A Y X := by
  simp only [row1_9, row1_17, row1_19, row1_20, row1_7, row1_8, row1_10, row1_11, row1_6, row1_14, row2_42] <;> ring
compact_certificate theorem row2_42_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_42 B A Y X=0 := by
  have z1_9 := row1_9_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_17 := row1_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_7 := row1_7_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_8 := row1_8_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_10 := row1_10_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_11 := row1_11_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_6 := row1_6_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_14 := row1_14_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_42_identity B A Y X).symm
  have hz : ((222))*row2_42 B A Y X=0 := by
    simpa only [z1_9, z1_17, z1_19, z1_20, z1_7, z1_8, z1_10, z1_11, z1_6, z1_14,mul_zero,add_zero] using he
  have hu : ((222):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_42_zero
compact_certificate def row2_43 (B A Y X : ℂ) : ℂ := (((((1)*Y)*A+((((1)*X^2+(-1))*X)*Y+(((-1)*X+(1))*X^2)))*A+((((-1)*X)*Y+((-1)*X^2))*Y+((((2)*X+(-3))*X+(1))*X)))*B)
compact_certificate theorem row2_43_identity (B A Y X : ℂ) :
  (((1)*B))*row1_19 B A Y X=((1))*row2_43 B A Y X := by
  simp only [row1_19, row2_43] <;> ring
compact_certificate theorem row2_43_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_43 B A Y X=0 := by
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_43_identity B A Y X).symm
  have hz : ((1))*row2_43 B A Y X=0 := by
    simpa only [z1_19,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_43_zero
compact_certificate def row2_44 (B A Y X : ℂ) : ℂ := ((((((1)*X^2+(-1))*X+(-1))*Y+((-1)*X^3))*A+((((-1)*X)*Y+(((-1)*X+(1))*X))*Y+(((2)*X+(-2))*X^2)))*A+(((1)*X)*Y+(((2)*X+(-1))*X)))
compact_certificate theorem row2_44_identity (B A Y X : ℂ) :
  ((-1))*row1_20 B A Y X+
  (((1)*A))*row1_19 B A Y X=((1))*row2_44 B A Y X := by
  simp only [row1_20, row1_19, row2_44] <;> ring
compact_certificate theorem row2_44_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_44 B A Y X=0 := by
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_44_identity B A Y X).symm
  have hz : ((1))*row2_44 B A Y X=0 := by
    simpa only [z1_20, z1_19,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_44_zero
compact_certificate def row2_45 (B A Y X : ℂ) : ℂ := (((((1)*Y+(1))*Y)*A+(((((1)*X^2+(-1))*X)*Y+(((1)*X+(-1))*X))*Y+(((-1)*X+(1))*X^2)))*A+(((((-1)*X)*Y+(((-1)*X+(-1))*X))*Y+((((2)*X+(-4))*X+(1))*X))*Y+((((2)*X+(-3))*X+(1))*X)))
compact_certificate theorem row2_45_identity (B A Y X : ℂ) :
  (((1)*Y+(1)))*row1_19 B A Y X=((1))*row2_45 B A Y X := by
  simp only [row1_19, row2_45] <;> ring
compact_certificate theorem row2_45_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_45 B A Y X=0 := by
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_45_identity B A Y X).symm
  have hz : ((1))*row2_45 B A Y X=0 := by
    simpa only [z1_19,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_45_zero
compact_certificate def row2_46 (B A Y X : ℂ) : ℂ := ((((((-96)*X+(4))*Y+(((-1524)*X+(-95))*X+(706)))*Y+(((540)*X+(-350))*X^3))*A+(((((-160)*X+(-1250))*X)*Y+(((-2241)*X+(-706))*X))*Y+((((-699)*X+(439))*X+(356))*X^2)))*A+(((((60)*X)*Y+(((-299)*X+(-1120))*X))*Y+((((-1219)*X+(-900))*X+(354))*X))*Y+(((((-762)*X+(1983))*X+(-2213))*X+(706))*X)))
compact_certificate theorem row2_46_identity (B A Y X : ℂ) :
  (((123)*A+(-222)))*row1_9 B A Y X+
  (((20610)*A+(-72372)))*row1_19 B A Y X+
  (((5616)*Y+(-15762)))*row1_20 B A Y X+
  (((1)*A))*row1_7 B A Y X+
  (((-384)*A+((-1440)*Y)))*row1_10 B A Y X+
  (((-1536)*A))*row1_11 B A Y X+
  (((-16)*Y))*row1_6 B A Y X+
  (((111)*X))*row1_17 B A Y X=((111))*row2_46 B A Y X := by
  simp only [row1_9, row1_19, row1_20, row1_7, row1_10, row1_11, row1_6, row1_17, row2_46] <;> ring
compact_certificate theorem row2_46_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_46 B A Y X=0 := by
  have z1_9 := row1_9_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_7 := row1_7_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_10 := row1_10_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_11 := row1_11_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_6 := row1_6_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z1_17 := row1_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_46_identity B A Y X).symm
  have hz : ((111))*row2_46 B A Y X=0 := by
    simpa only [z1_9, z1_19, z1_20, z1_7, z1_10, z1_11, z1_6, z1_17,mul_zero,add_zero] using he
  have hu : ((111):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_46_zero
compact_certificate def row2_48 (B A Y X : ℂ) : ℂ := ((((((1)*Y)*A+((1)*Y+((1)*X^2)))*A+(((-1)*X)*Y+(((-1)*X+(1))*X)))*A+(((-1)*X)*Y+(((-2)*X+(1))*X)))*B)
compact_certificate theorem row2_48_identity (B A Y X : ℂ) :
  (((1)*B))*row1_20 B A Y X=((1))*row2_48 B A Y X := by
  simp only [row1_20, row2_48] <;> ring
compact_certificate theorem row2_48_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_48 B A Y X=0 := by
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_48_identity B A Y X).symm
  have hz : ((1))*row2_48 B A Y X=0 := by
    simpa only [z1_20,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_48_zero
compact_certificate def row2_49 (B A Y X : ℂ) : ℂ := ((((((1)*Y)*A+((1)*X^2))*A+(((-1)*X+(-1))*Y+(((-2)*X+(1))*X)))*A+((-1)*X^2))*A+(((1)*X)*Y+(((2)*X+(-1))*X)))
compact_certificate theorem row2_49_identity (B A Y X : ℂ) :
  (((1)*A+(-1)))*row1_20 B A Y X=((1))*row2_49 B A Y X := by
  simp only [row1_20, row2_49] <;> ring
compact_certificate theorem row2_49_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_49 B A Y X=0 := by
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_49_identity B A Y X).symm
  have hz : ((1))*row2_49 B A Y X=0 := by
    simpa only [z1_20,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_49_zero
compact_certificate def row2_51 (B A Y X : ℂ) : ℂ := ((((((24)*X)*Y)*A+((24)*X^3))*A+((((-90)*X+(336))*X^2)*Y+(((-48)*X+(24))*X^2)))*B+((((((-270)*X+(-444))*X+(303))*Y+((540)*X^3))*A+((((-160)*X)*Y+(((780)*X+(-1815))*X))*Y+(((-699)*X+(843))*X^2)))*A+((((-455)*X)*Y+(((-171)*X+(4632))*X))*Y+((((-762)*X+(-225))*X+(303))*X))))
compact_certificate theorem row2_51_identity (B A Y X : ℂ) :
  ((1))*row1_17 B A Y X=((1))*row2_51 B A Y X := by
  simp only [row1_17, row2_51] <;> ring
compact_certificate theorem row2_51_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_51 B A Y X=0 := by
  have z1_17 := row1_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_51_identity B A Y X).symm
  have hz : ((1))*row2_51 B A Y X=0 := by
    simpa only [z1_17,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_51_zero
compact_certificate def row2_53 (B A Y X : ℂ) : ℂ := ((((1)*Y)*A+((((1)*X^2+(-1))*X)*Y+(((-1)*X+(1))*X^2)))*A+((((-1)*X)*Y+((-1)*X^2))*Y+((((2)*X+(-3))*X+(1))*X)))
compact_certificate theorem row2_53_identity (B A Y X : ℂ) :
  ((1))*row1_19 B A Y X=((1))*row2_53 B A Y X := by
  simp only [row1_19, row2_53] <;> ring
compact_certificate theorem row2_53_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_53 B A Y X=0 := by
  have z1_19 := row1_19_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_53_identity B A Y X).symm
  have hz : ((1))*row2_53 B A Y X=0 := by
    simpa only [z1_19,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_53_zero
compact_certificate def row2_54 (B A Y X : ℂ) : ℂ := (((((1)*Y)*A+((1)*Y+((1)*X^2)))*A+(((-1)*X)*Y+(((-1)*X+(1))*X)))*A+(((-1)*X)*Y+(((-2)*X+(1))*X)))
compact_certificate theorem row2_54_identity (B A Y X : ℂ) :
  ((1))*row1_20 B A Y X=((1))*row2_54 B A Y X := by
  simp only [row1_20, row2_54] <;> ring
compact_certificate theorem row2_54_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row2_54 B A Y X=0 := by
  have z1_20 := row1_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row2_54_identity B A Y X).symm
  have hz : ((1))*row2_54 B A Y X=0 := by
    simpa only [z1_20,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_54_zero
compact_certificate def row3_22 (B A Y X : ℂ) : ℂ := ((((((4175712)*Y+((12597120)*X^4+(433033290)))*Y+((-8164800)*X^3))*A+((((-33242400)*X)*Y+(((-422697528)*X+(-433033290))*X))*Y+(((-416703690)*X+(424868490))*X^2)))*A+(((((-2682720)*X)*Y+((((-12480480)*X+(-20412000))*X+(-442691082))*X))*Y+((((110917350)*X+(-1356163074))*X+(12340512))*X))*Y+((((866066580)*X+(-1299099870))*X+(433033290))*X)))*B+((((((-302400)*Y+((-921229176)*X+(-462498832)))*Y+(((9333369561)*X+(941455259))*X+(-2213949709)))*Y+((-1719761695)*X^3))*A+((((((12096000)*X+(172046160))*X)*Y+(((2721317710)*X+(5972406905))*X))*Y+(((-1147218417)*X+(1518410809))*X))*Y+(((((185822505)*X+(879867501))*X+(2189960438))*X+(-3933711404))*X^2)))*A+((((((-4536000)*X)*Y+(((190078380)*X+(178402080))*X))*Y+((((904540365)*X+(1998086216))*X+(4290167746))*X))*Y+(((((826656705)*X+(2002276486))*X+(4243639608))*X+(-13618025877))*X))*Y+((((((-371645010)*X+(-1573912497))*X+(3378993405))*X+(3178336466))*X+(-2213949709))*X))))
compact_certificate theorem row3_22_identity (B A Y X : ℂ) :
  ((274995))*row2_17 B A Y X+
  (((233280)*B+((59722758)*A+((-529200)*Y+(27813080)))))*row2_46 B A Y X+
  (((-33917940)*A+((933120)*Y+((14813280)*X+(233108685)))))*row2_51 B A Y X+
  (((20945832120)*B+((25947009720)*A+((-1869912000)*Y+((-405972000)*X+(-20908080450))))))*row2_53 B A Y X+
  (((-80248320)*Y+((-38491083360)*X+(-78513843780))))*row2_54 B A Y X+
  (((1925959680)*A))*row2_39 B A Y X+
  (((39660678)*A+((42900948)*X)))*row2_41 B A Y X+
  (((-23411455920)*A+((285768000)*X)))*row2_44 B A Y X+
  (((226800)*Y+((-34261299)*X)))*row2_42 B A Y X+
  (((5248800)*X))*row2_20 B A Y X+
  (((-3566592)*X))*row2_33 B A Y X+
  (((-49499100)*X))*row2_36 B A Y X+
  (((519291)*X))*row2_37 B A Y X+
  (((814030560)*X))*row2_48 B A Y X=((10))*row3_22 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_39, row2_41, row2_44, row2_42, row2_20, row2_33, row2_36, row2_37, row2_48, row3_22] <;> ring
compact_certificate theorem row3_22_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_22 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_20 := row2_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_22_identity B A Y X).symm
  have hz : ((10))*row3_22 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_39, z2_41, z2_44, z2_42, z2_20, z2_33, z2_36, z2_37, z2_48,mul_zero,add_zero] using he
  have hu : ((10):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_22_zero

compact_certificate def row3_23 (B A Y X : ℂ) : ℂ := (((((-387450)*Y)*A+((((-1549800)*X+(387450))*X)*Y+(((387450)*X+(-387450))*X^2)))*A+((((387450)*X)*Y+(((387450)*X+(-1162350))*X^2))*Y+((((-774900)*X+(1162350))*X+(-387450))*X)))*B+((((((349920)*X^4)*Y)*A+((((2842632)*X+(-773968))*Y+(((5733363)*X+(11710085))*X+(-6575647)))*Y+((1924775)*X^3)))*A+(((((38880)*X)*Y+(((6265330)*X+(16950095))*X))*Y+(((19368657)*X+(-9180653))*X))*Y+(((((751275)*X+(-56217))*X+(3070982))*X+(-4650872))*X^2)))*A+((((((-283500)*X+(525360))*X)*Y+((((1412775)*X+(4583648))*X+(16584130))*X))*Y+(((((3208275)*X+(4575298))*X+(19227420))*X+(-29820243))*X))*Y+((((((-1502550)*X+(863709))*X+(-13897281))*X+(20071826))*X+(-6575647))*X))))
compact_certificate theorem row3_23_identity (B A Y X : ℂ) :
  (((6486)*A+(-76880)))*row2_46 B A Y X+
  (((-86100)*A+(-86100)))*row2_51 B A Y X+
  (((-7749000)*B+((-187041960)*A+((-15120000)*Y+(-206349660)))))*row2_53 B A Y X+
  (((-51840)*Y+((-88027200)*X+(155202300))))*row2_54 B A Y X+
  (((1244160)*A))*row2_39 B A Y X+
  (((-6474)*A+((92196)*X)))*row2_41 B A Y X+
  (((-49785840)*A))*row2_44 B A Y X+
  (((6480)*X))*row2_21 B A Y X+
  (((-2304)*X))*row2_33 B A Y X+
  (((3237)*X))*row2_37 B A Y X+
  (((-3243)*X))*row2_42 B A Y X+
  (((2066400)*X))*row2_48 B A Y X=((20))*row3_23 B A Y X := by
  simp only [row2_46, row2_51, row2_53, row2_54, row2_39, row2_41, row2_44, row2_21, row2_33, row2_37, row2_42, row2_48, row3_23] <;> ring
compact_certificate theorem row3_23_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_23 B A Y X=0 := by
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_21 := row2_21_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_23_identity B A Y X).symm
  have hz : ((20))*row3_23 B A Y X=0 := by
    simpa only [z2_46, z2_51, z2_53, z2_54, z2_39, z2_41, z2_44, z2_21, z2_33, z2_37, z2_42, z2_48,mul_zero,add_zero] using he
  have hu : ((20):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_23_zero
compact_certificate def row3_28 (B A Y X : ℂ) : ℂ := ((((((-8398080)*Y)*A+((((-33592320)*X+(8398080))*X)*Y+(((8398080)*X+(-8398080))*X^2)))*A+((((8398080)*X)*Y+(((8398080)*X+(-25194240))*X^2))*Y+((((-16796160)*X+(25194240))*X+(-8398080))*X)))*B+(((((2052864)*Y+(-16946997390))*Y+(((50388480)*X^2+(41057280))*X^3))*A+((((232346880)*X)*Y+(((30894769224)*X+(16605475470))*X))*Y+(((16618539150)*X+(-16905940110))*X^2)))*A+(((((933120)*X)*Y+((((-63452160)*X+(-375114240))*X+(17154896526))*X))*Y+(((((-1464415200)*X^2+(14004520110))*X+(49384587222))*X+(-626870016))*X))*Y+((((((-201553920)*X+(201553920))*X+(-33451695900))*X+(50594648490))*X+(-16946997390))*X))))*B+(((((201553920)*X^5)*A+((((-138240)*Y+((8197525128)*X+(24376667056)))*Y+(((-336145698003)*X+(-115910648057))*X+(56668169527)))*Y+((54692424805)*X^3)))*A+((((((5529600)*X+(-5485302720))*X)*Y+(((-153935488090)*X+(-305160439235))*X))*Y+(((-67023217989)*X+(243654368933))*X))*Y+(((((-15971284755)*X+(-4684784703))*X+(-62536164074))*X+(111360594332))*X^2)))*A+((((((-2073600)*X)*Y+((((100776960)*X+(-2824979220))*X+(-15145906800))*X))*Y+(((((201553920)*X+(-48061117935))*X+(-103520790728))*X+(-182129644798))*X))*Y+(((((-51248451195)*X+(38675655182))*X+(12691496736))*X+(532623276471))*X))*Y+((((((30330138150)*X+(-4183068309))*X+(-99591479295))*X+(-66286099598))*X+(56668169527))*X))))
compact_certificate theorem row3_28_identity (B A Y X : ℂ) :
  (((116640)*X+(-9169605)))*row2_17 B A Y X+
  (((466560)*B+((-2688059358)*A+((-241920)*Y+(-954977000)))))*row2_46 B A Y X+
  (((-933120)*B+((1686324420)*A+((-25349760)*Y+((-230480640)*X+(-7765103475))))))*row2_51 B A Y X+
  (((-731176239960)*B+((450423710280)*A+((167551070400)*Y+((-185587200)*X+(1211947011990))))))*row2_53 B A Y X+
  (((2130312960)*B+((3656430720)*Y+((1903549248000)*X+(1948776880500)))))*row2_54 B A Y X+
  (((-83980800)*B+((-3905107200)*A+((-944784000)*X))))*row2_43 B A Y X+
  (((-20995200)*A))*row2_20 B A Y X+
  (((8631360)*A))*row2_21 B A Y X+
  (((-466560)*A))*row2_35 B A Y X+
  (((-75670433280)*A))*row2_39 B A Y X+
  (((-1772085438)*A+((-2166768468)*X)))*row2_41 B A Y X+
  (((1169942998320)*A+((4367001600)*Y+((130636800)*X))))*row2_44 B A Y X+
  (((103680)*Y+((1490743359)*X)))*row2_42 B A Y X+
  (((22394880)*X))*row2_29 B A Y X+
  (((140130432)*X))*row2_33 B A Y X+
  (((1650528900)*X))*row2_36 B A Y X+
  (((207491949)*X))*row2_37 B A Y X+
  (((325425600)*X))*row2_40 B A Y X+
  (((-40471786080)*X))*row2_48 B A Y X=((10))*row3_28 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_43, row2_20, row2_21, row2_35, row2_39, row2_41, row2_44, row2_42, row2_29, row2_33, row2_36, row2_37, row2_40, row2_48, row3_28] <;> ring
compact_certificate theorem row3_28_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_28 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_43 := row2_43_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_20 := row2_20_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_21 := row2_21_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_35 := row2_35_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_29 := row2_29_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_40 := row2_40_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_28_identity B A Y X).symm
  have hz : ((10))*row3_28 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_43, z2_20, z2_21, z2_35, z2_39, z2_41, z2_44, z2_42, z2_29, z2_33, z2_36, z2_37, z2_40, z2_48,mul_zero,add_zero] using he
  have hu : ((10):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_28_zero
compact_certificate def row3_40 (B A Y X : ℂ) : ℂ := (((((-2970)*Y)*A+((((-11880)*X+(2970))*X)*Y+(((2970)*X+(-2970))*X^2)))*A+((((2970)*X)*Y+(((2970)*X+(-8910))*X^2))*Y+((((-5940)*X+(8910))*X+(-2970))*X)))*B+(((((17496)*Y^2)*A^3+((((33300)*X+(7936))*Y+(((338820)*X+(123649))*X+(-36074)))*Y+((104143)*X^3)))*A+(((((1944)*X)*Y+(((68822)*X+(389335))*X))*Y+(((639909)*X+(-84706))*X))*Y+(((((8586)*X+(31764))*X+(-135683))*X+(68069))*X^2)))*A+((((((-3240)*X+(-3216))*X)*Y+((((16146)*X+(78436))*X+(213053))*X))*Y+(((((36666)*X+(108866))*X+(228483))*X+(-321603))*X))*Y+((((((-17172)*X+(-54942))*X+(-113442))*X+(144751))*X+(-36074))*X))))
compact_certificate theorem row3_40_identity (B A Y X : ℂ) :
  (((17214)*A+(-19760)))*row2_46 B A Y X+
  (((-3300)*A+(-3300)))*row2_51 B A Y X+
  (((-297000)*B+((-22812840)*A+((-864000)*Y+(590760)))))*row2_53 B A Y X+
  (((-12960)*Y+((-5823000)*X+(10752300))))*row2_54 B A Y X+
  (((311040)*A))*row2_39 B A Y X+
  (((13974)*A+((4824)*X)))*row2_41 B A Y X+
  (((-2604960)*A))*row2_44 B A Y X+
  (((1749600)*Y))*row2_31 B A Y X+
  (((-576)*X))*row2_33 B A Y X+
  (((-8607)*X))*row2_37 B A Y X+
  (((-8607)*X))*row2_42 B A Y X+
  (((79200)*X))*row2_48 B A Y X=((100))*row3_40 B A Y X := by
  simp only [row2_46, row2_51, row2_53, row2_54, row2_39, row2_41, row2_44, row2_31, row2_33, row2_37, row2_42, row2_48, row3_40] <;> ring
compact_certificate theorem row3_40_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_40 B A Y X=0 := by
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_31 := row2_31_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_40_identity B A Y X).symm
  have hz : ((100))*row3_40 B A Y X=0 := by
    simpa only [z2_46, z2_51, z2_53, z2_54, z2_39, z2_41, z2_44, z2_31, z2_33, z2_37, z2_42, z2_48,mul_zero,add_zero] using he
  have hu : ((100):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_40_zero
compact_certificate def row3_45 (B A Y X : ℂ) : ℂ := ((((((-1049760)*Y)*A+((((-4199040)*X+(1049760))*X)*Y+(((1049760)*X+(-1049760))*X^2)))*A+((((1049760)*X)*Y+(((1049760)*X+(-3149280))*X^2))*Y+((((-2099520)*X+(3149280))*X+(-1049760))*X)))*B+((((((6298560)*X)*Y)*A^2+(((256608)*Y+(180182070))*Y+((-17962560)*X^3)))*A+((((-349920)*X)*Y+(((-326792232)*X+(-216573750))*X))*Y+(((-175049910)*X+(162219510))*X^2)))*A+(((((116640)*X)*Y+((((4665600)*X+(-42690240))*X+(-177289398))*X))*Y+((((164926530)*X+(-985968126))*X+(-55264032))*X))*Y+((((421950060)*X+(-571339170))*X+(180182070))*X))))*B+((((((-17280)*Y+((-136008984)*X+(-298123648)))*Y+(((4968102999)*X+(1671507821))*X+(-2017782511)))*Y+((-1192814185)*X^3))*A+((((((691200)*X+(73226160))*X)*Y+(((1685228050)*X+(4253025695))*X))*Y+(((-253808343)*X+(1456434691))*X))*Y+(((((150920415)*X+(389257179))*X+(2187262142))*X+(-3210596696))*X^2)))*A+((((((-259200)*X)*Y+(((58764420)*X+(159921840))*X))*Y+((((517220235)*X+(1286732744))*X+(3276882754))*X))*Y+(((((646388775)*X+(1381590394))*X+(3794940972))*X+(-12276011523))*X))*Y+((((((-301840830)*X+(-627593943))*X+(785989635))*X+(3837198794))*X+(-2017782511))*X))))
compact_certificate theorem row3_45_identity (B A Y X : ℂ) :
  ((132435))*row2_17 B A Y X+
  (((58320)*B+((26315172)*A+((-30240)*Y+(11553800)))))*row2_46 B A Y X+
  (((-116640)*B+((-17780040)*A+((-544320)*Y+((6181920)*X+(101434545))))))*row2_51 B A Y X+
  (((9841830480)*B+((5329720080)*A+((-1518696000)*Y+((-23198400)*X+(-20625933150))))))*row2_53 B A Y X+
  (((35341920)*B+((-40474080)*Y+((-21801499920)*X+(-32189828760)))))*row2_54 B A Y X+
  (((-10497600)*B+((-118098000)*X)))*row2_43 B A Y X+
  (((-58320)*A))*row2_35 B A Y X+
  (((971377920)*A))*row2_39 B A Y X+
  (((17508852)*A+((24015312)*X)))*row2_41 B A Y X+
  (((-12982265280)*A+((16329600)*X)))*row2_44 B A Y X+
  (((12960)*Y+((-15276546)*X)))*row2_42 B A Y X+
  (((2799360)*X))*row2_29 B A Y X+
  (((2624400)*X))*row2_30 B A Y X+
  (((-1798848)*X))*row2_33 B A Y X+
  (((-23838300)*X))*row2_36 B A Y X+
  (((1045764)*X))*row2_37 B A Y X+
  (((426720960)*X))*row2_48 B A Y X=((10))*row3_45 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_43, row2_35, row2_39, row2_41, row2_44, row2_42, row2_29, row2_30, row2_33, row2_36, row2_37, row2_48, row3_45] <;> ring
compact_certificate theorem row3_45_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_45 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_43 := row2_43_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_35 := row2_35_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_29 := row2_29_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_30 := row2_30_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_45_identity B A Y X).symm
  have hz : ((10))*row3_45 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_43, z2_35, z2_39, z2_41, z2_44, z2_42, z2_29, z2_30, z2_33, z2_36, z2_37, z2_48,mul_zero,add_zero] using he
  have hu : ((10):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_45_zero
compact_certificate def row3_46 (B A Y X : ℂ) : ℂ := (((((3199230)*Y+((116640)*X^3))*A+((((116640)*X)*Y+(((-7148520)*X+(-3199230))*X))*Y+(((-3432510)*X+(3315870))*X^2)))*A+(((((-466560)*X+(-3082590))*X)*Y+((((2836890)*X+(-17579430))*X+(-116640))*X))*Y+((((6398460)*X+(-9597690))*X+(3199230))*X)))*B+((((((699840)*X)*Y)*A^3+((((1060632)*X+(-6365128))*Y+(((108577443)*X+(33829835))*X+(-44210407)))*Y+((-14121865)*X^3)))*A+(((((1205280)*X)*Y+(((41628850)*X+(103368455))*X))*Y+(((35689347)*X+(8411467))*X))*Y+(((((3842235)*X+(8206593))*X+(36482132))*X+(-58332272))*X^2)))*A+((((((766260)*X+(3049320))*X)*Y+((((11657655)*X+(31276658))*X+(85653370))*X))*Y+(((((16408035)*X+(33556828))*X+(96307020))*X+(-232155003))*X))*Y+((((((-7684470)*X+(-12570951))*X+(-8270211))*X+(96659216))*X+(-44210407))*X))))
compact_certificate theorem row3_46_identity (B A Y X : ℂ) :
  ((2565))*row2_17 B A Y X+
  (((576678)*A+(151100)))*row2_46 B A Y X+
  (((-406740)*A+((194400)*X+(2005035))))*row2_51 B A Y X+
  (((187342200)*B+((-22864680)*A+((-38664000)*Y+(-511690230)))))*row2_53 B A Y X+
  (((1166400)*B+((-803520)*Y+((-492669360)*X+(-523494180)))))*row2_54 B A Y X+
  (((17210880)*A))*row2_39 B A Y X+
  (((382278)*A+((537828)*X)))*row2_41 B A Y X+
  (((-6480)*A+((-329379)*X)))*row2_42 B A Y X+
  (((-290427120)*A))*row2_44 B A Y X+
  (((6998400)*X))*row2_31 B A Y X+
  (((-31872)*X))*row2_33 B A Y X+
  (((-461700)*X))*row2_36 B A Y X+
  (((-1329)*X))*row2_37 B A Y X+
  (((9761760)*X))*row2_48 B A Y X=((10))*row3_46 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_39, row2_41, row2_42, row2_44, row2_31, row2_33, row2_36, row2_37, row2_48, row3_46] <;> ring
compact_certificate theorem row3_46_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_46 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_31 := row2_31_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_46_identity B A Y X).symm
  have hz : ((10))*row3_46 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_39, z2_41, z2_42, z2_44, z2_31, z2_33, z2_36, z2_37, z2_48,mul_zero,add_zero] using he
  have hu : ((10):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_46_zero
compact_certificate def row3_53 (B A Y X : ℂ) : ℂ := (((((((12597120)*X^2)*Y)*A+(((-1026432)*Y+(-323333370))*Y+((8164800)*X^3)))*A+((((30093120)*X)*Y+(((801660888)*X+(323333370))*X))*Y+(((307003770)*X+(-315168570))*X^2)))*A+(((((-466560)*X)*Y+((((9331200)*X+(17262720))*X+(332991162))*X))*Y+((((-223766550)*X+(1625426514))*X+(-9191232))*X))*Y+((((-646666740)*X+(970000110))*X+(-323333370))*X)))*B+((((((69120)*Y+((103284696)*X+(591675472)))*Y+(((-9495755121)*X+(-3787638659))*X+(3784825909)))*Y+((1460776615)*X^3))*A+((((((-2764800)*X+(-120666240))*X)*Y+(((-3977852350)*X+(-9077563505))*X))*Y+(((-1846318023)*X+(731489471))*X))*Y+(((((-357370785)*X+(-752571141))*X+(-3333079958))*X+(5245602524))*X^2)))*A+((((((1036800)*X)*Y+(((-95308380)*X+(-285393360))*X))*Y+((((-1140298965)*X+(-2808878936))*X+(-7881899986))*X))*Y+(((((-1533699225)*X+(-2744746246))*X+(-8604089928))*X+(20582933997))*X))*Y+((((((714741570)*X+(1147771497))*X+(70482315))*X+(-7981178546))*X+(3784825909))*X))))
compact_certificate theorem row3_53_identity (B A Y X : ℂ) :
  ((-260415))*row2_17 B A Y X+
  (((-233280)*B+((-55159218)*A+((120960)*Y+(-21899000)))))*row2_46 B A Y X+
  (((43045020)*A+((-933120)*Y+((-14813280)*X+(-208891305)))))*row2_51 B A Y X+
  (((-18959161320)*B+((-3233994120)*A+((3596184000)*Y+((92793600)*X+(48806327250))))))*row2_53 B A Y X+
  (((80248320)*Y+((47472130080)*X+(55499634540))))*row2_54 B A Y X+
  (((-1925959680)*A))*row2_39 B A Y X+
  (((-35097138)*A+((-52377948)*X)))*row2_41 B A Y X+
  (((28340079120)*A+((-65318400)*X)))*row2_44 B A Y X+
  (((-51840)*Y+((31746249)*X)))*row2_42 B A Y X+
  (((3566592)*X))*row2_33 B A Y X+
  (((52123500)*X))*row2_36 B A Y X+
  (((-1722141)*X))*row2_37 B A Y X+
  (((-1033080480)*X))*row2_48 B A Y X=((10))*row3_53 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_39, row2_41, row2_44, row2_42, row2_33, row2_36, row2_37, row2_48, row3_53] <;> ring
compact_certificate theorem row3_53_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_53 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_53_identity B A Y X).symm
  have hz : ((10))*row3_53 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_39, z2_41, z2_44, z2_42, z2_33, z2_36, z2_37, z2_48,mul_zero,add_zero] using he
  have hu : ((10):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_53_zero
compact_certificate def row3_54 (B A Y X : ℂ) : ℂ := (((((14850)*Y)*A+((((59400)*X+(-14850))*X)*Y+(((-14850)*X+(14850))*X^2)))*A+((((-14850)*X)*Y+(((-14850)*X+(44550))*X^2))*Y+((((29700)*X+(-44550))*X+(14850))*X)))*B+((((((87480)*X^2)*Y)*A^2+((((-47916)*X+(46504))*Y+(((-1025364)*X+(-587465))*X+(301546)))*Y+((-407315)*X^3)))*A+(((((-9720)*X)*Y+(((-379750)*X+(-1454195))*X))*Y+(((-2123541)*X+(302354))*X))*Y+(((((-42930)*X+(-107304))*X+(361219))*X+(-105769))*X^2)))*A+((((((16200)*X+(-3360))*X)*Y+((((-80730)*X+(-382784))*X+(-1052305))*X))*Y+(((((-183330)*X+(-499294))*X+(-1113255))*X+(1493319))*X))*Y+((((((85860)*X+(171678))*X+(799518))*X+(-1056503))*X+(301546))*X))))
compact_certificate theorem row3_54_identity (B A Y X : ℂ) :
  (((-10734)*A+(13280)))*row2_46 B A Y X+
  (((3300)*A+(3300)))*row2_51 B A Y X+
  (((297000)*B+((17564040)*A+((864000)*Y+(4658040)))))*row2_53 B A Y X+
  (((12960)*Y+((4073400)*X+(-9002700))))*row2_54 B A Y X+
  (((-311040)*A))*row2_39 B A Y X+
  (((-7494)*A+((-4824)*X)))*row2_41 B A Y X+
  (((2604960)*A))*row2_44 B A Y X+
  (((576)*X))*row2_33 B A Y X+
  (((5367)*X))*row2_37 B A Y X+
  (((5367)*X))*row2_42 B A Y X+
  (((-79200)*X))*row2_48 B A Y X=((20))*row3_54 B A Y X := by
  simp only [row2_46, row2_51, row2_53, row2_54, row2_39, row2_41, row2_44, row2_33, row2_37, row2_42, row2_48, row3_54] <;> ring
compact_certificate theorem row3_54_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_54 B A Y X=0 := by
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_54_identity B A Y X).symm
  have hz : ((20))*row3_54 B A Y X=0 := by
    simpa only [z2_46, z2_51, z2_53, z2_54, z2_39, z2_41, z2_44, z2_33, z2_37, z2_42, z2_48,mul_zero,add_zero] using he
  have hu : ((20):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_54_zero
compact_certificate def row3_57 (B A Y X : ℂ) : ℂ := ((((((2099520)*Y)*A+((((8398080)*X+(-2099520))*X)*Y+(((-2099520)*X+(2099520))*X^2)))*A+((((-2099520)*X)*Y+(((-2099520)*X+(6298560))*X^2))*Y+((((4199040)*X+(-6298560))*X+(2099520))*X)))*B+(((((12597120)*X^3)*A+(((-513216)*Y+(-280341810))*Y+(((10730880)*X+(12597120))*X^2)))*A+((((699840)*X)*Y+(((444594744)*X+(353125170))*X))*Y+(((270077490)*X+(-244416690))*X^2)))*A+(((((-233280)*X)*Y+((((-9331200)*X+(72783360))*X+(274556466))*X))*Y+((((-305949150)*X+(1708118442))*X+(110528064))*X))*Y+((((-683855460)*X+(902611350))*X+(-280341810))*X))))*B+((((((34560)*Y+((282933528)*X+(429860336)))*Y+(((-7563555213)*X+(-2475101047))*X+(3103082897)))*Y+((2252589515)*X^3))*A+((((((-1382400)*X+(-114959520))*X)*Y+(((-2311051430)*X+(-6073389325))*X))*Y+(((1413628821)*X+(-3977045357))*X))*Y+(((((-202736925)*X+(-586375473))*X+(-3748262254))*X+(5355672412))*X^2)))*A+((((((518400)*X)*Y+(((-95090220)*X+(-231138960))*X))*Y+((((-728402625)*X+(-1809502648))*X+(-4683766298))*X))*Y+(((((-869560245)*X+(-1998496238))*X+(-5252649624))*X+(21081804441))*X))*Y+((((((405473850)*X+(970014021))*X+(-2100209025))*X+(-5449249018))*X+(3103082897))*X))))
compact_certificate theorem row3_57_identity (B A Y X : ℂ) :
  ((-195615))*row2_17 B A Y X+
  (((-116640)*B+((-38412414)*A+((60480)*Y+(-17188120)))))*row2_46 B A Y X+
  (((233280)*B+((23871780)*A+((1088640)*Y+((-12363840)*X+(-142878465))))))*row2_51 B A Y X+
  (((-14657497560)*B+((-10023023160)*A+((2040120000)*Y+((46396800)*X+(27137515050))))))*row2_53 B A Y X+
  (((-70683840)*B+((59952960)*Y+((30763268640)*X+(50083165620)))))*row2_54 B A Y X+
  (((20995200)*B+((236196000)*X)))*row2_43 B A Y X+
  (((116640)*A))*row2_35 B A Y X+
  (((-1438871040)*A))*row2_39 B A Y X+
  (((-26048574)*A+((-33873444)*X)))*row2_41 B A Y X+
  (((18319653360)*A+((-32659200)*X)))*row2_44 B A Y X+
  (((-25920)*Y+((22336047)*X)))*row2_42 B A Y X+
  (((-5598720)*X))*row2_29 B A Y X+
  (((2664576)*X))*row2_33 B A Y X+
  (((35210700)*X))*row2_36 B A Y X+
  (((-1451223)*X))*row2_37 B A Y X+
  (((-572922720)*X))*row2_48 B A Y X=((10))*row3_57 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_43, row2_35, row2_39, row2_41, row2_44, row2_42, row2_29, row2_33, row2_36, row2_37, row2_48, row3_57] <;> ring
compact_certificate theorem row3_57_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_57 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_43 := row2_43_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_35 := row2_35_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_29 := row2_29_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_57_identity B A Y X).symm
  have hz : ((10))*row3_57 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_43, z2_35, z2_39, z2_41, z2_44, z2_42, z2_29, z2_33, z2_36, z2_37, z2_48,mul_zero,add_zero] using he
  have hu : ((10):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_57_zero
compact_certificate def row3_58 (B A Y X : ℂ) : ℂ := (((((-593190)*Y+((-23328)*X^3))*A+((((-23328)*X)*Y+(((1616328)*X+(593190))*X))*Y+(((639846)*X+(-616518))*X^2)))*A+(((((93312)*X+(569862))*X)*Y+((((-614034)*X+(3655854))*X+(23328))*X))*Y+((((-1186380)*X+(1779570))*X+(-593190))*X)))*B+((((((139968)*X^3)*A+((139968)*X^2))*A+((((-245304)*X+(1270952))*Y+(((-20381127)*X+(-7517647))*X+(8756027)))*Y+(((3153557)*X+(279936))*X^2)))*A+(((((-241056)*X)*Y+(((-8242826)*X+(-20344507))*X))*Y+(((-5890599)*X+(21169))*X))*Y+(((((-768447)*X+(-1558893))*X+(-8371588))*X+(12469456))*X^2)))*A+((((((-153252)*X+(-640968))*X)*Y+((((-2331531)*X+(-6100330))*X+(-17065874))*X))*Y+(((((-3281607)*X+(-6359372))*X+(-19533564))*X+(48805791))*X))*Y+((((((1536894)*X+(2349339))*X+(330567))*X+(-18456784))*X+(8756027))*X))))
compact_certificate theorem row3_58_identity (B A Y X : ℂ) :
  ((-2565))*row2_17 B A Y X+
  (((-563718)*A+(-177020)))*row2_46 B A Y X+
  (((432660)*A+((-194400)*X+(-1979115))))*row2_51 B A Y X+
  (((-185009400)*B+((15866280)*A+((38664000)*Y+(525687030)))))*row2_53 B A Y X+
  (((-1166400)*B+((803520)*Y+((504177840)*X+(515640420)))))*row2_54 B A Y X+
  (((-17210880)*A))*row2_39 B A Y X+
  (((-369318)*A+((-537828)*X)))*row2_41 B A Y X+
  (((6480)*A+((322899)*X)))*row2_42 B A Y X+
  (((290427120)*A))*row2_44 B A Y X+
  (((31872)*X))*row2_33 B A Y X+
  (((461700)*X))*row2_36 B A Y X+
  (((-5151)*X))*row2_37 B A Y X+
  (((-10383840)*X))*row2_48 B A Y X=((50))*row3_58 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_39, row2_41, row2_42, row2_44, row2_33, row2_36, row2_37, row2_48, row3_58] <;> ring
compact_certificate theorem row3_58_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_58 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_58_identity B A Y X).symm
  have hz : ((50))*row3_58 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_39, z2_41, z2_42, z2_44, z2_33, z2_36, z2_37, z2_48,mul_zero,add_zero] using he
  have hu : ((50):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_58_zero
compact_certificate def row3_59 (B A Y X : ℂ) : ℂ := (((((1)*Y)*A+((((1)*X^2+(-1))*X)*Y+(((-1)*X+(1))*X^2)))*A+((((-1)*X)*Y+((-1)*X^2))*Y+((((2)*X+(-3))*X+(1))*X)))*B^2)
compact_certificate theorem row3_59_identity (B A Y X : ℂ) :
  (((1)*B))*row2_43 B A Y X=((1))*row3_59 B A Y X := by
  simp only [row2_43, row3_59] <;> ring
compact_certificate theorem row3_59_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_59 B A Y X=0 := by
  have z2_43 := row2_43_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_59_identity B A Y X).symm
  have hz : ((1))*row3_59 B A Y X=0 := by
    simpa only [z2_43,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_59_zero
compact_certificate def row3_60 (B A Y X : ℂ) : ℂ := ((((((24)*X^3+(-24))*Y+((-24)*X^3))*A+((((-24)*X)*Y+(((-24)*X+(24))*X))*Y+(((72)*X+(-48))*X^2)))*A+(((((-90)*X+(336))*X+(24))*X)*Y+((((-48)*X+(72))*X+(-24))*X)))*B+((((((-270)*X+(-444))*X+(303))*Y+((540)*X^3))*A+((((-160)*X)*Y+(((780)*X+(-1815))*X))*Y+(((-699)*X+(843))*X^2)))*A+((((-455)*X)*Y+(((-171)*X+(4632))*X))*Y+((((-762)*X+(-225))*X+(303))*X))))
compact_certificate theorem row3_60_identity (B A Y X : ℂ) :
  ((1))*row2_51 B A Y X+
  (((-24)*B))*row2_54 B A Y X+
  (((24)*A))*row2_43 B A Y X=((1))*row3_60 B A Y X := by
  simp only [row2_51, row2_54, row2_43, row3_60] <;> ring
compact_certificate theorem row3_60_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_60 B A Y X=0 := by
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_43 := row2_43_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_60_identity B A Y X).symm
  have hz : ((1))*row3_60 B A Y X=0 := by
    simpa only [z2_51, z2_54, z2_43,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_60_zero
compact_certificate def row3_65 (B A Y X : ℂ) : ℂ := ((((((256608)*Y+(70078770))*Y+(((3149280)*X+(-2041200))*X^3))*A+((((-7523280)*X)*Y+(((-133208712)*X+(-70078770))*X))*Y+(((-62847090)*X+(68037570))*X^2)))*A+(((((116640)*X)*Y+((((-2332800)*X+(1982880))*X+(-72493218))*X))*Y+((((23393610)*X+(-246514266))*X+(2297808))*X))*Y+(((((-12597120)*X+(146456100))*X+(-210236310))*X+(70078770))*X)))*B+((((((-17280)*Y+((-48699624)*X+(-97904608)))*Y+(((1700968809)*X+(523421111))*X+(-608254531)))*Y+((-203432395)*X^3))*A+((((((691200)*X+(22293360))*X)*Y+(((684678790)*X+(1510578725))*X))*Y+(((348680187)*X+(-298402769))*X))*Y+(((((59350725)*X+(139105689))*X+(490996592))*X+(-811686926))*X^2)))*A+((((((-259200)*X)*Y+(((17036460)*X+(41065680))*X))*Y+((((192458025)*X+(485500184))*X+(1285021204))*X))*Y+(((((255345885)*X+(488369374))*X+(1384668522))*X+(-2834252193))*X))*Y+((((((-118701450)*X+(-218860653))*X+(-29157915))*X+(1300640864))*X+(-608254531))*X))))
compact_certificate theorem row3_65_identity (B A Y X : ℂ) :
  ((44145))*row2_17 B A Y X+
  (((58320)*B+((10563372)*A+((-30240)*Y+(3110360)))))*row2_46 B A Y X+
  (((-7183080)*A+((233280)*Y+((3703320)*X+(36733095)))))*row2_51 B A Y X+
  (((3353341680)*B+((346276080)*A+((-597240000)*Y+((-23198400)*X+(-7304697450))))))*row2_53 B A Y X+
  (((-14813280)*Y+((-8012497320)*X+(-10019318760))))*row2_54 B A Y X+
  (((355518720)*A))*row2_39 B A Y X+
  (((6860052)*A+((8899092)*X)))*row2_41 B A Y X+
  (((-4819506480)*A+((16329600)*X)))*row2_44 B A Y X+
  (((12960)*Y+((-5988006)*X)))*row2_42 B A Y X+
  (((-658368)*X))*row2_33 B A Y X+
  (((-7946100)*X))*row2_36 B A Y X+
  (((-163296)*X))*row2_37 B A Y X+
  (((172393920)*X))*row2_48 B A Y X=((10))*row3_65 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_39, row2_41, row2_44, row2_42, row2_33, row2_36, row2_37, row2_48, row3_65] <;> ring
compact_certificate theorem row3_65_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_65 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_65_identity B A Y X).symm
  have hz : ((10))*row3_65 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_39, z2_41, z2_44, z2_42, z2_33, z2_36, z2_37, z2_48,mul_zero,add_zero] using he
  have hu : ((10):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_65_zero

compact_certificate def row3_67 (B A Y X : ℂ) : ℂ := (((((5022)*Y)*A+(((((2592)*X^2+(9720))*X+(-5022))*X)*Y+(((-5022)*X+(5022))*X^2)))*A+((((-5022)*X)*Y+(((-2430)*X+(4698))*X^2))*Y+((((10044)*X+(-15066))*X+(5022))*X)))*B+((((((-16584)*X+(6928))*Y+(((-7365)*X+(-74063))*X+(20833)))*Y+((-10877)*X^3))*A+(((((-36982)*X+(-89429))*X)*Y+(((-74979)*X+(77987))*X))*Y+(((((-4293)*X+(-825))*X+(-1862))*X+(9956))*X^2)))*A+((((((-972)*X+(-6672))*X)*Y+((((-13257)*X+(-21176))*X+(-81106))*X))*Y+(((((-18333)*X+(-5470))*X+(-112896))*X+(187905))*X))*Y+((((((8586)*X+(-2643))*X+(46407))*X+(-65282))*X+(20833))*X))))
compact_certificate theorem row3_67_identity (B A Y X : ℂ) :
  ((-3))*row2_17 B A Y X+
  (((270)*A+(-728)))*row2_46 B A Y X+
  (((540)*A+(-2565)))*row2_51 B A Y X+
  (((-132840)*B+((-249480)*A+((43200)*Y+(1126170)))))*row2_53 B A Y X+
  (((531360)*X+(231660)))*row2_54 B A Y X+
  (((270)*A+((-540)*X)))*row2_41 B A Y X+
  (((291600)*A))*row2_44 B A Y X+
  (((540)*X))*row2_36 B A Y X+
  (((-357)*X))*row2_37 B A Y X+
  (((-87)*X))*row2_42 B A Y X+
  (((25920)*X))*row2_43 B A Y X+
  (((-12960)*X))*row2_48 B A Y X=((10))*row3_67 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_41, row2_44, row2_36, row2_37, row2_42, row2_43, row2_48, row3_67] <;> ring
compact_certificate theorem row3_67_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_67 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_43 := row2_43_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_67_identity B A Y X).symm
  have hz : ((10))*row3_67 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_41, z2_44, z2_36, z2_37, z2_42, z2_43, z2_48,mul_zero,add_zero] using he
  have hu : ((10):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_67_zero
compact_certificate def row3_69 (B A Y X : ℂ) : ℂ := ((((((1)*X)*Y+((1)*X+(-1)))*Y)*A+(((((1)*X^2+(-1))*X^2)*Y+(((-1)*X+(1))*X))*Y+((((-1)*X+(2))*X+(-1))*X^2)))*A+(((((-1)*X^2)*Y+((((-1)*X+(-1))*X+(1))*X))*Y+((((2)*X+(-4))*X+(2))*X^2))*Y+(((((2)*X+(-5))*X+(4))*X+(-1))*X)))
compact_certificate theorem row3_69_identity (B A Y X : ℂ) :
  ((-1))*row2_53 B A Y X+
  (((1)*X))*row2_45 B A Y X=((1))*row3_69 B A Y X := by
  simp only [row2_53, row2_45, row3_69] <;> ring
compact_certificate theorem row3_69_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_69 B A Y X=0 := by
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_45 := row2_45_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_69_identity B A Y X).symm
  have hz : ((1))*row3_69 B A Y X=0 := by
    simpa only [z2_53, z2_45,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_69_zero
compact_certificate def row3_70 (B A Y X : ℂ) : ℂ := (((((-509310)*Y+((19440)*X^3))*A+((((19440)*X)*Y+(((1170360)*X+(509310))*X))*Y+((((19440)*X^2+(470430))*X+(-489870))*X^2)))*A+((((528750)*X)*Y+(((((-72900)*X^2+(873810))*X+(1407510))*X+(-19440))*X))*Y+((((((-38880)*X+(19440))*X+(-1018620))*X+(1527930))*X+(-509310))*X)))*B+((((((124768)*X+(882128))*Y+(((-9757623)*X+(-4860145))*X+(910937)))*Y+((1621565)*X^3))*A+(((((-181440)*X)*Y+(((-5286770)*X+(-9842995))*X))*Y+(((-2963757)*X+(12014803))*X))*Y+(((((-579555)*X+(449457))*X+(-1487812))*X+(2532502))*X^2)))*A+((((((-102060)*X+(-635280))*X)*Y+((((-1760535)*X+(-3340648))*X+(-4794240))*X))*Y+(((((-1626075)*X+(3778342))*X+(5778750))*X+(15212343))*X))*Y+((((((1159110)*X+(-1478469))*X+(-3061179))*X+(-66556))*X+(910937))*X))))
compact_certificate theorem row3_70_identity (B A Y X : ℂ) :
  ((-315))*row2_17 B A Y X+
  (((-85424)*A+(-43960)))*row2_46 B A Y X+
  (((60320)*A+(-273805)))*row2_51 B A Y X+
  (((-24508800)*B+((17267040)*A+((5832000)*Y+(46568790)))))*row2_53 B A Y X+
  (((194400)*B+((120960)*Y+((67066080)*X+(61664640)))))*row2_54 B A Y X+
  (((-2903040)*A))*row2_39 B A Y X+
  (((-55184)*A+((-74544)*X)))*row2_41 B A Y X+
  (((-194400)*A))*row2_43 B A Y X+
  (((40253760)*A))*row2_44 B A Y X+
  (((5376)*X))*row2_33 B A Y X+
  (((56700)*X))*row2_36 B A Y X+
  (((4282)*X))*row2_37 B A Y X+
  (((16200)*X))*row2_40 B A Y X+
  (((47752)*X))*row2_42 B A Y X+
  (((-1447680)*X))*row2_48 B A Y X=((10))*row3_70 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_39, row2_41, row2_43, row2_44, row2_33, row2_36, row2_37, row2_40, row2_42, row2_48, row3_70] <;> ring
compact_certificate theorem row3_70_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_70 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_43 := row2_43_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_40 := row2_40_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_70_identity B A Y X).symm
  have hz : ((10))*row3_70 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_39, z2_41, z2_43, z2_44, z2_33, z2_36, z2_37, z2_40, z2_42, z2_48,mul_zero,add_zero] using he
  have hu : ((10):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_70_zero
compact_certificate def row3_72 (B A Y X : ℂ) : ℂ := (((((1)*X^2+(1))*Y)*A+((((1)*X^4+(-1))*X)*Y+(((((-1)*X+(1))*X+(-1))*X+(1))*X^2)))*A+(((((-1)*X^2+(-1))*X)*Y+(((-1)*X^2+(-1))*X^2))*Y+((((((2)*X+(-3))*X+(3))*X+(-3))*X+(1))*X)))
compact_certificate theorem row3_72_identity (B A Y X : ℂ) :
  (((1)*Y+((1)*X+(1))))*row2_53 B A Y X+
  (((-1)*Y))*row2_28 B A Y X+
  (((1)*X))*row2_27 B A Y X=((1))*row3_72 B A Y X := by
  simp only [row2_53, row2_28, row2_27, row3_72] <;> ring
compact_certificate theorem row3_72_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_72 B A Y X=0 := by
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_28 := row2_28_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_27 := row2_27_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_72_identity B A Y X).symm
  have hz : ((1))*row3_72 B A Y X=0 := by
    simpa only [z2_53, z2_28, z2_27,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_72_zero
compact_certificate def row3_73 (B A Y X : ℂ) : ℂ := ((((((1)*Y)*A+((1)*Y+((1)*X^2)))*A+(((-1)*X)*Y+(((-1)*X+(1))*X)))*A+(((-1)*X)*Y+(((-2)*X+(1))*X)))*B^2)
compact_certificate theorem row3_73_identity (B A Y X : ℂ) :
  (((1)*B))*row2_48 B A Y X=((1))*row3_73 B A Y X := by
  simp only [row2_48, row3_73] <;> ring
compact_certificate theorem row3_73_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_73 B A Y X=0 := by
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_73_identity B A Y X).symm
  have hz : ((1))*row3_73 B A Y X=0 := by
    simpa only [z2_48,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_73_zero
compact_certificate def row3_78 (B A Y X : ℂ) : ℂ := (((((2430)*Y)*A+((((9720)*X+(-2430))*X)*Y+(((-2430)*X+(2430))*X^2)))*A+((((-2430)*X)*Y+(((-2430)*X+(7290))*X^2))*Y+((((4860)*X+(-7290))*X+(2430))*X)))*B+(((((2592)*Y^3)*A+((((2592)*Y+((-19176)*X+(4336)))*Y+(((-2181)*X+(-71471))*X+(33793)))*Y+((-5693)*X^3)))*A+(((((-2592)*X)*Y+(((-36982)*X+(-79061))*X))*Y+(((-74979)*X+(65027))*X))*Y+(((((-4293)*X+(1767))*X+(-22598))*X+(28100))*X^2)))*A+((((((1620)*X+(-6672))*X)*Y+((((-8073)*X+(-26360))*X+(-86290))*X))*Y+(((((-18333)*X+(-13246))*X+(-110304))*X+(180129))*X))*Y+((((((8586)*X+(-7827))*X+(69735))*X+(-101570))*X+(33793))*X))))
compact_certificate theorem row3_78_identity (B A Y X : ℂ) :
  (((54)*A+(16)))*row2_46 B A Y X+
  (((108)*A+(108)))*row2_51 B A Y X+
  (((9720)*B+((183384)*A+((-3456)*Y+(288468)))))*row2_53 B A Y X+
  (((-10368)*Y+((106272)*X+(-197316))))*row2_54 B A Y X+
  (((10368)*A))*row2_24 B A Y X+
  (((54)*A+((-108)*X)))*row2_41 B A Y X+
  (((58320)*A))*row2_44 B A Y X+
  (((-10368)*Y))*row2_23 B A Y X+
  (((-27)*X))*row2_37 B A Y X+
  (((-27)*X))*row2_42 B A Y X+
  (((-2592)*X))*row2_48 B A Y X=((4))*row3_78 B A Y X := by
  simp only [row2_46, row2_51, row2_53, row2_54, row2_24, row2_41, row2_44, row2_23, row2_37, row2_42, row2_48, row3_78] <;> ring
compact_certificate theorem row3_78_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_78 B A Y X=0 := by
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_24 := row2_24_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_23 := row2_23_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_78_identity B A Y X).symm
  have hz : ((4))*row3_78 B A Y X=0 := by
    simpa only [z2_46, z2_51, z2_53, z2_54, z2_24, z2_41, z2_44, z2_23, z2_37, z2_42, z2_48,mul_zero,add_zero] using he
  have hu : ((4):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_78_zero
compact_certificate def row3_79 (B A Y X : ℂ) : ℂ := (((((((4608)*X)*Y)*A+((4608)*X^3))*A+((((-17280)*X+(64512))*X^2)*Y+(((-9216)*X+(4608))*X^2)))*B+((((387486)*Y+((103680)*X^3))*A+((((-30720)*X)*Y+(((-710280)*X+(-677790))*X))*Y+(((-378270)*X+(491166))*X^2)))*A+(((((-51840)*X+(-416670))*X)*Y+((((-26910)*X+(-702630))*X+(889344))*X))*Y+((((341820)*X+(-945882))*X+(387486))*X))))*B+((((((44920)*X+(-684720))*Y+(((9388155)*X+(2953617))*X+(-3415599)))*Y+((204195)*X^3))*A+(((((129600)*X)*Y+(((4359690)*X+(9788235))*X))*Y+(((4814205)*X+(-6905805))*X))*Y+(((((407835)*X+(790695))*X+(1604202))*X+(-3211404))*X^2)))*A+((((((92340)*X+(365040))*X)*Y+((((1259415)*X+(3143880))*X+(7062110))*X))*Y+(((((1741635)*X+(3146850))*X+(9380208))*X+(-7832991))*X))*Y+((((((-815670)*X+(-1173555))*X+(-3234489))*X+(8843790))*X+(-3415599))*X))))
compact_certificate theorem row3_79_identity (B A Y X : ℂ) :
  ((57))*row2_17 B A Y X+
  (((11702)*A+(4872)))*row2_46 B A Y X+
  (((384)*B+((-9620)*A+((4320)*X+(52159)))))*row2_51 B A Y X+
  (((4136760)*B+((523800)*A+((-820800)*Y+(-11616750)))))*row2_53 B A Y X+
  (((-17280)*Y+((-10567680)*X+(-11766660))))*row2_54 B A Y X+
  (((414720)*A))*row2_39 B A Y X+
  (((7382)*A+((11652)*X)))*row2_41 B A Y X+
  (((-6292080)*A))*row2_44 B A Y X+
  (((-768)*X))*row2_33 B A Y X+
  (((-10260)*X))*row2_36 B A Y X+
  (((527)*X))*row2_37 B A Y X+
  (((-6763)*X))*row2_42 B A Y X+
  (((230880)*X))*row2_48 B A Y X=((2))*row3_79 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_39, row2_41, row2_44, row2_33, row2_36, row2_37, row2_42, row2_48, row3_79] <;> ring
compact_certificate theorem row3_79_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_79 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_79_identity B A Y X).symm
  have hz : ((2))*row3_79 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_39, z2_41, z2_44, z2_33, z2_36, z2_37, z2_42, z2_48,mul_zero,add_zero] using he
  have hu : ((2):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_79_zero
compact_certificate def row3_80 (B A Y X : ℂ) : ℂ := (((((((24)*X)*Y)*A+((24)*X^3))*A+(((-24)*X^2)*Y+(((-48)*X+(24))*X^2)))*A+((((90)*X+(-360))*X^2)*Y))*B+((((((270)*X+(444))*X+(-303))*Y+((-540)*X^3))*A+((((160)*X)*Y+(((-780)*X+(1815))*X))*Y+(((699)*X+(-843))*X^2)))*A+((((455)*X)*Y+(((171)*X+(-4632))*X))*Y+((((762)*X+(225))*X+(-303))*X))))
compact_certificate theorem row3_80_identity (B A Y X : ℂ) :
  ((-1))*row2_51 B A Y X+
  (((24)*X))*row2_48 B A Y X=((1))*row3_80 B A Y X := by
  simp only [row2_51, row2_48, row3_80] <;> ring
compact_certificate theorem row3_80_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_80 B A Y X=0 := by
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_80_identity B A Y X).symm
  have hz : ((1))*row3_80 B A Y X=0 := by
    simpa only [z2_51, z2_48,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_80_zero
compact_certificate def row3_81 (B A Y X : ℂ) : ℂ := (((((-180)*Y)*A+((((-720)*X+(180))*X)*Y+(((180)*X+(-180))*X^2)))*A+((((180)*X)*Y+(((180)*X+(-540))*X^2))*Y+((((-360)*X+(540))*X+(-180))*X)))*B+((((((1080)*X)*Y)*A^2+((((224)*X+(4))*Y+(((-4164)*X+(2455))*X+(166)))*Y+((-3080)*X^3)))*A+(((((-160)*X+(-20))*X)*Y+(((-2571)*X+(-6406))*X))*Y+((((-159)*X+(3169))*X+(-2914))*X^2)))*A+(((((60)*X)*Y+(((-299)*X+(330))*X))*Y+((((-679)*X+(1950))*X+(-9516))*X))*Y+(((((318)*X+(5823))*X+(-3323))*X+(166))*X))))
compact_certificate theorem row3_81_identity (B A Y X : ℂ) :
  (((-2)*A+(2)))*row2_46 B A Y X+
  (((-4)*A+(-4)))*row2_51 B A Y X+
  (((-360)*B+((1080)*A+(-1080))))*row2_53 B A Y X+
  (((-1776)*X+(1212)))*row2_54 B A Y X+
  (((-2)*A))*row2_41 B A Y X+
  (((1)*X))*row2_37 B A Y X+
  (((1)*X))*row2_42 B A Y X+
  (((96)*X))*row2_48 B A Y X+
  (((2160)*X))*row2_49 B A Y X=((2))*row3_81 B A Y X := by
  simp only [row2_46, row2_51, row2_53, row2_54, row2_41, row2_37, row2_42, row2_48, row2_49, row3_81] <;> ring
compact_certificate theorem row3_81_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_81 B A Y X=0 := by
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_49 := row2_49_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_81_identity B A Y X).symm
  have hz : ((2))*row3_81 B A Y X=0 := by
    simpa only [z2_46, z2_51, z2_53, z2_54, z2_41, z2_37, z2_42, z2_48, z2_49,mul_zero,add_zero] using he
  have hu : ((2):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_81_zero
compact_certificate def row3_82 (B A Y X : ℂ) : ℂ := (((((((1152)*X)*Y+(-13302))*Y)*A+((((-48600)*X+(13302))*X)*Y+(((13302)*X+(-13302))*X^2)))*A+((((((-4320)*X+(16128))*X+(13302))*X)*Y+(((9846)*X+(-34146))*X^2))*Y+((((-26604)*X+(39906))*X+(-13302))*X)))*B+((((((74568)*X+(-7136))*Y+(((10905)*X+(383275))*X+(-109493)))*Y+((54385)*X^3))*A+(((((-7680)*X)*Y+(((209390)*X+(347065))*X))*Y+(((441279)*X+(-384607))*X))*Y+(((((21465)*X+(-8835))*X+(27598))*X+(-55108))*X^2)))*A+((((((-8100)*X+(-1440))*X)*Y+((((40365)*X+(97672))*X+(633194))*X))*Y+(((((91665)*X+(29654))*X+(507168))*X+(-912021))*X))*Y+((((((-42930)*X+(39135))*X+(-281571))*X+(355354))*X+(-109493))*X))))
compact_certificate theorem row3_82_identity (B A Y X : ℂ) :
  (((-270)*A+(-80)))*row2_46 B A Y X+
  (((-540)*A+((192)*Y+(-540))))*row2_51 B A Y X+
  (((-53208)*B+((-1072440)*A+((-86400)*Y+(-1308132)))))*row2_53 B A Y X+
  (((-531360)*X+(1090260)))*row2_54 B A Y X+
  (((-270)*A+((540)*X)))*row2_41 B A Y X+
  (((-291600)*A))*row2_44 B A Y X+
  (((135)*X))*row2_37 B A Y X+
  (((135)*X))*row2_42 B A Y X+
  (((12960)*X))*row2_48 B A Y X=((4))*row3_82 B A Y X := by
  simp only [row2_46, row2_51, row2_53, row2_54, row2_41, row2_44, row2_37, row2_42, row2_48, row3_82] <;> ring
compact_certificate theorem row3_82_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_82 B A Y X=0 := by
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_82_identity B A Y X).symm
  have hz : ((4))*row3_82 B A Y X=0 := by
    simpa only [z2_46, z2_51, z2_53, z2_54, z2_41, z2_44, z2_37, z2_42, z2_48,mul_zero,add_zero] using he
  have hu : ((4):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_82_zero
compact_certificate def row3_83 (B A Y X : ℂ) : ℂ := ((((((1)*X)*Y^2)*A+((((1)*X)*Y+((1)*X+(2)))*Y+((1)*X^3)))*A+(((((-1)*X+(1))*X)*Y+(((2)*X+(-2))*X))*Y+(((-3)*X+(3))*X^2)))*A+(((((-1)*X+(-1))*X)*Y+(((-2)*X^2+(-1))*X))*Y+((((2)*X+(-5))*X+(2))*X)))
compact_certificate theorem row3_83_identity (B A Y X : ℂ) :
  (((-1080)*A+(540)))*row2_53 B A Y X+
  ((540))*row2_54 B A Y X+
  (((540)*A))*row2_39 B A Y X+
  (((540)*A))*row2_44 B A Y X+
  (((-1)*X))*row2_33 B A Y X+
  (((-1)*X))*row2_41 B A Y X=((540))*row3_83 B A Y X := by
  simp only [row2_53, row2_54, row2_39, row2_44, row2_33, row2_41, row3_83] <;> ring
compact_certificate theorem row3_83_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_83 B A Y X=0 := by
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_83_identity B A Y X).symm
  have hz : ((540))*row3_83 B A Y X=0 := by
    simpa only [z2_53, z2_54, z2_39, z2_44, z2_33, z2_41,mul_zero,add_zero] using he
  have hu : ((540):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_83_zero
compact_certificate def row3_84 (B A Y X : ℂ) : ℂ := (((((308610)*Y)*A+((((1234440)*X+(-308610))*X)*Y+(((-308610)*X+(308610))*X^2)))*A+((((-308610)*X)*Y+(((-308610)*X+(925830))*X^2))*Y+((((617220)*X+(-925830))*X+(308610))*X)))*B+(((((((20736)*X+(-864))*Y+((-2435568)*X+(399040)))*Y+(((-722811)*X+(-9289361))*X+(4731271)))*Y+((-723011)*X^3))*A+((((((34560)*X+(270000))*X)*Y+(((-4034674)*X+(-10411835))*X))*Y+(((-9740061)*X+(7818869))*X))*Y+(((((-545211)*X+(457689))*X+(-3522050))*X+(4008260))*X^2)))*A+((((((-12960)*X)*Y+(((270324)*X+(-263280))*X))*Y+((((-761967)*X+(-2408552))*X+(-11817862))*X))*Y+(((((-2163699)*X+(-2222890))*X+(-13819824))*X+(22724751))*X))*Y+((((((1090422)*X+(-1460589))*X+(10393833))*X+(-14430614))*X+(4731271))*X))))
compact_certificate theorem row3_84_identity (B A Y X : ℂ) :
  (((6858)*A+((-864)*Y+(2896))))*row2_46 B A Y X+
  (((13716)*A+(13716)))*row2_51 B A Y X+
  (((1234440)*B+((24304104)*A+((2194560)*Y+((-603936)*X+(37481292))))))*row2_53 B A Y X+
  (((13496544)*X+(-24756732)))*row2_54 B A Y X+
  (((6858)*A+((-13716)*X)))*row2_41 B A Y X+
  (((7406640)*A+((466560)*X)))*row2_44 B A Y X+
  (((-3429)*X))*row2_37 B A Y X+
  (((-3429)*X))*row2_42 B A Y X+
  (((-329184)*X))*row2_48 B A Y X=((4))*row3_84 B A Y X := by
  simp only [row2_46, row2_51, row2_53, row2_54, row2_41, row2_44, row2_37, row2_42, row2_48, row3_84] <;> ring
compact_certificate theorem row3_84_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_84 B A Y X=0 := by
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_84_identity B A Y X).symm
  have hz : ((4))*row3_84 B A Y X=0 := by
    simpa only [z2_46, z2_51, z2_53, z2_54, z2_41, z2_44, z2_37, z2_42, z2_48,mul_zero,add_zero] using he
  have hu : ((4):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_84_zero

compact_certificate def row3_85 (B A Y X : ℂ) : ℂ := ((((((10368)*X^2+(65862))*Y)*A+((((-172008)*X+(-65862))*X)*Y+(((-65862)*X+(65862))*X^2)))*A+(((((-10368)*X+(-65862))*X)*Y+(((58554)*X+(-372654))*X^2))*Y+((((131724)*X+(-197586))*X+(65862))*X)))*B+((((((8984)*X+(-136944))*Y+(((2069439)*X+(906141))*X+(-898371)))*Y+((-342777)*X^3))*A+(((((25920)*X)*Y+(((871938)*X+(2071311))*X))*Y+(((408729)*X+(-91785))*X))*Y+(((((81567)*X+(158139))*X+(817410))*X+(-1241148))*X^2)))*A+((((((18468)*X+(73008))*X)*Y+((((251883)*X+(628776))*X+(1735654))*X))*Y+(((((348327)*X+(629370))*X+(1997520))*X+(-4857171))*X))*Y+((((((-163134)*X+(-234711))*X+(-105573))*X+(1928598))*X+(-898371))*X))))
compact_certificate theorem row3_85_identity (B A Y X : ℂ) :
  ((57))*row2_17 B A Y X+
  (((11702)*A+(4872)))*row2_46 B A Y X+
  (((-9620)*A+((4320)*X+(45055))))*row2_51 B A Y X+
  (((4136760)*B+((523800)*A+((-820800)*Y+(-11616750)))))*row2_53 B A Y X+
  (((-17280)*Y+((-10567680)*X+(-11766660))))*row2_54 B A Y X+
  (((414720)*A))*row2_39 B A Y X+
  (((7382)*A+((11652)*X)))*row2_41 B A Y X+
  (((-6292080)*A))*row2_44 B A Y X+
  (((-768)*X))*row2_33 B A Y X+
  (((-10260)*X))*row2_36 B A Y X+
  (((527)*X))*row2_37 B A Y X+
  (((-6763)*X))*row2_42 B A Y X+
  (((230880)*X))*row2_48 B A Y X=((10))*row3_85 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_39, row2_41, row2_44, row2_33, row2_36, row2_37, row2_42, row2_48, row3_85] <;> ring
compact_certificate theorem row3_85_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_85 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_85_identity B A Y X).symm
  have hz : ((10))*row3_85 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_39, z2_41, z2_44, z2_33, z2_36, z2_37, z2_42, z2_48,mul_zero,add_zero] using he
  have hu : ((10):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_85_zero
compact_certificate def row3_86 (B A Y X : ℂ) : ℂ := ((((((540)*X^2)*Y)*A+((((96)*X+(-4))*Y+(((2064)*X+(95))*X+(-166)))*Y+((350)*X^3)))*A+(((((160)*X+(1250))*X)*Y+(((2241)*X+(166))*X))*Y+((((159)*X+(-439))*X+(184))*X^2)))*A+(((((-60)*X)*Y+(((299)*X+(580))*X))*Y+((((679)*X+(360))*X+(-354))*X))*Y+(((((-318)*X+(-363))*X+(593))*X+(-166))*X)))
compact_certificate theorem row3_86_identity (B A Y X : ℂ) :
  (((2)*A+(-2)))*row2_46 B A Y X+
  (((-1080)*A+(1080)))*row2_53 B A Y X+
  (((2)*A))*row2_41 B A Y X+
  (((-1)*X))*row2_37 B A Y X+
  (((-1)*X))*row2_42 B A Y X=((2))*row3_86 B A Y X := by
  simp only [row2_46, row2_53, row2_41, row2_37, row2_42, row3_86] <;> ring
compact_certificate theorem row3_86_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_86 B A Y X=0 := by
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_86_identity B A Y X).symm
  have hz : ((2))*row3_86 B A Y X=0 := by
    simpa only [z2_46, z2_53, z2_41, z2_37, z2_42,mul_zero,add_zero] using he
  have hu : ((2):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_86_zero
compact_certificate def row3_87 (B A Y X : ℂ) : ℂ := ((((((5832)*Y+(201690))*Y)*A+(((((23328)*X+(-5832))*X)*Y+(((789264)*X+(-201690))*X))*Y+(((-201690)*X+(201690))*X^2)))*A+(((((-5832)*X)*Y+((((-5832)*X+(17496))*X+(-201690))*X))*Y+((((-184194)*X+(564246))*X+(5832))*X))*Y+((((403380)*X+(-605070))*X+(201690))*X)))*B+((((((-432)*Y+((-1663968)*X+(301568)))*Y+(((-366999)*X+(-5937277))*X+(3096527)))*Y+((-577495)*X^3))*A+((((((17280)*X+(95148))*X)*Y+(((-2659754)*X+(-6555151))*X))*Y+(((-6218397)*X+(4868365))*X))*Y+(((((-356319)*X+(228309))*X+(-2133646))*X+(2519032))*X^2)))*A+((((((-6480)*X)*Y+(((166752)*X+(-258180))*X))*Y+((((-555903)*X+(-1692052))*X+(-7381310))*X))*Y+(((((-1474335)*X+(-1424174))*X+(-9090972))*X+(14589123))*X))*Y+((((((712638)*X+(-812937))*X+(6805581))*X+(-9481690))*X+(3096527))*X))))
compact_certificate theorem row3_87_identity (B A Y X : ℂ) :
  (((21762)*A+((-1512)*Y+(8800))))*row2_46 B A Y X+
  (((43524)*A+(43524)))*row2_51 B A Y X+
  (((4033800)*B+((79631640)*A+((7171200)*Y+((-1159920)*X+(123597900))))))*row2_53 B A Y X+
  (((42827616)*X+(-81067932)))*row2_54 B A Y X+
  (((21762)*A+((-44820)*X)))*row2_41 B A Y X+
  (((23502960)*A+((816480)*X)))*row2_44 B A Y X+
  (((648)*Y+((-10881)*X)))*row2_42 B A Y X+
  (((-10881)*X))*row2_37 B A Y X+
  (((-1044576)*X))*row2_48 B A Y X=((20))*row3_87 B A Y X := by
  simp only [row2_46, row2_51, row2_53, row2_54, row2_41, row2_44, row2_42, row2_37, row2_48, row3_87] <;> ring
compact_certificate theorem row3_87_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_87 B A Y X=0 := by
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_87_identity B A Y X).symm
  have hz : ((20))*row3_87 B A Y X=0 := by
    simpa only [z2_46, z2_51, z2_53, z2_54, z2_41, z2_44, z2_42, z2_37, z2_48,mul_zero,add_zero] using he
  have hu : ((20):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_87_zero
compact_certificate def row3_88 (B A Y X : ℂ) : ℂ := (((((-2430)*Y)*A+((((-9720)*X+(2430))*X)*Y+(((2430)*X+(-2430))*X^2)))*A+((((2430)*X)*Y+(((2430)*X+(-7290))*X^2))*Y+((((-4860)*X+(7290))*X+(-2430))*X)))*B+(((((((2592)*X+(19176))*X+(-4336))*Y+(((2181)*X+(71471))*X+(-33793)))*Y+((5693)*X^3))*A+(((((34390)*X+(81653))*X)*Y+(((74979)*X+(-65027))*X))*Y+(((((4293)*X+(-1767))*X+(22598))*X+(-28100))*X^2)))*A+((((((-1620)*X+(4080))*X)*Y+((((8073)*X+(21176))*X+(88882))*X))*Y+(((((18333)*X+(13246))*X+(110304))*X+(-180129))*X))*Y+((((((-8586)*X+(7827))*X+(-69735))*X+(101570))*X+(-33793))*X))))
compact_certificate theorem row3_88_identity (B A Y X : ℂ) :
  (((-54)*A+(-16)))*row2_46 B A Y X+
  (((-108)*A+(-108)))*row2_51 B A Y X+
  (((-9720)*B+((-193752)*A+((-17280)*Y+(-288468)))))*row2_53 B A Y X+
  (((-106272)*X+(197316)))*row2_54 B A Y X+
  (((-54)*A+((108)*X)))*row2_41 B A Y X+
  (((-58320)*A))*row2_44 B A Y X+
  (((27)*X))*row2_37 B A Y X+
  (((27)*X))*row2_42 B A Y X+
  (((2592)*X))*row2_48 B A Y X=((4))*row3_88 B A Y X := by
  simp only [row2_46, row2_51, row2_53, row2_54, row2_41, row2_44, row2_37, row2_42, row2_48, row3_88] <;> ring
compact_certificate theorem row3_88_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_88 B A Y X=0 := by
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_88_identity B A Y X).symm
  have hz : ((4))*row3_88 B A Y X=0 := by
    simpa only [z2_46, z2_51, z2_53, z2_54, z2_41, z2_44, z2_37, z2_42, z2_48,mul_zero,add_zero] using he
  have hu : ((4):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_88_zero
compact_certificate def row3_89 (B A Y X : ℂ) : ℂ := (((((180)*Y)*A+((((720)*X+(-180))*X)*Y+(((-180)*X+(180))*X^2)))*A+((((-180)*X)*Y+(((-180)*X+(540))*X^2))*Y+((((360)*X+(-540))*X+(180))*X)))*B+(((((1080)*X^3)*A+((((-224)*X+(-4))*Y+(((3084)*X+(-3535))*X+(-166)))*Y+(((920)*X+(1080))*X^2)))*A+(((((160)*X+(20))*X)*Y+(((2571)*X+(6406))*X))*Y+((((159)*X+(-4249))*X+(2914))*X^2)))*A+(((((-60)*X)*Y+(((299)*X+(-330))*X))*Y+((((679)*X+(-870))*X+(9516))*X))*Y+(((((-318)*X+(-3663))*X+(2243))*X+(-166))*X))))
compact_certificate theorem row3_89_identity (B A Y X : ℂ) :
  (((2)*A+(-2)))*row2_46 B A Y X+
  (((4)*A+(4)))*row2_51 B A Y X+
  (((360)*B+((-1080)*A+(1080))))*row2_53 B A Y X+
  (((1776)*X+(-1212)))*row2_54 B A Y X+
  (((2)*A))*row2_41 B A Y X+
  (((-1)*X))*row2_37 B A Y X+
  (((-1)*X))*row2_42 B A Y X+
  (((-96)*X))*row2_48 B A Y X=((2))*row3_89 B A Y X := by
  simp only [row2_46, row2_51, row2_53, row2_54, row2_41, row2_37, row2_42, row2_48, row3_89] <;> ring
compact_certificate theorem row3_89_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_89 B A Y X=0 := by
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_89_identity B A Y X).symm
  have hz : ((2))*row3_89 B A Y X=0 := by
    simpa only [z2_46, z2_51, z2_53, z2_54, z2_41, z2_37, z2_42, z2_48,mul_zero,add_zero] using he
  have hu : ((2):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_89_zero
compact_certificate def row3_90 (B A Y X : ℂ) : ℂ := (((((1)*Y)*A+((((1)*X^2+(-1))*X)*Y+(((-1)*X+(1))*X^2)))*A+((((-1)*X)*Y+((-1)*X^2))*Y+((((2)*X+(-3))*X+(1))*X)))*B)
compact_certificate theorem row3_90_identity (B A Y X : ℂ) :
  (((1)*B))*row2_53 B A Y X=((1))*row3_90 B A Y X := by
  simp only [row2_53, row3_90] <;> ring
compact_certificate theorem row3_90_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_90 B A Y X=0 := by
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_90_identity B A Y X).symm
  have hz : ((1))*row3_90 B A Y X=0 := by
    simpa only [z2_53,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_90_zero
compact_certificate def row3_91 (B A Y X : ℂ) : ℂ := ((((((1)*X^2+(-1))*X+(-1))*Y+((-1)*X^3))*A+((((-1)*X)*Y+(((-1)*X+(1))*X))*Y+(((2)*X+(-2))*X^2)))*A+(((1)*X)*Y+(((2)*X+(-1))*X)))
compact_certificate theorem row3_91_identity (B A Y X : ℂ) :
  ((-1))*row2_54 B A Y X+
  (((1)*A))*row2_53 B A Y X=((1))*row3_91 B A Y X := by
  simp only [row2_54, row2_53, row3_91] <;> ring
compact_certificate theorem row3_91_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_91 B A Y X=0 := by
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_91_identity B A Y X).symm
  have hz : ((1))*row3_91 B A Y X=0 := by
    simpa only [z2_54, z2_53,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_91_zero
compact_certificate def row3_92 (B A Y X : ℂ) : ℂ := (((((1)*Y+(1))*Y)*A+(((((1)*X^2+(-1))*X)*Y+(((1)*X+(-1))*X))*Y+(((-1)*X+(1))*X^2)))*A+(((((-1)*X)*Y+(((-1)*X+(-1))*X))*Y+((((2)*X+(-4))*X+(1))*X))*Y+((((2)*X+(-3))*X+(1))*X)))
compact_certificate theorem row3_92_identity (B A Y X : ℂ) :
  (((1)*Y+(1)))*row2_53 B A Y X=((1))*row3_92 B A Y X := by
  simp only [row2_53, row3_92] <;> ring
compact_certificate theorem row3_92_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_92 B A Y X=0 := by
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_92_identity B A Y X).symm
  have hz : ((1))*row3_92 B A Y X=0 := by
    simpa only [z2_53,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_92_zero
compact_certificate def row3_93 (B A Y X : ℂ) : ℂ := (((((5022)*Y)*A+((((12312)*X+(-5022))*X)*Y+((((2592)*X+(-5022))*X+(5022))*X^2)))*A+(((((2592)*X+(-5022))*X)*Y+(((-9558)*X+(40986))*X^2))*Y+(((((-5184)*X+(12636))*X+(-15066))*X+(5022))*X)))*B+((((((-16584)*X+(6928))*Y+(((-36525)*X+(-122015))*X+(53557)))*Y+((47443)*X^3))*A+(((((-36982)*X+(-106709))*X)*Y+(((9261)*X+(-118033))*X))*Y+(((((-4293)*X+(-825))*X+(-77354))*X+(101000))*X^2)))*A+((((((-972)*X+(-6672))*X)*Y+((((-13257)*X+(-21176))*X+(-130246))*X))*Y+(((((-18333)*X+(-5470))*X+(-131364))*X+(688161))*X))*Y+((((((8586)*X+(-2643))*X+(-35889))*X+(-89582))*X+(53557))*X))))
compact_certificate theorem row3_93_identity (B A Y X : ℂ) :
  ((-3))*row2_17 B A Y X+
  (((270)*A+(-728)))*row2_46 B A Y X+
  (((540)*A+(-1485)))*row2_51 B A Y X+
  (((-132840)*B+((-249480)*A+((43200)*Y+(1126170)))))*row2_53 B A Y X+
  (((531360)*X+(231660)))*row2_54 B A Y X+
  (((270)*A+((-540)*X)))*row2_41 B A Y X+
  (((291600)*A))*row2_44 B A Y X+
  (((540)*X))*row2_36 B A Y X+
  (((-357)*X))*row2_37 B A Y X+
  (((-87)*X))*row2_42 B A Y X+
  (((-12960)*X))*row2_48 B A Y X=((10))*row3_93 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_41, row2_44, row2_36, row2_37, row2_42, row2_48, row3_93] <;> ring
compact_certificate theorem row3_93_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_93 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_93_identity B A Y X).symm
  have hz : ((10))*row3_93 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_41, z2_44, z2_36, z2_37, z2_42, z2_48,mul_zero,add_zero] using he
  have hu : ((10):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_93_zero
compact_certificate def row3_94 (B A Y X : ℂ) : ℂ := ((((((-96)*X+(4))*Y+(((-1524)*X+(-95))*X+(706)))*Y+(((540)*X+(-350))*X^3))*A+(((((-160)*X+(-1250))*X)*Y+(((-2241)*X+(-706))*X))*Y+((((-699)*X+(439))*X+(356))*X^2)))*A+(((((60)*X)*Y+(((-299)*X+(-1120))*X))*Y+((((-1219)*X+(-900))*X+(354))*X))*Y+(((((-762)*X+(1983))*X+(-2213))*X+(706))*X)))
compact_certificate theorem row3_94_identity (B A Y X : ℂ) :
  ((1))*row2_46 B A Y X=((1))*row3_94 B A Y X := by
  simp only [row2_46, row3_94] <;> ring
compact_certificate theorem row3_94_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_94 B A Y X=0 := by
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_94_identity B A Y X).symm
  have hz : ((1))*row3_94 B A Y X=0 := by
    simpa only [z2_46,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_94_zero
compact_certificate def row3_95 (B A Y X : ℂ) : ℂ := (((((85950)*Y)*A+((((-122760)*X+(-85950))*X)*Y+(((-85950)*X+(85950))*X^2)))*A+((((-85950)*X)*Y+((((38880)*X+(-124830))*X+(-208710))*X^2))*Y+((((171900)*X+(-257850))*X+(85950))*X)))*B+((((((-98824)*X+(-107504))*Y+(((1456779)*X+(362785))*X+(74449)))*Y+((-187565)*X^3))*A+(((((25920)*X)*Y+(((724010)*X+(1221115))*X))*Y+(((378381)*X+(-1322509))*X))*Y+(((((64395)*X+(154839))*X+(-236774))*X+(-113116))*X^2)))*A+((((((14580)*X+(72240))*X)*Y+((((198855)*X+(611464))*X+(393870))*X))*Y+(((((274995)*X+(154754))*X+(-1254720))*X+(-2068239))*X))*Y+((((((-128790)*X+(-245283))*X+(1378647))*X+(-760802))*X+(74449))*X))))
compact_certificate theorem row3_95_identity (B A Y X : ℂ) :
  ((45))*row2_17 B A Y X+
  (((12782)*A+(6280)))*row2_46 B A Y X+
  (((-7460)*A+(39115)))*row2_51 B A Y X+
  (((3605400)*B+((-1640520)*A+((-648000)*Y+(-3742470)))))*row2_53 B A Y X+
  (((-17280)*Y+((-8442240)*X+(-9673620))))*row2_54 B A Y X+
  (((414720)*A))*row2_39 B A Y X+
  (((8462)*A+((9492)*X)))*row2_41 B A Y X+
  (((-5125680)*A))*row2_44 B A Y X+
  (((-768)*X))*row2_33 B A Y X+
  (((-8100)*X))*row2_36 B A Y X+
  (((-901)*X))*row2_37 B A Y X+
  (((-7111)*X))*row2_42 B A Y X+
  (((179040)*X))*row2_48 B A Y X=((10))*row3_95 B A Y X := by
  simp only [row2_17, row2_46, row2_51, row2_53, row2_54, row2_39, row2_41, row2_44, row2_33, row2_36, row2_37, row2_42, row2_48, row3_95] <;> ring
compact_certificate theorem row3_95_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_95 B A Y X=0 := by
  have z2_17 := row2_17_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_46 := row2_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_39 := row2_39_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_41 := row2_41_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_44 := row2_44_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_33 := row2_33_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_36 := row2_36_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_37 := row2_37_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_42 := row2_42_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z2_48 := row2_48_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_95_identity B A Y X).symm
  have hz : ((10))*row3_95 B A Y X=0 := by
    simpa only [z2_17, z2_46, z2_51, z2_53, z2_54, z2_39, z2_41, z2_44, z2_33, z2_36, z2_37, z2_42, z2_48,mul_zero,add_zero] using he
  have hu : ((10):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_95_zero
compact_certificate def row3_97 (B A Y X : ℂ) : ℂ := ((((((1)*Y)*A+((1)*Y+((1)*X^2)))*A+(((-1)*X)*Y+(((-1)*X+(1))*X)))*A+(((-1)*X)*Y+(((-2)*X+(1))*X)))*B)
compact_certificate theorem row3_97_identity (B A Y X : ℂ) :
  (((1)*B))*row2_54 B A Y X=((1))*row3_97 B A Y X := by
  simp only [row2_54, row3_97] <;> ring
compact_certificate theorem row3_97_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_97 B A Y X=0 := by
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_97_identity B A Y X).symm
  have hz : ((1))*row3_97 B A Y X=0 := by
    simpa only [z2_54,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_97_zero

compact_certificate def row3_98 (B A Y X : ℂ) : ℂ := ((((((1)*Y)*A+((1)*X^2))*A+(((-1)*X+(-1))*Y+(((-2)*X+(1))*X)))*A+((-1)*X^2))*A+(((1)*X)*Y+(((2)*X+(-1))*X)))
compact_certificate theorem row3_98_identity (B A Y X : ℂ) :
  (((1)*A+(-1)))*row2_54 B A Y X=((1))*row3_98 B A Y X := by
  simp only [row2_54, row3_98] <;> ring
compact_certificate theorem row3_98_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_98 B A Y X=0 := by
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_98_identity B A Y X).symm
  have hz : ((1))*row3_98 B A Y X=0 := by
    simpa only [z2_54,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_98_zero
compact_certificate def row3_100 (B A Y X : ℂ) : ℂ := ((((((24)*X)*Y)*A+((24)*X^3))*A+((((-90)*X+(336))*X^2)*Y+(((-48)*X+(24))*X^2)))*B+((((((-270)*X+(-444))*X+(303))*Y+((540)*X^3))*A+((((-160)*X)*Y+(((780)*X+(-1815))*X))*Y+(((-699)*X+(843))*X^2)))*A+((((-455)*X)*Y+(((-171)*X+(4632))*X))*Y+((((-762)*X+(-225))*X+(303))*X))))
compact_certificate theorem row3_100_identity (B A Y X : ℂ) :
  ((1))*row2_51 B A Y X=((1))*row3_100 B A Y X := by
  simp only [row2_51, row3_100] <;> ring
compact_certificate theorem row3_100_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_100 B A Y X=0 := by
  have z2_51 := row2_51_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_100_identity B A Y X).symm
  have hz : ((1))*row3_100 B A Y X=0 := by
    simpa only [z2_51,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_100_zero
compact_certificate def row3_102 (B A Y X : ℂ) : ℂ := ((((1)*Y)*A+((((1)*X^2+(-1))*X)*Y+(((-1)*X+(1))*X^2)))*A+((((-1)*X)*Y+((-1)*X^2))*Y+((((2)*X+(-3))*X+(1))*X)))
compact_certificate theorem row3_102_identity (B A Y X : ℂ) :
  ((1))*row2_53 B A Y X=((1))*row3_102 B A Y X := by
  simp only [row2_53, row3_102] <;> ring
compact_certificate theorem row3_102_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_102 B A Y X=0 := by
  have z2_53 := row2_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_102_identity B A Y X).symm
  have hz : ((1))*row3_102 B A Y X=0 := by
    simpa only [z2_53,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_102_zero
compact_certificate def row3_103 (B A Y X : ℂ) : ℂ := (((((1)*Y)*A+((1)*Y+((1)*X^2)))*A+(((-1)*X)*Y+(((-1)*X+(1))*X)))*A+(((-1)*X)*Y+(((-2)*X+(1))*X)))
compact_certificate theorem row3_103_identity (B A Y X : ℂ) :
  ((1))*row2_54 B A Y X=((1))*row3_103 B A Y X := by
  simp only [row2_54, row3_103] <;> ring
compact_certificate theorem row3_103_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row3_103 B A Y X=0 := by
  have z2_54 := row2_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row3_103_identity B A Y X).symm
  have hz : ((1))*row3_103 B A Y X=0 := by
    simpa only [z2_54,mul_zero,add_zero] using he
  have hu : ((1):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_103_zero
compact_certificate def row4_30 (B A Y X : ℂ) : ℂ := (((((((11549493484791644160)*X^2)*Y)*A^2+(((52521528626979333120)*Y+(12015094103603410245570))*Y))*A+((((-175479450814067696640)*X)*Y+(((-2698255688005759424760)*X+(-12015094103603410245570))*X))*Y+(((-12015094103603410245570)*X+(12015094103603410245570))*X^2)))*A+(((((-42272217552055034880)*X)*Y+(((-1283471900255702476800)*X+(-12025343414678334543810))*X))*Y+((((2138332789833095784510)*X+(-29065960576250898899130))*X+(52521528626979333120))*X))*Y+((((24030188207206820491140)*X+(-36045282310810230736710))*X+(12015094103603410245570))*X)))*B+((((((-1274796967889996640)*Y+((-28330049096973326120688)*X+(-8675067921763604746688)))*Y+(((225350826305227317401253)*X+(-45736737666160934658545))*X+(-40143988599241979717657)))*Y+((-56098112771696556771875)*X^3))*A+(((((3765784210950842938800)*X)*Y+(((38599139293049864091470)*X+(86366568407902106134885))*X))*Y+(((-90855846757394140786173)*X+(94136458900196736000917))*X))*Y+(((((1070245119923589843045)*X+(23295136652801567951673))*X+(57350931710761073854462))*X+(-96242101370938536489532))*X^2)))*A+(((((((17263839069559526400)*X+(-37710988385047063200))*X)*Y+(((5247959025096725112180)*X+(2752888914154499784720))*X))*Y+((((14775075810421546568625)*X+(36327103564532165646808))*X+(32555864353687761196730))*X))*Y+((((((138110712556476211200)*X+(6979216424617512023085))*X+(45120390004648039999958))*X+(32699649764809781107920))*X+(-220928397971443423997073))*X))*Y+((((((-2140490239847179686090)*X+(-45520028185679546060301))*X+(132985724318065647330249))*X+(25442683365851919746026))*X+(-40143988599241979717657))*X))))
compact_certificate theorem row4_30_identity (B A Y X : ℂ) :
  (((1085572347468772187013120)*B+((-117997132791386573853327360)*A+((29231825268153378268263312)*Y+((-2857001867946627921718272)*X+(-171192694580541309169998720))))))*row3_94 B A Y X+
  (((16369658202223974769920)*A+((-398871124297795587237120)*Y+(1125938519874708552645120))))*row3_95 B A Y X+
  (((382509231364237344452048160)*A+((63882173688139975442273280)*Y+((363562151055433752318750720)*X+(-9820586899118870822550240)))))*row3_100 B A Y X+
  (((-3920451160734871404912112320)*B+((818586153372985006652138188800)*A+((271174441600097648202015005760)*Y+((43230586865167625502572395200)*X+(378450678328375074265100959200))))))*row3_102 B A Y X+
  (((379950321614070265454592000)*B+((-6707367628773649275248640)*Y+((342157252593262347412665004800)*X+(-652505292676173682328409571680)))))*row3_103 B A Y X+
  (((-28691540056183357440)*A+((18596368554933657600)*X)))*row3_65 B A Y X+
  (((-3012611705899252531200)*A))*row3_70 B A Y X+
  (((-84917990206442582553600)*A+((39116929141729684154880)*X)))*row3_84 B A Y X+
  (((170983642015132499404800)*A+((-101824745846956553548800)*X)))*row3_87 B A Y X+
  (((3369046099979870538543360)*A+((-312935433133837473239040)*Y+((15208909625181524742178560)*X))))*row3_88 B A Y X+
  (((-690877029099545571096576000)*A+((3305612646706990681479168000)*Y+((-4042534038552393910297804800)*X))))*row3_90 B A Y X+
  (((220842452363107398700722986880)*A+((-39421493748470512131726827520)*Y+((-15785185644802824264862188480)*X))))*row3_91 B A Y X+
  (((-141795823149125058355200)*A+((1314074740605681238905600)*Y+((-45189175588488787968000)*X))))*row3_93 B A Y X+
  (((-123088565164473723840743)*Y))*row3_46 B A Y X+
  (((-658332194026432660842115)*Y))*row3_58 B A Y X+
  (((288145603288099933532282880)*Y))*row3_72 B A Y X+
  (((157147640306814728549601648)*Y+((58998566395693286926663680)*X)))*row3_89 B A Y X+
  (((394796727152061216797491200)*Y))*row3_92 B A Y X+
  (((-989814121521515637542830080)*Y+((-9180221552741696266849155840)*X)))*row3_97 B A Y X+
  (((4923542606578948953629720)*X))*row3_40 B A Y X+
  (((14345770028091678720)*X))*row3_45 B A Y X+
  (((1053331510442292257347384)*X))*row3_54 B A Y X+
  (((7172885014045839360)*X))*row3_57 B A Y X+
  (((-84729704228416477440000)*X))*row3_67 B A Y X+
  (((-288145603288099933532282880)*X))*row3_69 B A Y X+
  (((679343921651540660428800)*X))*row3_78 B A Y X+
  (((-3462418750806433112947200)*X))*row3_82 B A Y X+
  (((-8732567491147824435904389120)*X))*row3_83 B A Y X+
  (((-29865562535191010054400)*X))*row3_85 B A Y X+
  (((-723262784989754269507949568)*X))*row3_86 B A Y X=((7823520))*row4_30 B A Y X := by
  simp only [row3_94, row3_95, row3_100, row3_102, row3_103, row3_65, row3_70, row3_84, row3_87, row3_88, row3_90, row3_91, row3_93, row3_46, row3_58, row3_72, row3_89, row3_92, row3_97, row3_40, row3_45, row3_54, row3_57, row3_67, row3_69, row3_78, row3_82, row3_83, row3_85, row3_86, row4_30] <;> ring
compact_certificate theorem row4_30_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row4_30 B A Y X=0 := by
  have z3_94 := row3_94_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_95 := row3_95_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_100 := row3_100_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_102 := row3_102_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_103 := row3_103_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_65 := row3_65_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_70 := row3_70_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_84 := row3_84_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_87 := row3_87_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_88 := row3_88_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_90 := row3_90_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_91 := row3_91_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_93 := row3_93_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_46 := row3_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_58 := row3_58_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_72 := row3_72_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_89 := row3_89_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_92 := row3_92_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_97 := row3_97_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_40 := row3_40_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_45 := row3_45_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_54 := row3_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_57 := row3_57_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_67 := row3_67_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_69 := row3_69_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_78 := row3_78_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_82 := row3_82_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_83 := row3_83_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_85 := row3_85_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_86 := row3_86_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row4_30_identity B A Y X).symm
  have hz : ((7823520))*row4_30 B A Y X=0 := by
    simpa only [z3_94, z3_95, z3_100, z3_102, z3_103, z3_65, z3_70, z3_84, z3_87, z3_88, z3_90, z3_91, z3_93, z3_46, z3_58, z3_72, z3_89, z3_92, z3_97, z3_40, z3_45, z3_54, z3_57, z3_67, z3_69, z3_78, z3_82, z3_83, z3_85, z3_86,mul_zero,add_zero] using he
  have hu : ((7823520):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_30_zero
compact_certificate def row4_38 (B A Y X : ℂ) : ℂ := ((((((-329160564316561858560)*Y+((-7699662323194429440)*X^3))*A+((((-7699662323194429440)*X)*Y+((329160564316561858560)*X))*Y+(((344559888962950717440)*X+(-336860226639756288000))*X^2)))*A+(((((30798649292777717760)*X+(321460901993367429120))*X)*Y+((((-69296960908749864960)*X+(806539628354616483840))*X+(7699662323194429440))*X))*Y+((((-658321128633123717120)*X+(987481692949685575680))*X+(-329160564316561858560))*X)))*B+((((((46197973939166576640)*X^3)*A+((46197973939166576640)*X^2))*A+(((3413152696598572354560)*Y+(681549368110420962668670))*Y+((92395947878333153280)*X^2)))*A+((((-11219178394637202263040)*X)*Y+(((-156869225739381334431240)*X+(-684076140629482601263230))*X))*Y+(((-680771702215778325295230)*X+(681734160006177628975230))*X^2)))*A+(((((-2825361313255974620160)*X)*Y+(((-74368794264077571655680)*X+(-683015776516643635851390))*X))*Y+((((119449281070453244092290)*X+(-1648474876639932984465030))*X+(10807395080972956093440))*X))*Y+((((1360804236848529985364220)*X+(-2043500854645106918019450))*X+(681549368110420962668670))*X))))*B+((((((440194014614767021920)*Y+((-1576897799530432166144784)*X+(-502338890343013395371584)))*Y+(((12557029758207175015622139)*X+(-2411045823675143515808815))*X+(-2275974658925187272918791)))*Y+((-3113747702026213905867325)*X^3))*A+(((((204339349639191947161680)*X)*Y+(((2227463718307022025135730)*X+(4952035443830924887001915))*X))*Y+(((-5229962573095327367834019)*X+(5175354638766858012343051))*X))*Y+(((((71928131103542508583995)*X+(1283968079980105886270439))*X+(3219181807863789634628546))*X+(-5389722360951401178786116))*X^2)))*A+(((((((928463820849716751360)*X+(-2477663833443064691040))*X)*Y+(((291914973434620207742220)*X+(167107570427193082425840))*X))*Y+((((850427405929227054442095)*X+(2045120195976269015052584))*X+(1922642862787873234605190))*X))*Y+((((((7427710566797734010880)*X+(430303910498689650786675))*X+(2490377266999328667458794))*X+(1972403595384597119507760))*X+(-12598483677881086094699919))*X))*Y+((((((-143856262207085017167990)*X+(-2496008028856669263956883))*X+(7300595272357382240482647))*X+(1543635721661736368731478))*X+(-2275974658925187272918791))*X))))
compact_certificate theorem row4_38_identity (B A Y X : ℂ) :
  (((322680072900565738619320320)*B+((-42527347690877344057660369920)*A+((-3411070544677047596250572016)*Y+((-1228021645820117789076585984)*X+(-63513893971115810402479689600))))))*row3_94 B A Y X+
  (((-205402959414873344845440)*B+((23820610627909032033170880)*A+((-136228101981154956832443840)*Y+(447329426104187883665902080)))))*row3_95 B A Y X+
  (((8270369595788042744087040)*B+((155776372082794984106121564960)*A+((21636195154673732489710483200)*Y+((153286966759692244508876885760)*X+(-3435103457031172531667781600))))))*row3_100 B A Y X+
  (((-1494499430239025271946858964160)*B+((322470714301420750753504225536000)*A+((102145786651661774661226861093440)*Y+((4025033523574804860070992580800)*X+(140730193919751572950894978863840))))))*row3_102 B A Y X+
  (((155785076603350962271106273280)*B+((241434599885188241006349250560)*Y+((139840384201732961782454304956160)*X+(-252794709717854717214671062485600)))))*row3_103 B A Y X+
  (((9895219029532924329600)*B+((-60985807991194998666024000)*A+((450421229946396437549352000)*Y+((41152591957829720970988800)*X)))))*row3_93 B A Y X+
  (((-421669235251306578287001600)*B+((-337420017526222546301431664640)*Y+((-3738632929987079618546917559040)*X))))*row3_97 B A Y X+
  (((200840780393283502080)*A+((-791146801783587188160)*X)))*row3_57 B A Y X+
  (((3164587207134348752640)*A+((-14828486925246418684800)*X)))*row3_65 B A Y X+
  (((2402214881889919826937600)*A))*row3_70 B A Y X+
  (((-408899500484607318948480)*A+((-366032322266759182540800)*X)))*row3_79 B A Y X+
  (((-28922802165921171574828800)*A+((13658855571415440751579200)*X)))*row3_84 B A Y X+
  (((57735088105988431879718400)*A+((-34963795298254260378873600)*X)))*row3_87 B A Y X+
  (((1183868351181538241494187520)*A+((-109270844571323526012633600)*Y+((5124173081108466602102817600)*X))))*row3_88 B A Y X+
  (((-522371100437398279375123046400)*A+((1161602885078608736625648537600)*Y+((-2093637169234162731577604198400)*X))))*row3_90 B A Y X+
  (((89572576652674879636778334860160)*A+((-13281856626233145432650503219200)*Y+((1841978094125605701975308888640)*X))))*row3_91 B A Y X+
  (((-52175846000750099853351151)*Y))*row3_46 B A Y X+
  (((-275527413012476838711104555)*Y))*row3_58 B A Y X+
  (((81185585525684118194677056000)*Y))*row3_72 B A Y X+
  (((66683243162853577216834508016)*Y+((21263673845438672028830184960)*X)))*row3_89 B A Y X+
  (((141280103029660680638380032000)*Y))*row3_92 B A Y X+
  (((2087033840030003994134046040)*X))*row3_40 B A Y X+
  (((440843860819962941937767288)*X))*row3_54 B A Y X+
  (((67562293553153995132620000)*X))*row3_67 B A Y X+
  (((-81185585525684118194677056000)*X))*row3_69 B A Y X+
  (((1884208898233070525714595840)*X))*row3_73 B A Y X+
  (((231382417327369372598630400)*X))*row3_78 B A Y X+
  (((-1169135534146265745564297600)*X))*row3_82 B A Y X+
  (((-3068586766262547121952934051840)*X))*row3_83 B A Y X+
  (((17424603318849366591180000)*X))*row3_85 B A Y X+
  (((-299241628275105079686962228736)*X))*row3_86 B A Y X=((54764640))*row4_38 B A Y X := by
  simp only [row3_94, row3_95, row3_100, row3_102, row3_103, row3_93, row3_97, row3_57, row3_65, row3_70, row3_79, row3_84, row3_87, row3_88, row3_90, row3_91, row3_46, row3_58, row3_72, row3_89, row3_92, row3_40, row3_54, row3_67, row3_69, row3_73, row3_78, row3_82, row3_83, row3_85, row3_86, row4_38] <;> ring
compact_certificate theorem row4_38_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row4_38 B A Y X=0 := by
  have z3_94 := row3_94_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_95 := row3_95_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_100 := row3_100_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_102 := row3_102_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_103 := row3_103_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_93 := row3_93_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_97 := row3_97_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_57 := row3_57_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_65 := row3_65_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_70 := row3_70_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_79 := row3_79_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_84 := row3_84_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_87 := row3_87_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_88 := row3_88_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_90 := row3_90_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_91 := row3_91_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_46 := row3_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_58 := row3_58_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_72 := row3_72_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_89 := row3_89_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_92 := row3_92_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_40 := row3_40_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_54 := row3_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_67 := row3_67_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_69 := row3_69_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_73 := row3_73_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_78 := row3_78_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_82 := row3_82_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_83 := row3_83_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_85 := row3_85_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_86 := row3_86_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row4_38_identity B A Y X).symm
  have hz : ((54764640))*row4_38 B A Y X=0 := by
    simpa only [z3_94, z3_95, z3_100, z3_102, z3_103, z3_93, z3_97, z3_57, z3_65, z3_70, z3_79, z3_84, z3_87, z3_88, z3_90, z3_91, z3_46, z3_58, z3_72, z3_89, z3_92, z3_40, z3_54, z3_67, z3_69, z3_73, z3_78, z3_82, z3_83, z3_85, z3_86,mul_zero,add_zero] using he
  have hu : ((54764640):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_38_zero
compact_certificate def row4_41 (B A Y X : ℂ) : ℂ := (((((((142586339318415360)*X^3+(-106939754488811520))*Y+((-142586339318415360)*X^3))*A+((((-142586339318415360)*X)*Y+((106939754488811520)*X))*Y+(((392112433125642240)*X+(-249526093807226880))*X^2)))*A+((((-35646584829603840)*X)*Y+((((-570345357273661440)*X+(2103148504946626560))*X+(142586339318415360))*X))*Y+((((-213879508977623040)*X+(320819263466434560))*X+(-106939754488811520))*X)))*B+(((((193011570519100416)*Y+(-58561327715150018790))*Y)*A+((((-3366934752265989120)*X)*Y+(((92744319780734282856)*X+(51028016121160407270))*X))*Y+(((66308518818117253350)*X+(-58561327715150018790))*X^2)))*A+(((((-334650815062133760)*X)*Y+(((8183214674137866240)*X+(53870874349457864934))*X))*Y+((((-56049783408425937690)*X+(334028307126951793998))*X+(33415628631709879296))*X))*Y+((((-132617037636234506700)*X+(183431174248417290930))*X+(-58561327715150018790))*X))))*B+((((((-27265534644134880)*Y+((56046461099147579088)*X+(80025039574621616960)))*Y+(((-1640556794261298609663)*X+(-385763334654931832413))*X+(590682386029049832347)))*Y+((480625662250120457945)*X^3))*A+(((((-21481801905401260560)*X)*Y+(((-494677994519424516170)*X+(-1231656529864871191615))*X))*Y+(((160097846098484908935)*X+(-658541509739116628687))*X))*Y+(((((-35184285537678266175)*X+(-135164291140572397563))*X+(-738700454887890730330))*X+(1071308048279170290292))*X^2)))*A+(((((((220810789361157120)*X+(-71000585722075680))*X)*Y+(((-21182542281663846300)*X+(-37578878347447080240))*X))*Y+((((-140587794568507648995)*X+(-380755779863299969288))*X+(-998225482944796980302))*X))*Y+((((((1766486314889256960)*X+(-164478868630792137495))*X+(-417997257989555105378))*X+(-1050188130617304153456))*X+(4116543817581548740995))*X))*Y+((((((70368571075356532350)*X+(235144296743466528951))*X+(-580266030365272768683))*X+(-958813902445749479134))*X+(590682386029049832347))*X))))
compact_certificate theorem row4_41_identity (B A Y X : ℂ) :
  (((-23116795698272876531712)*B+((973842086633881506048000)*A+((-271431807626269283763600)*Y+((1161842994732464474112)*X+(2317305950894466117806976))))))*row3_94 B A Y X+
  (((2420848692240470784)*B+((-754795329243053523840)*A+((4513168693379485033344)*Y+(-10174113402688928189952)))))*row3_95 B A Y X+
  (((65333864506185825518592)*B+((-1896716514763658571914016)*A+((-617812809072701398912512)*Y+((-3594644797019524958163456)*X+(5520839869224492806651616))))))*row3_100 B A Y X+
  (((276804870312534892703292096)*B+((-3235801512802377972202536960)*A+((-2751487398069623371929531456)*Y+((-398352178130722479368821440)*X+(1797693678530329191969496608))))))*row3_102 B A Y X+
  (((-49358563247701288299257856)*B+((23305755876581328289726464)*Y+((-1119639820705855889996581632)*X+(2120628053524333145365837152)))))*row3_103 B A Y X+
  (((36312730383607061760)*B+((5286794400405837129600)*A+((-15989481854113457692800)*Y+((-2025443405841193889280)*X)))))*row3_93 B A Y X+
  (((-1561737908338172512174080)*B+((11324957342578538507476992)*Y+((45521196354327805725936384)*X))))*row3_97 B A Y X+
  (((1561737908338172512174080)*A))*row3_59 B A Y X+
  (((-179322125351145984)*A+((833515804872919296)*X)))*row3_65 B A Y X+
  (((-135029560389412925952)*A))*row3_70 B A Y X+
  (((21787638230164237056)*A))*row3_79 B A Y X+
  (((970573912554727964160)*A+((-176587471706692943232)*X)))*row3_84 B A Y X+
  (((-1933974940095410088960)*A+((673032015675789442560)*X)))*row3_87 B A Y X+
  (((-38614140468796022818560)*A+((1412699773653543545856)*Y+((-177714250118880982498944)*X))))*row3_88 B A Y X+
  (((19737533281666764754944000)*A+((-27397755366340401106329600)*Y+((70791179366832003346636800)*X))))*row3_90 B A Y X+
  (((-955412487242646160855052160)*A+((460635336308139506637262848)*Y+((146573176118185413232344000)*X))))*row3_91 B A Y X+
  (((1508441260078484536519)*Y))*row3_46 B A Y X+
  (((8027493256669786664675)*Y))*row3_58 B A Y X+
  (((-7584241952295844897692672)*Y))*row3_72 B A Y X+
  (((-1943936861490220011010416)*Y+((-486921043316940753024000)*X)))*row3_89 B A Y X+
  (((-6041282606501139214663680)*Y))*row3_92 B A Y X+
  (((-60337650403139381460760)*X))*row3_40 B A Y X+
  (((-12843989210671658663480)*X))*row3_54 B A Y X+
  (((44830531337786496)*X))*row3_57 B A Y X+
  (((-3797706385952238542400)*X))*row3_67 B A Y X+
  (((7584241952295844897692672)*X))*row3_69 B A Y X+
  (((-100397436964596804354048)*X))*row3_73 B A Y X+
  (((-7764591300437823713280)*X))*row3_78 B A Y X+
  (((39162992536932054301440)*X))*row3_82 B A Y X+
  (((100087852095119291145707520)*X))*row3_83 B A Y X+
  (((-811801617055210048320)*X))*row3_85 B A Y X+
  (((5657156106763118097678336)*X))*row3_86 B A Y X=((10952928))*row4_41 B A Y X := by
  simp only [row3_94, row3_95, row3_100, row3_102, row3_103, row3_93, row3_97, row3_59, row3_65, row3_70, row3_79, row3_84, row3_87, row3_88, row3_90, row3_91, row3_46, row3_58, row3_72, row3_89, row3_92, row3_40, row3_54, row3_57, row3_67, row3_69, row3_73, row3_78, row3_82, row3_83, row3_85, row3_86, row4_41] <;> ring
compact_certificate theorem row4_41_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row4_41 B A Y X=0 := by
  have z3_94 := row3_94_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_95 := row3_95_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_100 := row3_100_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_102 := row3_102_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_103 := row3_103_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_93 := row3_93_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_97 := row3_97_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_59 := row3_59_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_65 := row3_65_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_70 := row3_70_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_79 := row3_79_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_84 := row3_84_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_87 := row3_87_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_88 := row3_88_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_90 := row3_90_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_91 := row3_91_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_46 := row3_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_58 := row3_58_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_72 := row3_72_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_89 := row3_89_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_92 := row3_92_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_40 := row3_40_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_54 := row3_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_57 := row3_57_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_67 := row3_67_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_69 := row3_69_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_73 := row3_73_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_78 := row3_78_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_82 := row3_82_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_83 := row3_83_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_85 := row3_85_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_86 := row3_86_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row4_41_identity B A Y X).symm
  have hz : ((10952928))*row4_41 B A Y X=0 := by
    simpa only [z3_94, z3_95, z3_100, z3_102, z3_103, z3_93, z3_97, z3_59, z3_65, z3_70, z3_79, z3_84, z3_87, z3_88, z3_90, z3_91, z3_46, z3_58, z3_72, z3_89, z3_92, z3_40, z3_54, z3_57, z3_67, z3_69, z3_73, z3_78, z3_82, z3_83, z3_85, z3_86,mul_zero,add_zero] using he
  have hu : ((10952928):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_41_zero
compact_certificate def row4_50 (B A Y X : ℂ) : ℂ := (((((((28232095185046241280)*Y+(11374005347675504455680))*Y+(((346484804543749324800)*X+(-224573484426504192000))*X^3))*A+((((-827713699743401164800)*X)*Y+((-11374005347675504455680)*X))*Y+(((-10578373574278746746880)*X+(11149431863249000263680))*X^2)))*A+(((((12832770538657382400)*X)*Y+((((-256655410773147648000)*X+(218157099157175500800))*X+(-11639643697825712271360))*X))*Y+((((-1090143857258944634880)*X+(-16129830109301930373120))*X+(252805579611550433280))*X))*Y+(((((-1385939218174997299200)*X+(23440980304438507560960))*X+(-34122016043026513367040))*X+(11374005347675504455680))*X)))*B+(((((-72477678052171191333888)*Y+(-16537724345006181741296070))*Y)*A+((((300108162824862377333760)*X)*Y+(((7239843416003464331356392)*X+(16586972882381896155355590))*X))*Y+(((16529948113818773322807750)*X+(-16537724345006181741296070))*X^2)))*A+(((((53373694041061893780480)*X)*Y+(((1900807858145761977876480)*X+(16573293629136424370960838))*X))*Y+((((-3842395931087629999503930)*X+(44587666579182571249562286))*X+(-139439074722885412697088))*X))*Y+((((-33059896227637546645615500)*X+(49605396803831136805399890))*X+(-16537724345006181741296070))*X))))*B+((((((-13248635652285239316960)*Y+((34271933818754265239299536)*X+(13898594133125121638054720)))*Y+(((-319828244448776770322212911)*X+(34174344635101713126073619))*X+(69105401260968291966569099)))*Y+((77148730389807508981146665)*X^3))*A+(((((-4896033429122725821711120)*X)*Y+(((-67522574226854774047274090)*X+(-152841078545924019984684655))*X))*Y+(((109268129345801730879933495)*X+(-112606106865067087210352639))*X))*Y+(((((-3232697412128976768632175)*X+(-31272823971924333524005611))*X+(-89883084113840860424964730))*X+(146254131650775800947715764))*X^2)))*A+((((((((-171103607182098432000)*X+(-11993619236098238069760))*X+(44714607372003177116640))*X)*Y+((((-342207214364196864000)*X^2+(-6781903315792300904823900))*X+(-5194580428845989788818480))*X))*Y+((((-23715823651428622268108115)*X+(-57808104252425548159276936))*X+(-78651738317114256149477294))*X))*Y+((((((-95264539460057510830080)*X+(-16570380752178588268246215))*X+(-67585218329556830445848066))*X+(-85236725254822281108377712))*X+(384252846593133476867845875))*X))*Y+((((((6465394824257953537264350)*X+(59312950531719690279379047))*X+(-160101577303472648598662811))*X+(-73796425856162426395809598))*X+(69105401260968291966569099))*X))))
compact_certificate theorem row4_50_identity (B A Y X : ℂ) :
  (((-249523606234593202035750912)*B+((30668384444455868204307778560)*A+((11371816752813630634543424784)*Y+((777989010646655738300855808)*X+(48641362564110407272188141696))))))*row3_94 B A Y X+
  (((35546531772512952756864)*B+((-17972668259769697846372800)*A+((92790715289667874905092544)*Y+((39594325277533033267200)*X+(-324503263612855743460895232))))))*row3_95 B A Y X+
  (((3839025431431398897741312)*B+((-100977040581637404192246410976)*A+((-13979726419796792187856733952)*Y+((-110798473026379086250901726976)*X+(18185942883427324999343555616))))))*row3_100 B A Y X+
  (((2405221743973193974224076919616)*B+((-205604908207702874489726471669760)*A+((-73719186714513964336857133196736)*Y+((2220670368397342828708317524160)*X+(-65594592088826604086335673309472))))))*row3_102 B A Y X+
  (((-142301561013686161925583998976)*B+((-189815328093639577764616482816)*Y+((-88977023481907259551606521768192)*X+(158031890672241804635548472529312)))))*row3_103 B A Y X+
  (((172149240337100144640)*B+((-2633076427593552056064)*A+((127517955805259366400)*Y+((12238929320851510482816)*X)))))*row3_65 B A Y X+
  (((533197976587694291352960)*B+((58742073053514765087796800)*A+((-312682686548263489285185600)*Y+((-33682412378606723707034880)*X)))))*row3_93 B A Y X+
  (((-1982706549977944698216192)*A+((53366264504501044838400)*Y)))*row3_70 B A Y X+
  (((319918785952616574811776)*A))*row3_79 B A Y X+
  (((19740540241607562609442560)*A+((-8241951736633755900958272)*X)))*row3_84 B A Y X+
  (((-39375757426111383136642560)*A+((-5100718232210374656000)*Y+((22013866598725823963938560)*X))))*row3_87 B A Y X+
  (((-792322798945593391535600640)*A+((65935613893070047207666176)*Y+((-3507336019266150626696073024)*X))))*row3_88 B A Y X+
  (((367020130637091155712202137600)*A+((-749321338014447846120044236800)*Y+((1509250865472944816494175539200)*X))))*row3_90 B A Y X+
  (((-57761719862186134153784955600000)*A+((9091014961937862424396221278208)*Y+((-6140781046519360542653449383360)*X))))*row3_91 B A Y X+
  (((-2656624079276236800)*Y))*row3_28 B A Y X+
  (((42975297331837631962364593)*Y))*row3_46 B A Y X+
  (((-10626496317104947200)*Y+((658269106898388014016)*X)))*row3_57 B A Y X+
  (((224889114637904037541709045)*Y))*row3_58 B A Y X+
  (((-70466294121071295430683136512)*Y))*row3_72 B A Y X+
  (((-55199339654832940203590415120)*Y+((-15334192222227934102153889280)*X)))*row3_89 B A Y X+
  (((-103206477503550036298199777280)*Y))*row3_92 B A Y X+
  (((230315085785013512658901880832)*Y+((2423448973959297700613913863424)*X)))*row3_97 B A Y X+
  (((10626496317104947200)*X))*row3_22 B A Y X+
  (((1530215469663112396800)*X))*row3_23 B A Y X+
  (((-1719011893273505278494583720)*X))*row3_40 B A Y X+
  (((10626496317104947200)*X))*row3_53 B A Y X+
  (((-359822583420646460066734472)*X))*row3_54 B A Y X+
  (((-16732906160766134059008000)*X))*row3_60 B A Y X+
  (((-56163868701913452473618400)*X))*row3_67 B A Y X+
  (((70466294121071295430683136512)*X))*row3_69 B A Y X+
  (((-1474185765669657176732663808)*X))*row3_73 B A Y X+
  (((-157924321932860500875540480)*X))*row3_78 B A Y X+
  (((797359087878755508517011840)*X))*row3_82 B A Y X+
  (((2053700694866978070860276858880)*X))*row3_83 B A Y X+
  (((-12924343196827554314711520)*X))*row3_85 B A Y X+
  (((217364827202603165877152970240)*X))*row3_86 B A Y X=((1564704))*row4_50 B A Y X := by
  simp only [row3_94, row3_95, row3_100, row3_102, row3_103, row3_65, row3_93, row3_70, row3_79, row3_84, row3_87, row3_88, row3_90, row3_91, row3_28, row3_46, row3_57, row3_58, row3_72, row3_89, row3_92, row3_97, row3_22, row3_23, row3_40, row3_53, row3_54, row3_60, row3_67, row3_69, row3_73, row3_78, row3_82, row3_83, row3_85, row3_86, row4_50] <;> ring
compact_certificate theorem row4_50_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row4_50 B A Y X=0 := by
  have z3_94 := row3_94_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_95 := row3_95_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_100 := row3_100_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_102 := row3_102_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_103 := row3_103_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_65 := row3_65_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_93 := row3_93_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_70 := row3_70_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_79 := row3_79_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_84 := row3_84_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_87 := row3_87_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_88 := row3_88_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_90 := row3_90_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_91 := row3_91_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_28 := row3_28_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_46 := row3_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_57 := row3_57_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_58 := row3_58_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_72 := row3_72_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_89 := row3_89_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_92 := row3_92_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_97 := row3_97_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_22 := row3_22_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_23 := row3_23_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_40 := row3_40_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_53 := row3_53_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_54 := row3_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_60 := row3_60_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_67 := row3_67_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_69 := row3_69_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_73 := row3_73_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_78 := row3_78_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_82 := row3_82_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_83 := row3_83_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_85 := row3_85_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_86 := row3_86_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row4_50_identity B A Y X).symm
  have hz : ((1564704))*row4_50 B A Y X=0 := by
    simpa only [z3_94, z3_95, z3_100, z3_102, z3_103, z3_65, z3_93, z3_70, z3_79, z3_84, z3_87, z3_88, z3_90, z3_91, z3_28, z3_46, z3_57, z3_58, z3_72, z3_89, z3_92, z3_97, z3_22, z3_23, z3_40, z3_53, z3_54, z3_60, z3_67, z3_69, z3_73, z3_78, z3_82, z3_83, z3_85, z3_86,mul_zero,add_zero] using he
  have hu : ((1564704):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_50_zero
compact_certificate def row4_89 (B A Y X : ℂ) : ℂ := (((((((540327180575047680)*X^2+(5673435396038000640))*Y)*A+(((-5673435396038000640)*X)*Y+(((-5673435396038000640)*X+(5673435396038000640))*X^2)))*A+(((((-540327180575047680)*X+(-5673435396038000640))*X)*Y+(((810490770862571520)*X+(-12697688743513620480))*X^2))*Y+((((11346870792076001280)*X+(-17020306188114001920))*X+(5673435396038000640))*X)))*B+(((((-59020328156222592000)*Y+(-11830993799962610719530))*Y)*A+((((190233165811368268800)*X)*Y+(((2701920419809420766040)*X+(11870527738674685041450))*X))*Y+(((11809560821799800494890)*X+(-11830993799962610719530))*X^2)))*A+(((((48959708700836828160)*X)*Y+(((1291063776966700001280)*X+(11853902199045003172650))*X))*Y+((((-2047946378165107936470)*X+(28516424772775782479490))*X+(-166005109910082032640))*X))*Y+((((-23619121643599600989780)*X+(35471548421725021933950))*X+(-11830993799962610719530))*X))))*B+((((((-7717958384301960480)*Y+((27370570042176497575344)*X+(8706887990162434435264)))*Y+(((-217798946140998422975529)*X+(42123480392167323972325))*X+(39362846173980293291821)))*Y+((53966004501988331468095)*X^3))*A+(((((-3541422564592321411440)*X)*Y+(((-38590520073672423663910)*X+(-85731391691868954055145))*X))*Y+(((90769016089728171575649)*X+(-89484251178566999203801))*X))*Y+(((((-1236441067901821776105)*X+(-22276174476084149579469))*X+(-55721222410556000159126))*X+(93328850675968624759916))*X^2)))*A+(((((((-15869036150876021760)*X+(42602077360068107040))*X)*Y+(((-5067950893716396598020)*X+(-2894578540681211011920))*X))*Y+((((-14731993832907105081765)*X+(-35438934137552247988664))*X+(-33081957969283920453250))*X))*Y+((((((-126952289207008174080)*X+(-7424497970355744877905))*X+(-43169628523480057075534))*X+(-33993057841238086241040))*X+(217297457546206099024389))*X))*Y+((((((2472882135803643552210)*X+(43315907884266477382833))*X+(-126697747662925475133597))*X+(-26514905754539923806578))*X+(39362846173980293291821))*X))))
compact_certificate theorem row4_89_identity (B A Y X : ℂ) :
  (((-1096322992376593988155392)*B+((146558255659463812784901120)*A+((10593422400951119437405200)*Y+((4282632284929416192849408)*X+(219746090666944531888248960))))))*row3_94 B A Y X+
  (((723005573900976392832)*B+((-80915323300415469074880)*A+((474335876580210769793472)*Y+(-1552895298754876830297600)))))*row3_95 B A Y X+
  (((16437052967956535471616)*B+((-543087306894007157371052256)*A+((-75152086438848090884294400)*Y+((-533430153325676856915281664)*X+(8930253172809151389618720))))))*row3_100 B A Y X+
  (((5156160627082530097963646784)*B+((-1121551821097163304652425922560)*A+((-354880378526445252957557467584)*Y+((-14605655892196823858499566400)*X+(-489511422814228335551463888672))))))*row3_102 B A Y X+
  (((-553619335283486028940382208)*B+((-877195884538206274949296128)*Y+((-485650224537057953058162809088)*X+(878414738207687774150330075040)))))*row3_103 B A Y X+
  (((-318532722663219840)*B+((206625822836850054688320)*A+((-1569259847012255702982720)*Y+((-145299126153124614309120)*X)))))*row3_93 B A Y X+
  (((-11273698880628625152)*A+((52401822574773794688)*X)))*row3_65 B A Y X+
  (((-8489095257113354739456)*A))*row3_70 B A Y X+
  (((1369754413996377955968)*A+((1284323937778102394880)*X)))*row3_79 B A Y X+
  (((100739247306899291815680)*A+((-47341133655012557817408)*X)))*row3_84 B A Y X+
  (((-201027546658573438625280)*A+((121355768740642584641280)*X)))*row3_87 B A Y X+
  (((-4130037819254353218462720)*A+((378729069240100462539264)*Y+((-17846587957902434174742336)*X))))*row3_88 B A Y X+
  (((1826436550707570355957555200)*A+((-4029679310043240965328998400)*Y+((7213509293375920219762544640)*X))))*row3_90 B A Y X+
  (((-311030677042155750023363064960)*A+((46258355986883109380932134912)*Y+((-5720448096513604496198808000)*X))))*row3_91 B A Y X+
  (((180804962564548813681697)*Y))*row3_46 B A Y X+
  (((955028670519540925375525)*Y))*row3_58 B A Y X+
  (((-286186245676416806314480128)*Y))*row3_72 B A Y X+
  (((-231117641668098233327991312)*Y+((-73279127829731906392450560)*X)))*row3_89 B A Y X+
  (((-493242054151608258467512320)*Y))*row3_92 B A Y X+
  (((1175285573435160644305637376)*Y+((13034095365456171776905254144)*X)))*row3_97 B A Y X+
  (((-7232198502581952547267880)*X))*row3_40 B A Y X+
  (((-1528045872831265480600840)*X))*row3_54 B A Y X+
  (((2818424720157156288)*X))*row3_57 B A Y X+
  (((-238755804106313102047200)*X))*row3_67 B A Y X+
  (((286186245676416806314480128)*X))*row3_69 B A Y X+
  (((-6311828339695309621100544)*X))*row3_73 B A Y X+
  (((-805913978455194334525440)*X))*row3_78 B A Y X+
  (((4070807819836112132161920)*X))*row3_82 B A Y X+
  (((10705058027507283542255370240)*X))*row3_83 B A Y X+
  (((-61402252927921805230560)*X))*row3_85 B A Y X+
  (((1038218018599447855588136448)*X))*row3_86 B A Y X=((10952928))*row4_89 B A Y X := by
  simp only [row3_94, row3_95, row3_100, row3_102, row3_103, row3_93, row3_65, row3_70, row3_79, row3_84, row3_87, row3_88, row3_90, row3_91, row3_46, row3_58, row3_72, row3_89, row3_92, row3_97, row3_40, row3_54, row3_57, row3_67, row3_69, row3_73, row3_78, row3_82, row3_83, row3_85, row3_86, row4_89] <;> ring
compact_certificate theorem row4_89_zero (B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
    (h0 : input0 B A Y X=0)
    (h1 : input1 B A Y X=0)
    (h2 : input2 B A Y X=0)
    (h3 : input3 B A Y X=0)
    (h4 : input4 B A Y X=0)
    : row4_89 B A Y X=0 := by
  have z3_94 := row3_94_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_95 := row3_95_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_100 := row3_100_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_102 := row3_102_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_103 := row3_103_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_93 := row3_93_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_65 := row3_65_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_70 := row3_70_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_79 := row3_79_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_84 := row3_84_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_87 := row3_87_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_88 := row3_88_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_90 := row3_90_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_91 := row3_91_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_46 := row3_46_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_58 := row3_58_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_72 := row3_72_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_89 := row3_89_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_92 := row3_92_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_97 := row3_97_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_40 := row3_40_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_54 := row3_54_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_57 := row3_57_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_67 := row3_67_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_69 := row3_69_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_73 := row3_73_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_78 := row3_78_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_82 := row3_82_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_83 := row3_83_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_85 := row3_85_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have z3_86 := row3_86_zero B A Y X hA hY hX h0 h1 h2 h3 h4
  have he := (row4_89_identity B A Y X).symm
  have hz : ((10952928))*row4_89 B A Y X=0 := by
    simpa only [z3_94, z3_95, z3_100, z3_102, z3_103, z3_93, z3_65, z3_70, z3_79, z3_84, z3_87, z3_88, z3_90, z3_91, z3_46, z3_58, z3_72, z3_89, z3_92, z3_97, z3_40, z3_54, z3_57, z3_67, z3_69, z3_73, z3_78, z3_82, z3_83, z3_85, z3_86,mul_zero,add_zero] using he
  have hu : ((10952928):ℂ)≠0 := by norm_num [mul_ne_zero_iff,hA,hY,hX]
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_89_zero
compact_certificate def row4_90 (B A Y X : ℂ) : ℂ := (((((((120636319680)*X^2)*Y)*A+(((20068471872)*Y+(7315173504270))*Y))*A+((((30440940480)*X)*Y+(((209349402552)*X+(-7315173504270))*X))*Y+(((-7315173504270)*X+(7315173504270))*X^2)))*A+(((((-23676287040)*X)*Y+(((-755367405120)*X+(-7311565689102))*X))*Y+((((650824754850)*X+(-14914713284694))*X+(20068471872))*X))*Y+((((14630347008540)*X+(-21945520512810))*X+(7315173504270))*X)))*B+((((((1307476080)*Y+((-17042322039516)*X+(-4008317198312)))*Y+(((121251727432491)*X+(-42565480060511))*X+(-17615626300739)))*Y+((-35033863730765)*X^3))*A+(((((1603480863240)*X)*Y+(((16021185123950)*X+(31848559859155))*X))*Y+(((-72394256930067)*X+(60681172778759))*X))*Y+(((((-310924410165)*X+(12438987424311))*X+(33489092518318))*X+(-52649490031504))*X^2)))*A+((((((19612141200)*X)*Y+(((3207222287280)*X+(1016855374560))*X))*Y+((((6333634218915)*X+(15710718867256))*X+(2349719429306))*X))*Y+(((((306200828475)*X+(21174938047766))*X+(824372026488))*X+(-88653980509287))*X))*Y+((((((621848820330)*X+(-25188899258787))*X+(85596257310735))*X+(-1347382341734))*X+(-17615626300739))*X))))
compact_certificate theorem row4_90_identity (B A Y X : ℂ) :
  (((-882056691348480)*B+((-151136654684382720)*A+((-55089815999617584)*Y+((-6949877498539776)*X+(-93302963515463040))))))*row3_94 B A Y X+
  (((40721891011200)*A+((-454493939276160)*Y+(1338815499216480))))*row3_95 B A Y X+
  (((581584857494378400)*A+((67724694037255680)*Y+((507758316092075520)*X+(97201043723037600)))))*row3_100 B A Y X+
  (((321072136660399680)*B+((1127442988805789260800)*A+((372218226087911158080)*Y+((-8132126658903489600)*X+(544143222448122180960))))))*row3_102 B A Y X+
  (((-308719841971968000)*B+((4115435887861032960)*Y+((474350818568202236160)*X+(-883029130908168549600)))))*row3_103 B A Y X+
  (((-97740632102400)*A+((34209221235840)*X)))*row3_84 B A Y X+
  (((195481264204800)*A+((-97740632102400)*X)))*row3_87 B A Y X+
  (((3530775275210880)*A+((-273673769886720)*Y+((17588426746826880)*X))))*row3_88 B A Y X+
  (((-1140046732842393600)*A+((3420140198527180800)*Y+((-5573430687463833600)*X))))*row3_90 B A Y X+
  (((311362715796384378240)*A+((-45589202127775272960)*Y+((29748500639793495360)*X))))*row3_91 B A Y X+
  (((-544479439104000)*A+((1539414955612800)*Y)))*row3_93 B A Y X+
  (((-217594269291619)*Y))*row3_46 B A Y X+
  (((-1136841662509295)*Y))*row3_58 B A Y X+
  (((503520640338723840)*Y))*row3_72 B A Y X+
  (((280423556766733104)*Y+((75568327342191360)*X)))*row3_89 B A Y X+
  (((506687436818841600)*Y))*row3_92 B A Y X+
  (((-1140046732842393600)*Y+((-13958036579865081600)*X)))*row3_97 B A Y X+
  (((8703770771664760)*X))*row3_40 B A Y X+
  (((1818946660014872)*X))*row3_54 B A Y X+
  (((-503520640338723840)*X))*row3_69 B A Y X+
  (((781925056819200)*X))*row3_78 B A Y X+
  (((78650054978572800)*X))*row3_80 B A Y X+
  (((-3958495600147200)*X))*row3_82 B A Y X+
  (((-9151769513346600960)*X))*row3_83 B A Y X+
  (((-1137444735378622464)*X))*row3_86 B A Y X=((15647040))*row4_90 B A Y X := by
  simp only [row3_94, row3_95, row3_100, row3_102, row3_103, row3_84, row3_87, row3_88, row3_90, row3_91, row3_93, row3_46, row3_58, row3_72, row3_89, row3_92, row3_97, row3_40, row3_54, row3_69, row3_78, row3_80, row3_82, row3_83, row3_86, row4_90] <;> ring

}
end QuantitativeArithmeticSmallLevelTwentyFive.NegativeSecondAlgebra
end
