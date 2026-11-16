module

public import Mathlib.Tactic
public meta import SmallLevelCertificateBatchCommandV1
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.NegativeDZeroAlgebra
certificate_batch {
def input0 (u A X : ℂ) : ℂ := ((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))
def input1 (u A X : ℂ) : ℂ := (((((((-90)*X+(360))*A+((((-90)*X+(360))*X+(90))*X+(-360)))*A+(((270)*X+(-1170))*X+(360)))*A+(((((90)*X+(-450))*X+(270))*X+(360))*X))*u+(((((-540)*A+((-180)*X+(-1320)))*A+(((-225)*X+(1520))*X+(-1680)))*A+(((((-90)*X+(380))*X+(-560))*X+(230))*X+(5160)))*A+((((-320)*X+(320))*X+(320))*X)))*u+((((((48)*X+(-48))*A+((144)*X+(-336)))*A+((((48)*X+(-96))*X+(96))*X+(-432)))*A+(((96)*X+(-192))*X^2+(96)))*A))
def input2 (u A X : ℂ) : ℂ := ((((((((1)*X+(-1))*X)*A+(((((1)*X+(-1))*X+(-1))*X+(1))*X))*A+((((-3)*X+(4))*X+(-1))*X))*A+((((-1)*X+(2))*X^2+(-1))*X^2))*u+((((((-1)*X)*A+((((-1)*X+(-1))*X+(3))*X))*A+(((2)*X^2+(-2))*X))*A+((((1)*X+(-3))*X+(1))*X^3))*A+(((((-1)*X^2+(1))*X+(2))*X+(1))*X^2)))*u+((((((1)*X+(1))*X+(-1))*A^2+((((2)*X+(-3))*X+(1))*X+(1)))*A+((((1)*X^2+(-4))*X^2+(1))*X))*A+((((-1)*X^2+(3))*X^2+(-1))*X)))
def input3 (u A X : ℂ) : ℂ := ((((((-700)*X)*A+((((-160)*X+(-350))*X+(-2200))*X))*A+((((-395)*X+(-160))*X+(-2560))*X))*A+((((((60)*X+(-60))*X+(-1020))*X+(960))*X+(960))*X))*u+((((((48)*X+(192))*X)*A+(((64)*X+(304))*X))*A+(((((-32)*X+(-96))*X+(96))*X+(-32))*X))*A+(((((-64)*X+(-192))*X+(320))*X+(256))*X)))
def target0 (u A X : ℂ) : ℂ := (((1)*X)*A)
def target (u A X : ℂ) (i : ℕ) : ℂ := match i with
  | 0 => target0 u A X
  | _ => 0
def row0_0 (u A X : ℂ) : ℂ := ((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))
theorem row0_0_identity (u A X : ℂ) :
  ((1))*input0 u A X=((1))*row0_0 u A X := by
  simp only [input0, row0_0] <;> ring
theorem row0_0_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row0_0 u A X=0 := by
  have he := (row0_0_identity u A X).symm
  have hz : ((1))*row0_0 u A X=0 := by
    simpa only [h0,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_0_zero
def row0_1 (u A X : ℂ) : ℂ := (((((((90)*X+(-360))*A+((((90)*X+(-360))*X+(-90))*X+(360)))*A+(((-270)*X+(1170))*X+(-360)))*A+(((((-90)*X+(450))*X+(-270))*X+(-360))*X))*u+(((((540)*A+((180)*X+(1320)))*A+(((225)*X+(-1520))*X+(1680)))*A+(((((90)*X+(-380))*X+(560))*X+(-230))*X+(-5160)))*A+((((320)*X+(-320))*X+(-320))*X)))*u+((((((-48)*X+(48))*A+((-144)*X+(336)))*A+((((-48)*X+(96))*X+(-96))*X+(432)))*A+(((-96)*X+(192))*X^2+(-96)))*A))
theorem row0_1_identity (u A X : ℂ) :
  ((1))*input1 u A X=((-1))*row0_1 u A X := by
  simp only [input1, row0_1] <;> ring
theorem row0_1_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row0_1 u A X=0 := by
  have he := (row0_1_identity u A X).symm
  have hz : ((-1))*row0_1 u A X=0 := by
    simpa only [h1,mul_zero,add_zero] using he
  have hunit : ((-1):ℂ)=(-1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((-1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_1_zero
def row0_2 (u A X : ℂ) : ℂ := ((((((((1)*X+(-1))*X)*A+(((((1)*X+(-1))*X+(-1))*X+(1))*X))*A+((((-3)*X+(4))*X+(-1))*X))*A+((((-1)*X+(2))*X^2+(-1))*X^2))*u+((((((-1)*X)*A+((((-1)*X+(-1))*X+(3))*X))*A+(((2)*X^2+(-2))*X))*A+((((1)*X+(-3))*X+(1))*X^3))*A+(((((-1)*X^2+(1))*X+(2))*X+(1))*X^2)))*u+((((((1)*X+(1))*X+(-1))*A^2+((((2)*X+(-3))*X+(1))*X+(1)))*A+((((1)*X^2+(-4))*X^2+(1))*X))*A+((((-1)*X^2+(3))*X^2+(-1))*X)))
theorem row0_2_identity (u A X : ℂ) :
  ((1))*input2 u A X=((1))*row0_2 u A X := by
  simp only [input2, row0_2] <;> ring
theorem row0_2_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row0_2 u A X=0 := by
  have he := (row0_2_identity u A X).symm
  have hz : ((1))*row0_2 u A X=0 := by
    simpa only [h2,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_2_zero
def row0_3 (u A X : ℂ) : ℂ := (((((700)*A+(((160)*X+(350))*X+(2200)))*A+(((395)*X+(160))*X+(2560)))*A+(((((-60)*X+(60))*X+(1020))*X+(-960))*X+(-960)))*u+(((((-48)*X+(-192))*A+((-64)*X+(-304)))*A+((((32)*X+(96))*X+(-96))*X+(32)))*A+((((64)*X+(192))*X+(-320))*X+(-256))))
theorem row0_3_identity (u A X : ℂ) :
  ((1))*input3 u A X=(((-1)*X))*row0_3 u A X := by
  simp only [input3, row0_3] <;> ring
theorem row0_3_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row0_3 u A X=0 := by
  have he := (row0_3_identity u A X).symm
  have hz : (((-1)*X))*row0_3 u A X=0 := by
    simpa only [h3,mul_zero,add_zero] using he
  have hunit : (((-1)*X):ℂ)=(-1)*A^0*X^1*(A+1)^0 := by ring
  have hu : (((-1)*X):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row0_3_zero
def row1_0 (u A X : ℂ) : ℂ := (((((((2880)*X+(38880))*A+(((2880)*X^2+(22320))*X+(169920)))*A+(((19800)*X+(48960))*X+(172800)))*A+(((((-7200)*X+(18720))*X+(64800))*X+(-80640))*X+(-69120)))*u+(((((17280)*A+((2304)*X+(-3084)))*A+(-136126))*A+(((((2880)*X+(-9856))*X+(7057))*X+(47526))*X+(-278016)))*A+(((((2700)*X+(81146))*X+(-180312))*X+(9920))*X+(93766))))*u+((((((-1536)*X+(1536))*A+(16944))*A+((-1536)*X^3+(32832)))*A+((((-2064)*X+(-6144))*X+(-1008))*X+(-2064)))*A+(((((-3072)*X+(-2064))*X+(2016))*X+(11328))*X+(6192))))
theorem row1_0_identity (u A X : ℂ) :
  (((68998)*u+((2448)*A+((-3072)*X+(-5328)))))*row0_0 u A X+
  ((32))*row0_1 u A X+
  (((72)*u+(-45)))*row0_3 u A X=((1))*row1_0 u A X := by
  simp only [row0_0, row0_1, row0_3, row1_0] <;> ring
theorem row1_0_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row1_0 u A X=0 := by
  have z0_0 := row0_0_zero u A X hA hX hA1 h0 h1 h2 h3
  have z0_1 := row0_1_zero u A X hA hX hA1 h0 h1 h2 h3
  have z0_3 := row0_3_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row1_0_identity u A X).symm
  have hz : ((1))*row1_0 u A X=0 := by
    simpa only [z0_0, z0_1, z0_3,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_0_zero
def row1_1 (u A X : ℂ) : ℂ := ((((((116640)*A+((75600)*X+(509760)))*A+(((85320)*X+(138240))*X+(518400)))*A+(((((-12960)*X+(47520))*X+(185760))*X+(-241920))*X+(-207360)))*u+((((((20160)*X+(14040))*A+(((2880)*X^2+(15312))*X+(191848)))*A+(649812))*A+(((((8360)*X+(-21323))*X+(137806))*X+(-111652))*X+(387712)))*A+(((((((2880)*X+(540))*X+(-12500))*X+(54648))*X+(302784))*X+(-400320))*X+(-348452))))*u+(((((((-4416)*X+(-3360))*X+(17856))*A+((-4176)*X^2+(-26496)))*A+(((-1536)*X+(-9024))*X^3+(-48464)))*A+((((((-2880)*X+(-3360))*X+(27776))*X+(2976))*X+(-32432))*X+(28256)))*A+((((((2880)*X+(-10752))*X+(18032))*X+(89824))*X+(-108032))*X+(-94992))))
theorem row1_1_identity (u A X : ℂ) :
  (((15964)*u+((13344)*A+((-10176)*X+(-12560)))))*row0_0 u A X+
  (((32)*X+(96)))*row0_1 u A X+
  ((-2880))*row0_2 u A X+
  (((216)*u+((-54)*A+((-9)*X+(322)))))*row0_3 u A X=((1))*row1_1 u A X := by
  simp only [row0_0, row0_1, row0_2, row0_3, row1_1] <;> ring
theorem row1_1_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row1_1 u A X=0 := by
  have z0_0 := row0_0_zero u A X hA hX hA1 h0 h1 h2 h3
  have z0_1 := row0_1_zero u A X hA hX hA1 h0 h1 h2 h3
  have z0_2 := row0_2_zero u A X hA hX hA1 h0 h1 h2 h3
  have z0_3 := row0_3_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row1_1_identity u A X).symm
  have hz : ((1))*row1_1 u A X=0 := by
    simpa only [z0_0, z0_1, z0_2, z0_3,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_1_zero

def row1_2 (u A X : ℂ) : ℂ := ((((((700)*A+(((160)*X+(350))*X+(2200)))*A+(((395)*X+(160))*X+(2560)))*A+(((((-60)*X+(60))*X+(1020))*X+(-960))*X+(-960)))*u+(((((-48)*X+(-192))*A+(-368))*A+((((32)*X+(96))*X+(-32))*X+(32)))*A+((((128)*X+(64))*X+(-320))*X+(-192))))*u)
theorem row1_2_identity (u A X : ℂ) :
  (((64)*u))*row0_0 u A X+
  (((1)*u))*row0_3 u A X=((1))*row1_2 u A X := by
  simp only [row0_0, row0_3, row1_2] <;> ring
theorem row1_2_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row1_2 u A X=0 := by
  have z0_0 := row0_0_zero u A X hA hX hA1 h0 h1 h2 h3
  have z0_3 := row0_3_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row1_2_identity u A X).symm
  have hz : ((1))*row1_2 u A X=0 := by
    simpa only [z0_0, z0_3,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_2_zero
def row1_3 (u A X : ℂ) : ℂ := ((((((22400)*A+(((5120)*X+(11200))*X+(15100)))*A+(-114410))*A+(((((-1920)*X+(1920))*X+(1435))*X+(-20830))*X+(-232960)))*A+(((((4740)*X+(17790))*X+(-125640))*X+(75840))*X+(98370)))*u+((((((-1536)*X+(-6144))*A+(7184))*A+((1024)*X^3+(28352)))*A+((((-2224)*X+(-1024))*X+(-5968))*X+(-12464)))*A+(((((-3072)*X+(-2224))*X+(-8544))*X+(22208))*X+(16912))))
theorem row1_3_identity (u A X : ℂ) :
  (((22530)*u+((-1744)*A+((-3072)*X+(-3312)))))*row0_0 u A X+
  (((32)*A+(-79)))*row0_3 u A X=((1))*row1_3 u A X := by
  simp only [row0_0, row0_3, row1_3] <;> ring
theorem row1_3_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row1_3 u A X=0 := by
  have z0_0 := row0_0_zero u A X hA hX hA1 h0 h1 h2 h3
  have z0_3 := row0_3_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row1_3_identity u A X).symm
  have hz : ((1))*row1_3 u A X=0 := by
    simpa only [z0_0, z0_3,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_3_zero
def row1_5 (u A X : ℂ) : ℂ := (((((140)*A+((32)*X^2+(510)))*A+(((79)*X+(-38))*X+(512)))*A+(((((-12)*X+(-58))*X+(344))*X+(-192))*X+(-262)))*u+((((-48)*A+(-64))*A+(((16)*X^2+(-16))*X+(16)))*A+((((16)*X+(32))*X+(-64))*X+(-48))))
theorem row1_5_identity (u A X : ℂ) :
  (((-350)*u+((48)*A+(16))))*row0_0 u A X+
  ((1))*row0_3 u A X=((5))*row1_5 u A X := by
  simp only [row0_0, row0_3, row1_5] <;> ring
theorem row1_5_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row1_5 u A X=0 := by
  have z0_0 := row0_0_zero u A X hA hX hA1 h0 h1 h2 h3
  have z0_3 := row0_3_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row1_5_identity u A X).symm
  have hz : ((5))*row1_5 u A X=0 := by
    simpa only [z0_0, z0_3,mul_zero,add_zero] using he
  have hunit : ((5):ℂ)=(5)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((5):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_5_zero
def row1_6 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))*u)
theorem row1_6_identity (u A X : ℂ) :
  (((1)*u))*row0_0 u A X=((1))*row1_6 u A X := by
  simp only [row0_0, row1_6] <;> ring
theorem row1_6_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row1_6 u A X=0 := by
  have z0_0 := row0_0_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row1_6_identity u A X).symm
  have hz : ((1))*row1_6 u A X=0 := by
    simpa only [z0_0,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_6_zero
def row1_7 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+(1))*A+((((1)*X+(-2))*X+(-1))*X+(1)))*A+(((-1)*X+(2))*X^2+(-1)))
theorem row1_7_identity (u A X : ℂ) :
  (((1)*A+(-1)))*row0_0 u A X=((1))*row1_7 u A X := by
  simp only [row0_0, row1_7] <;> ring
theorem row1_7_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row1_7 u A X=0 := by
  have z0_0 := row0_0_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row1_7_identity u A X).symm
  have hz : ((1))*row1_7 u A X=0 := by
    simpa only [z0_0,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_7_zero
def row1_8 (u A X : ℂ) : ℂ := ((((1)*X^2+(-1))*A+(((1)*X+(1))*X))*A+(((((1)*X+(-1))*X+(-2))*X+(1))*X+(1)))
theorem row1_8_identity (u A X : ℂ) :
  (((1)*X+(1)))*row0_0 u A X=((1))*row1_8 u A X := by
  simp only [row0_0, row1_8] <;> ring
theorem row1_8_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row1_8 u A X=0 := by
  have z0_0 := row0_0_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row1_8_identity u A X).symm
  have hz : ((1))*row1_8 u A X=0 := by
    simpa only [z0_0,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_8_zero

def row1_9 (u A X : ℂ) : ℂ := ((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))
theorem row1_9_identity (u A X : ℂ) :
  ((1))*row0_0 u A X=((1))*row1_9 u A X := by
  simp only [row0_0, row1_9] <;> ring
theorem row1_9_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row1_9 u A X=0 := by
  have z0_0 := row0_0_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row1_9_identity u A X).symm
  have hz : ((1))*row1_9 u A X=0 := by
    simpa only [z0_0,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row1_9_zero
def row2_6 (u A X : ℂ) : ℂ := (((((((-855360)*X+(5846940))*A+(22268070))*A+((((-625680)*X+(2857635))*X+(1115730))*X+(24076800)))*A+((((((95040)*X+(-936540))*X+(547470))*X+(10141560))*X+(-8902080))*X+(-9101070)))*u+(((((1188000)*A+(-1099752))*A+(-11584348))*A+(((((231264)*X+(-1111264))*X+(1293550))*X+(3977916))*X+(-21482880)))*A+((((6831140)*X+(-12785280))*X+(-877000))*X+(5954140))))*u+(((((114048)*A+(1535520))*A+(2257152))*A+((((-235872)*X+(-38016))*X+(387936))*X+(-121824)))*A+((((((38016)*X+(-38016))*X+(-311904))*X+(-433728))*X+(981504))*X+(707616))))
theorem row2_6_identity (u A X : ℂ) :
  ((88))*row1_0 u A X+
  (((17325)*u+((-2376)*A+(5058))))*row1_5 u A X+
  (((-140472)*u+((270336)*X+(405504))))*row1_9 u A X+
  (((1520640)*u+((-506880)*A+((25848)*X))))*row1_6 u A X+
  (((135168)*A))*row1_7 u A X+
  (((-1584)*X))*row1_2 u A X+
  (((38016)*X))*row1_8 u A X=((1))*row2_6 u A X := by
  simp only [row1_0, row1_5, row1_9, row1_6, row1_7, row1_2, row1_8, row2_6] <;> ring
theorem row2_6_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row2_6 u A X=0 := by
  have z1_0 := row1_0_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_5 := row1_5_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_9 := row1_9_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_6 := row1_6_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_7 := row1_7_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_2 := row1_2_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_8 := row1_8_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row2_6_identity u A X).symm
  have hz : ((1))*row2_6 u A X=0 := by
    simpa only [z1_0, z1_5, z1_9, z1_6, z1_7, z1_2, z1_8,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_6_zero
def row2_7 (u A X : ℂ) : ℂ := ((((((1866240)*A+(9365760))*A+(((1365120)*X+(1002240))*X+(8294400)))*A+(((((-207360)*X+(-449280))*X+(5391360))*X+(-3870720))*X+(-4527360)))*u+((((((120960)*X+(665640))*A+(2847560))*A+(5558260))*A+((((((17280)*X+(78680))*X+(-645875))*X+(2794820))*X+(-375540))*X+(-1817080)))*A+((((((46080)*X+(-34020))*X^2+(1812920))*X+(614760))*X+(-4439140))*X+(-2556020))))*u+((((((-56832)*X^2+(136032))*A+(-94224))*A+((-33792)*X^4+(-38992)))*A+((((((-46080)*X+(33072))*X+(377488))*X+(-38256))*X+(-121888))*X+(212464)))*A+((((((169248)*X+(-317424))*X+(290896))*X+(493568))*X+(-969328))*X+(-657360))))
theorem row2_7_identity (u A X : ℂ) :
  ((16))*row1_1 u A X+
  (((3150)*A+(-13840)))*row1_5 u A X+
  (((-606868)*u+((131472)*A+((-3072)*X+(198192)))))*row1_9 u A X+
  (((-1209600)*u+((-109092)*A+((194030)*X))))*row1_6 u A X+
  (((-1536)*A+((66816)*X)))*row1_7 u A X+
  (((-9)*X))*row1_3 u A X+
  (((95520)*X))*row1_8 u A X=((1))*row2_7 u A X := by
  simp only [row1_1, row1_5, row1_9, row1_6, row1_7, row1_3, row1_8, row2_7] <;> ring
theorem row2_7_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row2_7 u A X=0 := by
  have z1_1 := row1_1_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_5 := row1_5_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_9 := row1_9_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_6 := row1_6_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_7 := row1_7_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_3 := row1_3_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_8 := row1_8_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row2_7_identity u A X).symm
  have hz : ((1))*row2_7 u A X=0 := by
    simpa only [z1_1, z1_5, z1_9, z1_6, z1_7, z1_3, z1_8,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_7_zero
def row2_11 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))*u^2)
theorem row2_11_identity (u A X : ℂ) :
  (((1)*u))*row1_6 u A X=((1))*row2_11 u A X := by
  simp only [row1_6, row2_11] <;> ring
theorem row2_11_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row2_11 u A X=0 := by
  have z1_6 := row1_6_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row2_11_identity u A X).symm
  have hz : ((1))*row2_11 u A X=0 := by
    simpa only [z1_6,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_11_zero
def row2_12 (u A X : ℂ) : ℂ := ((((((1)*X+(-1))*A+(1))*A+((((1)*X+(-2))*X+(-1))*X+(1)))*A+(((-1)*X+(2))*X^2+(-1)))*u)
theorem row2_12_identity (u A X : ℂ) :
  (((-1)*u))*row1_9 u A X+
  (((1)*A))*row1_6 u A X=((1))*row2_12 u A X := by
  simp only [row1_9, row1_6, row2_12] <;> ring
theorem row2_12_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row2_12 u A X=0 := by
  have z1_9 := row1_9_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_6 := row1_6_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row2_12_identity u A X).symm
  have hz : ((1))*row2_12 u A X=0 := by
    simpa only [z1_9, z1_6,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_12_zero
def row2_13 (u A X : ℂ) : ℂ := ((((((1)*X+(-1))*A+(1))*A+(-1))*A+((((-2)*X+(3))*X+(2))*X+(-1)))*A+(((((-1)*X+(3))*X^2+(-5))*X+(1))*X+(2)))
theorem row2_13_identity (u A X : ℂ) :
  (((2)*X+(2)))*row1_9 u A X+
  (((1)*A))*row1_7 u A X+
  (((-1)*X))*row1_8 u A X=((1))*row2_13 u A X := by
  simp only [row1_9, row1_7, row1_8, row2_13] <;> ring
theorem row2_13_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row2_13 u A X=0 := by
  have z1_9 := row1_9_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_7 := row1_7_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_8 := row1_8_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row2_13_identity u A X).symm
  have hz : ((1))*row2_13 u A X=0 := by
    simpa only [z1_9, z1_7, z1_8,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_13_zero

def row2_14 (u A X : ℂ) : ℂ := (((((140)*A+((44)*X^2+(498)))*A+(((91)*X+(-26))*X+(512)))*A+((((-70)*X+(320))*X+(-180))*X+(-250)))*u+((((-48)*A+(-64))*A+(((16)*X^2+(-16))*X+(16)))*A+((((16)*X+(32))*X+(-64))*X+(-48))))
theorem row2_14_identity (u A X : ℂ) :
  ((1))*row1_5 u A X+
  (((12)*u))*row1_9 u A X+
  (((12)*X))*row1_6 u A X=((1))*row2_14 u A X := by
  simp only [row1_5, row1_9, row1_6, row2_14] <;> ring
theorem row2_14_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row2_14 u A X=0 := by
  have z1_5 := row1_5_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_9 := row1_9_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_6 := row1_6_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row2_14_identity u A X).symm
  have hz : ((1))*row2_14 u A X=0 := by
    simpa only [z1_5, z1_9, z1_6,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_14_zero
def row2_16 (u A X : ℂ) : ℂ := ((((1)*X^3+(-1))*A+((((1)*X+(1))*X+(1))*X))*A+((((((1)*X+(-1))*X+(-1))*X+(-1))*X+(1))*X+(1)))
theorem row2_16_identity (u A X : ℂ) :
  ((1))*row1_9 u A X+
  (((1)*X))*row1_8 u A X=((1))*row2_16 u A X := by
  simp only [row1_9, row1_8, row2_16] <;> ring
theorem row2_16_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row2_16 u A X=0 := by
  have z1_9 := row1_9_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_8 := row1_8_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row2_16_identity u A X).symm
  have hz : ((1))*row2_16 u A X=0 := by
    simpa only [z1_9, z1_8,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_16_zero
def row2_17 (u A X : ℂ) : ℂ := (((((-140)*A+(-542))*A+(((-47)*X+(70))*X+(-512)))*A+(((((44)*X+(26))*X+(-408))*X+(224))*X+(294)))*u+((((48)*A+(64))*A+(((-16)*X^2+(16))*X+(-16)))*A+((((-16)*X+(-32))*X+(64))*X+(48))))
theorem row2_17_identity (u A X : ℂ) :
  ((-1))*row1_5 u A X+
  (((32)*u))*row1_9 u A X+
  (((32)*X))*row1_6 u A X=((1))*row2_17 u A X := by
  simp only [row1_5, row1_9, row1_6, row2_17] <;> ring
theorem row2_17_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row2_17 u A X=0 := by
  have z1_5 := row1_5_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_9 := row1_9_zero u A X hA hX hA1 h0 h1 h2 h3
  have z1_6 := row1_6_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row2_17_identity u A X).symm
  have hz : ((1))*row2_17 u A X=0 := by
    simpa only [z1_5, z1_9, z1_6,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_17_zero
def row2_18 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))*u)
theorem row2_18_identity (u A X : ℂ) :
  (((1)*u))*row1_9 u A X=((1))*row2_18 u A X := by
  simp only [row1_9, row2_18] <;> ring
theorem row2_18_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row2_18 u A X=0 := by
  have z1_9 := row1_9_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row2_18_identity u A X).symm
  have hz : ((1))*row2_18 u A X=0 := by
    simpa only [z1_9,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_18_zero
def row2_19 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+(1))*A+((((1)*X+(-2))*X+(-1))*X+(1)))*A+(((-1)*X+(2))*X^2+(-1)))
theorem row2_19_identity (u A X : ℂ) :
  (((1)*A+(-1)))*row1_9 u A X=((1))*row2_19 u A X := by
  simp only [row1_9, row2_19] <;> ring
theorem row2_19_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row2_19 u A X=0 := by
  have z1_9 := row1_9_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row2_19_identity u A X).symm
  have hz : ((1))*row2_19 u A X=0 := by
    simpa only [z1_9,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_19_zero
def row2_20 (u A X : ℂ) : ℂ := ((((1)*X^2+(-1))*A+(((1)*X+(1))*X))*A+(((((1)*X+(-1))*X+(-2))*X+(1))*X+(1)))
theorem row2_20_identity (u A X : ℂ) :
  (((1)*X+(1)))*row1_9 u A X=((1))*row2_20 u A X := by
  simp only [row1_9, row2_20] <;> ring
theorem row2_20_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row2_20 u A X=0 := by
  have z1_9 := row1_9_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row2_20_identity u A X).symm
  have hz : ((1))*row2_20 u A X=0 := by
    simpa only [z1_9,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_20_zero

def row2_21 (u A X : ℂ) : ℂ := ((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))
theorem row2_21_identity (u A X : ℂ) :
  ((1))*row1_9 u A X=((1))*row2_21 u A X := by
  simp only [row1_9, row2_21] <;> ring
theorem row2_21_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row2_21 u A X=0 := by
  have z1_9 := row1_9_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row2_21_identity u A X).symm
  have hz : ((1))*row2_21 u A X=0 := by
    simpa only [z1_9,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row2_21_zero
def row3_7 (u A X : ℂ) : ℂ := ((((((553212)*A+(3186414))*A+((((63162)*X+(40293))*X+(481338))*X+(3859416)))*A+(((((26136)*X^2+(67518))*X+(871200))*X+(-1136916))*X+(-1017126)))*u+(((((529056)*A+(545784))*A+(-2941100))*A+((((-436832)*X+(804950))*X+(1005132))*X+(-7216896)))*A+((((1994164)*X+(-4399680))*X+(411352))*X+(2405516))))*u+(((((-38016)*A+(403872))*A+(742656))*A+((((-89568)*X+(12672))*X+(38880))*X+(-127584)))*A+((((((-12672)*X+(12672))*X+(-64224))*X+(-191808))*X+(345600))*X+(268704))))
theorem row3_7_identity (u A X : ℂ) :
  ((11))*row2_6 u A X+
  (((234135)*u+((-57816)*A+(61758))))*row2_17 u A X+
  (((-9408960)*u+((-2717352)*X)))*row2_18 u A X+
  (((1329768)*u))*row2_21 u A X+
  (((9408960)*A))*row2_11 u A X+
  (((-925056)*X))*row2_20 u A X=((40))*row3_7 u A X := by
  simp only [row2_6, row2_17, row2_18, row2_21, row2_11, row2_20, row3_7] <;> ring
theorem row3_7_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_7 u A X=0 := by
  have z2_6 := row2_6_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_17 := row2_17_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_18 := row2_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_21 := row2_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_11 := row2_11_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_20 := row2_20_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_7_identity u A X).symm
  have hz : ((40))*row3_7 u A X=0 := by
    simpa only [z2_6, z2_17, z2_18, z2_21, z2_11, z2_20,mul_zero,add_zero] using he
  have hunit : ((40):ℂ)=(40)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((40):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_7_zero
def row3_8 (u A X : ℂ) : ℂ := ((((((3649536)*A+(20604672))*A+(((3459456)*X+(4029696))*X+(17791488)))*A+((((-988416)*X+(10492416))*X+(-8515584))*X+(-9504000)))*u+(((((3136760)*A+(7904744))*A+(4572116))*A+(((((52272)*X^2+(-2146573))*X+(8954428))*X+(328564))*X+(-25326072)))*A+(((((139392)*X^3+(6815440))*X+(-7526380))*X+(-7219636))*X+(13980))))*u+(((((-20064)*A+(1070096))*A+(1447504))*A+((((((-139392)*X+(-45936))*X+(982896))*X+(607024))*X+(642464))*X+(-222000)))*A+(((((((-69696)*X+(667040))*X+(-364496))*X+(276080))*X+(-1741120))*X+(-495184))*X+(541392))))
theorem row3_8_identity (u A X : ℂ) :
  ((121))*row2_7 u A X+
  (((570240)*u+((-216370)*A+((93555)*X+(1370320)))))*row2_17 u A X+
  (((-120407980)*u+((4599408)*A+((13753344)*X+(35420880)))))*row2_21 u A X+
  (((-14636160)*A))*row2_12 u A X+
  (((-33471900)*A+((-39441710)*X)))*row2_18 u A X+
  (((6876672)*A))*row2_19 u A X+
  (((6876672)*X))*row2_13 u A X+
  (((332640)*X))*row2_14 u A X+
  (((4088832)*X))*row2_16 u A X+
  (((-10338592)*X))*row2_20 u A X=((40))*row3_8 u A X := by
  simp only [row2_7, row2_17, row2_21, row2_12, row2_18, row2_19, row2_13, row2_14, row2_16, row2_20, row3_8] <;> ring
theorem row3_8_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_8 u A X=0 := by
  have z2_7 := row2_7_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_17 := row2_17_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_21 := row2_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_12 := row2_12_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_18 := row2_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_19 := row2_19_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_13 := row2_13_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_14 := row2_14_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_16 := row2_16_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_20 := row2_20_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_8_identity u A X).symm
  have hz : ((40))*row3_8 u A X=0 := by
    simpa only [z2_7, z2_17, z2_21, z2_12, z2_18, z2_19, z2_13, z2_14, z2_16, z2_20,mul_zero,add_zero] using he
  have hunit : ((40):ℂ)=(40)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((40):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_8_zero
def row3_13 (u A X : ℂ) : ℂ := ((((((140)*A+((44)*X^2+(498)))*A+(((91)*X+(-26))*X+(512)))*A+((((-70)*X+(320))*X+(-180))*X+(-250)))*u+((((-48)*A+(-64))*A+(((16)*X^2+(-16))*X+(16)))*A+((((16)*X+(32))*X+(-64))*X+(-48))))*u)
theorem row3_13_identity (u A X : ℂ) :
  (((-1)*u))*row2_17 u A X+
  (((44)*u))*row2_18 u A X+
  (((44)*X))*row2_11 u A X=((1))*row3_13 u A X := by
  simp only [row2_17, row2_18, row2_11, row3_13] <;> ring
theorem row3_13_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_13 u A X=0 := by
  have z2_17 := row2_17_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_18 := row2_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_11 := row2_11_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_13_identity u A X).symm
  have hz : ((1))*row3_13 u A X=0 := by
    simpa only [z2_17, z2_18, z2_11,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_13_zero
def row3_16 (u A X : ℂ) : ℂ := (((((-1820)*A+((968)*X^3+(-11094)))*A+((((-1078)*X+(3943))*X+(5838))*X+(-21000)))*A+((((74)*X+(-2488))*X+(2340))*X+(2414)))*u+((((624)*A+(1888))*A+(((((352)*X+(496))*X+(-2464))*X+(1264))*X+(496)))*A+(((((352)*X+(496))*X+(-3232))*X+(1184))*X+(2032))))
theorem row3_16_identity (u A X : ℂ) :
  ((35))*row2_17 u A X+
  (((-7876)*u+((1056)*A+(352))))*row2_21 u A X+
  (((-3080)*A))*row2_18 u A X+
  (((22)*X))*row2_14 u A X=((1))*row3_16 u A X := by
  simp only [row2_17, row2_21, row2_18, row2_14, row3_16] <;> ring
theorem row3_16_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_16 u A X=0 := by
  have z2_17 := row2_17_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_21 := row2_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_18 := row2_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_14 := row2_14_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_16_identity u A X).symm
  have hz : ((1))*row3_16 u A X=0 := by
    simpa only [z2_17, z2_21, z2_18, z2_14,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_16_zero
def row3_18 (u A X : ℂ) : ℂ := ((((((-140)*A+(-542))*A+(((-47)*X+(70))*X+(-512)))*A+(((((44)*X+(26))*X+(-408))*X+(224))*X+(294)))*u+((((48)*A+(64))*A+(((-16)*X^2+(16))*X+(-16)))*A+((((-16)*X+(-32))*X+(64))*X+(48))))*u)
theorem row3_18_identity (u A X : ℂ) :
  (((1)*u))*row2_17 u A X=((1))*row3_18 u A X := by
  simp only [row2_17, row3_18] <;> ring
theorem row3_18_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_18 u A X=0 := by
  have z2_17 := row2_17_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_18_identity u A X).symm
  have hz : ((1))*row3_18 u A X=0 := by
    simpa only [z2_17,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_18_zero

def row3_19 (u A X : ℂ) : ℂ := ((((((-6160)*A+(-17268))*A+(3958))*A+(((((1936)*X+(1144))*X+(-13675))*X+(5554))*X+(37000)))*A+((((-6370)*X+(21200))*X+(-8460))*X+(-14830)))*u+(((((2112)*A+(560))*A+(-3712))*A+((((752)*X+(-704))*X+(2064))*X+(2864)))*A+((((((704)*X+(-704))*X+(-656))*X+(2208))*X+(-2304))*X+(-2256))))
theorem row3_19_identity (u A X : ℂ) :
  (((44)*A+(-47)))*row2_17 u A X+
  (((-1012)*u))*row2_21 u A X+
  (((2068)*X))*row2_18 u A X+
  (((704)*X))*row2_20 u A X=((1))*row3_19 u A X := by
  simp only [row2_17, row2_21, row2_18, row2_20, row3_19] <;> ring
theorem row3_19_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_19 u A X=0 := by
  have z2_17 := row2_17_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_21 := row2_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_18 := row2_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_20 := row2_20_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_19_identity u A X).symm
  have hz : ((1))*row3_19 u A X=0 := by
    simpa only [z2_17, z2_21, z2_18, z2_20,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_19_zero
def row3_21 (u A X : ℂ) : ℂ := (((((-1260)*A+(-1798))*A+((((2046)*X+(-4009))*X+(-3330))*X+(9736)))*A+(((((968)*X^2+(-470))*X+(-7456))*X+(3556))*X+(5022)))*u+((((432)*A+(-480))*A+(((((-352)*X+(-848))*X+(2464))*X+(-912))*X+(-848)))*A+(((((-352)*X+(-848))*X+(2528))*X+(224))*X+(-976))))
theorem row3_21_identity (u A X : ℂ) :
  (((22)*X+(-13)))*row2_17 u A X+
  (((8844)*u+((-1056)*A+(-352))))*row2_21 u A X+
  (((3080)*A))*row2_18 u A X=((1))*row3_21 u A X := by
  simp only [row2_17, row2_21, row2_18, row3_21] <;> ring
theorem row3_21_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_21 u A X=0 := by
  have z2_17 := row2_17_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_21 := row2_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_18 := row2_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_21_identity u A X).symm
  have hz : ((1))*row3_21 u A X=0 := by
    simpa only [z2_17, z2_21, z2_18,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_21_zero
def row3_22 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))*u^2)
theorem row3_22_identity (u A X : ℂ) :
  (((1)*u))*row2_18 u A X=((1))*row3_22 u A X := by
  simp only [row2_18, row3_22] <;> ring
theorem row3_22_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_22 u A X=0 := by
  have z2_18 := row2_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_22_identity u A X).symm
  have hz : ((1))*row3_22 u A X=0 := by
    simpa only [z2_18,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_22_zero
def row3_23 (u A X : ℂ) : ℂ := ((((((1)*X+(-1))*A+(1))*A+((((1)*X+(-2))*X+(-1))*X+(1)))*A+(((-1)*X+(2))*X^2+(-1)))*u)
theorem row3_23_identity (u A X : ℂ) :
  (((-1)*u))*row2_21 u A X+
  (((1)*A))*row2_18 u A X=((1))*row3_23 u A X := by
  simp only [row2_21, row2_18, row3_23] <;> ring
theorem row3_23_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_23 u A X=0 := by
  have z2_21 := row2_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_18 := row2_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_23_identity u A X).symm
  have hz : ((1))*row3_23 u A X=0 := by
    simpa only [z2_21, z2_18,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_23_zero
def row3_25 (u A X : ℂ) : ℂ := (((((140)*A+((44)*X^2+(498)))*A+(((91)*X+(-26))*X+(512)))*A+((((-70)*X+(320))*X+(-180))*X+(-250)))*u+((((-48)*A+(-64))*A+(((16)*X^2+(-16))*X+(16)))*A+((((16)*X+(32))*X+(-64))*X+(-48))))
theorem row3_25_identity (u A X : ℂ) :
  ((-1))*row2_17 u A X+
  (((44)*u))*row2_21 u A X+
  (((44)*X))*row2_18 u A X=((1))*row3_25 u A X := by
  simp only [row2_17, row2_21, row2_18, row3_25] <;> ring
theorem row3_25_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_25 u A X=0 := by
  have z2_17 := row2_17_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_21 := row2_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_18 := row2_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_25_identity u A X).symm
  have hz : ((1))*row3_25 u A X=0 := by
    simpa only [z2_17, z2_21, z2_18,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_25_zero
def row3_27 (u A X : ℂ) : ℂ := ((((1)*X^3+(-1))*A+((((1)*X+(1))*X+(1))*X))*A+((((((1)*X+(-1))*X+(-1))*X+(-1))*X+(1))*X+(1)))
theorem row3_27_identity (u A X : ℂ) :
  ((1))*row2_21 u A X+
  (((1)*X))*row2_20 u A X=((1))*row3_27 u A X := by
  simp only [row2_21, row2_20, row3_27] <;> ring
theorem row3_27_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_27 u A X=0 := by
  have z2_21 := row2_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z2_20 := row2_20_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_27_identity u A X).symm
  have hz : ((1))*row3_27 u A X=0 := by
    simpa only [z2_21, z2_20,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_27_zero

def row3_28 (u A X : ℂ) : ℂ := (((((-140)*A+(-542))*A+(((-47)*X+(70))*X+(-512)))*A+(((((44)*X+(26))*X+(-408))*X+(224))*X+(294)))*u+((((48)*A+(64))*A+(((-16)*X^2+(16))*X+(-16)))*A+((((-16)*X+(-32))*X+(64))*X+(48))))
theorem row3_28_identity (u A X : ℂ) :
  ((1))*row2_17 u A X=((1))*row3_28 u A X := by
  simp only [row2_17, row3_28] <;> ring
theorem row3_28_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_28 u A X=0 := by
  have z2_17 := row2_17_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_28_identity u A X).symm
  have hz : ((1))*row3_28 u A X=0 := by
    simpa only [z2_17,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_28_zero
def row3_29 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))*u)
theorem row3_29_identity (u A X : ℂ) :
  (((1)*u))*row2_21 u A X=((1))*row3_29 u A X := by
  simp only [row2_21, row3_29] <;> ring
theorem row3_29_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_29 u A X=0 := by
  have z2_21 := row2_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_29_identity u A X).symm
  have hz : ((1))*row3_29 u A X=0 := by
    simpa only [z2_21,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_29_zero
def row3_30 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+(1))*A+((((1)*X+(-2))*X+(-1))*X+(1)))*A+(((-1)*X+(2))*X^2+(-1)))
theorem row3_30_identity (u A X : ℂ) :
  (((1)*A+(-1)))*row2_21 u A X=((1))*row3_30 u A X := by
  simp only [row2_21, row3_30] <;> ring
theorem row3_30_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_30 u A X=0 := by
  have z2_21 := row2_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_30_identity u A X).symm
  have hz : ((1))*row3_30 u A X=0 := by
    simpa only [z2_21,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_30_zero
def row3_31 (u A X : ℂ) : ℂ := ((((1)*X^2+(-1))*A+(((1)*X+(1))*X))*A+(((((1)*X+(-1))*X+(-2))*X+(1))*X+(1)))
theorem row3_31_identity (u A X : ℂ) :
  (((1)*X+(1)))*row2_21 u A X=((1))*row3_31 u A X := by
  simp only [row2_21, row3_31] <;> ring
theorem row3_31_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_31 u A X=0 := by
  have z2_21 := row2_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_31_identity u A X).symm
  have hz : ((1))*row3_31 u A X=0 := by
    simpa only [z2_21,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_31_zero
def row3_32 (u A X : ℂ) : ℂ := ((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))
theorem row3_32_identity (u A X : ℂ) :
  ((1))*row2_21 u A X=((1))*row3_32 u A X := by
  simp only [row2_21, row3_32] <;> ring
theorem row3_32_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row3_32 u A X=0 := by
  have z2_21 := row2_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row3_32_identity u A X).symm
  have hz : ((1))*row3_32 u A X=0 := by
    simpa only [z2_21,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row3_32_zero
def row4_10 (u A X : ℂ) : ℂ := ((((((639072)*A+((7920)*X^3+(3511800)))*A+(((197676)*X+(683928))*X+(3833424)))*A+((((89928)*X+(1174032))*X+(-1353888))*X+(-1263960)))*u+(((((632016)*A+(762852))*A+(-3107110))*A+((((-464872)*X+(911659))*X+(1097070))*X+(-8108088)))*A+((((2286674)*X+(-5024688))*X+(451340))*X+(2738014))))*u+(((((-57024)*A+(431184))*A+(833280))*A+((((-100080)*X+(19008))*X+(24048))*X+(-157104)))*A+((((((-19008)*X+(19008))*X+(-62064))*X+(-219168))*X+(381312))*X+(300240))))
theorem row4_10_identity (u A X : ℂ) :
  ((49))*row3_7 u A X+
  (((29799)*u+((-13464)*A+(918))))*row3_28 u A X+
  (((-14535972)*u+((1777248)*A+((-632808)*X))))*row3_29 u A X+
  (((902088)*u))*row3_32 u A X+
  (((-5183640)*A))*row3_22 u A X+
  (((7920)*X))*row3_13 u A X+
  (((-29106)*X))*row3_18 u A X+
  (((-215424)*X))*row3_31 u A X=((44))*row4_10 u A X := by
  simp only [row3_7, row3_28, row3_29, row3_32, row3_22, row3_13, row3_18, row3_31, row4_10] <;> ring
theorem row4_10_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_10 u A X=0 := by
  have z3_7 := row3_7_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_22 := row3_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_13 := row3_13_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_18 := row3_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_31 := row3_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_10_identity u A X).symm
  have hz : ((44))*row4_10 u A X=0 := by
    simpa only [z3_7, z3_28, z3_29, z3_32, z3_22, z3_13, z3_18, z3_31,mul_zero,add_zero] using he
  have hunit : ((44):ℂ)=(44)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((44):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_10_zero

def row4_14 (u A X : ℂ) : ℂ := (((((((-3049200)*A+(-50534748))*A+(-229340430))*A+((((958320)*X^2+(-17389449))*X+(-38095002))*X+(-238837896)))*A+((((-8888022)*X+(-66190608))*X+(83966652))*X+(75078630)))*u+(((((-38944224)*A+(-46790808))*A+(196897820))*A+((((29633648)*X+(-57600446))*X+(-67822140))*X+(513308352)))*A+((((-146003716)*X+(321143232))*X+(-29135800))*X+(-175139516))))*u+(((((3459456)*A+(-27714336))*A+(-52734720))*A+(((((126720)*X+(6599520))*X+(-2040192))*X+(-1353312))*X+(10058976)))*A+((((((1153152)*X+(-1026432))*X+(4293216))*X+(12831552))*X+(-24104448))*X+(-18531360))))
theorem row4_14_identity (u A X : ℂ) :
  ((-143))*row3_7 u A X+
  (((-96723)*u+((30888)*A+(23094))))*row3_28 u A X+
  (((-8437176)*u+((760320)*A+(253440))))*row3_32 u A X+
  (((33144804)*u+((-6294816)*A+((1451736)*X))))*row3_29 u A X+
  (((43560)*A+((84942)*X)))*row3_18 u A X+
  (((11891880)*A+((2047320)*X)))*row3_22 u A X+
  (((15840)*X))*row3_25 u A X+
  (((494208)*X))*row3_31 u A X=((2))*row4_14 u A X := by
  simp only [row3_7, row3_28, row3_32, row3_29, row3_18, row3_22, row3_25, row3_31, row4_14] <;> ring
theorem row4_14_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_14 u A X=0 := by
  have z3_7 := row3_7_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_18 := row3_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_22 := row3_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_25 := row3_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_31 := row3_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_14_identity u A X).symm
  have hz : ((2))*row4_14 u A X=0 := by
    simpa only [z3_7, z3_28, z3_32, z3_29, z3_18, z3_22, z3_25, z3_31,mul_zero,add_zero] using he
  have hunit : ((2):ℂ)=(2)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((2):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_14_zero
def row4_21 (u A X : ℂ) : ℂ := (((((((6322821120)*A+(35697594240))*A+(((5993507520)*X+(6981448320))*X+(30823752960)))*A+((((-1712430720)*X+(18178110720))*X+(-14753249280))*X+(-16465680000)))*u+(((((1660594320)*A+(-75428589852))*A+(-401423403150))*A+(((-22431604041)*X+(-65271276378))*X+(-437547676104)))*A+((((19010288682)*X+(-173672996112))*X+(135652418748))*X+(154662707430))))*u+(((((-52422035424)*A+(-47085750336))*A+(298150667912))*A+((((41829855716)*X+(-89276189708))*X+(-87319084920))*X+(759455185584)))*A+((((-197841495160)*X+(407125533840))*X+(-11442543520))*X+(-209284038680))))*u+((((((-496793088)*A+(333793152))*A+(-44351518080))*A+(-77917217856))*A+(((((-709803072)*X+(6099192576))*X+(5450051904))*X+(-7377951552))*X+(7542824832)))*A+(((((((204906240)*X+(917228928))*X+(-3636785856))*X+(6274488576))*X+(22791319680))*X+(-30655333824))*X+(-25568454528))))
theorem row4_21_identity (u A X : ℂ) :
  (((-6930)*A+((-18480)*X+(-224147))))*row3_7 u A X+
  (((-69174567)*u+((-123976776)*A+((-52529400)*X+(176680674)))))*row3_28 u A X+
  (((70121455272)*u+((-5444208000)*A+((-2790070272)*X+(611614080)))))*row3_32 u A X+
  (((3465)*u))*row3_8 u A X+
  (((101628555336)*u+((45720891216)*A+((14239702488)*X))))*row3_29 u A X+
  (((26528040)*A+((133143318)*X)))*row3_18 u A X+
  (((-595188)*A+((249480)*X)))*row3_19 u A X+
  (((27470700180)*A+((1526048370)*X)))*row3_22 u A X+
  (((11313751680)*A))*row3_23 u A X+
  (((-1229437440)*A))*row3_30 u A X+
  (((9948015)*X))*row3_13 u A X+
  (((1190376)*X))*row3_16 u A X+
  (((249480)*X))*row3_21 u A X+
  (((-300810312)*X))*row3_25 u A X+
  (((-927315840)*X))*row3_31 u A X=((2))*row4_21 u A X := by
  simp only [row3_7, row3_28, row3_32, row3_8, row3_29, row3_18, row3_19, row3_22, row3_23, row3_30, row3_13, row3_16, row3_21, row3_25, row3_31, row4_21] <;> ring
theorem row4_21_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_21 u A X=0 := by
  have z3_7 := row3_7_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_8 := row3_8_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_18 := row3_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_19 := row3_19_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_22 := row3_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_23 := row3_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_30 := row3_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_13 := row3_13_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_16 := row3_16_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_21 := row3_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_25 := row3_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_31 := row3_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_21_identity u A X).symm
  have hz : ((2))*row4_21 u A X=0 := by
    simpa only [z3_7, z3_28, z3_32, z3_8, z3_29, z3_18, z3_19, z3_22, z3_23, z3_30, z3_13, z3_16, z3_21, z3_25, z3_31,mul_zero,add_zero] using he
  have hunit : ((2):ℂ)=(2)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((2):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_21_zero
def row4_22 (u A X : ℂ) : ℂ := (((((((67760)*A+(114488))*A+(-792216))*A+(-2450342))*A+((((196856)*X+(-610471))*X+(126410))*X+(-1348036)))*A+((((371666)*X+(-1330312))*X+(586980))*X+(958646)))*u+((((((-23232)*A+(19712))*A+(231856))*A+(168576))*A+(((((23232)*X+(-90896))*X+(-9152))*X+(127504))*X+(-1488)))*A+((((((24640)*X+(-9152))*X+(-132432))*X+(-79712))*X+(248832))*X+(156528))))
theorem row4_22_identity (u A X : ℂ) :
  (((539)*A+(3261)))*row3_28 u A X+
  (((-88)*u+((-7744)*X)))*row3_32 u A X+
  (((-11)*A))*row3_19 u A X+
  (((22)*X))*row3_16 u A X+
  (((286)*X))*row3_25 u A X+
  (((-125092)*X))*row3_29 u A X+
  (((16896)*X))*row3_31 u A X=((1))*row4_22 u A X := by
  simp only [row3_28, row3_32, row3_19, row3_16, row3_25, row3_29, row3_31, row4_22] <;> ring
theorem row4_22_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_22 u A X=0 := by
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_19 := row3_19_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_16 := row3_16_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_25 := row3_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_31 := row3_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_22_identity u A X).symm
  have hz : ((1))*row4_22 u A X=0 := by
    simpa only [z3_28, z3_32, z3_19, z3_16, z3_25, z3_29, z3_31,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_22_zero
def row4_23 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))*u^3)
theorem row4_23_identity (u A X : ℂ) :
  (((1)*u))*row3_22 u A X=((1))*row4_23 u A X := by
  simp only [row3_22, row4_23] <;> ring
theorem row4_23_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_23 u A X=0 := by
  have z3_22 := row3_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_23_identity u A X).symm
  have hz : ((1))*row4_23 u A X=0 := by
    simpa only [z3_22,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_23_zero
def row4_24 (u A X : ℂ) : ℂ := (((((((21780)*X+(-1636668))*A+(-8874360))*A+(((-452034)*X+(-1592712))*X+(-9868716)))*A+((((-242352)*X+(-2905848))*X+(3390552))*X+(3148200)))*u+(((((-1538064)*A+(-1785108))*A+(7783870))*A+((((1153768)*X+(-2243191))*X+(-2715270))*X+(19978872)))*A+((((-5617466)*X+(12330672))*X+(-1095740))*X+(-6713206))))*u+(((((133056)*A+(-1074576))*A+(-2054400))*A+((((246960)*X+(-44352))*X+(-69552))*X+(380016)))*A+((((((44352)*X+(-44352))*X+(158256))*X+(538272))*X+(-943488))*X+(-740880))))
theorem row4_24_identity (u A X : ℂ) :
  ((-11))*row3_7 u A X+
  (((-3861)*u+((2376)*A+(-162))))*row3_28 u A X+
  (((2539548)*u+((-313632)*A+((111672)*X))))*row3_29 u A X+
  (((-159192)*u))*row3_32 u A X+
  (((1001880)*A))*row3_22 u A X+
  (((6534)*X))*row3_18 u A X+
  (((38016)*X))*row3_31 u A X=((4))*row4_24 u A X := by
  simp only [row3_7, row3_28, row3_29, row3_32, row3_22, row3_18, row3_31, row4_24] <;> ring
theorem row4_24_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_24 u A X=0 := by
  have z3_7 := row3_7_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_22 := row3_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_18 := row3_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_31 := row3_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_24_identity u A X).symm
  have hz : ((4))*row4_24 u A X=0 := by
    simpa only [z3_7, z3_28, z3_29, z3_32, z3_22, z3_18, z3_31,mul_zero,add_zero] using he
  have hunit : ((4):ℂ)=(4)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((4):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_24_zero
def row4_25 (u A X : ℂ) : ℂ := (((((((968)*X+(-968))*A+(8948))*A+(33006))*A+((((110)*X+(1997))*X+(-6014))*X+(42560)))*A+((((-2186)*X+(14632))*X+(-10260))*X+(-12446)))*u+((((-2736)*A+(-4704))*A+(((((-352)*X+(208))*X+(2464))*X+(-1968))*X+(208)))*A+(((((-352)*X+(208))*X+(4640))*X+(-4000))*X+(-4144))))
theorem row4_25_identity (u A X : ℂ) :
  ((-79))*row3_28 u A X+
  (((10780)*u+((-1056)*A+(-352))))*row3_32 u A X+
  (((968)*A))*row3_23 u A X+
  (((3080)*A+((1936)*X)))*row3_29 u A X+
  (((-22)*X))*row3_25 u A X=((1))*row4_25 u A X := by
  simp only [row3_28, row3_32, row3_23, row3_29, row3_25, row4_25] <;> ring
theorem row4_25_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_25 u A X=0 := by
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_23 := row3_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_25 := row3_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_25_identity u A X).symm
  have hz : ((1))*row4_25 u A X=0 := by
    simpa only [z3_28, z3_32, z3_23, z3_29, z3_25,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_25_zero

def row4_27 (u A X : ℂ) : ℂ := ((((((140)*A+((44)*X^2+(498)))*A+(((91)*X+(-26))*X+(512)))*A+((((-70)*X+(320))*X+(-180))*X+(-250)))*u+((((-48)*A+(-64))*A+(((16)*X^2+(-16))*X+(16)))*A+((((16)*X+(32))*X+(-64))*X+(-48))))*u)
theorem row4_27_identity (u A X : ℂ) :
  (((-1)*u))*row3_28 u A X+
  (((44)*u))*row3_29 u A X+
  (((44)*X))*row3_22 u A X=((1))*row4_27 u A X := by
  simp only [row3_28, row3_29, row3_22, row4_27] <;> ring
theorem row4_27_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_27 u A X=0 := by
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_22 := row3_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_27_identity u A X).symm
  have hz : ((1))*row4_27 u A X=0 := by
    simpa only [z3_28, z3_29, z3_22,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_27_zero
def row4_30 (u A X : ℂ) : ℂ := ((((((1614888)*A+(8896140))*A+((((21780)*X+(408474))*X+(1570932))*X+(9890496)))*A+((((220572)*X+(2949408))*X+(-3390552))*X+(-3169980)))*u+(((((1538064)*A+(1785108))*A+(-7783870))*A+((((-1153768)*X+(2243191))*X+(2715270))*X+(-19978872)))*A+((((5617466)*X+(-12330672))*X+(1095740))*X+(6713206))))*u+(((((-133056)*A+(1074576))*A+(2054400))*A+((((-246960)*X+(44352))*X+(69552))*X+(-380016)))*A+((((((-44352)*X+(44352))*X+(-158256))*X+(-538272))*X+(943488))*X+(740880))))
theorem row4_30_identity (u A X : ℂ) :
  ((11))*row3_7 u A X+
  (((3861)*u+((-2376)*A+(162))))*row3_28 u A X+
  (((-2626668)*u+((313632)*A+((-111672)*X))))*row3_29 u A X+
  (((159192)*u))*row3_32 u A X+
  (((-914760)*A))*row3_22 u A X+
  (((-6534)*X))*row3_18 u A X+
  (((-38016)*X))*row3_31 u A X=((4))*row4_30 u A X := by
  simp only [row3_7, row3_28, row3_29, row3_32, row3_22, row3_18, row3_31, row4_30] <;> ring
theorem row4_30_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_30 u A X=0 := by
  have z3_7 := row3_7_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_22 := row3_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_18 := row3_18_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_31 := row3_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_30_identity u A X).symm
  have hz : ((4))*row4_30 u A X=0 := by
    simpa only [z3_7, z3_28, z3_29, z3_32, z3_22, z3_18, z3_31,mul_zero,add_zero] using he
  have hunit : ((4):ℂ)=(4)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((4):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_30_zero
def row4_31 (u A X : ℂ) : ℂ := (((((-1820)*A+((968)*X^3+(-11094)))*A+((((-1078)*X+(3943))*X+(5838))*X+(-21000)))*A+((((74)*X+(-2488))*X+(2340))*X+(2414)))*u+((((624)*A+(1888))*A+(((((352)*X+(496))*X+(-2464))*X+(1264))*X+(496)))*A+(((((352)*X+(496))*X+(-3232))*X+(1184))*X+(2032))))
theorem row4_31_identity (u A X : ℂ) :
  ((35))*row3_28 u A X+
  (((-7876)*u+((1056)*A+(352))))*row3_32 u A X+
  (((-3080)*A))*row3_29 u A X+
  (((22)*X))*row3_25 u A X=((1))*row4_31 u A X := by
  simp only [row3_28, row3_32, row3_29, row3_25, row4_31] <;> ring
theorem row4_31_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_31 u A X=0 := by
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_25 := row3_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_31_identity u A X).symm
  have hz : ((1))*row4_31 u A X=0 := by
    simpa only [z3_28, z3_32, z3_29, z3_25,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_31_zero
def row4_33 (u A X : ℂ) : ℂ := ((((((-140)*A+(-542))*A+(((-47)*X+(70))*X+(-512)))*A+(((((44)*X+(26))*X+(-408))*X+(224))*X+(294)))*u+((((48)*A+(64))*A+(((-16)*X^2+(16))*X+(-16)))*A+((((-16)*X+(-32))*X+(64))*X+(48))))*u)
theorem row4_33_identity (u A X : ℂ) :
  (((1)*u))*row3_28 u A X=((1))*row4_33 u A X := by
  simp only [row3_28, row4_33] <;> ring
theorem row4_33_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_33 u A X=0 := by
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_33_identity u A X).symm
  have hz : ((1))*row4_33 u A X=0 := by
    simpa only [z3_28,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_33_zero
def row4_34 (u A X : ℂ) : ℂ := ((((((-6160)*A+(-17268))*A+(3958))*A+(((((1936)*X+(1144))*X+(-13675))*X+(5554))*X+(37000)))*A+((((-6370)*X+(21200))*X+(-8460))*X+(-14830)))*u+(((((2112)*A+(560))*A+(-3712))*A+((((752)*X+(-704))*X+(2064))*X+(2864)))*A+((((((704)*X+(-704))*X+(-656))*X+(2208))*X+(-2304))*X+(-2256))))
theorem row4_34_identity (u A X : ℂ) :
  (((44)*A+(-47)))*row3_28 u A X+
  (((-1012)*u))*row3_32 u A X+
  (((2068)*X))*row3_29 u A X+
  (((704)*X))*row3_31 u A X=((1))*row4_34 u A X := by
  simp only [row3_28, row3_32, row3_29, row3_31, row4_34] <;> ring
theorem row4_34_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_34 u A X=0 := by
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_31 := row3_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_34_identity u A X).symm
  have hz : ((1))*row4_34 u A X=0 := by
    simpa only [z3_28, z3_32, z3_29, z3_31,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_34_zero
def row4_35 (u A X : ℂ) : ℂ := ((((1)*X^4+(-1))*A+(((((1)*X+(1))*X+(1))*X+(1))*X))*A+((((((1)*X+(-1))*X+(-1))*X^2+(-1))*X+(1))*X+(1)))
theorem row4_35_identity (u A X : ℂ) :
  ((1))*row3_32 u A X+
  (((1)*X))*row3_27 u A X=((1))*row4_35 u A X := by
  simp only [row3_32, row3_27, row4_35] <;> ring
theorem row4_35_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_35 u A X=0 := by
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_27 := row3_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_35_identity u A X).symm
  have hz : ((1))*row4_35 u A X=0 := by
    simpa only [z3_32, z3_27,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_35_zero

def row4_36 (u A X : ℂ) : ℂ := (((((-1260)*A+(-1798))*A+((((2046)*X+(-4009))*X+(-3330))*X+(9736)))*A+(((((968)*X^2+(-470))*X+(-7456))*X+(3556))*X+(5022)))*u+((((432)*A+(-480))*A+(((((-352)*X+(-848))*X+(2464))*X+(-912))*X+(-848)))*A+(((((-352)*X+(-848))*X+(2528))*X+(224))*X+(-976))))
theorem row4_36_identity (u A X : ℂ) :
  (((22)*X+(-13)))*row3_28 u A X+
  (((8844)*u+((-1056)*A+(-352))))*row3_32 u A X+
  (((3080)*A))*row3_29 u A X=((1))*row4_36 u A X := by
  simp only [row3_28, row3_32, row3_29, row4_36] <;> ring
theorem row4_36_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_36 u A X=0 := by
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_36_identity u A X).symm
  have hz : ((1))*row4_36 u A X=0 := by
    simpa only [z3_28, z3_32, z3_29,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_36_zero
def row4_37 (u A X : ℂ) : ℂ := ((((((-20072448)*A+(-113325696))*A+(((-19027008)*X+(-22163328))*X+(-97853184)))*A+((((5436288)*X+(-57708288))*X+(46835712))*X+(52272000)))*u+(((((-12470480)*A+(-26808092))*A+(-11127806))*A+((((9208540)*X+(-45061321))*X+(-49834))*X+(133520184)))*A+((((-38364022)*X+(30406432))*X+(46321612))*X+(7957590))))*u+(((((-1529088)*A+(-7439216))*A+(-8099584))*A+((((((487872)*X+(-639936))*X+(-4335216))*X+(-865216))*X+(-6339536))*X+(-1821936)))*A+(((((((487872)*X+(-4389440))*X+(613184))*X+(2492176))*X+(9650464))*X+(1569856))*X+(-2640048))))
theorem row4_37_identity (u A X : ℂ) :
  ((-11))*row3_8 u A X+
  (((-81378)*A+(-2466)))*row3_28 u A X+
  (((16793964)*u+((-2846448)*A+((-1254528)*X+(793584)))))*row3_32 u A X+
  (((1829520)*A))*row3_23 u A X+
  (((12945636)*A+((-165726)*X)))*row3_29 u A X+
  (((-627264)*A))*row3_30 u A X+
  (((297)*X))*row3_19 u A X+
  (((1584)*X))*row3_21 u A X+
  (((-41580)*X))*row3_25 u A X+
  (((-674784)*X))*row3_31 u A X=((2))*row4_37 u A X := by
  simp only [row3_8, row3_28, row3_32, row3_23, row3_29, row3_30, row3_19, row3_21, row3_25, row3_31, row4_37] <;> ring
theorem row4_37_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_37 u A X=0 := by
  have z3_8 := row3_8_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_23 := row3_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_30 := row3_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_19 := row3_19_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_21 := row3_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_25 := row3_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_31 := row3_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_37_identity u A X).symm
  have hz : ((2))*row4_37 u A X=0 := by
    simpa only [z3_8, z3_28, z3_32, z3_23, z3_29, z3_30, z3_19, z3_21, z3_25, z3_31,mul_zero,add_zero] using he
  have hunit : ((2):ℂ)=(2)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((2):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_37_zero
def row4_38 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))*u^2)
theorem row4_38_identity (u A X : ℂ) :
  (((1)*u))*row3_29 u A X=((1))*row4_38 u A X := by
  simp only [row3_29, row4_38] <;> ring
theorem row4_38_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_38 u A X=0 := by
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_38_identity u A X).symm
  have hz : ((1))*row4_38 u A X=0 := by
    simpa only [z3_29,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_38_zero
def row4_39 (u A X : ℂ) : ℂ := ((((((1)*X+(-1))*A+(1))*A+((((1)*X+(-2))*X+(-1))*X+(1)))*A+(((-1)*X+(2))*X^2+(-1)))*u)
theorem row4_39_identity (u A X : ℂ) :
  (((-1)*u))*row3_32 u A X+
  (((1)*A))*row3_29 u A X=((1))*row4_39 u A X := by
  simp only [row3_32, row3_29, row4_39] <;> ring
theorem row4_39_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_39 u A X=0 := by
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_39_identity u A X).symm
  have hz : ((1))*row4_39 u A X=0 := by
    simpa only [z3_32, z3_29,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_39_zero
def row4_40 (u A X : ℂ) : ℂ := ((((((1)*X+(-1))*A+(1))*A+(-1))*A+((((-2)*X+(3))*X+(2))*X+(-1)))*A+(((((-1)*X+(3))*X^2+(-5))*X+(1))*X+(2)))
theorem row4_40_identity (u A X : ℂ) :
  (((2)*X+(2)))*row3_32 u A X+
  (((1)*A))*row3_30 u A X+
  (((-1)*X))*row3_31 u A X=((1))*row4_40 u A X := by
  simp only [row3_32, row3_30, row3_31, row4_40] <;> ring
theorem row4_40_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_40 u A X=0 := by
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_30 := row3_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_31 := row3_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_40_identity u A X).symm
  have hz : ((1))*row4_40 u A X=0 := by
    simpa only [z3_32, z3_30, z3_31,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_40_zero
def row4_41 (u A X : ℂ) : ℂ := (((((140)*A+((44)*X^2+(498)))*A+(((91)*X+(-26))*X+(512)))*A+((((-70)*X+(320))*X+(-180))*X+(-250)))*u+((((-48)*A+(-64))*A+(((16)*X^2+(-16))*X+(16)))*A+((((16)*X+(32))*X+(-64))*X+(-48))))
theorem row4_41_identity (u A X : ℂ) :
  ((-1))*row3_28 u A X+
  (((44)*u))*row3_32 u A X+
  (((44)*X))*row3_29 u A X=((1))*row4_41 u A X := by
  simp only [row3_28, row3_32, row3_29, row4_41] <;> ring
theorem row4_41_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_41 u A X=0 := by
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_29 := row3_29_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_41_identity u A X).symm
  have hz : ((1))*row4_41 u A X=0 := by
    simpa only [z3_28, z3_32, z3_29,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_41_zero

def row4_43 (u A X : ℂ) : ℂ := ((((1)*X^3+(-1))*A+((((1)*X+(1))*X+(1))*X))*A+((((((1)*X+(-1))*X+(-1))*X+(-1))*X+(1))*X+(1)))
theorem row4_43_identity (u A X : ℂ) :
  ((1))*row3_32 u A X+
  (((1)*X))*row3_31 u A X=((1))*row4_43 u A X := by
  simp only [row3_32, row3_31, row4_43] <;> ring
theorem row4_43_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_43 u A X=0 := by
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have z3_31 := row3_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_43_identity u A X).symm
  have hz : ((1))*row4_43 u A X=0 := by
    simpa only [z3_32, z3_31,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_43_zero
def row4_44 (u A X : ℂ) : ℂ := (((((-140)*A+(-542))*A+(((-47)*X+(70))*X+(-512)))*A+(((((44)*X+(26))*X+(-408))*X+(224))*X+(294)))*u+((((48)*A+(64))*A+(((-16)*X^2+(16))*X+(-16)))*A+((((-16)*X+(-32))*X+(64))*X+(48))))
theorem row4_44_identity (u A X : ℂ) :
  ((1))*row3_28 u A X=((1))*row4_44 u A X := by
  simp only [row3_28, row4_44] <;> ring
theorem row4_44_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_44 u A X=0 := by
  have z3_28 := row3_28_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_44_identity u A X).symm
  have hz : ((1))*row4_44 u A X=0 := by
    simpa only [z3_28,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_44_zero
def row4_45 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))*u)
theorem row4_45_identity (u A X : ℂ) :
  (((1)*u))*row3_32 u A X=((1))*row4_45 u A X := by
  simp only [row3_32, row4_45] <;> ring
theorem row4_45_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_45 u A X=0 := by
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_45_identity u A X).symm
  have hz : ((1))*row4_45 u A X=0 := by
    simpa only [z3_32,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_45_zero
def row4_46 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+(1))*A+((((1)*X+(-2))*X+(-1))*X+(1)))*A+(((-1)*X+(2))*X^2+(-1)))
theorem row4_46_identity (u A X : ℂ) :
  (((1)*A+(-1)))*row3_32 u A X=((1))*row4_46 u A X := by
  simp only [row3_32, row4_46] <;> ring
theorem row4_46_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_46 u A X=0 := by
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_46_identity u A X).symm
  have hz : ((1))*row4_46 u A X=0 := by
    simpa only [z3_32,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_46_zero
def row4_47 (u A X : ℂ) : ℂ := ((((1)*X^2+(-1))*A+(((1)*X+(1))*X))*A+(((((1)*X+(-1))*X+(-2))*X+(1))*X+(1)))
theorem row4_47_identity (u A X : ℂ) :
  (((1)*X+(1)))*row3_32 u A X=((1))*row4_47 u A X := by
  simp only [row3_32, row4_47] <;> ring
theorem row4_47_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_47 u A X=0 := by
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_47_identity u A X).symm
  have hz : ((1))*row4_47 u A X=0 := by
    simpa only [z3_32,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_47_zero
def row4_48 (u A X : ℂ) : ℂ := ((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))
theorem row4_48_identity (u A X : ℂ) :
  ((1))*row3_32 u A X=((1))*row4_48 u A X := by
  simp only [row3_32, row4_48] <;> ring
theorem row4_48_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row4_48 u A X=0 := by
  have z3_32 := row3_32_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row4_48_identity u A X).symm
  have hz : ((1))*row4_48 u A X=0 := by
    simpa only [z3_32,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row4_48_zero

def row5_1 (u A X : ℂ) : ℂ := (((((((5693419245991775387443200)*A^2+(-127235317527189375198211440))*A+(((-88441856272876014503262360)*X+(-47935179930348201605138640))*X+(-7752835738877862890869920)))*A+((((52934713705734729367237200)*X+(-189610135487931821724784800))*X+(83740708076462362990310400))*X+(136675421782197092357547600)))*u+(((111746376602631415776905730)*A+(((-172660422704546076267383955)*X+(380586286220526653663578050))*X+(522117457090229408625508500)))*A+((((179356530584653564959234990)*X+(-411018243824851464165310980))*X+(52305182655544334246841000))*X+(231661713240197899206075990))))*u+(((((79095438048284924559701672)*A+(30002886957595613300633216))*A+(-434081888330020242300077758))*A+((((-56471182186227469173341521)*X+(33853392217373049780508711))*X+(-3345622560671474661337550))*X+(-881716417365902066077129524)))*A+((((437017758195217730625030454)*X+(-1020261893876996348841615388))*X+(146226377486560887591554480))*X+(583244135681778618216584934))))*u+(((((((-447340083613639494727680)*A+(-8428732945570987924235328))*A+(-11936576387953925353506432))*A+(89873669614877601888319424))*A+(95708022275750377977964144))*A+(((((-6363673879788992898594672)*X+(-54485789120420901113311104))*X+(97193474799168662513583952))*X+(-3108454835303414014588144))*X+(-30190675271825876685827712)))*A+((((((5711794316715948068960000)*X+(-1425650456447451268480688))*X+(-84088345639341465556343488))*X+(69332895994682780610141632))*X+(74561775069762763963187408))*X+(471367607405743276283232))))
theorem row5_1_identity (u A X : ℂ) :
  (((1795603268969654416715520)*u+((-763510661236088673147240)*A+((1135807084271871008689560)*X+(1426164950776496745828420)))))*row4_30 u A X+
  (((161175711821611790602530)*u+((-28349182046921772960)*A+((-8025613228692472422240)*X+(-20495124181569202579040)))))*row4_37 u A X+
  (((2834938249856068348726547954184)*u+((2846491747715800027051403120640)*A+((-2462908202230488751717364308032)*X+(-1100686955769281610368021494848)))))*row4_48 u A X+
  (((3353151780519006588328926720)*u+((-562224506714576149301332200)*A)))*row4_33 u A X+
  (((-808137198969785068597954836480)*u+((195594315925742411367360163680)*A+((240414918550197287107971771000)*X))))*row4_38 u A X+
  (((-15209028749049900775220890350)*u+((191251968319582117066500177843)*A+((17888857106445403882557636960)*X))))*row4_44 u A X+
  (((1499381642299239867718585415160)*u+((-13179267056618040811609041000564)*A+((6156759941590965284052402269100)*X))))*row4_45 u A X+
  (((10443304592592081139776)*A))*row4_14 u A X+
  (((19176100977950938560)*A+((19041104872965596784)*X)))*row4_21 u A X+
  (((-120393500038921792379279278080)*A+((-114932105415628304450417971200)*X)))*row4_23 u A X+
  (((-1451769999934388961199296)*A))*row4_24 u A X+
  (((2532926690110017887874813450)*A))*row4_25 u A X+
  (((-455339161480126976761207653)*A+((-40616279379046171231837560)*X)))*row4_34 u A X+
  (((3842300719386433063016465987592)*A))*row4_39 u A X+
  (((-831182694491740938757451857728)*A))*row4_40 u A X+
  (((859494226963015487365450967808)*A))*row4_46 u A X+
  (((-1263639855703641817912896)*X))*row4_10 u A X+
  (((-36184667001571684112497335)*X))*row4_22 u A X+
  (((377937777311863893207883800)*X))*row4_27 u A X+
  (((910678322960253953522415306)*X))*row4_31 u A X+
  (((13830772143595819217541120)*X))*row4_35 u A X+
  (((-81232558758092342463675120)*X))*row4_36 u A X+
  (((-89233280471849715846895890765)*X))*row4_41 u A X+
  (((903859933081722429533372245440)*X))*row4_43 u A X+
  (((337708271268075789665607672000)*X))*row4_47 u A X=((21296))*row5_1 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_14, row4_21, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_10, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_1] <;> ring
theorem row5_1_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_1 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_14 := row4_14_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_10 := row4_10_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_1_identity u A X).symm
  have hz : ((21296))*row5_1 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_14, z4_21, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_10, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((21296):ℂ)=(21296)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((21296):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_1_zero
def row5_2 (u A X : ℂ) : ℂ := ((((((26149228606296734400)*A^3+(1576287212028861170520))*A+(((-15961255262788834548)*X+(726450102914418154008))*X+(2416374843447192973488)))*A+((((12738472768493845560)*X+(846758746070320792896))*X+(-872235691607308484016))*X+(-859497218838814638456)))*u+(((((290068440457114627088)*A+(-49989281546242049092))*A+(-1935454428223422639650))*A+((((-237857374226536516760)*X+(441822274933648928081))*X+(223201175871867938890))*X+(-3473660510445748500408)))*A+((((1232071948105888227846)*X+(-2489293952050222984816))*X+(25150055838446529124))*X+(1257222003944334756970))))*u+((((((-22759618864762391040)*A+(-6419235504686313408))*A+(278687197521649878128))*A+(370756166923211748480))*A+(((((27633638598244087552)*X+(-113805142018359774672))*X+(4639127650592195904))*X+(80431775587594042576))*X+(15684116333549822832)))*A+((((((-4540191544069411648)*X+(53754578761152653120))*X+(-175322741892288896848))*X+(5034150209055823136))*X+(207048555012411069440))*X+(76400008793136002416))))
theorem row5_2_identity (u A X : ℂ) :
  (((885565804353310080)*u+((-11475225841953439896)*A+((-7340916360059156864)*X+(7380001850317039240)))))*row4_30 u A X+
  (((73797150362775840)*u+((12299525060462640)*A+((-12299525060462640)*X+(127187259550391920)))))*row4_37 u A X+
  (((-16875884835728944256757240)*u+((11746037222238707214309120)*A+((-7536916826064549955268160)*X+(-3098147066588114560205120)))))*row4_48 u A X+
  (((2279446380405420145920)*u+((3633753598229282647680)*A)))*row4_33 u A X+
  (((-1720455991118306343982080)*u+((-2422472242064706033364800)*A+((-896222036899401536586240)*X))))*row4_38 u A X+
  (((-14035669988880254600160)*u+((646808600953082450017435)*A+((8254654050978654359040)*X))))*row4_44 u A X+
  (((-8648849717702778128022720)*u+((-57727548331088987923025300)*A+((15138035961468492663137580)*X))))*row4_45 u A X+
  (((-228286916404177840)*A))*row4_14 u A X+
  (((-370322365801249796014080)*A))*row4_23 u A X+
  (((-4465547565285302496)*A))*row4_24 u A X+
  (((8142020456660898586170)*A))*row4_25 u A X+
  (((-1611320419405109370045)*A+((-18596881891419511680)*X)))*row4_34 u A X+
  (((9951800717410567619795400)*A))*row4_39 u A X+
  (((-2673123517674844601083200)*A))*row4_40 u A X+
  (((2892117372567770638283520)*A))*row4_46 u A X+
  (((27622716884905518640)*X))*row4_10 u A X+
  (((58569166954584)*X))*row4_21 u A X+
  (((-116314577952298551231)*X))*row4_22 u A X+
  (((5680236791766952748520)*X))*row4_27 u A X+
  (((3222640838810218740090)*X))*row4_31 u A X+
  (((-6000593890298029102080)*X))*row4_35 u A X+
  (((-37193763782839023360)*X))*row4_36 u A X+
  (((-235949122294555390302005)*X))*row4_41 u A X+
  (((2902790627660465938207680)*X))*row4_43 u A X+
  (((1457540928915289830842560)*X))*row4_47 u A X=((26620))*row5_2 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_14, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_10, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_2] <;> ring
theorem row5_2_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_2 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_14 := row4_14_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_10 := row4_10_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_2_identity u A X).symm
  have hz : ((26620))*row5_2 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_14, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_10, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((26620):ℂ)=(26620)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((26620):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_2_zero
def row5_6 (u A X : ℂ) : ℂ := (((((((2614922860629673440)*X)*A^2+(-101750010157420732800))*A+(((868373083760800464)*X+(-60299451302433878304))*X+(-125900095546779833664)))*A+((((-13260039028325369280)*X+(-25532942043056551488))*X+(52053020099707290048))*X+(38792981071381920768)))*u+(((((-38941303808281439664)*A+(-56079553727314317924))*A+(151929172347966237310))*A+((((26745372523268292520)*X+(-49639991228045965903))*X+(-54857238057693596790))*X+(430054660064935615464)))*A+((((-141065777842868589338)*X+(317643990790007968848))*X+(-35512435104270790172))*X+(-176578212947139379510))))*u+((((((759803150621560320)*A+(5245873690991486784))*A+(-22882670109309795984))*A+(-44045598434381968000))*A+(((((-119672584871350016)*X+(8818580736998089776))*X+(-7072182663990972352))*X+(433618855221390032))*X+(10451945408376284784)))*A+((((((779076337242270144)*X+(-1027069776417882560))*X+(7687411448292994224))*X+(6288502076078794272))*X+(-22477497329622485760))*X+(-14259002983262833808))))
theorem row5_6_identity (u A X : ℂ) :
  (((-13993923820947840)*u+((3313853352072711448)*A+((-30466059729605808)*X+(-591588492395528320)))))*row4_30 u A X+
  (((-1166160318412320)*u+((-194360053068720)*A+((194360053068720)*X+(744320655041040)))))*row4_37 u A X+
  (((-496896374132153110617480)*u+((-116052847783226002978560)*A+((125046574320496930812480)*X+(60686465088242173322560)))))*row4_48 u A X+
  (((-36020359915119740160)*u+((15080699566154874960)*A)))*row4_33 u A X+
  (((27187059345165760803840)*u+((212939618733507238372800)*A+((119994116054180877875520)*X))))*row4_38 u A X+
  (((-4808211195359793402720)*u+((-8859527427527421775755)*A+((-130442028576328465920)*X))))*row4_44 u A X+
  (((637005325474134290741760)*u+((464999441267488242534100)*A+((-251186185172634400936940)*X))))*row4_45 u A X+
  (((5851923087748683939840)*A))*row4_23 u A X+
  (((3266582486259306368)*A))*row4_24 u A X+
  (((-123533839982531752410)*A))*row4_25 u A X+
  (((31608788508784451085)*A+((293872400239904640)*X)))*row4_34 u A X+
  (((-199469977942922136918600)*A))*row4_39 u A X+
  (((40539322764165141576000)*A))*row4_40 u A X+
  (((-38855352672959044104960)*A))*row4_46 u A X+
  (((-925524062232)*X))*row4_21 u A X+
  (((1764769142607596463)*X))*row4_22 u A X+
  (((-1640357409275992166760)*X))*row4_27 u A X+
  (((-63217577017568902170)*X))*row4_31 u A X+
  (((94822827810742563840)*X))*row4_35 u A X+
  (((587744800479809280)*X))*row4_36 u A X+
  (((5306111866156724519365)*X))*row4_41 u A X+
  (((-43608289668771761250240)*X))*row4_43 u A X+
  (((-9061790671934569356480)*X))*row4_47 u A X=((26620))*row5_6 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_6] <;> ring
theorem row5_6_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_6 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_6_identity u A X).symm
  have hz : ((26620))*row5_6 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((26620):ℂ)=(26620)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((26620):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_6_zero
def row5_9 (u A X : ℂ) : ℂ := (((((((242067144812575484160)*X^2+(-1608737899900241238480))*A+(((-229459481020253844360)*X+(-993483906834945216240))*X+(-938010186148730001120)))*A+((((-176507293092502957200)*X+(-453875896523579032800))*X+(806890482708584947200))*X+(630383189616081990000)))*u+(((-4932880761863864536650)*A+(((-506512035943948581921)*X+(-2292723360370496945034))*X+(-5760960138012419690724)))*A+((((-3201455474074038199590)*X+(2185663190723276555412))*X+(4217247757424799843768))*X+(1015792283350761644178))))*u+(((((-3037481841492508623048)*A+(-6023170562237079663216))*A+(6923218164571695982206))*A+((((1773452781064656274077)*X+(-3601794130391058755415))*X+(-4495566753355378034850))*X+(25972966550354479518372)))*A+((((-10284578591893347080646)*X+(23448950211940604379564))*X+(-2879793028153910218272))*X+(-13164371620047257298918))))*u+((((((72508602429240158016)*A+(687360412990473518208))*A+(-965459323070621478912))*A+(-2497210400555522207408))*A+(((((63191509338209759408)*X+(626003907630892305984))*X+(-1187963969918311655696))*X+(343150039778227223920))*X+(1277178858432856519488)))*A+((((((-113248104041935163136)*X+(358216321602109101296))*X+(325112772689922629760))*X+(369370949345900376768))*X+(-1528004939322397124496))*X+(-1071172053114235719712))))
theorem row5_9_identity (u A X : ℂ) :
  (((16870639447153578240)*u+((-60634447184425713368)*A+((85467998936048814888)*X+(-69255390746225569380)))))*row4_30 u A X+
  (((5491703590329996270)*u+((234314436766021920)*A+((-234314436766021920)*X+(5019245841580328160)))))*row4_37 u A X+
  (((-946972360355740423531164360)*u+((292116307263326004127426560)*A+((-145756399891157446417498560)*X+(-49497416373967757394527680)))))*row4_48 u A X+
  (((-542377464509459361277440)*u+((-42306659473344163369560)*A)))*row4_33 u A X+
  (((-7000563842940202565437440)*u+((-62764536702274646082069600)*A+((-11217843794914458554702520)*X))))*row4_38 u A X+
  (((-578876746809383011644930)*u+((13476051292260043129049925)*A+((564857954734051234761120)*X))))*row4_44 u A X+
  (((-334475581533047448746159160)*u+((-1391419615326060572725126060)*A+((347128133355931941299481140)*X))))*row4_45 u A X+
  (((-7054896521452894734090240)*A+((25775309579643037553356800)*X)))*row4_23 u A X+
  (((-85071761508517025088)*A))*row4_24 u A X+
  (((171595889290206066136710)*A))*row4_25 u A X+
  (((-21337772875284453536355)*A+((-1383909304763159060040)*X)))*row4_34 u A X+
  (((196241901553845564208570680)*A))*row4_39 u A X+
  (((-56395910987458234392150720)*A))*row4_40 u A X+
  (((61885520813458500046183680)*A))*row4_46 u A X+
  (((1115783032219152)*X))*row4_21 u A X+
  (((-2451369847002943801953)*X))*row4_22 u A X+
  (((30014051356290728117160)*X))*row4_27 u A X+
  (((42675545750568907072710)*X))*row4_31 u A X+
  (((-114315452893912646154240)*X))*row4_35 u A X+
  (((-2767818609526318120080)*X))*row4_36 u A X+
  (((-3757878326101716413694715)*X))*row4_41 u A X+
  (((60551699273558836283519040)*X))*row4_43 u A X+
  (((28344380958413405363522880)*X))*row4_47 u A X=((106480))*row5_9 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_9] <;> ring
theorem row5_9_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_9 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_9_identity u A X).symm
  have hz : ((106480))*row5_9 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((106480):ℂ)=(106480)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((106480):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_9_zero
def row5_13 (u A X : ℂ) : ℂ := ((((((-43032478055952220965360)*A+((((4236175034220070972800)*X+(-218286569367498407169240))*X+(-41267405125027191393360))*X+(392481616920489575629920)))*A+((((127967787492064643970000)*X+(-329362608910610518135200))*X+(73427033926481230195200))*X+(201394821418545874165200)))*u+(((1186993779486757736162130)*A+(((-640040759642465666941995)*X+(1423696009232873303713170))*X+(3271301487663549231012660)))*A+((((969112001379545512854750)*X+(-1536699132568005964159140))*X+(-401524870191085061550360))*X+(567587131188460451304390))))*u+(((((692997210286027889412456)*A+(599348209045953301870128))*A+(-3895166231166052949336214))*A+((((-466031779757146637268993)*X+(445557949213872265876803))*X+(879015256309588183800330))*X+(-7534911209401700118288372)))*A+((((3165544778260353742331262)*X+(-7844310480876749033476764))*X+(1513220924356041548814240))*X+(4678765702616395291145502))))*u+((((((-34149072807932851036224)*A+(-150669171458456289023616))*A+(529103351185507175764992))*A+(821526324410033803522672))*A+(((((-28329109116767545212016)*X+(-356217696730429915643712))*X+(503330962054696860133456))*X+(-79126262535320874128432))*X+(-330819878736816179443776)))*A+((((((-7179212612965725615360)*X+(-1592671846361640881584))*X+(-387528652765329305683584))*X+(176465156468936166282816))*X+(639266227665635995805904))*X+(235786477828013598010016))))
theorem row5_13_identity (u A X : ℂ) :
  (((458100908778478775040)*u+((-555441450404765534456)*A+((66461749468900718856)*X+(775506497129878081260)))))*row4_30 u A X+
  (((37090477045028726550)*u+((1132666900663969440)*A+((-1132666900663969440)*X+(-3420075113585776800)))))*row4_37 u A X+
  (((3804371507550861343022098392)*u+((-123883708632471560148203520)*A+((-132905967571644221577475776)*X+(-127103794982021649965804224)))))*row4_48 u A X+
  (((209914891366252128376320)*u+((-32898565987105855833720)*A)))*row4_33 u A X+
  (((-158437301083512760279111680)*u+((238279785912948233113339680)*A+((60996853226629679878106280)*X))))*row4_38 u A X+
  (((-3472449643493889323382810)*u+((11235456741124746496663809)*A+((4161911706060772365868320)*X))))*row4_44 u A X+
  (((1376310639845722909981763880)*u+((544757996619766005679925828)*A+((462664271458772062956228260)*X))))*row4_45 u A X+
  (((-34103096197348038086983680)*A))*row4_23 u A X+
  (((-411233596067731838016)*A))*row4_24 u A X+
  (((152970309272337217372110)*A))*row4_25 u A X+
  (((-62337835808449649240199)*A+((-9346800215347239090600)*X)))*row4_34 u A X+
  (((359012094574138079721941976)*A))*row4_39 u A X+
  (((-48089131370421771778720704)*A))*row4_40 u A X+
  (((68127704246298462134417664)*A))*row4_46 u A X+
  (((5393651907923664)*X))*row4_21 u A X+
  (((-2185290132461960248173)*X))*row4_22 u A X+
  (((274943517950358939555720)*X))*row4_27 u A X+
  (((124675671616899298480398)*X))*row4_31 u A X+
  (((-552596466160732098631680)*X))*row4_35 u A X+
  (((-18693600430694478181200)*X))*row4_36 u A X+
  (((-10951439491572576173105215)*X))*row4_41 u A X+
  (((54570383189605998462538560)*X))*row4_43 u A X+
  (((-181646966483057463030720)*X))*row4_47 u A X=((1936))*row5_13 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_13] <;> ring
theorem row5_13_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_13 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_13_identity u A X).symm
  have hz : ((1936))*row5_13 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((1936):ℂ)=(1936)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1936):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_13_zero
def row5_17 (u A X : ℂ) : ℂ := ((((((1366670755087665754320)*A+(((471526625832829328520)*X+(1235551051647520700400))*X+(938010186148730001120)))*A+(((((242067144812575484160)*X+(-65559851720072526960))*X+(-30258393101571935520))*X+(-564823337896009463040))*X+(-388316044803506505840)))*u+(((4932880761863864536650)*A+(((506512035943948581921)*X+(2292723360370496945034))*X+(5760960138012419690724)))*A+((((3201455474074038199590)*X+(-2185663190723276555412))*X+(-4217247757424799843768))*X+(-1015792283350761644178))))*u+(((((3037481841492508623048)*A+(6023170562237079663216))*A+(-6923218164571695982206))*A+((((-1773452781064656274077)*X+(3601794130391058755415))*X+(4495566753355378034850))*X+(-25972966550354479518372)))*A+((((10284578591893347080646)*X+(-23448950211940604379564))*X+(2879793028153910218272))*X+(13164371620047257298918))))*u+((((((-72508602429240158016)*A+(-687360412990473518208))*A+(965459323070621478912))*A+(2497210400555522207408))*A+(((((-63191509338209759408)*X+(-626003907630892305984))*X+(1187963969918311655696))*X+(-343150039778227223920))*X+(-1277178858432856519488)))*A+((((((113248104041935163136)*X+(-358216321602109101296))*X+(-325112772689922629760))*X+(-369370949345900376768))*X+(1528004939322397124496))*X+(1071172053114235719712))))
theorem row5_17_identity (u A X : ℂ) :
  (((-16870639447153578240)*u+((60634447184425713368)*A+((-85467998936048814888)*X+(69255390746225569380)))))*row4_30 u A X+
  (((-5491703590329996270)*u+((-234314436766021920)*A+((234314436766021920)*X+(-5019245841580328160)))))*row4_37 u A X+
  (((946972360355740423531164360)*u+((-292116307263326004127426560)*A+((145756399891157446417498560)*X+(49497416373967757394527680)))))*row4_48 u A X+
  (((542377464509459361277440)*u+((42306659473344163369560)*A)))*row4_33 u A X+
  (((32775873422583240118794240)*u+((62764536702274646082069600)*A+((11217843794914458554702520)*X))))*row4_38 u A X+
  (((578876746809383011644930)*u+((-13476051292260043129049925)*A+((-564857954734051234761120)*X))))*row4_44 u A X+
  (((334475581533047448746159160)*u+((1391419615326060572725126060)*A+((-347128133355931941299481140)*X))))*row4_45 u A X+
  (((7054896521452894734090240)*A))*row4_23 u A X+
  (((85071761508517025088)*A))*row4_24 u A X+
  (((-171595889290206066136710)*A))*row4_25 u A X+
  (((21337772875284453536355)*A+((1383909304763159060040)*X)))*row4_34 u A X+
  (((-196241901553845564208570680)*A))*row4_39 u A X+
  (((56395910987458234392150720)*A))*row4_40 u A X+
  (((-61885520813458500046183680)*A))*row4_46 u A X+
  (((-1115783032219152)*X))*row4_21 u A X+
  (((2451369847002943801953)*X))*row4_22 u A X+
  (((-30014051356290728117160)*X))*row4_27 u A X+
  (((-42675545750568907072710)*X))*row4_31 u A X+
  (((114315452893912646154240)*X))*row4_35 u A X+
  (((2767818609526318120080)*X))*row4_36 u A X+
  (((3757878326101716413694715)*X))*row4_41 u A X+
  (((-60551699273558836283519040)*X))*row4_43 u A X+
  (((-28344380958413405363522880)*X))*row4_47 u A X=((106480))*row5_17 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_17] <;> ring
theorem row5_17_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_17 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_17_identity u A X).symm
  have hz : ((106480))*row5_17 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((106480):ℂ)=(106480)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((106480):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_17_zero

def row5_25 (u A X : ℂ) : ℂ := (((((-170649439720191820230480)*A+(((-121564224056027933173224)*X+(-129704556686172213967056))*X+(-32449212628921474363296)))*A+((((25802014739746888138320)*X+(-185425034171137664520672))*X+(133821004691643888244032))*X+(159623019431390776382352)))*u+(((((9549115712516663663600)*A+(-12471003095611877852308))*A+(-495606307206291378723034))*A+((((-13191838696855455385408)*X+(-274975276983542872309619))*X+(390294477053758647114370))*X+(-242099701642372358605176)))*A+((((15278461019110327392430)*X+(-500532345459828068140432))*X+(469975423421607413355572))*X+(485253884440717740748002))))*u+((((((4842232105373359526016)*A+(-22392809637337629019200))*A+(-10106958415281141367504))*A+(72335801194390416721792))*A+((((((1317921121757355413760)*X^2+(-16476506242646796086400))*X+(-33166340722807753661328))*X+(-25312459362831260345792))*X+(-65250394402905995267824))*X+(-49101889741505159695440)))*A+((((((-45984971009394045095104)*X+(778324634926377622336))*X+(75466882210555011792752))*X+(31514806315758396897824))*X+(45141310405322672125184))*X+(29416575232015971350064))))
theorem row5_25_identity (u A X : ℂ) :
  (((-706178261606114626560)*u+((4213990744888551957792)*A+((-1441254819229277988672)*X+(2630876574575810709720)))))*row4_30 u A X+
  (((-58848188467176218880)*u+((26147157922461973320)*A+((45763220744854046280)*X+(286678392104690369960)))))*row4_37 u A X+
  (((-7084764138220189893683731080)*u+((3188311486339236477714236160)*A+((-2279458131196470799387032000)*X+(-409249888176257879446491840)))))*row4_48 u A X+
  (((-1817702845374139048765440)*u+((713421135518492604392640)*A)))*row4_33 u A X+
  (((1371946178370080949729730560)*u+((15188927608774861371619200)*A+((419406504268183228306414080)*X))))*row4_38 u A X+
  (((8899340381131245045271920)*u+((141015337556637664189490085)*A+((-6582522969184463139041280)*X))))*row4_44 u A X+
  (((283591552514703668685743040)*u+((-11597385393103959464732111340)*A+((6860200214746025794082230740)*X))))*row4_45 u A X+
  (((295306800725398590076354560)*A))*row4_23 u A X+
  (((3560969271024907644672)*A))*row4_24 u A X+
  (((2111896595131424353915110)*A))*row4_25 u A X+
  (((-221752385363556840393315)*A+((14829743493728407157760)*X)))*row4_34 u A X+
  (((3884513568252029932324632120)*A))*row4_39 u A X+
  (((-724110987172613469079654080)*A))*row4_40 u A X+
  (((457187833002610955462595840)*A))*row4_46 u A X+
  (((-46704911481885888)*X))*row4_21 u A X+
  (((-30169951359020347913073)*X))*row4_22 u A X+
  (((-2085925418719833219107040)*X))*row4_27 u A X+
  (((443504770727113680786630)*X))*row4_31 u A X+
  (((-12756466229947367847575040)*X))*row4_35 u A X+
  (((29659486987456814315520)*X))*row4_36 u A X+
  (((-75887831737520011638894915)*X))*row4_41 u A X+
  (((760120109138529997936626240)*X))*row4_43 u A X+
  (((352942656129772717467919680)*X))*row4_47 u A X=((26620))*row5_25 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_25] <;> ring
theorem row5_25_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_25 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_25_identity u A X).symm
  have hz : ((26620))*row5_25 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((26620):ℂ)=(26620)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((26620):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_25_zero
def row5_26 (u A X : ℂ) : ℂ := (((((41000297090052961821600)*A+(((-123149388606344870072688)*X+(36264281169493366802208))*X+(345422069279736284645568)))*A+((((67385834778409415468640)*X+(-131201776011317395944384))*X+(-3569893545501434992896))*X+(63815941232907980475744)))*u+(((((10481478525561249640808)*A+(-112047110377328335902112))*A+(-410034521167394221213300))*A+((((-23937968101821395793985)*X+(-52613568532588729937324))*X+(45046888046581033095220))*X+(-97818572861771265853488)))*A+((((110923206169380014690776)*X+(-453068468996949162175756))*X+(231222056658189132794204))*X+(342145262827569147484980))))*u+((((((-6303054667044887880480)*A+(-20123276810094750756288))*A+(23212446780361435197008))*A+(28958083168383332820400))*A+(((((-2895045110805047857008)*X+(-44398030394958677832432))*X+(33596609435092940427664))*X+(-17169603675930987602944))*X+(-18191103579043066325328)))*A+(((((((329480280439338853440)*X^2+(-19023005689253141971648))*X+(23267529140040120593680))*X+(-44168343860194253904208))*X+(43870786596519295542176))*X+(65495098504303155248720))*X+(8195673807839432262096))))
theorem row5_26_identity (u A X : ℂ) :
  (((1494120263672458920960)*u+((-8219996112483317249472)*A+((3660224800284419021952)*X+(1792007088663438614880)))))*row4_30 u A X+
  (((124510021972704910080)*u+((2774075661955146780)*A+((-2774075661955146780)*X+(160869760372950817540)))))*row4_37 u A X+
  (((6642446132873380964652805320)*u+((1937551370138387212057453440)*A+((-877836229486733963656077120)*X+(-466620649186508967413461440)))))*row4_48 u A X+
  (((3845865558692909262551040)*u+((-1811811276140787415866240)*A)))*row4_33 u A X+
  (((-2902740989376525052626984960)*u+((917481672525673210389350400)*A+((-80450620132627037689735680)*X))))*row4_38 u A X+
  (((-52398584635382771909555520)*u+((133154426816037251165624895)*A+((13927193017778880421908480)*X))))*row4_44 u A X+
  (((4868648739374428054936200960)*u+((-9376277022335243516613219300)*A+((2709466097123194202619903660)*X))))*row4_45 u A X+
  (((-624805235381494181731368960)*A))*row4_23 u A X+
  (((-7534239774037232669952)*A))*row4_24 u A X+
  (((1645047191406696437860290)*A))*row4_25 u A X+
  (((-435346895012714156392965)*A+((-31376525537121637340160)*X)))*row4_34 u A X+
  (((2013225053415311501121292200)*A))*row4_39 u A X+
  (((-496875822230887909212110400)*A))*row4_40 u A X+
  (((979300978882479085074359040)*A))*row4_46 u A X+
  (((98817477756115008)*X))*row4_21 u A X+
  (((-23500674162952806255147)*X))*row4_22 u A X+
  (((4068898075679242038488640)*X))*row4_27 u A X+
  (((870693790025428312785930)*X))*row4_31 u A X+
  (((-1353393841349381369852160)*X))*row4_35 u A X+
  (((-62753051074243274680320)*X))*row4_36 u A X+
  (((-57770029154230869852258285)*X))*row4_41 u A X+
  (((580831842257966074936628160)*X))*row4_43 u A X+
  (((-14698913198417202471266880)*X))*row4_47 u A X=((53240))*row5_26 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_26] <;> ring
theorem row5_26_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_26 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_26_identity u A X).symm
  have hz : ((53240))*row5_26 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((53240):ℂ)=(53240)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((53240):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_26_zero
def row5_27 (u A X : ℂ) : ℂ := (((((((1694470013688028389120)*A+(9566695285613660280240))*A+(((1606216367141776910520)*X+(1870977306780531346320))*X+(8260541316729138396960)))*A+((((-458918962040507688720)*X+(4871601289353081618720))*X+(-3953763365272066241280))*X+(-4412682327312573930000)))*u+(((12928638399046047347670)*A+(((1689348680547917349807)*X+(5499587191085830046358))*X+(15149539253422819972188)))*A+((((6706372047668189854650)*X+(-2225047580683142089644))*X+(-11187696514653237619656))*X+(-4481324466985047765006))))*u+(((((6551748191741588679096)*A+(12297374345767851683472))*A+(-15956601095834214911202))*A+((((-3921531975651710970099)*X+(8096358166659383698905))*X+(9370206441679137385470))*X+(-57039309614009262079644)))*A+((((22635765902606842994202)*X+(-50659445495450448122388))*X+(5387913690236762133984))*X+(28023679592843605128186))))*u+((((((-176852211941443845312)*A+(-1399585045345088359296))*A+(2284109767163127097344))*A+(5512273895383289266256))*A+(((((-90727270186370489936)*X+(-1396305251575323069888))*X+(2416770950429563818992))*X+(-599162677248722150800))*X+(-2550114576121485318336)))*A+((((((233090579559234093312)*X+(-671997232881627598352))*X+(-865260039365551443840))*X+(-706087382275645782336))*X+(3287146261855460998512))*X+(2216070148726750142944))))
theorem row5_27_identity (u A X : ℂ) :
  (((-2776667513183182080)*u+((8860543761756881656)*A+((-14028274827294469896)*X+(16484087000784586260)))))*row4_30 u A X+
  (((-1048552353378704790)*u+((-38564826571988640)*A+((38564826571988640)*X+(-875209328006317920)))))*row4_37 u A X+
  (((162753101421993970719111720)*u+((-45625384326670163457361920)*A+((21215123890068688221808320)*X+(6928234026549233503328960)))))*row4_48 u A X+
  (((-7147142178933510673920)*u+((6943996039510762598520)*A)))*row4_33 u A X+
  (((5394443004591969748654080)*u+((10190359379832341754290400)*A+((2302493423516087336682840)*X))))*row4_38 u A X+
  (((85594815806817630554010)*u+((-2034819284463986646569025)*A+((-107402463626348237387040)*X))))*row4_44 u A X+
  (((56786424972491800319330520)*u+((218210445036181133086329020)*A+((-51643357614173982550889380)*X))))*row4_45 u A X+
  (((1161135713992890349486080)*A))*row4_23 u A X+
  (((14001603034070008896)*A))*row4_24 u A X+
  (((-25797330727320977909070)*A))*row4_25 u A X+
  (((2848288937322263275335)*A+((264235193051433607080)*X)))*row4_34 u A X+
  (((-28134533892679099913996760)*A))*row4_39 u A X+
  (((8470533443288000883733440)*A))*row4_40 u A X+
  (((-9568871729959697068488960)*A))*row4_46 u A X+
  (((-183642031295184)*X))*row4_21 u A X+
  (((368533296104585398701)*X))*row4_22 u A X+
  (((-4385969162069656419720)*X))*row4_27 u A X+
  (((-5696577874644526550670)*X))*row4_31 u A X+
  (((18814699069329241774080)*X))*row4_35 u A X+
  (((528470386102867214160)*X))*row4_36 u A X+
  (((505646312240976331366655)*X))*row4_41 u A X+
  (((-9105339436874156346319680)*X))*row4_43 u A X+
  (((-4260061275554226294250560)*X))*row4_47 u A X=((9680))*row5_27 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_27] <;> ring
theorem row5_27_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_27 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_27_identity u A X).symm
  have hz : ((9680))*row5_27 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((9680):ℂ)=(9680)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((9680):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_27_zero
def row5_28 (u A X : ℂ) : ℂ := ((((((2614922860629673440)*A^2+(-57802926713471311680))*A+(((1649133673767163584)*X+(-20527498615485353184))*X+(-93010970301245910144)))*A+((((-4140639073290867840)*X+(-20749712285514709728))*X+(29030990432096445408))*X+(24890351358805577568)))*u+(((((-12991815897092320464)*A+(-10690608659049411564))*A+(58192792936706887370))*A+((((8408459957521816280)*X+(-15078404209007899013))*X+(-13353497116158406290))*X+(124382512643183568024)))*A+((((-55266023798074783678)*X+(119715673340718376368))*X+(-9183625744568809012))*X+(-64449649542643592690))))*u+((((((757320855309596160)*A+(2239933104003021504))*A+(-8143101216644173104))*A+(-12958233501525420160))*A+(((((-112756406907812096)*X+(5108468244028106256))*X+(-6093003437957372992))*X+(133881091930268912))*X+(3759689160616323024)))*A+((((((-230578640295976896)*X+(-3090471041261120))*X+(5973262031813433744))*X+(-2118353018490507168))*X+(-8666006430532692480))*X+(-3156992150352473648))))
theorem row5_28_identity (u A X : ℂ) :
  (((-1250784357863040)*u+((10595468007144328)*A+((-2659895702820048)*X+(-17588345953883320)))))*row4_30 u A X+
  (((-104232029821920)*u+((-17372004970320)*A+((17372004970320)*X+(72271133328240)))))*row4_37 u A X+
  (((-41573880549717190460280)*u+((-10818191093856241455360)*A+((11607585707448075871680)*X+(5581732007461041248960)))))*row4_48 u A X+
  (((-3219518937139464960)*u+((1316648372895923760)*A)))*row4_33 u A X+
  (((2429993831631725399040)*u+((-861343833771378619200)*A+((-1745560994181930636480)*X))))*row4_38 u A X+
  (((78256619781869224080)*u+((-870999030970638701205)*A+((-11658977927760683520)*X))))*row4_44 u A X+
  (((-12924511792699248181440)*u+((49997555806187360739500)*A+((-25941148635916532635540)*X))))*row4_45 u A X+
  (((523047999633734615040)*A))*row4_23 u A X+
  (((6307195937890848)*A))*row4_24 u A X+
  (((-11440961670596020710)*A))*row4_25 u A X+
  (((2903754063247322835)*A+((26266471515123840)*X)))*row4_34 u A X+
  (((-18579206323850969379000)*A))*row4_39 u A X+
  (((3755995107618588753600)*A))*row4_40 u A X+
  (((-3576988703551468719360)*A))*row4_46 u A X+
  (((-82723833192)*X))*row4_21 u A X+
  (((163442309579943153)*X))*row4_22 u A X+
  (((-5244756663536442360)*X))*row4_27 u A X+
  (((-5807508126494645670)*X))*row4_31 u A X+
  (((8475314808879959040)*X))*row4_35 u A X+
  (((52532943030247680)*X))*row4_36 u A X+
  (((491921039197176562715)*X))*row4_41 u A X+
  (((-4038335479422485989440)*X))*row4_43 u A X+
  (((-1667188328496158825280)*X))*row4_47 u A X=((2420))*row5_28 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_28] <;> ring
theorem row5_28_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_28 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_28_identity u A X).symm
  have hz : ((2420))*row5_28 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((2420):ℂ)=(2420)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((2420):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_28_zero
def row5_29 (u A X : ℂ) : ℂ := (((((((67760)*A+(114488))*A+(-792216))*A+(-2450342))*A+((((196856)*X+(-610471))*X+(126410))*X+(-1348036)))*A+((((371666)*X+(-1330312))*X+(586980))*X+(958646)))*u+((((((-23232)*A+(19712))*A+(231856))*A+(168576))*A+(((((23232)*X+(-90896))*X+(-9152))*X+(127504))*X+(-1488)))*A+((((((24640)*X+(-9152))*X+(-132432))*X+(-79712))*X+(248832))*X+(156528))))
theorem row5_29_identity (u A X : ℂ) :
  (((463984664)*u+((-321404160)*A+((228122048)*X+(75759552)))))*row4_48 u A X+
  (((-228270)*A))*row4_25 u A X+
  (((30547)*A))*row4_34 u A X+
  (((-373345368)*A))*row4_39 u A X+
  (((75759552)*A))*row4_40 u A X+
  (((-16086517)*A))*row4_44 u A X+
  (((1315604796)*A+((-629171620)*X)))*row4_45 u A X+
  (((-64280832)*A))*row4_46 u A X+
  (((3261)*X))*row4_22 u A X+
  (((-61094)*X))*row4_31 u A X+
  (((8261575)*X))*row4_41 u A X+
  (((-80351040)*X))*row4_43 u A X+
  (((-17075520)*X))*row4_47 u A X=((484))*row5_29 u A X := by
  simp only [row4_48, row4_25, row4_34, row4_39, row4_40, row4_44, row4_45, row4_46, row4_22, row4_31, row4_41, row4_43, row4_47, row5_29] <;> ring
theorem row5_29_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_29 u A X=0 := by
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_29_identity u A X).symm
  have hz : ((484))*row5_29 u A X=0 := by
    simpa only [z4_48, z4_25, z4_34, z4_39, z4_40, z4_44, z4_45, z4_46, z4_22, z4_31, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((484):ℂ)=(484)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((484):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_29_zero
def row5_30 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))*u^3)
theorem row5_30_identity (u A X : ℂ) :
  (((1)*u))*row4_38 u A X=((1))*row5_30 u A X := by
  simp only [row4_38, row5_30] <;> ring
theorem row5_30_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_30 u A X=0 := by
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_30_identity u A X).symm
  have hz : ((1))*row5_30 u A X=0 := by
    simpa only [z4_38,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_30_zero

def row5_31 (u A X : ℂ) : ℂ := (((((((93390102165345480)*X)*A+(443682543849425100))*A+(((37929405306169278)*X+(36964812045532932))*X+(65791354936143672)))*A+((((-367104749094964980)*X+(890534657754151344))*X+(-156325159564221384))*X+(-523429908659186364)))*u+(((((-232378722294834896)*A+(-646393681447807532))*A+(524469038353014202))*A+((((118892130097654144)*X+(-168370985042478925))*X+(-546128529081239650))*X+(2268470122642422264)))*A+((((-619904487059794702)*X+(1806765648896757328))*X+(-566956674777167924))*X+(-1186861161836962626))))*u+((((((-8142322638371328)*A+(67688601737144256))*A+(-44247013992671024))*A+(-219725927464507136))*A+(((((22686161526430336)*X+(18482298285984528))*X+(-97353666831092672))*X+(65440190991020400))*X+(164228286909118416)))*A+((((((-2611635525025472)*X+(49597704537724992))*X+(-52875898280021360))*X+(109878185809273696))*X+(-139861325237278592))*X+(-148362790029625904))))
theorem row5_31_identity (u A X : ℂ) :
  (((70164349960320)*u+((-383592000662024)*A+((359984597774384)*X+(40198476704760)))))*row4_30 u A X+
  (((5847029163360)*u+((974504860560)*A+((-974504860560)*X+(15107162136880)))))*row4_37 u A X+
  (((-3128700292043113707480)*u+((1502952773298992590080)*A+((-932003619397977910080)*X+(-348936566107571506240)))))*row4_48 u A X+
  (((180603036797863680)*u+((-178192375898320080)*A)))*row4_33 u A X+
  (((-136313615158510648320)*u+((-51448062552137143200)*A+((6919974860205068640)*X))))*row4_38 u A X+
  (((-3544331310548697240)*u+((77554772252101194775)*A+((654025294096796160)*X))))*row4_44 u A X+
  (((-1413145127394429612480)*u+((-7054888831684132524580)*A+((2088308110139611325020)*X))))*row4_45 u A X+
  (((-29341047209006776320)*A))*row4_23 u A X+
  (((-353810231373984)*A))*row4_24 u A X+
  (((1000785806321782530)*A))*row4_25 u A X+
  (((-166675238813513265)*A+((-1473451349166720)*X)))*row4_34 u A X+
  (((1305184143560743323240)*A))*row4_39 u A X+
  (((-329841144183115920960)*A))*row4_40 u A X+
  (((329792252362681194240)*A))*row4_46 u A X+
  (((4640499336)*X))*row4_21 u A X+
  (((-14296940090311179)*X))*row4_22 u A X+
  (((189878040327701880)*X))*row4_27 u A X+
  (((333350477627026530)*X))*row4_31 u A X+
  (((-475433635331128320)*X))*row4_35 u A X+
  (((-2946902698333440)*X))*row4_36 u A X+
  (((-28881368328282678745)*X))*row4_41 u A X+
  (((352900224567714774720)*X))*row4_43 u A X+
  (((165447930497740411840)*X))*row4_47 u A X=((2420))*row5_31 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_31] <;> ring
theorem row5_31_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_31 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_31_identity u A X).symm
  have hz : ((2420))*row5_31 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((2420):ℂ)=(2420)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((2420):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_31_zero
def row5_32 (u A X : ℂ) : ℂ := (((((((968)*X+(-968))*A+(8948))*A+(33006))*A+((((110)*X+(1997))*X+(-6014))*X+(42560)))*A+((((-2186)*X+(14632))*X+(-10260))*X+(-12446)))*u+((((-2736)*A+(-4704))*A+(((((-352)*X+(208))*X+(2464))*X+(-1968))*X+(208)))*A+(((((-352)*X+(208))*X+(4640))*X+(-4000))*X+(-4144))))
theorem row5_32_identity (u A X : ℂ) :
  (((-6023864)*u+((7275136)*A+((-5617216)*X+(-2005696)))))*row4_48 u A X+
  (((5530)*A))*row4_25 u A X+
  (((-869)*A))*row4_34 u A X+
  (((9513064)*A))*row4_39 u A X+
  (((-1835328)*A))*row4_40 u A X+
  (((396027)*A))*row4_44 u A X+
  (((-30380724)*A+((14712412)*X)))*row4_45 u A X+
  (((1557248)*A))*row4_46 u A X+
  (((-79)*X))*row4_22 u A X+
  (((1738)*X))*row4_31 u A X+
  (((-207437)*X))*row4_41 u A X+
  (((1946560)*X))*row4_43 u A X+
  (((611776)*X))*row4_47 u A X=((484))*row5_32 u A X := by
  simp only [row4_48, row4_25, row4_34, row4_39, row4_40, row4_44, row4_45, row4_46, row4_22, row4_31, row4_41, row4_43, row4_47, row5_32] <;> ring
theorem row5_32_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_32 u A X=0 := by
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_32_identity u A X).symm
  have hz : ((484))*row5_32 u A X=0 := by
    simpa only [z4_48, z4_25, z4_34, z4_39, z4_40, z4_44, z4_45, z4_46, z4_22, z4_31, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((484):ℂ)=(484)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((484):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_32_zero
def row5_33 (u A X : ℂ) : ℂ := (((((-18311368541656769370)*A+(((24883415232142664043)*X+(-17895915310776147018))*X+(-91016565186944589588)))*A+((((-6365867757204523590)*X+(4263545415824267364))*X+(8468190098584779816))*X+(2102322341380256226)))*u+(((((22445644867272625504)*A+(68237395093722028948))*A+(-100214482606174369448))*A+((((-9870899825800357916)*X+(6524378955076842350))*X+(66741140300876482340))*X+(-349110870757396413036)))*A+((((60059899689590560208)*X+(-168852391926188048072))*X+(48732592547006927656))*X+(108792492236597487864))))*u+(((((((1743281907086448960)*X+(1621900446203940672))*A+(1951756715620336416))*A+(6872722180992066496))*A+(44786737921209531424))*A+(((((3649962714821437696)*X+(3885780536918651808))*X+(-23654203517462056352))*X+(-11205453943139580000))*X+(-8830152562759360704)))*A+((((((1811025118253806048)*X+(-16409429125262292768))*X+(17994301869624292000))*X+(-793723770540484064))*X+(4978281815809748128))*X+(10185204796679359456))))
theorem row5_33_identity (u A X : ℂ) :
  (((-137974469289592320)*u+((738657606963469424)*A+((-343068104623276384)*X+(115176301205795940)))))*row4_30 u A X+
  (((-11497872440799360)*u+((-1916312073466560)*A+((1916312073466560)*X+(3458249119207520)))))*row4_37 u A X+
  (((74620232570587359597480)*u+((-437147500696530218369280)*A+((202639940994929292761280)*X+(22390908065171678267840)))))*row4_48 u A X+
  (((-355146283951410631680)*u+((169818711788521810080)*A)))*row4_33 u A X+
  (((268053487548557009080320)*u+((-44637566232818053598400)*A+((-15700412941249327568640)*X))))*row4_38 u A X+
  (((5200773271339393832040)*u+((-24696258825055231824825)*A+((-1286106019738053212160)*X))))*row4_44 u A X+
  (((-289546476704532188269920)*u+((2002568189940179263399580)*A+((-682180145258797380314020)*X))))*row4_45 u A X+
  (((57697611669644558008320)*A))*row4_23 u A X+
  (((695749036806592384)*A))*row4_24 u A X+
  (((-319494463641252552030)*A))*row4_25 u A X+
  (((64799366759808874215)*A+((2897463855081438720)*X)))*row4_34 u A X+
  (((-431507046467870889340440)*A))*row4_39 u A X+
  (((118377233362461600500160)*A))*row4_40 u A X+
  (((-135760183379041693866240)*A))*row4_46 u A X+
  (((-9125295587936)*X))*row4_21 u A X+
  (((4564206623446465029)*X))*row4_22 u A X+
  (((-365635515446917364880)*X))*row4_27 u A X+
  (((-129598733519617748430)*X))*row4_31 u A X+
  (((934915003906277560320)*X))*row4_35 u A X+
  (((5794927710162877440)*X))*row4_36 u A X+
  (((10508887109944616637095)*X))*row4_41 u A X+
  (((-113688368284766794854720)*X))*row4_43 u A X+
  (((-2610692738857609496640)*X))*row4_47 u A X=((9680))*row5_33 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_33] <;> ring
theorem row5_33_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_33 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_33_identity u A X).symm
  have hz : ((9680))*row5_33 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((9680):ℂ)=(9680)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((9680):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_33_zero
def row5_34 (u A X : ℂ) : ℂ := ((((((18678020433069096)*X^2+(-114598441129058568))*A+(((21894253510317804)*X+(-69183997292850264))*X+(-141561967809086352)))*A+((((-35406427031818920)*X+(22782677010524640))*X+(48030177053113200))*X+(12623750021294280)))*u+(((((-53881712372432560)*A+(-79722247714897252))*A+(251035466218098334))*A+((((47680362507887824)*X+(-80028060129988495))*X+(-100763009012899094))*X+(713046828794569704)))*A+((((-191937663709591386)*X+(446030220649512368))*X+(-62154893230329596))*X+(-254092556939920982))))*u+((((((68952647554560)*A+(4258262952820800))*A+(-38644891895533840))*A+(-72737857776129280))*A+(((((-192116054542720)*X+(8811001499198640))*X+(-786060716795200))*X+(-3079721072942640))*X+(12408241335394800)))*A+((((((1632609369702080)*X+(-2030507365212480))*X+(6194307164963120))*X+(18615032676185120))*X+(-33075171758984320))*X+(-25646153219829520))))
theorem row5_34_identity (u A X : ℂ) :
  (((-118836305280)*u+((649684007896)*A+((-609700504336)*X+(-17642907201920)))))*row4_30 u A X+
  (((-9903025440)*u+((-1650504240)*A+((1650504240)*X+(-25586773520)))))*row4_37 u A X+
  (((5299032674643550920)*u+((-2545528529661976320)*A+((1578520526442256320)*X+(590988619103072960)))))*row4_48 u A X+
  (((-305884649790720)*u+((301801749646320)*A)))*row4_33 u A X+
  (((230872321826657280)*u+((469916469524779200)*A+((9028441632160139904)*X))))*row4_38 u A X+
  (((-199455244078098096)*u+((-131353352471499725)*A+((-1107712813616640)*X))))*row4_44 u A X+
  (((11050804899786921984)*u+((11948759211659551820)*A+((-3536936068467766580)*X))))*row4_45 u A X+
  (((49694490796769280)*A))*row4_23 u A X+
  (((599243072736)*A))*row4_24 u A X+
  (((-1695015882954870)*A))*row4_25 u A X+
  (((282295347615435)*A+((2495562410880)*X)))*row4_34 u A X+
  (((-2210570773028115960)*A))*row4_39 u A X+
  (((558646989906075840)*A))*row4_40 u A X+
  (((-558564182564424960)*A))*row4_46 u A X+
  (((-7859544)*X))*row4_21 u A X+
  (((24214512613641)*X))*row4_22 u A X+
  (((-321593583908520)*X))*row4_27 u A X+
  (((-564590695230870)*X))*row4_31 u A X+
  (((805234804577280)*X))*row4_35 u A X+
  (((4991124821760)*X))*row4_36 u A X+
  (((48915939583348355)*X))*row4_41 u A X+
  (((-597701807881442880)*X))*row4_43 u A X+
  (((-280216673961815360)*X))*row4_47 u A X=((484))*row5_34 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_34] <;> ring
theorem row5_34_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_34 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_34_identity u A X).symm
  have hz : ((484))*row5_34 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((484):ℂ)=(484)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((484):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_34_zero
def row5_37 (u A X : ℂ) : ℂ := (((((20249094724074810)*A+((((11673762770668185)*X+(-24801412343199921))*X+(-4872635036959734))*X+(73949276641735836)))*A+((((35332283362118490)*X+(-65761589043472608))*X+(-4902977680764372))*X+(30429305681354118)))*u+(((((39631248074296472)*A+(92456504460744524))*A+(-120205745067844404))*A+((((-22893157438179798)*X+(36766170655843320))*X+(86724655731755200))*X+(-422287390955445468)))*A+((((116524246284934724)*X+(-310790496534953296))*X+(77742003965083848))*X+(194266250250018572))))*u+((((((1004246059741056)*A+(-9297519725732832))*A+(13121837657135168))*A+(41753534424803072))*A+(((((-2798033108661472)*X+(-4041019723090656))*X+(12323613137542784))*X+(-7575078663120960))*X+(-22965868983092352)))*A+((((((5763314436704)*X+(-5800863406191744))*X+(5392748377599200))*X+(-17391297501838432))*X+(23979574393031744))*X+(23582985993312608))))
theorem row5_37_identity (u A X : ℂ) :
  (((-34615318066560)*u+((189243670299992)*A+((-177597046905872)*X+(49212182798020)))))*row4_30 u A X+
  (((-2884609838880)*u+((-480768306480)*A+((480768306480)*X+(-7453061601040)))))*row4_37 u A X+
  (((1543532517656885760840)*u+((-741476095997252816640)*A+((459800479059394376640)*X+(172146542050166537920)))))*row4_48 u A X+
  (((-89099828703325440)*u+((87910538218406640)*A)))*row4_33 u A X+
  (((67249809172079170560)*u+((136879954480146398400)*A+((-3413943561567417120)*X))))*row4_38 u A X+
  (((1748582516866390920)*u+((-38261355098483991325)*A+((-322660918137761280)*X))))*row4_44 u A X+
  (((585671585394290963040)*u+((3480502861796260880140)*A+((-1030258949086539436660)*X))))*row4_45 u A X+
  (((14475295247801794560)*A))*row4_23 u A X+
  (((174550946472672)*A))*row4_24 u A X+
  (((-493733912192139990)*A))*row4_25 u A X+
  (((82228601969695995)*A+((726921679397760)*X)))*row4_34 u A X+
  (((-643907686600618348920)*A))*row4_39 u A X+
  (((162725887488355519680)*A))*row4_40 u A X+
  (((-162701766892694641920)*A))*row4_46 u A X+
  (((-2289372888)*X))*row4_21 u A X+
  (((7053341602744857)*X))*row4_22 u A X+
  (((-93675616798496040)*X))*row4_27 u A X+
  (((-164457203939391990)*X))*row4_31 u A X+
  (((234553395219010560)*X))*row4_35 u A X+
  (((1453843358795520)*X))*row4_36 u A X+
  (((14248514401492470835)*X))*row4_41 u A X+
  (((-174101998038608861760)*X))*row4_43 u A X+
  (((-81623114029734502720)*X))*row4_47 u A X=((9680))*row5_37 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_37] <;> ring
theorem row5_37_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_37 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_37_identity u A X).symm
  have hz : ((9680))*row5_37 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((9680):ℂ)=(9680)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((9680):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_37_zero
def row5_38 (u A X : ℂ) : ℂ := (((((-1820)*A+((968)*X^3+(-11094)))*A+((((-1078)*X+(3943))*X+(5838))*X+(-21000)))*A+((((74)*X+(-2488))*X+(2340))*X+(2414)))*u+((((624)*A+(1888))*A+(((((352)*X+(496))*X+(-2464))*X+(1264))*X+(496)))*A+(((((352)*X+(496))*X+(-3232))*X+(1184))*X+(2032))))
theorem row5_38_identity (u A X : ℂ) :
  (((1168376)*u+((-2938496)*A+((2488640)*X+(983488)))))*row4_48 u A X+
  (((-2450)*A))*row4_25 u A X+
  (((385)*A))*row4_34 u A X+
  (((-4007080)*A))*row4_39 u A X+
  (((813120)*A))*row4_40 u A X+
  (((-175455)*A))*row4_44 u A X+
  (((12629540)*A+((-6103020)*X)))*row4_45 u A X+
  (((-689920)*A))*row4_46 u A X+
  (((35)*X))*row4_22 u A X+
  (((-770)*X))*row4_31 u A X+
  (((97833)*X))*row4_41 u A X+
  (((-862400)*X))*row4_43 u A X+
  (((-271040)*X))*row4_47 u A X=((484))*row5_38 u A X := by
  simp only [row4_48, row4_25, row4_34, row4_39, row4_40, row4_44, row4_45, row4_46, row4_22, row4_31, row4_41, row4_43, row4_47, row5_38] <;> ring
theorem row5_38_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_38 u A X=0 := by
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_38_identity u A X).symm
  have hz : ((484))*row5_38 u A X=0 := by
    simpa only [z4_48, z4_25, z4_34, z4_39, z4_40, z4_44, z4_45, z4_46, z4_22, z4_31, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((484):ℂ)=(484)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((484):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_38_zero

def row5_40 (u A X : ℂ) : ℂ := (((((95920420695989472)*A+(((-3216233077248708)*X+(87862017725919360))*X+(141561967809086352)))*A+(((((18678020433069096)*X+(16728406598749824))*X+(-60138717876662832))*X+(-29352156620044104))*X+(6054270411774816)))*u+(((((53881712372432560)*A+(79722247714897252))*A+(-251035466218098334))*A+((((-47680362507887824)*X+(80028060129988495))*X+(100763009012899094))*X+(-713046828794569704)))*A+((((191937663709591386)*X+(-446030220649512368))*X+(62154893230329596))*X+(254092556939920982))))*u+((((((-68952647554560)*A+(-4258262952820800))*A+(38644891895533840))*A+(72737857776129280))*A+(((((192116054542720)*X+(-8811001499198640))*X+(786060716795200))*X+(3079721072942640))*X+(-12408241335394800)))*A+((((((-1632609369702080)*X+(2030507365212480))*X+(-6194307164963120))*X+(-18615032676185120))*X+(33075171758984320))*X+(25646153219829520))))
theorem row5_40_identity (u A X : ℂ) :
  (((118836305280)*u+((-649684007896)*A+((609700504336)*X+(17642907201920)))))*row4_30 u A X+
  (((9903025440)*u+((1650504240)*A+((-1650504240)*X+(25586773520)))))*row4_37 u A X+
  (((-5299032674643550920)*u+((2545528529661976320)*A+((-1578520526442256320)*X+(-590988619103072960)))))*row4_48 u A X+
  (((305884649790720)*u+((-301801749646320)*A)))*row4_33 u A X+
  (((-230872321826657280)*u+((-469916469524779200)*A+((11720257445302560)*X))))*row4_38 u A X+
  (((199455244078098096)*u+((131353352471499725)*A+((1107712813616640)*X))))*row4_44 u A X+
  (((-2010643010181479520)*u+((-11948759211659551820)*A+((3536936068467766580)*X))))*row4_45 u A X+
  (((-49694490796769280)*A))*row4_23 u A X+
  (((-599243072736)*A))*row4_24 u A X+
  (((1695015882954870)*A))*row4_25 u A X+
  (((-282295347615435)*A+((-2495562410880)*X)))*row4_34 u A X+
  (((2210570773028115960)*A))*row4_39 u A X+
  (((-558646989906075840)*A))*row4_40 u A X+
  (((558564182564424960)*A))*row4_46 u A X+
  (((7859544)*X))*row4_21 u A X+
  (((-24214512613641)*X))*row4_22 u A X+
  (((321593583908520)*X))*row4_27 u A X+
  (((564590695230870)*X))*row4_31 u A X+
  (((-805234804577280)*X))*row4_35 u A X+
  (((-4991124821760)*X))*row4_36 u A X+
  (((-48915939583348355)*X))*row4_41 u A X+
  (((597701807881442880)*X))*row4_43 u A X+
  (((280216673961815360)*X))*row4_47 u A X=((484))*row5_40 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_40] <;> ring
theorem row5_40_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_40 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_40_identity u A X).symm
  have hz : ((484))*row5_40 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((484):ℂ)=(484)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((484):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_40_zero
def row5_41 (u A X : ℂ) : ℂ := ((((((-6160)*A+(-17268))*A+(3958))*A+(((((1936)*X+(1144))*X+(-13675))*X+(5554))*X+(37000)))*A+((((-6370)*X+(21200))*X+(-8460))*X+(-14830)))*u+(((((2112)*A+(560))*A+(-3712))*A+((((752)*X+(-704))*X+(2064))*X+(2864)))*A+((((((704)*X+(-704))*X+(-656))*X+(2208))*X+(-2304))*X+(-2256))))
theorem row5_41_identity (u A X : ℂ) :
  (((-7177720)*u+((4632320)*A+((-3341888)*X+(-1091904)))))*row4_48 u A X+
  (((3290)*A))*row4_25 u A X+
  (((-517)*A))*row4_34 u A X+
  (((5380936)*A))*row4_39 u A X+
  (((-1091904)*A))*row4_40 u A X+
  (((256907)*A))*row4_44 u A X+
  (((-18961492)*A+((9196396)*X)))*row4_45 u A X+
  (((926464)*A))*row4_46 u A X+
  (((-47)*X))*row4_22 u A X+
  (((1034)*X))*row4_31 u A X+
  (((-117077)*X))*row4_41 u A X+
  (((1158080)*X))*row4_43 u A X+
  (((704704)*X))*row4_47 u A X=((484))*row5_41 u A X := by
  simp only [row4_48, row4_25, row4_34, row4_39, row4_40, row4_44, row4_45, row4_46, row4_22, row4_31, row4_41, row4_43, row4_47, row5_41] <;> ring
theorem row5_41_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_41 u A X=0 := by
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_41_identity u A X).symm
  have hz : ((484))*row5_41 u A X=0 := by
    simpa only [z4_48, z4_25, z4_34, z4_39, z4_40, z4_44, z4_45, z4_46, z4_22, z4_31, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((484):ℂ)=(484)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((484):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_41_zero
def row5_42 (u A X : ℂ) : ℂ := (((((-20420756252422646670)*A+(((218022920532077475969)*X+(-26628639364311584094))*X+(-523537621484067300924)))*A+((((-97979127427513829970)*X+(222074021552355647532))*X+(-26115766697327987592))*X+(-124094894124841817562)))*u+(((((5934259171271854192)*A+(277219874069866987384))*A+(825899019659641191766))*A+((((19713644356546296112)*X+(212870063481511090475))*X+(-139471096578716642170))*X+(78415937645329744452)))*A+((((-128084129996930772106)*X+(733197107750613174664))*X+(-477028847756751630452))*X+(-605112977753682402558))))*u+((((((10345195045531564416)*A+(32434147539494947488))*A+(-34322350741396416272))*A+((5229845721259346880)*X^4+(-57856751995726540768)))*A+(((((6654554308407390528)*X+(84800608831716482064))*X+(-27924815996228114656))*X+(38880804401714681200))*X+(27505398110919669168)))*A+((((((42708035170433954464)*X+(-42233655300197478304))*X+(54924282130573188880))*X+(-85502890221288693632))*X+(-111184883991435021536))*X+(-13078186820191402032))))
theorem row5_42_identity (u A X : ℂ) :
  (((-422528514500252160)*u+((2263017368022168912)*A+((-1073353598389519392)*X+(-932019211026784980)))))*row4_30 u A X+
  (((-35210709541687680)*u+((-5868451590281280)*A+((5868451590281280)*X+(-95244807649211440)))))*row4_37 u A X+
  (((607571223729379663125240)*u+((-1495767859391742448976640)*A+((874097469079166580747840)*X+(312466680701386320563520)))))*row4_48 u A X+
  (((-1087588396323649059840)*u+((531310031202812099040)*A)))*row4_33 u A X+
  (((820878257286741890396160)*u+((-99885375830922720667200)*A+((-47949919408587262936320)*X))))*row4_38 u A X+
  (((16037004221153657822520)*u+((-83600260375273378418475)*A+((-3938529126495017134080)*X))))*row4_44 u A X+
  (((-723045897399198230652960)*u+((6872931293992822593987540)*A+((-2302655029259955215809260)*X))))*row4_45 u A X+
  (((176691284079657447260160)*A))*row4_23 u A X+
  (((2130639157378123392)*A))*row4_24 u A X+
  (((-1081221912459781156890)*A))*row4_25 u A X+
  (((214839509679328293045)*A+((8873098804505295360)*X)))*row4_34 u A X+
  (((-1454591727036825727707720)*A))*row4_39 u A X+
  (((344959220111821712527680)*A))*row4_40 u A X+
  (((-447726980545447327845120)*A))*row4_46 u A X+
  (((-27945007572768)*X))*row4_21 u A X+
  (((15446027320854016527)*X))*row4_22 u A X+
  (((-1120193597170973611440)*X))*row4_27 u A X+
  (((-429679019358656586090)*X))*row4_31 u A X+
  (((2863053214253708636160)*X))*row4_35 u A X+
  (((17746197609010590720)*X))*row4_36 u A X+
  (((35068734394977794794485)*X))*row4_41 u A X+
  (((-333720640040930730624960)*X))*row4_43 u A X+
  (((-129372781051263065469120)*X))*row4_47 u A X=((9680))*row5_42 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_42] <;> ring
theorem row5_42_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_42 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_42_identity u A X).symm
  have hz : ((9680))*row5_42 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((9680):ℂ)=(9680)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((9680):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_42_zero
def row5_43 (u A X : ℂ) : ℂ := (((((-1260)*A+(-1798))*A+((((2046)*X+(-4009))*X+(-3330))*X+(9736)))*A+(((((968)*X^2+(-470))*X+(-7456))*X+(3556))*X+(5022)))*u+((((432)*A+(-480))*A+(((((-352)*X+(-848))*X+(2464))*X+(-912))*X+(-848)))*A+(((((-352)*X+(-848))*X+(2528))*X+(224))*X+(-976))))
theorem row5_43_identity (u A X : ℂ) :
  (((2430648)*u+((770176)*A+((-924352)*X+(-472384)))))*row4_48 u A X+
  (((910)*A))*row4_25 u A X+
  (((-143)*A))*row4_34 u A X+
  (((1488344)*A))*row4_39 u A X+
  (((-302016)*A))*row4_40 u A X+
  (((65169)*A+((10648)*X)))*row4_44 u A X+
  (((-3753948)*A+((2266836)*X)))*row4_45 u A X+
  (((256256)*A))*row4_46 u A X+
  (((-13)*X))*row4_22 u A X+
  (((286)*X))*row4_31 u A X+
  (((-32383)*X))*row4_41 u A X+
  (((320320)*X))*row4_43 u A X+
  (((100672)*X))*row4_47 u A X=((484))*row5_43 u A X := by
  simp only [row4_48, row4_25, row4_34, row4_39, row4_40, row4_44, row4_45, row4_46, row4_22, row4_31, row4_41, row4_43, row4_47, row5_43] <;> ring
theorem row5_43_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_43 u A X=0 := by
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_43_identity u A X).symm
  have hz : ((484))*row5_43 u A X=0 := by
    simpa only [z4_48, z4_25, z4_34, z4_39, z4_40, z4_44, z4_45, z4_46, z4_22, z4_31, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((484):ℂ)=(484)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((484):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_43_zero
def row5_44 (u A X : ℂ) : ℂ := (((((-18311368541656769370)*A+(((24883415232142664043)*X+(-17895915310776147018))*X+(-91016565186944589588)))*A+((((-6365867757204523590)*X+(4263545415824267364))*X+(8468190098584779816))*X+(2102322341380256226)))*u+(((((22445644867272625504)*A+(68237395093722028948))*A+(-100214482606174369448))*A+((((-9870899825800357916)*X+(6524378955076842350))*X+(66741140300876482340))*X+(-349110870757396413036)))*A+((((60059899689590560208)*X+(-168852391926188048072))*X+(48732592547006927656))*X+(108792492236597487864))))*u+((((((3365182353290389632)*A+(208474808533887456))*A+(8616004088078515456))*A+(41300174107036633504))*A+((((((1743281907086448960)*X+(-1579883006437909184))*X+(399216722745753888))*X+(-13194512074943362592))*X+(-7718890128966682080))*X+(-12316716376932258624)))*A+((((((-1675538695919091872)*X+(-7693019589830047968))*X+(19737583776710740960))*X+(-14739979027232075744))*X+(6721563722896197088))*X+(15415050517938706336))))
theorem row5_44_identity (u A X : ℂ) :
  (((-137974469289592320)*u+((738657606963469424)*A+((-343068104623276384)*X+(115176301205795940)))))*row4_30 u A X+
  (((-11497872440799360)*u+((-1916312073466560)*A+((1916312073466560)*X+(3458249119207520)))))*row4_37 u A X+
  (((74620232570587359597480)*u+((-437147500696530218369280)*A+((253264847576719770559680)*X+(73015814646962156066240)))))*row4_48 u A X+
  (((-355146283951410631680)*u+((169818711788521810080)*A)))*row4_33 u A X+
  (((268053487548557009080320)*u+((-44637566232818053598400)*A+((-15700412941249327568640)*X))))*row4_38 u A X+
  (((5200773271339393832040)*u+((-24696258825055231824825)*A+((-1286106019738053212160)*X))))*row4_44 u A X+
  (((-289546476704532188269920)*u+((2002568189940179263399580)*A+((-682180145258797380314020)*X))))*row4_45 u A X+
  (((57697611669644558008320)*A))*row4_23 u A X+
  (((695749036806592384)*A))*row4_24 u A X+
  (((-319494463641252552030)*A))*row4_25 u A X+
  (((64799366759808874215)*A+((2897463855081438720)*X)))*row4_34 u A X+
  (((-431507046467870889340440)*A))*row4_39 u A X+
  (((101502264501864774567360)*A))*row4_40 u A X+
  (((-135760183379041693866240)*A))*row4_46 u A X+
  (((-9125295587936)*X))*row4_21 u A X+
  (((4564206623446465029)*X))*row4_22 u A X+
  (((-365635515446917364880)*X))*row4_27 u A X+
  (((-129598733519617748430)*X))*row4_31 u A X+
  (((934915003906277560320)*X))*row4_35 u A X+
  (((5794927710162877440)*X))*row4_36 u A X+
  (((10508887109944616637095)*X))*row4_41 u A X+
  (((-113688368284766794854720)*X))*row4_43 u A X+
  (((-36360630460051261362240)*X))*row4_47 u A X=((9680))*row5_44 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_44] <;> ring
theorem row5_44_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_44 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_44_identity u A X).symm
  have hz : ((9680))*row5_44 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((9680):ℂ)=(9680)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((9680):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_44_zero
def row5_45 (u A X : ℂ) : ℂ := (((((20420756252422646670)*A+(((-218022920532077475969)*X+(26628639364311584094))*X+(523537621484067300924)))*A+((((97979127427513829970)*X+(-222074021552355647532))*X+(26115766697327987592))*X+(124094894124841817562)))*u+(((((-5934259171271854192)*A+(-277219874069866987384))*A+(-825899019659641191766))*A+((((-19713644356546296112)*X+(-212870063481511090475))*X+(139471096578716642170))*X+(-78415937645329744452)))*A+((((128084129996930772106)*X+(-733197107750613174664))*X+(477028847756751630452))*X+(605112977753682402558))))*u+((((((-10345195045531564416)*A+(-32434147539494947488))*A+(34322350741396416272))*A+(52626906274467193888))*A+(((((-1424708587148043648)*X+(-79570763110457135184))*X+(33154661717487461536))*X+(-33650958680455334320))*X+(-27505398110919669168)))*A+(((((((5229845721259346880)*X+(-47937880891693301344))*X+(37003809578938131424))*X+(-54924282130573188880))*X+(80273044500029346752))*X+(116414729712694368416))*X+(18308032541450748912))))
theorem row5_45_identity (u A X : ℂ) :
  (((422528514500252160)*u+((-2263017368022168912)*A+((1073353598389519392)*X+(932019211026784980)))))*row4_30 u A X+
  (((35210709541687680)*u+((5868451590281280)*A+((-5868451590281280)*X+(95244807649211440)))))*row4_37 u A X+
  (((-607571223729379663125240)*u+((1495767859391742448976640)*A+((-874097469079166580747840)*X+(-261841774119595842765120)))))*row4_48 u A X+
  (((1087588396323649059840)*u+((-531310031202812099040)*A)))*row4_33 u A X+
  (((-820878257286741890396160)*u+((99885375830922720667200)*A+((47949919408587262936320)*X))))*row4_38 u A X+
  (((-16037004221153657822520)*u+((83600260375273378418475)*A+((3938529126495017134080)*X))))*row4_44 u A X+
  (((723045897399198230652960)*u+((-6872931293992822593987540)*A+((2302655029259955215809260)*X))))*row4_45 u A X+
  (((-176691284079657447260160)*A))*row4_23 u A X+
  (((-2130639157378123392)*A))*row4_24 u A X+
  (((1081221912459781156890)*A))*row4_25 u A X+
  (((-214839509679328293045)*A+((-8873098804505295360)*X)))*row4_34 u A X+
  (((1454591727036825727707720)*A))*row4_39 u A X+
  (((-344959220111821712527680)*A))*row4_40 u A X+
  (((447726980545447327845120)*A))*row4_46 u A X+
  (((27945007572768)*X))*row4_21 u A X+
  (((-15446027320854016527)*X))*row4_22 u A X+
  (((1120193597170973611440)*X))*row4_27 u A X+
  (((429679019358656586090)*X))*row4_31 u A X+
  (((-2863053214253708636160)*X))*row4_35 u A X+
  (((-17746197609010590720)*X))*row4_36 u A X+
  (((-35068734394977794794485)*X))*row4_41 u A X+
  (((384345546622721208423360)*X))*row4_43 u A X+
  (((129372781051263065469120)*X))*row4_47 u A X=((9680))*row5_45 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_45] <;> ring
theorem row5_45_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_45 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_45_identity u A X).symm
  have hz : ((9680))*row5_45 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((9680):ℂ)=(9680)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((9680):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_45_zero

def row5_46 (u A X : ℂ) : ℂ := ((((((1698001857551736)*A+(9314276354121420))*A+(((478151107113834)*X+(1661342434821828))*X+(10254463016448816)))*A+((((162611272133244)*X+(3230213474103264))*X+(-3555436018369752))*X+(-3392824746236508)))*u+(((((1539477496355216)*A+(1695606440693612))*A+(-7948671312540746))*A+((((-1168238716505168)*X+(2286516003713957))*X+(2684885759505490))*X+(-20178709181838936)))*A+((((5677990603994238)*X+(-12355605879688528))*X+(999624671700052))*X+(6677615275694290))))*u+((((((-1970075644416)*A+(-121664655794880))*A+(1104139768443824))*A+(2078224507889408))*A+(((((5489030129792)*X+(-251742899977104))*X+(22458877622720))*X+(87992030655504))*X+(-354521181011280)))*A+((((((-46645981991488)*X+(58014496148928))*X+(-176980204713232))*X+(-531858076462432))*X+(945004907399552))*X+(732747234852272))))
theorem row5_46_identity (u A X : ℂ) :
  (((16976615040)*u+((-92812001128)*A+((87100072048)*X+(2520415314560)))))*row4_30 u A X+
  (((1414717920)*u+((235786320)*A+((-235786320)*X+(3655253360)))))*row4_37 u A X+
  (((-757004667806221560)*u+((363646932808853760)*A+((-225502932348893760)*X+(-84426945586153280)))))*row4_48 u A X+
  (((43697807112960)*u+((-43114535663760)*A)))*row4_33 u A X+
  (((-32981760260951040)*u+((-67130924217825600)*A+((1674322492186080)*X))))*row4_38 u A X+
  (((-857568669380280)*u+((18764764638785675)*A+((158244687659520)*X))))*row4_44 u A X+
  (((-287234715740211360)*u+((-1706965601665650260)*A+((505276581209680940)*X))))*row4_45 u A X+
  (((-7099212970967040)*A))*row4_23 u A X+
  (((-85606153248)*A))*row4_24 u A X+
  (((242145126136410)*A))*row4_25 u A X+
  (((-40327906802205)*A+((-356508915840)*X)))*row4_34 u A X+
  (((315795824718302280)*A))*row4_39 u A X+
  (((-79806712843725120)*A))*row4_40 u A X+
  (((79794883223489280)*A))*row4_46 u A X+
  (((1122792)*X))*row4_21 u A X+
  (((-3459216087663)*X))*row4_22 u A X+
  (((45941940558360)*X))*row4_27 u A X+
  (((80655813604410)*X))*row4_31 u A X+
  (((-115033543511040)*X))*row4_35 u A X+
  (((-713017831680)*X))*row4_36 u A X+
  (((-6987991369049765)*X))*row4_41 u A X+
  (((85385972554491840)*X))*row4_43 u A X+
  (((40030953423116480)*X))*row4_47 u A X=((2420))*row5_46 u A X := by
  simp only [row4_30, row4_37, row4_48, row4_33, row4_38, row4_44, row4_45, row4_23, row4_24, row4_25, row4_34, row4_39, row4_40, row4_46, row4_21, row4_22, row4_27, row4_31, row4_35, row4_36, row4_41, row4_43, row4_47, row5_46] <;> ring
theorem row5_46_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_46 u A X=0 := by
  have z4_30 := row4_30_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_37 := row4_37_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_33 := row4_33_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_38 := row4_38_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_44 := row4_44_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_23 := row4_23_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_24 := row4_24_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_25 := row4_25_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_34 := row4_34_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_39 := row4_39_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_40 := row4_40_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_21 := row4_21_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_22 := row4_22_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_27 := row4_27_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_31 := row4_31_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_35 := row4_35_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_36 := row4_36_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_41 := row4_41_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_43 := row4_43_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_46_identity u A X).symm
  have hz : ((2420))*row5_46 u A X=0 := by
    simpa only [z4_30, z4_37, z4_48, z4_33, z4_38, z4_44, z4_45, z4_23, z4_24, z4_25, z4_34, z4_39, z4_40, z4_46, z4_21, z4_22, z4_27, z4_31, z4_35, z4_36, z4_41, z4_43, z4_47,mul_zero,add_zero] using he
  have hunit : ((2420):ℂ)=(2420)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((2420):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_46_zero
def row5_47 (u A X : ℂ) : ℂ := (((((1)*X+(-1))*A+((1)*X))*A+(((1)*X+(-2))*X^2+(1)))*u^2)
theorem row5_47_identity (u A X : ℂ) :
  (((1)*u))*row4_45 u A X=((1))*row5_47 u A X := by
  simp only [row4_45, row5_47] <;> ring
theorem row5_47_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_47 u A X=0 := by
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_47_identity u A X).symm
  have hz : ((1))*row5_47 u A X=0 := by
    simpa only [z4_45,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_47_zero
def row5_48 (u A X : ℂ) : ℂ := ((((((1)*X+(-1))*A+(1))*A+((((1)*X+(-2))*X+(-1))*X+(1)))*A+(((-1)*X+(2))*X^2+(-1)))*u)
theorem row5_48_identity (u A X : ℂ) :
  (((-1)*u))*row4_48 u A X+
  (((1)*A))*row4_45 u A X=((1))*row5_48 u A X := by
  simp only [row4_48, row4_45, row5_48] <;> ring
theorem row5_48_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_48 u A X=0 := by
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_45 := row4_45_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_48_identity u A X).symm
  have hz : ((1))*row5_48 u A X=0 := by
    simpa only [z4_48, z4_45,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_48_zero
def row5_49 (u A X : ℂ) : ℂ := ((((((1)*X+(-1))*A+(1))*A+(-1))*A+((((-2)*X+(3))*X+(2))*X+(-1)))*A+(((((-1)*X+(3))*X^2+(-5))*X+(1))*X+(2)))
theorem row5_49_identity (u A X : ℂ) :
  (((2)*X+(2)))*row4_48 u A X+
  (((1)*A))*row4_46 u A X+
  (((-1)*X))*row4_47 u A X=((1))*row5_49 u A X := by
  simp only [row4_48, row4_46, row4_47, row5_49] <;> ring
theorem row5_49_zero (u A X : ℂ) (hA : A≠0) (hX : X≠0) (hA1 : A+1≠0)
    (h0 : input0 u A X=0)
    (h1 : input1 u A X=0)
    (h2 : input2 u A X=0)
    (h3 : input3 u A X=0)
    : row5_49 u A X=0 := by
  have z4_48 := row4_48_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_46 := row4_46_zero u A X hA hX hA1 h0 h1 h2 h3
  have z4_47 := row4_47_zero u A X hA hX hA1 h0 h1 h2 h3
  have he := (row5_49_identity u A X).symm
  have hz : ((1))*row5_49 u A X=0 := by
    simpa only [z4_48, z4_46, z4_47,mul_zero,add_zero] using he
  have hunit : ((1):ℂ)=(1)*A^0*X^0*(A+1)^0 := by ring
  have hu : ((1):ℂ)≠0 := by
    rw [hunit]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA)) (pow_ne_zero _ hX)) (pow_ne_zero _ hA1)
  exact (mul_eq_zero.mp hz).resolve_left hu
#print axioms row5_49_zero
def row5_50 (u A X : ℂ) : ℂ := (((((140)*A+((44)*X^2+(498)))*A+(((91)*X+(-26))*X+(512)))*A+((((-70)*X+(320))*X+(-180))*X+(-250)))*u+((((-48)*A+(-64))*A+(((16)*X^2+(-16))*X+(16)))*A+((((16)*X+(32))*X+(-64))*X+(-48))))
theorem row5_50_identity (u A X : ℂ) :
  (((-121000)*u+((98560)*A+((-71104)*X+(-23232)))))*row4_48 u A X+
  (((70)*A))*row4_25 u A X+
  (((-11)*A))*row4_34 u A X+
  (((114488)*A))*row4_39 u A X+
  (((-23232)*A))*row4_40 u A X+
  (((5013)*A))*row4_44 u A X+
  (((-403436)*A+((195668)*X)))*row4_45 u A X+
  (((19712)*A))*row4_46 u A X+
  (((-1)*X))*row4_22 u A X+
  (((22)*X))*row4_31 u A X+
  (((-2491)*X))*row4_41 u A X+
  (((24640)*X))*row4_43 u A X+
  (((7744)*X))*row4_47 u A X=((484))*row5_50 u A X := by
  simp only [row4_48, row4_25, row4_34, row4_39, row4_40, row4_44, row4_45, row4_46, row4_22, row4_31, row4_41, row4_43, row4_47, row5_50] <;> ring

}
end QuantitativeArithmeticSmallLevelTwentyFive.NegativeDZeroAlgebra
end
