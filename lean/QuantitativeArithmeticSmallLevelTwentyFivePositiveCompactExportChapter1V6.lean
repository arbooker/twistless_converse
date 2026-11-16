module

public import QuantitativeArithmeticSmallLevelTwentyFivePositiveChartSixSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFivePositiveCompactExportChapter0V6
public meta import SmallLevelCertificateBatchCommandV1
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.PositiveChart.CompactSource
certificate_batch {
theorem relation6 (u B A Y X : ℂ) :
  (((((-1)*X)*Y+(1))*Y))*row0 u B A Y X+
  (((1)*Y))*row5 u B A Y X=(((1)*Y))*row6 u B A Y X := by
  simp only [row0, row5, row6]
  ring
theorem zero6 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<6, row u B A Y X i=0) : row6 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have he := (relation6 u B A Y X).symm
  have hf : (((1)*Y):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((1)*Y))*row6 u B A Y X=0 := by
    simpa only [h0, h5, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero6

theorem relation7 (u B A Y X : ℂ) :
  (((((-1)*Y)*A+(((1)*X+(1))*Y))*B+((((1)*Y+(1))*Y)*A+(((-1)*Y+(-2))*Y))))*row0 u B A Y X+
  (((1)*Y))*row2 u B A Y X+
  (((-1)*Y))*row5 u B A Y X+
  (((1)*Y))*row6 u B A Y X=(((1)*Y))*row7 u B A Y X := by
  simp only [row0, row2, row5, row6, row7]
  ring
theorem zero7 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<7, row u B A Y X i=0) : row7 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have he := (relation7 u B A Y X).symm
  have hf : (((1)*Y):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((1)*Y))*row7 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero7

theorem relation8 (u B A Y X : ℂ) :
  (((((-160)*X)*A+((160)*X^2))*B+((160)*A+((-160)*Y+((-416)*X+(-2336))))))*row0 u B A Y X+
  ((80))*row1 u B A Y X+
  (((160)*X))*row2 u B A Y X+
  ((1))*row3 u B A Y X+
  ((-1))*row4 u B A Y X+
  (((160)*A+((-160)*Y+((-160)*X+(-192)))))*row5 u B A Y X+
  (((160)*X+(992)))*row6 u B A Y X+
  ((((-160)*X)*B+(((160)*X+(-320))*X)))*row7 u B A Y X=(((4)*X))*row8 u B A Y X := by
  simp only [row0, row1, row2, row3, row4, row5, row6, row7, row8]
  ring
theorem zero8 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<8, row u B A Y X i=0) : row8 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h1 : row1 u B A Y X=0 := hs 1 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h3 : row3 u B A Y X=0 := hs 3 (by decide)
  have h4 : row4 u B A Y X=0 := hs 4 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have he := (relation8 u B A Y X).symm
  have hf : (((4)*X):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((4)*X))*row8 u B A Y X=0 := by
    simpa only [h0, h1, h2, h3, h4, h5, h6, h7, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero8

theorem relation9 (u B A Y X : ℂ) :
  ((((-900)*X^2)*A+((((-900)*X+(900))*X+(-960))*Y+(((-360)*X+(-4692))*X+(22188)))))*row0 u B A Y X+
  ((480))*row1 u B A Y X+
  ((2))*row3 u B A Y X+
  ((13))*row4 u B A Y X+
  (((180)*X+(-564)))*row5 u B A Y X+
  (((-900)*X+(-4716)))*row6 u B A Y X+
  ((((960)*X+(480))*X))*row7 u B A Y X=(((1)*X))*row9 u B A Y X := by
  simp only [row0, row1, row3, row4, row5, row6, row7, row9]
  ring
theorem zero9 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<9, row u B A Y X i=0) : row9 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h1 : row1 u B A Y X=0 := hs 1 (by decide)
  have h3 : row3 u B A Y X=0 := hs 3 (by decide)
  have h4 : row4 u B A Y X=0 := hs 4 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have he := (relation9 u B A Y X).symm
  have hf : (((1)*X):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((1)*X))*row9 u B A Y X=0 := by
    simpa only [h0, h1, h3, h4, h5, h6, h7, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero9

theorem relation10 (u B A Y X : ℂ) :
  ((((120)*A+((-120)*X+(-120)))*B+(((-120)*Y+((-240)*X+(-120)))*A+(((-240)*X+(120))*Y+((-96)*X+(-1536))))))*row0 u B A Y X+
  ((-120))*row2 u B A Y X+
  ((1))*row3 u B A Y X+
  ((-1))*row4 u B A Y X+
  ((168))*row5 u B A Y X+
  ((312))*row6 u B A Y X+
  ((120))*row7 u B A Y X=(((4)*X))*row10 u B A Y X := by
  simp only [row0, row2, row3, row4, row5, row6, row7, row10]
  ring
theorem zero10 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<10, row u B A Y X i=0) : row10 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h3 : row3 u B A Y X=0 := hs 3 (by decide)
  have h4 : row4 u B A Y X=0 := hs 4 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have he := (relation10 u B A Y X).symm
  have hf : (((4)*X):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((4)*X))*row10 u B A Y X=0 := by
    simpa only [h0, h2, h3, h4, h5, h6, h7, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero10

theorem relation11 (u B A Y X : ℂ) :
  (((((-80640)*A)*B+(((80640)*A+((80640)*Y+(-779520)))*A+(((60480)*X+(262080))*Y+(((-80640)*X+(809760))*X+(2160480)))))*B+((((-80640)*Y+(-80640))*A+((860160)*Y+(860160)))*A+((((322560)*X+(430080))*X+(-5913600))*Y+(((161280)*X+(295680))*X+(1344000))))))*row0 u B A Y X+
  ((-255360))*row1 u B A Y X+
  (((80640)*B+((-80640)*A+((-80640)*X+(779520)))))*row2 u B A Y X+
  ((-1400))*row3 u B A Y X+
  ((1400))*row4 u B A Y X+
  (((80640)*B+((80640)*X+(-1021440))))*row5 u B A Y X+
  (((60480)*B+((241920)*X+(-1290240))))*row6 u B A Y X+
  ((((221760)*A+(-120960))*B+(((322560)*X+(430080))*A+(((-510720)*X+(1317120))*X+(-215040)))))*row7 u B A Y X+
  (((2016)*X+(-2016)))*row8 u B A Y X+
  (((84)*B+((357)*A+((448)*X+(-1344)))))*row9 u B A Y X+
  (((4368)*B+((11904)*A+((26880)*X+(-67872)))))*row10 u B A Y X=(((15)*A))*row11 u B A Y X := by
  simp only [row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11]
  ring
theorem zero11 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<11, row u B A Y X i=0) : row11 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h1 : row1 u B A Y X=0 := hs 1 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h3 : row3 u B A Y X=0 := hs 3 (by decide)
  have h4 : row4 u B A Y X=0 := hs 4 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h8 : row8 u B A Y X=0 := hs 8 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have he := (relation11 u B A Y X).symm
  have hf : (((15)*A):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((15)*A))*row11 u B A Y X=0 := by
    simpa only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero11

theorem relation12 (u B A Y X : ℂ) :
  ((((-3060)*A+((3060)*X+(9780)))*B+(((3060)*Y+(3060))*A+((((1440)*X+(1200))*X+(-29700))*Y+(((720)*X+(24))*X+(1104))))))*row0 u B A Y X+
  ((-960))*row1 u B A Y X+
  ((3060))*row2 u B A Y X+
  ((-4))*row3 u B A Y X+
  ((4))*row4 u B A Y X+
  ((-4212))*row5 u B A Y X+
  (((1440)*X+(-4668)))*row6 u B A Y X+
  ((((1440)*X+(1200))*A+(((-1920)*X+(5760))*X+(300))))*row7 u B A Y X+
  (((2)*X+(-7)))*row9 u B A Y X+
  (((120)*X+(-364)))*row10 u B A Y X=(((15)*A))*row12 u B A Y X := by
  simp only [row0, row1, row2, row3, row4, row5, row6, row7, row9, row10, row12]
  ring
theorem zero12 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<12, row u B A Y X i=0) : row12 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h1 : row1 u B A Y X=0 := hs 1 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h3 : row3 u B A Y X=0 := hs 3 (by decide)
  have h4 : row4 u B A Y X=0 := hs 4 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have he := (relation12 u B A Y X).symm
  have hf : (((15)*A):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((15)*A))*row12 u B A Y X=0 := by
    simpa only [h0, h1, h2, h3, h4, h5, h6, h7, h9, h10, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero12

theorem relation13 (u B A Y X : ℂ) :
  ((((-42360)*A+((42360)*X+(114360)))*B+(((42360)*Y+(42360))*A+((((23040)*X+(45840))*X+(-317640))*Y+(((11520)*X+(13704))*X+(35304))))))*row0 u B A Y X+
  ((-15360))*row1 u B A Y X+
  ((42360))*row2 u B A Y X+
  ((-64))*row3 u B A Y X+
  ((64))*row4 u B A Y X+
  ((-60792))*row5 u B A Y X+
  (((23040)*X+(-54648)))*row6 u B A Y X+
  ((((23040)*X+(45840))*A+(((-30720)*X+(56640))*X+(-6360))))*row7 u B A Y X+
  (((32)*X+(-75)))*row9 u B A Y X+
  (((1920)*X+(-3900)))*row10 u B A Y X+
  (((-240)*A))*row12 u B A Y X=(((15)*A))*row13 u B A Y X := by
  simp only [row0, row1, row2, row3, row4, row5, row6, row7, row9, row10, row12, row13]
  ring
theorem zero13 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<13, row u B A Y X i=0) : row13 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h1 : row1 u B A Y X=0 := hs 1 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h3 : row3 u B A Y X=0 := hs 3 (by decide)
  have h4 : row4 u B A Y X=0 := hs 4 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have he := (relation13 u B A Y X).symm
  have hf : (((15)*A):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((15)*A))*row13 u B A Y X=0 := by
    simpa only [h0, h1, h2, h3, h4, h5, h6, h7, h9, h10, h12, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero13

theorem relation14 (u B A Y X : ℂ) :
  ((((35520)*A+((-248640)*X+(-1172160)))*B+(((-35520)*Y+(-35520))*A+(((1065600)*X+(4866240))*Y+((-42624)*X+(-468864))))))*row0 u B A Y X+
  ((106560))*row1 u B A Y X+
  ((-35520))*row2 u B A Y X+
  ((444))*row3 u B A Y X+
  ((-444))*row4 u B A Y X+
  ((163392))*row5 u B A Y X+
  ((1115328))*row6 u B A Y X+
  (((159840)*A+((-1136640)*X+(-319680))))*row7 u B A Y X+
  ((1184))*row9 u B A Y X+
  (((-1776)*X+(61568)))*row10 u B A Y X+
  (((1665)*A))*row12 u B A Y X+
  ((((-90)*X+(-165))*A))*row13 u B A Y X=(((213120)*A))*row14 u B A Y X := by
  simp only [row0, row1, row2, row3, row4, row5, row6, row7, row9, row10, row12, row13, row14]
  ring
theorem zero14 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<14, row u B A Y X i=0) : row14 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h1 : row1 u B A Y X=0 := hs 1 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h3 : row3 u B A Y X=0 := hs 3 (by decide)
  have h4 : row4 u B A Y X=0 := hs 4 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have he := (relation14 u B A Y X).symm
  have hf : (((213120)*A):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((213120)*A))*row14 u B A Y X=0 := by
    simpa only [h0, h1, h2, h3, h4, h5, h6, h7, h9, h10, h12, h13, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero14

theorem relation15 (u B A Y X : ℂ) :
  ((((-80)*A+((80)*X+(176)))*B+(((80)*Y+(80))*A+(((168)*Y+(16))*Y+(-184)))))*row0 u B A Y X+
  ((80))*row2 u B A Y X+
  ((-80))*row5 u B A Y X+
  ((80))*row6 u B A Y X+
  ((-80))*row7 u B A Y X+
  (((-1)*A+((1)*Y+(-1))))*row10 u B A Y X+
  (((336)*Y))*row14 u B A Y X=(((1)*Y))*row15 u B A Y X := by
  simp only [row0, row2, row5, row6, row7, row10, row14, row15]
  ring
theorem zero15 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<15, row u B A Y X i=0) : row15 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have he := (relation15 u B A Y X).symm
  have hf : (((1)*Y):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((1)*Y))*row15 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, h7, h10, h14, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero15

theorem relation16 (u B A Y X : ℂ) :
  ((((142346400)*A+((-116239200)*X+(16783200)))*B+(((-142346400)*Y+(-142346400))*A+((((26107200)*X+(278476800))*Y+(338772000))*Y+(271017600)))))*row0 u B A Y X+
  ((-142346400))*row2 u B A Y X+
  ((142346400))*row5 u B A Y X+
  (((-26107200)*A+((26107200)*Y+(-674933280))))*row6 u B A Y X+
  (((257591040)*B+((-10442880)*Y+(486961440))))*row7 u B A Y X+
  ((6439776))*row8 u B A Y X+
  ((-268324))*row9 u B A Y X+
  (((-1657600)*A+((1657600)*Y+((3263400)*X+(-21832664)))))*row10 u B A Y X+
  (((543900)*Y))*row12 u B A Y X+
  (((91875)*Y+(8820)))*row13 u B A Y X+
  (((747225360)*Y))*row14 u B A Y X+
  ((((-155400)*X+(-190920))*Y))*row15 u B A Y X=(((185)*Y))*row16 u B A Y X := by
  simp only [row0, row2, row5, row6, row7, row8, row9, row10, row12, row13, row14, row15, row16]
  ring
theorem zero16 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<16, row u B A Y X i=0) : row16 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h8 : row8 u B A Y X=0 := hs 8 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have he := (relation16 u B A Y X).symm
  have hf : (((185)*Y):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((185)*Y))*row16 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, h7, h8, h9, h10, h12, h13, h14, h15, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero16

theorem relation17 (u B A Y X : ℂ) :
  ((((1767120)*A+((-1767120)*X+(79920)))*B+(((-1767120)*Y+(-1767120))*A+(((3232320)*Y+(3614160))*Y+(3072480)))))*row0 u B A Y X+
  ((-1767120))*row2 u B A Y X+
  ((1767120))*row5 u B A Y X+
  ((-7920960))*row6 u B A Y X+
  (((3232320)*B+((372960)*Y+(7175040))))*row7 u B A Y X+
  ((80808))*row8 u B A Y X+
  ((-3367))*row9 u B A Y X+
  (((-19240)*A+((19240)*Y+((38850)*X+(-282902)))))*row10 u B A Y X+
  ((-315))*row13 u B A Y X+
  (((9759120)*Y))*row14 u B A Y X=(((185)*Y))*row17 u B A Y X := by
  simp only [row0, row2, row5, row6, row7, row8, row9, row10, row13, row14, row17]
  ring
theorem zero17 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<17, row u B A Y X i=0) : row17 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h8 : row8 u B A Y X=0 := hs 8 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have he := (relation17 u B A Y X).symm
  have hf : (((185)*Y):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((185)*Y))*row17 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, h7, h8, h9, h10, h13, h14, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero17

theorem relation18 (u B A Y X : ℂ) :
  ((((-1767120)*A+((1767120)*X+(-79920)))*B+(((1767120)*Y+(1767120))*A+(((-3232320)*Y+(-3614160))*Y+(-3072480)))))*row0 u B A Y X+
  ((1767120))*row2 u B A Y X+
  ((-1767120))*row5 u B A Y X+
  ((8293920))*row6 u B A Y X+
  (((-3232320)*B+((-497280)*X+(-7796640))))*row7 u B A Y X+
  ((-80808))*row8 u B A Y X+
  ((3885))*row9 u B A Y X+
  (((19240)*A+((-19240)*Y+((-38850)*X+(309838)))))*row10 u B A Y X+
  ((525))*row13 u B A Y X+
  (((-11126640)*Y))*row14 u B A Y X=(((185)*Y))*row18 u B A Y X := by
  simp only [row0, row2, row5, row6, row7, row8, row9, row10, row13, row14, row18]
  ring
theorem zero18 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<18, row u B A Y X i=0) : row18 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h8 : row8 u B A Y X=0 := hs 8 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have he := (relation18 u B A Y X).symm
  have hf : (((185)*Y):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((185)*Y))*row18 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, h7, h8, h9, h10, h13, h14, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero18

theorem relation19 (u B A Y X : ℂ) :
  ((((-2749248)*A+((2749248)*X+(-92352)))*B+(((2749248)*Y+(2749248))*A+(((-4972800)*Y+(-5590848))*Y+(-4788096)))))*row0 u B A Y X+
  ((2749248))*row2 u B A Y X+
  ((-2749248))*row5 u B A Y X+
  ((12147840))*row6 u B A Y X+
  (((-4972800)*B+(-11476512)))*row7 u B A Y X+
  ((-124320))*row8 u B A Y X+
  ((5180))*row9 u B A Y X+
  (((29600)*A+((-29600)*Y+((-55944)*X+(454360)))))*row10 u B A Y X+
  ((-2331))*row12 u B A Y X+
  (((126)*X+(819)))*row13 u B A Y X+
  (((-17653440)*Y+(298368)))*row14 u B A Y X=(((148)*Y))*row19 u B A Y X := by
  simp only [row0, row2, row5, row6, row7, row8, row9, row10, row12, row13, row14, row19]
  ring
theorem zero19 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<19, row u B A Y X i=0) : row19 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h8 : row8 u B A Y X=0 := hs 8 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have he := (relation19 u B A Y X).symm
  have hf : (((148)*Y):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((148)*Y))*row19 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, h7, h8, h9, h10, h12, h13, h14, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero19

theorem relation20 (u B A Y X : ℂ) :
  ((((888000)*A+((-888000)*X+(26959680)))*B+(((-888000)*Y+(-888000))*A+(((-57435840)*X+(-322841280))*Y+((-93985920)*X+(-474120960))))))*row0 u B A Y X+
  ((-888000))*row2 u B A Y X+
  ((888000))*row5 u B A Y X+
  ((-58323840))*row6 u B A Y X+
  (((-57435840)*A+((41771520)*X+(126202560))))*row7 u B A Y X+
  ((-43512))*row9 u B A Y X+
  ((-3132864))*row10 u B A Y X+
  ((-543900))*row12 u B A Y X+
  (((17640)*A+(-91875)))*row13 u B A Y X+
  (((120093120)*A+(-435679440)))*row14 u B A Y X+
  (((155400)*X+(1019720)))*row15 u B A Y X+
  ((185))*row16 u B A Y X+
  (((12950)*A+(-46620)))*row17 u B A Y X+
  ((-31080))*row18 u B A Y X=(((2590)*A))*row20 u B A Y X := by
  simp only [row0, row2, row5, row6, row7, row9, row10, row12, row13, row14, row15, row16, row17, row18, row20]
  ring
theorem zero20 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<20, row u B A Y X i=0) : row20 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have he := (relation20 u B A Y X).symm
  have hf : (((2590)*A):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((2590)*A))*row20 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, h7, h9, h10, h12, h13, h14, h15, h16, h17, h18, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero20

theorem relation21 (u B A Y X : ℂ) :
  (((((1121718195763200)*A+((-1121718195763200)*X+(-1121718195763200)))*B+((7330395024842400)*A+(((1121718195763200)*X)*Y+((-9573831416368800)*X+(-1788572986250400)))))*B+((((-1121718195763200)*Y+(-9573831416368800))*Y+(-8452113220605600))*A+((((-1121718195763200)*X+(2500496811388800))*Y+(1067468431831200))*Y+(14116623186859200)))))*row0 u B A Y X+
  (((-1121718195763200)*B+((-1121718195763200)*Y+(-8452113220605600))))*row2 u B A Y X+
  (((-1121718195763200)*B+((1121718195763200)*Y+(8452113220605600))))*row5 u B A Y X+
  (((1121718195763200)*A+((-2243436391526400)*Y+(-22778557802118720))))*row6 u B A Y X+
  ((((1121718195763200)*B+((-1121718195763200)*Y+((-1121718195763200)*X+(14802006358258560))))*B+((3743734478359680)*Y+((1121718195763200)*X+(25737089543444160)))))*row7 u B A Y X+
  (((28042954894080)*B+(236846123209584)))*row8 u B A Y X+
  (((-340799799060)*Y+(-6071104991826)))*row9 u B A Y X+
  (((-51412083972480)*B+((-69411877441200)*A+((-2698578000720)*Y+((94206801597300)*X+(-745123289645196))))))*row10 u B A Y X+
  (((-208652938200)*Y+(-208652938200)))*row11 u B A Y X+
  ((((11684564539200)*Y)*B+((-255599849295000)*Y+(46738258156800))))*row12 u B A Y X+
  ((((1973744010000)*Y)*B+((-52432509625650)*Y+(-744101491770))))*row13 u B A Y X+
  (((30861271860935040)*Y))*row14 u B A Y X+
  ((((67881755894400)*X+(8272859539320))*Y))*row15 u B A Y X+
  ((((-18546927840)*Y)*B+((-500583054380)*Y)))*row16 u B A Y X+
  ((((3375540866880)*Y)*B+((97370004629380)*Y)))*row17 u B A Y X+
  (((158397525654375)*Y))*row18 u B A Y X+
  ((((-391107301200)*Y)*B+((6288234115800)*Y)))*row20 u B A Y X=(((6475)*Y))*row21 u B A Y X := by
  simp only [row0, row2, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row20, row21]
  ring
theorem zero21 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<21, row u B A Y X i=0) : row21 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h8 : row8 u B A Y X=0 := hs 8 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h11 : row11 u B A Y X=0 := hs 11 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have he := (relation21 u B A Y X).symm
  have hf : (((6475)*Y):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((6475)*Y))*row21 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h20, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero21

theorem relation22 (u B A Y X : ℂ) :
  ((((-6986286720)*X+(-61479323136))*B+(((-10479430080)*X+(-95945004288))*Y+((-122260017600)*X+(-821021761728)))))*row0 u B A Y X+
  ((-10479430080))*row6 u B A Y X+
  (((-10479430080)*A+((-37260195840)*X+(163013356800))))*row7 u B A Y X+
  ((38812704))*row9 u B A Y X+
  ((504565152))*row10 u B A Y X+
  ((-946059660))*row12 u B A Y X+
  (((-15734880)*A+(-159807375)))*row13 u B A Y X+
  (((208889972928)*A+(-757820817936)))*row14 u B A Y X+
  (((41585040)*A+((270302760)*X+(1773700968))))*row15 u B A Y X+
  (((115514)*A+(321789)))*row16 u B A Y X+
  (((4967102)*A+(-81090828)))*row17 u B A Y X+
  (((-30322425)*A+(-54060552)))*row18 u B A Y X+
  (((-6062931)*A))*row20 u B A Y X=(((18130)*A))*row22 u B A Y X := by
  simp only [row0, row6, row7, row9, row10, row12, row13, row14, row15, row16, row17, row18, row20, row22]
  ring
theorem zero22 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<22, row u B A Y X i=0) : row22 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have he := (relation22 u B A Y X).symm
  have hf : (((18130)*A):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((18130)*A))*row22 u B A Y X=0 := by
    simpa only [h0, h6, h7, h9, h10, h12, h13, h14, h15, h16, h17, h18, h20, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero22

theorem relation23 (u B A Y X : ℂ) :
  ((((123673908960)*A+((-123673908960)*X+(14721104160)))*B+(((-123673908960)*Y+(-123673908960))*A+(((242191272960)*Y+(262068922080))*Y+(212749064640)))))*row0 u B A Y X+
  ((-123673908960))*row2 u B A Y X+
  ((123673908960))*row5 u B A Y X+
  ((-1088030986560))*row6 u B A Y X+
  (((436809260160)*B+((-291926980800)*Y+((103796259840)*X+(1802628313920)))))*row7 u B A Y X+
  ((10920231504))*row8 u B A Y X+
  ((-563130750))*row9 u B A Y X+
  (((-1441614720)*A+((1441614720)*Y+((4002560100)*X+(-48932423484)))))*row10 u B A Y X+
  ((-339283350))*row13 u B A Y X+
  (((1998493852320)*Y))*row14 u B A Y X+
  (((1158440400)*Y+(1039626000)))*row15 u B A Y X+
  ((2887850))*row16 u B A Y X+
  (((144805050)*Y+(-438953200)))*row17 u B A Y X+
  (((38614680)*Y+(-758060625)))*row18 u B A Y X+
  (((-22943700)*Y+(-38947125)))*row20 u B A Y X+
  ((-453250))*row22 u B A Y X=(((310800)*Y))*row23 u B A Y X := by
  simp only [row0, row2, row5, row6, row7, row8, row9, row10, row13, row14, row15, row16, row17, row18, row20, row22, row23]
  ring
theorem zero23 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<23, row u B A Y X i=0) : row23 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h8 : row8 u B A Y X=0 := hs 8 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h22 : row22 u B A Y X=0 := hs 22 (by decide)
  have he := (relation23 u B A Y X).symm
  have hf : (((310800)*Y):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((310800)*Y))*row23 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, h7, h8, h9, h10, h13, h14, h15, h16, h17, h18, h20, h22, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero23

theorem relation24 (u B A Y X : ℂ) :
  ((((59296441216320)*A+((-59296441216320)*X+(703119856320)))*B+(((-59296441216320)*Y+(-59296441216320))*A+(((104999231877120)*Y+(119296002288960))*Y+(103592992164480)))))*row0 u B A Y X+
  ((-59296441216320))*row2 u B A Y X+
  ((59296441216320))*row5 u B A Y X+
  ((-231560806014720))*row6 u B A Y X+
  (((62812040497920)*B+((44999670804480)*X+(74061958199040))))*row7 u B A Y X+
  ((1570301012448))*row8 u B A Y X+
  ((-112303865940))*row9 u B A Y X+
  (((-624995427840)*A+((624995427840)*Y+((1025383123800)*X+(-6833934381288)))))*row10 u B A Y X+
  ((29692561500))*row13 u B A Y X+
  (((197107933055040)*Y))*row14 u B A Y X+
  (((-251114234400)*Y+(-41852372400)))*row15 u B A Y X+
  ((-116256590))*row16 u B A Y X+
  ((17671001680))*row17 u B A Y X+
  (((16740948960)*Y+(30517354875)))*row18 u B A Y X+
  (((2299065300)*Y+(1567899975)))*row20 u B A Y X+
  ((18246550))*row22 u B A Y X+
  (((95648700)*Y))*row23 u B A Y X=(((467831700)*Y))*row24 u B A Y X := by
  simp only [row0, row2, row5, row6, row7, row8, row9, row10, row13, row14, row15, row16, row17, row18, row20, row22, row23, row24]
  ring
theorem zero24 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<24, row u B A Y X i=0) : row24 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h8 : row8 u B A Y X=0 := hs 8 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h22 : row22 u B A Y X=0 := hs 22 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have he := (relation24 u B A Y X).symm
  have hf : (((467831700)*Y):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((467831700)*Y))*row24 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, h7, h8, h9, h10, h13, h14, h15, h16, h17, h18, h20, h22, h23, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero24

theorem relation25 (u B A Y X : ℂ) :
  ((-120353849280))*row7 u B A Y X+
  (((-120353849280)*X+(-120353849280)))*row14 u B A Y X+
  ((59699330))*row17 u B A Y X+
  ((-10440690))*row20 u B A Y X+
  (((63555)*X+(110390)))*row23 u B A Y X+
  (((-460941)*X+(-1826370)))*row24 u B A Y X=(((358195980)*X))*row25 u B A Y X := by
  simp only [row7, row14, row17, row20, row23, row24, row25]
  ring
theorem zero25 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<25, row u B A Y X i=0) : row25 u B A Y X=0 := by
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have he := (relation25 u B A Y X).symm
  have hf : (((358195980)*X):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((358195980)*X))*row25 u B A Y X=0 := by
    simpa only [h7, h14, h17, h20, h23, h24, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero25

theorem relation26 (u B A Y X : ℂ) :
  ((((-23925672940261921920)*A+((23925672940261921920)*X+(23925672940261921920)))*B+(((23925672940261921920)*Y+(23925672940261921920))*A+((-23925672940261921920)*Y+((4730509393913511936)*X+(70891831327633295616))))))*row0 u B A Y X+
  ((-11826273484783779840))*row1 u B A Y X+
  ((23925672940261921920))*row2 u B A Y X+
  ((-49276139519932416))*row3 u B A Y X+
  ((49276139519932416))*row4 u B A Y X+
  ((-38117201122002457728))*row5 u B A Y X+
  ((-3097264716930488832))*row6 u B A Y X+
  ((((-23652546969567559680)*X+(23652546969567559680))*X+(113136557504686934400)))*row7 u B A Y X+
  (((24638069759966208)*X))*row9 u B A Y X+
  (((1090058021763918480)*X))*row10 u B A Y X+
  ((467738355599358480))*row12 u B A Y X+
  ((82755509862048660))*row13 u B A Y X+
  (((20590386870828902400)*X+(262870779388186831680)))*row14 u B A Y X+
  (((105591727542712320)*X+(9942642108257040)))*row15 u B A Y X+
  (((-195540236190208)*X+(27618450300714)))*row16 u B A Y X+
  (((29722115900911616)*X+(-123923383476371388)))*row17 u B A Y X+
  (((51329311999929600)*X+(-32513488953902775)))*row18 u B A Y X+
  (((1652023237268040)*X+(18051006086400105)))*row20 u B A Y X+
  (((30690171599360)*X+(-19440053186190)))*row22 u B A Y X+
  (((92402121493890)*X+(-247135005996060)))*row23 u B A Y X+
  (((-975876231454350)*X+(3729926300979060)))*row24 u B A Y X+
  (((244335977159768440)*X))*row25 u B A Y X=(((61848505880)*X))*row26 u B A Y X := by
  simp only [row0, row1, row2, row3, row4, row5, row6, row7, row9, row10, row12, row13, row14, row15, row16, row17, row18, row20, row22, row23, row24, row25, row26]
  ring
theorem zero26 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<26, row u B A Y X i=0) : row26 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h1 : row1 u B A Y X=0 := hs 1 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h3 : row3 u B A Y X=0 := hs 3 (by decide)
  have h4 : row4 u B A Y X=0 := hs 4 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h22 : row22 u B A Y X=0 := hs 22 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have h25 : row25 u B A Y X=0 := hs 25 (by decide)
  have he := (relation26 u B A Y X).symm
  have hf : (((61848505880)*X):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((61848505880)*X))*row26 u B A Y X=0 := by
    simpa only [h0, h1, h2, h3, h4, h5, h6, h7, h9, h10, h12, h13, h14, h15, h16, h17, h18, h20, h22, h23, h24, h25, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero26

theorem relation27 (u B A Y X : ℂ) :
  ((44530924233600))*row0 u B A Y X+
  ((31171646963520))*row6 u B A Y X+
  ((-31171646963520))*row7 u B A Y X+
  (((-185545517640)*X))*row10 u B A Y X+
  ((649409311740))*row12 u B A Y X+
  ((109697518875))*row13 u B A Y X+
  (((-13359277270080)*X+(98339124349200)))*row14 u B A Y X+
  ((-79519507560))*row15 u B A Y X+
  ((-220887521))*row16 u B A Y X+
  ((9277275882))*row17 u B A Y X+
  ((1456074690))*row20 u B A Y X+
  (((-25866885)*X+(-104029940)))*row23 u B A Y X+
  (((187602987)*X+(897543780)))*row24 u B A Y X+
  (((145785763860)*X))*row25 u B A Y X=(((185545517640)*X))*row27 u B A Y X := by
  simp only [row0, row6, row7, row10, row12, row13, row14, row15, row16, row17, row20, row23, row24, row25, row27]
  ring
theorem zero27 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<27, row u B A Y X i=0) : row27 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have h25 : row25 u B A Y X=0 := hs 25 (by decide)
  have he := (relation27 u B A Y X).symm
  have hf : (((185545517640)*X):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((185545517640)*X))*row27 u B A Y X=0 := by
    simpa only [h0, h6, h7, h10, h12, h13, h14, h15, h16, h17, h20, h23, h24, h25, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero27

theorem relation28 (u B A Y X : ℂ) :
  (((((1870298817811200)*X)*Y+((2805448226716800)*X+(1736706045110400)))*u+((935149408905600)*A+((-3460052812950720)*Y+(-3460052812950720)))))*row0 u B A Y X+
  (((1870298817811200)*u))*row6 u B A Y X+
  ((((1870298817811200)*A+(-4675747044528000))*u))*row7 u B A Y X+
  ((-20595552458040))*row10 u B A Y X+
  (((38964558704400)*u))*row12 u B A Y X+
  (((6581851132500)*u))*row13 u B A Y X+
  ((((1870298817811200)*A+(3094899234235200))*u+((4395202221856320)*A+(-4942932589929600))))*row14 u B A Y X+
  ((((-11132731058400)*X+(-4771170453600))*u+(20595552458040)))*row15 u B A Y X+
  (((-13253251260)*u))*row16 u B A Y X+
  ((((-927727588200)*A+(1948227935220))*u))*row17 u B A Y X+
  ((((162248322600)*A+(-156008002500))*u))*row20 u B A Y X+
  ((((-1715460600)*A+(-3668605500))*u+((-2320965045)*A+(-1044081540))))*row23 u B A Y X+
  ((((28381789800)*A+(11279942100))*u+((16833104379)*A+(7572338748))))*row24 u B A Y X+
  ((((4329395411600)*A)*u+((10916261287820)*A+(5884443559440))))*row25 u B A Y X+
  (((19482279352200)*A+(-20595552458040)))*row27 u B A Y X=(((2164697705800)*A))*row28 u B A Y X := by
  simp only [row0, row6, row7, row10, row12, row13, row14, row15, row16, row17, row20, row23, row24, row25, row27, row28]
  ring
theorem zero28 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<28, row u B A Y X i=0) : row28 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have h25 : row25 u B A Y X=0 := hs 25 (by decide)
  have h27 : row27 u B A Y X=0 := hs 27 (by decide)
  have he := (relation28 u B A Y X).symm
  have hf : (((2164697705800)*A):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((2164697705800)*A))*row28 u B A Y X=0 := by
    simpa only [h0, h6, h7, h10, h12, h13, h14, h15, h16, h17, h20, h23, h24, h25, h27, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero28

theorem relation29 (u B A Y X : ℂ) :
  (((((2022915201344593920)*X)*Y+((2022915201344593920)*X+(2889878859063705600)))*B+((1011457600672296960)*Y+(20752942556651235840))))*row0 u B A Y X+
  (((2022915201344593920)*B+(-2022915201344593920)))*row6 u B A Y X+
  ((((2022915201344593920)*A+(-5057288003361484800))*B+(5057288003361484800)))*row7 u B A Y X+
  (((-2107203334733952)*A))*row9 u B A Y X+
  (((-67430506711486464)*A+((12041161912765440)*X)))*row10 u B A Y X+
  (((42144066694679040)*B+((-21072033347339520)*A+(-42144066694679040))))*row12 u B A Y X+
  (((7118930184912000)*B+((-4413736714645440)*A+(-7118930184912000))))*row13 u B A Y X+
  (((3347443011748792320)*B+((11041745474005908480)*A+((2889878859063705600)*X+(11824420998335662080)))))*row14 u B A Y X+
  ((((-12041161912765440)*X+(-5160497962613760))*B+((-1753246102682880)*A+(5160497962613760))))*row15 u B A Y X+
  (((-14334716562816)*B+(31058552552768)))*row16 u B A Y X+
  ((((-1003430159397120)*A+(2107203334733952))*B+((-1602547800355840)*A+(-4147511325508096))))*row17 u B A Y X+
  (((1881431548869600)*A+(-2132289088718880)))*row18 u B A Y X+
  ((((175487785724160)*A+(-168738255504000))*B+((514905095714880)*A+(260419374327840))))*row20 u B A Y X+
  (((1124921703360)*A+(-2624817307840)))*row22 u B A Y X+
  ((((-787205677440)*A+(-3967963708800))*B+((-11855262507400)*A+((610420861440)*X+(2801725683120)))))*row23 u B A Y X+
  ((((11575301232768)*A+(12200385375360))*B+((125600967700568)*A+((-4427157616128)*X+(27424161181872)))))*row24 u B A Y X+
  (((-20780249767599360)*A+((-3440331975075840)*X+(18061742869148160))))*row25 u B A Y X+
  (((1057934969)*A))*row26 u B A Y X+
  ((((8644936757882880)*A)*B+(((-879931062855936)*Y+(-16935968227159100))*A+((12041161912765440)*X+(-63216100042018560)))))*row27 u B A Y X=(((81379613)*A))*row29 u B A Y X := by
  simp only [row0, row6, row7, row9, row10, row12, row13, row14, row15, row16, row17, row18, row20, row22, row23, row24, row25, row26, row27, row29]
  ring
theorem zero29 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<29, row u B A Y X i=0) : row29 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h22 : row22 u B A Y X=0 := hs 22 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have h25 : row25 u B A Y X=0 := hs 25 (by decide)
  have h26 : row26 u B A Y X=0 := hs 26 (by decide)
  have h27 : row27 u B A Y X=0 := hs 27 (by decide)
  have he := (relation29 u B A Y X).symm
  have hf : (((81379613)*A):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((81379613)*A))*row29 u B A Y X=0 := by
    simpa only [h0, h6, h7, h9, h10, h12, h13, h14, h15, h16, h17, h18, h20, h22, h23, h24, h25, h26, h27, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero29

theorem relation30 (u B A Y X : ℂ) :
  ((((-1870298817811200)*X+(4052314105257600))*Y+((-935149408905600)*X+(19825167468798720))))*row0 u B A Y X+
  ((-1246865878540800))*row6 u B A Y X+
  (((-1870298817811200)*A+((-997492702832640)*X+(3117164696352000))))*row7 u B A Y X+
  ((1039054898784))*row9 u B A Y X+
  (((-3710910352800)*X+(54030854736768)))*row10 u B A Y X+
  ((-45458651821800))*row12 u B A Y X+
  (((-421238472480)*A+(-7678826321250)))*row13 u B A Y X+
  (((-2618418344935680)*A+((44530924233600)*X+(10697070182981280))))*row14 u B A Y X+
  (((16699096587600)*X+(-1484364141120)))*row15 u B A Y X+
  ((12369701176))*row16 u B A Y X+
  (((1391591382300)*A+(-983391243492)))*row17 u B A Y X+
  ((3038307851355))*row18 u B A Y X+
  (((-220075288860)*A+(479776610355)))*row20 u B A Y X+
  ((485358230))*row22 u B A Y X+
  (((-1242158820)*A+((-681945150)*X+(3730314840))))*row23 u B A Y X+
  (((-30841544916)*A+((4945896930)*X+(15983903208))))*row24 u B A Y X+
  (((20781097975680)*A+((3843442865400)*X+(17812369693440))))*row25 u B A Y X+
  (((-3710910352800)*X+(-62343293927040)))*row27 u B A Y X=(((10390548987840)*A))*row30 u B A Y X := by
  simp only [row0, row6, row7, row9, row10, row12, row13, row14, row15, row16, row17, row18, row20, row22, row23, row24, row25, row27, row30]
  ring
theorem zero30 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<30, row u B A Y X i=0) : row30 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h22 : row22 u B A Y X=0 := hs 22 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have h25 : row25 u B A Y X=0 := hs 25 (by decide)
  have h27 : row27 u B A Y X=0 := hs 27 (by decide)
  have he := (relation30 u B A Y X).symm
  have hf : (((10390548987840)*A):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((10390548987840)*A))*row30 u B A Y X=0 := by
    simpa only [h0, h6, h7, h9, h10, h12, h13, h14, h15, h16, h17, h18, h20, h22, h23, h24, h25, h27, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero30

theorem relation31 (u B A Y X : ℂ) :
  ((((2022915201344593920)*Y)*B+(-49308558032774476800)))*row0 u B A Y X+
  (((2107203334733952)*A))*row9 u B A Y X+
  (((12041161912765440)*B+((67430506711486464)*A)))*row10 u B A Y X+
  (((21072033347339520)*A))*row12 u B A Y X+
  (((4413736714645440)*A))*row13 u B A Y X+
  (((2889878859063705600)*B+((-12053203074678205440)*A+(-32366643221513502720))))*row14 u B A Y X+
  (((-12041161912765440)*B+((9493993046603520)*A+(12041161912765440))))*row15 u B A Y X+
  (((16723835989952)*A))*row16 u B A Y X+
  (((-1512863932629504)*A))*row17 u B A Y X+
  (((-6271438496232000)*A+(-4515435717287040)))*row18 u B A Y X+
  (((-771306892530720)*A+(-809943626419200)))*row20 u B A Y X+
  (((-3749739011200)*A))*row22 u B A Y X+
  (((610420861440)*B+((32575811599240)*A+(4187918236320))))*row23 u B A Y X+
  ((((11374916786688)*A+(-4427157616128))*B+((-153786759682136)*A+(-109946836962144))))*row24 u B A Y X+
  (((-3440331975075840)*B+((-70337089615018240)*A+(-36123485738296320))))*row25 u B A Y X+
  (((-1057934969)*A))*row26 u B A Y X+
  ((((-8644936757882880)*A+(12041161912765440))*B+(((-324185128420608)*Y+(-1897643995371460))*A+(126432200084037120))))*row27 u B A Y X+
  (((81379613)*A))*row29 u B A Y X+
  (((-79180931167811200)*A))*row30 u B A Y X=(((19296733834560)*A))*row31 u B A Y X := by
  simp only [row0, row9, row10, row12, row13, row14, row15, row16, row17, row18, row20, row22, row23, row24, row25, row26, row27, row29, row30, row31]
  ring
theorem zero31 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<31, row u B A Y X i=0) : row31 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h22 : row22 u B A Y X=0 := hs 22 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have h25 : row25 u B A Y X=0 := hs 25 (by decide)
  have h26 : row26 u B A Y X=0 := hs 26 (by decide)
  have h27 : row27 u B A Y X=0 := hs 27 (by decide)
  have h29 : row29 u B A Y X=0 := hs 29 (by decide)
  have h30 : row30 u B A Y X=0 := hs 30 (by decide)
  have he := (relation31 u B A Y X).symm
  have hf : (((19296733834560)*A):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((19296733834560)*A))*row31 u B A Y X=0 := by
    simpa only [h0, h9, h10, h12, h13, h14, h15, h16, h17, h18, h20, h22, h23, h24, h25, h26, h27, h29, h30, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero31

theorem relation32 (u B A Y X : ℂ) :
  ((((16428300426720)*Y+(16428300426720))*Y))*row0 u B A Y X+
  (((-97787502540)*A+((97787502540)*Y)))*row10 u B A Y X+
  (((-7040700182880)*A+((23469000609600)*Y)))*row14 u B A Y X+
  (((-97787502540)*Y))*row15 u B A Y X+
  (((-219254490)*A))*row20 u B A Y X+
  (((39624975)*A+((4957290)*Y)))*row23 u B A Y X+
  (((-124172421)*A+((-35953398)*Y)))*row24 u B A Y X+
  (((-151755696860)*A+((-27939286440)*Y)))*row25 u B A Y X+
  (((-10029487440)*A+((97787502540)*Y)))*row27 u B A Y X+
  (((-143338091330)*A))*row30 u B A Y X=(((8775801510)*A))*row32 u B A Y X := by
  simp only [row0, row10, row14, row15, row20, row23, row24, row25, row27, row30, row32]
  ring
theorem zero32 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<32, row u B A Y X i=0) : row32 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have h25 : row25 u B A Y X=0 := hs 25 (by decide)
  have h27 : row27 u B A Y X=0 := hs 27 (by decide)
  have h30 : row30 u B A Y X=0 := hs 30 (by decide)
  have he := (relation32 u B A Y X).symm
  have hf : (((8775801510)*A):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((8775801510)*A))*row32 u B A Y X=0 := by
    simpa only [h0, h10, h14, h15, h20, h23, h24, h25, h27, h30, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero32

theorem relation33 (u B A Y X : ℂ) :
  ((((-67024560825811835359499813614387200)*X+(52157062502366328583951967059968000))*Y+((209464583067752581814194440691200000)*X+(-51010753436380255428260715036672000))))*row0 u B A Y X+
  (((6018122596426884067379073122304000)*B+(-72217471157122608808548877467648000)))*row6 u B A Y X+
  ((((-4513591947320163050534304841728000)*X+(-12036245192853768134758146244608000))*B+(((15045306491067210168447682805760000)*X+(-181572218830204127031429148041216000))*X+(144434942314245217617097754935296000))))*row7 u B A Y X+
  ((((6268877704611337570186534502400)*X)*Y+((33042209568055591776191525606400)*X+(12537755409222675140373069004800))))*row9 u B A Y X+
  ((((200604086547562802245969104076800)*X)*Y+((1995212803985844803020277935718400)*X+(711666878466353750824985631129600))))*row10 u B A Y X+
  ((((31344388523056687850932672512000)*X)*B+(((62688777046113375701865345024000)*X)*Y+(((-323892014738252441126304282624000)*X+(7178189514761886406237642116326400))*X+(-1379153095014494265441037590528000)))))*row12 u B A Y X+
  ((((5294660223489305380225113600000)*X)*B+(((-54711488976056155595659507200000)*X+(1409588005175203022723915444603520))*X+(-227882176018979703564888889344000))))*row13 u B A Y X+
  (((-52157062502366328583951967059968000)*A+((-117043905889586201788252457118812160)*X+(-146799204762841493500710962233344000))))*row14 u B A Y X+
  ((((391058561573373915092588580864000)*X+(-1828353706477641162603288335001600))*X+(-115798735202920050354570731520000)))*row15 u B A Y X+
  ((((-99505995311291072542643404800)*X)*B+((-8540620676050200062655686287360)*X+(511745118743782658790737510400))))*row16 u B A Y X+
  ((((15124911287316243026481797529600)*X+(5970359718677464352558604288000))*B+((976935508268877952597309842283520)*X+(-50765553168373619053458930892800))))*row17 u B A Y X+
  ((((17351357932406380774623443712000)*X+(1596212156583466932121467712771200))*X+(-11194424472520245661047383040000)))*row18 u B A Y X+
  (((2985179859338732176279302144000)*B+((-54945486006084450094455824269440)*X+(-2985179859338732176279302144000))))*row19 u B A Y X+
  ((((-1470836937420821515106225664000)*X+(-40159370305005365600169984000))*B+((89839127187166419763550190781440)*X+(-513539786574262752051990528000))))*row20 u B A Y X+
  (((-38054971439553942473600)*X))*row21 u B A Y X+
  ((((-3346614192083780466680832000)*X)*Y+(((6916335996973146297807052800)*X+(462401852421670459012761446400))*X+(-6693228384167560933361664000))))*row22 u B A Y X+
  ((((-107597214428246892831081600000)*X+(28293022183180974392549376000))*B+((27542468538966301129617408000)*A+(((114808753437102027719326310400)*X)*Y+((-3106331741850955256205143388240)*X+(208903229789261430862543104000))))))*row23 u B A Y X+
  ((((1137985610479501964662422420480)*X+(-141464157001572041342292787200))*B+((-199755377087871383982172569600)*A+((20109873279756539970084156298800)*X+(-1610272144686155047471325952000)))))*row24 u B A Y X+
  (((-155229352685614073166523711488000)*A+((15656219695580787555821478414859840)*X+(146385683753214121038769250304000))))*row25 u B A Y X+
  ((((-12589321269141076991731200)*X)*B+(((2775373097969737427722560)*X+(228564719211253996571243100))*X+(-6294660634570538495865600))))*row26 u B A Y X+
  ((((-386591138973928087381043698636800)*X+(-51436945268605846729735667712000))*B+(((-859252328382812184002166558013440)*X+(5235546214840237970705237606400))*Y+((1743259997631768894000344736119280)*X+(411226876980683451390857970816000)))))*row27 u B A Y X+
  ((((-1888398190371161548759680)*X)*Y+((79677889050196785838829097)*X+(484204664197733730451200))))*row29 u B A Y X+
  (((-71789830906151852071853365316274257)*X+(-76619616389694125857835421696000)))*row30 u B A Y X+
  ((((327221638427514873169077350400)*X)*Y+(((1613265705048228768638515814400)*X+(-21797826029335548497186368961760))*X)))*row31 u B A Y X+
  (((((21200204601049250691903553044480)*X)*Y+((-689027862893641501094281160295552)*X))*Y+((2144451616724438208423376719143085)*X)))*row32 u B A Y X=(((2067507196560)*X))*row33 u B A Y X := by
  simp only [row0, row6, row7, row9, row10, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23, row24, row25, row26, row27, row29, row30, row31, row32, row33]
  ring
theorem zero33 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<33, row u B A Y X i=0) : row33 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h19 : row19 u B A Y X=0 := hs 19 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h21 : row21 u B A Y X=0 := hs 21 (by decide)
  have h22 : row22 u B A Y X=0 := hs 22 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have h25 : row25 u B A Y X=0 := hs 25 (by decide)
  have h26 : row26 u B A Y X=0 := hs 26 (by decide)
  have h27 : row27 u B A Y X=0 := hs 27 (by decide)
  have h29 : row29 u B A Y X=0 := hs 29 (by decide)
  have h30 : row30 u B A Y X=0 := hs 30 (by decide)
  have h31 : row31 u B A Y X=0 := hs 31 (by decide)
  have h32 : row32 u B A Y X=0 := hs 32 (by decide)
  have he := (relation33 u B A Y X).symm
  have hf : (((2067507196560)*X):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((2067507196560)*X))*row33 u B A Y X=0 := by
    simpa only [h0, h6, h7, h9, h10, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h29, h30, h31, h32, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero33

theorem relation34 (u B A Y X : ℂ) :
  ((((1620925642103040)*A+((-1620925642103040)*X+(-1620925642103040)))*B+(((-1620925642103040)*Y+(-1620925642103040))*A+((1620925642103040)*Y+(65763268908180480)))))*row0 u B A Y X+
  ((-1620925642103040))*row2 u B A Y X+
  ((1620925642103040))*row5 u B A Y X+
  ((76183505178842880))*row6 u B A Y X+
  ((-100497389810388480))*row7 u B A Y X+
  (((-463121612029440)*X))*row10 u B A Y X+
  ((911770673682960))*row12 u B A Y X+
  ((154015316500500))*row13 u B A Y X+
  (((-57658640697665280)*X+(99165915175803840)))*row14 u B A Y X+
  ((-227425791621600))*row15 u B A Y X+
  ((-631738310060))*row16 u B A Y X+
  ((81207088220440))*row17 u B A Y X+
  ((84423210526200))*row18 u B A Y X+
  ((7236275187960))*row19 u B A Y X+
  (((-113573825820)*X+(5440727084520)))*row20 u B A Y X+
  ((50477255920))*row22 u B A Y X+
  (((2825733105)*X+(-53146209480)))*row23 u B A Y X+
  (((84557955957)*X+(493843142520)))*row24 u B A Y X+
  (((20498361948800)*X+(-67538568420960)))*row25 u B A Y X+
  (((-281287004742240)*X))*row27 u B A Y X+
  (((-170361709446460)*X+(-67538568420960)))*row30 u B A Y X+
  (((-18183460728720)*X))*row32 u B A Y X=(((151961778947160)*X))*row34 u B A Y X := by
  simp only [row0, row2, row5, row6, row7, row10, row12, row13, row14, row15, row16, row17, row18, row19, row20, row22, row23, row24, row25, row27, row30, row32, row34]
  ring
theorem zero34 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<34, row u B A Y X i=0) : row34 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h19 : row19 u B A Y X=0 := hs 19 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h22 : row22 u B A Y X=0 := hs 22 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have h25 : row25 u B A Y X=0 := hs 25 (by decide)
  have h27 : row27 u B A Y X=0 := hs 27 (by decide)
  have h30 : row30 u B A Y X=0 := hs 30 (by decide)
  have h32 : row32 u B A Y X=0 := hs 32 (by decide)
  have he := (relation34 u B A Y X).symm
  have hf : (((151961778947160)*X):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((151961778947160)*X))*row34 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, h7, h10, h12, h13, h14, h15, h16, h17, h18, h19, h20, h22, h23, h24, h25, h27, h30, h32, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero34

theorem relation35 (u B A Y X : ℂ) :
  (((-133158282500332821251520)*Y+((-651095486704770999091200)*X+(400136961123237459401280))))*row0 u B A Y X+
  ((372054563831297713766400))*row6 u B A Y X+
  ((-744109127662595427532800))*row7 u B A Y X+
  (((-2214610498995819724800)*X+(245489846997547512360)))*row10 u B A Y X+
  ((7751136746485369036800))*row12 u B A Y X+
  ((1309313639609015040000))*row13 u B A Y X+
  (((186027281915648856883200)*u+((133158282500332821251520)*A+((-174400576795920803328000)*Y+((-1372857181150226791219200)*X+(687994710984550886716800))))))*row14 u B A Y X+
  ((-156509960877179755560))*row15 u B A Y X+
  ((-2636441070233118720))*row16 u B A Y X+
  ((295281399866109296640))*row17 u B A Y X+
  (((69206578093619366400)*u))*row18 u B A Y X+
  (((12103392581395315200)*u+(-12568907680679750400)))*row20 u B A Y X+
  (((117617725582156800)*u+((-70316609688319995)*A+((92095339904568000)*Y+((332021641006598400)*X+(-1362193118265519540))))))*row23 u B A Y X+
  (((1643613889895577600)*u+((509980463950026069)*A+((-667933570465761600)*Y+((-3477841562246388480)*X+(6683324746373903628))))))*row24 u B A Y X+
  ((((861237416276152115200)*X+(-133681082471435699200))*u+((396304412203371491820)*A+((-519049335702145248000)*Y+((-330231144309968844800)*X+(1838660278827035103440))))))*row25 u B A Y X+
  (((-993735480318637056000)*u+(((-1726389548080832194560)*X)*Y+((3795230667203937561600)*X+(-648872085289225838040)))))*row27 u B A Y X+
  (((-430618708138076057600)*X+(-4140564501327654400)))*row28 u B A Y X+
  (((1897978305165396854400)*X+(1521657454237912992000)))*row30 u B A Y X+
  (((-19153730193204499200)*X))*row31 u B A Y X+
  ((((-70464879513503354880)*X+(99373548031863705600))*u+((-315727387793290045440)*X+(93162701279872224000))))*row32 u B A Y X+
  ((((493254156594523484160)*X)*u+((83856558425142587710080)*X)))*row34 u B A Y X=(((25664655999964800)*X))*row35 u B A Y X := by
  simp only [row0, row6, row7, row10, row12, row13, row14, row15, row16, row17, row18, row20, row23, row24, row25, row27, row28, row30, row31, row32, row34, row35]
  ring
theorem zero35 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<35, row u B A Y X i=0) : row35 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have h25 : row25 u B A Y X=0 := hs 25 (by decide)
  have h27 : row27 u B A Y X=0 := hs 27 (by decide)
  have h28 : row28 u B A Y X=0 := hs 28 (by decide)
  have h30 : row30 u B A Y X=0 := hs 30 (by decide)
  have h31 : row31 u B A Y X=0 := hs 31 (by decide)
  have h32 : row32 u B A Y X=0 := hs 32 (by decide)
  have h34 : row34 u B A Y X=0 := hs 34 (by decide)
  have he := (relation35 u B A Y X).symm
  have hf : (((25664655999964800)*X):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((25664655999964800)*X))*row35 u B A Y X=0 := by
    simpa only [h0, h6, h7, h10, h12, h13, h14, h15, h16, h17, h18, h20, h23, h24, h25, h27, h28, h30, h31, h32, h34, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero35

theorem relation36 (u B A Y X : ℂ) :
  ((((-8915091031566720)*A+((8915091031566720)*X+(8915091031566720)))*B+(((8915091031566720)*Y+(8915091031566720))*A+((17830182063133440)*Y+(-449575304877578880)))))*row0 u B A Y X+
  ((8915091031566720))*row2 u B A Y X+
  ((-8915091031566720))*row5 u B A Y X+
  ((-499245097767736320))*row6 u B A Y X+
  ((739952555620037760))*row7 u B A Y X+
  (((3024763028567280)*X+(-159198054135120)))*row10 u B A Y X+
  ((-6686318273675040))*row12 u B A Y X+
  ((-1129445654337000))*row13 u B A Y X+
  (((-26745273094700160)*A+((53490546189400320)*Y+((458490395909145600)*X+(-596037514681889280)))))*row14 u B A Y X+
  ((1137128958108000))*row15 u B A Y X+
  ((3600908367342))*row16 u B A Y X+
  ((-469634259698604))*row17 u B A Y X+
  ((-328345986653685))*row18 u B A Y X+
  ((-53066018045040))*row19 u B A Y X+
  ((-17802697197285))*row20 u B A Y X+
  ((-208218680670))*row22 u B A Y X+
  (((14123319210)*A+((-28246638420)*Y+((96845617440)*X+(503409020400)))))*row23 u B A Y X+
  (((-102431230902)*A+((204862461804)*Y+((-852775108152)*X+(-2664741144780)))))*row24 u B A Y X+
  (((-79599027067560)*A+((159198054135120)*Y+((-293418147395560)*X+(-82757718617860)))))*row25 u B A Y X+
  (((2024672688487680)*X+(-159198054135120)))*row27 u B A Y X+
  (((952466990552000)*X+(30955177192940)))*row30 u B A Y X+
  (((79747463481672)*X))*row32 u B A Y X+
  (((1256217372629856)*X))*row34 u B A Y X=(((101307852631440)*X))*row36 u B A Y X := by
  simp only [row0, row2, row5, row6, row7, row10, row12, row13, row14, row15, row16, row17, row18, row19, row20, row22, row23, row24, row25, row27, row30, row32, row34, row36]
  ring
theorem zero36 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<36, row u B A Y X i=0) : row36 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h19 : row19 u B A Y X=0 := hs 19 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h22 : row22 u B A Y X=0 := hs 22 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have h25 : row25 u B A Y X=0 := hs 25 (by decide)
  have h27 : row27 u B A Y X=0 := hs 27 (by decide)
  have h30 : row30 u B A Y X=0 := hs 30 (by decide)
  have h32 : row32 u B A Y X=0 := hs 32 (by decide)
  have h34 : row34 u B A Y X=0 := hs 34 (by decide)
  have he := (relation36 u B A Y X).symm
  have hf : (((101307852631440)*X):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((101307852631440)*X))*row36 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, h7, h10, h12, h13, h14, h15, h16, h17, h18, h19, h20, h22, h23, h24, h25, h27, h30, h32, h34, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero36

theorem relation37 (u B A Y X : ℂ) :
  (((((-28435629268117027218366120502886400000)*X+(317381303020089082290977098822766316134400))*Y+((-42653443902175540827549180754329600000)*X+(317834241972002660653098216313633720934400)))*u+(((-16258240444196999728887326118433692057600)*A+((-48340569755798946271222404854906880000)*Y+((16229804814928882701668959997930805657600)*X+(133157552064508300062807620389329680793600))))*B+(((13236480907305096969815619712993630617600)*Y+(12856662144938105249113157960562219417600))*A+(((139334583413773433369993990464143360000)*Y+((-32858949376490787007889739247779840000)*X+(2675731386137793033767680516012486681374720)))*Y+((1014425276568259325444534478873526272000)*X+(2405365939329227723075429956553844875550720)))))))*row0 u B A Y X+
  ((16258240444196999728887326118433692057600))*row2 u B A Y X+
  ((-16258240444196999728887326118433692057600))*row5 u B A Y X+
  (((298574107315228785792844265280307200000)*u+((-758283447149787392489763213410304000000)*B+((-255920663413053244965295084525977600000)*A+(306944662805330336758311194521759879987200)))))*row6 u B A Y X+
  ((((-28435629268117027218366120502886400000)*A+(-582930399996399057976505470309171200000))*u+((-29002838977813975059109716673908660633600)*B+((540276956094223517148956289554841600000)*A+((42653443902175540827549180754329600000)*X+(-497043515459070758932942113564113431756800))))))*row7 u B A Y X+
  ((-763139173128041046666330560670955683840))*row8 u B A Y X+
  (((-434433224929565693613926841016320000)*u+((17772268292573142011478825314304000)*Y+(15712488178223475066474186852499307520))))*row9 u B A Y X+
  ((((-1946486527281820315542918962995200000)*X+(1874723405853955434460450636514867020800))*u+(((4513591947320163050534304841728000000)*X+(-287741486641660394471561933660160000))*B+(((1523337282220555029555327884083200000)*X+(-1973200565592383273873650101781262499840))*A+((63661675521480532236070444246099968000)*Y+((-1730107063880150119060747037397757747200)*X+(16027644525938546128513069926249714286080)))))))*row10 u B A Y X+
  (((2468370596190714168260947960320000000)*u+((-15708710474157704966812672819476480000)*B+((-5331680487771942603443647594291200000)*A+((177722682925731420114788253143040000)*Y+((-918233861782945670593072641239040000)*X+(4439825640342306928725385938188149324800)))))))*row12 u B A Y X+
  (((240832914925634544524919517209600000)*u+((-2653498390905017730880519057344000000)*B+((-912629993402404589778642381004800000)*A+((-155107071247119201113694702912000000)*X+(745581161435548657919970734588614089600))))))*row13 u B A Y X+
  ((((-417055895932383065869369767375667200000)*B+((-317381303020089082290977098822766316134400)*A+((35386560866990078316188949959147520000)*Y+((-467156766547636875730300551118848000000)*X+(456509255117382552111086681108001626112000)))))*u+(((48340569755798946271222404854906880000)*A+((17061377560870216331019672301731840000)*Y+((1083262067356839132128233162014720000000)*X+(-17482822022252978791423076573705119334400))))*B+(((3021759536891902759071706405440061440000)*A+((328336600899214713818331516703347895173120)*Y+((426895526377541021319534551930634240000)*X+(-2837662628262273688244701797949404932812800))))*A+(((-10460283189854082770836130477990952960000)*Y+((-61294578644607814226255859750666240000)*X+(308545985292606659646241963050025889464320)))*Y+((-312980572038317492936887457336915263488000)*X+(4059171679411891720665369685291255510763520)))))))*row14 u B A Y X+
  (((-1891409828750447309590802525424916300800)*u+((2222138035493158844700549722972160000)*B+((18808782443332736597726524604743680000)*A+((-182529175646044138690614383436323635200)*Y+((1981278798542413239057454229483520000)*X+(-17372779187804433146079856291570394826240)))))))*row15 u B A Y X+
  (((-5294962775502076197675412177920000)*u+((5091224250102207726644349806592000)*B+((1970218707163563236344339415040000)*A+(-1832760755313225215609031181197396480)))))*row16 u B A Y X+
  (((476794649352731921694662607267840000)*u+((-568336452700063864113111217987584000)*B+((-226933372906930420040752548986880000)*A+(207328356203165926627097129790753653760)))))*row17 u B A Y X+
  (((1169537496766552665437925343104000000)*u+((-31736193379594896449069330918400000)*B+((-41139509936511902804349132672000000)*A+((10578731126531632149689776972800000)*Y+((49191099738372089496057462923520000)*X+(84688980299899849470844303693260624000)))))))*row18 u B A Y X+
  ((-119285584586411431359296630999894400))*row19 u B A Y X+
  (((130400375350265793164287104168960000)*u+((21886430122918433570083139473920000)*B+((-1617915029248674466616306151021911040)*A+((447003551094082114543502857884518400)*Y+((1104362603702495051321874475008000)*X+(-4385366517124785482709202407512528640)))))))*row20 u B A Y X+
  ((-107885844031135426912656000))*row21 u B A Y X+
  (((699275035435905928512959846400000)*u+((-24597614311815786430104115200000)*A+((-9487651234557517623040158720000)*Y+((19607812551418869754282994688000)*X+(49231896240731084941169883072499200))))))*row22 u B A Y X+
  ((((220233815740426692494133043200000)*B+((167568834576168956493830248668086400)*A+((-18686505577975598151017349120000)*Y+((-98676190169411959623994675200000)*X+(90387489445569140208947964135820800)))))*u+(((-25527101369913093902729057280000)*A+((-9009565189381091965669079040000)*Y+((228814354016027732461436928000000)*X+(9807233221968238420191722140646400))))*B+(((-1595694101319273399252945776640000)*A+((-173384007200318696252371825627422720)*Y+((44857147318558770051294197760000)*X+(1761887094443758251237537328358819520))))*A+(((5523739391039576981118474389760000)*Y+((32367697161850589654440765440000)*X+(-203090615842062446056032735334993920)))*Y+((-67305563314414176454342777660723200)*X+(896532285303085912686950516565290640)))))))*row23 u B A Y X+
  ((((-3942393349892663839753950289920000)*B+((-1215315021294530642360516224550647680)*A+((135526340455001969747904774144000)*Y+((715662052912893054536129802240000)*X+(-663721278307535238281573809341288960)))))*u+(((185138661514422333673477057536000)*A+((65343057005090235414168373248000)*Y+((-1659506209653085343851895193600000)*X+(-154576836423374529976946370483287040))))*B+(((11572981429568203916687154106368000)*A+((1257490325905469281240886187971518464)*Y+((-325332363184073605950965286912000)*X+(-11436053467157435595576999019969730880))))*A+(((-40061646741329142526217145837312000)*Y+((-234750982573842697599049340928000)*X+(1402220724021765696651162628139495424)))*Y+((486906773358838504398769946619555840)*X+(-4497260984353865372323607173950684144)))))))*row24 u B A Y X+
  ((((-1203624519285376813475814624460800000)*B+((-944483774887186657843714240105610150400)*A+((105317145437470471179133779640320000)*Y+((556139007794805804440833989427200000)*X+(-533452314071821459134046429523824588800)))))*u+(((143870743320830197235780966830080000)*A+((50777909407351834318510929469440000)*Y+((-1289597699234332300152658526208000000)*X+(-46652324720011822097975229319889510400))))*B+(((8993331955035424878189602397143040000)*A+((977192264580996172078367609236154449920)*Y+((-252814882287397228009094098575360000)*X+(-9394875643095782474979372649869825857280))))*A+(((-31131795207899055865583721660687360000)*Y+((-182424341204189923292428154019840000)*X+(994309184058820428874062569920570552320)))*Y+((378880343614553884326512332032865075200)*X+(-7638187569588273918735751111153941396800)))))))*row25 u B A Y X+
  (((218109990987869158881743040000)*u+((-35690725798014953271557952000)*B+((7868182732744205607593457600)*X+(9008515321316325561712017632580)))))*row26 u B A Y X+
  ((((1782290153557192589185340886220800000)*B+((32983941153493499215442996920320000)*Y+((-1946486527281820315542918962995200000)*X+(1888676050029901209242811643210474060800))))*u+(((4513591947320163050534304841728000000)*X+(65464156846902220604160930353740953600))*B+(((-78987859078102853384350334730240000)*Y+((1523337282220555029555327884083200000)*X+(-192206665062798188054006717004266864640)))*A+((-80363934259707012945954123259769149440)*Y+((-1310205959440557889993428484006495027200)*X+(17264340182771601726284052251188103425680)))))))*row27 u B A Y X+
  (((65823215898419044486958612275200000)*B+((32911607949209522243479306137600000)*A+(-49367411923814283365218959206400000))))*row28 u B A Y X+
  (((-16777691614451473760134080000)*u+((-5353608869702242990733692800)*Y+(-398928274570819352630675184165))))*row29 u B A Y X+
  (((20437738833414995208677279136337920000)*u+((-191984379703722213086962619136000000)*B+((-1186851507001539471031367640696036833280)*A+((19077560104178046800325121396721049600)*Y+((638485194214664731523498539069440000)*X+(-2088142968165323234364839205328918307075)))))))*row30 u B A Y X+
  (((3435827203488906168275312179200000)*u+((-1265831074969597009364588697600000)*A+((927673344942004665434334288384000)*Y+((4573608273811728559090192333824000)*X+(86178484343593308844075562493429600))))))*row31 u B A Y X+
  (((-18903077386212648673177857884160000)*u+((-167864333884762720807737159512874946560)*A+(((60102580043974625711546572881100800)*Y+(3682972036213650947995417004365630080))*Y+(-162967301171793872834425014517139436585)))))*row32 u B A Y X+
  ((-5861382902247600))*row33 u B A Y X+
  (((-1400774622095394208346498651453904967680)*A+((47103916087107398472923669926786560000)*Y+(-1433110309318439786657064733766746951680))))*row34 u B A Y X+
  (((125662503078799994020557350707200000)*A))*row36 u B A Y X=(((12466518162579364486166403840000)*A))*row37 u B A Y X := by
  simp only [row0, row2, row5, row6, row7, row8, row9, row10, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23, row24, row25, row26, row27, row28, row29, row30, row31, row32, row33, row34, row36, row37]
  ring
theorem zero37 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<37, row u B A Y X i=0) : row37 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h8 : row8 u B A Y X=0 := hs 8 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h19 : row19 u B A Y X=0 := hs 19 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h21 : row21 u B A Y X=0 := hs 21 (by decide)
  have h22 : row22 u B A Y X=0 := hs 22 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have h25 : row25 u B A Y X=0 := hs 25 (by decide)
  have h26 : row26 u B A Y X=0 := hs 26 (by decide)
  have h27 : row27 u B A Y X=0 := hs 27 (by decide)
  have h28 : row28 u B A Y X=0 := hs 28 (by decide)
  have h29 : row29 u B A Y X=0 := hs 29 (by decide)
  have h30 : row30 u B A Y X=0 := hs 30 (by decide)
  have h31 : row31 u B A Y X=0 := hs 31 (by decide)
  have h32 : row32 u B A Y X=0 := hs 32 (by decide)
  have h33 : row33 u B A Y X=0 := hs 33 (by decide)
  have h34 : row34 u B A Y X=0 := hs 34 (by decide)
  have h36 : row36 u B A Y X=0 := hs 36 (by decide)
  have he := (relation37 u B A Y X).symm
  have hf : (((12466518162579364486166403840000)*A):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((12466518162579364486166403840000)*A))*row37 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, h7, h8, h9, h10, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h36, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero37

theorem relation38 (u B A Y X : ℂ) :
  ((((970467467813844584917132800)*Y+(970467467813844584917132800))*u+(((-29923968058601902200115200)*A+((-1997679334207820110848000)*Y+((29923968058601902200115200)*X+(376600605533111382706483200))))*B+(((29923968058601902200115200)*Y+(29923968058601902200115200))*A+(((-1065428978244170725785600)*Y+(7606482028956969816754736640))*Y+(6487606408493900106963786240))))))*row0 u B A Y X+
  ((29923968058601902200115200))*row2 u B A Y X+
  ((-29923968058601902200115200))*row5 u B A Y X+
  ((544526164550536362754560000))*row6 u B A Y X+
  (((-55180342498229342172979200)*B+(-892655083191819147405004800)))*row7 u B A Y X+
  ((-1379508562455733554324480))*row8 u B A Y X+
  (((-2080915973133145948800)*A+(34926357936364897242240)))*row9 u B A Y X+
  (((5776592070320503481649600)*u+((-11890948417903691136000)*B+((-5852949418095646069082880)*A+((27745546308441945984000)*Y+((-3063108312451990836633600)*X+(43458866981125755137138160)))))))*row10 u B A Y X+
  (((-20809159731331459488000)*A+(8088421296331722438892800)))*row12 u B A Y X+
  (((-4358675349130238136000)*A+(1360574905241757490084800)))*row13 u B A Y X+
  ((((-970467467813844584917132800)*A+(1386382096876920835595904000))*u+((-24504866499615926693068800)*B+(((973173926946748917710960640)*Y+(-8041187674661178133506009600))*A+(((-5726680758062417651097600)*Y+(922376589773801627246221440))*Y+((-568672717137826124888064000)*X+(10837850941308904150276679040)))))))*row14 u B A Y X+
  (((-5776592070320503481649600)*u+((11890948417903691136000)*B+((-9375555483347141088000)*A+((-322112580476102210995200)*Y+((-5945474208951845568000)*X+(-48674264625999320807378880)))))))*row15 u B A Y X+
  (((-16515206135977348800)*A+(-3153853865100474375840)))*row16 u B A Y X+
  (((998534770990630473600)*A+(354264891941811712942080)))*row17 u B A Y X+
  (((6193202300991505800000)*A+(105706166702113591614000)))*row18 u B A Y X+
  (((-4028672898407392915680)*A+((628762780692590544000)*Y+(-15391466178518283333480))))*row20 u B A Y X+
  (((3702961017035280000)*A+(63202491301712162400)))*row22 u B A Y X+
  ((((512472681895005631800)*A+(292841532511431789600))*u+((10830411972777196800)*B+(((-513901875985770111840)*Y+(5018720937924203349840))*A+(((3024076070320905600)*Y+(-532896360548083221690))*Y+((-120119114607165273600)*X+(3535364224103984337780)))))))*row23 u B A Y X+
  ((((-3716775556059567161160)*A+(-2123871746319752663520))*u+(((-11233014699774067200)*A+(-200293471013848692480))*B+(((3727140974254690600608)*Y+(-32379542441707428974160))*A+(((-21932509604748462720)*Y+(3854782864210149669798))*Y+((871179683835124984320)*X+(-17967897346967516213628)))))))*row24 u B A Y X+
  ((((-2888296035160251740824800)*A+(-1650454877234429566185600))*u+((-61040201878572281164800)*B+(((2896350973055800350330240)*Y+(-26834408174696048117489760))*A+(((-17043692732328623961600)*Y+(2783657321579145387416040))*Y+((676991329925983482009600)*X+(-22862970409074833908125200)))))))*row25 u B A Y X+
  (((1044737230261725)*A+(8536995652995810)))*row26 u B A Y X+
  (((5776592070320503481649600)*u+(((8537091171828291072000)*A+(80634858758673406387200))*B+(((320140918943560915200)*Y+(-572248120606596969838380))*A+((-99117661145681656558080)*Y+((-2369469654740942187033600)*X+(49183213993080490038213960)))))))*row27 u B A Y X+
  (((-80364402327825)*A+(-870997046181570)))*row29 u B A Y X+
  (((-3510395766386052565781760)*A+((-80794082284497188006400)*Y+(-7068120924785414541407360))))*row30 u B A Y X+
  (((19056007079973864000)*A+(206530819590573878400)))*row31 u B A Y X+
  (((-509923797231515021147520)*A+((2489984925116584896000)*Y+(-507641131397566151905920))))*row32 u B A Y X+
  (((-4242061616568969059717760)*A+((20809159731331459488000)*Y+(-4256880260620068735413760))))*row34 u B A Y X=(((315290298959567568000)*A))*row38 u B A Y X := by
  simp only [row0, row2, row5, row6, row7, row8, row9, row10, row12, row13, row14, row15, row16, row17, row18, row20, row22, row23, row24, row25, row26, row27, row29, row30, row31, row32, row34, row38]
  ring
theorem zero38 (u B A Y X : ℂ) (hA : A≠0) (hY : Y≠0) (hX : X≠0)
  (hs : ∀ i<38, row u B A Y X i=0) : row38 u B A Y X=0 := by
  have h0 : row0 u B A Y X=0 := hs 0 (by decide)
  have h2 : row2 u B A Y X=0 := hs 2 (by decide)
  have h5 : row5 u B A Y X=0 := hs 5 (by decide)
  have h6 : row6 u B A Y X=0 := hs 6 (by decide)
  have h7 : row7 u B A Y X=0 := hs 7 (by decide)
  have h8 : row8 u B A Y X=0 := hs 8 (by decide)
  have h9 : row9 u B A Y X=0 := hs 9 (by decide)
  have h10 : row10 u B A Y X=0 := hs 10 (by decide)
  have h12 : row12 u B A Y X=0 := hs 12 (by decide)
  have h13 : row13 u B A Y X=0 := hs 13 (by decide)
  have h14 : row14 u B A Y X=0 := hs 14 (by decide)
  have h15 : row15 u B A Y X=0 := hs 15 (by decide)
  have h16 : row16 u B A Y X=0 := hs 16 (by decide)
  have h17 : row17 u B A Y X=0 := hs 17 (by decide)
  have h18 : row18 u B A Y X=0 := hs 18 (by decide)
  have h20 : row20 u B A Y X=0 := hs 20 (by decide)
  have h22 : row22 u B A Y X=0 := hs 22 (by decide)
  have h23 : row23 u B A Y X=0 := hs 23 (by decide)
  have h24 : row24 u B A Y X=0 := hs 24 (by decide)
  have h25 : row25 u B A Y X=0 := hs 25 (by decide)
  have h26 : row26 u B A Y X=0 := hs 26 (by decide)
  have h27 : row27 u B A Y X=0 := hs 27 (by decide)
  have h29 : row29 u B A Y X=0 := hs 29 (by decide)
  have h30 : row30 u B A Y X=0 := hs 30 (by decide)
  have h31 : row31 u B A Y X=0 := hs 31 (by decide)
  have h32 : row32 u B A Y X=0 := hs 32 (by decide)
  have h34 : row34 u B A Y X=0 := hs 34 (by decide)
  have he := (relation38 u B A Y X).symm
  have hf : (((315290298959567568000)*A):ℂ)≠0 := by norm_num [mul_ne_zero_iff, hA, hY, hX]
  have hz : (((315290298959567568000)*A))*row38 u B A Y X=0 := by
    simpa only [h0, h2, h5, h6, h7, h8, h9, h10, h12, h13, h14, h15, h16, h17, h18, h20, h22, h23, h24, h25, h26, h27, h29, h30, h31, h32, h34, mul_zero, add_zero] using he
  exact (mul_eq_zero.mp hz).resolve_left hf
#print axioms zero38


}
end QuantitativeArithmeticSmallLevelTwentyFive.PositiveChart.CompactSource
end
