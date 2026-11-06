module
public import SmallLevelTwentySixFactorIndexPhysicalSeriesV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelTwentySixExceptionalCurve
open SmallLevelTwentySixPariFirstChart SmallLevelTwentySixPariFinalFactors
def extraFactor7 (x y : ℂ) : ℂ := (((((((125*x+-1625)*x+9025)*x+-26175)*x+38690)*x+9560)*x+-92336)*x+87360)

def linearCoeff (x y : ℂ) : ℂ := (((-1/2)*x+(3/2))*x+-1)

def quotient (x y : ℂ) : ℂ := (((((((((((((-611/437400)*x+((13/14580)*y+(871/145800)))*x+(((13/12150)*y+(-1183/36450))*y+(255229/1093500)))*x+(((-221/12150)*y+(16757/40500))*y+(-3429257/1093500)))*x+(((52/405)*y+(-255463/91125))*y+(211268473/10935000)))*x+(((-2951/6075)*y+(4244383/364500))*y+(-817004123/10935000)))*x+(((12701/12150)*y+(-1883479/60750))*y+(548989987/2733750)))*x+(((-4771/4050)*y+(18752123/364500))*y+(-528343933/1366875)))*x+(((1651/6075)*y+(-4134689/91125))*y+(288298361/546750)))*x+(((6058/6075)*y+(111059/30375))*y+(-24619478/50625)))*x+(((-884/675)*y+(2968888/91125))*y+(372219458/1366875)))*x+(((832/1215)*y+(-2582008/91125))*y+(-6557512/91125)))*x+(((-832/6075)*y+(15808/2025))*y+(5408/2025)))

def multiplier (x y : ℂ) : ℂ := (((13/656100000)*x+(-13/218700000))*x+(13/328050000))

def resultantMultiplier0 (x y : ℂ) : ℂ := (((((((((20375/4)*y+(-6549125/144))*y+(-6620725/144))*y+(865258675/1728))*y+(-192837445/1728))*y+(-2277595435/1728))*y+(932730823/576))*x+((((((((61125/8)*y+(-10044125/96))*y+(59420575/288))*y+(1296157675/1152))*y+(-10727411585/3456))*y+(-6786682355/3456))*y+(34833970817/3456))*y+(-5126420605/576)))*x+((((((((-314625/8)*y+(33875425/96))*y+(-3081625/24))*y+(-4442382335/1152))*y+(563371975/96))*y+(5024050637/576))*y+(-7212931295/288))*y+(32762650807/1920)))

def resultantMultiplier1 (x y : ℂ) : ℂ := (((((((((((((7640625/4)*y+(-818640625/48))*y+(-827590625/48))*y+(108157334375/576))*y+(-24104680625/576))*y+(-284699429375/576))*y+(116591352875/192))*x+(((((((-115734375/4)*y+(3834765625/16))*y+(13353521875/48))*y+(-499854959375/192))*y+(195718941875/576))*y+(436673058125/64))*y+(-524511132875/64)))*x+(((((((700434375/4)*y+(-65532509375/48))*y+(-29054558125/16))*y+(8519096385625/576))*y+(-233669102375/576))*y+(-22346744634625/576))*y+(8628551391325/192)))*x+(((((((-2106665625/4)*y+(186700628125/48))*y+(275730183125/48))*y+(-24266240046875/576))*y+(-1736446880875/576))*y+(63510377625875/576))*y+(-23175562342775/192)))*x+((((((719842500*y+-5073664375)*y+(-47507724875/6))*y+(224550126125/4))*y+(580303216025/72))*y+(-1802229116675/12))*y+(1199803223255/8)))*x+((((((315738750*y+(-17769351875/6))*y+(-8121733375/2))*y+(2081922014125/72))*y+(-60505757525/72))*y+(-5172825879925/72))*y+(2187332589535/24)))*x+((((((-2655432000*y+18136027000)*y+30530839950)*y+(-584275136900/3))*y+(-164792032405/6))*y+(1579322193605/3))*y+(-1068651377443/2)))

def resultant (x y : ℂ) : ℂ := (((((((-780273000*y+10035177750)*y+-23611927950)*y+(-223182882975/2))*y+(690750914035/2))*y+(416149886685/2))*y+(-2254312145787/2))*y+956374922997)

def monicResultant (x y : ℂ) : ℂ := (((((((1*y+(-463/36))*y+(5447/180))*y+(926743/6480))*y+(-43024037/97200))*y+(-8640089/32400))*y+(234019739/162000))*y+(-33093703/27000))

theorem curve_identity (x y : ℂ) :
    (linearCoeff x y)^3*lowCurve x y 0 0 0 0 0=
      quotient x y*constantTerm x y+multiplier x y*factor6 x*extraFactor7 x y := by
  unfold linearCoeff lowCurve SmallLevelTwentySixPariIdentity007.p1
    quotient constantTerm multiplier factor6 extraFactor7
  ring

theorem linearCoeff_factor (x y : ℂ) :
    linearCoeff x y=(-1/2:ℂ)*(x-1)*(x-2) := by unfold linearCoeff; ring

theorem low_curve_of_constant_zero (x y : ℂ) (hc : constantTerm x y=0)
    (hx : factor6 x=0 ∨ extraFactor7 x y=0) : lowCurve x y 0 0 0 0 0=0 := by
  obtain ⟨h1,h2⟩:=constant_zero_avoids_one_two x y hc
  have hl : linearCoeff x y≠0 := by
    rw [linearCoeff_factor]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr h1)) (sub_ne_zero.mpr h2)
  have he:=curve_identity x y
  have hp : (linearCoeff x y)^3*lowCurve x y 0 0 0 0 0=0 := by
    rcases hx with hx|hx <;> simpa only [hc,hx,mul_zero,zero_mul,zero_add,add_zero] using he
  exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero 3 hl)

theorem no_factor6_constant (h u : ℂ) (hu : ‖u‖=1)
    (hc : constantTerm (u*(2:ℂ)^h) ((9:ℂ)^h)=0)
    (hx : factor6 (u*(2:ℂ)^h)=0) : False := by
  exact SmallLevelTwentySixFactor6Physical.no_signed_low_curve h u hu hx
    (low_curve_of_constant_zero _ _ hc (Or.inl hx))

theorem exceptional_resultant_identity (x y : ℂ) :
    resultantMultiplier0 x y*extraFactor7 x y+
      resultantMultiplier1 x y*constantTerm x y=resultant x y := by
  unfold resultantMultiplier0 resultantMultiplier1 extraFactor7 constantTerm resultant
  ring

theorem monic_resultant_binding (x y : ℂ) :
    resultant x y=(-780273000:ℂ)*monicResultant x y := by
  unfold resultant monicResultant
  ring

theorem exceptional_resultant_zero (x y : ℂ) (hx : extraFactor7 x y=0)
    (hc : constantTerm x y=0) : monicResultant x y=0 := by
  have he:=exceptional_resultant_identity x y
  rw [hx,hc,mul_zero,mul_zero,zero_add,monic_resultant_binding] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

#print axioms curve_identity
#print axioms low_curve_of_constant_zero
#print axioms no_factor6_constant
#print axioms exceptional_resultant_identity
#print axioms exceptional_resultant_zero
end SmallLevelTwentySixExceptionalCurve
