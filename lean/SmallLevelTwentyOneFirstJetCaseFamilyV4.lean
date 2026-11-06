module
public import SmallLevelTwentyOneTheoryV4
@[expose] public noncomputable section
section
set_option autoImplicit false
-- Uniform four-variable row interfaces intentionally retain unused arguments.
set_option linter.unusedVariables false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

namespace SmallLevelTwentyOneFirstJetCase0

-- Signs (-1, -1, -1). These are algebraic certificates, not yet pole exclusion.
def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((1*x^2*y*z))*w 41)

def row003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y*z)))*w 0+((1))*w 2)

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((1*y)/(x^2*z)))*w 14)

def row005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 4+(((1*x^2)/(y*z)))*w 21)

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((1*y)/(z)))*w 28)

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((1*z)/(x^2*y)))*w 30)

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((1*x^2*y)/(z)))*w 35)

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((1*z)/(y)))*w 36)

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((1*y*z)/(x^2)))*w 38)

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((1*x^2*z)/(y)))*w 39)

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

def row046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 23+(((-1)/(x^2)))*w 34)

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

def row387 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+(((1)/(z)))*w 14+((1))*w 16+((1))*w 30)

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1*x^2)/(z)))*w 7+((1))*w 18+(((1*x^2)/(z)))*w 21+((1))*w 32)

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 8+(((1)/(z)))*w 28+((1))*w 36)

def row398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 6+(((1)/(z)))*w 14+((1))*w 34)

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y)))*w 0+(((1)/(y)))*w 6+((1))*w 8+(((1)/(y)))*w 12+((1))*w 14+(((1)/(y)))*w 18+((1))*w 20+(((1)/(y)))*w 24+((1))*w 26+(((1)/(y)))*w 30+((1))*w 32+((1))*w 38)

def row419 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((2))*w 6+((1))*w 8+((1))*w 10+((1))*w 12+((1))*w 14+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 28+((1))*w 30+((1))*w 32+((1))*w 34+((2))*w 36+((1))*w 38+((1))*w 40)

def row423 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((1))*w 6+((1))*w 10+((2))*w 12+((1))*w 14+((1))*w 16+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 26+((1))*w 28+((2))*w 30+((1))*w 32+((1))*w 36+((1))*w 38+((1))*w 40)

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

def row429 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+((1))*w 12+((1))*w 18+((1))*w 24+((1))*w 30+((1))*w 36)

def row435 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 2+(((-1*a)/(x)))*w 4+(((1)/(x^2)))*w 8+((1))*w 23)

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

def shift003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21)/(y*z)))*w 0)

def shift005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21*x^2)/(2*y*z)))*w 21)

def shift006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-7*y)/(z)))*w 28)

def shift007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-6*z)/(x^2*y)))*w 30)

def shift008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-7*x^2*y)/(2*z)))*w 35)

def shift009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-3*z)/(y)))*w 36)

def shift011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-3*x^2*z)/(2*y)))*w 39)

def shift038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-210)/(x^2)))*w 0)

def shift043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21*x^2)/(2)))*w 39)

def shift046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(x^2)))*w 34)

def shift047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((21))*w 36)

def shift397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-42)/(z)))*w 0+(((-42)/(z)))*w 28)

def shift398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(z)))*w 0+(((42)/(z)))*w 14)

theorem syzygy429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row006 x y z a w+(((-1*x^2*y)/(z)))*row007 x y z a w+((-1))*row008 x y z a w+(((-2*y)/(z)))*row009 x y z a w+(((-1*y)/(z)))*row011 x y z a w+((-1))*row043 x y z a w+((-1))*row047 x y z a w+(((2*y)/(z)))*row427 x y z a w+(((1*x^2*y)/(z)))*row428 x y z a w+((1))*row429 x y z a w)=0 := by
  dsimp only [row006,row007,row008,row009,row011,row043,row047,row427,row428,row429]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy429

theorem syzygy435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row003 x y z a w+(((1*a)/(x)))*row005 x y z a w+(((1)/(x^2)))*row006 x y z a w+(((1*y)/(x^2*z)))*row009 x y z a w+(((-1*x*a)/(y*z)))*row038 x y z a w+((-1))*row046 x y z a w+(((2)/(x^2*z))+((-1*a)/(x*y*z))+((1)/(y*z)))*row319 x y z a w+(((-1)/(x^2)))*row397 x y z a w+(((-1)/(x^2)))*row398 x y z a w+(((1)/(x^2*z))+((-1*y)/(x^2*z)))*row427 x y z a w+((1))*row435 x y z a w)=0 := by
  dsimp only [row003,row005,row006,row009,row038,row046,row319,row397,row398,row427,row435]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy435

theorem projection429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift006 x y z a w+(((-7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((-14*y)/(3*z)))*shift009 x y z a w+(((-7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)-(((-7*y)/(z))+((7*x*y*a)/(z))+((7*x^2*y)/(z)))*w 28=(((7*x^2))*row004 x y z a w+((-7*x*a))*row006 x y z a w+(((7*x^2*y)/(2*z)))*row007 x y z a w+((7))*row008 x y z a w+(((-7*y)/(z))+((7*x^2*y)/(z)))*row009 x y z a w+(((14*y)/(z)))*row011 x y z a w+((7*x^2))*row047 x y z a w+(((-7*x^2*y)/(z)))*row427 x y z a w+(((-7*x^2*y)/(2*z)))*row428 x y z a w+((-7*x^2))*row436 x y z a w) := by
  dsimp only [shift006,shift007,shift008,shift009,shift011,shift043,shift047,row004,row006,row007,row008,row009,row011,row047,row427,row428,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms projection429

theorem projection435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((28*y)/(3*x^2*z)))*shift009 x y z a w+(((-21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)-(((294)/(x^2*z))+((-98*y)/(x^2*z)))*w 28=((((42)/(x^2)))*row006 x y z a w+(((-28*y)/(x^2*z)))*row009 x y z a w+(((-21*x*a)/(y*z)))*row038 x y z a w+(((42)/(x^2*z))+((2184*a)/(x*y*z))+((21)/(y*z)))*row319 x y z a w+(((-42)/(x^2)))*row398 x y z a w+(((-126)/(x^2*z))+((28*y)/(x^2*z)))*row427 x y z a w) := by
  dsimp only [shift003,shift005,shift006,shift009,shift038,shift046,shift397,shift398,row006,row009,row038,row319,row398,row427]
  field_simp [hx,hy,hz]
  ring

#print axioms projection435

theorem residual403 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((-1)/(y*z)))*row000 x y z a w+(((-1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((-1)/(y))+((1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((-1*x^2)/(z)))*row007 x y z a w+(((-2)/(y)))*row008 x y z a w+(((-1)/(z))+((1*y)/(z))+((-1*x^2)/(z))+((-1*x^2*y)/(z)))*row009 x y z a w+(((-1*x^2)/(y*z)))*row010 x y z a w+(((-1)/(z))+((1*y)/(z)))*row011 x y z a w+(((1*x^2)/(y*z))+((1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((-1)/(y))+(1))*row043 x y z a w+(((-1)/(y))+((-1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((2)/(y*z))+((-1)/(y))+((3)/(z)))*row319 x y z a w+((1))*row387 x y z a w+((-1))*row389 x y z a w+((-2))*row397 x y z a w+((-1))*row398 x y z a w+((1))*row403 x y z a w+((1))*row419 x y z a w+((-1))*row423 x y z a w+(((2)/(z))+(-1)+((1*x^2)/(z))+((1*x^2*y)/(z)))*row427 x y z a w+(((2*x^2)/(z)))*row428 x y z a w+(((1*x^2)/(y))+(1*x^2))*row436 x y z a w)=(((-2)/(z))+(-1)+((1*y)/(z))+((1*x*a)/(z))+((1*x*y*a)/(z))+((1*x^2)/(z))+((1*x^2*y)/(z)))*w 28 := by
  dsimp only [row000,row004,row006,row007,row008,row009,row010,row011,row038,row040,row043,row047,row319,row387,row389,row397,row398,row403,row419,row423,row427,row428,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms residual403
end SmallLevelTwentyOneFirstJetCase0
end

section
set_option autoImplicit false
-- Uniform four-variable row interfaces intentionally retain unused arguments.
set_option linter.unusedVariables false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

namespace SmallLevelTwentyOneFirstJetCase1

-- Signs (-1, -1, 1). These are algebraic certificates, not yet pole exclusion.
def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((1*x^2*y*z))*w 41)

def row003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y*z)))*w 0+((1))*w 2)

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((1*y)/(x^2*z)))*w 14)

def row005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 4+(((1*x^2)/(y*z)))*w 21)

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((1*y)/(z)))*w 28)

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((1*z)/(x^2*y)))*w 30)

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((1*x^2*y)/(z)))*w 35)

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((1*z)/(y)))*w 36)

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((1*y*z)/(x^2)))*w 38)

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((1*x^2*z)/(y)))*w 39)

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

def row046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 23+(((-1)/(x^2)))*w 34)

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

def row388 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 12+((1))*w 26+(((1)/(z)))*w 28)

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1*x^2)/(z)))*w 7+((1))*w 18+(((1*x^2)/(z)))*w 21+((1))*w 32)

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 8+(((1)/(z)))*w 28+((1))*w 36)

def row398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 6+(((1)/(z)))*w 14+((1))*w 34)

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y)))*w 0+(((-1)/(y)))*w 6+((1))*w 8+(((-1)/(y)))*w 12+((1))*w 14+(((-1)/(y)))*w 18+((1))*w 20+(((-1)/(y)))*w 24+((1))*w 26+(((-1)/(y)))*w 30+((1))*w 32+((1))*w 38)

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

def row429 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+((1))*w 12+((1))*w 18+((1))*w 24+((1))*w 30+((1))*w 36)

def row435 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 2+(((-1*a)/(x)))*w 4+(((1)/(x^2)))*w 8+((1))*w 23)

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

def shift003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21)/(y*z)))*w 0)

def shift005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21*x^2)/(2*y*z)))*w 21)

def shift006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-7*y)/(z)))*w 28)

def shift007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-6*z)/(x^2*y)))*w 30)

def shift008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-7*x^2*y)/(2*z)))*w 35)

def shift009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-3*z)/(y)))*w 36)

def shift011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-3*x^2*z)/(2*y)))*w 39)

def shift038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-210)/(x^2)))*w 0)

def shift043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21*x^2)/(2)))*w 39)

def shift046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(x^2)))*w 34)

def shift047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((21))*w 36)

def shift397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-42)/(z)))*w 0+(((-42)/(z)))*w 28)

def shift398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(z)))*w 0+(((42)/(z)))*w 14)

theorem syzygy429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row006 x y z a w+(((-1*x^2*y)/(z)))*row007 x y z a w+((-1))*row008 x y z a w+(((-2*y)/(z)))*row009 x y z a w+(((-1*y)/(z)))*row011 x y z a w+((-1))*row043 x y z a w+((-1))*row047 x y z a w+(((2*y)/(z)))*row427 x y z a w+(((1*x^2*y)/(z)))*row428 x y z a w+((1))*row429 x y z a w)=0 := by
  dsimp only [row006,row007,row008,row009,row011,row043,row047,row427,row428,row429]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy429

theorem syzygy435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row003 x y z a w+(((1*a)/(x)))*row005 x y z a w+(((1)/(x^2)))*row006 x y z a w+(((1*y)/(x^2*z)))*row009 x y z a w+(((-1*x*a)/(y*z)))*row038 x y z a w+((-1))*row046 x y z a w+(((2)/(x^2*z))+((-1*a)/(x*y*z))+((1)/(y*z)))*row319 x y z a w+(((-1)/(x^2)))*row397 x y z a w+(((-1)/(x^2)))*row398 x y z a w+(((1)/(x^2*z))+((-1*y)/(x^2*z)))*row427 x y z a w+((1))*row435 x y z a w)=0 := by
  dsimp only [row003,row005,row006,row009,row038,row046,row319,row397,row398,row427,row435]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy435

theorem projection429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift006 x y z a w+(((-7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((-14*y)/(3*z)))*shift009 x y z a w+(((-7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)-(((-7*y)/(z))+((7*x*y*a)/(z))+((7*x^2*y)/(z)))*w 28=(((7*x^2))*row004 x y z a w+((-7*x*a))*row006 x y z a w+(((7*x^2*y)/(2*z)))*row007 x y z a w+((7))*row008 x y z a w+(((-7*y)/(z))+((7*x^2*y)/(z)))*row009 x y z a w+(((14*y)/(z)))*row011 x y z a w+((7*x^2))*row047 x y z a w+(((-7*x^2*y)/(z)))*row427 x y z a w+(((-7*x^2*y)/(2*z)))*row428 x y z a w+((-7*x^2))*row436 x y z a w) := by
  dsimp only [shift006,shift007,shift008,shift009,shift011,shift043,shift047,row004,row006,row007,row008,row009,row011,row047,row427,row428,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms projection429

theorem projection435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((28*y)/(3*x^2*z)))*shift009 x y z a w+(((-21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)-(((294)/(x^2*z))+((-98*y)/(x^2*z)))*w 28=((((42)/(x^2)))*row006 x y z a w+(((-28*y)/(x^2*z)))*row009 x y z a w+(((-21*x*a)/(y*z)))*row038 x y z a w+(((42)/(x^2*z))+((2184*a)/(x*y*z))+((21)/(y*z)))*row319 x y z a w+(((-42)/(x^2)))*row398 x y z a w+(((-126)/(x^2*z))+((28*y)/(x^2*z)))*row427 x y z a w) := by
  dsimp only [shift003,shift005,shift006,shift009,shift038,shift046,shift397,shift398,row006,row009,row038,row319,row398,row427]
  field_simp [hx,hy,hz]
  ring

#print axioms projection435

theorem residual403 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((-1)/(y*z)))*row000 x y z a w+(((-1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((1)/(y))+((1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((1*x^2)/(z)))*row007 x y z a w+(((1)/(z))+((1*y)/(z))+((-1*x^2)/(z))+((-1*x^2*y)/(z)))*row009 x y z a w+(((-1*x^2)/(y*z)))*row010 x y z a w+(((1)/(z))+((1*y)/(z)))*row011 x y z a w+(((1*x^2)/(y*z))+((1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((1)/(y))+(1))*row043 x y z a w+(((1)/(y))+((-1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((2)/(y*z))+((1)/(y))+((3)/(z)))*row319 x y z a w+((-1))*row388 x y z a w+((-1))*row389 x y z a w+((-1))*row397 x y z a w+((1))*row403 x y z a w+((-1)+((1*x^2)/(z))+((1*x^2*y)/(z)))*row427 x y z a w+(((1*x^2)/(y))+(1*x^2))*row436 x y z a w)=((-1)+((1*y)/(z))+((1*x*a)/(z))+((1*x*y*a)/(z))+((1*x^2)/(z))+((1*x^2*y)/(z)))*w 28 := by
  dsimp only [row000,row004,row006,row007,row009,row010,row011,row038,row040,row043,row047,row319,row388,row389,row397,row403,row427,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms residual403
end SmallLevelTwentyOneFirstJetCase1
end

section
set_option autoImplicit false
-- Uniform four-variable row interfaces intentionally retain unused arguments.
set_option linter.unusedVariables false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

namespace SmallLevelTwentyOneFirstJetCase2

-- Signs (-1, 1, -1). These are algebraic certificates, not yet pole exclusion.
def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((1*x^2*y*z))*w 41)

def row003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y*z)))*w 0+((1))*w 2)

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((1*y)/(x^2*z)))*w 14)

def row005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 4+(((1*x^2)/(y*z)))*w 21)

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((1*y)/(z)))*w 28)

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((1*z)/(x^2*y)))*w 30)

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((1*x^2*y)/(z)))*w 35)

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((1*z)/(y)))*w 36)

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((1*y*z)/(x^2)))*w 38)

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((1*x^2*z)/(y)))*w 39)

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

def row046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 23+(((-1)/(x^2)))*w 34)

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

def row388 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 12+((1))*w 26+(((-1)/(z)))*w 28)

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1*x^2)/(z)))*w 7+((1))*w 18+(((-1*x^2)/(z)))*w 21+((1))*w 32)

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 8+(((-1)/(z)))*w 28+((1))*w 36)

def row398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 6+(((-1)/(z)))*w 14+((1))*w 34)

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y)))*w 0+(((1)/(y)))*w 6+((1))*w 8+(((1)/(y)))*w 12+((1))*w 14+(((1)/(y)))*w 18+((1))*w 20+(((1)/(y)))*w 24+((1))*w 26+(((1)/(y)))*w 30+((1))*w 32+((1))*w 38)

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

def row429 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+((1))*w 12+((1))*w 18+((1))*w 24+((1))*w 30+((1))*w 36)

def row435 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 2+(((-1*a)/(x)))*w 4+(((1)/(x^2)))*w 8+((1))*w 23)

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

def shift003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21)/(y*z)))*w 0)

def shift005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21*x^2)/(2*y*z)))*w 21)

def shift006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-7*y)/(z)))*w 28)

def shift007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-6*z)/(x^2*y)))*w 30)

def shift008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-7*x^2*y)/(2*z)))*w 35)

def shift009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-3*z)/(y)))*w 36)

def shift011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-3*x^2*z)/(2*y)))*w 39)

def shift038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-210)/(x^2)))*w 0)

def shift043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21*x^2)/(2)))*w 39)

def shift046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(x^2)))*w 34)

def shift047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((21))*w 36)

def shift397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(z)))*w 0+(((42)/(z)))*w 28)

def shift398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-42)/(z)))*w 0+(((-42)/(z)))*w 14)

theorem syzygy429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row006 x y z a w+(((-1*x^2*y)/(z)))*row007 x y z a w+((-1))*row008 x y z a w+(((-2*y)/(z)))*row009 x y z a w+(((-1*y)/(z)))*row011 x y z a w+((-1))*row043 x y z a w+((-1))*row047 x y z a w+(((2*y)/(z)))*row427 x y z a w+(((1*x^2*y)/(z)))*row428 x y z a w+((1))*row429 x y z a w)=0 := by
  dsimp only [row006,row007,row008,row009,row011,row043,row047,row427,row428,row429]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy429

theorem syzygy435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row003 x y z a w+(((1*a)/(x)))*row005 x y z a w+(((1)/(x^2)))*row006 x y z a w+(((1*y)/(x^2*z)))*row009 x y z a w+(((-1*x*a)/(y*z)))*row038 x y z a w+((-1))*row046 x y z a w+(((-2)/(x^2*z))+((-1*a)/(x*y*z))+((1)/(y*z)))*row319 x y z a w+(((-1)/(x^2)))*row397 x y z a w+(((-1)/(x^2)))*row398 x y z a w+(((-1)/(x^2*z))+((-1*y)/(x^2*z)))*row427 x y z a w+((1))*row435 x y z a w)=0 := by
  dsimp only [row003,row005,row006,row009,row038,row046,row319,row397,row398,row427,row435]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy435

theorem projection429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift006 x y z a w+(((-7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((-14*y)/(3*z)))*shift009 x y z a w+(((-7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)-(((-7*y)/(z))+((7*x*y*a)/(z))+((7*x^2*y)/(z)))*w 28=(((7*x^2))*row004 x y z a w+((-7*x*a))*row006 x y z a w+(((7*x^2*y)/(2*z)))*row007 x y z a w+((7))*row008 x y z a w+(((-7*y)/(z))+((7*x^2*y)/(z)))*row009 x y z a w+(((14*y)/(z)))*row011 x y z a w+((7*x^2))*row047 x y z a w+(((-7*x^2*y)/(z)))*row427 x y z a w+(((-7*x^2*y)/(2*z)))*row428 x y z a w+((-7*x^2))*row436 x y z a w) := by
  dsimp only [shift006,shift007,shift008,shift009,shift011,shift043,shift047,row004,row006,row007,row008,row009,row011,row047,row427,row428,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms projection429

theorem projection435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((28*y)/(3*x^2*z)))*shift009 x y z a w+(((-21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)-(((-294)/(x^2*z))+((-98*y)/(x^2*z)))*w 28=((((42)/(x^2)))*row006 x y z a w+(((-28*y)/(x^2*z)))*row009 x y z a w+(((-21*x*a)/(y*z)))*row038 x y z a w+(((-42)/(x^2*z))+((2184*a)/(x*y*z))+((21)/(y*z)))*row319 x y z a w+(((-42)/(x^2)))*row398 x y z a w+(((126)/(x^2*z))+((28*y)/(x^2*z)))*row427 x y z a w) := by
  dsimp only [shift003,shift005,shift006,shift009,shift038,shift046,shift397,shift398,row006,row009,row038,row319,row398,row427]
  field_simp [hx,hy,hz]
  ring

#print axioms projection435

theorem residual403 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((-1)/(y*z)))*row000 x y z a w+(((1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((-1)/(y))+((-1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((-1*x^2)/(z)))*row007 x y z a w+(((-1)/(z))+((1*y)/(z))+((1*x^2)/(z))+((-1*x^2*y)/(z)))*row009 x y z a w+(((-1*x^2)/(y*z)))*row010 x y z a w+(((-1)/(z))+((1*y)/(z)))*row011 x y z a w+(((1*x^2)/(y*z))+((-1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((-1)/(y))+(1))*row043 x y z a w+(((-1)/(y))+((1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((2)/(y*z))+((-1)/(y))+((-3)/(z)))*row319 x y z a w+((-1))*row388 x y z a w+((-1))*row389 x y z a w+((-1))*row397 x y z a w+((1))*row403 x y z a w+((-1)+((-1*x^2)/(z))+((1*x^2*y)/(z)))*row427 x y z a w+(((-1*x^2)/(y))+(1*x^2))*row436 x y z a w)=((-1)+((1*y)/(z))+((-1*x*a)/(z))+((1*x*y*a)/(z))+((-1*x^2)/(z))+((1*x^2*y)/(z)))*w 28 := by
  dsimp only [row000,row004,row006,row007,row009,row010,row011,row038,row040,row043,row047,row319,row388,row389,row397,row403,row427,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms residual403
end SmallLevelTwentyOneFirstJetCase2
end

section
set_option autoImplicit false
-- Uniform four-variable row interfaces intentionally retain unused arguments.
set_option linter.unusedVariables false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

namespace SmallLevelTwentyOneFirstJetCase3

-- Signs (-1, 1, 1). These are algebraic certificates, not yet pole exclusion.
def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((1*x^2*y*z))*w 41)

def row003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y*z)))*w 0+((1))*w 2)

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((1*y)/(x^2*z)))*w 14)

def row005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 4+(((1*x^2)/(y*z)))*w 21)

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((1*y)/(z)))*w 28)

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((1*z)/(x^2*y)))*w 30)

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((1*x^2*y)/(z)))*w 35)

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((1*z)/(y)))*w 36)

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((1*y*z)/(x^2)))*w 38)

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((1*x^2*z)/(y)))*w 39)

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

def row046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 23+(((-1)/(x^2)))*w 34)

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

def row387 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+(((-1)/(z)))*w 14+((1))*w 16+((1))*w 30)

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1*x^2)/(z)))*w 7+((1))*w 18+(((-1*x^2)/(z)))*w 21+((1))*w 32)

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 8+(((-1)/(z)))*w 28+((1))*w 36)

def row398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 6+(((-1)/(z)))*w 14+((1))*w 34)

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y)))*w 0+(((-1)/(y)))*w 6+((1))*w 8+(((-1)/(y)))*w 12+((1))*w 14+(((-1)/(y)))*w 18+((1))*w 20+(((-1)/(y)))*w 24+((1))*w 26+(((-1)/(y)))*w 30+((1))*w 32+((1))*w 38)

def row419 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((2))*w 6+((1))*w 8+((1))*w 10+((1))*w 12+((1))*w 14+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 28+((1))*w 30+((1))*w 32+((1))*w 34+((2))*w 36+((1))*w 38+((1))*w 40)

def row423 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((1))*w 6+((1))*w 10+((2))*w 12+((1))*w 14+((1))*w 16+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 26+((1))*w 28+((2))*w 30+((1))*w 32+((1))*w 36+((1))*w 38+((1))*w 40)

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

def row429 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+((1))*w 12+((1))*w 18+((1))*w 24+((1))*w 30+((1))*w 36)

def row435 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 2+(((-1*a)/(x)))*w 4+(((1)/(x^2)))*w 8+((1))*w 23)

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

def shift003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21)/(y*z)))*w 0)

def shift005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21*x^2)/(2*y*z)))*w 21)

def shift006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-7*y)/(z)))*w 28)

def shift007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-6*z)/(x^2*y)))*w 30)

def shift008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-7*x^2*y)/(2*z)))*w 35)

def shift009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-3*z)/(y)))*w 36)

def shift011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-3*x^2*z)/(2*y)))*w 39)

def shift038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-210)/(x^2)))*w 0)

def shift043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21*x^2)/(2)))*w 39)

def shift046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(x^2)))*w 34)

def shift047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((21))*w 36)

def shift397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(z)))*w 0+(((42)/(z)))*w 28)

def shift398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-42)/(z)))*w 0+(((-42)/(z)))*w 14)

theorem syzygy429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row006 x y z a w+(((-1*x^2*y)/(z)))*row007 x y z a w+((-1))*row008 x y z a w+(((-2*y)/(z)))*row009 x y z a w+(((-1*y)/(z)))*row011 x y z a w+((-1))*row043 x y z a w+((-1))*row047 x y z a w+(((2*y)/(z)))*row427 x y z a w+(((1*x^2*y)/(z)))*row428 x y z a w+((1))*row429 x y z a w)=0 := by
  dsimp only [row006,row007,row008,row009,row011,row043,row047,row427,row428,row429]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy429

theorem syzygy435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row003 x y z a w+(((1*a)/(x)))*row005 x y z a w+(((1)/(x^2)))*row006 x y z a w+(((1*y)/(x^2*z)))*row009 x y z a w+(((-1*x*a)/(y*z)))*row038 x y z a w+((-1))*row046 x y z a w+(((-2)/(x^2*z))+((-1*a)/(x*y*z))+((1)/(y*z)))*row319 x y z a w+(((-1)/(x^2)))*row397 x y z a w+(((-1)/(x^2)))*row398 x y z a w+(((-1)/(x^2*z))+((-1*y)/(x^2*z)))*row427 x y z a w+((1))*row435 x y z a w)=0 := by
  dsimp only [row003,row005,row006,row009,row038,row046,row319,row397,row398,row427,row435]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy435

theorem projection429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift006 x y z a w+(((-7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((-14*y)/(3*z)))*shift009 x y z a w+(((-7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)-(((-7*y)/(z))+((7*x*y*a)/(z))+((7*x^2*y)/(z)))*w 28=(((7*x^2))*row004 x y z a w+((-7*x*a))*row006 x y z a w+(((7*x^2*y)/(2*z)))*row007 x y z a w+((7))*row008 x y z a w+(((-7*y)/(z))+((7*x^2*y)/(z)))*row009 x y z a w+(((14*y)/(z)))*row011 x y z a w+((7*x^2))*row047 x y z a w+(((-7*x^2*y)/(z)))*row427 x y z a w+(((-7*x^2*y)/(2*z)))*row428 x y z a w+((-7*x^2))*row436 x y z a w) := by
  dsimp only [shift006,shift007,shift008,shift009,shift011,shift043,shift047,row004,row006,row007,row008,row009,row011,row047,row427,row428,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms projection429

theorem projection435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((28*y)/(3*x^2*z)))*shift009 x y z a w+(((-21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)-(((-294)/(x^2*z))+((-98*y)/(x^2*z)))*w 28=((((42)/(x^2)))*row006 x y z a w+(((-28*y)/(x^2*z)))*row009 x y z a w+(((-21*x*a)/(y*z)))*row038 x y z a w+(((-42)/(x^2*z))+((2184*a)/(x*y*z))+((21)/(y*z)))*row319 x y z a w+(((-42)/(x^2)))*row398 x y z a w+(((126)/(x^2*z))+((28*y)/(x^2*z)))*row427 x y z a w) := by
  dsimp only [shift003,shift005,shift006,shift009,shift038,shift046,shift397,shift398,row006,row009,row038,row319,row398,row427]
  field_simp [hx,hy,hz]
  ring

#print axioms projection435

theorem residual403 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((-1)/(y*z)))*row000 x y z a w+(((1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((1)/(y))+((-1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((1*x^2)/(z)))*row007 x y z a w+(((2)/(y)))*row008 x y z a w+(((1)/(z))+((1*y)/(z))+((1*x^2)/(z))+((-1*x^2*y)/(z)))*row009 x y z a w+(((-1*x^2)/(y*z)))*row010 x y z a w+(((1)/(z))+((1*y)/(z)))*row011 x y z a w+(((1*x^2)/(y*z))+((-1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((1)/(y))+(1))*row043 x y z a w+(((1)/(y))+((1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((2)/(y*z))+((1)/(y))+((-3)/(z)))*row319 x y z a w+((1))*row387 x y z a w+((-1))*row389 x y z a w+((-2))*row397 x y z a w+((-1))*row398 x y z a w+((1))*row403 x y z a w+((1))*row419 x y z a w+((-1))*row423 x y z a w+(((-2)/(z))+(-1)+((-1*x^2)/(z))+((1*x^2*y)/(z)))*row427 x y z a w+(((-2*x^2)/(z)))*row428 x y z a w+(((-1*x^2)/(y))+(1*x^2))*row436 x y z a w)=(((2)/(z))+(-1)+((1*y)/(z))+((-1*x*a)/(z))+((1*x*y*a)/(z))+((-1*x^2)/(z))+((1*x^2*y)/(z)))*w 28 := by
  dsimp only [row000,row004,row006,row007,row008,row009,row010,row011,row038,row040,row043,row047,row319,row387,row389,row397,row398,row403,row419,row423,row427,row428,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms residual403
end SmallLevelTwentyOneFirstJetCase3
end

section
set_option autoImplicit false
-- Uniform four-variable row interfaces intentionally retain unused arguments.
set_option linter.unusedVariables false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

namespace SmallLevelTwentyOneFirstJetCase4

-- Signs (1, -1, -1). These are algebraic certificates, not yet pole exclusion.
def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((-1*x^2*y*z))*w 41)

def row003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y*z)))*w 0+((1))*w 2)

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*y)/(x^2*z)))*w 14)

def row005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 4+(((-1*x^2)/(y*z)))*w 21)

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((-1*y)/(z)))*w 28)

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((-1*z)/(x^2*y)))*w 30)

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((-1*x^2*y)/(z)))*w 35)

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((-1*z)/(y)))*w 36)

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((-1*y*z)/(x^2)))*w 38)

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((-1*x^2*z)/(y)))*w 39)

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

def row046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 23+(((-1)/(x^2)))*w 34)

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

def row388 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 12+((1))*w 26+(((-1)/(z)))*w 28)

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1*x^2)/(z)))*w 7+((1))*w 18+(((-1*x^2)/(z)))*w 21+((1))*w 32)

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 8+(((-1)/(z)))*w 28+((1))*w 36)

def row398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 6+(((-1)/(z)))*w 14+((1))*w 34)

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y)))*w 0+(((-1)/(y)))*w 6+((1))*w 8+(((-1)/(y)))*w 12+((1))*w 14+(((-1)/(y)))*w 18+((1))*w 20+(((-1)/(y)))*w 24+((1))*w 26+(((-1)/(y)))*w 30+((1))*w 32+((1))*w 38)

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

def row429 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+((1))*w 12+((1))*w 18+((1))*w 24+((1))*w 30+((1))*w 36)

def row435 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 2+(((-1*a)/(x)))*w 4+(((1)/(x^2)))*w 8+((1))*w 23)

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

def shift003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((21)/(y*z)))*w 0)

def shift005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((21*x^2)/(2*y*z)))*w 21)

def shift006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((7*y)/(z)))*w 28)

def shift007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((6*z)/(x^2*y)))*w 30)

def shift008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((7*x^2*y)/(2*z)))*w 35)

def shift009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((3*z)/(y)))*w 36)

def shift011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((3*x^2*z)/(2*y)))*w 39)

def shift038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-210)/(x^2)))*w 0)

def shift043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21*x^2)/(2)))*w 39)

def shift046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(x^2)))*w 34)

def shift047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((21))*w 36)

def shift397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(z)))*w 0+(((42)/(z)))*w 28)

def shift398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-42)/(z)))*w 0+(((-42)/(z)))*w 14)

theorem syzygy429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row006 x y z a w+(((1*x^2*y)/(z)))*row007 x y z a w+((-1))*row008 x y z a w+(((2*y)/(z)))*row009 x y z a w+(((1*y)/(z)))*row011 x y z a w+((-1))*row043 x y z a w+((-1))*row047 x y z a w+(((-2*y)/(z)))*row427 x y z a w+(((-1*x^2*y)/(z)))*row428 x y z a w+((1))*row429 x y z a w)=0 := by
  dsimp only [row006,row007,row008,row009,row011,row043,row047,row427,row428,row429]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy429

theorem syzygy435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row003 x y z a w+(((1*a)/(x)))*row005 x y z a w+(((1)/(x^2)))*row006 x y z a w+(((-1*y)/(x^2*z)))*row009 x y z a w+(((1*x*a)/(y*z)))*row038 x y z a w+((-1))*row046 x y z a w+(((-2)/(x^2*z))+((1*a)/(x*y*z))+((-1)/(y*z)))*row319 x y z a w+(((-1)/(x^2)))*row397 x y z a w+(((-1)/(x^2)))*row398 x y z a w+(((-1)/(x^2*z))+((1*y)/(x^2*z)))*row427 x y z a w+((1))*row435 x y z a w)=0 := by
  dsimp only [row003,row005,row006,row009,row038,row046,row319,row397,row398,row427,row435]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy435

theorem projection429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift006 x y z a w+(((7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((14*y)/(3*z)))*shift009 x y z a w+(((7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)-(((7*y)/(z))+((-7*x*y*a)/(z))+((-7*x^2*y)/(z)))*w 28=(((7*x^2))*row004 x y z a w+((-7*x*a))*row006 x y z a w+(((-7*x^2*y)/(2*z)))*row007 x y z a w+((7))*row008 x y z a w+(((7*y)/(z))+((-7*x^2*y)/(z)))*row009 x y z a w+(((-14*y)/(z)))*row011 x y z a w+((7*x^2))*row047 x y z a w+(((7*x^2*y)/(z)))*row427 x y z a w+(((7*x^2*y)/(2*z)))*row428 x y z a w+((-7*x^2))*row436 x y z a w) := by
  dsimp only [shift006,shift007,shift008,shift009,shift011,shift043,shift047,row004,row006,row007,row008,row009,row011,row047,row427,row428,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms projection429

theorem projection435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((-28*y)/(3*x^2*z)))*shift009 x y z a w+(((21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)-(((-294)/(x^2*z))+((98*y)/(x^2*z)))*w 28=((((42)/(x^2)))*row006 x y z a w+(((28*y)/(x^2*z)))*row009 x y z a w+(((21*x*a)/(y*z)))*row038 x y z a w+(((-42)/(x^2*z))+((-2184*a)/(x*y*z))+((-21)/(y*z)))*row319 x y z a w+(((-42)/(x^2)))*row398 x y z a w+(((126)/(x^2*z))+((-28*y)/(x^2*z)))*row427 x y z a w) := by
  dsimp only [shift003,shift005,shift006,shift009,shift038,shift046,shift397,shift398,row006,row009,row038,row319,row398,row427]
  field_simp [hx,hy,hz]
  ring

#print axioms projection435

theorem residual403 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((1)/(y*z)))*row000 x y z a w+(((-1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((1)/(y))+((1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((-1*x^2)/(z)))*row007 x y z a w+(((-1)/(z))+((-1*y)/(z))+((1*x^2)/(z))+((1*x^2*y)/(z)))*row009 x y z a w+(((1*x^2)/(y*z)))*row010 x y z a w+(((-1)/(z))+((-1*y)/(z)))*row011 x y z a w+(((-1*x^2)/(y*z))+((-1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((1)/(y))+(1))*row043 x y z a w+(((1)/(y))+((-1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((-2)/(y*z))+((1)/(y))+((-3)/(z)))*row319 x y z a w+((-1))*row388 x y z a w+((-1))*row389 x y z a w+((-1))*row397 x y z a w+((1))*row403 x y z a w+((-1)+((-1*x^2)/(z))+((-1*x^2*y)/(z)))*row427 x y z a w+(((1*x^2)/(y))+(1*x^2))*row436 x y z a w)=((-1)+((-1*y)/(z))+((-1*x*a)/(z))+((-1*x*y*a)/(z))+((-1*x^2)/(z))+((-1*x^2*y)/(z)))*w 28 := by
  dsimp only [row000,row004,row006,row007,row009,row010,row011,row038,row040,row043,row047,row319,row388,row389,row397,row403,row427,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms residual403
end SmallLevelTwentyOneFirstJetCase4
end

section
set_option autoImplicit false
-- Uniform four-variable row interfaces intentionally retain unused arguments.
set_option linter.unusedVariables false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

namespace SmallLevelTwentyOneFirstJetCase5

-- Signs (1, -1, 1). These are algebraic certificates, not yet pole exclusion.
def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((-1*x^2*y*z))*w 41)

def row003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y*z)))*w 0+((1))*w 2)

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*y)/(x^2*z)))*w 14)

def row005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 4+(((-1*x^2)/(y*z)))*w 21)

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((-1*y)/(z)))*w 28)

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((-1*z)/(x^2*y)))*w 30)

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((-1*x^2*y)/(z)))*w 35)

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((-1*z)/(y)))*w 36)

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((-1*y*z)/(x^2)))*w 38)

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((-1*x^2*z)/(y)))*w 39)

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

def row046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 23+(((-1)/(x^2)))*w 34)

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

def row387 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+(((-1)/(z)))*w 14+((1))*w 16+((1))*w 30)

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1*x^2)/(z)))*w 7+((1))*w 18+(((-1*x^2)/(z)))*w 21+((1))*w 32)

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 8+(((-1)/(z)))*w 28+((1))*w 36)

def row398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(z)))*w 0+((1))*w 6+(((-1)/(z)))*w 14+((1))*w 34)

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y)))*w 0+(((1)/(y)))*w 6+((1))*w 8+(((1)/(y)))*w 12+((1))*w 14+(((1)/(y)))*w 18+((1))*w 20+(((1)/(y)))*w 24+((1))*w 26+(((1)/(y)))*w 30+((1))*w 32+((1))*w 38)

def row419 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((2))*w 6+((1))*w 8+((1))*w 10+((1))*w 12+((1))*w 14+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 28+((1))*w 30+((1))*w 32+((1))*w 34+((2))*w 36+((1))*w 38+((1))*w 40)

def row423 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((1))*w 6+((1))*w 10+((2))*w 12+((1))*w 14+((1))*w 16+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 26+((1))*w 28+((2))*w 30+((1))*w 32+((1))*w 36+((1))*w 38+((1))*w 40)

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

def row429 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+((1))*w 12+((1))*w 18+((1))*w 24+((1))*w 30+((1))*w 36)

def row435 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 2+(((-1*a)/(x)))*w 4+(((1)/(x^2)))*w 8+((1))*w 23)

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

def shift003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((21)/(y*z)))*w 0)

def shift005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((21*x^2)/(2*y*z)))*w 21)

def shift006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((7*y)/(z)))*w 28)

def shift007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((6*z)/(x^2*y)))*w 30)

def shift008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((7*x^2*y)/(2*z)))*w 35)

def shift009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((3*z)/(y)))*w 36)

def shift011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((3*x^2*z)/(2*y)))*w 39)

def shift038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-210)/(x^2)))*w 0)

def shift043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21*x^2)/(2)))*w 39)

def shift046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(x^2)))*w 34)

def shift047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((21))*w 36)

def shift397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(z)))*w 0+(((42)/(z)))*w 28)

def shift398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-42)/(z)))*w 0+(((-42)/(z)))*w 14)

theorem syzygy429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row006 x y z a w+(((1*x^2*y)/(z)))*row007 x y z a w+((-1))*row008 x y z a w+(((2*y)/(z)))*row009 x y z a w+(((1*y)/(z)))*row011 x y z a w+((-1))*row043 x y z a w+((-1))*row047 x y z a w+(((-2*y)/(z)))*row427 x y z a w+(((-1*x^2*y)/(z)))*row428 x y z a w+((1))*row429 x y z a w)=0 := by
  dsimp only [row006,row007,row008,row009,row011,row043,row047,row427,row428,row429]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy429

theorem syzygy435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row003 x y z a w+(((1*a)/(x)))*row005 x y z a w+(((1)/(x^2)))*row006 x y z a w+(((-1*y)/(x^2*z)))*row009 x y z a w+(((1*x*a)/(y*z)))*row038 x y z a w+((-1))*row046 x y z a w+(((-2)/(x^2*z))+((1*a)/(x*y*z))+((-1)/(y*z)))*row319 x y z a w+(((-1)/(x^2)))*row397 x y z a w+(((-1)/(x^2)))*row398 x y z a w+(((-1)/(x^2*z))+((1*y)/(x^2*z)))*row427 x y z a w+((1))*row435 x y z a w)=0 := by
  dsimp only [row003,row005,row006,row009,row038,row046,row319,row397,row398,row427,row435]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy435

theorem projection429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift006 x y z a w+(((7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((14*y)/(3*z)))*shift009 x y z a w+(((7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)-(((7*y)/(z))+((-7*x*y*a)/(z))+((-7*x^2*y)/(z)))*w 28=(((7*x^2))*row004 x y z a w+((-7*x*a))*row006 x y z a w+(((-7*x^2*y)/(2*z)))*row007 x y z a w+((7))*row008 x y z a w+(((7*y)/(z))+((-7*x^2*y)/(z)))*row009 x y z a w+(((-14*y)/(z)))*row011 x y z a w+((7*x^2))*row047 x y z a w+(((7*x^2*y)/(z)))*row427 x y z a w+(((7*x^2*y)/(2*z)))*row428 x y z a w+((-7*x^2))*row436 x y z a w) := by
  dsimp only [shift006,shift007,shift008,shift009,shift011,shift043,shift047,row004,row006,row007,row008,row009,row011,row047,row427,row428,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms projection429

theorem projection435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((-28*y)/(3*x^2*z)))*shift009 x y z a w+(((21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)-(((-294)/(x^2*z))+((98*y)/(x^2*z)))*w 28=((((42)/(x^2)))*row006 x y z a w+(((28*y)/(x^2*z)))*row009 x y z a w+(((21*x*a)/(y*z)))*row038 x y z a w+(((-42)/(x^2*z))+((-2184*a)/(x*y*z))+((-21)/(y*z)))*row319 x y z a w+(((-42)/(x^2)))*row398 x y z a w+(((126)/(x^2*z))+((-28*y)/(x^2*z)))*row427 x y z a w) := by
  dsimp only [shift003,shift005,shift006,shift009,shift038,shift046,shift397,shift398,row006,row009,row038,row319,row398,row427]
  field_simp [hx,hy,hz]
  ring

#print axioms projection435

theorem residual403 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((1)/(y*z)))*row000 x y z a w+(((-1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((-1)/(y))+((1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((1*x^2)/(z)))*row007 x y z a w+(((-2)/(y)))*row008 x y z a w+(((1)/(z))+((-1*y)/(z))+((1*x^2)/(z))+((1*x^2*y)/(z)))*row009 x y z a w+(((1*x^2)/(y*z)))*row010 x y z a w+(((1)/(z))+((-1*y)/(z)))*row011 x y z a w+(((-1*x^2)/(y*z))+((-1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((-1)/(y))+(1))*row043 x y z a w+(((-1)/(y))+((-1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((-2)/(y*z))+((-1)/(y))+((-3)/(z)))*row319 x y z a w+((1))*row387 x y z a w+((-1))*row389 x y z a w+((-2))*row397 x y z a w+((-1))*row398 x y z a w+((1))*row403 x y z a w+((1))*row419 x y z a w+((-1))*row423 x y z a w+(((-2)/(z))+(-1)+((-1*x^2)/(z))+((-1*x^2*y)/(z)))*row427 x y z a w+(((-2*x^2)/(z)))*row428 x y z a w+(((1*x^2)/(y))+(1*x^2))*row436 x y z a w)=(((2)/(z))+(-1)+((-1*y)/(z))+((-1*x*a)/(z))+((-1*x*y*a)/(z))+((-1*x^2)/(z))+((-1*x^2*y)/(z)))*w 28 := by
  dsimp only [row000,row004,row006,row007,row008,row009,row010,row011,row038,row040,row043,row047,row319,row387,row389,row397,row398,row403,row419,row423,row427,row428,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms residual403
end SmallLevelTwentyOneFirstJetCase5
end

section
set_option autoImplicit false
-- Uniform four-variable row interfaces intentionally retain unused arguments.
set_option linter.unusedVariables false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

namespace SmallLevelTwentyOneFirstJetCase6

-- Signs (1, 1, -1). These are algebraic certificates, not yet pole exclusion.
def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((-1*x^2*y*z))*w 41)

def row003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y*z)))*w 0+((1))*w 2)

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*y)/(x^2*z)))*w 14)

def row005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 4+(((-1*x^2)/(y*z)))*w 21)

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((-1*y)/(z)))*w 28)

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((-1*z)/(x^2*y)))*w 30)

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((-1*x^2*y)/(z)))*w 35)

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((-1*z)/(y)))*w 36)

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((-1*y*z)/(x^2)))*w 38)

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((-1*x^2*z)/(y)))*w 39)

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

def row046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 23+(((-1)/(x^2)))*w 34)

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

def row387 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+(((1)/(z)))*w 14+((1))*w 16+((1))*w 30)

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1*x^2)/(z)))*w 7+((1))*w 18+(((1*x^2)/(z)))*w 21+((1))*w 32)

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 8+(((1)/(z)))*w 28+((1))*w 36)

def row398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 6+(((1)/(z)))*w 14+((1))*w 34)

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y)))*w 0+(((-1)/(y)))*w 6+((1))*w 8+(((-1)/(y)))*w 12+((1))*w 14+(((-1)/(y)))*w 18+((1))*w 20+(((-1)/(y)))*w 24+((1))*w 26+(((-1)/(y)))*w 30+((1))*w 32+((1))*w 38)

def row419 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((2))*w 6+((1))*w 8+((1))*w 10+((1))*w 12+((1))*w 14+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 28+((1))*w 30+((1))*w 32+((1))*w 34+((2))*w 36+((1))*w 38+((1))*w 40)

def row423 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((2))*w 0+((1))*w 2+((1))*w 4+((1))*w 6+((1))*w 10+((2))*w 12+((1))*w 14+((1))*w 16+((2))*w 18+((1))*w 20+((1))*w 22+((2))*w 24+((1))*w 26+((1))*w 28+((2))*w 30+((1))*w 32+((1))*w 36+((1))*w 38+((1))*w 40)

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

def row429 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+((1))*w 12+((1))*w 18+((1))*w 24+((1))*w 30+((1))*w 36)

def row435 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 2+(((-1*a)/(x)))*w 4+(((1)/(x^2)))*w 8+((1))*w 23)

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

def shift003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((21)/(y*z)))*w 0)

def shift005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((21*x^2)/(2*y*z)))*w 21)

def shift006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((7*y)/(z)))*w 28)

def shift007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((6*z)/(x^2*y)))*w 30)

def shift008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((7*x^2*y)/(2*z)))*w 35)

def shift009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((3*z)/(y)))*w 36)

def shift011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((3*x^2*z)/(2*y)))*w 39)

def shift038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-210)/(x^2)))*w 0)

def shift043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21*x^2)/(2)))*w 39)

def shift046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(x^2)))*w 34)

def shift047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((21))*w 36)

def shift397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-42)/(z)))*w 0+(((-42)/(z)))*w 28)

def shift398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(z)))*w 0+(((42)/(z)))*w 14)

theorem syzygy429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row006 x y z a w+(((1*x^2*y)/(z)))*row007 x y z a w+((-1))*row008 x y z a w+(((2*y)/(z)))*row009 x y z a w+(((1*y)/(z)))*row011 x y z a w+((-1))*row043 x y z a w+((-1))*row047 x y z a w+(((-2*y)/(z)))*row427 x y z a w+(((-1*x^2*y)/(z)))*row428 x y z a w+((1))*row429 x y z a w)=0 := by
  dsimp only [row006,row007,row008,row009,row011,row043,row047,row427,row428,row429]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy429

theorem syzygy435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row003 x y z a w+(((1*a)/(x)))*row005 x y z a w+(((1)/(x^2)))*row006 x y z a w+(((-1*y)/(x^2*z)))*row009 x y z a w+(((1*x*a)/(y*z)))*row038 x y z a w+((-1))*row046 x y z a w+(((2)/(x^2*z))+((1*a)/(x*y*z))+((-1)/(y*z)))*row319 x y z a w+(((-1)/(x^2)))*row397 x y z a w+(((-1)/(x^2)))*row398 x y z a w+(((1)/(x^2*z))+((1*y)/(x^2*z)))*row427 x y z a w+((1))*row435 x y z a w)=0 := by
  dsimp only [row003,row005,row006,row009,row038,row046,row319,row397,row398,row427,row435]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy435

theorem projection429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift006 x y z a w+(((7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((14*y)/(3*z)))*shift009 x y z a w+(((7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)-(((7*y)/(z))+((-7*x*y*a)/(z))+((-7*x^2*y)/(z)))*w 28=(((7*x^2))*row004 x y z a w+((-7*x*a))*row006 x y z a w+(((-7*x^2*y)/(2*z)))*row007 x y z a w+((7))*row008 x y z a w+(((7*y)/(z))+((-7*x^2*y)/(z)))*row009 x y z a w+(((-14*y)/(z)))*row011 x y z a w+((7*x^2))*row047 x y z a w+(((7*x^2*y)/(z)))*row427 x y z a w+(((7*x^2*y)/(2*z)))*row428 x y z a w+((-7*x^2))*row436 x y z a w) := by
  dsimp only [shift006,shift007,shift008,shift009,shift011,shift043,shift047,row004,row006,row007,row008,row009,row011,row047,row427,row428,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms projection429

theorem projection435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((-28*y)/(3*x^2*z)))*shift009 x y z a w+(((21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)-(((294)/(x^2*z))+((98*y)/(x^2*z)))*w 28=((((42)/(x^2)))*row006 x y z a w+(((28*y)/(x^2*z)))*row009 x y z a w+(((21*x*a)/(y*z)))*row038 x y z a w+(((42)/(x^2*z))+((-2184*a)/(x*y*z))+((-21)/(y*z)))*row319 x y z a w+(((-42)/(x^2)))*row398 x y z a w+(((-126)/(x^2*z))+((-28*y)/(x^2*z)))*row427 x y z a w) := by
  dsimp only [shift003,shift005,shift006,shift009,shift038,shift046,shift397,shift398,row006,row009,row038,row319,row398,row427]
  field_simp [hx,hy,hz]
  ring

#print axioms projection435

theorem residual403 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((1)/(y*z)))*row000 x y z a w+(((1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((1)/(y))+((-1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((-1*x^2)/(z)))*row007 x y z a w+(((2)/(y)))*row008 x y z a w+(((-1)/(z))+((-1*y)/(z))+((-1*x^2)/(z))+((1*x^2*y)/(z)))*row009 x y z a w+(((1*x^2)/(y*z)))*row010 x y z a w+(((-1)/(z))+((-1*y)/(z)))*row011 x y z a w+(((-1*x^2)/(y*z))+((1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((1)/(y))+(1))*row043 x y z a w+(((1)/(y))+((1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((-2)/(y*z))+((1)/(y))+((3)/(z)))*row319 x y z a w+((1))*row387 x y z a w+((-1))*row389 x y z a w+((-2))*row397 x y z a w+((-1))*row398 x y z a w+((1))*row403 x y z a w+((1))*row419 x y z a w+((-1))*row423 x y z a w+(((2)/(z))+(-1)+((1*x^2)/(z))+((-1*x^2*y)/(z)))*row427 x y z a w+(((2*x^2)/(z)))*row428 x y z a w+(((-1*x^2)/(y))+(1*x^2))*row436 x y z a w)=(((-2)/(z))+(-1)+((-1*y)/(z))+((1*x*a)/(z))+((-1*x*y*a)/(z))+((1*x^2)/(z))+((-1*x^2*y)/(z)))*w 28 := by
  dsimp only [row000,row004,row006,row007,row008,row009,row010,row011,row038,row040,row043,row047,row319,row387,row389,row397,row398,row403,row419,row423,row427,row428,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms residual403
end SmallLevelTwentyOneFirstJetCase6
end

section
set_option autoImplicit false
-- Uniform four-variable row interfaces intentionally retain unused arguments.
set_option linter.unusedVariables false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

namespace SmallLevelTwentyOneFirstJetCase7

-- Signs (1, 1, 1). These are algebraic certificates, not yet pole exclusion.
def row000 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0+((-1*x^2*y*z))*w 41)

def row003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(y*z)))*w 0+((1))*w 2)

def row004 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*y)/(x^2*z)))*w 14)

def row005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 4+(((-1*x^2)/(y*z)))*w 21)

def row006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+(((-1*y)/(z)))*w 28)

def row007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+(((-1*z)/(x^2*y)))*w 30)

def row008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 12+(((-1*x^2*y)/(z)))*w 35)

def row009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+(((-1*z)/(y)))*w 36)

def row010 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 21+(((-1*y*z)/(x^2)))*w 38)

def row011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 28+(((-1*x^2*z)/(y)))*w 39)

def row038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-1)/(x^2)))*w 0+((1))*w 21)

def row040 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 20+((-1*x^2))*w 41)

def row043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 18+((-1*x^2))*w 39)

def row046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 23+(((-1)/(x^2)))*w 34)

def row047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 24+((-1))*w 36)

def row319 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 0)

def row388 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 12+((1))*w 26+(((1)/(z)))*w 28)

def row389 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1*x^2)/(z)))*w 7+((1))*w 18+(((1*x^2)/(z)))*w 21+((1))*w 32)

def row397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 8+(((1)/(z)))*w 28+((1))*w 36)

def row398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(z)))*w 0+((1))*w 6+(((1)/(z)))*w 14+((1))*w 34)

def row403 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((1)/(y)))*w 0+(((1)/(y)))*w 6+((1))*w 8+(((1)/(y)))*w 12+((1))*w 14+(((1)/(y)))*w 18+((1))*w 20+(((1)/(y)))*w 24+((1))*w 26+(((1)/(y)))*w 30+((1))*w 32+((1))*w 38)

def row427 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 14+((1))*w 28)

def row428 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 7+((1))*w 35)

def row429 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 6+((1))*w 12+((1))*w 18+((1))*w 24+((1))*w 30+((1))*w 36)

def row435 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 2+(((-1*a)/(x)))*w 4+(((1)/(x^2)))*w 8+((1))*w 23)

def row436 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((1))*w 3+(((-1*a)/(x)))*w 6+(((1)/(x^2)))*w 12+((1))*w 24)

def shift003 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((21)/(y*z)))*w 0)

def shift005 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((21*x^2)/(2*y*z)))*w 21)

def shift006 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((7*y)/(z)))*w 28)

def shift007 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((6*z)/(x^2*y)))*w 30)

def shift008 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((7*x^2*y)/(2*z)))*w 35)

def shift009 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((3*z)/(y)))*w 36)

def shift011 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((3*x^2*z)/(2*y)))*w 39)

def shift038 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-210)/(x^2)))*w 0)

def shift043 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-21*x^2)/(2)))*w 39)

def shift046 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(x^2)))*w 34)

def shift047 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  (((21))*w 36)

def shift397 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((-42)/(z)))*w 0+(((-42)/(z)))*w 28)

def shift398 (x y z a : ℂ) (w : Fin 42 → ℂ) : ℂ :=
  ((((42)/(z)))*w 0+(((42)/(z)))*w 14)

theorem syzygy429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row006 x y z a w+(((1*x^2*y)/(z)))*row007 x y z a w+((-1))*row008 x y z a w+(((2*y)/(z)))*row009 x y z a w+(((1*y)/(z)))*row011 x y z a w+((-1))*row043 x y z a w+((-1))*row047 x y z a w+(((-2*y)/(z)))*row427 x y z a w+(((-1*x^2*y)/(z)))*row428 x y z a w+((1))*row429 x y z a w)=0 := by
  dsimp only [row006,row007,row008,row009,row011,row043,row047,row427,row428,row429]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy429

theorem syzygy435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : (((-1))*row003 x y z a w+(((1*a)/(x)))*row005 x y z a w+(((1)/(x^2)))*row006 x y z a w+(((-1*y)/(x^2*z)))*row009 x y z a w+(((1*x*a)/(y*z)))*row038 x y z a w+((-1))*row046 x y z a w+(((2)/(x^2*z))+((1*a)/(x*y*z))+((-1)/(y*z)))*row319 x y z a w+(((-1)/(x^2)))*row397 x y z a w+(((-1)/(x^2)))*row398 x y z a w+(((1)/(x^2*z))+((1*y)/(x^2*z)))*row427 x y z a w+((1))*row435 x y z a w)=0 := by
  dsimp only [row003,row005,row006,row009,row038,row046,row319,row397,row398,row427,row435]
  field_simp [hx,hy,hz]
  ring

#print axioms syzygy435

theorem projection429 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift006 x y z a w+(((7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((14*y)/(3*z)))*shift009 x y z a w+(((7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)-(((7*y)/(z))+((-7*x*y*a)/(z))+((-7*x^2*y)/(z)))*w 28=(((7*x^2))*row004 x y z a w+((-7*x*a))*row006 x y z a w+(((-7*x^2*y)/(2*z)))*row007 x y z a w+((7))*row008 x y z a w+(((7*y)/(z))+((-7*x^2*y)/(z)))*row009 x y z a w+(((-14*y)/(z)))*row011 x y z a w+((7*x^2))*row047 x y z a w+(((7*x^2*y)/(z)))*row427 x y z a w+(((7*x^2*y)/(2*z)))*row428 x y z a w+((-7*x^2))*row436 x y z a w) := by
  dsimp only [shift006,shift007,shift008,shift009,shift011,shift043,shift047,row004,row006,row007,row008,row009,row011,row047,row427,row428,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms projection429

theorem projection435 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((-28*y)/(3*x^2*z)))*shift009 x y z a w+(((21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)-(((294)/(x^2*z))+((98*y)/(x^2*z)))*w 28=((((42)/(x^2)))*row006 x y z a w+(((28*y)/(x^2*z)))*row009 x y z a w+(((21*x*a)/(y*z)))*row038 x y z a w+(((42)/(x^2*z))+((-2184*a)/(x*y*z))+((-21)/(y*z)))*row319 x y z a w+(((-42)/(x^2)))*row398 x y z a w+(((-126)/(x^2*z))+((-28*y)/(x^2*z)))*row427 x y z a w) := by
  dsimp only [shift003,shift005,shift006,shift009,shift038,shift046,shift397,shift398,row006,row009,row038,row319,row398,row427]
  field_simp [hx,hy,hz]
  ring

#print axioms projection435

theorem residual403 (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) : ((((1)/(y*z)))*row000 x y z a w+(((1*x^2)/(y))+(-1*x^2))*row004 x y z a w+(((-1)/(y))+((-1*x*a)/(y))+(1*x*a))*row006 x y z a w+(((1*x^2)/(z)))*row007 x y z a w+(((1)/(z))+((-1*y)/(z))+((-1*x^2)/(z))+((1*x^2*y)/(z)))*row009 x y z a w+(((1*x^2)/(y*z)))*row010 x y z a w+(((1)/(z))+((-1*y)/(z)))*row011 x y z a w+(((-1*x^2)/(y*z))+((1*x^2)/(z)))*row038 x y z a w+((-1))*row040 x y z a w+(((-1)/(y))+(1))*row043 x y z a w+(((-1)/(y))+((1*x^2)/(y))+(-1*x^2))*row047 x y z a w+(((-2)/(y*z))+((-1)/(y))+((3)/(z)))*row319 x y z a w+((-1))*row388 x y z a w+((-1))*row389 x y z a w+((-1))*row397 x y z a w+((1))*row403 x y z a w+((-1)+((1*x^2)/(z))+((-1*x^2*y)/(z)))*row427 x y z a w+(((-1*x^2)/(y))+(1*x^2))*row436 x y z a w)=((-1)+((-1*y)/(z))+((1*x*a)/(z))+((-1*x*y*a)/(z))+((1*x^2)/(z))+((-1*x^2*y)/(z)))*w 28 := by
  dsimp only [row000,row004,row006,row007,row009,row010,row011,row038,row040,row043,row047,row319,row388,row389,row397,row403,row427,row436]
  field_simp [hx,hy,hz]
  ring

#print axioms residual403
end SmallLevelTwentyOneFirstJetCase7
end
