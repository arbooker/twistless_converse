module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

/-! Consolidated chapter: SmallLevelTwentySixSecondChart. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixSecondChartV1 -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace SmallLevelTwentySixSecondChart
def source0 (u A B Y W z x t : ℂ) : ℂ := (1/2:ℂ)*A*x + (-9/10:ℂ)*x^2 + (-1:ℂ)*A + (13/10:ℂ)*x + (1:ℂ)

def multiplier0 (u A B Y W z x t : ℂ) : ℂ := (26269/124176:ℂ)*A*Y*W*z*x*t + (-62089/62088:ℂ)*A*Y*W*z*t + (619129/620880:ℂ)*A*W*z*x*t + (-114716/38805:ℂ)*Y*W*z*x*t + (-370777/310440:ℂ)*A*W*z*t + (110243/7761:ℂ)*Y*W*z*t + (1375628/194025:ℂ)*W*z*x*t + (-994263/25870:ℂ)*W*z*t

def source1 (u A B Y W z x t : ℂ) : ℂ := (1/4:ℂ)*A*x^2 + (-9/20:ℂ)*x^3 + (-1/4:ℂ)*x^2 + (-1:ℂ)*A + (9/5:ℂ)*x + (1:ℂ)

def multiplier1 (u A B Y W z x t : ℂ) : ℂ := (26269/41392:ℂ)*Y*W*z*x*t + (-62089/20696:ℂ)*Y*W*z*t + (-53277629/1552200:ℂ)*W*z*x*t + (23088409/155220:ℂ)*W*z*t

def source2 (u A B Y W z x t : ℂ) : ℂ := (-1:ℂ)*A^2 + (-1:ℂ)*A*Y + (1:ℂ)*A*x + (1:ℂ)*Y*x + (1:ℂ)*Y + (1:ℂ)*x + (1:ℂ)

def multiplier2 (u A B Y W z x t : ℂ) : ℂ := (1149329/3104400:ℂ)*A*W*z*x^2*t + (-1149329/6208800:ℂ)*W*z*x^3*t + (-2557383/1034800:ℂ)*A*W*z*x*t + (26061413/6208800:ℂ)*W*z*x^2*t + (801511/310440:ℂ)*A*W*z*t + (-3746329/206960:ℂ)*W*z*x*t + (512383/77610:ℂ)*W*z*t

def source3 (u A B Y W z x t : ℂ) : ℂ := (-1/3:ℂ)*A^2 + (-1/3:ℂ)*A*x + (4/3:ℂ)*x^2 + (-2/3:ℂ)*A + (1:ℂ)*x + (1:ℂ)

def multiplier3 (u A B Y W z x t : ℂ) : ℂ := (-1149329/1034800:ℂ)*A*W*z*x^2*t + (-1149329/1034800:ℂ)*Y*W*z*x^2*t + (7672149/1034800:ℂ)*A*W*z*x*t + (33728/4975:ℂ)*Y*W*z*x*t + (-3447987/517400:ℂ)*W*z*x^2*t + (-801511/103480:ℂ)*A*W*z*t + (-245533/51740:ℂ)*Y*W*z*t + (33747437/1034800:ℂ)*W*z*x*t + (-75733/103480:ℂ)*W*z*t

def source4 (u A B Y W z x t : ℂ) : ℂ := (1:ℂ)*x^4 + (-1/2:ℂ)*A*x^2 + (1/2:ℂ)*Y*x^2 + (1:ℂ)*x^3 + (-1:ℂ)*A*Y + (1:ℂ)*Y*x + (3/2:ℂ)*x^2 + (1:ℂ)*Y

def multiplier4 (u A B Y W z x t : ℂ) : ℂ := (2170687/1552200:ℂ)*W*z*x*t + (-5334787/776100:ℂ)*W*z*t

def source5 (u A B Y W z x t : ℂ) : ℂ := (1/18:ℂ)*A*Y*x + (-1/10:ℂ)*Y*x^2 + (-1/9:ℂ)*A*Y + (1/2:ℂ)*A*x + (13/90:ℂ)*Y*x + (-9/10:ℂ)*x^2 + (-1:ℂ)*A + (1/9:ℂ)*Y + (13/10:ℂ)*x + (1:ℂ)

def multiplier5 (u A B Y W z x t : ℂ) : ℂ := (-3447987/206960:ℂ)*W*z*x^2*t + (23016447/206960:ℂ)*W*z*x*t + (-2404533/20696:ℂ)*W*z*t

def source6 (u A B Y W z x t : ℂ) : ℂ := (-1/2:ℂ)*A*x^3 + (-1/2:ℂ)*Y*x^3 + (1:ℂ)*x^4 + (-1:ℂ)*A*x^2 + (1:ℂ)*Y*x^2 + (3/2:ℂ)*x^3 + (-1:ℂ)*A*Y + (-1:ℂ)*A*x + (1:ℂ)*Y*x + (2:ℂ)*x^2 + (1:ℂ)*Y + (1:ℂ)*x

def multiplier6 (u A B Y W z x t : ℂ) : ℂ := (-26269/119400:ℂ)*W*z*x*t + (62089/59700:ℂ)*W*z*t

def source7 (u A B Y W z x t : ℂ) : ℂ := (-7/4:ℂ)*A*x^3 + (7/2:ℂ)*x^4 + (-5/4:ℂ)*A*Y*x + (29/8:ℂ)*A*x^2 + (7/4:ℂ)*Y*x^2 + (-57/8:ℂ)*x^3 + (-1:ℂ)*A*Y + (25/4:ℂ)*A*x + (9/4:ℂ)*Y*x + (-23/8:ℂ)*x^2 + (1:ℂ)*Y + (-25/4:ℂ)*x

def multiplier7 (u A B Y W z x t : ℂ) : ℂ := (-229432/194025:ℂ)*W*z*x*t + (220486/38805:ℂ)*W*z*t

def source32 (u A B Y W z x t : ℂ) : ℂ := (-9/31146314301440:ℂ)*A^2*x + (-9/31146314301440:ℂ)*A*x^2 + (9/7786578575360:ℂ)*x^3 + (-9/15573157150720:ℂ)*A*x + (27/31146314301440:ℂ)*x^2 + (27/31146314301440:ℂ)*x

def multiplier32 (u A B Y W z x t : ℂ) : ℂ := (1966784928808960/5373:ℂ)*Y*W*z*x*t + (17210270321999872/5373:ℂ)*W*z*x^2*t + (-9297324560875520/5373:ℂ)*Y*W*z*t + (-105613258506895360/5373:ℂ)*W*z*x*t + (108915606377463808/5373:ℂ)*W*z*t

def source51 (u A B Y W z x t : ℂ) : ℂ := (1/62292628602880:ℂ)*A*Y*x^2 + (-9/311463143014400:ℂ)*Y*x^3 + (-1/31146314301440:ℂ)*A*Y*x + (81/62292628602880:ℂ)*A*x^2 + (1/23958703308800:ℂ)*Y*x^2 + (-729/311463143014400:ℂ)*x^3 + (-81/31146314301440:ℂ)*A*x + (1/31146314301440:ℂ)*Y*x + (81/23958703308800:ℂ)*x^2 + (81/31146314301440:ℂ)*x

def multiplier51 (u A B Y W z x t : ℂ) : ℂ := (2106495225568428032/80595:ℂ)*W*z*x*t + (-10471419438897823744/80595:ℂ)*W*z*t

def source62 (u A B Y W z x t : ℂ) : ℂ := (1/62292628602880:ℂ)*A*Y*x^2 + (-9/311463143014400:ℂ)*Y*x^3 + (-1/31146314301440:ℂ)*A*Y*x + (27/31146314301440:ℂ)*A*x^2 + (1/23958703308800:ℂ)*Y*x^2 + (-243/155731571507200:ℂ)*x^3 + (-27/15573157150720:ℂ)*A*x + (1/31146314301440:ℂ)*Y*x + (27/11979351654400:ℂ)*x^2 + (27/15573157150720:ℂ)*x

def multiplier62 (u A B Y W z x t : ℂ) : ℂ := (-2106495225568428032/80595:ℂ)*W*z*x*t + (10471419438897823744/80595:ℂ)*W*z*t

def source65 (u A B Y W z x t : ℂ) : ℂ := (27/31146314301440:ℂ)*A*x^2 + (-243/155731571507200:ℂ)*x^3 + (-27/15573157150720:ℂ)*A*x + (27/11979351654400:ℂ)*x^2 + (27/15573157150720:ℂ)*x

def multiplier65 (u A B Y W z x t : ℂ) : ℂ := (2556820407451648/16119:ℂ)*Y*W*z*x*t + (851672005869568/1791:ℂ)*W*z*x^2*t + (-12086521929138176/16119:ℂ)*Y*W*z*t + (32444172233867264/8955:ℂ)*W*z*x*t + (-644161214203559936/26865:ℂ)*W*z*t

def source86 (u A B Y W z x t : ℂ) : ℂ := (1:ℂ)*Y*W*z*x*t + (-1:ℂ)

def multiplier86 (u A B Y W z x t : ℂ) : ℂ := (-1:ℂ)

/-- Exact polynomial ideal-membership identity, checked by Lean. -/
theorem unit_identity (u A B Y W z x t : ℂ) :
    multiplier0 u A B Y W z x t*source0 u A B Y W z x t +
    multiplier1 u A B Y W z x t*source1 u A B Y W z x t +
    multiplier2 u A B Y W z x t*source2 u A B Y W z x t +
    multiplier3 u A B Y W z x t*source3 u A B Y W z x t +
    multiplier4 u A B Y W z x t*source4 u A B Y W z x t +
    multiplier5 u A B Y W z x t*source5 u A B Y W z x t +
    multiplier6 u A B Y W z x t*source6 u A B Y W z x t +
    multiplier7 u A B Y W z x t*source7 u A B Y W z x t +
    multiplier32 u A B Y W z x t*source32 u A B Y W z x t +
    multiplier51 u A B Y W z x t*source51 u A B Y W z x t +
    multiplier62 u A B Y W z x t*source62 u A B Y W z x t +
    multiplier65 u A B Y W z x t*source65 u A B Y W z x t +
    multiplier86 u A B Y W z x t*source86 u A B Y W z x t=1 := by
  unfold source0 multiplier0 source1 multiplier1 source2 multiplier2 source3 multiplier3 source4 multiplier4 source5 multiplier5 source6 multiplier6 source7 multiplier7 source32 multiplier32 source51 multiplier51 source62 multiplier62 source65 multiplier65 source86 multiplier86
  ring

/-- Finite chart exclusion; the original-germ source linkage is separate. -/
theorem no_common_zero (u A B Y W z x t : ℂ)
    (h0 : source0 u A B Y W z x t=0)
    (h1 : source1 u A B Y W z x t=0)
    (h2 : source2 u A B Y W z x t=0)
    (h3 : source3 u A B Y W z x t=0)
    (h4 : source4 u A B Y W z x t=0)
    (h5 : source5 u A B Y W z x t=0)
    (h6 : source6 u A B Y W z x t=0)
    (h7 : source7 u A B Y W z x t=0)
    (h32 : source32 u A B Y W z x t=0)
    (h51 : source51 u A B Y W z x t=0)
    (h62 : source62 u A B Y W z x t=0)
    (h65 : source65 u A B Y W z x t=0)
    (h86 : source86 u A B Y W z x t=0)
    : False := by
  have hh:=unit_identity u A B Y W z x t
  rw [h0,h1,h2,h3,h4,h5,h6,h7,h32,h51,h62,h65,h86] at hh
  norm_num at hh

#print axioms unit_identity
#print axioms no_common_zero
end SmallLevelTwentySixSecondChart
end
end

/-! ## SmallLevelTwentySixSecondChartReducedV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixSecondChart
open Complex

/-- Only the first eight top-column constraints are needed. The additional
four constraints in the saved certificate are polynomial multiples of these. -/
theorem no_first_eight (A Y x : ℂ) (hx : x≠0) (hy : Y≠0)
    (h0 : source0 0 A 0 Y 1 1 x 0=0)
    (h1 : source1 0 A 0 Y 1 1 x 0=0)
    (h2 : source2 0 A 0 Y 1 1 x 0=0)
    (h3 : source3 0 A 0 Y 1 1 x 0=0)
    (h4 : source4 0 A 0 Y 1 1 x 0=0)
    (h5 : source5 0 A 0 Y 1 1 x 0=0)
    (h6 : source6 0 A 0 Y 1 1 x 0=0)
    (h7 : source7 0 A 0 Y 1 1 x 0=0)
    : False := by
  apply no_common_zero 0 A 0 Y 1 1 x (1/(x*Y))
  · simpa only [source0] using h0
  · simpa only [source1] using h1
  · simpa only [source2] using h2
  · simpa only [source3] using h3
  · simpa only [source4] using h4
  · simpa only [source5] using h5
  · simpa only [source6] using h6
  · simpa only [source7] using h7
  · calc
      source32 0 A 0 Y 1 1 x (1/(x*Y))=(27*x/31146314301440)*source3 0 A 0 Y 1 1 x 0 := by
        unfold source32 source3
        ring
      _=0 := by rw [h3,mul_zero]
  · calc
      source51 0 A 0 Y 1 1 x (1/(x*Y))=(x*(Y+81)/31146314301440)*source0 0 A 0 Y 1 1 x 0 := by
        unfold source51 source0
        ring
      _=0 := by rw [h0,mul_zero]
  · calc
      source62 0 A 0 Y 1 1 x (1/(x*Y))=(x*(Y+54)/31146314301440)*source0 0 A 0 Y 1 1 x 0 := by
        unfold source62 source0
        ring
      _=0 := by rw [h0,mul_zero]
  · calc
      source65 0 A 0 Y 1 1 x (1/(x*Y))=(27*x/15573157150720)*source0 0 A 0 Y 1 1 x 0 := by
        unfold source65 source0
        ring
      _=0 := by rw [h0,mul_zero]
  · norm_num only [source86,zero_pow,one_pow,mul_one,one_mul]
    field_simp [hx,hy]
    norm_num

#print axioms no_first_eight
end SmallLevelTwentySixSecondChart
end
end
