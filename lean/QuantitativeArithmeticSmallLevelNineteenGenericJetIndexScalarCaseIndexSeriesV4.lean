module
public import QuantitativeArithmeticSmallLevelNineteenPoleLeadingTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenGenericCertificatesInputBundleV4
public import QuantitativeArithmeticSmallLevelNineteenGenericJet109IdentityCase0V1
public import QuantitativeArithmeticSmallLevelNineteenGenericJet115IdentityCase0V1
public import QuantitativeArithmeticSmallLevelNineteenGenericJet200IdentityCase2V1
public import QuantitativeArithmeticSmallLevelNineteenGenericJet201IdentityCase2V1
public import QuantitativeArithmeticSmallLevelNineteenGenericJet202IdentityCase2V1
public import QuantitativeArithmeticSmallLevelNineteenGenericJet39IdentityCase0V1
public import QuantitativeArithmeticSmallLevelNineteenGenericJet41IdentityCase0V1
public import QuantitativeArithmeticSmallLevelNineteenGenericJet43IdentityCase0V1
public import QuantitativeArithmeticSmallLevelNineteenOppositeCertificatesInputBundleV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet109
open QuantitativeArithmeticSmallLevelNineteenPoleLeading
open QuantitativeArithmeticSmallLevelNineteenFullSystem
/-- Input9 of the published equal-sign generic certificate. -/
def compact109 (B A Z Y X : ℂ) : ℂ := QuantitativeArithmeticSmallLevelNineteenGenericCertificates.poly9 B A Z Y X

theorem output_contraction (x y z a b t : ℂ)
    (hx : x≠0) (hy : y≠0) (ha : a≠0) (v : Fin 114→ℂ)
    (hw : v 18= -(x^4+(a^2-2)*x^2+1)*t)
    (hu : v 42=x*a*(y^2+1)*t) (hl : v 72= -x*a*(y^2+1)*t) :
    output0 x y z a b v = ((10944:ℂ)/(x^5*y^2*a))*compact109 (b*y) (a*x) z (y^2) (x^2)*t := by
  unfold output0 compact109 QuantitativeArithmeticSmallLevelNineteenGenericCertificates.poly9
  rw [hw,hu,hl]
  field_simp [hx,hy,ha]
  <;> ring1

/-- Combine the actual leading rows with this first-Taylor output. -/
theorem scalar_zero_of_output (x y z a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (ha : a≠0)
    (hx4 : x^4≠1) (hY : y^2+1≠0) (hgap : a= -x-1/x ∨ x^2+a*x+1≠0)
    (v : Fin 114→ℂ) (hvn : v≠0)
    (hv : symbolicRows (-1) (-1) x y z a b v=0)
    (hout : output0 x y z a b v=0) : compact109 (b*y) (a*x) z (y^2) (x^2)=0 := by
  obtain ⟨hr,hinj⟩ := actual_symbolic_kernel_reduce0 x y z a b hx hy hz ha v hv
  obtain ⟨h72,hrow⟩ := leading_coordinates_gap0 x y z a b hx hy ha hx4 hgap v hr
  have hK : x*a*(y^2+1)≠0 := mul_ne_zero (mul_ne_zero hx ha) hY
  let t : ℂ := v 42/(x*a*(y^2+1))
  have hu : v 42=x*a*(y^2+1)*t := by dsimp [t]; field_simp
  have hw : v 18= -(x^4+(a^2-2)*x^2+1)*t := by
    apply mul_left_cancel₀ hK
    linear_combination hrow-(x^4+(a^2-2)*x^2+1)*hu
  have hlast : v 72= -x*a*(y^2+1)*t := by rw [h72,hu]; ring
  have ht : t≠0 := by
    intro he
    apply hvn
    apply hinj
    · simpa [he] using hw
    · simpa [he] using hu
    · simpa [he] using hlast
  have he := output_contraction x y z a b t hx hy ha v hw hu hlast
  rw [hout] at he
  have hc : ((10944:ℂ)/(x^5*y^2*a))≠0 := by
    simp [div_ne_zero_iff,mul_ne_zero_iff,hx,hy,ha]
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right ht)).resolve_left hc

#print axioms output_contraction
#print axioms scalar_zero_of_output
end QuantitativeArithmeticSmallLevelNineteenGenericJet109
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet115
open QuantitativeArithmeticSmallLevelNineteenPoleLeading
open QuantitativeArithmeticSmallLevelNineteenFullSystem
/-- Input15 of the published equal-sign generic certificate. -/
def compact115 (B A Z Y X : ℂ) : ℂ := QuantitativeArithmeticSmallLevelNineteenGenericCertificates.poly15 B A Z Y X

theorem output_contraction (x y z a b t : ℂ)
    (hx : x≠0) (hy : y≠0) (ha : a≠0) (v : Fin 114→ℂ)
    (hw : v 18= -(x^4+(a^2-2)*x^2+1)*t)
    (hu : v 42=x*a*(y^2+1)*t) (hl : v 72= -x*a*(y^2+1)*t) :
    output0 x y z a b v = ((98496:ℂ)/(x^7*y^4*a))*compact115 (b*y) (a*x) z (y^2) (x^2)*t := by
  unfold output0 compact115 QuantitativeArithmeticSmallLevelNineteenGenericCertificates.poly15
  rw [hw,hu,hl]
  field_simp [hx,hy,ha]
  <;> ring1

/-- Combine the actual leading rows with this first-Taylor output. -/
theorem scalar_zero_of_output (x y z a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (ha : a≠0)
    (hx4 : x^4≠1) (hY : y^2+1≠0) (hgap : a= -x-1/x ∨ x^2+a*x+1≠0)
    (v : Fin 114→ℂ) (hvn : v≠0)
    (hv : symbolicRows (-1) (-1) x y z a b v=0)
    (hout : output0 x y z a b v=0) : compact115 (b*y) (a*x) z (y^2) (x^2)=0 := by
  obtain ⟨hr,hinj⟩ := actual_symbolic_kernel_reduce0 x y z a b hx hy hz ha v hv
  obtain ⟨h72,hrow⟩ := leading_coordinates_gap0 x y z a b hx hy ha hx4 hgap v hr
  have hK : x*a*(y^2+1)≠0 := mul_ne_zero (mul_ne_zero hx ha) hY
  let t : ℂ := v 42/(x*a*(y^2+1))
  have hu : v 42=x*a*(y^2+1)*t := by dsimp [t]; field_simp
  have hw : v 18= -(x^4+(a^2-2)*x^2+1)*t := by
    apply mul_left_cancel₀ hK
    linear_combination hrow-(x^4+(a^2-2)*x^2+1)*hu
  have hlast : v 72= -x*a*(y^2+1)*t := by rw [h72,hu]; ring
  have ht : t≠0 := by
    intro he
    apply hvn
    apply hinj
    · simpa [he] using hw
    · simpa [he] using hu
    · simpa [he] using hlast
  have he := output_contraction x y z a b t hx hy ha v hw hu hlast
  rw [hout] at he
  have hc : ((98496:ℂ)/(x^7*y^4*a))≠0 := by
    simp [div_ne_zero_iff,mul_ne_zero_iff,hx,hy,ha]
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right ht)).resolve_left hc

#print axioms output_contraction
#print axioms scalar_zero_of_output
end QuantitativeArithmeticSmallLevelNineteenGenericJet115
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet200
open QuantitativeArithmeticSmallLevelNineteenPoleLeading
open QuantitativeArithmeticSmallLevelNineteenFullSystem
/-- Opposite-sign compact input 3. -/
def compact200 (B A Z Y X : ℂ) : ℂ := QuantitativeArithmeticSmallLevelNineteenOppositeCertificates.poly3 B A Z Y X

theorem output_contraction (x y z a b t : ℂ)
    (hx : x≠0) (hy : y≠0) (ha : a≠0) (v : Fin 114→ℂ)
    (hw : v 18= -(x^4+(a^2-2)*x^2+1)*t)
    (hu : v 42=x*a*(y^2+1)*t) (hl : v 72= -x*a*(y^2+1)*t) :
    output2 x y z a b v = ((-19:ℂ)/x^2)*compact200 (b*y) (a*x) z (y^2) (x^2)*t := by
  unfold output2 compact200 QuantitativeArithmeticSmallLevelNineteenOppositeCertificates.poly3
  rw [hw,hu,hl]
  field_simp [hx,hy,ha]
  <;> ring1

/-- Combine the actual leading rows with this first-Taylor output. -/
theorem scalar_zero_of_output (x y z a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (ha : a≠0)
    (hx4 : x^4≠1) (hY : y^2+1≠0) (hgap : a= -x-1/x ∨ x^2+a*x+1≠0)
    (v : Fin 114→ℂ) (hvn : v≠0)
    (hv : symbolicRows (-1) 1 x y z a b v=0)
    (hout : output2 x y z a b v=0) : compact200 (b*y) (a*x) z (y^2) (x^2)=0 := by
  obtain ⟨hr,hinj⟩ := actual_symbolic_kernel_reduce2 x y z a b hx hy hz ha v hv
  obtain ⟨h72,hrow⟩ := leading_coordinates_gap2 x y z a b hx hy ha hx4 hgap v hr
  have hK : x*a*(y^2+1)≠0 := mul_ne_zero (mul_ne_zero hx ha) hY
  let t : ℂ := v 42/(x*a*(y^2+1))
  have hu : v 42=x*a*(y^2+1)*t := by dsimp [t]; field_simp
  have hw : v 18= -(x^4+(a^2-2)*x^2+1)*t := by
    apply mul_left_cancel₀ hK
    linear_combination hrow-(x^4+(a^2-2)*x^2+1)*hu
  have hlast : v 72= -x*a*(y^2+1)*t := by rw [h72,hu]; ring
  have ht : t≠0 := by
    intro he
    apply hvn
    apply hinj
    · simpa [he] using hw
    · simpa [he] using hu
    · simpa [he] using hlast
  have he := output_contraction x y z a b t hx hy ha v hw hu hlast
  rw [hout] at he
  have hc : ((-19:ℂ)/x^2)≠0 := by
    simp [div_ne_zero_iff,mul_ne_zero_iff,hx,hy,ha]
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right ht)).resolve_left hc

#print axioms output_contraction
#print axioms scalar_zero_of_output
end QuantitativeArithmeticSmallLevelNineteenGenericJet200
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet201
open QuantitativeArithmeticSmallLevelNineteenPoleLeading
open QuantitativeArithmeticSmallLevelNineteenFullSystem
/-- Opposite-sign compact input 4. -/
def compact201 (B A Z Y X : ℂ) : ℂ := QuantitativeArithmeticSmallLevelNineteenOppositeCertificates.poly4 B A Z Y X

theorem output_contraction (x y z a b t : ℂ)
    (hx : x≠0) (hy : y≠0) (ha : a≠0) (v : Fin 114→ℂ)
    (hw : v 18= -(x^4+(a^2-2)*x^2+1)*t)
    (hu : v 42=x*a*(y^2+1)*t) (hl : v 72= -x*a*(y^2+1)*t) :
    output2 x y z a b v = ((228:ℂ)/(x^2*y^2))*compact201 (b*y) (a*x) z (y^2) (x^2)*t := by
  unfold output2 compact201 QuantitativeArithmeticSmallLevelNineteenOppositeCertificates.poly4
  rw [hw,hu,hl]
  field_simp [hx,hy,ha]
  <;> ring1

/-- Combine the actual leading rows with this first-Taylor output. -/
theorem scalar_zero_of_output (x y z a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (ha : a≠0)
    (hx4 : x^4≠1) (hY : y^2+1≠0) (hgap : a= -x-1/x ∨ x^2+a*x+1≠0)
    (v : Fin 114→ℂ) (hvn : v≠0)
    (hv : symbolicRows (-1) 1 x y z a b v=0)
    (hout : output2 x y z a b v=0) : compact201 (b*y) (a*x) z (y^2) (x^2)=0 := by
  obtain ⟨hr,hinj⟩ := actual_symbolic_kernel_reduce2 x y z a b hx hy hz ha v hv
  obtain ⟨h72,hrow⟩ := leading_coordinates_gap2 x y z a b hx hy ha hx4 hgap v hr
  have hK : x*a*(y^2+1)≠0 := mul_ne_zero (mul_ne_zero hx ha) hY
  let t : ℂ := v 42/(x*a*(y^2+1))
  have hu : v 42=x*a*(y^2+1)*t := by dsimp [t]; field_simp
  have hw : v 18= -(x^4+(a^2-2)*x^2+1)*t := by
    apply mul_left_cancel₀ hK
    linear_combination hrow-(x^4+(a^2-2)*x^2+1)*hu
  have hlast : v 72= -x*a*(y^2+1)*t := by rw [h72,hu]; ring
  have ht : t≠0 := by
    intro he
    apply hvn
    apply hinj
    · simpa [he] using hw
    · simpa [he] using hu
    · simpa [he] using hlast
  have he := output_contraction x y z a b t hx hy ha v hw hu hlast
  rw [hout] at he
  have hc : ((228:ℂ)/(x^2*y^2))≠0 := by
    simp [div_ne_zero_iff,mul_ne_zero_iff,hx,hy,ha]
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right ht)).resolve_left hc

#print axioms output_contraction
#print axioms scalar_zero_of_output
end QuantitativeArithmeticSmallLevelNineteenGenericJet201
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet202
open QuantitativeArithmeticSmallLevelNineteenPoleLeading
open QuantitativeArithmeticSmallLevelNineteenFullSystem
/-- Opposite-sign compact input 5. -/
def compact202 (B A Z Y X : ℂ) : ℂ := QuantitativeArithmeticSmallLevelNineteenOppositeCertificates.poly5 B A Z Y X

theorem output_contraction (x y z a b t : ℂ)
    (hx : x≠0) (hy : y≠0) (ha : a≠0) (v : Fin 114→ℂ)
    (hw : v 18= -(x^4+(a^2-2)*x^2+1)*t)
    (hu : v 42=x*a*(y^2+1)*t) (hl : v 72= -x*a*(y^2+1)*t) :
    output2 x y z a b v = ((4256:ℂ)/(9*x^2*y^2))*compact202 (b*y) (a*x) z (y^2) (x^2)*t := by
  unfold output2 compact202 QuantitativeArithmeticSmallLevelNineteenOppositeCertificates.poly5
  rw [hw,hu,hl]
  field_simp [hx,hy,ha]
  <;> ring1

/-- Combine the actual leading rows with this first-Taylor output. -/
theorem scalar_zero_of_output (x y z a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (ha : a≠0)
    (hx4 : x^4≠1) (hY : y^2+1≠0) (hgap : a= -x-1/x ∨ x^2+a*x+1≠0)
    (v : Fin 114→ℂ) (hvn : v≠0)
    (hv : symbolicRows (-1) 1 x y z a b v=0)
    (hout : output2 x y z a b v=0) : compact202 (b*y) (a*x) z (y^2) (x^2)=0 := by
  obtain ⟨hr,hinj⟩ := actual_symbolic_kernel_reduce2 x y z a b hx hy hz ha v hv
  obtain ⟨h72,hrow⟩ := leading_coordinates_gap2 x y z a b hx hy ha hx4 hgap v hr
  have hK : x*a*(y^2+1)≠0 := mul_ne_zero (mul_ne_zero hx ha) hY
  let t : ℂ := v 42/(x*a*(y^2+1))
  have hu : v 42=x*a*(y^2+1)*t := by dsimp [t]; field_simp
  have hw : v 18= -(x^4+(a^2-2)*x^2+1)*t := by
    apply mul_left_cancel₀ hK
    linear_combination hrow-(x^4+(a^2-2)*x^2+1)*hu
  have hlast : v 72= -x*a*(y^2+1)*t := by rw [h72,hu]; ring
  have ht : t≠0 := by
    intro he
    apply hvn
    apply hinj
    · simpa [he] using hw
    · simpa [he] using hu
    · simpa [he] using hlast
  have he := output_contraction x y z a b t hx hy ha v hw hu hlast
  rw [hout] at he
  have hc : ((4256:ℂ)/(9*x^2*y^2))≠0 := by
    simp [div_ne_zero_iff,mul_ne_zero_iff,hx,hy,ha]
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right ht)).resolve_left hc

#print axioms output_contraction
#print axioms scalar_zero_of_output
end QuantitativeArithmeticSmallLevelNineteenGenericJet202
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet39
open QuantitativeArithmeticSmallLevelNineteenPoleLeading
open QuantitativeArithmeticSmallLevelNineteenFullSystem
/-- Input17 of the published equal-sign generic certificate. -/
def compact39 (B A Z Y X : ℂ) : ℂ := (((((((6:ℂ)*B*A^4*X^2 + ((2:ℂ)*A^4*Y*X^2 + (6:ℂ)*B*A^3*X^3)) + ((3:ℂ)*A^3*Y*X^3 + ((6:ℂ)*B*A^2*X^4 + (3:ℂ)*A^2*Y*X^4))) + (((6:ℂ)*B*A*X^5 + ((3:ℂ)*A*Y*X^5 + (1:ℂ)*Y*X^6)) + ((6:ℂ)*B*A^5 + ((2:ℂ)*A^5*Y + (6:ℂ)*B*A^4*X)))) + ((((-6:ℂ)*B*A^3*Y*X + ((3:ℂ)*A^4*Y*X + (-2:ℂ)*A^3*Y^2*X)) + ((12:ℂ)*B*A^3*X^2 + ((9:ℂ)*A^3*Y*X^2 + (-1:ℂ)*A^2*Y^2*X^2))) + (((-6:ℂ)*B*A^2*X^3 + ((-9:ℂ)*A^3*X^3 + (4:ℂ)*A^2*Y*X^3)) + ((-6:ℂ)*B*A*X^4 + ((-9:ℂ)*A^2*X^4 + (1:ℂ)*A*Y*X^4))))) + (((((-9:ℂ)*A*X^5 + ((3:ℂ)*Y*X^5 + (-9:ℂ)*X^6)) + ((2:ℂ)*B*A^4 + ((-6:ℂ)*B*A^3*Y + (6:ℂ)*A^4*Y))) + (((-2:ℂ)*A^3*Y^2 + ((-22:ℂ)*B*A^3*X + (-9:ℂ)*A^4*X)) + ((6:ℂ)*B^2*A*Y*X + ((-1:ℂ)*A^3*Y*X + (2:ℂ)*B*A*Y^2*X)))) + ((((-5:ℂ)*A^2*Y^2*X + ((-4:ℂ)*B*A^2*X^2 + (-45:ℂ)*A^3*X^2)) + ((14:ℂ)*A^2*Y*X^2 + ((1:ℂ)*B*Y^2*X^2 + (-10:ℂ)*B*A*X^3))) + (((-54:ℂ)*A^2*X^3 + ((-6:ℂ)*A*Y*X^3 + (-27:ℂ)*A*X^4)) + ((-5:ℂ)*Y*X^4 + ((-27:ℂ)*X^5 + (10:ℂ)*B*A^3)))))) + ((((((-72:ℂ)*A^4 + ((-6:ℂ)*B^2*A*Y + (-12:ℂ)*B*A^2*Y)) + ((6:ℂ)*A^3*Y + ((-2:ℂ)*B*A*Y^2 + (-8:ℂ)*A^2*Y^2))) + (((6:ℂ)*B^2*A*X + ((2:ℂ)*B*A^2*X + (-93:ℂ)*A^3*X)) + ((8:ℂ)*B*A*Y*X + ((32:ℂ)*A^2*Y*X + (3:ℂ)*B*Y^2*X)))) + ((((24:ℂ)*B*A*X^2 + ((-93:ℂ)*A^2*X^2 + (-8:ℂ)*B*Y*X^2)) + ((3:ℂ)*A*Y*X^2 + ((1:ℂ)*Y^2*X^2 + (-12:ℂ)*A*X^3))) + (((-2:ℂ)*Y*X^3 + ((33:ℂ)*X^4 + (-6:ℂ)*B^2*A)) + ((-10:ℂ)*B*A^2 + ((-120:ℂ)*A^3 + (16:ℂ)*B*A*Y))))) + (((((38:ℂ)*A^2*Y + ((-4:ℂ)*B*Y^2 + (-10:ℂ)*A*Y^2)) + ((-18:ℂ)*B*A*X + ((99:ℂ)*A^2*X + (-24:ℂ)*B*Y*X))) + (((35:ℂ)*A*Y*X + ((3:ℂ)*Y^2*X + (-9:ℂ)*B*X^2)) + ((21:ℂ)*A*X^2 + ((10:ℂ)*Y*X^2 + (-30:ℂ)*X^3)))) + ((((28:ℂ)*B*A + ((-168:ℂ)*A^2 + (32:ℂ)*B*Y)) + ((116:ℂ)*A*Y + ((-4:ℂ)*Y^2 + (-27:ℂ)*B*X))) + (((189:ℂ)*A*X + ((5:ℂ)*Y*X + (-15:ℂ)*X^2)) + (((36:ℂ)*B + (-12:ℂ)*Y) + ((192:ℂ)*X + (-144:ℂ))))))))

theorem output_contraction (x y z a b t : ℂ)
    (hx : x≠0) (hy : y≠0) (ha : a≠0) (v : Fin 114→ℂ)
    (hw : v 18= -(x^4+(a^2-2)*x^2+1)*t)
    (hu : v 42=x*a*(y^2+1)*t) (hl : v 72= -x*a*(y^2+1)*t) :
    output0 x y z a b v = ((-1539/64:ℂ)*x^7*y^4*a)*compact39 (b*y) (a*x) z (y^2) (x^2)*t := by
  unfold output0 compact39
  rw [hw,hu,hl]
  field_simp [hx,hy,ha]
  <;> ring1

/-- Combine the actual leading rows with this first-Taylor output. -/
theorem scalar_zero_of_output (x y z a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (ha : a≠0)
    (hx4 : x^4≠1) (hY : y^2+1≠0) (hgap : a= -x-1/x ∨ x^2+a*x+1≠0)
    (v : Fin 114→ℂ) (hvn : v≠0)
    (hv : symbolicRows (-1) (-1) x y z a b v=0)
    (hout : output0 x y z a b v=0) : compact39 (b*y) (a*x) z (y^2) (x^2)=0 := by
  obtain ⟨hr,hinj⟩ := actual_symbolic_kernel_reduce0 x y z a b hx hy hz ha v hv
  obtain ⟨h72,hrow⟩ := leading_coordinates_gap0 x y z a b hx hy ha hx4 hgap v hr
  have hK : x*a*(y^2+1)≠0 := mul_ne_zero (mul_ne_zero hx ha) hY
  let t : ℂ := v 42/(x*a*(y^2+1))
  have hu : v 42=x*a*(y^2+1)*t := by dsimp [t]; field_simp
  have hw : v 18= -(x^4+(a^2-2)*x^2+1)*t := by
    apply mul_left_cancel₀ hK
    linear_combination hrow-(x^4+(a^2-2)*x^2+1)*hu
  have hlast : v 72= -x*a*(y^2+1)*t := by rw [h72,hu]; ring
  have ht : t≠0 := by
    intro he
    apply hvn
    apply hinj
    · simpa [he] using hw
    · simpa [he] using hu
    · simpa [he] using hlast
  have he := output_contraction x y z a b t hx hy ha v hw hu hlast
  rw [hout] at he
  have hc : ((-1539/64:ℂ)*x^7*y^4*a)≠0 := by
    simp [mul_ne_zero_iff,hx,hy,ha]
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right ht)).resolve_left hc

#print axioms output_contraction
#print axioms scalar_zero_of_output
end QuantitativeArithmeticSmallLevelNineteenGenericJet39
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet41
open QuantitativeArithmeticSmallLevelNineteenPoleLeading
open QuantitativeArithmeticSmallLevelNineteenFullSystem
/-- Input18 of the published equal-sign generic certificate. -/
def compact41 (B A Z Y X : ℂ) : ℂ := ((((((-2:ℂ)*A^4*X^2 + (-1:ℂ)*A^3*X^3) + ((-1:ℂ)*A^2*X^4 + ((-1:ℂ)*A*X^5 + (1:ℂ)*X^6))) + (((-2:ℂ)*A^5 + ((-1:ℂ)*A^4*X + (2:ℂ)*A^3*Y*X)) + ((1:ℂ)*A^3*X^2 + ((-1:ℂ)*A^2*Y*X^2 + (8:ℂ)*A^2*X^3)))) + ((((5:ℂ)*A*X^4 + ((3:ℂ)*X^5 + ((10:ℂ)/3)*A^4)) + ((2:ℂ)*A^3*Y + (((35:ℂ)/3)*A^3*X + (-2:ℂ)*B*A*Y*X))) + (((-5:ℂ)*A^2*Y*X + (((17:ℂ)/3)*A^2*X^2 + (1:ℂ)*B*Y*X^2)) + (((-4:ℂ)/3)*A*X^3 + (((-17:ℂ)/3)*X^4 + (-2:ℂ)*A^3))))) + (((((2:ℂ)*B*A*Y + ((56:ℂ)/27)*A^2*Y) + ((-2:ℂ)*B*A*X + (((-41:ℂ)/3)*A^2*X + (3:ℂ)*B*Y*X))) + (((-4:ℂ)*A*Y*X + ((1:ℂ)*B*X^2 + ((-31:ℂ)/3)*A*X^2)) + (((-25:ℂ)/27)*Y*X^2 + (((-8:ℂ)/3)*X^3 + (2:ℂ)*B*A)))) + (((((70:ℂ)/3)*A^2 + ((-4:ℂ)*B*Y + (-14:ℂ)*A*Y)) + ((3:ℂ)*B*X + (((17:ℂ)/3)*A*X + ((77:ℂ)/27)*Y*X))) + ((((67:ℂ)/3)*X^2 + ((-4:ℂ)*B + (-16:ℂ)*A)) + (((-52:ℂ)/27)*Y + ((-34:ℂ)*X + (16:ℂ)))))))

theorem output_contraction (x y z a b t : ℂ)
    (hx : x≠0) (hy : y≠0) (ha : a≠0) (v : Fin 114→ℂ)
    (hw : v 18= -(x^4+(a^2-2)*x^2+1)*t)
    (hu : v 42=x*a*(y^2+1)*t) (hl : v 72= -x*a*(y^2+1)*t) :
    output0 x y z a b v = ((13851/256:ℂ)*x^7*y^4*a)*compact41 (b*y) (a*x) z (y^2) (x^2)*t := by
  unfold output0 compact41
  rw [hw,hu,hl]
  field_simp [hx,hy,ha]
  <;> ring1

/-- Combine the actual leading rows with this first-Taylor output. -/
theorem scalar_zero_of_output (x y z a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (ha : a≠0)
    (hx4 : x^4≠1) (hY : y^2+1≠0) (hgap : a= -x-1/x ∨ x^2+a*x+1≠0)
    (v : Fin 114→ℂ) (hvn : v≠0)
    (hv : symbolicRows (-1) (-1) x y z a b v=0)
    (hout : output0 x y z a b v=0) : compact41 (b*y) (a*x) z (y^2) (x^2)=0 := by
  obtain ⟨hr,hinj⟩ := actual_symbolic_kernel_reduce0 x y z a b hx hy hz ha v hv
  obtain ⟨h72,hrow⟩ := leading_coordinates_gap0 x y z a b hx hy ha hx4 hgap v hr
  have hK : x*a*(y^2+1)≠0 := mul_ne_zero (mul_ne_zero hx ha) hY
  let t : ℂ := v 42/(x*a*(y^2+1))
  have hu : v 42=x*a*(y^2+1)*t := by dsimp [t]; field_simp
  have hw : v 18= -(x^4+(a^2-2)*x^2+1)*t := by
    apply mul_left_cancel₀ hK
    linear_combination hrow-(x^4+(a^2-2)*x^2+1)*hu
  have hlast : v 72= -x*a*(y^2+1)*t := by rw [h72,hu]; ring
  have ht : t≠0 := by
    intro he
    apply hvn
    apply hinj
    · simpa [he] using hw
    · simpa [he] using hu
    · simpa [he] using hlast
  have he := output_contraction x y z a b t hx hy ha v hw hu hlast
  rw [hout] at he
  have hc : ((13851/256:ℂ)*x^7*y^4*a)≠0 := by
    simp [mul_ne_zero_iff,hx,hy,ha]
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right ht)).resolve_left hc

#print axioms output_contraction
#print axioms scalar_zero_of_output
end QuantitativeArithmeticSmallLevelNineteenGenericJet41
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet43
open QuantitativeArithmeticSmallLevelNineteenPoleLeading
open QuantitativeArithmeticSmallLevelNineteenFullSystem
/-- Input19 of the published equal-sign generic certificate. -/
def compact43 (B A Z Y X : ℂ) : ℂ := QuantitativeArithmeticSmallLevelNineteenGenericCertificates.poly19 B A Z Y X

theorem output_contraction (x y z a b t : ℂ)
    (hx : x≠0) (hy : y≠0) (ha : a≠0) (v : Fin 114→ℂ)
    (hw : v 18= -(x^4+(a^2-2)*x^2+1)*t)
    (hu : v 42=x*a*(y^2+1)*t) (hl : v 72= -x*a*(y^2+1)*t) :
    output0 x y z a b v = ((13851/256:ℂ)*x^7*y^4*a^2)*compact43 (b*y) (a*x) z (y^2) (x^2)*t := by
  unfold output0 compact43 QuantitativeArithmeticSmallLevelNineteenGenericCertificates.poly19
  rw [hw,hu,hl]
  field_simp [hx,hy,ha]
  <;> ring1

/-- Combine the actual leading rows with this first-Taylor output. -/
theorem scalar_zero_of_output (x y z a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (ha : a≠0)
    (hx4 : x^4≠1) (hY : y^2+1≠0) (hgap : a= -x-1/x ∨ x^2+a*x+1≠0)
    (v : Fin 114→ℂ) (hvn : v≠0)
    (hv : symbolicRows (-1) (-1) x y z a b v=0)
    (hout : output0 x y z a b v=0) : compact43 (b*y) (a*x) z (y^2) (x^2)=0 := by
  obtain ⟨hr,hinj⟩ := actual_symbolic_kernel_reduce0 x y z a b hx hy hz ha v hv
  obtain ⟨h72,hrow⟩ := leading_coordinates_gap0 x y z a b hx hy ha hx4 hgap v hr
  have hK : x*a*(y^2+1)≠0 := mul_ne_zero (mul_ne_zero hx ha) hY
  let t : ℂ := v 42/(x*a*(y^2+1))
  have hu : v 42=x*a*(y^2+1)*t := by dsimp [t]; field_simp
  have hw : v 18= -(x^4+(a^2-2)*x^2+1)*t := by
    apply mul_left_cancel₀ hK
    linear_combination hrow-(x^4+(a^2-2)*x^2+1)*hu
  have hlast : v 72= -x*a*(y^2+1)*t := by rw [h72,hu]; ring
  have ht : t≠0 := by
    intro he
    apply hvn
    apply hinj
    · simpa [he] using hw
    · simpa [he] using hu
    · simpa [he] using hlast
  have he := output_contraction x y z a b t hx hy ha v hw hu hlast
  rw [hout] at he
  have hc : ((13851/256:ℂ)*x^7*y^4*a^2)≠0 := by
    simp [div_ne_zero_iff,mul_ne_zero_iff,hx,hy,ha]
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right ht)).resolve_left hc

#print axioms output_contraction
#print axioms scalar_zero_of_output
end QuantitativeArithmeticSmallLevelNineteenGenericJet43
end
