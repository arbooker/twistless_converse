module
public import QuantitativeArithmeticLevelThirtyFivePoleSignedExclusionV1
public import QuantitativeArithmeticLevelThirtyFivePositiveA0CertificateV4
public meta import SmallLevelCertificateBatchCommandV1
public import QuantitativeArithmeticLevelThirtyFiveNegativeP17CertificateV4
public import QuantitativeArithmeticLevelThirtyFiveNegativeYCertificateV4
public import QuantitativeArithmeticLevelThirtyFivePositiveP15CertificateV4
public import QuantitativeArithmeticLevelThirtyFivePositiveYCertificateV4
public import QuantitativeArithmeticLevelThirtyFivePositiveZCertificateV4
-- Bounded certificate elaboration.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

set_option Elab.async false

/-! ## ThirtyFiveOriginalPositiveBranch -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

certificate_batch {
theorem original_positive_branch_parameter {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hr : v 192≠0) (hz : (u5*primeParameter 5 m s)≠1) :
    let x := primeParameter 2 m s
    let y := primeParameter 3 m s
    let z := (u5*primeParameter 5 m s)
    let w := (u7*primeParameter 7 m s)
    let b := (Real.sqrt 3:ℂ)*f 3
    x^(4:ℕ)-x^(2:ℕ)-y*b-2=0 ∧
    (y*b+x^(2:ℕ)+y^(2:ℕ)+1)*v 42=0 ∧
    (x^(4:ℕ)-3*x^(2:ℕ)-y^(2:ℕ)-1)*(v 84+v 42)= -w*(z-1)*v 192 := by
  let x := primeParameter 2 m s
  let y := primeParameter 3 m s
  let z := u5*primeParameter 5 m s
  let w := u7*primeParameter 7 m s
  let a := (Real.sqrt 2:ℂ)*f 2
  let b := (Real.sqrt 3:ℂ)*f 3
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  have hRows := original_positive_rows hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7
    BG G hG hGF s v hv hshift
  have he0 := original_all_sign_row118 hm hf ε hε hlaw BG G hG hGF s v hv hshift
  have he := (mul_eq_zero.mp he0).resolve_right hr
  exact positive_rows_branch_parameter x y z w a b v
    (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) hz hr he hRows

theorem original_positive_branch_constraints {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hr : v 192≠0) (hz : (u5*primeParameter 5 m s)≠1) :
    let x := primeParameter 2 m s
    let y := primeParameter 3 m s
    let z := (u5*primeParameter 5 m s)
    let w := (u7*primeParameter 7 m s)
    let b := (Real.sqrt 3:ℂ)*f 3
    x^(4:ℕ)-x^(2:ℕ)-y*b-2=0 ∧
    w= -x^(2:ℕ)*z+x^(2:ℕ)-1 ∧
    x^(4:ℕ)-3*x^(2:ℕ)-y^(2:ℕ)-1≠0 ∧ v 84+v 42≠0 := by
  let x := primeParameter 2 m s
  let y := primeParameter 3 m s
  let z := u5*primeParameter 5 m s
  let w := u7*primeParameter 7 m s
  let a := (Real.sqrt 2:ℂ)*f 2
  let b := (Real.sqrt 3:ℂ)*f 3
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  have hw : w≠0 := mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)
  obtain ⟨hp,h1,hc⟩ := original_positive_branch_parameter hm hf ε hε hlaw
    u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift hr hz
  have hRows := original_positive_rows hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7
    BG G hG hGF s v hv hshift
  have he0 := original_all_sign_row118 hm hf ε hε hlaw BG G hG hGF s v hv hshift
  have he := (mul_eq_zero.mp he0).resolve_right hr
  have hwrel := positive_rows_all_branch_w x y z w a b v hw hr he hp h1 hc hRows
  have hn : (x^(4:ℕ)-3*x^(2:ℕ)-y^(2:ℕ)-1)*(v 84+v 42)≠0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hw) (sub_ne_zero.mpr hz)) hr
  exact ⟨hp,hwrel,(mul_ne_zero_iff.mp hn).1,(mul_ne_zero_iff.mp hn).2⟩

#print axioms original_positive_branch_parameter
#print axioms original_positive_branch_constraints
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveReducedRowData -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
def positiveReduced3C24 (X Y Z W : ℂ) : ℂ := ((-2) + X + ((-1)*(X)^(2:ℕ)))

def positiveReduced3C42 (X Y Z W : ℂ) : ℂ := ((1/(W)^(1:ℕ))*((-3) + Y + ((-1)*(X)^(4:ℕ)) + ((-1)*(X)^(5:ℕ)) + ((-5)*(X)^(2:ℕ)) + (2*(X)^(3:ℕ)) + (3*Z) + (4*X) + (Y*(X)^(2:ℕ)) + (Z*(X)^(2:ℕ)) + ((-1)*X*Z) + ((-1)*Y*(X)^(3:ℕ)) + ((-3)*X*Y)))

def positiveReduced3C84 (X Y Z W : ℂ) : ℂ := ((1/(W)^(1:ℕ))*(Y + ((-1)*W) + ((-1)*(X)^(4:ℕ)) + ((-2)*(X)^(2:ℕ)) + (2*X) + (2*Z) + (3*(X)^(3:ℕ)) + (Y*(X)^(2:ℕ)) + ((-1)*W*(X)^(2:ℕ)) + ((-1)*X*Y) + ((-1)*X*Z)))

def positiveReduced3C192 (X Y Z W : ℂ) : ℂ := ((-1) + ((-1)*X) + ((-1)*Z) + ((-1)*(X)^(2:ℕ)) + (X*Z) + ((-1)*Z*(X)^(2:ℕ)))

def positiveReduced13C24 (X Y Z W : ℂ) : ℂ := (Z*(1/(X)^(1:ℕ))*(1/(Y)^(1:ℕ))*(1 + Y))

def positiveReduced13C42 (X Y Z W : ℂ) : ℂ := (Z*(1/(W)^(1:ℕ))*(1/(X)^(1:ℕ))*(1/(Y)^(1:ℕ))*((-5) + Z + ((-1)*Y) + ((-1)*(X)^(4:ℕ)) + ((-1)*(X)^(5:ℕ)) + ((-3)*(X)^(2:ℕ)) + ((-2)*X) + (2*W) + (4*(X)^(3:ℕ)) + (X*Z) + (Y*(X)^(2:ℕ)) + (Z*(X)^(2:ℕ)) + ((-1)*X*Y) + ((-1)*Y*(X)^(3:ℕ))))

def positiveReduced13C84 (X Y Z W : ℂ) : ℂ := ((-1)*Z*(1/(W)^(1:ℕ))*(1/(X)^(1:ℕ))*(1/(Y)^(1:ℕ))*(2 + Y + (X)^(4:ℕ) + ((-1)*W) + ((-3)*(X)^(3:ℕ)) + (2*X) + (W*(X)^(2:ℕ)) + (X*Y) + ((-1)*X*Z) + ((-1)*Y*(X)^(2:ℕ))))

def positiveReduced13C192 (X Y Z W : ℂ) : ℂ := ((-1)*Z*(1/(X)^(1:ℕ))*(1/(Y)^(1:ℕ))*((-3) + (X)^(2:ℕ) + ((-1)*Z) + (Z*(X)^(2:ℕ)) + ((-1)*X*Z)))

def positiveReduced16C24 (X Y Z W : ℂ) : ℂ := ((1/(X)^(1:ℕ))*(6 + X + (X)^(3:ℕ) + ((-1)*(X)^(2:ℕ)) + (X*Y)))

def positiveReduced16C42 (X Y Z W : ℂ) : ℂ := ((1/(W)^(1:ℕ))*(1/(X)^(1:ℕ))*(4 + W + (X)^(3:ℕ) + ((-6)*X) + ((-6)*Z) + ((-5)*Y) + ((-3)*(X)^(2:ℕ)) + ((-1)*W*X) + ((-1)*X*Y) + ((-1)*X*Z) + (3*Z*(X)^(2:ℕ))))

def positiveReduced16C84 (X Y Z W : ℂ) : ℂ := ((1/(W)^(1:ℕ))*(1/(X)^(1:ℕ))*(2 + W + (X)^(3:ℕ) + ((-1)*(X)^(2:ℕ)) + ((-6)*X) + ((-6)*Z) + ((-3)*Y) + ((-1)*W*X) + ((-1)*X*Y) + ((-1)*X*Z) + (3*Z*(X)^(2:ℕ))))

def positiveReduced16C192 (X Y Z W : ℂ) : ℂ := ((1/(X)^(1:ℕ))*((X)^(2:ℕ) + ((-1)*W) + (2*X) + (3*Z)))

def positiveReduced164C24 (X Y Z W : ℂ) : ℂ := ((1/(Y)^(1:ℕ))*(5 + (X)^(2:ℕ) + ((-1)*X) + ((-1)*Y)))

def positiveReduced164C42 (X Y Z W : ℂ) : ℂ := ((1/(W)^(1:ℕ))*(1/(Y)^(1:ℕ))*(5 + ((-8)*X) + ((-5)*(X)^(3:ℕ)) + ((-4)*Z) + ((-3)*Y) + (2*(X)^(4:ℕ)) + (2*(X)^(5:ℕ)) + (8*(X)^(2:ℕ)) + ((-2)*Y*(X)^(2:ℕ)) + ((-2)*Z*(X)^(2:ℕ)) + (2*Y*(X)^(3:ℕ)) + (3*X*Z) + (5*X*Y)))

def positiveReduced164C84 (X Y Z W : ℂ) : ℂ := ((1/(W)^(1:ℕ))*(1/(Y)^(1:ℕ))*(2 + W + ((-6)*(X)^(3:ℕ)) + ((-5)*X) + ((-3)*Z) + ((-2)*Y) + (2*(X)^(4:ℕ)) + (3*(X)^(2:ℕ)) + ((-2)*Y*(X)^(2:ℕ)) + (2*W*(X)^(2:ℕ)) + (2*X*Y) + (2*X*Z)))

def positiveReduced164C192 (X Y Z W : ℂ) : ℂ := ((1/(Y)^(1:ℕ))*(1 + X + (X)^(2:ℕ) + (2*Z) + ((-2)*X*Z) + (2*Z*(X)^(2:ℕ))))

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveReducedRowBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
theorem positive_reduced_row13 (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hx : x≠0) (hy : y≠0) (hw : w≠0)
    (ha : a= -x-1/x) (hb : b=(x^(4:ℕ)-x^(2:ℕ)-2)/y)
    (hRows : positiveRowsConclusion x y z w a b v) :
    positiveReduced13C24 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 24 + positiveReduced13C42 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 42 + positiveReduced13C84 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 84 + positiveReduced13C192 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 192=0 := by
  rcases hRows with ⟨h0,h3,h13,h14,h16,h18,h19,h45,h53,h150,h159,h163,h164⟩
  rw [ha,hb] at h13
  unfold positiveReduced13C24 positiveReduced13C42 positiveReduced13C84 positiveReduced13C192
  linear_combination (norm := (field_simp [hx,hy,hw]; ring)) h13

#print axioms positive_reduced_row13

theorem positive_reduced_row164 (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hx : x≠0) (hy : y≠0) (hw : w≠0)
    (ha : a= -x-1/x) (hb : b=(x^(4:ℕ)-x^(2:ℕ)-2)/y)
    (hRows : positiveRowsConclusion x y z w a b v) :
    positiveReduced164C24 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 24 + positiveReduced164C42 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 42 + positiveReduced164C84 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 84 + positiveReduced164C192 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 192=0 := by
  rcases hRows with ⟨h0,h3,h13,h14,h16,h18,h19,h45,h53,h150,h159,h163,h164⟩
  rw [ha,hb] at h164
  unfold positiveReduced164C24 positiveReduced164C42 positiveReduced164C84 positiveReduced164C192
  linear_combination (norm := (field_simp [hx,hy,hw]; ring)) h164

#print axioms positive_reduced_row164

theorem positive_reduced_row16 (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hx : x≠0) (hy : y≠0) (hw : w≠0)
    (ha : a= -x-1/x) (hb : b=(x^(4:ℕ)-x^(2:ℕ)-2)/y)
    (hRows : positiveRowsConclusion x y z w a b v) :
    positiveReduced16C24 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 24 + positiveReduced16C42 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 42 + positiveReduced16C84 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 84 + positiveReduced16C192 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 192=0 := by
  rcases hRows with ⟨h0,h3,h13,h14,h16,h18,h19,h45,h53,h150,h159,h163,h164⟩
  rw [ha,hb] at h16
  unfold positiveReduced16C24 positiveReduced16C42 positiveReduced16C84 positiveReduced16C192
  linear_combination (norm := (field_simp [hx,hy,hw]; ring)) h16

#print axioms positive_reduced_row16

def positiveReduced18C24 (X Y Z W : ℂ) : ℂ := ((-1)*Z*(1/(Y)^(1:ℕ))*(3 + Y + ((-1)*X) + (X*Y)))

def positiveReduced18C42 (X Y Z W : ℂ) : ℂ := ((-1)*Z*(1/(W)^(1:ℕ))*(1/(Y)^(1:ℕ))*((-2) + W + (X)^(4:ℕ) + ((-1)*Z) + ((-1)*(X)^(3:ℕ)) + ((-1)*(X)^(6:ℕ)) + ((-7)*X) + ((-3)*Y) + ((-2)*(X)^(2:ℕ)) + ((-2)*(X)^(5:ℕ)) + (Z*(X)^(3:ℕ)) + ((-1)*Y*(X)^(4:ℕ)) + ((-2)*X*Y) + ((-2)*Y*(X)^(2:ℕ)) + (2*Z*(X)^(2:ℕ)) + (3*X*Z)))

def positiveReduced18C84 (X Y Z W : ℂ) : ℂ := (Z*(1/(W)^(1:ℕ))*(1/(Y)^(1:ℕ))*((X)^(5:ℕ) + ((-2)*(X)^(3:ℕ)) + ((-2)*(X)^(4:ℕ)) + (2*Y) + (2*Z) + (5*X) + (W*X) + (W*(X)^(2:ℕ)) + (W*(X)^(3:ℕ)) + (X*Y) + ((-1)*Y*(X)^(3:ℕ)) + ((-1)*Z*(X)^(2:ℕ)) + ((-2)*X*Z)))

def positiveReduced18C192 (X Y Z W : ℂ) : ℂ := (Z*(1/(Y)^(1:ℕ))*((-1) + W + (X)^(2:ℕ) + (X)^(3:ℕ) + ((-1)*X) + ((-2)*Z) + (Z*(X)^(3:ℕ))))

theorem positive_reduced_row18 (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hx : x≠0) (hy : y≠0) (hw : w≠0)
    (ha : a= -x-1/x) (hb : b=(x^(4:ℕ)-x^(2:ℕ)-2)/y)
    (hRows : positiveRowsConclusion x y z w a b v) :
    positiveReduced18C24 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 24 + positiveReduced18C42 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 42 + positiveReduced18C84 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 84 + positiveReduced18C192 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 192=0 := by
  rcases hRows with ⟨h0,h3,h13,h14,h16,h18,h19,h45,h53,h150,h159,h163,h164⟩
  rw [ha,hb] at h18
  unfold positiveReduced18C24 positiveReduced18C42 positiveReduced18C84 positiveReduced18C192
  linear_combination (norm := (field_simp [hx,hy,hw]; ring)) h18
#print axioms positive_reduced_row18

theorem positive_reduced_row3 (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hx : x≠0) (hy : y≠0) (hw : w≠0)
    (ha : a= -x-1/x) (hb : b=(x^(4:ℕ)-x^(2:ℕ)-2)/y)
    (hRows : positiveRowsConclusion x y z w a b v) :
    positiveReduced3C24 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 24 + positiveReduced3C42 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 42 + positiveReduced3C84 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 84 + positiveReduced3C192 (x^(2:ℕ)) (y^(2:ℕ)) z w*v 192=0 := by
  rcases hRows with ⟨h0,h3,h13,h14,h16,h18,h19,h45,h53,h150,h159,h163,h164⟩
  rw [ha,hb] at h3
  unfold positiveReduced3C24 positiveReduced3C42 positiveReduced3C84 positiveReduced3C192
  linear_combination (norm := (field_simp [hx,hy,hw]; ring)) h3

#print axioms positive_reduced_row3

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveGenericCoordinateData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
def positiveGenericV84 (X Y Z : ℂ) : ℂ := ((1/(((-1) + (X)^(2:ℕ) + ((-1)*Y) + ((-3)*X)))^(1:ℕ))*((-1) + Z)*(1 + ((-1)*X) + (X*Z)))

def positiveGenericV24 (X Y Z : ℂ) : ℂ := ((-3/4:ℂ) + ((-1/2:ℂ)*Z) + ((1/4:ℂ)*(X)^(2:ℕ)) + ((1/4:ℂ)*(1/(((-1) + X + ((-1)*X*Z)))^(1:ℕ))*(1/(((-1) + (X)^(2:ℕ) + ((-1)*Y) + ((-3)*X)))^(1:ℕ))*((-1) + Z)*(1 + ((-1)*X) + (X*Z))*(1 + Z + ((-1)*(X)^(2:ℕ)) + (2*Y) + (4*X) + ((-1)*X*Z))))

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveGenericScalarRowBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
theorem positive_generic_scalar_row13 (X Y Z : ℂ)
    (hX : X≠0) (hY : Y≠0)
    (hW : X*Z-X+1≠0) (hC : X^(2:ℕ)-3*X-Y-1≠0) :
    positiveReduced13C24 X Y Z (-X*Z+X-1)*positiveGenericV24 X Y Z + positiveReduced13C84 X Y Z (-X*Z+X-1)*positiveGenericV84 X Y Z + positiveReduced13C192 X Y Z (-X*Z+X-1) = ((1/4:ℂ)*Z*(1/(X)^(1:ℕ))*(1/(Y)^(1:ℕ))*(1/(((-1) + (X)^(2:ℕ) + ((-1)*Y) + ((-3)*X)))^(1:ℕ)))*positiveGenericInput1 X Y Z := by
  unfold positiveReduced13C24 positiveReduced13C84 positiveReduced13C192 positiveGenericV24 positiveGenericV84 positiveGenericInput1
  generalize hd0 : ((-1)+X+(-1)*X*Z)=D0
  have hn0 : D0≠0 := by
    rw [←hd0]
    convert neg_ne_zero.mpr hW using 1 <;> ring
  generalize hd1 : (-X*Z+X-1)=D1
  have hn1 : D1≠0 := by
    rw [←hd1]
    convert neg_ne_zero.mpr hW using 1 <;> ring
  generalize hd2 : (1+(-1)*X+X*Z)=D2
  have hn2 : D2≠0 := by
    rw [←hd2]
    convert hW using 1 <;> ring
  generalize hd3 : (X*Z-X+1)=D3
  have hn3 : D3≠0 := by
    rw [←hd3]
    convert hW using 1 <;> ring
  generalize hd4 : ((-1)+X^(2:ℕ)+(-1)*Y+(-3)*X)=D4
  have hn4 : D4≠0 := by
    rw [←hd4]
    convert hC using 1 <;> ring
  generalize hd5 : (X^(2:ℕ)-3*X-Y-1)=D5
  have hn5 : D5≠0 := by
    rw [←hd5]
    convert hC using 1 <;> ring
  field_simp [hX,hY,hn0,hn1,hn2,hn3,hn4,hn5]
  subst D5 D4 D3 D2 D1 D0
  ring

#print axioms positive_generic_scalar_row13

theorem positive_generic_scalar_row16 (X Y Z : ℂ)
    (hX : X≠0) (hY : Y≠0)
    (hW : X*Z-X+1≠0) (hC : X^(2:ℕ)-3*X-Y-1≠0) :
    positiveReduced16C24 X Y Z (-X*Z+X-1)*positiveGenericV24 X Y Z + positiveReduced16C84 X Y Z (-X*Z+X-1)*positiveGenericV84 X Y Z + positiveReduced16C192 X Y Z (-X*Z+X-1) = ((1/4:ℂ)*(1/(X)^(1:ℕ))*(1/(((-1) + (X)^(2:ℕ) + ((-1)*Y) + ((-3)*X)))^(1:ℕ)))*positiveGenericInput2 X Y Z := by
  unfold positiveReduced16C24 positiveReduced16C84 positiveReduced16C192 positiveGenericV24 positiveGenericV84 positiveGenericInput2
  generalize hd0 : ((-1)+X+(-1)*X*Z)=D0
  have hn0 : D0≠0 := by
    rw [←hd0]
    convert neg_ne_zero.mpr hW using 1 <;> ring
  generalize hd1 : (-X*Z+X-1)=D1
  have hn1 : D1≠0 := by
    rw [←hd1]
    convert neg_ne_zero.mpr hW using 1 <;> ring
  generalize hd2 : (1+(-1)*X+X*Z)=D2
  have hn2 : D2≠0 := by
    rw [←hd2]
    convert hW using 1 <;> ring
  generalize hd3 : (X*Z-X+1)=D3
  have hn3 : D3≠0 := by
    rw [←hd3]
    convert hW using 1 <;> ring
  generalize hd4 : ((-1)+X^(2:ℕ)+(-1)*Y+(-3)*X)=D4
  have hn4 : D4≠0 := by
    rw [←hd4]
    convert hC using 1 <;> ring
  generalize hd5 : (X^(2:ℕ)-3*X-Y-1)=D5
  have hn5 : D5≠0 := by
    rw [←hd5]
    convert hC using 1 <;> ring
  field_simp [hX,hY,hn0,hn1,hn2,hn3,hn4,hn5]
  subst D5 D4 D3 D2 D1 D0
  ring

#print axioms positive_generic_scalar_row16

theorem positive_generic_scalar_row18 (X Y Z : ℂ)
    (hX : X≠0) (hY : Y≠0)
    (hW : X*Z-X+1≠0) (hC : X^(2:ℕ)-3*X-Y-1≠0) :
    positiveReduced18C24 X Y Z (-X*Z+X-1)*positiveGenericV24 X Y Z + positiveReduced18C84 X Y Z (-X*Z+X-1)*positiveGenericV84 X Y Z + positiveReduced18C192 X Y Z (-X*Z+X-1) = ((1/4:ℂ)*Z*(1/(Y)^(1:ℕ))*(1/(((-1) + (X)^(2:ℕ) + ((-1)*Y) + ((-3)*X)))^(1:ℕ)))*positiveGenericInput3 X Y Z := by
  unfold positiveReduced18C24 positiveReduced18C84 positiveReduced18C192 positiveGenericV24 positiveGenericV84 positiveGenericInput3
  generalize hd0 : ((-1)+X+(-1)*X*Z)=D0
  have hn0 : D0≠0 := by
    rw [←hd0]
    convert neg_ne_zero.mpr hW using 1 <;> ring
  generalize hd1 : (-X*Z+X-1)=D1
  have hn1 : D1≠0 := by
    rw [←hd1]
    convert neg_ne_zero.mpr hW using 1 <;> ring
  generalize hd2 : (1+(-1)*X+X*Z)=D2
  have hn2 : D2≠0 := by
    rw [←hd2]
    convert hW using 1 <;> ring
  generalize hd3 : (X*Z-X+1)=D3
  have hn3 : D3≠0 := by
    rw [←hd3]
    convert hW using 1 <;> ring
  generalize hd4 : ((-1)+X^(2:ℕ)+(-1)*Y+(-3)*X)=D4
  have hn4 : D4≠0 := by
    rw [←hd4]
    convert hC using 1 <;> ring
  generalize hd5 : (X^(2:ℕ)-3*X-Y-1)=D5
  have hn5 : D5≠0 := by
    rw [←hd5]
    convert hC using 1 <;> ring
  field_simp [hX,hY,hn0,hn1,hn2,hn3,hn4,hn5]
  subst D5 D4 D3 D2 D1 D0
  ring

#print axioms positive_generic_scalar_row18

theorem positive_generic_scalar_row3 (X Y Z : ℂ)
    (hX : X≠0) (hY : Y≠0)
    (hW : X*Z-X+1≠0) (hC : X^(2:ℕ)-3*X-Y-1≠0) :
    positiveReduced3C24 X Y Z (-X*Z+X-1)*positiveGenericV24 X Y Z + positiveReduced3C84 X Y Z (-X*Z+X-1)*positiveGenericV84 X Y Z + positiveReduced3C192 X Y Z (-X*Z+X-1) = ((1/4:ℂ)*(1/(((-1) + (X)^(2:ℕ) + ((-1)*Y) + ((-3)*X)))^(1:ℕ)))*positiveGenericInput0 X Y Z := by
  unfold positiveReduced3C24 positiveReduced3C84 positiveReduced3C192 positiveGenericV24 positiveGenericV84 positiveGenericInput0
  generalize hd0 : ((-1)+X+(-1)*X*Z)=D0
  have hn0 : D0≠0 := by
    rw [←hd0]
    convert neg_ne_zero.mpr hW using 1 <;> ring
  generalize hd1 : (-X*Z+X-1)=D1
  have hn1 : D1≠0 := by
    rw [←hd1]
    convert neg_ne_zero.mpr hW using 1 <;> ring
  generalize hd2 : (1+(-1)*X+X*Z)=D2
  have hn2 : D2≠0 := by
    rw [←hd2]
    convert hW using 1 <;> ring
  generalize hd3 : (X*Z-X+1)=D3
  have hn3 : D3≠0 := by
    rw [←hd3]
    convert hW using 1 <;> ring
  generalize hd4 : ((-1)+X^(2:ℕ)+(-1)*Y+(-3)*X)=D4
  have hn4 : D4≠0 := by
    rw [←hd4]
    convert hC using 1 <;> ring
  generalize hd5 : (X^(2:ℕ)-3*X-Y-1)=D5
  have hn5 : D5≠0 := by
    rw [←hd5]
    convert hC using 1 <;> ring
  field_simp [hX,hY,hn0,hn1,hn2,hn3,hn4,hn5]
  subst D5 D4 D3 D2 D1 D0
  ring

#print axioms positive_generic_scalar_row3

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveGenericRowsCheck -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveCoefficientPivot -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex

certificate_batch {
/-- A constant pivot for the remaining coordinate, including A=0.
No division by any good-prime eigenvalue is used. -/
theorem positive_constant_coordinate_pivot (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hx : x≠0) (hy : y≠0) (hw : w≠0)
    (ha : a= -x-1/x) (hb : b=(x^(4:ℕ)-x^(2:ℕ)-2)/y)
    (hRows : positiveRowsConclusion x y z w a b v) :
    -4*v 24-
      ((x^(6:ℕ)+x^(2:ℕ)*y^(2:ℕ)+x^(2:ℕ)*z-6*x^(2:ℕ)-3*y^(2:ℕ)-2*z+5)/w)*v 42-
      ((w+x^(4:ℕ)+2*x^(2:ℕ)*z-5*x^(2:ℕ)-2*y^(2:ℕ)-z)/w)*v 84+
      (x^(4:ℕ)-2*z-3)*v 192=0 := by
  rcases hRows with ⟨h0,h3,h13,h14,h16,h18,h19,h45,h53,h150,h159,h163,h164⟩
  rw [ha,hb] at h0 h163
  linear_combination (norm := (field_simp [hx,hy,hw]; ring)) x^(2:ℕ)*h0+y^(2:ℕ)*h163

#print axioms positive_constant_coordinate_pivot
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveGenericRowLink -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
theorem positive_generic_normalized_inputs (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (ha : a= -x-1/x) (hb : b=(x^(4:ℕ)-x^(2:ℕ)-2)/y)
    (hC : x^(4:ℕ)-3*x^(2:ℕ)-y^(2:ℕ)-1≠0)
    (hwrel : w= -x^(2:ℕ)*z+x^(2:ℕ)-1)
    (hcrow : (x^(4:ℕ)-3*x^(2:ℕ)-y^(2:ℕ)-1)*(v 84+v 42)= -w*(z-1)*v 192)
    (h192 : v 192=1) (h42 : v 42=0)
    (hRows : positiveRowsConclusion x y z w a b v) :
    positiveGenericInput0 (x^(2:ℕ)) (y^(2:ℕ)) z=0 ∧
    positiveGenericInput1 (x^(2:ℕ)) (y^(2:ℕ)) z=0 ∧
    positiveGenericInput2 (x^(2:ℕ)) (y^(2:ℕ)) z=0 ∧
    positiveGenericInput3 (x^(2:ℕ)) (y^(2:ℕ)) z=0 := by
  let X := x^(2:ℕ)
  let Y := y^(2:ℕ)
  have hx4 : x^(4:ℕ)=X^(2:ℕ) := by dsimp [X]; ring
  have hx6 : x^(6:ℕ)=X^(3:ℕ) := by dsimp [X]; ring
  have hX : X≠0 := pow_ne_zero _ hx
  have hY : Y≠0 := pow_ne_zero _ hy
  have hC' : X^(2:ℕ)-3*X-Y-1≠0 := by simpa only [hx4] using hC
  have hCexact : -1+X^(2:ℕ)+(-1)*Y+(-3)*X≠0 := by convert hC' using 1 <;> ring
  have hCnorm : -1-Y-X*3+X^(2:ℕ)≠0 := by convert hC' using 1 <;> ring
  have hCnorm2 : -1-X*3+X^(2:ℕ)-Y≠0 := by convert hC' using 1 <;> ring
  have hWn : -X*z+X-1≠0 := hwrel ▸ hw
  have hW : X*z-X+1≠0 := by convert neg_ne_zero.mpr hWn using 1 <;> ring
  have hWexact : -1+X+(-1)*X*z≠0 := by convert hWn using 1 <;> ring
  have h84 : v 84=positiveGenericV84 X Y z := by
    unfold positiveGenericV84
    rw [h42,add_zero,h192,mul_one,hwrel,hx4] at hcrow
    change (X^(2:ℕ)-3*X-Y-1)*v 84= -(-X*z+X-1)*(z-1) at hcrow
    linear_combination (norm := (field_simp [hC',hCexact,hCnorm,hCnorm2] <;> ring_nf <;> field_simp [hC',hCexact,hCnorm,hCnorm2] <;> ring)) (1/(X^(2:ℕ)-3*X-Y-1))*hcrow
  have h24 : v 24=positiveGenericV24 X Y z := by
    have hp := positive_constant_coordinate_pivot x y z w a b v hx hy hw ha hb hRows
    rw [h42,mul_zero,sub_zero,h192,mul_one,hwrel,h84,hx4] at hp
    unfold positiveGenericV24
    change -4*v 24-
      (((-X*z+X-1)+X^(2:ℕ)+2*X*z-5*X-2*Y-z)/(-X*z+X-1))*positiveGenericV84 X Y z+
      (X^(2:ℕ)-2*z-3)=0 at hp
    unfold positiveGenericV84 at hp
    linear_combination (norm := (field_simp [hWn,hWexact,hC',hCexact,hCnorm,hCnorm2] <;> ring_nf <;> field_simp [hWn,hWexact,hC',hCexact,hCnorm,hCnorm2] <;> ring)) (-1/4:ℂ)*hp
  have hr3 := positive_reduced_row3 x y z w a b v hx hy hw ha hb hRows
  rw [h42,mul_zero,add_zero,h192,mul_one,hwrel] at hr3
  have hs3 := positive_generic_scalar_row3 X Y z hX hY hW hC'
  rw [←h24,←h84] at hs3
  rw [hr3] at hs3
  have hi0 : positiveGenericInput0 X Y z=0 := by
    apply (mul_eq_zero.mp hs3.symm).resolve_left
    exact (mul_ne_zero (by norm_num : (1/4:ℂ)≠0) (div_ne_zero (by norm_num) (pow_ne_zero 1 hCexact)))
  have hr13 := positive_reduced_row13 x y z w a b v hx hy hw ha hb hRows
  rw [h42,mul_zero,add_zero,h192,mul_one,hwrel] at hr13
  have hs13 := positive_generic_scalar_row13 X Y z hX hY hW hC'
  rw [←h24,←h84] at hs13
  rw [hr13] at hs13
  have hi1 : positiveGenericInput1 X Y z=0 := by
    apply (mul_eq_zero.mp hs13.symm).resolve_left
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (1/4:ℂ)≠0) hz) (div_ne_zero (by norm_num) (pow_ne_zero 1 hX))) (div_ne_zero (by norm_num) (pow_ne_zero 1 hY))) (div_ne_zero (by norm_num) (pow_ne_zero 1 hCexact)))
  have hr16 := positive_reduced_row16 x y z w a b v hx hy hw ha hb hRows
  rw [h42,mul_zero,add_zero,h192,mul_one,hwrel] at hr16
  have hs16 := positive_generic_scalar_row16 X Y z hX hY hW hC'
  rw [←h24,←h84] at hs16
  rw [hr16] at hs16
  have hi2 : positiveGenericInput2 X Y z=0 := by
    apply (mul_eq_zero.mp hs16.symm).resolve_left
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (1/4:ℂ)≠0) (div_ne_zero (by norm_num) (pow_ne_zero 1 hX))) (div_ne_zero (by norm_num) (pow_ne_zero 1 hCexact)))
  have hr18 := positive_reduced_row18 x y z w a b v hx hy hw ha hb hRows
  rw [h42,mul_zero,add_zero,h192,mul_one,hwrel] at hr18
  have hs18 := positive_generic_scalar_row18 X Y z hX hY hW hC'
  rw [←h24,←h84] at hs18
  rw [hr18] at hs18
  have hi3 : positiveGenericInput3 X Y z=0 := by
    apply (mul_eq_zero.mp hs18.symm).resolve_left
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (1/4:ℂ)≠0) hz) (div_ne_zero (by norm_num) (pow_ne_zero 1 hY))) (div_ne_zero (by norm_num) (pow_ne_zero 1 hCexact)))
  exact ⟨hi0,hi1,hi2,hi3⟩

#print axioms positive_generic_normalized_inputs
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalPositiveGenericInputs -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

certificate_batch {
theorem original_positive_generic_inputs {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hr : v 192≠0) (hz : u5*primeParameter 5 m s≠1)
    (hA : (primeParameter 2 m s)^(4:ℕ)+(primeParameter 3 m s)^(2:ℕ)-1≠0) :
    let X := (primeParameter 2 m s)^(2:ℕ)
    let Y := (primeParameter 3 m s)^(2:ℕ)
    let Z := u5*primeParameter 5 m s
    positiveGenericInput0 X Y Z=0 ∧ positiveGenericInput1 X Y Z=0 ∧
    positiveGenericInput2 X Y Z=0 ∧ positiveGenericInput3 X Y Z=0 := by
  obtain ⟨v',hv',h192,hformula⟩ := hv.normalize (192:Fin 210) hr
  have hr' : v' 192≠0 := by rw [h192]; norm_num
  have hRows := original_positive_rows hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7
    BG G hG hGF s v' hv' hshift
  obtain ⟨hp,hwrel,hC,_⟩ := original_positive_branch_constraints hm hf ε hε hlaw
    u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v' hv' hshift hr' hz
  obtain ⟨_,h1,hcrow⟩ := original_positive_branch_parameter hm hf ε hε hlaw
    u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v' hv' hshift hr' hz
  have he := original_all_sign_row118 hm hf ε hε hlaw BG G hG hGF s v' hv' hshift
  rw [h192,mul_one] at he
  let x := primeParameter 2 m s
  let y := primeParameter 3 m s
  let a := (Real.sqrt 2:ℂ)*f 2
  let b := (Real.sqrt 3:ℂ)*f 3
  have hx : x≠0 := primeParameter_ne_zero 2 m (by decide) s
  have hy : y≠0 := primeParameter_ne_zero 3 m (by decide) s
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  have hz0 := mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s)
  have hw0 := mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)
  have ha : a= -x-1/x := by
    change 1+x*a+x^(2:ℕ)=0 at he
    linear_combination (norm := (field_simp [hx]; ring)) (1/x)*he
  have hb : b=(x^(4:ℕ)-x^(2:ℕ)-2)/y := by
    change x^(4:ℕ)-x^(2:ℕ)-y*b-2=0 at hp
    linear_combination (norm := (field_simp [hy]; ring)) -(1/y)*hp
  have h42 : v' 42=0 := by
    change (y*b+x^(2:ℕ)+y^(2:ℕ)+1)*v' 42=0 at h1
    apply (mul_eq_zero.mp h1).resolve_left
    intro hP1
    apply hA
    change x^(4:ℕ)-x^(2:ℕ)-y*b-2=0 at hp
    linear_combination hp+hP1
  exact positive_generic_normalized_inputs x y (u5*primeParameter 5 m s)
    (u7*primeParameter 7 m s) a b v' hx hy hz0 hw0 ha hb hC hwrel hcrow h192 h42 hRows

#print axioms original_positive_generic_inputs
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveGenericCertificates -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 60000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveMinusOne -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex

certificate_batch {
theorem positive_generic_minus_one (Y Z : ℂ) (hZ : Z≠1)
    (h0 : positiveGenericInput0 (-1) Y Z=0) : Z=3 := by
  have hp : 4*(Z-3)*(Z-1)=0 := by
    unfold positiveGenericInput0 at h0
    linear_combination h0
  have h := (mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr hZ)
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (by norm_num))

theorem signed_prime_two_minus_one_not_three (m : ℕ) (s u : ℂ)
    (hu : u=1 ∨ u= -1)
    (hx : (primeParameter 2 m s)^(2:ℕ)= -1) : u*primeParameter 5 m s≠3 := by
  have hn := congrArg norm hx
  rw [primeParameter_pow_norm 2 m 2 (by decide) s] at hn
  norm_num only [norm_neg,norm_one,Nat.cast_ofNat] at hn
  have hα : s.re-(m:ℝ)=0 :=
    (Real.rpow_right_inj (by norm_num : (0:ℝ)<4)
      (by norm_num : (4:ℝ)≠1)).mp (by simpa only [Real.rpow_zero] using hn)
  intro hz
  have hzN := congrArg norm hz
  rw [sign_mul_norm u _ hu,primeParameter_norm 5 m (by decide),hα,Real.rpow_zero] at hzN
  norm_num at hzN

#print axioms positive_generic_minus_one
#print axioms signed_prime_two_minus_one_not_three
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveRootDiskData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
open Complex Polynomial
open QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
def center : Fin 15 → ℂ := ![(-10427636131428806166945087/10000000000000000000000000:ℂ) + (0/1:ℂ)*Complex.I,
  (127388809748397191180801/78125000000000000000000:ℂ) + (0/1:ℂ)*Complex.I,
  (8881167960099189869149213/5000000000000000000000000:ℂ) + (0/1:ℂ)*Complex.I,
  (-40605348031977578834852189/50000000000000000000000000:ℂ) + (-16395185662844131241011149/20000000000000000000000000:ℂ)*Complex.I,
  (-40605348031977578834852189/50000000000000000000000000:ℂ) + (16395185662844131241011149/20000000000000000000000000:ℂ)*Complex.I,
  (-14930176777537320503300461/50000000000000000000000000:ℂ) + (-67572671083225753517713109/100000000000000000000000000:ℂ)*Complex.I,
  (-14930176777537320503300461/50000000000000000000000000:ℂ) + (67572671083225753517713109/100000000000000000000000000:ℂ)*Complex.I,
  (-18215982265501329418642213/100000000000000000000000000:ℂ) + (-3367398124889505603609967/1250000000000000000000000:ℂ)*Complex.I,
  (-18215982265501329418642213/100000000000000000000000000:ℂ) + (3367398124889505603609967/1250000000000000000000000:ℂ)*Complex.I,
  (91799894428399088283123777/1000000000000000000000000000:ℂ) + (-2172121520980340866339683/1000000000000000000000000:ℂ)*Complex.I,
  (91799894428399088283123777/1000000000000000000000000000:ℂ) + (2172121520980340866339683/1000000000000000000000000:ℂ)*Complex.I,
  (16999886284449618653478733/10000000000000000000000000:ℂ) + (-13370291123993822474236647/10000000000000000000000000:ℂ)*Complex.I,
  (16999886284449618653478733/10000000000000000000000000:ℂ) + (13370291123993822474236647/10000000000000000000000000:ℂ)*Complex.I,
  (1449411515089831015746053/625000000000000000000000:ℂ) + (-17123680429069126286755677/50000000000000000000000000:ℂ)*Complex.I,
  (1449411515089831015746053/625000000000000000000000:ℂ) + (17123680429069126286755677/50000000000000000000000000:ℂ)*Complex.I]

def polePolynomial : Polynomial ℂ := C (1/1:ℂ)*X^(15:ℕ) + C (-8/1:ℂ)*X^(14:ℕ) + C (69/2:ℂ)*X^(13:ℕ) + C (-116/1:ℂ)*X^(12:ℕ) + C (296/1:ℂ)*X^(11:ℕ) + C (-528/1:ℂ)*X^(10:ℕ) + C (666/1:ℂ)*X^(9:ℕ) + C (-558/1:ℂ)*X^(8:ℕ) + C (16/1:ℂ)*X^(7:ℕ) + C (336/1:ℂ)*X^(6:ℕ) + C (2115/2:ℂ)*X^(5:ℕ) + C (-1076/1:ℂ)*X^(4:ℕ) + C (-2751/1:ℂ)*X^(3:ℕ) + C (1362/1:ℂ)*X^(2:ℕ) + C (1044/1:ℂ)*X^(1:ℕ) + C (1944/1:ℂ)*X^(0:ℕ)

theorem polePolynomial_monic : polePolynomial.Monic := by
  unfold polePolynomial
  monicity!

theorem polePolynomial_degree : polePolynomial.degree=(15:WithBot ℕ) := by
  unfold polePolynomial
  compute_degree!

theorem polePolynomial_eval (z : ℂ) : polePolynomial.eval z=positiveGenericP15 z := by
  simp only [polePolynomial,positiveGenericP15,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X]
  ring

theorem center_injective : Function.Injective center := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first | rfl | norm_num [center,Complex.ext_iff] at h

#print axioms polePolynomial_monic
#print axioms polePolynomial_degree
#print axioms polePolynomial_eval
#print axioms center_injective
}

end QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
end
end

/-! ## ThirtyFivePositiveVariation -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
open QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open scoped BigOperators

certificate_batch {
def qCoefficient : Fin 15 → ℂ := ![(-1397885791/1362628808:ℂ),
  (-1641152923/1021971606:ℂ),
  (-35350530967/16351545696:ℂ),
  (65211308555/49054637088:ℂ),
  (19206594615/10901030464:ℂ),
  (1257846913/2043943212:ℂ),
  (-9560063335/12263659272:ℂ),
  (-730493689/2725257616:ℂ),
  (1842541657/2725257616:ℂ),
  (-2648100685/4087886424:ℂ),
  (10540873589/24527318544:ℂ),
  (-9430320979/49054637088:ℂ),
  (1964894683/32703091392:ℂ),
  (-380927327/24527318544:ℂ),
  (123036821/49054637088:ℂ)]

theorem q_eval_sum (z : ℂ) : positiveGenericQ14 z=∑ i : Fin 15, qCoefficient i*z^i.val := by
  norm_num [positiveGenericQ14,qCoefficient,Fin.sum_univ_succ]
  ring

theorem q_coefficient_bound (i : Fin 15) : ‖qCoefficient i‖≤(10:ℝ) := by
  fin_cases i <;> norm_num [qCoefficient,norm_div]

theorem q_variation (z w : ℂ) (hz : ‖z‖≤4) (hw : ‖w‖≤4) :
    ‖positiveGenericQ14 z-positiveGenericQ14 w‖ ≤ (100000000000000:ℝ)*‖z-w‖ := by
  rw [q_eval_sum z,q_eval_sum w]
  have h := QuantitativeArithmeticPolynomialVariation.finite_polynomial_difference
    qCoefficient z w 4 10 (by norm_num) (by norm_num) hz hw q_coefficient_bound
  have hL : (10:ℝ)*(∑ i : Fin 15, (i.val:ℝ)*4^i.val)≤100000000000000 := by
    norm_num [Fin.sum_univ_succ]
  exact h.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
#print axioms q_variation

def rCoefficient : Fin 15 → ℂ := ![(408584927/55023016:ℂ),
  (132115181/14564916:ℂ),
  (16892195905/1980828576:ℂ),
  (-29823770401/5942485728:ℂ),
  (-7530220529/1320552384:ℂ),
  (13918735/495207144:ℂ),
  (573323819/371405358:ℂ),
  (64609633/330138096:ℂ),
  (-324830869/330138096:ℂ),
  (7534065/6877877:ℂ),
  (-2436659869/2971242864:ℂ),
  (2284959461/5942485728:ℂ),
  (-487608805/3961657152:ℂ),
  (99431857/2971242864:ℂ),
  (-32572219/5942485728:ℂ)]

theorem r_eval_sum (z : ℂ) : positiveGenericR14 z=∑ i : Fin 15, rCoefficient i*z^i.val := by
  norm_num [positiveGenericR14,rCoefficient,Fin.sum_univ_succ]
  ring

theorem r_coefficient_bound (i : Fin 15) : ‖rCoefficient i‖≤(10:ℝ) := by
  fin_cases i <;> norm_num [rCoefficient,norm_div]

theorem r_variation (z w : ℂ) (hz : ‖z‖≤4) (hw : ‖w‖≤4) :
    ‖positiveGenericR14 z-positiveGenericR14 w‖ ≤ (100000000000000:ℝ)*‖z-w‖ := by
  rw [r_eval_sum z,r_eval_sum w]
  have h := QuantitativeArithmeticPolynomialVariation.finite_polynomial_difference
    rCoefficient z w 4 10 (by norm_num) (by norm_num) hz hw r_coefficient_bound
  have hL : (10:ℝ)*(∑ i : Fin 15, (i.val:ℝ)*4^i.val)≤100000000000000 := by
    norm_num [Fin.sum_univ_succ]
  exact h.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
#print axioms r_variation

}

end QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
end
end

/-! ## ThirtyFivePositivePhysicalDiskBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
open QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
def value0 : ℂ := (245371440684041735468281940373254933989652426062200038125290450771703255132944985593733756858287451654594304692977436136465423504593271645970700517243567463622201417636065988728087462743934742208067635109438359570015193573352619018748785861659691705882664657343569018429120704277228700308682746873804553612791448035347790025033011259734528579604132060036071341/545051523200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ) + (0/1:ℂ)*Complex.I

theorem value0_eq : positiveGenericQ14 (center 0)=value0 := by
  apply Complex.ext <;>
    norm_num [positiveGenericQ14,center,value0,pow_succ,Complex.mul_re,Complex.mul_im,
      Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem disk0_bounds :
    ‖center 0‖≤(260691/250000:ℝ) ∧ (260691/250000:ℝ)+1/1000000000000000000<4 ∧
    ((260691/250000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 0)‖+1/10000<1 ∨
      ((260691/250000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 0)‖ ∨
      ‖positiveGenericR14 (center 0)‖+1/10000<1) := by
  have hc : ‖center 0‖≤(260691/250000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(260691/250000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  have hb : ‖positiveGenericQ14 (center 0)‖≤(450181/1000000:ℝ) := by
    rw [value0_eq]
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(450181/1000000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [value0,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  right; left
  linarith

#print axioms disk0_bounds

def value1 : ℂ := (64100608653284476887129273866215747078629426192909490242158128500991120338816683961835454580901797063566068487968700477857902862811432521055129608391907208963998048433369034461135278218744237698449352203663473373056249345174359674799319383249610902621619139405032981655959066238499935956160114014187993552334651790058914299629392021/15478914167411159418654407675483997836041183404631738085299730300903320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ) + (0/1:ℂ)*Complex.I

theorem value1_eq : positiveGenericQ14 (center 1)=value1 := by
  apply Complex.ext <;>
    norm_num [positiveGenericQ14,center,value1,pow_succ,Complex.mul_re,Complex.mul_im,
      Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem disk1_bounds :
    ‖center 1‖≤(1630577/1000000:ℝ) ∧ (1630577/1000000:ℝ)+1/1000000000000000000<4 ∧
    ((1630577/1000000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 1)‖+1/10000<1 ∨
      ((1630577/1000000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 1)‖ ∨
      ‖positiveGenericR14 (center 1)‖+1/10000<1) := by
  have hc : ‖center 1‖≤(1630577/1000000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(1630577/1000000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  have hb : ‖positiveGenericQ14 (center 1)‖≥(1035289/250000:ℝ) := by
    rw [value1_eq]
    apply (sq_le_sq₀ (by norm_num : (0:ℝ)≤(1035289/250000:ℝ)) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [value1,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  right; right; left
  linarith

#print axioms disk1_bounds

def value2 : ℂ := (1848741543302068944194307272816326528937846434021733003348241987625013240345754595248947832820090112812949203395119591945862184623542326826338846092124663213038455187542640233247372187886444912697485055199226923931763709276988008425856879212532572358430597837418764255216919433825979429293457445365254550711409975661130777264593966021460593530479213319674669/299405743945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ) + (0/1:ℂ)*Complex.I

theorem value2_eq : positiveGenericQ14 (center 2)=value2 := by
  apply Complex.ext <;>
    norm_num [positiveGenericQ14,center,value2,pow_succ,Complex.mul_re,Complex.mul_im,
      Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem disk2_bounds :
    ‖center 2‖≤(888117/500000:ℝ) ∧ (888117/500000:ℝ)+1/1000000000000000000<4 ∧
    ((888117/500000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 2)‖+1/10000<1 ∨
      ((888117/500000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 2)‖ ∨
      ‖positiveGenericR14 (center 2)‖+1/10000<1) := by
  have hc : ‖center 2‖≤(888117/500000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(888117/500000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  have hb : ‖positiveGenericQ14 (center 2)‖≥(3087351/500000:ℝ) := by
    rw [value2_eq]
    apply (sq_le_sq₀ (by norm_num : (0:ℝ)≤(3087351/500000:ℝ)) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [value2,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  right; right; left
  linarith

#print axioms disk2_bounds

def value3 : ℂ := (1244686665542912456994623567081902086125233647544212911449801878042311111418169775537681898368522763258709094984759370267848518231273928158871276677708190238899392403775680063440990418733768780470984622131795706819891990480569175172073739923331409309371887729210160829975828564358469292391260830318987658059876403864158422237550176377173354380690783084629211227256126538053399/490546370880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ) + (27168316148396088035660363356828206181788462614471625971263457147652135083123978658436785573615292417673329345993212441535818996891880865156512818866604965331795503397183579955464210823005419786976230278640813627256857768045334057093812284343377816619966640931206607875719558771756608007960134185395380965266313441894628439077717336407189570481473660144701603101143616108849/8175772848000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ)*Complex.I

theorem value3_eq : positiveGenericQ14 (center 3)=value3 := by
  apply Complex.ext <;>
    norm_num [positiveGenericQ14,center,value3,pow_succ,Complex.mul_re,Complex.mul_im,
      Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem disk3_bounds :
    ‖center 3‖≤(1153917/1000000:ℝ) ∧ (1153917/1000000:ℝ)+1/1000000000000000000<4 ∧
    ((1153917/1000000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 3)‖+1/10000<1 ∨
      ((1153917/1000000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 3)‖ ∨
      ‖positiveGenericR14 (center 3)‖+1/10000<1) := by
  have hc : ‖center 3‖≤(1153917/1000000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(1153917/1000000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  have hb : ‖positiveGenericQ14 (center 3)‖≥(836197/200000:ℝ) := by
    rw [value3_eq]
    apply (sq_le_sq₀ (by norm_num : (0:ℝ)≤(836197/200000:ℝ)) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [value3,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  right; right; left
  linarith

#print axioms disk3_bounds

def value4 : ℂ := (1244686665542912456994623567081902086125233647544212911449801878042311111418169775537681898368522763258709094984759370267848518231273928158871276677708190238899392403775680063440990418733768780470984622131795706819891990480569175172073739923331409309371887729210160829975828564358469292391260830318987658059876403864158422237550176377173354380690783084629211227256126538053399/490546370880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ) + (-27168316148396088035660363356828206181788462614471625971263457147652135083123978658436785573615292417673329345993212441535818996891880865156512818866604965331795503397183579955464210823005419786976230278640813627256857768045334057093812284343377816619966640931206607875719558771756608007960134185395380965266313441894628439077717336407189570481473660144701603101143616108849/8175772848000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ)*Complex.I

theorem value4_eq : positiveGenericQ14 (center 4)=value4 := by
  apply Complex.ext <;>
    norm_num [positiveGenericQ14,center,value4,pow_succ,Complex.mul_re,Complex.mul_im,
      Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem disk4_bounds :
    ‖center 4‖≤(1153917/1000000:ℝ) ∧ (1153917/1000000:ℝ)+1/1000000000000000000<4 ∧
    ((1153917/1000000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 4)‖+1/10000<1 ∨
      ((1153917/1000000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 4)‖ ∨
      ‖positiveGenericR14 (center 4)‖+1/10000<1) := by
  have hc : ‖center 4‖≤(1153917/1000000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(1153917/1000000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  have hb : ‖positiveGenericQ14 (center 4)‖≥(836197/200000:ℝ) := by
    rw [value4_eq]
    apply (sq_le_sq₀ (by norm_num : (0:ℝ)≤(836197/200000:ℝ)) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [value4,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  right; right; left
  linarith

#print axioms disk4_bounds

theorem disk5_bounds :
    ‖center 5‖≤(738763/1000000:ℝ) ∧ (738763/1000000:ℝ)+1/1000000000000000000<4 ∧
    ((738763/1000000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 5)‖+1/10000<1 ∨
      ((738763/1000000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 5)‖ ∨
      ‖positiveGenericR14 (center 5)‖+1/10000<1) := by
  have hc : ‖center 5‖≤(738763/1000000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(738763/1000000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  left; norm_num

#print axioms disk5_bounds

theorem disk6_bounds :
    ‖center 6‖≤(738763/1000000:ℝ) ∧ (738763/1000000:ℝ)+1/1000000000000000000<4 ∧
    ((738763/1000000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 6)‖+1/10000<1 ∨
      ((738763/1000000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 6)‖ ∨
      ‖positiveGenericR14 (center 6)‖+1/10000<1) := by
  have hc : ‖center 6‖≤(738763/1000000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(738763/1000000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  left; norm_num

#print axioms disk6_bounds

def value7 : ℂ := (3180228035734925142433684165290251020022440201470653165871855053760098927582300988255739289769569081848105032941010418070826153120806257227267984814150657491035396769411718851439621590905164015962021362176445621756771140175995366469093793904415765580901149358415662774338655981143355074599452144061556875817708119748969344394813688558360714924542011036256122939718687617887069/490546370880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ) + (-1564739829087754614788979209116661895767136573185933371242264837144688223990080553849797265601954032459747450729239221071886331846307411293879456617751000367438258680334872863799845023172153019874501598320827279768689942115368751887388245767470440807089315558258301201518499899978414580468695014904003751697575338242933737125534744480793272609759546407379180813958734582567/340657202000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ)*Complex.I

theorem value7_eq : positiveGenericQ14 (center 7)=value7 := by
  apply Complex.ext <;>
    norm_num [positiveGenericQ14,center,value7,pow_succ,Complex.mul_re,Complex.mul_im,
      Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem disk7_bounds :
    ‖center 7‖≤(2700071/1000000:ℝ) ∧ (2700071/1000000:ℝ)+1/1000000000000000000<4 ∧
    ((2700071/1000000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 7)‖+1/10000<1 ∨
      ((2700071/1000000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 7)‖ ∨
      ‖positiveGenericR14 (center 7)‖+1/10000<1) := by
  have hc : ‖center 7‖≤(2700071/1000000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(2700071/1000000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  have hb : ‖positiveGenericQ14 (center 7)‖≥(3972659/500000:ℝ) := by
    rw [value7_eq]
    apply (sq_le_sq₀ (by norm_num : (0:ℝ)≤(3972659/500000:ℝ)) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [value7,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  right; right; left
  linarith

#print axioms disk7_bounds

def value8 : ℂ := (3180228035734925142433684165290251020022440201470653165871855053760098927582300988255739289769569081848105032941010418070826153120806257227267984814150657491035396769411718851439621590905164015962021362176445621756771140175995366469093793904415765580901149358415662774338655981143355074599452144061556875817708119748969344394813688558360714924542011036256122939718687617887069/490546370880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ) + (1564739829087754614788979209116661895767136573185933371242264837144688223990080553849797265601954032459747450729239221071886331846307411293879456617751000367438258680334872863799845023172153019874501598320827279768689942115368751887388245767470440807089315558258301201518499899978414580468695014904003751697575338242933737125534744480793272609759546407379180813958734582567/340657202000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ)*Complex.I

theorem value8_eq : positiveGenericQ14 (center 8)=value8 := by
  apply Complex.ext <;>
    norm_num [positiveGenericQ14,center,value8,pow_succ,Complex.mul_re,Complex.mul_im,
      Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem disk8_bounds :
    ‖center 8‖≤(2700071/1000000:ℝ) ∧ (2700071/1000000:ℝ)+1/1000000000000000000<4 ∧
    ((2700071/1000000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 8)‖+1/10000<1 ∨
      ((2700071/1000000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 8)‖ ∨
      ‖positiveGenericR14 (center 8)‖+1/10000<1) := by
  have hc : ‖center 8‖≤(2700071/1000000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(2700071/1000000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  have hb : ‖positiveGenericQ14 (center 8)‖≥(3972659/500000:ℝ) := by
    rw [value8_eq]
    apply (sq_le_sq₀ (by norm_num : (0:ℝ)≤(3972659/500000:ℝ)) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [value8,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  right; right; left
  linarith

#print axioms disk8_bounds

def value9 : ℂ := (22067573170098834401738262160251018919242812558039521730751431174940113650121844382491059805565847556020559713619799069464557499208025021777512286134964350608552603947313667742595400557545066565726099032459175260121831801175396501658798909445853537336333309258169025898715987385005476598053887639137696757077158552317101174014787943719990880052344124333301858303392704772570608947990416621/5450515232000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ) + (-7387462281159499503537755382592419025446751839547933654336735785467825382682478645026891512328918808848564436125528212144002593991562805377380215732902275294547960350477928771280324047134763519239516005659025030712532162524281479409906266871343671950482644056046280785517283211392559213123598679701052670735141102097399866822807502749357654945000371625821635888061866820124955568685713/2725257616000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ)*Complex.I

theorem value9_eq : positiveGenericQ14 (center 9)=value9 := by
  apply Complex.ext <;>
    norm_num [positiveGenericQ14,center,value9,pow_succ,Complex.mul_re,Complex.mul_im,
      Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem disk9_bounds :
    ‖center 9‖≤(2174061/1000000:ℝ) ∧ (2174061/1000000:ℝ)+1/1000000000000000000<4 ∧
    ((2174061/1000000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 9)‖+1/10000<1 ∨
      ((2174061/1000000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 9)‖ ∨
      ‖positiveGenericR14 (center 9)‖+1/10000<1) := by
  have hc : ‖center 9‖≤(2174061/1000000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(2174061/1000000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  have hb : ‖positiveGenericQ14 (center 9)‖≥(487239/100000:ℝ) := by
    rw [value9_eq]
    apply (sq_le_sq₀ (by norm_num : (0:ℝ)≤(487239/100000:ℝ)) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [value9,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  right; right; left
  linarith

#print axioms disk9_bounds

def value10 : ℂ := (22067573170098834401738262160251018919242812558039521730751431174940113650121844382491059805565847556020559713619799069464557499208025021777512286134964350608552603947313667742595400557545066565726099032459175260121831801175396501658798909445853537336333309258169025898715987385005476598053887639137696757077158552317101174014787943719990880052344124333301858303392704772570608947990416621/5450515232000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ) + (7387462281159499503537755382592419025446751839547933654336735785467825382682478645026891512328918808848564436125528212144002593991562805377380215732902275294547960350477928771280324047134763519239516005659025030712532162524281479409906266871343671950482644056046280785517283211392559213123598679701052670735141102097399866822807502749357654945000371625821635888061866820124955568685713/2725257616000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ)*Complex.I

theorem value10_eq : positiveGenericQ14 (center 10)=value10 := by
  apply Complex.ext <;>
    norm_num [positiveGenericQ14,center,value10,pow_succ,Complex.mul_re,Complex.mul_im,
      Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem disk10_bounds :
    ‖center 10‖≤(2174061/1000000:ℝ) ∧ (2174061/1000000:ℝ)+1/1000000000000000000<4 ∧
    ((2174061/1000000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 10)‖+1/10000<1 ∨
      ((2174061/1000000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 10)‖ ∨
      ‖positiveGenericR14 (center 10)‖+1/10000<1) := by
  have hc : ‖center 10‖≤(2174061/1000000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(2174061/1000000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  have hb : ‖positiveGenericQ14 (center 10)‖≥(487239/100000:ℝ) := by
    rw [value10_eq]
    apply (sq_le_sq₀ (by norm_num : (0:ℝ)≤(487239/100000:ℝ)) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [value10,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  right; right; left
  linarith

#print axioms disk10_bounds

def value11 : ℂ := (176400738199096363152411517929030248189221580217538049372751201952811408281182840212232710293735773956471239783652551252925979420948851851952314161934925738204979925418894523954545312733881761702771822788750648830202818606378534546202803173472186027799118407653417225765499098786156223963024744092006676555043133955426251220257156078934980145379994965940711/232128348750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ) + (-85289852428914598746567957485346241845937961531837632953868479840092444214882741453293755992620244116288054993283698383662272151811442263978149794988705524932606705200787850377933028052927322585942087431784987111420685025321941411486402872133053635661825540886743409029575102005881364675111453391703173388543726526459557652906636075211612154458989491026947/171946925000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ)*Complex.I

theorem value11_eq : positiveGenericR14 (center 11)=value11 := by
  apply Complex.ext <;>
    norm_num [positiveGenericR14,center,value11,pow_succ,Complex.mul_re,Complex.mul_im,
      Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem disk11_bounds :
    ‖center 11‖≤(1081389/500000:ℝ) ∧ (1081389/500000:ℝ)+1/1000000000000000000<4 ∧
    ((1081389/500000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 11)‖+1/10000<1 ∨
      ((1081389/500000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 11)‖ ∨
      ‖positiveGenericR14 (center 11)‖+1/10000<1) := by
  have hc : ‖center 11‖≤(1081389/500000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(1081389/500000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  have hb : ‖positiveGenericR14 (center 11)‖≤(453743/500000:ℝ) := by
    rw [value11_eq]
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(453743/500000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [value11,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  right; right; right
  linarith

#print axioms disk11_bounds

def value12 : ℂ := (176400738199096363152411517929030248189221580217538049372751201952811408281182840212232710293735773956471239783652551252925979420948851851952314161934925738204979925418894523954545312733881761702771822788750648830202818606378534546202803173472186027799118407653417225765499098786156223963024744092006676555043133955426251220257156078934980145379994965940711/232128348750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ) + (85289852428914598746567957485346241845937961531837632953868479840092444214882741453293755992620244116288054993283698383662272151811442263978149794988705524932606705200787850377933028052927322585942087431784987111420685025321941411486402872133053635661825540886743409029575102005881364675111453391703173388543726526459557652906636075211612154458989491026947/171946925000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ)*Complex.I

theorem value12_eq : positiveGenericR14 (center 12)=value12 := by
  apply Complex.ext <;>
    norm_num [positiveGenericR14,center,value12,pow_succ,Complex.mul_re,Complex.mul_im,
      Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem disk12_bounds :
    ‖center 12‖≤(1081389/500000:ℝ) ∧ (1081389/500000:ℝ)+1/1000000000000000000<4 ∧
    ((1081389/500000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 12)‖+1/10000<1 ∨
      ((1081389/500000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 12)‖ ∨
      ‖positiveGenericR14 (center 12)‖+1/10000<1) := by
  have hc : ‖center 12‖≤(1081389/500000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(1081389/500000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  have hb : ‖positiveGenericR14 (center 12)‖≤(453743/500000:ℝ) := by
    rw [value12_eq]
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(453743/500000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [value12,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  right; right; right
  linarith

#print axioms disk12_bounds

def value13 : ℂ := (1744291280321253337280509961833770945199706840779725800140690934575635127580544234984243028562023953322192950911865685288567168720225757511115394267343657239347403636288162748191544242689607810347563706874948015992252470299948355297448666046069685917157601893330313431878083154357865646063137740462303978890497274758931247229341238397185098846771966650071245300639243171/3627005449218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ) + (-1494523804583214865914718805088209571896250674585120920910273210210566166954294422341071091273852710888667560837992476839442725315034837496271586435399703974461182453164770236493009780963171622022484729725090762090298208629226745898776962241964811632491943795694253720171242306930698205964741861536477507813689082899530405266606532310238532774292629136562442680385889/7556261352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ)*Complex.I

theorem value13_eq : positiveGenericR14 (center 13)=value13 := by
  apply Complex.ext <;>
    norm_num [positiveGenericR14,center,value13,pow_succ,Complex.mul_re,Complex.mul_im,
      Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem disk13_bounds :
    ‖center 13‖≤(234421/100000:ℝ) ∧ (234421/100000:ℝ)+1/1000000000000000000<4 ∧
    ((234421/100000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 13)‖+1/10000<1 ∨
      ((234421/100000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 13)‖ ∨
      ‖positiveGenericR14 (center 13)‖+1/10000<1) := by
  have hc : ‖center 13‖≤(234421/100000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(234421/100000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  have hb : ‖positiveGenericR14 (center 13)‖≤(260001/500000:ℝ) := by
    rw [value13_eq]
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(260001/500000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [value13,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  right; right; right
  linarith

#print axioms disk13_bounds

def value14 : ℂ := (1744291280321253337280509961833770945199706840779725800140690934575635127580544234984243028562023953322192950911865685288567168720225757511115394267343657239347403636288162748191544242689607810347563706874948015992252470299948355297448666046069685917157601893330313431878083154357865646063137740462303978890497274758931247229341238397185098846771966650071245300639243171/3627005449218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ) + (1494523804583214865914718805088209571896250674585120920910273210210566166954294422341071091273852710888667560837992476839442725315034837496271586435399703974461182453164770236493009780963171622022484729725090762090298208629226745898776962241964811632491943795694253720171242306930698205964741861536477507813689082899530405266606532310238532774292629136562442680385889/7556261352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:ℂ)*Complex.I

theorem value14_eq : positiveGenericR14 (center 14)=value14 := by
  apply Complex.ext <;>
    norm_num [positiveGenericR14,center,value14,pow_succ,Complex.mul_re,Complex.mul_im,
      Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem disk14_bounds :
    ‖center 14‖≤(234421/100000:ℝ) ∧ (234421/100000:ℝ)+1/1000000000000000000<4 ∧
    ((234421/100000:ℝ)+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 (center 14)‖+1/10000<1 ∨
      ((234421/100000:ℝ)+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 (center 14)‖ ∨
      ‖positiveGenericR14 (center 14)‖+1/10000<1) := by
  have hc : ‖center 14‖≤(234421/100000:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(234421/100000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [center,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  refine ⟨hc,by norm_num,?_⟩
  have hb : ‖positiveGenericR14 (center 14)‖≤(260001/500000:ℝ) := by
    rw [value14_eq]
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤(260001/500000:ℝ))).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [value14,Complex.normSq,Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  right; right; right
  linarith

#print axioms disk14_bounds

}

end QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
end
end

/-! ## ThirtyFivePositiveRootDiskNodeBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
open Complex Polynomial

certificate_batch {
lemma nodalWeight_full_product (i : Fin 15) :
    Lagrange.nodalWeight Finset.univ center i =
      ∏ j : Fin 15, if j=i then 1 else (center i-center j)⁻¹ := by
  rw [Lagrange.nodalWeight]
  have h := Finset.prod_erase_mul Finset.univ
    (fun j : Fin 15 => if j=i then (1:ℂ) else (center i-center j)⁻¹)
    (Finset.mem_univ i)
  rw [ite_eq_left (rfl : i=i),mul_one] at h
  rw [← h]
  apply Finset.prod_congr rfl
  intro j hj
  rw [ite_eq_right (Finset.mem_erase.mp hj).1]

def node0Coefficient : ℂ := (149340009571625682446922009605429439077822581339486043504776914383283148660589998729774306997315301999686282738566852434290496873074266960919689622783983841556790455159948904570848978119302470447222066704528396836211512570568662887846549408059794528824151568886822113101683158181931397141147667613453271491903245180419885909692507777531924046529122692473/3133019405808765185791062464316255551130868315855831326309940507776593075041608203970536123224764585955275294909025393287912636282974499596169477928633281638194793896139174073154529145575747855833401751751139832126442253561745534255624280389958015200647951541317432608155348484228234552553505913276156806516743200146927719225078034869980803877230776960496726220558000000000000000:ℂ) + (0/1:ℂ)*Complex.I

theorem node0_coefficient :
    Lagrange.nodalWeight Finset.univ center 0*polePolynomial.eval (center 0)=node0Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [Fin.prod_univ_succ,center,polePolynomial,node0Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node0_bound :
    |(Lagrange.nodalWeight Finset.univ center 0*polePolynomial.eval (center 0)).re|+
    |(Lagrange.nodalWeight Finset.univ center 0*polePolynomial.eval (center 0)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node0_coefficient]
  norm_num [node0Coefficient]

#print axioms node0_coefficient
#print axioms node0_bound

def node1Coefficient : ℂ := (311999072206261204629750514491867406117270800501735427482705243484531514135951553629686804108622076136934176277015430522194679801660271816923027563726527734313723977932739920264412415707934771766044209951969610738163499861908311326551017806867281707462767053531923368682199221760928231239647622356470067965550187718105661356333964104315701448146944/6525122098915537712780759298539612023859069241217606386341480242960136271046515385593881118992100702414484198387647567377044948145634292255020556183911590339998016889377003575540493750731878188172790618852345180422240494892651682308235718557211638114803849215121458029233070418921687532460606528854801697969007252176063625317099245888972425190440966285107698217254638671875:ℂ) + (0/1:ℂ)*Complex.I

theorem node1_coefficient :
    Lagrange.nodalWeight Finset.univ center 1*polePolynomial.eval (center 1)=node1Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [Fin.prod_univ_succ,center,polePolynomial,node1Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node1_bound :
    |(Lagrange.nodalWeight Finset.univ center 1*polePolynomial.eval (center 1)).re|+
    |(Lagrange.nodalWeight Finset.univ center 1*polePolynomial.eval (center 1)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node1_coefficient]
  norm_num [node1Coefficient]

#print axioms node1_coefficient
#print axioms node1_bound

def node2Coefficient : ℂ := (-415992057221803051775195887769002666868256542772819469913681805273752287972793100269230826609024952755906501754362103736546262788308698197932768469396046932452753097807796991101401996944172724582345102191953171882792822689355335899354812764333099640912957651672432426484620410331811068604950291243509494217093701936293488819527799258034550320527243/27233450397908142880389097696696756826355018992150233517844699665962515459889654410573663548011359235333988595033678702941021039570982671806538600271885701494546283486850621115696615598417932299215065738142203562519590691454365003011140510947352160962675841410635221264097178742824478530560033575910621971722096342758193150616293039200924980949327831239424069013500976562500:ℂ) + (0/1:ℂ)*Complex.I

theorem node2_coefficient :
    Lagrange.nodalWeight Finset.univ center 2*polePolynomial.eval (center 2)=node2Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [Fin.prod_univ_succ,center,polePolynomial,node2Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node2_bound :
    |(Lagrange.nodalWeight Finset.univ center 2*polePolynomial.eval (center 2)).re|+
    |(Lagrange.nodalWeight Finset.univ center 2*polePolynomial.eval (center 2)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node2_coefficient]
  norm_num [node2Coefficient]

#print axioms node2_coefficient
#print axioms node2_bound

def node3Coefficient : ℂ := (-8783397507352644337715362392562679291370055673190130761978028915380398997149090855444163622153690829809416218584336475955841321534004052500736596257739126185716739180681764756317107480655411727215126074426935466716664233379928073650900855943035364448634535015121944717744460606316945030291469752560900490198994732510129057754086771699428874373777247308802765391055269676130742741836813055012864440326288242701003295263914191749996594914916040704393075204762250478459430465335330215504772571821377347341384094082478057929589317091500017670959480989166949429080881158739210899710712389964685676140604300222059036416069202798464816937632408246535267952499864516509457544739680464593749/14568273159355932740582882389168315051040515865370344644175415411228072670821766511513628363096617392227143160454163795346920028033989831868717472068698022731892758191388909534999368410397835345741814369653483377834932348383012853305671588105445625414774034158645093066846253950829358654369325087376316977108174710778941260896750277607614864056105895761364246516792522792258950290421989057845852495707028118479384767708915935528770769139122423530208095264727776690727252218638852208640615325034167557546825084285867675989562239248834175098648720666367592403115084726092731754617108460161827981675664347560303024200200641375315554618400322946467346949516641149052041026466887255434900000000000000000000000000000:ℂ) + (-40560223099348322580030836540097767835620962803693742252282330284433139779947757559232555083292746425134535869492924694185903103462777788481780629136525178730860062557699441503046627284211704183614091267343269328584588585741920682759470646672003987135939676123505549731522249936100643487633701861231149973313566296644857736142024853029047936491552634020181761355903907826221001747894109984238077963756446878330592882744897678836549104220161883069843290744036250833623112351469520419017674619485110546011795216232131782741442135075028586679151835388435156947185830591850861412684582492489601886048403964754768229188005186863944709417739965174279211037567423802053794502434680667609950462064573651627089532241/13269419068592742451357631933999948994342706510815224631855698401307157870542192338397707871867856842396261082017917664605338965931270957836344266818826449039606413861116958887804702234538992584401890984429476993352861921836727846636107487139953421234906757499049901203493116629386695136949365595034097459968227540580485848890390234272457771222916381157286662754853820989419199776736854648296518250981029942813005034092830827173342749937345333658238964760622731948719356980383684304300343592696591761122006164639908085484476728863814329587579326115471773933686145475626877442726091763481130857528859994592667380450866914942494208893062442165856554412218748674685579945744822158083444035785845858762319094450000000000000000000000000000:ℂ)*Complex.I

theorem node3_coefficient :
    Lagrange.nodalWeight Finset.univ center 3*polePolynomial.eval (center 3)=node3Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [pow_succ,Fin.prod_univ_succ,center,polePolynomial,node3Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node3_bound :
    |(Lagrange.nodalWeight Finset.univ center 3*polePolynomial.eval (center 3)).re|+
    |(Lagrange.nodalWeight Finset.univ center 3*polePolynomial.eval (center 3)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node3_coefficient]
  norm_num [node3Coefficient]

#print axioms node3_coefficient
#print axioms node3_bound

def node4Coefficient : ℂ := (-8783397507352644337715362392562679291370055673190130761978028915380398997149090855444163622153690829809416218584336475955841321534004052500736596257739126185716739180681764756317107480655411727215126074426935466716664233379928073650900855943035364448634535015121944717744460606316945030291469752560900490198994732510129057754086771699428874373777247308802765391055269676130742741836813055012864440326288242701003295263914191749996594914916040704393075204762250478459430465335330215504772571821377347341384094082478057929589317091500017670959480989166949429080881158739210899710712389964685676140604300222059036416069202798464816937632408246535267952499864516509457544739680464593749/14568273159355932740582882389168315051040515865370344644175415411228072670821766511513628363096617392227143160454163795346920028033989831868717472068698022731892758191388909534999368410397835345741814369653483377834932348383012853305671588105445625414774034158645093066846253950829358654369325087376316977108174710778941260896750277607614864056105895761364246516792522792258950290421989057845852495707028118479384767708915935528770769139122423530208095264727776690727252218638852208640615325034167557546825084285867675989562239248834175098648720666367592403115084726092731754617108460161827981675664347560303024200200641375315554618400322946467346949516641149052041026466887255434900000000000000000000000000000:ℂ) + (40560223099348322580030836540097767835620962803693742252282330284433139779947757559232555083292746425134535869492924694185903103462777788481780629136525178730860062557699441503046627284211704183614091267343269328584588585741920682759470646672003987135939676123505549731522249936100643487633701861231149973313566296644857736142024853029047936491552634020181761355903907826221001747894109984238077963756446878330592882744897678836549104220161883069843290744036250833623112351469520419017674619485110546011795216232131782741442135075028586679151835388435156947185830591850861412684582492489601886048403964754768229188005186863944709417739965174279211037567423802053794502434680667609950462064573651627089532241/13269419068592742451357631933999948994342706510815224631855698401307157870542192338397707871867856842396261082017917664605338965931270957836344266818826449039606413861116958887804702234538992584401890984429476993352861921836727846636107487139953421234906757499049901203493116629386695136949365595034097459968227540580485848890390234272457771222916381157286662754853820989419199776736854648296518250981029942813005034092830827173342749937345333658238964760622731948719356980383684304300343592696591761122006164639908085484476728863814329587579326115471773933686145475626877442726091763481130857528859994592667380450866914942494208893062442165856554412218748674685579945744822158083444035785845858762319094450000000000000000000000000000:ℂ)*Complex.I

theorem node4_coefficient :
    Lagrange.nodalWeight Finset.univ center 4*polePolynomial.eval (center 4)=node4Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [pow_succ,Fin.prod_univ_succ,center,polePolynomial,node4Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node4_bound :
    |(Lagrange.nodalWeight Finset.univ center 4*polePolynomial.eval (center 4)).re|+
    |(Lagrange.nodalWeight Finset.univ center 4*polePolynomial.eval (center 4)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node4_coefficient]
  norm_num [node4Coefficient]

#print axioms node4_coefficient
#print axioms node4_bound

def node5Coefficient : ℂ := (-2478506707100273716805876240870902491848295054926239360840783051169067336269037447736951396307441198279553290064192763713946007096032883554078517330056198246853422459181398537863840844142625598652640392422400269007525818878701471351749321055113898860895663203873120985673082209226907030229461461297235904947057272366357055464770314797487926490883953043997200279548448226474353888814567080734036056555893092986502208573577046575747378462761023784329081358423390369050774572333662034222440340288031707966550877953141566949208749526922589757596993543197066972000427400715982462232266468855013389190118985514323138788750650250704508861556678083859350769027286497319222579090751583859/1209597684792872232188876417851098157111721475547496595910814378396686442343095919440286595629859575780987190509555860133262975412773717287711198897709276021184370544031655087564201860122148380037427566928179954285976381657856429434805990449469275980315671549648386924051036090374699705653952509630584074139209662215026944047058607473274087627623407311795323169457248770026856601675068100467136878796295774777011596282755951315336764427559810142135733335053657898772753533337935228060524965625721970981560817288212143349903185226547808806540773023892891897078604134574623986534605034132323669847536801154261365606842201628985753441963799843728759269880220610051939359823176527812896000000000000000000000000:ℂ) + (4744122792234414746262621862944521883909645300436544167976144737269572504172323689359708797026281221412775674769614980689398473320338057441974480182824165158304749516718649649025220777925485791466206103634581255072705342650484455640358613090786660461421253993550507950348320928218432519077480599730200658932920077410634227360733443685735292967916831399116064120412162658141350527921277992273883040331218903988166013157975803163460856425614856286368353019742270391392766192271562975048753861584826326657698616372812268555613000908617975285699181517901950270956036707233835172176672890557624312122097914001305086283047969475449828792934425744440718986513435852555801333552404718203266041383764440164789887/2403992544045298154732428665680610741914412853406352448832137712966029052347236768127270761248387131946885330373828726982800495208217577359965557104323330221479919073891102948294602668502445227901432755298059403200210517740775077058648779286283789200778953559237700749059283980142099713852075792762091287511357823650671188748391122420483440575087773899271875901577410380043961830071249996174098098850005969975127596338857391331120254144607991039409293864770341755652557564342939125780988254270433361233729514791255042393127995943131423619566239843897415231977483390286366703446172822013371144299355052802069808485128472603420669137501508087558612801881016389191196637448035813420916523467533034721392895696000000000000000000000000:ℂ)*Complex.I

theorem node5_coefficient :
    Lagrange.nodalWeight Finset.univ center 5*polePolynomial.eval (center 5)=node5Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [pow_succ,Fin.prod_univ_succ,center,polePolynomial,node5Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node5_bound :
    |(Lagrange.nodalWeight Finset.univ center 5*polePolynomial.eval (center 5)).re|+
    |(Lagrange.nodalWeight Finset.univ center 5*polePolynomial.eval (center 5)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node5_coefficient]
  norm_num [node5Coefficient]

#print axioms node5_coefficient
#print axioms node5_bound

def node6Coefficient : ℂ := (-2478506707100273716805876240870902491848295054926239360840783051169067336269037447736951396307441198279553290064192763713946007096032883554078517330056198246853422459181398537863840844142625598652640392422400269007525818878701471351749321055113898860895663203873120985673082209226907030229461461297235904947057272366357055464770314797487926490883953043997200279548448226474353888814567080734036056555893092986502208573577046575747378462761023784329081358423390369050774572333662034222440340288031707966550877953141566949208749526922589757596993543197066972000427400715982462232266468855013389190118985514323138788750650250704508861556678083859350769027286497319222579090751583859/1209597684792872232188876417851098157111721475547496595910814378396686442343095919440286595629859575780987190509555860133262975412773717287711198897709276021184370544031655087564201860122148380037427566928179954285976381657856429434805990449469275980315671549648386924051036090374699705653952509630584074139209662215026944047058607473274087627623407311795323169457248770026856601675068100467136878796295774777011596282755951315336764427559810142135733335053657898772753533337935228060524965625721970981560817288212143349903185226547808806540773023892891897078604134574623986534605034132323669847536801154261365606842201628985753441963799843728759269880220610051939359823176527812896000000000000000000000000:ℂ) + (-4744122792234414746262621862944521883909645300436544167976144737269572504172323689359708797026281221412775674769614980689398473320338057441974480182824165158304749516718649649025220777925485791466206103634581255072705342650484455640358613090786660461421253993550507950348320928218432519077480599730200658932920077410634227360733443685735292967916831399116064120412162658141350527921277992273883040331218903988166013157975803163460856425614856286368353019742270391392766192271562975048753861584826326657698616372812268555613000908617975285699181517901950270956036707233835172176672890557624312122097914001305086283047969475449828792934425744440718986513435852555801333552404718203266041383764440164789887/2403992544045298154732428665680610741914412853406352448832137712966029052347236768127270761248387131946885330373828726982800495208217577359965557104323330221479919073891102948294602668502445227901432755298059403200210517740775077058648779286283789200778953559237700749059283980142099713852075792762091287511357823650671188748391122420483440575087773899271875901577410380043961830071249996174098098850005969975127596338857391331120254144607991039409293864770341755652557564342939125780988254270433361233729514791255042393127995943131423619566239843897415231977483390286366703446172822013371144299355052802069808485128472603420669137501508087558612801881016389191196637448035813420916523467533034721392895696000000000000000000000000:ℂ)*Complex.I

theorem node6_coefficient :
    Lagrange.nodalWeight Finset.univ center 6*polePolynomial.eval (center 6)=node6Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [pow_succ,Fin.prod_univ_succ,center,polePolynomial,node6Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node6_bound :
    |(Lagrange.nodalWeight Finset.univ center 6*polePolynomial.eval (center 6)).re|+
    |(Lagrange.nodalWeight Finset.univ center 6*polePolynomial.eval (center 6)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node6_coefficient]
  norm_num [node6Coefficient]

#print axioms node6_coefficient
#print axioms node6_bound

def node7Coefficient : ℂ := (-1694144460959523488787885237759752485285629914023643369991857423161305786969745171107072390983480205678140776325819852688342178103379409509367665429039335300509269782590003515760169352493186709620563782779098954238489923982999362727173364421715578367242456687248839090976281017473428002530812335623939070705441280972224480417697459478666281592551525879132976389886520952985359779848597955922574447767578030838938563647402546310572040921311289902063046461736929132940293670657136636111461987160543243068528760199280901413609345625236337150774187545510251438106205309026019222148269362460398915047394679593851185735946319476413405166024530661485607654757063803802673654820224413632013/593147535268167713718264718693099658727252144138686286346267205714605246020089557150496318198912823733105213233950303831495250211816429105598310871438024206629525820716405340326339302265795776424564329422508856992062839327608497386415076237225897011235217269465629784718806558349397875685036901780548918539215691247014629793822762418475302714182823637666988568717257995531671894014707272346642760009578868827456901167512308942004248144647779105786366822477783383408074353764800701837508087266340579194770802367019198825803940639908045895473564217949838330337497245840964390852995523035988768782979796964721914281188638604670746520894878753937751055783511039728033718816593760488297656250000000000000000000000:ℂ) + (-18907228861026366143370969159810115627048984076361707004340600475225415835737047407667245943279348822350721242495952703265898448793597802983867366139551683971745929391026829221236329073033896402056557695886219083178370931437037095728311333204662127576207636953389445162927923529563375320443142887001151020166359941486443880828414817817517299811588253948971239955528270943759436966275219286064653165964501126528021162419394408211308560831403815924441920340787063813918308025535308460017482736360461839528385758631300331544779759266221875414381492673700861494832489425541209695931441989402829462008153157366700779277325878561977176836144020874128480481189828820780935271867681063514506244155516395460573522310849/1022650315798968244470133447579415761454852534983650481667562430614626775291226416638338978466927235918654353756471781552909644984587061202459680618947694538447500133404167143958581511557956567534885628919408772414504090100903607085233733498020814480299374044834617678799249077114809835075527987200736076499311402220113561473341759858644629479266124756991757929346827379909183408437956054401747712557103487477242793251595318573982911494216280742136559814111848286409323407097952097660505775974990634805497254126733839705068131468370400824207536500851451627854232793912119301182852269666756791375223107638338790449322907664724885964437228974858953209225415071516271123479185303843059238043867598064593113722800000000000000000000000000000:ℂ)*Complex.I

theorem node7_coefficient :
    Lagrange.nodalWeight Finset.univ center 7*polePolynomial.eval (center 7)=node7Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [pow_succ,Fin.prod_univ_succ,center,polePolynomial,node7Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node7_bound :
    |(Lagrange.nodalWeight Finset.univ center 7*polePolynomial.eval (center 7)).re|+
    |(Lagrange.nodalWeight Finset.univ center 7*polePolynomial.eval (center 7)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node7_coefficient]
  norm_num [node7Coefficient]

#print axioms node7_coefficient
#print axioms node7_bound

def node8Coefficient : ℂ := (-1694144460959523488787885237759752485285629914023643369991857423161305786969745171107072390983480205678140776325819852688342178103379409509367665429039335300509269782590003515760169352493186709620563782779098954238489923982999362727173364421715578367242456687248839090976281017473428002530812335623939070705441280972224480417697459478666281592551525879132976389886520952985359779848597955922574447767578030838938563647402546310572040921311289902063046461736929132940293670657136636111461987160543243068528760199280901413609345625236337150774187545510251438106205309026019222148269362460398915047394679593851185735946319476413405166024530661485607654757063803802673654820224413632013/593147535268167713718264718693099658727252144138686286346267205714605246020089557150496318198912823733105213233950303831495250211816429105598310871438024206629525820716405340326339302265795776424564329422508856992062839327608497386415076237225897011235217269465629784718806558349397875685036901780548918539215691247014629793822762418475302714182823637666988568717257995531671894014707272346642760009578868827456901167512308942004248144647779105786366822477783383408074353764800701837508087266340579194770802367019198825803940639908045895473564217949838330337497245840964390852995523035988768782979796964721914281188638604670746520894878753937751055783511039728033718816593760488297656250000000000000000000000:ℂ) + (18907228861026366143370969159810115627048984076361707004340600475225415835737047407667245943279348822350721242495952703265898448793597802983867366139551683971745929391026829221236329073033896402056557695886219083178370931437037095728311333204662127576207636953389445162927923529563375320443142887001151020166359941486443880828414817817517299811588253948971239955528270943759436966275219286064653165964501126528021162419394408211308560831403815924441920340787063813918308025535308460017482736360461839528385758631300331544779759266221875414381492673700861494832489425541209695931441989402829462008153157366700779277325878561977176836144020874128480481189828820780935271867681063514506244155516395460573522310849/1022650315798968244470133447579415761454852534983650481667562430614626775291226416638338978466927235918654353756471781552909644984587061202459680618947694538447500133404167143958581511557956567534885628919408772414504090100903607085233733498020814480299374044834617678799249077114809835075527987200736076499311402220113561473341759858644629479266124756991757929346827379909183408437956054401747712557103487477242793251595318573982911494216280742136559814111848286409323407097952097660505775974990634805497254126733839705068131468370400824207536500851451627854232793912119301182852269666756791375223107638338790449322907664724885964437228974858953209225415071516271123479185303843059238043867598064593113722800000000000000000000000000000:ℂ)*Complex.I

theorem node8_coefficient :
    Lagrange.nodalWeight Finset.univ center 8*polePolynomial.eval (center 8)=node8Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [pow_succ,Fin.prod_univ_succ,center,polePolynomial,node8Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node8_bound :
    |(Lagrange.nodalWeight Finset.univ center 8*polePolynomial.eval (center 8)).re|+
    |(Lagrange.nodalWeight Finset.univ center 8*polePolynomial.eval (center 8)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node8_coefficient]
  norm_num [node8Coefficient]

#print axioms node8_coefficient
#print axioms node8_bound

def node9Coefficient : ℂ := (-5032787064691507422299750075880460708049514674686663901916112341346670334743593112178153334175280858423119374117675835106244704870779047301977966672475017975674258972895105024251761573701838808366937941718905096965557392667721692764405272008874103477356837201872764723632200344141861336825956779309891479030785177227901274529268623273482261750397102584161017162629818931019095647679376389781284898513024003387019902912637027083467570028561336665615129466402755292606966430034615252275950415665956951593699483518367003078891174518537561490953245066697258951984695948373799838000900398924666793738441052049190179300004546476875242482666283223971016178156984196435694658474434028340989355054090276073588484786211/53114048836191001162096269153451433390051553893186392375739916030640092266300802761157436069878954818851668036977103106382437871984087089363866126452127210846171428011337163905539670694476219858850232187414397331921394427682540391086649565674169250889953613603399759831161792619818766775763523696525386469402779592458159860261488177670996211987505883269160318967375609500236410336189419039141195161394641300318117298318319394500247991017333707410791991179926300573898641001421573871151733954840321129415370630808740766046143799911871412305596201598220466985299881220736349759581777119056540864120105249287591342490111047589769826642391596526295764108505656522874256316004874779629864306706003658507812982041637000000000000000000000000000:ℂ) + (3109861856411005278812306110251633604104095777744347428496995330356102860972555043187311777280915566261699776241276801407629230085408344507110175172433046280801615804065220515283617249624500902355373367469503811049680102270659747398329839308930035103866992558991339691116164808098905909481687363757512742077321916614505608045396879040125114130109236845920859624357093525363952426691842956880953928032260680532419794517364540563604152002655899655649803835010876966461693929442759535831618608959474897534768883018183215950504103574475227562899428328607514477224913460976771688016201070845681728510801758335161026782473275112186364455547737671345651926896178251396624964926486295015528398313087686322089059843792283875555927261382357787371/174406906339367046266687879382319533584860992009412310849634918995153777445247160928929156541300724384789753998226351902159920010712597504850792808376824379058316558196968217049041493864702777167895725691039887800032912753044177925637881707869795044440472770332028107939435390442936247914211691668533151871597125748754399142309713052796531782700669506234193781133539287157084455587788527236275741650312276900031740658628460310757791267935219468630514966519116422682036214177936730871048727951378862356580546211136550479442664861290000750628519023926724903870795565931650662542155455954402103071524667645458680426958599372341796104486770501363011502914599603047875165108379037194764883605667989529117484652613070825460151627840500954000000000000000000000000000000:ℂ)*Complex.I

theorem node9_coefficient :
    Lagrange.nodalWeight Finset.univ center 9*polePolynomial.eval (center 9)=node9Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [pow_succ,Fin.prod_univ_succ,center,polePolynomial,node9Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node9_bound :
    |(Lagrange.nodalWeight Finset.univ center 9*polePolynomial.eval (center 9)).re|+
    |(Lagrange.nodalWeight Finset.univ center 9*polePolynomial.eval (center 9)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node9_coefficient]
  norm_num [node9Coefficient]

#print axioms node9_coefficient
#print axioms node9_bound

def node10Coefficient : ℂ := (-5032787064691507422299750075880460708049514674686663901916112341346670334743593112178153334175280858423119374117675835106244704870779047301977966672475017975674258972895105024251761573701838808366937941718905096965557392667721692764405272008874103477356837201872764723632200344141861336825956779309891479030785177227901274529268623273482261750397102584161017162629818931019095647679376389781284898513024003387019902912637027083467570028561336665615129466402755292606966430034615252275950415665956951593699483518367003078891174518537561490953245066697258951984695948373799838000900398924666793738441052049190179300004546476875242482666283223971016178156984196435694658474434028340989355054090276073588484786211/53114048836191001162096269153451433390051553893186392375739916030640092266300802761157436069878954818851668036977103106382437871984087089363866126452127210846171428011337163905539670694476219858850232187414397331921394427682540391086649565674169250889953613603399759831161792619818766775763523696525386469402779592458159860261488177670996211987505883269160318967375609500236410336189419039141195161394641300318117298318319394500247991017333707410791991179926300573898641001421573871151733954840321129415370630808740766046143799911871412305596201598220466985299881220736349759581777119056540864120105249287591342490111047589769826642391596526295764108505656522874256316004874779629864306706003658507812982041637000000000000000000000000000:ℂ) + (-3109861856411005278812306110251633604104095777744347428496995330356102860972555043187311777280915566261699776241276801407629230085408344507110175172433046280801615804065220515283617249624500902355373367469503811049680102270659747398329839308930035103866992558991339691116164808098905909481687363757512742077321916614505608045396879040125114130109236845920859624357093525363952426691842956880953928032260680532419794517364540563604152002655899655649803835010876966461693929442759535831618608959474897534768883018183215950504103574475227562899428328607514477224913460976771688016201070845681728510801758335161026782473275112186364455547737671345651926896178251396624964926486295015528398313087686322089059843792283875555927261382357787371/174406906339367046266687879382319533584860992009412310849634918995153777445247160928929156541300724384789753998226351902159920010712597504850792808376824379058316558196968217049041493864702777167895725691039887800032912753044177925637881707869795044440472770332028107939435390442936247914211691668533151871597125748754399142309713052796531782700669506234193781133539287157084455587788527236275741650312276900031740658628460310757791267935219468630514966519116422682036214177936730871048727951378862356580546211136550479442664861290000750628519023926724903870795565931650662542155455954402103071524667645458680426958599372341796104486770501363011502914599603047875165108379037194764883605667989529117484652613070825460151627840500954000000000000000000000000000000:ℂ)*Complex.I

theorem node10_coefficient :
    Lagrange.nodalWeight Finset.univ center 10*polePolynomial.eval (center 10)=node10Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [pow_succ,Fin.prod_univ_succ,center,polePolynomial,node10Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node10_bound :
    |(Lagrange.nodalWeight Finset.univ center 10*polePolynomial.eval (center 10)).re|+
    |(Lagrange.nodalWeight Finset.univ center 10*polePolynomial.eval (center 10)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node10_coefficient]
  norm_num [node10Coefficient]

#print axioms node10_coefficient
#print axioms node10_bound

def node11Coefficient : ℂ := (11509902835006589276840570999783974907066034199201756349481430949101807611833824827729836166398307296121043218239579922673504536212264227349544734717794819899926837964028711144601216443118795253717650321495263237744398433283699566008877038180080240327822353689857472914589140342235801268309525850898099512650835085387455637356465817169747746679024032434623275979360991926927565348804437624825958828145467531979604921040046785699264592058968861075619865967118727964455234316018555449083412946855109836642535654893597243186186509479935069367066310809961927876648591440893053351749962333465268315820694791041357288504243042145919059245199071433090278864293593477239/242115365860261137136583224829676764601928975891079729148390846824074859837781807761130501432510373932919060701861054041079254194174903427309743884669029128175805073571030775918738569554353270245819627227941995296157745937001660183485072002554535393455147382961426661846230404481606755029471007831226520420225821224576905092156535858043614467134310377449775307357590819123282032683378082705170614882766738869093747048235073276462486941391787387861690151923266237262890510648992419649973371105755362918993216229870556258703704722999015814139536960360929431035709787956430268403574445839301782898245689679548604961457073779931936682256336234244741834078762694513522292497657406250000000000:ℂ) + (-2917409705920184982181489602601188746259448545173819806021912635973167508680306089236325960089908630006505598625124772867385381208271639199292049735483001291411397015692031443803770212104450698061428967726770183221633508234910995767134003474457774394627861203754796572202995859746688951133341002698431305753149302696741715182735782911528437581394707504345647460573305735179732446320328510721032606523640812704652962211573380767488165633331611872945842567275393300423118362883932572188104173207835735857063302479630347449065937990886242506857361410379779344145685612066319233532395850768928611020618033485613145657506851122755793900998744251392407175824272228479832072029745978429289359/83003921208819652109464104258225796575477441442468141405720163752245663855128197256746155024744177016217553036019718303421755276438554474167456554172379824323284869716977644473837077681265428291186470783588257582062031269936339936147109988902123024912583176202526293992884818523958488639723790223065924149956042762641594647447434298628573948149087968183886395710582968466279607484948828311279832984291293861382721951327734957130833841279562982127492591854933659892891243879759547135235537786128217484225833995447261920417849520693799806801443361846178578111159207617126314853435931856890016726579029312629746106612555903000515666514266281210169675696125327926627609835220774964930634650935671659406250000000000:ℂ)*Complex.I

theorem node11_coefficient :
    Lagrange.nodalWeight Finset.univ center 11*polePolynomial.eval (center 11)=node11Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [pow_succ,Fin.prod_univ_succ,center,polePolynomial,node11Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node11_bound :
    |(Lagrange.nodalWeight Finset.univ center 11*polePolynomial.eval (center 11)).re|+
    |(Lagrange.nodalWeight Finset.univ center 11*polePolynomial.eval (center 11)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node11_coefficient]
  norm_num [node11Coefficient]

#print axioms node11_coefficient
#print axioms node11_bound

def node12Coefficient : ℂ := (11509902835006589276840570999783974907066034199201756349481430949101807611833824827729836166398307296121043218239579922673504536212264227349544734717794819899926837964028711144601216443118795253717650321495263237744398433283699566008877038180080240327822353689857472914589140342235801268309525850898099512650835085387455637356465817169747746679024032434623275979360991926927565348804437624825958828145467531979604921040046785699264592058968861075619865967118727964455234316018555449083412946855109836642535654893597243186186509479935069367066310809961927876648591440893053351749962333465268315820694791041357288504243042145919059245199071433090278864293593477239/242115365860261137136583224829676764601928975891079729148390846824074859837781807761130501432510373932919060701861054041079254194174903427309743884669029128175805073571030775918738569554353270245819627227941995296157745937001660183485072002554535393455147382961426661846230404481606755029471007831226520420225821224576905092156535858043614467134310377449775307357590819123282032683378082705170614882766738869093747048235073276462486941391787387861690151923266237262890510648992419649973371105755362918993216229870556258703704722999015814139536960360929431035709787956430268403574445839301782898245689679548604961457073779931936682256336234244741834078762694513522292497657406250000000000:ℂ) + (2917409705920184982181489602601188746259448545173819806021912635973167508680306089236325960089908630006505598625124772867385381208271639199292049735483001291411397015692031443803770212104450698061428967726770183221633508234910995767134003474457774394627861203754796572202995859746688951133341002698431305753149302696741715182735782911528437581394707504345647460573305735179732446320328510721032606523640812704652962211573380767488165633331611872945842567275393300423118362883932572188104173207835735857063302479630347449065937990886242506857361410379779344145685612066319233532395850768928611020618033485613145657506851122755793900998744251392407175824272228479832072029745978429289359/83003921208819652109464104258225796575477441442468141405720163752245663855128197256746155024744177016217553036019718303421755276438554474167456554172379824323284869716977644473837077681265428291186470783588257582062031269936339936147109988902123024912583176202526293992884818523958488639723790223065924149956042762641594647447434298628573948149087968183886395710582968466279607484948828311279832984291293861382721951327734957130833841279562982127492591854933659892891243879759547135235537786128217484225833995447261920417849520693799806801443361846178578111159207617126314853435931856890016726579029312629746106612555903000515666514266281210169675696125327926627609835220774964930634650935671659406250000000000:ℂ)*Complex.I

theorem node12_coefficient :
    Lagrange.nodalWeight Finset.univ center 12*polePolynomial.eval (center 12)=node12Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [pow_succ,Fin.prod_univ_succ,center,polePolynomial,node12Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node12_bound :
    |(Lagrange.nodalWeight Finset.univ center 12*polePolynomial.eval (center 12)).re|+
    |(Lagrange.nodalWeight Finset.univ center 12*polePolynomial.eval (center 12)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node12_coefficient]
  norm_num [node12Coefficient]

#print axioms node12_coefficient
#print axioms node12_bound

def node13Coefficient : ℂ := (28110264747838274659457614843810957729442515911284987960541249181465766283447849172861187598847645975710997724437926522660059590757972101815952440784096493471332743967982793179075333554351665532589317435281190300993394423597581189097812475119599914537281112107086430350321230236007847516753666317689089056690863391265527873946164415864455071095106409587671774681082881687088666403495708090006137352157019289276247749218295985079009969909124761777660987709875095068645747098378247948482267622362287754438451751381182037177792335077478923123914426141784646422735015820474512999194023126435646157332703694763406656608040606139694773801269511161892520455638565669620439012569795606563/1878936946625296028473858735308150697545976232358386517863513912634439249424934382634232524980198257910391230397701554807897268452857935145287923058972955672540123575899140557271927890046279859872360721029591068751560475052694969752299351482343795036274362276068617150701672821389123337668034839051078255947755690018285319233093613621612893585813313365623627691483151451993085629769191932780102411167769351057985719427048240895017251038365021132613513898725637108699632325155681506794218572712784547394209071482538094013266110990505614353621575054109635614273769217053277786939733848886178696505418049067687064697706718465356461450311274275632943342988625614964388544097005216858735351562500000000000000000:ℂ) + (-9824145053899804796116873707824361119094302294104589460906962868753750594987437189942248258809778560639189346099120823247595580022081757161137156733536685387507368831727470932354788648841400079370891390484110696371859602698702743240791325350167702459389237044854825187786839588708307811040079905517935570248936181591858882286891286297928579928247036266165291730431019164755818830813747714955932989164688219108743677931734742032551499906444855441376100869712656122039864588035842153793636075214599843626993122575358412428828787762040876274274870530944618825800744154168771734840945439642166462276563275033111449840819092673069785437102609648219863660274059414705768552442366984707010445056499284608924623/3574923980042498125919721994113420368124475689833953308423730115691092114124054695165137050199063116877581445398536527350463937298033536959441833214429551585407349780820716265668723878073962205194388895968757407802234803237424435517772978375984083655325553393033118723039312217295417469934871793569655263166801480315347821910656212607795160254615406383401499789910984351343364848474283825949446384856731873207644752869080691019706634728712270281304578911628369995828256161613287215738195532761162246946825697125692346126915230215603183730425731040399804962147074901012260806200436929868190499883311307225579585945457455625017121066634972778623816684887653477323388133345806838954293870382541932564786497348632812500000000000000000:ℂ)*Complex.I

theorem node13_coefficient :
    Lagrange.nodalWeight Finset.univ center 13*polePolynomial.eval (center 13)=node13Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [pow_succ,Fin.prod_univ_succ,center,polePolynomial,node13Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node13_bound :
    |(Lagrange.nodalWeight Finset.univ center 13*polePolynomial.eval (center 13)).re|+
    |(Lagrange.nodalWeight Finset.univ center 13*polePolynomial.eval (center 13)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node13_coefficient]
  norm_num [node13Coefficient]

#print axioms node13_coefficient
#print axioms node13_bound

def node14Coefficient : ℂ := (28110264747838274659457614843810957729442515911284987960541249181465766283447849172861187598847645975710997724437926522660059590757972101815952440784096493471332743967982793179075333554351665532589317435281190300993394423597581189097812475119599914537281112107086430350321230236007847516753666317689089056690863391265527873946164415864455071095106409587671774681082881687088666403495708090006137352157019289276247749218295985079009969909124761777660987709875095068645747098378247948482267622362287754438451751381182037177792335077478923123914426141784646422735015820474512999194023126435646157332703694763406656608040606139694773801269511161892520455638565669620439012569795606563/1878936946625296028473858735308150697545976232358386517863513912634439249424934382634232524980198257910391230397701554807897268452857935145287923058972955672540123575899140557271927890046279859872360721029591068751560475052694969752299351482343795036274362276068617150701672821389123337668034839051078255947755690018285319233093613621612893585813313365623627691483151451993085629769191932780102411167769351057985719427048240895017251038365021132613513898725637108699632325155681506794218572712784547394209071482538094013266110990505614353621575054109635614273769217053277786939733848886178696505418049067687064697706718465356461450311274275632943342988625614964388544097005216858735351562500000000000000000:ℂ) + (9824145053899804796116873707824361119094302294104589460906962868753750594987437189942248258809778560639189346099120823247595580022081757161137156733536685387507368831727470932354788648841400079370891390484110696371859602698702743240791325350167702459389237044854825187786839588708307811040079905517935570248936181591858882286891286297928579928247036266165291730431019164755818830813747714955932989164688219108743677931734742032551499906444855441376100869712656122039864588035842153793636075214599843626993122575358412428828787762040876274274870530944618825800744154168771734840945439642166462276563275033111449840819092673069785437102609648219863660274059414705768552442366984707010445056499284608924623/3574923980042498125919721994113420368124475689833953308423730115691092114124054695165137050199063116877581445398536527350463937298033536959441833214429551585407349780820716265668723878073962205194388895968757407802234803237424435517772978375984083655325553393033118723039312217295417469934871793569655263166801480315347821910656212607795160254615406383401499789910984351343364848474283825949446384856731873207644752869080691019706634728712270281304578911628369995828256161613287215738195532761162246946825697125692346126915230215603183730425731040399804962147074901012260806200436929868190499883311307225579585945457455625017121066634972778623816684887653477323388133345806838954293870382541932564786497348632812500000000000000000:ℂ)*Complex.I

theorem node14_coefficient :
    Lagrange.nodalWeight Finset.univ center 14*polePolynomial.eval (center 14)=node14Coefficient := by
  rw [nodalWeight_full_product]
  apply Complex.ext <;>
    norm_num [pow_succ,Fin.prod_univ_succ,center,polePolynomial,node14Coefficient,
      Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.normSq]

theorem node14_bound :
    |(Lagrange.nodalWeight Finset.univ center 14*polePolynomial.eval (center 14)).re|+
    |(Lagrange.nodalWeight Finset.univ center 14*polePolynomial.eval (center 14)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
  rw [node14_coefficient]
  norm_num [node14Coefficient]

#print axioms node14_coefficient
#print axioms node14_bound

}

end QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
end
end

/-! ## ThirtyFivePositiveRootDiskCover -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
open QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
/-- Every root is covered by the certified rational disks. This uses only
exact barycentric identities and the general Lagrange interpolation bound. -/
theorem positive_root_in_disk (z : ℂ) (hz : positiveGenericP15 z=0) :
    ∃ i : Fin 15, ‖z-center i‖ < (1/1000000000000000000 : ℝ) := by
  have hb : ∀ i : Fin 15,
      |(Lagrange.nodalWeight Finset.univ center i*polePolynomial.eval (center i)).re|+
      |(Lagrange.nodalWeight Finset.univ center i*polePolynomial.eval (center i)).im| ≤
      (1/1000000000000000000000 : ℝ) := by
    intro i
    fin_cases i
    · exact node0_bound
    · exact node1_bound
    · exact node2_bound
    · exact node3_bound
    · exact node4_bound
    · exact node5_bound
    · exact node6_bound
    · exact node7_bound
    · exact node8_bound
    · exact node9_bound
    · exact node10_bound
    · exact node11_bound
    · exact node12_bound
    · exact node13_bound
    · exact node14_bound
  have hr : ∀ i ∈ (Finset.univ : Finset (Fin 15)),
      (0:ℝ)<1/1000000000000000000 := by intros; norm_num
  have hsmall : ∑ _i : Fin 15, (1/1000:ℝ)<1 := by norm_num
  have hbound : ∀ i ∈ (Finset.univ : Finset (Fin 15)),
      |(Lagrange.nodalWeight Finset.univ center i*polePolynomial.eval (center i)).re|+
      |(Lagrange.nodalWeight Finset.univ center i*polePolynomial.eval (center i)).im| ≤
      (1/1000:ℝ)*(1/1000000000000000000) := by
    intro i _
    convert hb i using 1; norm_num
  obtain ⟨i,_,hi⟩ := QuantitativeArithmeticPolynomialRootCover.monic_root_cover_of_coordinate_bounds
    Finset.univ center (fun _ => 1/1000000000000000000) (fun _ => 1/1000)
    polePolynomial center_injective.injOn polePolynomial_monic
    (by simpa using polePolynomial_degree) hr hbound hsmall z
    (by simpa only [polePolynomial_eval] using hz)
  exact ⟨i,hi⟩

#print axioms positive_root_in_disk
}

end QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
end
end

/-! ## ThirtyFivePositiveDiskExclusion -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
open QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
/-- Rational norm bounds at a center and a common variation estimate
exclude the entire disk from the physical modulus constraints. -/
theorem disk_exclusion (z c : ℂ) (U : ℝ)
    (hc : ‖c‖≤U) (hU : U+1/1000000000000000000<4)
    (hclose : ‖z-c‖<(1/1000000000000000000:ℝ))
    (halt : U+1/1000000000000000000<1 ∨
      ‖positiveGenericQ14 c‖+1/10000<1 ∨
      (U+1/1000000000000000000)^2+1/10000<‖positiveGenericQ14 c‖ ∨
      ‖positiveGenericR14 c‖+1/10000<1)
    (hx : 1≤‖z‖) (hy : 1≤‖positiveGenericQ14 z‖)
    (hyx : ‖positiveGenericQ14 z‖≤‖z‖^2) (hr : 1≤‖positiveGenericR14 z‖) : False := by
  have htri : ‖z‖≤‖z-c‖+‖c‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z-c) c
  have hzu : ‖z‖<U+1/1000000000000000000 := by linarith
  have hz4 : ‖z‖≤4 := (hzu.trans hU).le
  have hc4 : ‖c‖≤4 := by linarith
  have hv := q_variation z c hz4 hc4
  have hdiff : ‖positiveGenericQ14 z-positiveGenericQ14 c‖<(1/10000:ℝ) := by nlinarith
  rcases halt with hsmall | hsmall | hlarge | hrsmall
  · linarith
  · have ht : ‖positiveGenericQ14 z‖≤‖positiveGenericQ14 z-positiveGenericQ14 c‖+‖positiveGenericQ14 c‖ := by
      simpa only [sub_add_cancel] using
        norm_add_le (positiveGenericQ14 z-positiveGenericQ14 c) (positiveGenericQ14 c)
    linarith
  · have ht : ‖positiveGenericQ14 c‖≤‖positiveGenericQ14 z-positiveGenericQ14 c‖+‖positiveGenericQ14 z‖ := by
      calc
        ‖positiveGenericQ14 c‖ = ‖(positiveGenericQ14 c-positiveGenericQ14 z)+positiveGenericQ14 z‖ := by rw [sub_add_cancel]
        _ ≤ ‖positiveGenericQ14 c-positiveGenericQ14 z‖+‖positiveGenericQ14 z‖ := norm_add_le _ _
        _ = ‖positiveGenericQ14 z-positiveGenericQ14 c‖+‖positiveGenericQ14 z‖ := by rw [norm_sub_rev]
    have hs : ‖z‖^2≤(U+1/1000000000000000000)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hzu.le 2
    linarith

  · have hrv := r_variation z c hz4 hc4
    have hrdiff : ‖positiveGenericR14 z-positiveGenericR14 c‖<(1/10000:ℝ) := by nlinarith
    have ht : ‖positiveGenericR14 z‖≤‖positiveGenericR14 z-positiveGenericR14 c‖+‖positiveGenericR14 c‖ := by
      simpa only [sub_add_cancel] using norm_add_le (positiveGenericR14 z-positiveGenericR14 c) (positiveGenericR14 c)
    linarith

#print axioms disk_exclusion
}

end QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
end
end

/-! ## ThirtyFivePositivePhysicalExclusion -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
open QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
theorem positive_no_physical_root (z : ℂ) (hP : positiveGenericP15 z=0)
    (hx : 1≤‖z‖) (hy : 1≤‖positiveGenericQ14 z‖)
    (hyx : ‖positiveGenericQ14 z‖≤‖z‖^2) (hr : 1≤‖positiveGenericR14 z‖) : False := by
  obtain ⟨i,hi⟩ := positive_root_in_disk z hP
  fin_cases i
  · exact disk_exclusion z (center 0) (260691/250000:ℝ) disk0_bounds.1 disk0_bounds.2.1 hi disk0_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 1) (1630577/1000000:ℝ) disk1_bounds.1 disk1_bounds.2.1 hi disk1_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 2) (888117/500000:ℝ) disk2_bounds.1 disk2_bounds.2.1 hi disk2_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 3) (1153917/1000000:ℝ) disk3_bounds.1 disk3_bounds.2.1 hi disk3_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 4) (1153917/1000000:ℝ) disk4_bounds.1 disk4_bounds.2.1 hi disk4_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 5) (738763/1000000:ℝ) disk5_bounds.1 disk5_bounds.2.1 hi disk5_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 6) (738763/1000000:ℝ) disk6_bounds.1 disk6_bounds.2.1 hi disk6_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 7) (2700071/1000000:ℝ) disk7_bounds.1 disk7_bounds.2.1 hi disk7_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 8) (2700071/1000000:ℝ) disk8_bounds.1 disk8_bounds.2.1 hi disk8_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 9) (2174061/1000000:ℝ) disk9_bounds.1 disk9_bounds.2.1 hi disk9_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 10) (2174061/1000000:ℝ) disk10_bounds.1 disk10_bounds.2.1 hi disk10_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 11) (1081389/500000:ℝ) disk11_bounds.1 disk11_bounds.2.1 hi disk11_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 12) (1081389/500000:ℝ) disk12_bounds.1 disk12_bounds.2.1 hi disk12_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 13) (234421/100000:ℝ) disk13_bounds.1 disk13_bounds.2.1 hi disk13_bounds.2.2 hx hy hyx hr
  · exact disk_exclusion z (center 14) (234421/100000:ℝ) disk14_bounds.1 disk14_bounds.2.1 hi disk14_bounds.2.2 hx hy hyx hr

#print axioms positive_no_physical_root

}

end QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks
end
end

/-! ## ThirtyFiveOriginalPositiveGenericExclusion -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

certificate_batch {
theorem original_positive_generic_pole_exclusion {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hz : u5*primeParameter 5 m s≠1)
    (hA : (primeParameter 2 m s)^(4:ℕ)+(primeParameter 3 m s)^(2:ℕ)-1≠0)
    (hs : (m:ℝ)≤s.re) : v 192=0 := by
  by_contra hr
  obtain ⟨h0,h1,h2,h3⟩ := original_positive_generic_inputs hm hf ε hε hlaw u5 u7 hu5 hu7
    hphase h5 h7 BG G hG hGF s v hv hshift hr hz hA
  obtain ⟨_,_,hC,_⟩ := original_positive_branch_constraints hm hf ε hε hlaw u5 u7 hu5 hu7
    hphase h5 h7 BG G hG hGF s v hv hshift hr hz
  let X := (primeParameter 2 m s)^(2:ℕ)
  let Y := (primeParameter 3 m s)^(2:ℕ)
  let Z := u5*primeParameter 5 m s
  have hC' : X^(2:ℕ)-Y-3*X-1≠0 := by
    convert hC using 1 <;> dsimp [X,Y] <;> ring
  have hXm : X+1≠0 := by
    intro h
    have hx : X= -1 := by linear_combination h
    change positiveGenericInput0 X Y Z=0 at h0
    rw [hx] at h0
    have hz3 := positive_generic_minus_one Y Z hz h0
    exact signed_prime_two_minus_one_not_three m s u5 hu5 hx hz3
  have hfactor := mul_ne_zero hC' hXm
  have hP := (mul_eq_zero.mp (positive_generic_p15_certificate X Y Z h0 h1 h2 h3)).resolve_left hfactor
  have hQ := sub_eq_zero.mp ((mul_eq_zero.mp
    (positive_generic_y_certificate X Y Z h0 h1 h2 h3)).resolve_left hfactor)
  have hR := sub_eq_zero.mp ((mul_eq_zero.mp
    (positive_generic_z_certificate X Y Z h0 h1 h2 h3)).resolve_left hfactor)
  obtain ⟨hx,hy,hyx⟩ := physical_parameters m s hs
  change 1≤‖X‖ at hx
  change 1≤‖Y‖ at hy
  change ‖Y‖≤‖X‖^(2:ℕ) at hyx
  have hzN : 1≤‖Z‖ := by
    dsimp [Z]
    rw [sign_mul_norm u5 _ hu5,primeParameter_norm 5 m (by decide)]
    exact Real.one_le_rpow (by norm_num) (sub_nonneg.mpr hs)
  rw [hQ] at hy hyx
  rw [hR] at hzN
  exact QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks.positive_no_physical_root
    X hP hx hy hyx hzN

#print axioms original_positive_generic_pole_exclusion
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveA0CoordinateData -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
def positiveA0V84 (T Z X : ℂ) : ℂ := (((-1)*T) + ((1/((1 + (2*X)))^(1:ℕ))*(1/(((-2) + X))^(1:ℕ))*((-1) + Z)*(1 + ((-1)*X) + (X*Z))))

def positiveA0V24 (T Z X : ℂ) : ℂ := ((-3/4:ℂ) + ((-1/2:ℂ)*Z) + ((1/4:ℂ)*(X)^(2:ℕ)) + ((1/4:ℂ)*T*(1/(((-1) + X + ((-1)*X*Z)))^(1:ℕ))*((-2) + ((-1)*(X)^(3:ℕ)) + ((-3)*(X)^(2:ℕ)) + (2*Z) + (6*X) + ((-1)*X*Z) + ((-1)*X*(1 + ((-1)*(X)^(2:ℕ)))))) + ((1/4:ℂ)*(1/(((-1) + X + ((-1)*X*Z)))^(1:ℕ))*(((-1)*T) + ((1/((1 + (2*X)))^(1:ℕ))*(1/(((-2) + X))^(1:ℕ))*((-1) + Z)*(1 + ((-1)*X) + (X*Z))))*(3 + Z + ((-3)*(X)^(2:ℕ)) + (4*X) + ((-1)*X*Z))))

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveA0InputData -/
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
def positiveA0Input0 (T Z X : ℂ) : ℂ := (-2:ℂ)*Z*X^(7:ℕ) + (-5:ℂ)*Z^(3:ℕ)*X^(4:ℕ) + (8:ℂ)*T*Z*X^(5:ℕ) + (1:ℂ)*Z^(2:ℕ)*X^(5:ℕ) + (5:ℂ)*Z*X^(6:ℕ) + (2:ℂ)*X^(7:ℕ) + (2:ℂ)*Z^(3:ℕ)*X^(3:ℕ) + (-18:ℂ)*T*Z*X^(4:ℕ) + (15:ℂ)*Z^(2:ℕ)*X^(4:ℕ) + (-6:ℂ)*T*X^(5:ℕ) + (-13:ℂ)*Z*X^(5:ℕ) + (-7:ℂ)*X^(6:ℕ) + (-3:ℂ)*Z^(3:ℕ)*X^(2:ℕ) + (7:ℂ)*T*Z*X^(3:ℕ) + (-14:ℂ)*Z^(2:ℕ)*X^(3:ℕ) + (29:ℂ)*T*X^(4:ℕ) + (-11:ℂ)*Z*X^(4:ℕ) + (17:ℂ)*X^(5:ℕ) + (-6:ℂ)*Z^(3:ℕ)*X + (-7:ℂ)*T*Z*X^(2:ℕ) + (9:ℂ)*Z^(2:ℕ)*X^(2:ℕ) + (-18:ℂ)*T*X^(3:ℕ) + (51:ℂ)*Z*X^(3:ℕ) + (-10:ℂ)*X^(4:ℕ) + (7:ℂ)*Z^(2:ℕ)*X + (-17:ℂ)*T*X^(2:ℕ) + (-8:ℂ)*Z*X^(2:ℕ) + (-36:ℂ)*X^(3:ℕ) + (4:ℂ)*T*Z + (-6:ℂ)*Z^(2:ℕ) + (-24:ℂ)*T*X + (-2:ℂ)*Z*X + (31:ℂ)*X^(2:ℕ) + (-12:ℂ)*T + (4:ℂ)*Z + (5:ℂ)*X + (-2:ℂ)

def positiveA0Input1 (T Z X : ℂ) : ℂ := (-2:ℂ)*Z*X^(7:ℕ) + (-5:ℂ)*Z^(3:ℕ)*X^(4:ℕ) + (8:ℂ)*T*Z*X^(5:ℕ) + (1:ℂ)*Z^(2:ℕ)*X^(5:ℕ) + (3:ℂ)*Z*X^(6:ℕ) + (2:ℂ)*X^(7:ℕ) + (1:ℂ)*Z^(3:ℕ)*X^(3:ℕ) + (-18:ℂ)*T*Z*X^(4:ℕ) + (16:ℂ)*Z^(2:ℕ)*X^(4:ℕ) + (-6:ℂ)*T*X^(5:ℕ) + (-2:ℂ)*Z*X^(5:ℕ) + (-5:ℂ)*X^(6:ℕ) + (2:ℂ)*Z^(3:ℕ)*X^(2:ℕ) + (9:ℂ)*T*Z*X^(3:ℕ) + (-18:ℂ)*Z^(2:ℕ)*X^(3:ℕ) + (31:ℂ)*T*X^(4:ℕ) + (-5:ℂ)*Z*X^(4:ℕ) + (4:ℂ)*X^(5:ℕ) + (-2:ℂ)*Z^(3:ℕ)*X + (-18:ℂ)*T*Z*X^(2:ℕ) + (-11:ℂ)*Z^(2:ℕ)*X^(2:ℕ) + (-39:ℂ)*T*X^(3:ℕ) + (36:ℂ)*Z*X^(3:ℕ) + (-6:ℂ)*X^(4:ℕ) + (10:ℂ)*T*Z*X + (16:ℂ)*Z^(2:ℕ)*X + (48:ℂ)*T*X^(2:ℕ) + (-20:ℂ)*Z*X^(2:ℕ) + (-8:ℂ)*X^(3:ℕ) + (12:ℂ)*T*Z + (-2:ℂ)*Z^(2:ℕ) + (-66:ℂ)*T*X + (-44:ℂ)*Z*X + (31:ℂ)*X^(2:ℕ) + (-52:ℂ)*T + (12:ℂ)*Z + (4:ℂ)*X + (-22:ℂ)

def positiveA0Input2 (T Z X : ℂ) : ℂ := (-2:ℂ)*Z*X^(7:ℕ) + (-1:ℂ)*Z^(3:ℕ)*X^(4:ℕ) + (1:ℂ)*Z^(2:ℕ)*X^(5:ℕ) + (7:ℂ)*Z*X^(6:ℕ) + (2:ℂ)*X^(7:ℕ) + (-13:ℂ)*Z^(3:ℕ)*X^(3:ℕ) + (2:ℂ)*T*Z*X^(4:ℕ) + (-2:ℂ)*Z^(2:ℕ)*X^(4:ℕ) + (2:ℂ)*T*X^(5:ℕ) + (24:ℂ)*Z*X^(5:ℕ) + (-9:ℂ)*X^(6:ℕ) + (12:ℂ)*Z^(3:ℕ)*X^(2:ℕ) + (-7:ℂ)*T*Z*X^(3:ℕ) + (30:ℂ)*Z^(2:ℕ)*X^(3:ℕ) + (-17:ℂ)*T*X^(4:ℕ) + (-45:ℂ)*Z*X^(4:ℕ) + (-18:ℂ)*X^(5:ℕ) + (18:ℂ)*Z^(3:ℕ)*X + (-8:ℂ)*T*Z*X^(2:ℕ) + (-47:ℂ)*Z^(2:ℕ)*X^(2:ℕ) + (27:ℂ)*T*X^(3:ℕ) + (-78:ℂ)*Z*X^(3:ℕ) + (74:ℂ)*X^(4:ℕ) + (22:ℂ)*T*Z*X + (-34:ℂ)*Z^(2:ℕ)*X + (62:ℂ)*T*X^(2:ℕ) + (96:ℂ)*Z*X^(2:ℕ) + (8:ℂ)*X^(3:ℕ) + (12:ℂ)*T*Z + (18:ℂ)*Z^(2:ℕ) + (-98:ℂ)*T*X + (44:ℂ)*Z*X + (-113:ℂ)*X^(2:ℕ) + (-60:ℂ)*T + (-28:ℂ)*Z + (18:ℂ)*X + (38:ℂ)

def positiveA0Input3 (T Z X : ℂ) : ℂ := (-4:ℂ)*Z*X^(7:ℕ) + (-10:ℂ)*Z^(3:ℕ)*X^(4:ℕ) + (16:ℂ)*T*Z*X^(5:ℕ) + (2:ℂ)*Z^(2:ℕ)*X^(5:ℕ) + (8:ℂ)*Z*X^(6:ℕ) + (4:ℂ)*X^(7:ℕ) + (3:ℂ)*Z^(3:ℕ)*X^(3:ℕ) + (-36:ℂ)*T*Z*X^(4:ℕ) + (31:ℂ)*Z^(2:ℕ)*X^(4:ℕ) + (-12:ℂ)*T*X^(5:ℕ) + (-15:ℂ)*Z*X^(5:ℕ) + (-12:ℂ)*X^(6:ℕ) + (-1:ℂ)*Z^(3:ℕ)*X^(2:ℕ) + (16:ℂ)*T*Z*X^(3:ℕ) + (-32:ℂ)*Z^(2:ℕ)*X^(3:ℕ) + (60:ℂ)*T*X^(4:ℕ) + (-16:ℂ)*Z*X^(4:ℕ) + (21:ℂ)*X^(5:ℕ) + (-8:ℂ)*Z^(3:ℕ)*X + (-9:ℂ)*T*Z*X^(2:ℕ) + (-2:ℂ)*Z^(2:ℕ)*X^(2:ℕ) + (-41:ℂ)*T*X^(3:ℕ) + (87:ℂ)*Z*X^(3:ℕ) + (-16:ℂ)*X^(4:ℕ) + (-14:ℂ)*T*Z*X + (23:ℂ)*Z^(2:ℕ)*X + (-73:ℂ)*T*X^(2:ℕ) + (-28:ℂ)*Z*X^(2:ℕ) + (-44:ℂ)*X^(3:ℕ) + (-8:ℂ)*Z^(2:ℕ) + (14:ℂ)*T*X + (-46:ℂ)*Z*X + (62:ℂ)*X^(2:ℕ) + (16:ℂ)*T + (16:ℂ)*Z + (9:ℂ)*X + (-24:ℂ)

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveA0ScalarRowBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
theorem positive_a0_scalar_row13 (T Z X : ℂ)
    (hX : X≠0) (hY : 1-X^(2:ℕ)≠0)
    (hW : X*Z-X+1≠0) (hC1 : X-2≠0) (hC2 : 2*X+1≠0) :
    positiveReduced13C24 X (1-X^(2:ℕ)) Z (-X*Z+X-1)*positiveA0V24 T Z X + positiveReduced13C42 X (1-X^(2:ℕ)) Z (-X*Z+X-1)*T + positiveReduced13C84 X (1-X^(2:ℕ)) Z (-X*Z+X-1)*positiveA0V84 T Z X + positiveReduced13C192 X (1-X^(2:ℕ)) Z (-X*Z+X-1) = ((-1/4:ℂ)*Z*(1/(X)^(1:ℕ))*(1/((1 + X))^(1:ℕ))*(1/((1 + (2*X)))^(1:ℕ))*(1/(((-1) + X))^(1:ℕ))*(1/(((-2) + X))^(1:ℕ))*(1/((1 + ((-1)*X) + (X*Z)))^(1:ℕ)))*positiveA0Input1 T Z X := by
  have hW' : -X*Z+X-1≠0 := by
    convert neg_ne_zero.mpr hW using 1 <;> ring
  have hW'' : -1+X-X*Z≠0 := by convert hW' using 1 <;> ring
  have hWalt : 1-X+X*Z≠0 := by convert hW using 1 <;> ring
  have hXm : X-1≠0 := by
    intro h
    apply hY
    linear_combination -(X+1)*h
  have hXp : X+1≠0 := by
    intro h
    apply hY
    linear_combination -(X-1)*h
  unfold positiveReduced13C24 positiveReduced13C42 positiveReduced13C84 positiveReduced13C192 positiveA0V24 positiveA0V84 positiveA0Input1
  generalize hd0 : (1-X^(2:ℕ))=D0
  have hn0 : D0≠0 := by
    rw [←hd0]
    convert hY using 1 <;> ring
  generalize hd1 : (1+(-1)*X^(2:ℕ))=D1
  have hn1 : D1≠0 := by
    rw [←hd1]
    convert hY using 1 <;> ring
  generalize hd2 : ((-2)+X)=D2
  have hn2 : D2≠0 := by
    rw [←hd2]
    convert hC1 using 1 <;> ring
  generalize hd3 : (X-2)=D3
  have hn3 : D3≠0 := by
    rw [←hd3]
    convert hC1 using 1 <;> ring
  generalize hd4 : (1+2*X)=D4
  have hn4 : D4≠0 := by
    rw [←hd4]
    convert hC2 using 1 <;> ring
  generalize hd5 : (2*X+1)=D5
  have hn5 : D5≠0 := by
    rw [←hd5]
    convert hC2 using 1 <;> ring
  generalize hd6 : ((-1)+X+(-1)*X*Z)=D6
  have hn6 : D6≠0 := by
    rw [←hd6]
    convert hW'' using 1 <;> ring
  generalize hd7 : (-X*Z+X-1)=D7
  have hn7 : D7≠0 := by
    rw [←hd7]
    convert hW' using 1 <;> ring
  generalize hd8 : (1+(-1)*X+X*Z)=D8
  have hn8 : D8≠0 := by
    rw [←hd8]
    convert hWalt using 1 <;> ring
  generalize hd9 : (X*Z-X+1)=D9
  have hn9 : D9≠0 := by
    rw [←hd9]
    convert hW using 1 <;> ring
  generalize hd10 : ((-1)+X)=D10
  have hn10 : D10≠0 := by
    rw [←hd10]
    convert hXm using 1 <;> ring
  generalize hd11 : (X-1)=D11
  have hn11 : D11≠0 := by
    rw [←hd11]
    convert hXm using 1 <;> ring
  generalize hd12 : (1+X)=D12
  have hn12 : D12≠0 := by
    rw [←hd12]
    convert hXp using 1 <;> ring
  generalize hd13 : (X+1)=D13
  have hn13 : D13≠0 := by
    rw [←hd13]
    convert hXp using 1 <;> ring
  field_simp [hX,hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13]
  subst D13 D12 D11 D10 D9 D8 D7 D6 D5 D4 D3 D2 D1 D0
  ring

#print axioms positive_a0_scalar_row13

theorem positive_a0_scalar_row164 (T Z X : ℂ)
    (hX : X≠0) (hY : 1-X^(2:ℕ)≠0)
    (hW : X*Z-X+1≠0) (hC1 : X-2≠0) (hC2 : 2*X+1≠0) :
    positiveReduced164C24 X (1-X^(2:ℕ)) Z (-X*Z+X-1)*positiveA0V24 T Z X + positiveReduced164C42 X (1-X^(2:ℕ)) Z (-X*Z+X-1)*T + positiveReduced164C84 X (1-X^(2:ℕ)) Z (-X*Z+X-1)*positiveA0V84 T Z X + positiveReduced164C192 X (1-X^(2:ℕ)) Z (-X*Z+X-1) = ((1/4:ℂ)*(1/((1 + X))^(1:ℕ))*(1/((1 + (2*X)))^(1:ℕ))*(1/(((-1) + X))^(1:ℕ))*(1/(((-2) + X))^(1:ℕ))*(1/((1 + ((-1)*X) + (X*Z)))^(1:ℕ)))*positiveA0Input3 T Z X := by
  have hW' : -X*Z+X-1≠0 := by
    convert neg_ne_zero.mpr hW using 1 <;> ring
  have hW'' : -1+X-X*Z≠0 := by convert hW' using 1 <;> ring
  have hWalt : 1-X+X*Z≠0 := by convert hW using 1 <;> ring
  have hXm : X-1≠0 := by
    intro h
    apply hY
    linear_combination -(X+1)*h
  have hXp : X+1≠0 := by
    intro h
    apply hY
    linear_combination -(X-1)*h
  unfold positiveReduced164C24 positiveReduced164C42 positiveReduced164C84 positiveReduced164C192 positiveA0V24 positiveA0V84 positiveA0Input3
  generalize hd0 : (1-X^(2:ℕ))=D0
  have hn0 : D0≠0 := by
    rw [←hd0]
    convert hY using 1 <;> ring
  generalize hd1 : (1+(-1)*X^(2:ℕ))=D1
  have hn1 : D1≠0 := by
    rw [←hd1]
    convert hY using 1 <;> ring
  generalize hd2 : ((-2)+X)=D2
  have hn2 : D2≠0 := by
    rw [←hd2]
    convert hC1 using 1 <;> ring
  generalize hd3 : (X-2)=D3
  have hn3 : D3≠0 := by
    rw [←hd3]
    convert hC1 using 1 <;> ring
  generalize hd4 : (1+2*X)=D4
  have hn4 : D4≠0 := by
    rw [←hd4]
    convert hC2 using 1 <;> ring
  generalize hd5 : (2*X+1)=D5
  have hn5 : D5≠0 := by
    rw [←hd5]
    convert hC2 using 1 <;> ring
  generalize hd6 : ((-1)+X+(-1)*X*Z)=D6
  have hn6 : D6≠0 := by
    rw [←hd6]
    convert hW'' using 1 <;> ring
  generalize hd7 : (-X*Z+X-1)=D7
  have hn7 : D7≠0 := by
    rw [←hd7]
    convert hW' using 1 <;> ring
  generalize hd8 : (1+(-1)*X+X*Z)=D8
  have hn8 : D8≠0 := by
    rw [←hd8]
    convert hWalt using 1 <;> ring
  generalize hd9 : (X*Z-X+1)=D9
  have hn9 : D9≠0 := by
    rw [←hd9]
    convert hW using 1 <;> ring
  generalize hd10 : ((-1)+X)=D10
  have hn10 : D10≠0 := by
    rw [←hd10]
    convert hXm using 1 <;> ring
  generalize hd11 : (X-1)=D11
  have hn11 : D11≠0 := by
    rw [←hd11]
    convert hXm using 1 <;> ring
  generalize hd12 : (1+X)=D12
  have hn12 : D12≠0 := by
    rw [←hd12]
    convert hXp using 1 <;> ring
  generalize hd13 : (X+1)=D13
  have hn13 : D13≠0 := by
    rw [←hd13]
    convert hXp using 1 <;> ring
  field_simp [hX,hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13]
  subst D13 D12 D11 D10 D9 D8 D7 D6 D5 D4 D3 D2 D1 D0
  ring

#print axioms positive_a0_scalar_row164

theorem positive_a0_scalar_row16 (T Z X : ℂ)
    (hX : X≠0) (hY : 1-X^(2:ℕ)≠0)
    (hW : X*Z-X+1≠0) (hC1 : X-2≠0) (hC2 : 2*X+1≠0) :
    positiveReduced16C24 X (1-X^(2:ℕ)) Z (-X*Z+X-1)*positiveA0V24 T Z X + positiveReduced16C42 X (1-X^(2:ℕ)) Z (-X*Z+X-1)*T + positiveReduced16C84 X (1-X^(2:ℕ)) Z (-X*Z+X-1)*positiveA0V84 T Z X + positiveReduced16C192 X (1-X^(2:ℕ)) Z (-X*Z+X-1) = ((1/4:ℂ)*(1/(X)^(1:ℕ))*(1/((1 + (2*X)))^(1:ℕ))*(1/(((-2) + X))^(1:ℕ))*(1/((1 + ((-1)*X) + (X*Z)))^(1:ℕ)))*positiveA0Input2 T Z X := by
  have hW' : -X*Z+X-1≠0 := by
    convert neg_ne_zero.mpr hW using 1 <;> ring
  have hW'' : -1+X-X*Z≠0 := by convert hW' using 1 <;> ring
  have hWalt : 1-X+X*Z≠0 := by convert hW using 1 <;> ring
  have hXm : X-1≠0 := by
    intro h
    apply hY
    linear_combination -(X+1)*h
  have hXp : X+1≠0 := by
    intro h
    apply hY
    linear_combination -(X-1)*h
  unfold positiveReduced16C24 positiveReduced16C42 positiveReduced16C84 positiveReduced16C192 positiveA0V24 positiveA0V84 positiveA0Input2
  generalize hd0 : (1-X^(2:ℕ))=D0
  have hn0 : D0≠0 := by
    rw [←hd0]
    convert hY using 1 <;> ring
  generalize hd1 : (1+(-1)*X^(2:ℕ))=D1
  have hn1 : D1≠0 := by
    rw [←hd1]
    convert hY using 1 <;> ring
  generalize hd2 : ((-2)+X)=D2
  have hn2 : D2≠0 := by
    rw [←hd2]
    convert hC1 using 1 <;> ring
  generalize hd3 : (X-2)=D3
  have hn3 : D3≠0 := by
    rw [←hd3]
    convert hC1 using 1 <;> ring
  generalize hd4 : (1+2*X)=D4
  have hn4 : D4≠0 := by
    rw [←hd4]
    convert hC2 using 1 <;> ring
  generalize hd5 : (2*X+1)=D5
  have hn5 : D5≠0 := by
    rw [←hd5]
    convert hC2 using 1 <;> ring
  generalize hd6 : ((-1)+X+(-1)*X*Z)=D6
  have hn6 : D6≠0 := by
    rw [←hd6]
    convert hW'' using 1 <;> ring
  generalize hd7 : (-X*Z+X-1)=D7
  have hn7 : D7≠0 := by
    rw [←hd7]
    convert hW' using 1 <;> ring
  generalize hd8 : (1+(-1)*X+X*Z)=D8
  have hn8 : D8≠0 := by
    rw [←hd8]
    convert hWalt using 1 <;> ring
  generalize hd9 : (X*Z-X+1)=D9
  have hn9 : D9≠0 := by
    rw [←hd9]
    convert hW using 1 <;> ring
  generalize hd10 : ((-1)+X)=D10
  have hn10 : D10≠0 := by
    rw [←hd10]
    convert hXm using 1 <;> ring
  generalize hd11 : (X-1)=D11
  have hn11 : D11≠0 := by
    rw [←hd11]
    convert hXm using 1 <;> ring
  generalize hd12 : (1+X)=D12
  have hn12 : D12≠0 := by
    rw [←hd12]
    convert hXp using 1 <;> ring
  generalize hd13 : (X+1)=D13
  have hn13 : D13≠0 := by
    rw [←hd13]
    convert hXp using 1 <;> ring
  field_simp [hX,hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13]
  subst D13 D12 D11 D10 D9 D8 D7 D6 D5 D4 D3 D2 D1 D0
  ring

#print axioms positive_a0_scalar_row16

theorem positive_a0_scalar_row3 (T Z X : ℂ)
    (hX : X≠0) (hY : 1-X^(2:ℕ)≠0)
    (hW : X*Z-X+1≠0) (hC1 : X-2≠0) (hC2 : 2*X+1≠0) :
    positiveReduced3C24 X (1-X^(2:ℕ)) Z (-X*Z+X-1)*positiveA0V24 T Z X + positiveReduced3C42 X (1-X^(2:ℕ)) Z (-X*Z+X-1)*T + positiveReduced3C84 X (1-X^(2:ℕ)) Z (-X*Z+X-1)*positiveA0V84 T Z X + positiveReduced3C192 X (1-X^(2:ℕ)) Z (-X*Z+X-1) = ((1/4:ℂ)*(1/((1 + (2*X)))^(1:ℕ))*(1/(((-2) + X))^(1:ℕ))*(1/((1 + ((-1)*X) + (X*Z)))^(1:ℕ)))*positiveA0Input0 T Z X := by
  have hW' : -X*Z+X-1≠0 := by
    convert neg_ne_zero.mpr hW using 1 <;> ring
  have hW'' : -1+X-X*Z≠0 := by convert hW' using 1 <;> ring
  have hWalt : 1-X+X*Z≠0 := by convert hW using 1 <;> ring
  have hXm : X-1≠0 := by
    intro h
    apply hY
    linear_combination -(X+1)*h
  have hXp : X+1≠0 := by
    intro h
    apply hY
    linear_combination -(X-1)*h
  have hCn := mul_ne_zero hC1 hC2
  have hCW := mul_ne_zero hCn hW
  have hCWn := mul_ne_zero hCn hW'
  have hXn := hXm
  have hXpn := hXp
  have hWnn := hW'
  have hYnn := hY
  ring_nf at hCn hCW hCWn hXn hXpn hWnn hYnn
  unfold positiveReduced3C24 positiveReduced3C42 positiveReduced3C84 positiveReduced3C192 positiveA0V24 positiveA0V84 positiveA0Input0
  field_simp [hX,hY,hW,hW',hW'',hWalt,hC1,hC2,hXm,hXp,hCn,hCW,hCWn,hXn,hXpn,hWnn,hYnn] <;> ring_nf <;>
    field_simp [hX,hY,hW,hW',hW'',hWalt,hC1,hC2,hXm,hXp,hCn,hCW,hCWn,hXn,hXpn,hWnn,hYnn] <;> ring

#print axioms positive_a0_scalar_row3

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveA0Certificate -/
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
theorem positive_a0_certificate (T Z X : ℂ)
    (h0 : positiveA0Input0 T Z X=0)
    (h1 : positiveA0Input1 T Z X=0)
    (h2 : positiveA0Input2 T Z X=0)
    (h3 : positiveA0Input3 T Z X=0)
    : X*Z*(X*Z-X+1)*(X-2)*(2*X+1)*(X-1)*(X+1)*(Z-1)=0 := by
  have h0prime : QuantitativeArithmeticSmallLevelThirtyFivePositiveA0Sparse.positiveA0Input0 T Z X=0 := by
    convert h0 using 1 <;> simp only [positiveA0Input0, QuantitativeArithmeticSmallLevelThirtyFivePositiveA0Sparse.positiveA0Input0] <;> ring
  have h1prime : QuantitativeArithmeticSmallLevelThirtyFivePositiveA0Sparse.positiveA0Input1 T Z X=0 := by
    convert h1 using 1 <;> simp only [positiveA0Input1, QuantitativeArithmeticSmallLevelThirtyFivePositiveA0Sparse.positiveA0Input1] <;> ring
  have h2prime : QuantitativeArithmeticSmallLevelThirtyFivePositiveA0Sparse.positiveA0Input2 T Z X=0 := by
    convert h2 using 1 <;> simp only [positiveA0Input2, QuantitativeArithmeticSmallLevelThirtyFivePositiveA0Sparse.positiveA0Input2] <;> ring
  have h3prime : QuantitativeArithmeticSmallLevelThirtyFivePositiveA0Sparse.positiveA0Input3 T Z X=0 := by
    convert h3 using 1 <;> simp only [positiveA0Input3, QuantitativeArithmeticSmallLevelThirtyFivePositiveA0Sparse.positiveA0Input3] <;> ring
  exact QuantitativeArithmeticSmallLevelThirtyFivePositiveA0Sparse.a0_sparse_certificate T Z X h0prime h1prime h2prime h3prime
#print axioms positive_a0_certificate
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveA0RowsCheck -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveA0RowLink -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
theorem positive_a0_normalized_exclusion (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (hz1 : z≠1)
    (ha : a= -x-1/x) (hb : b=(x^(4:ℕ)-x^(2:ℕ)-2)/y)
    (hA : x^(4:ℕ)+y^(2:ℕ)-1=0)
    (hC : x^(4:ℕ)-3*x^(2:ℕ)-y^(2:ℕ)-1≠0)
    (hwrel : w= -x^(2:ℕ)*z+x^(2:ℕ)-1)
    (hcrow : (x^(4:ℕ)-3*x^(2:ℕ)-y^(2:ℕ)-1)*(v 84+v 42)= -w*(z-1)*v 192)
    (h192 : v 192=1)
    (hRows : positiveRowsConclusion x y z w a b v) : False := by
  let X := x^(2:ℕ)
  have hx4 : x^(4:ℕ)=X^(2:ℕ) := by dsimp [X]; ring
  have hx6 : x^(6:ℕ)=X^(3:ℕ) := by dsimp [X]; ring
  have hX : X≠0 := pow_ne_zero _ hx
  have hY : y^(2:ℕ)=1-X^(2:ℕ) := by dsimp [X]; linear_combination hA
  have hYn : 1-X^(2:ℕ)≠0 := hY ▸ (pow_ne_zero 2 hy)
  have hW : X*z-X+1≠0 := by
    intro h; apply hw
    linear_combination hwrel-h
  have hWn : -X*z+X-1≠0 := hwrel ▸ hw
  have hC1 : X-2≠0 := by
    intro h; apply hC
    dsimp [X] at h
    linear_combination (2*x^(2:ℕ)+1)*h-hA
  have hC2 : 2*X+1≠0 := by
    intro h; apply hC
    dsimp [X] at h
    linear_combination (x^(2:ℕ)-2)*h-hA
  have hXm : X-1≠0 := by
    intro h; apply hYn; linear_combination -(X+1)*h
  have hXp : X+1≠0 := by
    intro h; apply hYn; linear_combination -(X-1)*h
  have hWalt : 1-X+X*z≠0 := by convert hW using 1 <;> ring
  have hCmalt : -2+X≠0 := by convert hC1 using 1 <;> ring
  have hCpalt : 1+2*X≠0 := by convert hC2 using 1 <;> ring
  have hWexact : 1+(-1)*X+X*z≠0 := by convert hW using 1 <;> ring
  have hXmexact : (-1)+X≠0 := by convert hXm using 1 <;> ring
  have hXpexact : 1+X≠0 := by convert hXp using 1 <;> ring
  have hCpRing : 1+X*2≠0 := by convert hC2 using 1 <;> ring
  have h84 : v 84=positiveA0V84 (v 42) z X := by
    unfold positiveA0V84
    rw [h192,mul_one,hY,hwrel,hx4] at hcrow
    change (X^(2:ℕ)-3*X-(1-X^(2:ℕ))-1)*(v 84+v 42)=
      -(-X*z+X-1)*(z-1) at hcrow
    linear_combination (norm := (field_simp [hC1,hC2,hCmalt,hCpalt,hCpRing]; ring_nf; field_simp [hC1,hC2,hCmalt,hCpalt,hCpRing]; ring))
      (1/((X-2)*(2*X+1)))*hcrow
  have h24 : v 24=positiveA0V24 (v 42) z X := by
    have hp := positive_constant_coordinate_pivot x y z w a b v hx hy hw ha hb hRows
    rw [h192,mul_one,hY,hwrel,h84,hx4,hx6] at hp
    unfold positiveA0V24
    change -4*v 24-((X^(3:ℕ)+X*(1-X^(2:ℕ))+X*z-6*X-3*(1-X^(2:ℕ))-2*z+5)/(-X*z+X-1))*v 42-
      (((-X*z+X-1)+X^(2:ℕ)+2*X*z-5*X-2*(1-X^(2:ℕ))-z)/(-X*z+X-1))*positiveA0V84 (v 42) z X+
      (X^(2:ℕ)-2*z-3)=0 at hp
    unfold positiveA0V84 at hp
    linear_combination (norm := (field_simp [hWn,hWalt,hC1,hC2,hCmalt,hCpalt]; ring)) (-1/4:ℂ)*hp
  have hr3 := positive_reduced_row3 x y z w a b v hx hy hw ha hb hRows
  rw [h192,mul_one,hY,hwrel] at hr3
  have hs3 := positive_a0_scalar_row3 (v 42) z X hX hYn hW hC1 hC2
  rw [←h24,←h84] at hs3
  rw [hr3] at hs3
  have hi0 : positiveA0Input0 (v 42) z X=0 := by
    apply (mul_eq_zero.mp hs3.symm).resolve_left
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (div_ne_zero (by norm_num) (pow_ne_zero _ hCpalt))) (div_ne_zero (by norm_num) (pow_ne_zero _ hCmalt))) (div_ne_zero (by norm_num) (pow_ne_zero _ hWexact)))
  have hr13 := positive_reduced_row13 x y z w a b v hx hy hw ha hb hRows
  rw [h192,mul_one,hY,hwrel] at hr13
  have hs13 := positive_a0_scalar_row13 (v 42) z X hX hYn hW hC1 hC2
  rw [←h24,←h84] at hs13
  rw [hr13] at hs13
  have hi1 : positiveA0Input1 (v 42) z X=0 := by
    apply (mul_eq_zero.mp hs13.symm).resolve_left
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hz) (div_ne_zero (by norm_num) (pow_ne_zero _ hX))) (div_ne_zero (by norm_num) (pow_ne_zero _ hXpexact))) (div_ne_zero (by norm_num) (pow_ne_zero _ hCpalt))) (div_ne_zero (by norm_num) (pow_ne_zero _ hXmexact))) (div_ne_zero (by norm_num) (pow_ne_zero _ hCmalt))) (div_ne_zero (by norm_num) (pow_ne_zero _ hWexact)))
  have hr16 := positive_reduced_row16 x y z w a b v hx hy hw ha hb hRows
  rw [h192,mul_one,hY,hwrel] at hr16
  have hs16 := positive_a0_scalar_row16 (v 42) z X hX hYn hW hC1 hC2
  rw [←h24,←h84] at hs16
  rw [hr16] at hs16
  have hi2 : positiveA0Input2 (v 42) z X=0 := by
    apply (mul_eq_zero.mp hs16.symm).resolve_left
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (div_ne_zero (by norm_num) (pow_ne_zero _ hX))) (div_ne_zero (by norm_num) (pow_ne_zero _ hCpalt))) (div_ne_zero (by norm_num) (pow_ne_zero _ hCmalt))) (div_ne_zero (by norm_num) (pow_ne_zero _ hWexact)))
  have hr164 := positive_reduced_row164 x y z w a b v hx hy hw ha hb hRows
  rw [h192,mul_one,hY,hwrel] at hr164
  have hs164 := positive_a0_scalar_row164 (v 42) z X hX hYn hW hC1 hC2
  rw [←h24,←h84] at hs164
  rw [hr164] at hs164
  have hi3 : positiveA0Input3 (v 42) z X=0 := by
    apply (mul_eq_zero.mp hs164.symm).resolve_left
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (div_ne_zero (by norm_num) (pow_ne_zero _ hXpexact))) (div_ne_zero (by norm_num) (pow_ne_zero _ hCpalt))) (div_ne_zero (by norm_num) (pow_ne_zero _ hXmexact))) (div_ne_zero (by norm_num) (pow_ne_zero _ hCmalt))) (div_ne_zero (by norm_num) (pow_ne_zero _ hWexact)))
  have hg := positive_a0_certificate (v 42) z X hi0 hi1 hi2 hi3
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (mul_ne_zero hX hz) hW) hC1) hC2) hXm) hXp)
    (sub_ne_zero.mpr hz1)) hg

#print axioms positive_a0_normalized_exclusion
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalPositiveA0Exclusion -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

certificate_batch {
theorem original_positive_a0_pole_exclusion {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hz : u5*primeParameter 5 m s≠1)
    (hA : (primeParameter 2 m s)^(4:ℕ)+(primeParameter 3 m s)^(2:ℕ)-1=0) : v 192=0 := by
  by_contra hr
  obtain ⟨v',hv',h192,hformula⟩ := hv.normalize (192:Fin 210) hr
  have hr' : v' 192≠0 := by rw [h192]; norm_num
  have hRows := original_positive_rows hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7
    BG G hG hGF s v' hv' hshift
  obtain ⟨hp,hwrel,hC,_⟩ := original_positive_branch_constraints hm hf ε hε hlaw
    u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v' hv' hshift hr' hz
  obtain ⟨_,_,hcrow⟩ := original_positive_branch_parameter hm hf ε hε hlaw
    u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v' hv' hshift hr' hz
  have he := original_all_sign_row118 hm hf ε hε hlaw BG G hG hGF s v' hv' hshift
  rw [h192,mul_one] at he
  let x := primeParameter 2 m s
  let y := primeParameter 3 m s
  let a := (Real.sqrt 2:ℂ)*f 2
  let b := (Real.sqrt 3:ℂ)*f 3
  have hx : x≠0 := primeParameter_ne_zero 2 m (by decide) s
  have hy : y≠0 := primeParameter_ne_zero 3 m (by decide) s
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  have hz0 := mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s)
  have hw0 := mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)
  have ha : a= -x-1/x := by
    change 1+x*a+x^(2:ℕ)=0 at he
    linear_combination (norm := (field_simp [hx]; ring)) (1/x)*he
  have hb : b=(x^(4:ℕ)-x^(2:ℕ)-2)/y := by
    change x^(4:ℕ)-x^(2:ℕ)-y*b-2=0 at hp
    linear_combination (norm := (field_simp [hy]; ring)) -(1/y)*hp
  exact positive_a0_normalized_exclusion x y (u5*primeParameter 5 m s)
    (u7*primeParameter 7 m s) a b v' hx hy hz0 hw0 hz ha hb hA hC hwrel hcrow h192 hRows

#print axioms original_positive_a0_pole_exclusion
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalPositiveZOneExclusion -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

certificate_batch {
theorem original_positive_z_one_pole_exclusion {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hz : u5*primeParameter 5 m s=1)
    : v 192=0 := by
  by_contra hr
  have hB := original_positive_rows hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  rw [hz] at hB
  have he0 := original_all_sign_row118 hm hf ε hε hlaw BG G hG hGF s v hv hshift
  have hx := primeParameter_ne_zero 2 m (by decide) s
  have he := (mul_eq_zero.mp he0).resolve_right hr
  by_cases hw : u7*primeParameter 7 m s+1=0
  · have hw' : u7*primeParameter 7 m s= -1 := by linear_combination hw
    have hs := signed_prime_five_seven_center m s u5 u7 hu5 hu7 hz hw'
    have hp2 : primeParameter 2 m s=1 := by simp only [primeParameter,hs,Complex.cpow_zero]
    have hp3 : primeParameter 3 m s=1 := by simp only [primeParameter,hs,Complex.cpow_zero]
    rw [hp2] at he
    have ha : (Real.sqrt 2:ℂ)*f 2= -2 := by linear_combination he
    rw [hp2,hp3,hw',ha] at hB
    exact hr (positive_rows_signed_central ((Real.sqrt 3:ℂ)*f 3) v hB)
  · have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
    exact hr (positive_z_one_rows (primeParameter 2 m s) (primeParameter 3 m s)
      (u7*primeParameter 7 m s) ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v hx
      (primeParameter_ne_zero 3 m (by decide) s)
      (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s))
      hw (signed_prime_five_one_C_ne_zero m s u5 hu5 hz) he hB)

#print axioms original_positive_z_one_pole_exclusion
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalPositiveProductExclusion -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

certificate_batch {
theorem original_signed_positive_pole_exclusion {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re) : v 192=0 := by
  by_cases hz : u5*primeParameter 5 m s=1
  · exact original_positive_z_one_pole_exclusion hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7
      BG G hG hGF s v hv hshift hz
  · by_cases hA : (primeParameter 2 m s)^(4:ℕ)+(primeParameter 3 m s)^(2:ℕ)-1=0
    · exact original_positive_a0_pole_exclusion hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7
        BG G hG hGF s v hv hshift hz hA
    · exact original_positive_generic_pole_exclusion hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7
        BG G hG hGF s v hv hshift hz hA hs



theorem original_positive_product_pole_exclusion {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hproduct : ε*I^(2*m)*badFive f*badSeven f=1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re) : v 192=0 := by
  have h5 := badFive_sign hf.toEulerData
  have h7 := badSeven_sign hf.toEulerData
  have hu5 : -badFive f=1 ∨ -badFive f= -1 := by
    rcases h5 with h|h <;> simp [h]
  have hu7 : -badSeven f=1 ∨ -badSeven f= -1 := by
    rcases h7 with h|h <;> simp [h]
  have h5sq : (badFive f)^(2:ℕ)=1 := by rcases h5 with h|h <;> rw [h] <;> norm_num
  have h7sq : (badSeven f)^(2:ℕ)=1 := by rcases h7 with h|h <;> rw [h] <;> norm_num
  have hphase : ε*I^(2*m)= (-badFive f)*(-badSeven f) := by
    linear_combination (badFive f*badSeven f)*hproduct-
      (ε*I^(2*m)*(badSeven f)^(2:ℕ))*h5sq-(ε*I^(2*m))*h7sq
  exact original_signed_positive_pole_exclusion hm hf ε hε hlaw
    (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
    BG G hG hGF s v hv hshift hs

#print axioms original_signed_positive_pole_exclusion
#print axioms original_positive_product_pole_exclusion
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

