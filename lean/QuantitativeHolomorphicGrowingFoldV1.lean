module

public import QuantitativeHolomorphicGrowingDepthV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight

theorem ceil_add_one_le_exponential {x B u : ℝ} (hx : 0≤x) (hB : 0≤B)
    (hu : 1≤u) (hxu : x≤Real.exp (B*u)) :
    ((⌈x⌉₊+1:ℕ):ℝ)≤Real.exp ((B+Real.log 3)*u) := by
  have he : 1≤Real.exp (B*u) := Real.one_le_exp (by positivity)
  have hc : ((⌈x⌉₊+1:ℕ):ℝ)≤x+2 := by
    have h := Nat.ceil_lt_add_one hx
    push_cast
    linarith
  apply hc.trans
  calc
    x+2 ≤ 3*Real.exp (B*u) := by linarith
    _ = Real.exp (Real.log 3+B*u) := by rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<3)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hl : 0≤Real.log 3 := Real.log_nonneg (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left hu hl]

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def foldTailCoefficient (P : Parameters A) : ℝ :=
  let P' := AsymptoticReconstructedCount.parameters A P
  terminalFoldTailConstant A P'+lowFoldTailConstant A P' (P'.s+3)*
    AsymptoticCertificateOperators.terminalConstant A P'

theorem foldTailCoefficient_nonneg (P : Parameters A) : 0≤foldTailCoefficient A P := by
  have hρ := (AsymptoticReconstructedCount.parameters A P).rho_pos
  unfold foldTailCoefficient terminalFoldTailConstant lowFoldTailConstant
    AsymptoticCertificateOperators.terminalConstant AsymptoticCertificateBranches.level
  positivity

theorem foldTail_exponential (P : Parameters A) (j : ℕ) :
    reconstructionFoldTailConstant A (AsymptoticReconstructedCount.parameters A P) j≤
      Real.exp (foldTailCoefficient A P+2*j) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let a := terminalFoldTailConstant A P'
  let b := lowFoldTailConstant A P' (P'.s+3)*AsymptoticCertificateOperators.terminalConstant A P'
  have hρ := P'.rho_pos
  have ha : 0≤a := by dsimp [a,terminalFoldTailConstant]; positivity
  have hb : 0≤b := by
    dsimp [b,lowFoldTailConstant,AsymptoticCertificateOperators.terminalConstant,AsymptoticCertificateBranches.level]
    positivity
  have hc : 0≤a+b := add_nonneg ha hb
  have hj : 0≤(j:ℝ) := Nat.cast_nonneg _
  have hpoly : (j:ℝ)*a+(j:ℝ)^2*b≤(a+b)*(1+j)^2 := by
    nlinarith [mul_nonneg ha hj,mul_nonneg hb hj,mul_nonneg ha (sq_nonneg (j:ℝ))]
  have hexp : (1+(j:ℝ))^2≤Real.exp (2*j) := by
    have h := Real.add_one_le_exp (j:ℝ)
    have hm := mul_self_le_mul_self (by positivity : 0≤1+(j:ℝ)) (by linarith : 1+(j:ℝ)≤Real.exp j)
    have he : Real.exp (2*(j:ℝ))=(Real.exp (j:ℝ))^2 := by
      simpa using Real.exp_nat_mul (j:ℝ) 2
    rw [he]
    nlinarith only [hm]
  have hcoeff : a+b≤Real.exp (a+b) := by linarith [Real.add_one_le_exp (a+b)]
  have h := mul_le_mul hcoeff hexp (sq_nonneg _) (Real.exp_nonneg _)
  have hF : reconstructionFoldTailConstant A P' j=(j:ℝ)*a+(j:ℝ)^2*b := by
    dsimp [reconstructionFoldTailConstant,a,b]
    ring
  rw [hF]
  apply hpoly.trans
  apply h.trans_eq
  rw [←Real.exp_add]
  rfl

def foldGrowthConstant (P : Parameters A) (C : ℝ) : ℝ :=
  16+foldTailCoefficient A P+2*reconstructionGrowthConstant A P C+
    newtonAmplificationConstant A P C+C+8+Real.log 3

/-- Actual fold radius from the already checked error schedule, with no
hypothesis on the radius or on the reconstruction error. -/
theorem growing_fold_cutoff (P : Parameters A) {C s : ℝ} (hC : 0≤C)
    (hs : 1≤s) (d : ℕ) (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    let D : ℝ := 2*d+2
    let n := newtonDepth A P D (Real.exp (-8*s))
    let j := reconstructionDepth A P D (Real.exp (-8*s)) n
    (foldCutoff A P D (Real.exp (-8*s)) j n:ℝ)≤Real.exp (foldGrowthConstant A P C*s^4) := by
  let D : ℝ := 2*d+2
  let n := newtonDepth A P D (Real.exp (-8*s))
  let j := reconstructionDepth A P D (Real.exp (-8*s)) n
  let F := reconstructionFoldTailConstant A (AsymptoticReconstructedCount.parameters A P) j
  let V := amplification n
  let K := newtonAmplificationConstant A P C
  let L := reconstructionGrowthConstant A P C
  let B := foldTailCoefficient A P
  let Z := 16+B+2*L+K+C+8
  have hB : 0≤B := foldTailCoefficient_nonneg A P
  have hK : 0≤K := by
    dsimp [K,newtonAmplificationConstant]
    have hl : 0≤Real.log 7 := Real.log_nonneg (by norm_num)
    positivity
  have hL : 0≤L := by
    dsimp [L,reconstructionGrowthConstant,reconstructionThresholdConstant]
    have hl : 0≤Real.log 6 := Real.log_nonneg (by norm_num)
    have ht : 0≤AsymptoticCertificateOperators.terminalConstant A (AsymptoticReconstructedCount.parameters A P) := by
      unfold AsymptoticCertificateOperators.terminalConstant
      positivity
    have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hZ : 0≤Z := by dsimp [Z]; positivity
  have hs2 : 1≤s^2 := by nlinarith
  have hs24 : s^2≤s^4 := by nlinarith [sq_nonneg (s^2-1)]
  have hs4 : 1≤s^4 := hs2.trans hs24
  have hss4 : s≤s^4 := (by nlinarith : s≤s^2).trans hs24
  have hj : (j:ℝ)≤L*s^4 := growing_reconstruction_depth A P hC hs d hd
  have hF : F≤Real.exp ((B+2*L)*s^4) := by
    apply (foldTail_exponential A P j).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hs4 hB]
  have hV : 0≤V := (amplification_pos n).le
  have hVE : V≤Real.exp (K*s^4) := (growing_newton_complexity A P hC hs d hd).2.2
  have hD : 0≤D := by dsimp [D]; positivity
  have hDE : D≤4*Real.exp (C*s^2) := by
    have he : 1≤Real.exp (C*s^2) := Real.one_le_exp (by positivity)
    dsimp [D]
    linarith
  have hF0 : 0≤F := by
    have hρ := (AsymptoticReconstructedCount.parameters A P).rho_pos
    dsimp [F,reconstructionFoldTailConstant,terminalFoldTailConstant,lowFoldTailConstant,
      AsymptoticCertificateOperators.terminalConstant,AsymptoticCertificateBranches.level]
    positivity
  let x := (F*V*D)/(Real.exp (-8*s)/4)
  have hx : 0≤x := by dsimp [x]; positivity
  have hxeq : x=4*F*V*D*Real.exp (8*s) := by
    dsimp [x]
    rw [show Real.exp (-8*s)=(Real.exp (8*s))⁻¹ by rw [←Real.exp_neg]; congr 1; ring]
    field_simp
  have hxE : x≤Real.exp (Z*s^4) := by
    rw [hxeq]
    have hprod : 4*F*V*D*Real.exp (8*s)≤
        16*Real.exp ((B+2*L)*s^4)*Real.exp (K*s^4)*Real.exp (C*s^2)*Real.exp (8*s) := by
      have hh := mul_le_mul (mul_le_mul hF hVE hV (Real.exp_nonneg _)) hDE hD (by positivity)
      have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤4)) (Real.exp_nonneg (8*s))
      convert hh' using 1 <;> ring
    apply hprod.trans
    have h16 : (16:ℝ)≤Real.exp 16 := by linarith [Real.add_one_le_exp 16]
    have hh := mul_le_mul_of_nonneg_right h16
      (by positivity : 0≤Real.exp ((B+2*L)*s^4)*Real.exp (K*s^4)*Real.exp (C*s^2)*Real.exp (8*s))
    have hh' : 16*Real.exp ((B+2*L)*s^4)*Real.exp (K*s^4)*Real.exp (C*s^2)*Real.exp (8*s)≤
        Real.exp (16+(B+2*L)*s^4+K*s^4+C*s^2+8*s) := by
      rw [Real.exp_add,Real.exp_add,Real.exp_add,Real.exp_add]
      convert hh using 1 <;> ring
    apply hh'.trans
    apply Real.exp_le_exp.mpr
    dsimp [Z]
    nlinarith [mul_le_mul_of_nonneg_left hs24 hC]
  exact ceil_add_one_le_exponential hx hZ hs4 hxE

#print axioms foldTail_exponential
#print axioms growing_fold_cutoff

end QuantitativeHolomorphic.Schedule
