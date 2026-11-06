module

public import QuantitativeHolomorphicGrowingFilterComplexityV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight AsymptoticCompactObservationCount

variable {ι : Type*}

theorem natFilter_cast (qs : Finset ι) (r : ι → ℕ) (K d : ℕ) :
    ((K^2*(1+∑ i∈qs,(r i*K)^2)^d:ℕ):ℝ)=
      (K:ℝ)^2*(1+(∑ i∈qs,(r i:ℝ)^2)*(K:ℝ)^2)^d := by
  push_cast
  simp only [mul_pow,Finset.sum_mul]

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def normalizedWordLength (j J n : ℕ) : ℕ :=
  rawReconstructionLength A j J*(3+(rawReconstructionLength A j J)^2)^(4^n)

theorem closedFilterComplexity_growth (hN : 0<N) (P : Parameters A)
    (qs : Finset ι) (r : ι → Row N) (L U : ℝ) (j J n d : ℕ) {a b C s : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hC : 0≤C) (hs : 1≤s)
    (hd : (d:ℝ)≤Real.exp (C*s^2))
    (hV : (4:ℝ)^(4^n)≤Real.exp (a*s^12))
    (hK : (normalizedWordLength A j J n:ℝ)≤Real.exp (a*s^12))
    (hrowsM : (∑ i∈qs,(quantifiedRowMass hN (r i) L U
      ((AsymptoticReconstructedCount.parameters A P).s+4))^2)≤Real.exp (b*s^2))
    (hrowsL : (∑ i∈qs,(quantifiedRowLength hN (r i) L U:ℝ)^2)≤Real.exp (b*s^2)) :
    closedFilterComplexity A hN P qs r L U j J n d≤
      Real.exp (Real.exp ((16+4*a+b+C)*s^2)) := by
  let V := (4:ℝ)^(4^n)
  let K := normalizedWordLength A j J n
  let Sm := ∑ i∈qs,(quantifiedRowMass hN (r i) L U
    ((AsymptoticReconstructedCount.parameters A P).s+4))^2
  let Sl := ∑ i∈qs,(quantifiedRowLength hN (r i) L U:ℝ)^2
  have hSm : 0≤Sm := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSl : 0≤Sl := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := scalarFilter_growth (by positivity : 0≤V) hSm ha hb hC hs d hd hV hrowsM
  have hl := scalarFilter_growth (Nat.cast_nonneg K : (0:ℝ)≤K) hSl ha hb hC hs d hd hK hrowsL
  have he : (∑ i∈qs,(quantifiedRowMass hN (r i) L U
      ((AsymptoticReconstructedCount.parameters A P).s+4)*V)^2)=Sm*V^2 := by
    simp only [Sm,mul_pow,Finset.sum_mul]
  have hnat := natFilter_cast qs (fun i => quantifiedRowLength hN (r i) L U) K d
  change V^2*(1+∑ i∈qs,(quantifiedRowMass hN (r i) L U
    ((AsymptoticReconstructedCount.parameters A P).s+4)*V)^2)^d+
    ((K^2*(1+∑ i∈qs,(quantifiedRowLength hN (r i) L U*K)^2)^d:ℕ):ℝ)≤_
  rw [he,hnat]
  have hsum := add_le_add hm hl
  apply hsum.trans
  have ht := twice_double_exp_le (K:=14+4*a+b+C) (by positivity) hs
  convert ht using 1 <;> congr 2 <;> ring

/-- One explicit constant bounds both the literal normalized expression mass
and the literal normalized word count at the chosen cutoffs. -/
def normalizedComplexityGrowthConstant (P : Parameters A) (C : ℝ) : ℝ :=
  let a := rawLengthGrowthConstant A P C
  let b := 4*(newtonGrowthConstant A P C+2)^2
  b*Real.log 4+(a+b*(4+2*a))

theorem growing_normalized_complexity (P : Parameters A) {C s : ℝ} (hC : 0≤C)
    (hs : 1≤s) (d : ℕ) (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    let D : ℝ := 2*d+2
    let n := newtonDepth A P D (Real.exp (-8*s))
    let j := reconstructionDepth A P D (Real.exp (-8*s)) n
    let J := foldCutoff A P D (Real.exp (-8*s)) j n
    (4:ℝ)^(4^n)≤Real.exp (normalizedComplexityGrowthConstant A P C*s^12) ∧
    (normalizedWordLength A j J n:ℝ)≤Real.exp (normalizedComplexityGrowthConstant A P C*s^12) := by
  let D : ℝ := 2*d+2
  let n := newtonDepth A P D (Real.exp (-8*s))
  let j := reconstructionDepth A P D (Real.exp (-8*s)) n
  let J := foldCutoff A P D (Real.exp (-8*s)) j n
  let R := (rawReconstructionLength A j J:ℝ)
  let a := rawLengthGrowthConstant A P C
  let b := 4*(newtonGrowthConstant A P C+2)^2
  have ha : 0≤a := by
    have hL := reconstructionGrowthConstant_nonneg A P hC
    have hF := foldGrowthConstant_nonneg A P hC
    dsimp [a,rawLengthGrowthConstant]
    positivity
  have hb : 0≤b := by dsimp [b]; positivity
  have hl4 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hs4 : 1≤s^4 := by simpa using (pow_le_pow_right₀ hs (by norm_num : 0≤4))
  have hs412 : s^4≤s^12 := pow_le_pow_right₀ hs (by norm_num)
  have hn : (4:ℝ)^n≤b*s^4 := (growing_newton_complexity A P hC hs d hd).2.1
  have hR : R≤Real.exp (a*(s^4)^2) := by
    convert growing_raw_reconstruction_length A P hC hs d hd using 1
    congr 1
    ring
  have hword := normalizedLength_growth (Nat.cast_nonneg (rawReconstructionLength A j J) : 0≤R) ha hb hs4 n hR hn
  have hK : (normalizedWordLength A j J n:ℝ)≤Real.exp ((a+b*(4+2*a))*s^12) := by
    unfold normalizedWordLength
    push_cast
    convert hword using 1
    congr 1
    ring
  have hmass : (4:ℝ)^(4^n)≤Real.exp ((b*Real.log 4)*s^12) := by
    calc
      _ = Real.exp (((4^n:ℕ):ℝ)*Real.log 4) := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<4)]
      _ ≤ Real.exp ((b*Real.log 4)*s^4) := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_right hn hl4
        exact_mod_cast (show (4:ℝ)^n*Real.log 4≤(b*Real.log 4)*s^4 by nlinarith only [hm])
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs412 (mul_nonneg hb hl4))
  have hmnonneg : 0≤b*Real.log 4 := mul_nonneg hb hl4
  have hknonneg : 0≤a+b*(4+2*a) := by positivity
  constructor
  · apply hmass.trans
    apply Real.exp_le_exp.mpr
    change b*Real.log 4*s^12≤(b*Real.log 4+(a+b*(4+2*a)))*s^12
    nlinarith [mul_nonneg hknonneg (by positivity : 0≤s^12)]
  · apply hK.trans
    apply Real.exp_le_exp.mpr
    change (a+b*(4+2*a))*s^12≤(b*Real.log 4+(a+b*(4+2*a)))*s^12
    nlinarith [mul_nonneg hmnonneg (by positivity : 0≤s^12)]

#print axioms closedFilterComplexity_growth
#print axioms growing_normalized_complexity

end QuantitativeHolomorphic.Schedule
