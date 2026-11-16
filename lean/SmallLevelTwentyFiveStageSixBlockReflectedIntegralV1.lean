module
public import SmallLevelTwentyFiveStageSixCertificateDataIntegralV1
public meta import SmallLevelCertificateBatchCommandV1
public import SmallLevelTwentyFiveStageSixReflectionNormalFormsIntegralV1
public import SmallLevelSparseIntegerPolynomialCheckV1
public meta import SmallLevelPolynomialCertificateCommandsV4
public import SmallLevelPolynomialCoefficientCertificateTheoryV4
set_option Elab.async false
set_option autoImplicit false
set_option maxErrors 1
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
@[expose] public noncomputable section
namespace SmallLevelTwentyFiveStageSixBlockReflectedIntegral
open SmallLevelSparseIntegerPolynomialCheck SmallLevelPolynomialCoefficientCertificate
local notation "spadd" => SmallLevelSparseIntegerPolynomialCheck.add
local notation "spmul" => SmallLevelSparseIntegerPolynomialCheck.mul
local notation "spscale" => SmallLevelSparseIntegerPolynomialCheck.scale
noncomputable def mulShort (p q : Poly) : Poly :=
  if p.length <= q.length then spmul p q else spmul q p
theorem eval_mulShort (v : ℕ→ℂ) (p q : Poly) :
    eval v (mulShort p q)=eval v p*eval v q := by
  unfold mulShort
  split <;> simp only [eval_mul, mul_comm]
certificate_batch {
compact_certificate_declaration theorem cast_int_ofNat (n : ℕ) :
    ((Int.ofNat n : ℤ) : ℂ) = (n : ℂ) := by
  exact Int.cast_natCast n
compact_certificate_declaration theorem product_0_checked :
    mulShort n_c31_0 n_d0_0=product_0 := by
  decide +kernel
compact_certificate_declaration theorem product_0_value (v : ℕ→ℂ) :
    eval v product_0=eval v n_c31_0*eval v n_d0_0 := by
  rw [←product_0_checked, eval_mulShort]
compact_certificate_declaration theorem product_1_checked :
    mulShort n_c31_1 n_d0_1=product_1 := by
  decide +kernel
compact_certificate_declaration theorem product_1_value (v : ℕ→ℂ) :
    eval v product_1=eval v n_c31_1*eval v n_d0_1 := by
  rw [←product_1_checked, eval_mulShort]
compact_certificate_declaration theorem product_2_checked :
    mulShort n_c31_2 n_d0_2=product_2 := by
  decide +kernel
compact_certificate_declaration theorem product_2_value (v : ℕ→ℂ) :
    eval v product_2=eval v n_c31_2*eval v n_d0_2 := by
  rw [←product_2_checked, eval_mulShort]
compact_certificate_declaration theorem product_3_checked :
    mulShort n_c31_3 n_d0_3=product_3 := by
  decide +kernel
compact_certificate_declaration theorem product_3_value (v : ℕ→ℂ) :
    eval v product_3=eval v n_c31_3*eval v n_d0_3 := by
  rw [←product_3_checked, eval_mulShort]
compact_certificate_declaration theorem product_4_checked :
    mulShort n_c31_4 n_d0_4=product_4 := by
  decide +kernel
compact_certificate_declaration theorem product_4_value (v : ℕ→ℂ) :
    eval v product_4=eval v n_c31_4*eval v n_d0_4 := by
  rw [←product_4_checked, eval_mulShort]
compact_certificate_declaration theorem product_5_checked :
    mulShort n_c31_5 n_d0_5=product_5 := by
  decide +kernel
compact_certificate_declaration theorem product_5_value (v : ℕ→ℂ) :
    eval v product_5=eval v n_c31_5*eval v n_d0_5 := by
  rw [←product_5_checked, eval_mulShort]
compact_certificate_declaration theorem product_6_checked :
    mulShort n_c31_6 n_d0_6=product_6 := by
  decide +kernel
compact_certificate_declaration theorem product_6_value (v : ℕ→ℂ) :
    eval v product_6=eval v n_c31_6*eval v n_d0_6 := by
  rw [←product_6_checked, eval_mulShort]
compact_certificate_declaration theorem product_7_checked :
    mulShort n_c31_7 n_d0_7=product_7 := by
  decide +kernel
compact_certificate_declaration theorem product_7_value (v : ℕ→ℂ) :
    eval v product_7=eval v n_c31_7*eval v n_d0_7 := by
  rw [←product_7_checked, eval_mulShort]
compact_certificate_declaration theorem product_8_checked :
    mulShort n_c31_8 n_d0_8=product_8 := by
  decide +kernel
compact_certificate_declaration theorem product_8_value (v : ℕ→ℂ) :
    eval v product_8=eval v n_c31_8*eval v n_d0_8 := by
  rw [←product_8_checked, eval_mulShort]
compact_certificate_declaration theorem product_9_checked :
    mulShort n_c31_9 n_d0_9=product_9 := by
  decide +kernel
compact_certificate_declaration theorem product_9_value (v : ℕ→ℂ) :
    eval v product_9=eval v n_c31_9*eval v n_d0_9 := by
  rw [←product_9_checked, eval_mulShort]
compact_certificate_declaration theorem product_10_checked :
    mulShort n_c31_10 n_d0_10=product_10 := by
  decide +kernel
compact_certificate_declaration theorem product_10_value (v : ℕ→ℂ) :
    eval v product_10=eval v n_c31_10*eval v n_d0_10 := by
  rw [←product_10_checked, eval_mulShort]
compact_certificate_declaration theorem product_11_checked :
    mulShort n_c31_11 n_d0_12=product_11 := by
  decide +kernel
compact_certificate_declaration theorem product_11_value (v : ℕ→ℂ) :
    eval v product_11=eval v n_c31_11*eval v n_d0_12 := by
  rw [←product_11_checked, eval_mulShort]
compact_certificate_declaration theorem product_12_checked :
    mulShort n_c31_12 n_d0_13=product_12 := by
  decide +kernel
compact_certificate_declaration theorem product_12_value (v : ℕ→ℂ) :
    eval v product_12=eval v n_c31_12*eval v n_d0_13 := by
  rw [←product_12_checked, eval_mulShort]
compact_certificate_declaration theorem product_13_checked :
    mulShort n_c31_13 n_d0_14=product_13 := by
  decide +kernel
compact_certificate_declaration theorem product_13_value (v : ℕ→ℂ) :
    eval v product_13=eval v n_c31_13*eval v n_d0_14 := by
  rw [←product_13_checked, eval_mulShort]
compact_certificate_declaration theorem product_14_checked :
    mulShort n_c31_14 n_d0_15=product_14 := by
  decide +kernel
compact_certificate_declaration theorem product_14_value (v : ℕ→ℂ) :
    eval v product_14=eval v n_c31_14*eval v n_d0_15 := by
  rw [←product_14_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_0_checked :
    (spadd (spadd (spadd product_7 product_8) (spadd product_9 product_10)) (spadd (spadd product_11 product_12) (spadd product_13 product_14)))=partial_sum_0 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_0_value (v : ℕ→ℂ) :
    eval v partial_sum_0=eval v (spadd (spadd product_7 product_8) (spadd product_9 product_10))+eval v (spadd (spadd product_11 product_12) (spadd product_13 product_14)) := by
  rw [←partial_sum_0_checked, eval_add]
compact_certificate_declaration theorem partial_sum_1_checked :
    (spadd (spadd (spadd product_0 (spadd product_1 product_2)) (spadd (spadd product_3 product_4) (spadd product_5 product_6))) partial_sum_0)=partial_sum_1 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_1_value (v : ℕ→ℂ) :
    eval v partial_sum_1=eval v (spadd (spadd product_0 (spadd product_1 product_2)) (spadd (spadd product_3 product_4) (spadd product_5 product_6)))+eval v partial_sum_0 := by
  rw [←partial_sum_1_checked, eval_add]
compact_certificate_declaration theorem product_15_checked :
    mulShort n_c31_15 n_d0_16=product_15 := by
  decide +kernel
compact_certificate_declaration theorem product_15_value (v : ℕ→ℂ) :
    eval v product_15=eval v n_c31_15*eval v n_d0_16 := by
  rw [←product_15_checked, eval_mulShort]
compact_certificate_declaration theorem product_16_checked :
    mulShort n_c31_16 n_d0_17=product_16 := by
  decide +kernel
compact_certificate_declaration theorem product_16_value (v : ℕ→ℂ) :
    eval v product_16=eval v n_c31_16*eval v n_d0_17 := by
  rw [←product_16_checked, eval_mulShort]
compact_certificate_declaration theorem product_17_checked :
    mulShort n_c31_17 n_d0_18=product_17 := by
  decide +kernel
compact_certificate_declaration theorem product_17_value (v : ℕ→ℂ) :
    eval v product_17=eval v n_c31_17*eval v n_d0_18 := by
  rw [←product_17_checked, eval_mulShort]
compact_certificate_declaration theorem product_18_checked :
    mulShort n_c31_18 n_d0_19=product_18 := by
  decide +kernel
compact_certificate_declaration theorem product_18_value (v : ℕ→ℂ) :
    eval v product_18=eval v n_c31_18*eval v n_d0_19 := by
  rw [←product_18_checked, eval_mulShort]
compact_certificate_declaration theorem product_19_checked :
    mulShort n_c31_19 n_d0_20=product_19 := by
  decide +kernel
compact_certificate_declaration theorem product_19_value (v : ℕ→ℂ) :
    eval v product_19=eval v n_c31_19*eval v n_d0_20 := by
  rw [←product_19_checked, eval_mulShort]
compact_certificate_declaration theorem product_20_checked :
    mulShort n_c31_20 n_d0_21=product_20 := by
  decide +kernel
compact_certificate_declaration theorem product_20_value (v : ℕ→ℂ) :
    eval v product_20=eval v n_c31_20*eval v n_d0_21 := by
  rw [←product_20_checked, eval_mulShort]
compact_certificate_declaration theorem product_21_checked :
    mulShort n_c31_21 n_d0_22=product_21 := by
  decide +kernel
compact_certificate_declaration theorem product_21_value (v : ℕ→ℂ) :
    eval v product_21=eval v n_c31_21*eval v n_d0_22 := by
  rw [←product_21_checked, eval_mulShort]
compact_certificate_declaration theorem product_22_checked :
    mulShort n_c31_22 n_d0_23=product_22 := by
  decide +kernel
compact_certificate_declaration theorem product_22_value (v : ℕ→ℂ) :
    eval v product_22=eval v n_c31_22*eval v n_d0_23 := by
  rw [←product_22_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_2_checked :
    (spadd (spadd (spadd product_15 product_16) (spadd product_17 product_18)) (spadd (spadd product_19 product_20) (spadd product_21 product_22)))=partial_sum_2 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_2_value (v : ℕ→ℂ) :
    eval v partial_sum_2=eval v (spadd (spadd product_15 product_16) (spadd product_17 product_18))+eval v (spadd (spadd product_19 product_20) (spadd product_21 product_22)) := by
  rw [←partial_sum_2_checked, eval_add]
compact_certificate_declaration theorem product_23_checked :
    mulShort n_c31_23 n_d0_24=product_23 := by
  decide +kernel
compact_certificate_declaration theorem product_23_value (v : ℕ→ℂ) :
    eval v product_23=eval v n_c31_23*eval v n_d0_24 := by
  rw [←product_23_checked, eval_mulShort]
compact_certificate_declaration theorem product_24_checked :
    mulShort n_c31_24 n_d0_25=product_24 := by
  decide +kernel
compact_certificate_declaration theorem product_24_value (v : ℕ→ℂ) :
    eval v product_24=eval v n_c31_24*eval v n_d0_25 := by
  rw [←product_24_checked, eval_mulShort]
compact_certificate_declaration theorem product_25_checked :
    mulShort n_c31_25 n_d0_26=product_25 := by
  decide +kernel
compact_certificate_declaration theorem product_25_value (v : ℕ→ℂ) :
    eval v product_25=eval v n_c31_25*eval v n_d0_26 := by
  rw [←product_25_checked, eval_mulShort]
compact_certificate_declaration theorem product_26_checked :
    mulShort n_c31_26 n_d0_27=product_26 := by
  decide +kernel
compact_certificate_declaration theorem product_26_value (v : ℕ→ℂ) :
    eval v product_26=eval v n_c31_26*eval v n_d0_27 := by
  rw [←product_26_checked, eval_mulShort]
compact_certificate_declaration theorem product_27_checked :
    mulShort n_c31_27 n_d0_28=product_27 := by
  decide +kernel
compact_certificate_declaration theorem product_27_value (v : ℕ→ℂ) :
    eval v product_27=eval v n_c31_27*eval v n_d0_28 := by
  rw [←product_27_checked, eval_mulShort]
compact_certificate_declaration theorem product_28_checked :
    mulShort n_c31_28 n_d0_29=product_28 := by
  decide +kernel
compact_certificate_declaration theorem product_28_value (v : ℕ→ℂ) :
    eval v product_28=eval v n_c31_28*eval v n_d0_29 := by
  rw [←product_28_checked, eval_mulShort]
compact_certificate_declaration theorem product_29_checked :
    mulShort n_c31_29 n_d0_30=product_29 := by
  decide +kernel
compact_certificate_declaration theorem product_29_value (v : ℕ→ℂ) :
    eval v product_29=eval v n_c31_29*eval v n_d0_30 := by
  rw [←product_29_checked, eval_mulShort]
compact_certificate_declaration theorem product_30_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c31_30) n_d1_31=product_30 := by
  decide +kernel
compact_certificate_declaration theorem product_30_value (v : ℕ→ℂ) :
    eval v product_30=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c31_30)*eval v n_d1_31 := by
  rw [←product_30_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_3_checked :
    (spadd (spadd (spadd product_23 product_24) (spadd product_25 product_26)) (spadd (spadd product_27 product_28) (spadd product_29 product_30)))=partial_sum_3 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_3_value (v : ℕ→ℂ) :
    eval v partial_sum_3=eval v (spadd (spadd product_23 product_24) (spadd product_25 product_26))+eval v (spadd (spadd product_27 product_28) (spadd product_29 product_30)) := by
  rw [←partial_sum_3_checked, eval_add]
compact_certificate_declaration theorem partial_sum_4_checked :
    (spadd partial_sum_2 partial_sum_3)=partial_sum_4 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_4_value (v : ℕ→ℂ) :
    eval v partial_sum_4=eval v partial_sum_2+eval v partial_sum_3 := by
  rw [←partial_sum_4_checked, eval_add]
compact_certificate_declaration theorem partial_sum_5_checked :
    (spadd partial_sum_1 partial_sum_4)=partial_sum_5 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_5_value (v : ℕ→ℂ) :
    eval v partial_sum_5=eval v partial_sum_1+eval v partial_sum_4 := by
  rw [←partial_sum_5_checked, eval_add]
compact_certificate_declaration theorem checked_0 : checkZero e0=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_0 (y z w a b u : ℂ) :
    (certificate y z w a b u)[0]?=some 0 := by
  change some ((((((c31_0 y z w a b u)*(d0_0 y z w a b u)+((c31_1 y z w a b u)*(d0_1 y z w a b u)+(c31_2 y z w a b u)*(d0_2 y z w a b u)))+(((c31_3 y z w a b u)*(d0_3 y z w a b u)+(c31_4 y z w a b u)*(d0_4 y z w a b u))+((c31_5 y z w a b u)*(d0_5 y z w a b u)+(c31_6 y z w a b u)*(d0_6 y z w a b u))))+((((c31_7 y z w a b u)*(d0_7 y z w a b u)+(c31_8 y z w a b u)*(d0_8 y z w a b u))+((c31_9 y z w a b u)*(d0_9 y z w a b u)+(c31_10 y z w a b u)*(d0_10 y z w a b u)))+(((c31_11 y z w a b u)*(d0_12 y z w a b u)+(c31_12 y z w a b u)*(d0_13 y z w a b u))+((c31_13 y z w a b u)*(d0_14 y z w a b u)+(c31_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c31_15 y z w a b u)*(d0_16 y z w a b u)+(c31_16 y z w a b u)*(d0_17 y z w a b u))+((c31_17 y z w a b u)*(d0_18 y z w a b u)+(c31_18 y z w a b u)*(d0_19 y z w a b u)))+(((c31_19 y z w a b u)*(d0_20 y z w a b u)+(c31_20 y z w a b u)*(d0_21 y z w a b u))+((c31_21 y z w a b u)*(d0_22 y z w a b u)+(c31_22 y z w a b u)*(d0_23 y z w a b u))))+((((c31_23 y z w a b u)*(d0_24 y z w a b u)+(c31_24 y z w a b u)*(d0_25 y z w a b u))+((c31_25 y z w a b u)*(d0_26 y z w a b u)+(c31_26 y z w a b u)*(d0_27 y z w a b u)))+(((c31_27 y z w a b u)*(d0_28 y z w a b u)+(c31_28 y z w a b u)*(d0_29 y z w a b u))+((c31_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c31_30 y z w a b u)*(d1_31 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e0 checked_0
  simp only [e0, eval_add, eval_mul, eval_scale, eval_pow, product_0_value, product_1_value, product_2_value, product_3_value, product_4_value, product_5_value, product_6_value, product_7_value, product_8_value, product_9_value, product_10_value, product_11_value, product_12_value, product_13_value, product_14_value, partial_sum_0_value, partial_sum_1_value, product_15_value, product_16_value, product_17_value, product_18_value, product_19_value, product_20_value, product_21_value, product_22_value, partial_sum_2_value, product_23_value, product_24_value, product_25_value, product_26_value, product_27_value, product_28_value, product_29_value, product_30_value, partial_sum_3_value, partial_sum_4_value, partial_sum_5_value, n_c31_0_value y z w a b u, n_c31_1_value y z w a b u, n_c31_10_value y z w a b u, n_c31_11_value y z w a b u, n_c31_12_value y z w a b u, n_c31_13_value y z w a b u, n_c31_14_value y z w a b u, n_c31_15_value y z w a b u, n_c31_16_value y z w a b u, n_c31_17_value y z w a b u, n_c31_18_value y z w a b u, n_c31_19_value y z w a b u, n_c31_2_value y z w a b u, n_c31_20_value y z w a b u, n_c31_21_value y z w a b u, n_c31_22_value y z w a b u, n_c31_23_value y z w a b u, n_c31_24_value y z w a b u, n_c31_25_value y z w a b u, n_c31_26_value y z w a b u, n_c31_27_value y z w a b u, n_c31_28_value y z w a b u, n_c31_29_value y z w a b u, n_c31_3_value y z w a b u, n_c31_30_value y z w a b u, n_c31_4_value y z w a b u, n_c31_5_value y z w a b u, n_c31_6_value y z w a b u, n_c31_7_value y z w a b u, n_c31_8_value y z w a b u, n_c31_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_31_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_31_checked :
    mulShort n_c32_0 n_d0_0=product_31 := by
  decide +kernel
compact_certificate_declaration theorem product_31_value (v : ℕ→ℂ) :
    eval v product_31=eval v n_c32_0*eval v n_d0_0 := by
  rw [←product_31_checked, eval_mulShort]
compact_certificate_declaration theorem product_32_checked :
    mulShort n_c32_1 n_d0_1=product_32 := by
  decide +kernel
compact_certificate_declaration theorem product_32_value (v : ℕ→ℂ) :
    eval v product_32=eval v n_c32_1*eval v n_d0_1 := by
  rw [←product_32_checked, eval_mulShort]
compact_certificate_declaration theorem product_33_checked :
    mulShort n_c32_2 n_d0_2=product_33 := by
  decide +kernel
compact_certificate_declaration theorem product_33_value (v : ℕ→ℂ) :
    eval v product_33=eval v n_c32_2*eval v n_d0_2 := by
  rw [←product_33_checked, eval_mulShort]
compact_certificate_declaration theorem product_34_checked :
    mulShort n_c32_3 n_d0_3=product_34 := by
  decide +kernel
compact_certificate_declaration theorem product_34_value (v : ℕ→ℂ) :
    eval v product_34=eval v n_c32_3*eval v n_d0_3 := by
  rw [←product_34_checked, eval_mulShort]
compact_certificate_declaration theorem product_35_checked :
    mulShort n_c32_4 n_d0_4=product_35 := by
  decide +kernel
compact_certificate_declaration theorem product_35_value (v : ℕ→ℂ) :
    eval v product_35=eval v n_c32_4*eval v n_d0_4 := by
  rw [←product_35_checked, eval_mulShort]
compact_certificate_declaration theorem product_36_checked :
    mulShort n_c32_5 n_d0_5=product_36 := by
  decide +kernel
compact_certificate_declaration theorem product_36_value (v : ℕ→ℂ) :
    eval v product_36=eval v n_c32_5*eval v n_d0_5 := by
  rw [←product_36_checked, eval_mulShort]
compact_certificate_declaration theorem product_37_checked :
    mulShort n_c32_6 n_d0_6=product_37 := by
  decide +kernel
compact_certificate_declaration theorem product_37_value (v : ℕ→ℂ) :
    eval v product_37=eval v n_c32_6*eval v n_d0_6 := by
  rw [←product_37_checked, eval_mulShort]
compact_certificate_declaration theorem product_38_checked :
    mulShort n_c32_7 n_d0_7=product_38 := by
  decide +kernel
compact_certificate_declaration theorem product_38_value (v : ℕ→ℂ) :
    eval v product_38=eval v n_c32_7*eval v n_d0_7 := by
  rw [←product_38_checked, eval_mulShort]
compact_certificate_declaration theorem product_39_checked :
    mulShort n_c32_8 n_d0_8=product_39 := by
  decide +kernel
compact_certificate_declaration theorem product_39_value (v : ℕ→ℂ) :
    eval v product_39=eval v n_c32_8*eval v n_d0_8 := by
  rw [←product_39_checked, eval_mulShort]
compact_certificate_declaration theorem product_40_checked :
    mulShort n_c32_9 n_d0_9=product_40 := by
  decide +kernel
compact_certificate_declaration theorem product_40_value (v : ℕ→ℂ) :
    eval v product_40=eval v n_c32_9*eval v n_d0_9 := by
  rw [←product_40_checked, eval_mulShort]
compact_certificate_declaration theorem product_41_checked :
    mulShort n_c32_10 n_d0_10=product_41 := by
  decide +kernel
compact_certificate_declaration theorem product_41_value (v : ℕ→ℂ) :
    eval v product_41=eval v n_c32_10*eval v n_d0_10 := by
  rw [←product_41_checked, eval_mulShort]
compact_certificate_declaration theorem product_42_checked :
    mulShort n_c32_11 n_d0_12=product_42 := by
  decide +kernel
compact_certificate_declaration theorem product_42_value (v : ℕ→ℂ) :
    eval v product_42=eval v n_c32_11*eval v n_d0_12 := by
  rw [←product_42_checked, eval_mulShort]
compact_certificate_declaration theorem product_43_checked :
    mulShort n_c32_12 n_d0_13=product_43 := by
  decide +kernel
compact_certificate_declaration theorem product_43_value (v : ℕ→ℂ) :
    eval v product_43=eval v n_c32_12*eval v n_d0_13 := by
  rw [←product_43_checked, eval_mulShort]
compact_certificate_declaration theorem product_44_checked :
    mulShort n_c32_13 n_d0_14=product_44 := by
  decide +kernel
compact_certificate_declaration theorem product_44_value (v : ℕ→ℂ) :
    eval v product_44=eval v n_c32_13*eval v n_d0_14 := by
  rw [←product_44_checked, eval_mulShort]
compact_certificate_declaration theorem product_45_checked :
    mulShort n_c32_14 n_d0_15=product_45 := by
  decide +kernel
compact_certificate_declaration theorem product_45_value (v : ℕ→ℂ) :
    eval v product_45=eval v n_c32_14*eval v n_d0_15 := by
  rw [←product_45_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_6_checked :
    (spadd (spadd (spadd product_38 product_39) (spadd product_40 product_41)) (spadd (spadd product_42 product_43) (spadd product_44 product_45)))=partial_sum_6 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_6_value (v : ℕ→ℂ) :
    eval v partial_sum_6=eval v (spadd (spadd product_38 product_39) (spadd product_40 product_41))+eval v (spadd (spadd product_42 product_43) (spadd product_44 product_45)) := by
  rw [←partial_sum_6_checked, eval_add]
compact_certificate_declaration theorem partial_sum_7_checked :
    (spadd (spadd (spadd product_31 (spadd product_32 product_33)) (spadd (spadd product_34 product_35) (spadd product_36 product_37))) partial_sum_6)=partial_sum_7 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_7_value (v : ℕ→ℂ) :
    eval v partial_sum_7=eval v (spadd (spadd product_31 (spadd product_32 product_33)) (spadd (spadd product_34 product_35) (spadd product_36 product_37)))+eval v partial_sum_6 := by
  rw [←partial_sum_7_checked, eval_add]
compact_certificate_declaration theorem product_46_checked :
    mulShort n_c32_15 n_d0_16=product_46 := by
  decide +kernel
compact_certificate_declaration theorem product_46_value (v : ℕ→ℂ) :
    eval v product_46=eval v n_c32_15*eval v n_d0_16 := by
  rw [←product_46_checked, eval_mulShort]
compact_certificate_declaration theorem product_47_checked :
    mulShort n_c32_16 n_d0_17=product_47 := by
  decide +kernel
compact_certificate_declaration theorem product_47_value (v : ℕ→ℂ) :
    eval v product_47=eval v n_c32_16*eval v n_d0_17 := by
  rw [←product_47_checked, eval_mulShort]
compact_certificate_declaration theorem product_48_checked :
    mulShort n_c32_17 n_d0_18=product_48 := by
  decide +kernel
compact_certificate_declaration theorem product_48_value (v : ℕ→ℂ) :
    eval v product_48=eval v n_c32_17*eval v n_d0_18 := by
  rw [←product_48_checked, eval_mulShort]
compact_certificate_declaration theorem product_49_checked :
    mulShort n_c32_18 n_d0_19=product_49 := by
  decide +kernel
compact_certificate_declaration theorem product_49_value (v : ℕ→ℂ) :
    eval v product_49=eval v n_c32_18*eval v n_d0_19 := by
  rw [←product_49_checked, eval_mulShort]
compact_certificate_declaration theorem product_50_checked :
    mulShort n_c32_19 n_d0_20=product_50 := by
  decide +kernel
compact_certificate_declaration theorem product_50_value (v : ℕ→ℂ) :
    eval v product_50=eval v n_c32_19*eval v n_d0_20 := by
  rw [←product_50_checked, eval_mulShort]
compact_certificate_declaration theorem product_51_checked :
    mulShort n_c32_20 n_d0_21=product_51 := by
  decide +kernel
compact_certificate_declaration theorem product_51_value (v : ℕ→ℂ) :
    eval v product_51=eval v n_c32_20*eval v n_d0_21 := by
  rw [←product_51_checked, eval_mulShort]
compact_certificate_declaration theorem product_52_checked :
    mulShort n_c32_21 n_d0_22=product_52 := by
  decide +kernel
compact_certificate_declaration theorem product_52_value (v : ℕ→ℂ) :
    eval v product_52=eval v n_c32_21*eval v n_d0_22 := by
  rw [←product_52_checked, eval_mulShort]
compact_certificate_declaration theorem product_53_checked :
    mulShort n_c32_22 n_d0_23=product_53 := by
  decide +kernel
compact_certificate_declaration theorem product_53_value (v : ℕ→ℂ) :
    eval v product_53=eval v n_c32_22*eval v n_d0_23 := by
  rw [←product_53_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_8_checked :
    (spadd (spadd (spadd product_46 product_47) (spadd product_48 product_49)) (spadd (spadd product_50 product_51) (spadd product_52 product_53)))=partial_sum_8 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_8_value (v : ℕ→ℂ) :
    eval v partial_sum_8=eval v (spadd (spadd product_46 product_47) (spadd product_48 product_49))+eval v (spadd (spadd product_50 product_51) (spadd product_52 product_53)) := by
  rw [←partial_sum_8_checked, eval_add]
compact_certificate_declaration theorem product_54_checked :
    mulShort n_c32_23 n_d0_24=product_54 := by
  decide +kernel
compact_certificate_declaration theorem product_54_value (v : ℕ→ℂ) :
    eval v product_54=eval v n_c32_23*eval v n_d0_24 := by
  rw [←product_54_checked, eval_mulShort]
compact_certificate_declaration theorem product_55_checked :
    mulShort n_c32_24 n_d0_25=product_55 := by
  decide +kernel
compact_certificate_declaration theorem product_55_value (v : ℕ→ℂ) :
    eval v product_55=eval v n_c32_24*eval v n_d0_25 := by
  rw [←product_55_checked, eval_mulShort]
compact_certificate_declaration theorem product_56_checked :
    mulShort n_c32_25 n_d0_26=product_56 := by
  decide +kernel
compact_certificate_declaration theorem product_56_value (v : ℕ→ℂ) :
    eval v product_56=eval v n_c32_25*eval v n_d0_26 := by
  rw [←product_56_checked, eval_mulShort]
compact_certificate_declaration theorem product_57_checked :
    mulShort n_c32_26 n_d0_27=product_57 := by
  decide +kernel
compact_certificate_declaration theorem product_57_value (v : ℕ→ℂ) :
    eval v product_57=eval v n_c32_26*eval v n_d0_27 := by
  rw [←product_57_checked, eval_mulShort]
compact_certificate_declaration theorem product_58_checked :
    mulShort n_c32_27 n_d0_28=product_58 := by
  decide +kernel
compact_certificate_declaration theorem product_58_value (v : ℕ→ℂ) :
    eval v product_58=eval v n_c32_27*eval v n_d0_28 := by
  rw [←product_58_checked, eval_mulShort]
compact_certificate_declaration theorem product_59_checked :
    mulShort n_c32_28 n_d0_29=product_59 := by
  decide +kernel
compact_certificate_declaration theorem product_59_value (v : ℕ→ℂ) :
    eval v product_59=eval v n_c32_28*eval v n_d0_29 := by
  rw [←product_59_checked, eval_mulShort]
compact_certificate_declaration theorem product_60_checked :
    mulShort n_c32_29 n_d0_30=product_60 := by
  decide +kernel
compact_certificate_declaration theorem product_60_value (v : ℕ→ℂ) :
    eval v product_60=eval v n_c32_29*eval v n_d0_30 := by
  rw [←product_60_checked, eval_mulShort]
compact_certificate_declaration theorem product_61_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c32_30) n_d1_32=product_61 := by
  decide +kernel
compact_certificate_declaration theorem product_61_value (v : ℕ→ℂ) :
    eval v product_61=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c32_30)*eval v n_d1_32 := by
  rw [←product_61_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_9_checked :
    (spadd (spadd (spadd product_54 product_55) (spadd product_56 product_57)) (spadd (spadd product_58 product_59) (spadd product_60 product_61)))=partial_sum_9 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_9_value (v : ℕ→ℂ) :
    eval v partial_sum_9=eval v (spadd (spadd product_54 product_55) (spadd product_56 product_57))+eval v (spadd (spadd product_58 product_59) (spadd product_60 product_61)) := by
  rw [←partial_sum_9_checked, eval_add]
compact_certificate_declaration theorem partial_sum_10_checked :
    (spadd partial_sum_8 partial_sum_9)=partial_sum_10 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_10_value (v : ℕ→ℂ) :
    eval v partial_sum_10=eval v partial_sum_8+eval v partial_sum_9 := by
  rw [←partial_sum_10_checked, eval_add]
compact_certificate_declaration theorem partial_sum_11_checked :
    (spadd partial_sum_7 partial_sum_10)=partial_sum_11 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_11_value (v : ℕ→ℂ) :
    eval v partial_sum_11=eval v partial_sum_7+eval v partial_sum_10 := by
  rw [←partial_sum_11_checked, eval_add]
compact_certificate_declaration theorem checked_1 : checkZero e1=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_1 (y z w a b u : ℂ) :
    (certificate y z w a b u)[1]?=some 0 := by
  change some ((((((c32_0 y z w a b u)*(d0_0 y z w a b u)+((c32_1 y z w a b u)*(d0_1 y z w a b u)+(c32_2 y z w a b u)*(d0_2 y z w a b u)))+(((c32_3 y z w a b u)*(d0_3 y z w a b u)+(c32_4 y z w a b u)*(d0_4 y z w a b u))+((c32_5 y z w a b u)*(d0_5 y z w a b u)+(c32_6 y z w a b u)*(d0_6 y z w a b u))))+((((c32_7 y z w a b u)*(d0_7 y z w a b u)+(c32_8 y z w a b u)*(d0_8 y z w a b u))+((c32_9 y z w a b u)*(d0_9 y z w a b u)+(c32_10 y z w a b u)*(d0_10 y z w a b u)))+(((c32_11 y z w a b u)*(d0_12 y z w a b u)+(c32_12 y z w a b u)*(d0_13 y z w a b u))+((c32_13 y z w a b u)*(d0_14 y z w a b u)+(c32_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c32_15 y z w a b u)*(d0_16 y z w a b u)+(c32_16 y z w a b u)*(d0_17 y z w a b u))+((c32_17 y z w a b u)*(d0_18 y z w a b u)+(c32_18 y z w a b u)*(d0_19 y z w a b u)))+(((c32_19 y z w a b u)*(d0_20 y z w a b u)+(c32_20 y z w a b u)*(d0_21 y z w a b u))+((c32_21 y z w a b u)*(d0_22 y z w a b u)+(c32_22 y z w a b u)*(d0_23 y z w a b u))))+((((c32_23 y z w a b u)*(d0_24 y z w a b u)+(c32_24 y z w a b u)*(d0_25 y z w a b u))+((c32_25 y z w a b u)*(d0_26 y z w a b u)+(c32_26 y z w a b u)*(d0_27 y z w a b u)))+(((c32_27 y z w a b u)*(d0_28 y z w a b u)+(c32_28 y z w a b u)*(d0_29 y z w a b u))+((c32_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c32_30 y z w a b u)*(d1_32 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e1 checked_1
  simp only [e1, eval_add, eval_mul, eval_scale, eval_pow, product_31_value, product_32_value, product_33_value, product_34_value, product_35_value, product_36_value, product_37_value, product_38_value, product_39_value, product_40_value, product_41_value, product_42_value, product_43_value, product_44_value, product_45_value, partial_sum_6_value, partial_sum_7_value, product_46_value, product_47_value, product_48_value, product_49_value, product_50_value, product_51_value, product_52_value, product_53_value, partial_sum_8_value, product_54_value, product_55_value, product_56_value, product_57_value, product_58_value, product_59_value, product_60_value, product_61_value, partial_sum_9_value, partial_sum_10_value, partial_sum_11_value, n_c32_0_value y z w a b u, n_c32_1_value y z w a b u, n_c32_10_value y z w a b u, n_c32_11_value y z w a b u, n_c32_12_value y z w a b u, n_c32_13_value y z w a b u, n_c32_14_value y z w a b u, n_c32_15_value y z w a b u, n_c32_16_value y z w a b u, n_c32_17_value y z w a b u, n_c32_18_value y z w a b u, n_c32_19_value y z w a b u, n_c32_2_value y z w a b u, n_c32_20_value y z w a b u, n_c32_21_value y z w a b u, n_c32_22_value y z w a b u, n_c32_23_value y z w a b u, n_c32_24_value y z w a b u, n_c32_25_value y z w a b u, n_c32_26_value y z w a b u, n_c32_27_value y z w a b u, n_c32_28_value y z w a b u, n_c32_29_value y z w a b u, n_c32_3_value y z w a b u, n_c32_30_value y z w a b u, n_c32_4_value y z w a b u, n_c32_5_value y z w a b u, n_c32_6_value y z w a b u, n_c32_7_value y z w a b u, n_c32_8_value y z w a b u, n_c32_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_32_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_62_checked :
    mulShort n_c33_0 n_d0_0=product_62 := by
  decide +kernel
compact_certificate_declaration theorem product_62_value (v : ℕ→ℂ) :
    eval v product_62=eval v n_c33_0*eval v n_d0_0 := by
  rw [←product_62_checked, eval_mulShort]
compact_certificate_declaration theorem product_63_checked :
    mulShort n_c33_1 n_d0_1=product_63 := by
  decide +kernel
compact_certificate_declaration theorem product_63_value (v : ℕ→ℂ) :
    eval v product_63=eval v n_c33_1*eval v n_d0_1 := by
  rw [←product_63_checked, eval_mulShort]
compact_certificate_declaration theorem product_64_checked :
    mulShort n_c33_2 n_d0_2=product_64 := by
  decide +kernel
compact_certificate_declaration theorem product_64_value (v : ℕ→ℂ) :
    eval v product_64=eval v n_c33_2*eval v n_d0_2 := by
  rw [←product_64_checked, eval_mulShort]
compact_certificate_declaration theorem product_65_checked :
    mulShort n_c33_3 n_d0_3=product_65 := by
  decide +kernel
compact_certificate_declaration theorem product_65_value (v : ℕ→ℂ) :
    eval v product_65=eval v n_c33_3*eval v n_d0_3 := by
  rw [←product_65_checked, eval_mulShort]
compact_certificate_declaration theorem product_66_checked :
    mulShort n_c33_4 n_d0_4=product_66 := by
  decide +kernel
compact_certificate_declaration theorem product_66_value (v : ℕ→ℂ) :
    eval v product_66=eval v n_c33_4*eval v n_d0_4 := by
  rw [←product_66_checked, eval_mulShort]
compact_certificate_declaration theorem product_67_checked :
    mulShort n_c33_5 n_d0_5=product_67 := by
  decide +kernel
compact_certificate_declaration theorem product_67_value (v : ℕ→ℂ) :
    eval v product_67=eval v n_c33_5*eval v n_d0_5 := by
  rw [←product_67_checked, eval_mulShort]
compact_certificate_declaration theorem product_68_checked :
    mulShort n_c33_6 n_d0_6=product_68 := by
  decide +kernel
compact_certificate_declaration theorem product_68_value (v : ℕ→ℂ) :
    eval v product_68=eval v n_c33_6*eval v n_d0_6 := by
  rw [←product_68_checked, eval_mulShort]
compact_certificate_declaration theorem product_69_checked :
    mulShort n_c33_7 n_d0_7=product_69 := by
  decide +kernel
compact_certificate_declaration theorem product_69_value (v : ℕ→ℂ) :
    eval v product_69=eval v n_c33_7*eval v n_d0_7 := by
  rw [←product_69_checked, eval_mulShort]
compact_certificate_declaration theorem product_70_checked :
    mulShort n_c33_8 n_d0_8=product_70 := by
  decide +kernel
compact_certificate_declaration theorem product_70_value (v : ℕ→ℂ) :
    eval v product_70=eval v n_c33_8*eval v n_d0_8 := by
  rw [←product_70_checked, eval_mulShort]

compact_certificate_declaration theorem product_71_checked :
    mulShort n_c33_9 n_d0_9=product_71 := by
  decide +kernel
compact_certificate_declaration theorem product_71_value (v : ℕ→ℂ) :
    eval v product_71=eval v n_c33_9*eval v n_d0_9 := by
  rw [←product_71_checked, eval_mulShort]
compact_certificate_declaration theorem product_72_checked :
    mulShort n_c33_10 n_d0_10=product_72 := by
  decide +kernel
compact_certificate_declaration theorem product_72_value (v : ℕ→ℂ) :
    eval v product_72=eval v n_c33_10*eval v n_d0_10 := by
  rw [←product_72_checked, eval_mulShort]
compact_certificate_declaration theorem product_73_checked :
    mulShort n_c33_11 n_d0_12=product_73 := by
  decide +kernel
compact_certificate_declaration theorem product_73_value (v : ℕ→ℂ) :
    eval v product_73=eval v n_c33_11*eval v n_d0_12 := by
  rw [←product_73_checked, eval_mulShort]
compact_certificate_declaration theorem product_74_checked :
    mulShort n_c33_12 n_d0_13=product_74 := by
  decide +kernel
compact_certificate_declaration theorem product_74_value (v : ℕ→ℂ) :
    eval v product_74=eval v n_c33_12*eval v n_d0_13 := by
  rw [←product_74_checked, eval_mulShort]
compact_certificate_declaration theorem product_75_checked :
    mulShort n_c33_13 n_d0_14=product_75 := by
  decide +kernel
compact_certificate_declaration theorem product_75_value (v : ℕ→ℂ) :
    eval v product_75=eval v n_c33_13*eval v n_d0_14 := by
  rw [←product_75_checked, eval_mulShort]
compact_certificate_declaration theorem product_76_checked :
    mulShort n_c33_14 n_d0_15=product_76 := by
  decide +kernel
compact_certificate_declaration theorem product_76_value (v : ℕ→ℂ) :
    eval v product_76=eval v n_c33_14*eval v n_d0_15 := by
  rw [←product_76_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_12_checked :
    (spadd (spadd (spadd product_69 product_70) (spadd product_71 product_72)) (spadd (spadd product_73 product_74) (spadd product_75 product_76)))=partial_sum_12 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_12_value (v : ℕ→ℂ) :
    eval v partial_sum_12=eval v (spadd (spadd product_69 product_70) (spadd product_71 product_72))+eval v (spadd (spadd product_73 product_74) (spadd product_75 product_76)) := by
  rw [←partial_sum_12_checked, eval_add]
compact_certificate_declaration theorem partial_sum_13_checked :
    (spadd (spadd (spadd product_62 (spadd product_63 product_64)) (spadd (spadd product_65 product_66) (spadd product_67 product_68))) partial_sum_12)=partial_sum_13 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_13_value (v : ℕ→ℂ) :
    eval v partial_sum_13=eval v (spadd (spadd product_62 (spadd product_63 product_64)) (spadd (spadd product_65 product_66) (spadd product_67 product_68)))+eval v partial_sum_12 := by
  rw [←partial_sum_13_checked, eval_add]
compact_certificate_declaration theorem product_77_checked :
    mulShort n_c33_15 n_d0_16=product_77 := by
  decide +kernel
compact_certificate_declaration theorem product_77_value (v : ℕ→ℂ) :
    eval v product_77=eval v n_c33_15*eval v n_d0_16 := by
  rw [←product_77_checked, eval_mulShort]
compact_certificate_declaration theorem product_78_checked :
    mulShort n_c33_16 n_d0_17=product_78 := by
  decide +kernel
compact_certificate_declaration theorem product_78_value (v : ℕ→ℂ) :
    eval v product_78=eval v n_c33_16*eval v n_d0_17 := by
  rw [←product_78_checked, eval_mulShort]
compact_certificate_declaration theorem product_79_checked :
    mulShort n_c33_17 n_d0_18=product_79 := by
  decide +kernel
compact_certificate_declaration theorem product_79_value (v : ℕ→ℂ) :
    eval v product_79=eval v n_c33_17*eval v n_d0_18 := by
  rw [←product_79_checked, eval_mulShort]
compact_certificate_declaration theorem product_80_checked :
    mulShort n_c33_18 n_d0_19=product_80 := by
  decide +kernel
compact_certificate_declaration theorem product_80_value (v : ℕ→ℂ) :
    eval v product_80=eval v n_c33_18*eval v n_d0_19 := by
  rw [←product_80_checked, eval_mulShort]
compact_certificate_declaration theorem product_81_checked :
    mulShort n_c33_19 n_d0_20=product_81 := by
  decide +kernel
compact_certificate_declaration theorem product_81_value (v : ℕ→ℂ) :
    eval v product_81=eval v n_c33_19*eval v n_d0_20 := by
  rw [←product_81_checked, eval_mulShort]
compact_certificate_declaration theorem product_82_checked :
    mulShort n_c33_20 n_d0_21=product_82 := by
  decide +kernel
compact_certificate_declaration theorem product_82_value (v : ℕ→ℂ) :
    eval v product_82=eval v n_c33_20*eval v n_d0_21 := by
  rw [←product_82_checked, eval_mulShort]
compact_certificate_declaration theorem product_83_checked :
    mulShort n_c33_21 n_d0_22=product_83 := by
  decide +kernel
compact_certificate_declaration theorem product_83_value (v : ℕ→ℂ) :
    eval v product_83=eval v n_c33_21*eval v n_d0_22 := by
  rw [←product_83_checked, eval_mulShort]
compact_certificate_declaration theorem product_84_checked :
    mulShort n_c33_22 n_d0_23=product_84 := by
  decide +kernel
compact_certificate_declaration theorem product_84_value (v : ℕ→ℂ) :
    eval v product_84=eval v n_c33_22*eval v n_d0_23 := by
  rw [←product_84_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_14_checked :
    (spadd (spadd (spadd product_77 product_78) (spadd product_79 product_80)) (spadd (spadd product_81 product_82) (spadd product_83 product_84)))=partial_sum_14 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_14_value (v : ℕ→ℂ) :
    eval v partial_sum_14=eval v (spadd (spadd product_77 product_78) (spadd product_79 product_80))+eval v (spadd (spadd product_81 product_82) (spadd product_83 product_84)) := by
  rw [←partial_sum_14_checked, eval_add]
compact_certificate_declaration theorem product_85_checked :
    mulShort n_c33_23 n_d0_24=product_85 := by
  decide +kernel
compact_certificate_declaration theorem product_85_value (v : ℕ→ℂ) :
    eval v product_85=eval v n_c33_23*eval v n_d0_24 := by
  rw [←product_85_checked, eval_mulShort]
compact_certificate_declaration theorem product_86_checked :
    mulShort n_c33_24 n_d0_25=product_86 := by
  decide +kernel
compact_certificate_declaration theorem product_86_value (v : ℕ→ℂ) :
    eval v product_86=eval v n_c33_24*eval v n_d0_25 := by
  rw [←product_86_checked, eval_mulShort]
compact_certificate_declaration theorem product_87_checked :
    mulShort n_c33_25 n_d0_26=product_87 := by
  decide +kernel
compact_certificate_declaration theorem product_87_value (v : ℕ→ℂ) :
    eval v product_87=eval v n_c33_25*eval v n_d0_26 := by
  rw [←product_87_checked, eval_mulShort]
compact_certificate_declaration theorem product_88_checked :
    mulShort n_c33_26 n_d0_27=product_88 := by
  decide +kernel
compact_certificate_declaration theorem product_88_value (v : ℕ→ℂ) :
    eval v product_88=eval v n_c33_26*eval v n_d0_27 := by
  rw [←product_88_checked, eval_mulShort]
compact_certificate_declaration theorem product_89_checked :
    mulShort n_c33_27 n_d0_28=product_89 := by
  decide +kernel
compact_certificate_declaration theorem product_89_value (v : ℕ→ℂ) :
    eval v product_89=eval v n_c33_27*eval v n_d0_28 := by
  rw [←product_89_checked, eval_mulShort]
compact_certificate_declaration theorem product_90_checked :
    mulShort n_c33_28 n_d0_29=product_90 := by
  decide +kernel
compact_certificate_declaration theorem product_90_value (v : ℕ→ℂ) :
    eval v product_90=eval v n_c33_28*eval v n_d0_29 := by
  rw [←product_90_checked, eval_mulShort]
compact_certificate_declaration theorem product_91_checked :
    mulShort n_c33_29 n_d0_30=product_91 := by
  decide +kernel
compact_certificate_declaration theorem product_91_value (v : ℕ→ℂ) :
    eval v product_91=eval v n_c33_29*eval v n_d0_30 := by
  rw [←product_91_checked, eval_mulShort]
compact_certificate_declaration theorem product_92_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c33_30) n_d1_33=product_92 := by
  decide +kernel
compact_certificate_declaration theorem product_92_value (v : ℕ→ℂ) :
    eval v product_92=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c33_30)*eval v n_d1_33 := by
  rw [←product_92_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_15_checked :
    (spadd (spadd (spadd product_85 product_86) (spadd product_87 product_88)) (spadd (spadd product_89 product_90) (spadd product_91 product_92)))=partial_sum_15 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_15_value (v : ℕ→ℂ) :
    eval v partial_sum_15=eval v (spadd (spadd product_85 product_86) (spadd product_87 product_88))+eval v (spadd (spadd product_89 product_90) (spadd product_91 product_92)) := by
  rw [←partial_sum_15_checked, eval_add]
compact_certificate_declaration theorem partial_sum_16_checked :
    (spadd partial_sum_14 partial_sum_15)=partial_sum_16 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_16_value (v : ℕ→ℂ) :
    eval v partial_sum_16=eval v partial_sum_14+eval v partial_sum_15 := by
  rw [←partial_sum_16_checked, eval_add]
compact_certificate_declaration theorem partial_sum_17_checked :
    (spadd partial_sum_13 partial_sum_16)=partial_sum_17 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_17_value (v : ℕ→ℂ) :
    eval v partial_sum_17=eval v partial_sum_13+eval v partial_sum_16 := by
  rw [←partial_sum_17_checked, eval_add]
compact_certificate_declaration theorem checked_2 : checkZero e2=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_2 (y z w a b u : ℂ) :
    (certificate y z w a b u)[2]?=some 0 := by
  change some ((((((c33_0 y z w a b u)*(d0_0 y z w a b u)+((c33_1 y z w a b u)*(d0_1 y z w a b u)+(c33_2 y z w a b u)*(d0_2 y z w a b u)))+(((c33_3 y z w a b u)*(d0_3 y z w a b u)+(c33_4 y z w a b u)*(d0_4 y z w a b u))+((c33_5 y z w a b u)*(d0_5 y z w a b u)+(c33_6 y z w a b u)*(d0_6 y z w a b u))))+((((c33_7 y z w a b u)*(d0_7 y z w a b u)+(c33_8 y z w a b u)*(d0_8 y z w a b u))+((c33_9 y z w a b u)*(d0_9 y z w a b u)+(c33_10 y z w a b u)*(d0_10 y z w a b u)))+(((c33_11 y z w a b u)*(d0_12 y z w a b u)+(c33_12 y z w a b u)*(d0_13 y z w a b u))+((c33_13 y z w a b u)*(d0_14 y z w a b u)+(c33_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c33_15 y z w a b u)*(d0_16 y z w a b u)+(c33_16 y z w a b u)*(d0_17 y z w a b u))+((c33_17 y z w a b u)*(d0_18 y z w a b u)+(c33_18 y z w a b u)*(d0_19 y z w a b u)))+(((c33_19 y z w a b u)*(d0_20 y z w a b u)+(c33_20 y z w a b u)*(d0_21 y z w a b u))+((c33_21 y z w a b u)*(d0_22 y z w a b u)+(c33_22 y z w a b u)*(d0_23 y z w a b u))))+((((c33_23 y z w a b u)*(d0_24 y z w a b u)+(c33_24 y z w a b u)*(d0_25 y z w a b u))+((c33_25 y z w a b u)*(d0_26 y z w a b u)+(c33_26 y z w a b u)*(d0_27 y z w a b u)))+(((c33_27 y z w a b u)*(d0_28 y z w a b u)+(c33_28 y z w a b u)*(d0_29 y z w a b u))+((c33_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c33_30 y z w a b u)*(d1_33 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e2 checked_2
  simp only [e2, eval_add, eval_mul, eval_scale, eval_pow, product_62_value, product_63_value, product_64_value, product_65_value, product_66_value, product_67_value, product_68_value, product_69_value, product_70_value, product_71_value, product_72_value, product_73_value, product_74_value, product_75_value, product_76_value, partial_sum_12_value, partial_sum_13_value, product_77_value, product_78_value, product_79_value, product_80_value, product_81_value, product_82_value, product_83_value, product_84_value, partial_sum_14_value, product_85_value, product_86_value, product_87_value, product_88_value, product_89_value, product_90_value, product_91_value, product_92_value, partial_sum_15_value, partial_sum_16_value, partial_sum_17_value, n_c33_0_value y z w a b u, n_c33_1_value y z w a b u, n_c33_10_value y z w a b u, n_c33_11_value y z w a b u, n_c33_12_value y z w a b u, n_c33_13_value y z w a b u, n_c33_14_value y z w a b u, n_c33_15_value y z w a b u, n_c33_16_value y z w a b u, n_c33_17_value y z w a b u, n_c33_18_value y z w a b u, n_c33_19_value y z w a b u, n_c33_2_value y z w a b u, n_c33_20_value y z w a b u, n_c33_21_value y z w a b u, n_c33_22_value y z w a b u, n_c33_23_value y z w a b u, n_c33_24_value y z w a b u, n_c33_25_value y z w a b u, n_c33_26_value y z w a b u, n_c33_27_value y z w a b u, n_c33_28_value y z w a b u, n_c33_29_value y z w a b u, n_c33_3_value y z w a b u, n_c33_30_value y z w a b u, n_c33_4_value y z w a b u, n_c33_5_value y z w a b u, n_c33_6_value y z w a b u, n_c33_7_value y z w a b u, n_c33_8_value y z w a b u, n_c33_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_33_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_93_checked :
    mulShort n_c34_0 n_d0_0=product_93 := by
  decide +kernel
compact_certificate_declaration theorem product_93_value (v : ℕ→ℂ) :
    eval v product_93=eval v n_c34_0*eval v n_d0_0 := by
  rw [←product_93_checked, eval_mulShort]
compact_certificate_declaration theorem product_94_checked :
    mulShort n_c34_1 n_d0_1=product_94 := by
  decide +kernel
compact_certificate_declaration theorem product_94_value (v : ℕ→ℂ) :
    eval v product_94=eval v n_c34_1*eval v n_d0_1 := by
  rw [←product_94_checked, eval_mulShort]
compact_certificate_declaration theorem product_95_checked :
    mulShort n_c34_2 n_d0_2=product_95 := by
  decide +kernel
compact_certificate_declaration theorem product_95_value (v : ℕ→ℂ) :
    eval v product_95=eval v n_c34_2*eval v n_d0_2 := by
  rw [←product_95_checked, eval_mulShort]
compact_certificate_declaration theorem product_96_checked :
    mulShort n_c34_3 n_d0_3=product_96 := by
  decide +kernel
compact_certificate_declaration theorem product_96_value (v : ℕ→ℂ) :
    eval v product_96=eval v n_c34_3*eval v n_d0_3 := by
  rw [←product_96_checked, eval_mulShort]
compact_certificate_declaration theorem product_97_checked :
    mulShort n_c34_4 n_d0_4=product_97 := by
  decide +kernel
compact_certificate_declaration theorem product_97_value (v : ℕ→ℂ) :
    eval v product_97=eval v n_c34_4*eval v n_d0_4 := by
  rw [←product_97_checked, eval_mulShort]
compact_certificate_declaration theorem product_98_checked :
    mulShort n_c34_5 n_d0_5=product_98 := by
  decide +kernel
compact_certificate_declaration theorem product_98_value (v : ℕ→ℂ) :
    eval v product_98=eval v n_c34_5*eval v n_d0_5 := by
  rw [←product_98_checked, eval_mulShort]
compact_certificate_declaration theorem product_99_checked :
    mulShort n_c34_6 n_d0_6=product_99 := by
  decide +kernel
compact_certificate_declaration theorem product_99_value (v : ℕ→ℂ) :
    eval v product_99=eval v n_c34_6*eval v n_d0_6 := by
  rw [←product_99_checked, eval_mulShort]
compact_certificate_declaration theorem product_100_checked :
    mulShort n_c34_7 n_d0_7=product_100 := by
  decide +kernel
compact_certificate_declaration theorem product_100_value (v : ℕ→ℂ) :
    eval v product_100=eval v n_c34_7*eval v n_d0_7 := by
  rw [←product_100_checked, eval_mulShort]
compact_certificate_declaration theorem product_101_checked :
    mulShort n_c34_8 n_d0_8=product_101 := by
  decide +kernel
compact_certificate_declaration theorem product_101_value (v : ℕ→ℂ) :
    eval v product_101=eval v n_c34_8*eval v n_d0_8 := by
  rw [←product_101_checked, eval_mulShort]
compact_certificate_declaration theorem product_102_checked :
    mulShort n_c34_9 n_d0_9=product_102 := by
  decide +kernel
compact_certificate_declaration theorem product_102_value (v : ℕ→ℂ) :
    eval v product_102=eval v n_c34_9*eval v n_d0_9 := by
  rw [←product_102_checked, eval_mulShort]
compact_certificate_declaration theorem product_103_checked :
    mulShort n_c34_10 n_d0_10=product_103 := by
  decide +kernel
compact_certificate_declaration theorem product_103_value (v : ℕ→ℂ) :
    eval v product_103=eval v n_c34_10*eval v n_d0_10 := by
  rw [←product_103_checked, eval_mulShort]
compact_certificate_declaration theorem product_104_checked :
    mulShort n_c34_11 n_d0_12=product_104 := by
  decide +kernel
compact_certificate_declaration theorem product_104_value (v : ℕ→ℂ) :
    eval v product_104=eval v n_c34_11*eval v n_d0_12 := by
  rw [←product_104_checked, eval_mulShort]
compact_certificate_declaration theorem product_105_checked :
    mulShort n_c34_12 n_d0_13=product_105 := by
  decide +kernel
compact_certificate_declaration theorem product_105_value (v : ℕ→ℂ) :
    eval v product_105=eval v n_c34_12*eval v n_d0_13 := by
  rw [←product_105_checked, eval_mulShort]
compact_certificate_declaration theorem product_106_checked :
    mulShort n_c34_13 n_d0_14=product_106 := by
  decide +kernel
compact_certificate_declaration theorem product_106_value (v : ℕ→ℂ) :
    eval v product_106=eval v n_c34_13*eval v n_d0_14 := by
  rw [←product_106_checked, eval_mulShort]
}
certificate_batch {
compact_certificate_declaration theorem product_107_checked :
    mulShort n_c34_14 n_d0_15=product_107 := by
  decide +kernel
compact_certificate_declaration theorem product_107_value (v : ℕ→ℂ) :
    eval v product_107=eval v n_c34_14*eval v n_d0_15 := by
  rw [←product_107_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_18_checked :
    (spadd (spadd (spadd product_100 product_101) (spadd product_102 product_103)) (spadd (spadd product_104 product_105) (spadd product_106 product_107)))=partial_sum_18 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_18_value (v : ℕ→ℂ) :
    eval v partial_sum_18=eval v (spadd (spadd product_100 product_101) (spadd product_102 product_103))+eval v (spadd (spadd product_104 product_105) (spadd product_106 product_107)) := by
  rw [←partial_sum_18_checked, eval_add]
compact_certificate_declaration theorem partial_sum_19_checked :
    (spadd (spadd (spadd product_93 (spadd product_94 product_95)) (spadd (spadd product_96 product_97) (spadd product_98 product_99))) partial_sum_18)=partial_sum_19 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_19_value (v : ℕ→ℂ) :
    eval v partial_sum_19=eval v (spadd (spadd product_93 (spadd product_94 product_95)) (spadd (spadd product_96 product_97) (spadd product_98 product_99)))+eval v partial_sum_18 := by
  rw [←partial_sum_19_checked, eval_add]
compact_certificate_declaration theorem product_108_checked :
    mulShort n_c34_15 n_d0_16=product_108 := by
  decide +kernel
compact_certificate_declaration theorem product_108_value (v : ℕ→ℂ) :
    eval v product_108=eval v n_c34_15*eval v n_d0_16 := by
  rw [←product_108_checked, eval_mulShort]
compact_certificate_declaration theorem product_109_checked :
    mulShort n_c34_16 n_d0_17=product_109 := by
  decide +kernel
compact_certificate_declaration theorem product_109_value (v : ℕ→ℂ) :
    eval v product_109=eval v n_c34_16*eval v n_d0_17 := by
  rw [←product_109_checked, eval_mulShort]
compact_certificate_declaration theorem product_110_checked :
    mulShort n_c34_17 n_d0_18=product_110 := by
  decide +kernel
compact_certificate_declaration theorem product_110_value (v : ℕ→ℂ) :
    eval v product_110=eval v n_c34_17*eval v n_d0_18 := by
  rw [←product_110_checked, eval_mulShort]
compact_certificate_declaration theorem product_111_checked :
    mulShort n_c34_18 n_d0_19=product_111 := by
  decide +kernel
compact_certificate_declaration theorem product_111_value (v : ℕ→ℂ) :
    eval v product_111=eval v n_c34_18*eval v n_d0_19 := by
  rw [←product_111_checked, eval_mulShort]
compact_certificate_declaration theorem product_112_checked :
    mulShort n_c34_19 n_d0_20=product_112 := by
  decide +kernel
compact_certificate_declaration theorem product_112_value (v : ℕ→ℂ) :
    eval v product_112=eval v n_c34_19*eval v n_d0_20 := by
  rw [←product_112_checked, eval_mulShort]
compact_certificate_declaration theorem product_113_checked :
    mulShort n_c34_20 n_d0_21=product_113 := by
  decide +kernel
compact_certificate_declaration theorem product_113_value (v : ℕ→ℂ) :
    eval v product_113=eval v n_c34_20*eval v n_d0_21 := by
  rw [←product_113_checked, eval_mulShort]
compact_certificate_declaration theorem product_114_checked :
    mulShort n_c34_21 n_d0_22=product_114 := by
  decide +kernel
compact_certificate_declaration theorem product_114_value (v : ℕ→ℂ) :
    eval v product_114=eval v n_c34_21*eval v n_d0_22 := by
  rw [←product_114_checked, eval_mulShort]
compact_certificate_declaration theorem product_115_checked :
    mulShort n_c34_22 n_d0_23=product_115 := by
  decide +kernel
compact_certificate_declaration theorem product_115_value (v : ℕ→ℂ) :
    eval v product_115=eval v n_c34_22*eval v n_d0_23 := by
  rw [←product_115_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_20_checked :
    (spadd (spadd (spadd product_108 product_109) (spadd product_110 product_111)) (spadd (spadd product_112 product_113) (spadd product_114 product_115)))=partial_sum_20 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_20_value (v : ℕ→ℂ) :
    eval v partial_sum_20=eval v (spadd (spadd product_108 product_109) (spadd product_110 product_111))+eval v (spadd (spadd product_112 product_113) (spadd product_114 product_115)) := by
  rw [←partial_sum_20_checked, eval_add]
compact_certificate_declaration theorem product_116_checked :
    mulShort n_c34_23 n_d0_24=product_116 := by
  decide +kernel
compact_certificate_declaration theorem product_116_value (v : ℕ→ℂ) :
    eval v product_116=eval v n_c34_23*eval v n_d0_24 := by
  rw [←product_116_checked, eval_mulShort]
compact_certificate_declaration theorem product_117_checked :
    mulShort n_c34_24 n_d0_25=product_117 := by
  decide +kernel
compact_certificate_declaration theorem product_117_value (v : ℕ→ℂ) :
    eval v product_117=eval v n_c34_24*eval v n_d0_25 := by
  rw [←product_117_checked, eval_mulShort]
compact_certificate_declaration theorem product_118_checked :
    mulShort n_c34_25 n_d0_26=product_118 := by
  decide +kernel
compact_certificate_declaration theorem product_118_value (v : ℕ→ℂ) :
    eval v product_118=eval v n_c34_25*eval v n_d0_26 := by
  rw [←product_118_checked, eval_mulShort]
compact_certificate_declaration theorem product_119_checked :
    mulShort n_c34_26 n_d0_27=product_119 := by
  decide +kernel
compact_certificate_declaration theorem product_119_value (v : ℕ→ℂ) :
    eval v product_119=eval v n_c34_26*eval v n_d0_27 := by
  rw [←product_119_checked, eval_mulShort]
compact_certificate_declaration theorem product_120_checked :
    mulShort n_c34_27 n_d0_28=product_120 := by
  decide +kernel
compact_certificate_declaration theorem product_120_value (v : ℕ→ℂ) :
    eval v product_120=eval v n_c34_27*eval v n_d0_28 := by
  rw [←product_120_checked, eval_mulShort]
compact_certificate_declaration theorem product_121_checked :
    mulShort n_c34_28 n_d0_29=product_121 := by
  decide +kernel
compact_certificate_declaration theorem product_121_value (v : ℕ→ℂ) :
    eval v product_121=eval v n_c34_28*eval v n_d0_29 := by
  rw [←product_121_checked, eval_mulShort]
compact_certificate_declaration theorem product_122_checked :
    mulShort n_c34_29 n_d0_30=product_122 := by
  decide +kernel
compact_certificate_declaration theorem product_122_value (v : ℕ→ℂ) :
    eval v product_122=eval v n_c34_29*eval v n_d0_30 := by
  rw [←product_122_checked, eval_mulShort]
compact_certificate_declaration theorem product_123_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c34_30) n_d1_34=product_123 := by
  decide +kernel
compact_certificate_declaration theorem product_123_value (v : ℕ→ℂ) :
    eval v product_123=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c34_30)*eval v n_d1_34 := by
  rw [←product_123_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_21_checked :
    (spadd (spadd (spadd product_116 product_117) (spadd product_118 product_119)) (spadd (spadd product_120 product_121) (spadd product_122 product_123)))=partial_sum_21 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_21_value (v : ℕ→ℂ) :
    eval v partial_sum_21=eval v (spadd (spadd product_116 product_117) (spadd product_118 product_119))+eval v (spadd (spadd product_120 product_121) (spadd product_122 product_123)) := by
  rw [←partial_sum_21_checked, eval_add]
compact_certificate_declaration theorem partial_sum_22_checked :
    (spadd partial_sum_20 partial_sum_21)=partial_sum_22 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_22_value (v : ℕ→ℂ) :
    eval v partial_sum_22=eval v partial_sum_20+eval v partial_sum_21 := by
  rw [←partial_sum_22_checked, eval_add]
compact_certificate_declaration theorem partial_sum_23_checked :
    (spadd partial_sum_19 partial_sum_22)=partial_sum_23 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_23_value (v : ℕ→ℂ) :
    eval v partial_sum_23=eval v partial_sum_19+eval v partial_sum_22 := by
  rw [←partial_sum_23_checked, eval_add]
compact_certificate_declaration theorem checked_3 : checkZero e3=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_3 (y z w a b u : ℂ) :
    (certificate y z w a b u)[3]?=some 0 := by
  change some ((((((c34_0 y z w a b u)*(d0_0 y z w a b u)+((c34_1 y z w a b u)*(d0_1 y z w a b u)+(c34_2 y z w a b u)*(d0_2 y z w a b u)))+(((c34_3 y z w a b u)*(d0_3 y z w a b u)+(c34_4 y z w a b u)*(d0_4 y z w a b u))+((c34_5 y z w a b u)*(d0_5 y z w a b u)+(c34_6 y z w a b u)*(d0_6 y z w a b u))))+((((c34_7 y z w a b u)*(d0_7 y z w a b u)+(c34_8 y z w a b u)*(d0_8 y z w a b u))+((c34_9 y z w a b u)*(d0_9 y z w a b u)+(c34_10 y z w a b u)*(d0_10 y z w a b u)))+(((c34_11 y z w a b u)*(d0_12 y z w a b u)+(c34_12 y z w a b u)*(d0_13 y z w a b u))+((c34_13 y z w a b u)*(d0_14 y z w a b u)+(c34_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c34_15 y z w a b u)*(d0_16 y z w a b u)+(c34_16 y z w a b u)*(d0_17 y z w a b u))+((c34_17 y z w a b u)*(d0_18 y z w a b u)+(c34_18 y z w a b u)*(d0_19 y z w a b u)))+(((c34_19 y z w a b u)*(d0_20 y z w a b u)+(c34_20 y z w a b u)*(d0_21 y z w a b u))+((c34_21 y z w a b u)*(d0_22 y z w a b u)+(c34_22 y z w a b u)*(d0_23 y z w a b u))))+((((c34_23 y z w a b u)*(d0_24 y z w a b u)+(c34_24 y z w a b u)*(d0_25 y z w a b u))+((c34_25 y z w a b u)*(d0_26 y z w a b u)+(c34_26 y z w a b u)*(d0_27 y z w a b u)))+(((c34_27 y z w a b u)*(d0_28 y z w a b u)+(c34_28 y z w a b u)*(d0_29 y z w a b u))+((c34_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c34_30 y z w a b u)*(d1_34 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e3 checked_3
  simp only [e3, eval_add, eval_mul, eval_scale, eval_pow, product_93_value, product_94_value, product_95_value, product_96_value, product_97_value, product_98_value, product_99_value, product_100_value, product_101_value, product_102_value, product_103_value, product_104_value, product_105_value, product_106_value, product_107_value, partial_sum_18_value, partial_sum_19_value, product_108_value, product_109_value, product_110_value, product_111_value, product_112_value, product_113_value, product_114_value, product_115_value, partial_sum_20_value, product_116_value, product_117_value, product_118_value, product_119_value, product_120_value, product_121_value, product_122_value, product_123_value, partial_sum_21_value, partial_sum_22_value, partial_sum_23_value, n_c34_0_value y z w a b u, n_c34_1_value y z w a b u, n_c34_10_value y z w a b u, n_c34_11_value y z w a b u, n_c34_12_value y z w a b u, n_c34_13_value y z w a b u, n_c34_14_value y z w a b u, n_c34_15_value y z w a b u, n_c34_16_value y z w a b u, n_c34_17_value y z w a b u, n_c34_18_value y z w a b u, n_c34_19_value y z w a b u, n_c34_2_value y z w a b u, n_c34_20_value y z w a b u, n_c34_21_value y z w a b u, n_c34_22_value y z w a b u, n_c34_23_value y z w a b u, n_c34_24_value y z w a b u, n_c34_25_value y z w a b u, n_c34_26_value y z w a b u, n_c34_27_value y z w a b u, n_c34_28_value y z w a b u, n_c34_29_value y z w a b u, n_c34_3_value y z w a b u, n_c34_30_value y z w a b u, n_c34_4_value y z w a b u, n_c34_5_value y z w a b u, n_c34_6_value y z w a b u, n_c34_7_value y z w a b u, n_c34_8_value y z w a b u, n_c34_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_34_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_124_checked :
    mulShort n_c35_0 n_d0_0=product_124 := by
  decide +kernel
compact_certificate_declaration theorem product_124_value (v : ℕ→ℂ) :
    eval v product_124=eval v n_c35_0*eval v n_d0_0 := by
  rw [←product_124_checked, eval_mulShort]
compact_certificate_declaration theorem product_125_checked :
    mulShort n_c35_1 n_d0_1=product_125 := by
  decide +kernel
compact_certificate_declaration theorem product_125_value (v : ℕ→ℂ) :
    eval v product_125=eval v n_c35_1*eval v n_d0_1 := by
  rw [←product_125_checked, eval_mulShort]
compact_certificate_declaration theorem product_126_checked :
    mulShort n_c35_2 n_d0_2=product_126 := by
  decide +kernel
compact_certificate_declaration theorem product_126_value (v : ℕ→ℂ) :
    eval v product_126=eval v n_c35_2*eval v n_d0_2 := by
  rw [←product_126_checked, eval_mulShort]
compact_certificate_declaration theorem product_127_checked :
    mulShort n_c35_3 n_d0_3=product_127 := by
  decide +kernel
compact_certificate_declaration theorem product_127_value (v : ℕ→ℂ) :
    eval v product_127=eval v n_c35_3*eval v n_d0_3 := by
  rw [←product_127_checked, eval_mulShort]
compact_certificate_declaration theorem product_128_checked :
    mulShort n_c35_4 n_d0_4=product_128 := by
  decide +kernel
compact_certificate_declaration theorem product_128_value (v : ℕ→ℂ) :
    eval v product_128=eval v n_c35_4*eval v n_d0_4 := by
  rw [←product_128_checked, eval_mulShort]
compact_certificate_declaration theorem product_129_checked :
    mulShort n_c35_5 n_d0_5=product_129 := by
  decide +kernel
compact_certificate_declaration theorem product_129_value (v : ℕ→ℂ) :
    eval v product_129=eval v n_c35_5*eval v n_d0_5 := by
  rw [←product_129_checked, eval_mulShort]
compact_certificate_declaration theorem product_130_checked :
    mulShort n_c35_6 n_d0_6=product_130 := by
  decide +kernel
compact_certificate_declaration theorem product_130_value (v : ℕ→ℂ) :
    eval v product_130=eval v n_c35_6*eval v n_d0_6 := by
  rw [←product_130_checked, eval_mulShort]
compact_certificate_declaration theorem product_131_checked :
    mulShort n_c35_7 n_d0_7=product_131 := by
  decide +kernel
compact_certificate_declaration theorem product_131_value (v : ℕ→ℂ) :
    eval v product_131=eval v n_c35_7*eval v n_d0_7 := by
  rw [←product_131_checked, eval_mulShort]
compact_certificate_declaration theorem product_132_checked :
    mulShort n_c35_8 n_d0_8=product_132 := by
  decide +kernel
compact_certificate_declaration theorem product_132_value (v : ℕ→ℂ) :
    eval v product_132=eval v n_c35_8*eval v n_d0_8 := by
  rw [←product_132_checked, eval_mulShort]
compact_certificate_declaration theorem product_133_checked :
    mulShort n_c35_9 n_d0_9=product_133 := by
  decide +kernel
compact_certificate_declaration theorem product_133_value (v : ℕ→ℂ) :
    eval v product_133=eval v n_c35_9*eval v n_d0_9 := by
  rw [←product_133_checked, eval_mulShort]
compact_certificate_declaration theorem product_134_checked :
    mulShort n_c35_10 n_d0_10=product_134 := by
  decide +kernel
compact_certificate_declaration theorem product_134_value (v : ℕ→ℂ) :
    eval v product_134=eval v n_c35_10*eval v n_d0_10 := by
  rw [←product_134_checked, eval_mulShort]
compact_certificate_declaration theorem product_135_checked :
    mulShort n_c35_11 n_d0_12=product_135 := by
  decide +kernel
compact_certificate_declaration theorem product_135_value (v : ℕ→ℂ) :
    eval v product_135=eval v n_c35_11*eval v n_d0_12 := by
  rw [←product_135_checked, eval_mulShort]
compact_certificate_declaration theorem product_136_checked :
    mulShort n_c35_12 n_d0_13=product_136 := by
  decide +kernel
compact_certificate_declaration theorem product_136_value (v : ℕ→ℂ) :
    eval v product_136=eval v n_c35_12*eval v n_d0_13 := by
  rw [←product_136_checked, eval_mulShort]
compact_certificate_declaration theorem product_137_checked :
    mulShort n_c35_13 n_d0_14=product_137 := by
  decide +kernel
compact_certificate_declaration theorem product_137_value (v : ℕ→ℂ) :
    eval v product_137=eval v n_c35_13*eval v n_d0_14 := by
  rw [←product_137_checked, eval_mulShort]
compact_certificate_declaration theorem product_138_checked :
    mulShort n_c35_14 n_d0_15=product_138 := by
  decide +kernel
compact_certificate_declaration theorem product_138_value (v : ℕ→ℂ) :
    eval v product_138=eval v n_c35_14*eval v n_d0_15 := by
  rw [←product_138_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_24_checked :
    (spadd (spadd (spadd product_131 product_132) (spadd product_133 product_134)) (spadd (spadd product_135 product_136) (spadd product_137 product_138)))=partial_sum_24 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_24_value (v : ℕ→ℂ) :
    eval v partial_sum_24=eval v (spadd (spadd product_131 product_132) (spadd product_133 product_134))+eval v (spadd (spadd product_135 product_136) (spadd product_137 product_138)) := by
  rw [←partial_sum_24_checked, eval_add]
compact_certificate_declaration theorem partial_sum_25_checked :
    (spadd (spadd (spadd product_124 (spadd product_125 product_126)) (spadd (spadd product_127 product_128) (spadd product_129 product_130))) partial_sum_24)=partial_sum_25 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_25_value (v : ℕ→ℂ) :
    eval v partial_sum_25=eval v (spadd (spadd product_124 (spadd product_125 product_126)) (spadd (spadd product_127 product_128) (spadd product_129 product_130)))+eval v partial_sum_24 := by
  rw [←partial_sum_25_checked, eval_add]
compact_certificate_declaration theorem product_139_checked :
    mulShort n_c35_15 n_d0_16=product_139 := by
  decide +kernel
compact_certificate_declaration theorem product_139_value (v : ℕ→ℂ) :
    eval v product_139=eval v n_c35_15*eval v n_d0_16 := by
  rw [←product_139_checked, eval_mulShort]
compact_certificate_declaration theorem product_140_checked :
    mulShort n_c35_16 n_d0_17=product_140 := by
  decide +kernel

compact_certificate_declaration theorem product_140_value (v : ℕ→ℂ) :
    eval v product_140=eval v n_c35_16*eval v n_d0_17 := by
  rw [←product_140_checked, eval_mulShort]
compact_certificate_declaration theorem product_141_checked :
    mulShort n_c35_17 n_d0_18=product_141 := by
  decide +kernel
compact_certificate_declaration theorem product_141_value (v : ℕ→ℂ) :
    eval v product_141=eval v n_c35_17*eval v n_d0_18 := by
  rw [←product_141_checked, eval_mulShort]
compact_certificate_declaration theorem product_142_checked :
    mulShort n_c35_18 n_d0_19=product_142 := by
  decide +kernel
compact_certificate_declaration theorem product_142_value (v : ℕ→ℂ) :
    eval v product_142=eval v n_c35_18*eval v n_d0_19 := by
  rw [←product_142_checked, eval_mulShort]
compact_certificate_declaration theorem product_143_checked :
    mulShort n_c35_19 n_d0_20=product_143 := by
  decide +kernel
compact_certificate_declaration theorem product_143_value (v : ℕ→ℂ) :
    eval v product_143=eval v n_c35_19*eval v n_d0_20 := by
  rw [←product_143_checked, eval_mulShort]
compact_certificate_declaration theorem product_144_checked :
    mulShort n_c35_20 n_d0_21=product_144 := by
  decide +kernel
compact_certificate_declaration theorem product_144_value (v : ℕ→ℂ) :
    eval v product_144=eval v n_c35_20*eval v n_d0_21 := by
  rw [←product_144_checked, eval_mulShort]
compact_certificate_declaration theorem product_145_checked :
    mulShort n_c35_21 n_d0_22=product_145 := by
  decide +kernel
compact_certificate_declaration theorem product_145_value (v : ℕ→ℂ) :
    eval v product_145=eval v n_c35_21*eval v n_d0_22 := by
  rw [←product_145_checked, eval_mulShort]
compact_certificate_declaration theorem product_146_checked :
    mulShort n_c35_22 n_d0_23=product_146 := by
  decide +kernel
compact_certificate_declaration theorem product_146_value (v : ℕ→ℂ) :
    eval v product_146=eval v n_c35_22*eval v n_d0_23 := by
  rw [←product_146_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_26_checked :
    (spadd (spadd (spadd product_139 product_140) (spadd product_141 product_142)) (spadd (spadd product_143 product_144) (spadd product_145 product_146)))=partial_sum_26 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_26_value (v : ℕ→ℂ) :
    eval v partial_sum_26=eval v (spadd (spadd product_139 product_140) (spadd product_141 product_142))+eval v (spadd (spadd product_143 product_144) (spadd product_145 product_146)) := by
  rw [←partial_sum_26_checked, eval_add]
compact_certificate_declaration theorem product_147_checked :
    mulShort n_c35_23 n_d0_24=product_147 := by
  decide +kernel
compact_certificate_declaration theorem product_147_value (v : ℕ→ℂ) :
    eval v product_147=eval v n_c35_23*eval v n_d0_24 := by
  rw [←product_147_checked, eval_mulShort]
compact_certificate_declaration theorem product_148_checked :
    mulShort n_c35_24 n_d0_25=product_148 := by
  decide +kernel
compact_certificate_declaration theorem product_148_value (v : ℕ→ℂ) :
    eval v product_148=eval v n_c35_24*eval v n_d0_25 := by
  rw [←product_148_checked, eval_mulShort]
compact_certificate_declaration theorem product_149_checked :
    mulShort n_c35_25 n_d0_26=product_149 := by
  decide +kernel
compact_certificate_declaration theorem product_149_value (v : ℕ→ℂ) :
    eval v product_149=eval v n_c35_25*eval v n_d0_26 := by
  rw [←product_149_checked, eval_mulShort]
compact_certificate_declaration theorem product_150_checked :
    mulShort n_c35_26 n_d0_27=product_150 := by
  decide +kernel
compact_certificate_declaration theorem product_150_value (v : ℕ→ℂ) :
    eval v product_150=eval v n_c35_26*eval v n_d0_27 := by
  rw [←product_150_checked, eval_mulShort]
compact_certificate_declaration theorem product_151_checked :
    mulShort n_c35_27 n_d0_28=product_151 := by
  decide +kernel
compact_certificate_declaration theorem product_151_value (v : ℕ→ℂ) :
    eval v product_151=eval v n_c35_27*eval v n_d0_28 := by
  rw [←product_151_checked, eval_mulShort]
compact_certificate_declaration theorem product_152_checked :
    mulShort n_c35_28 n_d0_29=product_152 := by
  decide +kernel
compact_certificate_declaration theorem product_152_value (v : ℕ→ℂ) :
    eval v product_152=eval v n_c35_28*eval v n_d0_29 := by
  rw [←product_152_checked, eval_mulShort]
compact_certificate_declaration theorem product_153_checked :
    mulShort n_c35_29 n_d0_30=product_153 := by
  decide +kernel
compact_certificate_declaration theorem product_153_value (v : ℕ→ℂ) :
    eval v product_153=eval v n_c35_29*eval v n_d0_30 := by
  rw [←product_153_checked, eval_mulShort]
compact_certificate_declaration theorem product_154_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c35_30) n_d1_35=product_154 := by
  decide +kernel
compact_certificate_declaration theorem product_154_value (v : ℕ→ℂ) :
    eval v product_154=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c35_30)*eval v n_d1_35 := by
  rw [←product_154_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_27_checked :
    (spadd (spadd (spadd product_147 product_148) (spadd product_149 product_150)) (spadd (spadd product_151 product_152) (spadd product_153 product_154)))=partial_sum_27 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_27_value (v : ℕ→ℂ) :
    eval v partial_sum_27=eval v (spadd (spadd product_147 product_148) (spadd product_149 product_150))+eval v (spadd (spadd product_151 product_152) (spadd product_153 product_154)) := by
  rw [←partial_sum_27_checked, eval_add]
compact_certificate_declaration theorem partial_sum_28_checked :
    (spadd partial_sum_26 partial_sum_27)=partial_sum_28 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_28_value (v : ℕ→ℂ) :
    eval v partial_sum_28=eval v partial_sum_26+eval v partial_sum_27 := by
  rw [←partial_sum_28_checked, eval_add]
compact_certificate_declaration theorem partial_sum_29_checked :
    (spadd partial_sum_25 partial_sum_28)=partial_sum_29 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_29_value (v : ℕ→ℂ) :
    eval v partial_sum_29=eval v partial_sum_25+eval v partial_sum_28 := by
  rw [←partial_sum_29_checked, eval_add]
compact_certificate_declaration theorem checked_4 : checkZero e4=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_4 (y z w a b u : ℂ) :
    (certificate y z w a b u)[4]?=some 0 := by
  change some ((((((c35_0 y z w a b u)*(d0_0 y z w a b u)+((c35_1 y z w a b u)*(d0_1 y z w a b u)+(c35_2 y z w a b u)*(d0_2 y z w a b u)))+(((c35_3 y z w a b u)*(d0_3 y z w a b u)+(c35_4 y z w a b u)*(d0_4 y z w a b u))+((c35_5 y z w a b u)*(d0_5 y z w a b u)+(c35_6 y z w a b u)*(d0_6 y z w a b u))))+((((c35_7 y z w a b u)*(d0_7 y z w a b u)+(c35_8 y z w a b u)*(d0_8 y z w a b u))+((c35_9 y z w a b u)*(d0_9 y z w a b u)+(c35_10 y z w a b u)*(d0_10 y z w a b u)))+(((c35_11 y z w a b u)*(d0_12 y z w a b u)+(c35_12 y z w a b u)*(d0_13 y z w a b u))+((c35_13 y z w a b u)*(d0_14 y z w a b u)+(c35_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c35_15 y z w a b u)*(d0_16 y z w a b u)+(c35_16 y z w a b u)*(d0_17 y z w a b u))+((c35_17 y z w a b u)*(d0_18 y z w a b u)+(c35_18 y z w a b u)*(d0_19 y z w a b u)))+(((c35_19 y z w a b u)*(d0_20 y z w a b u)+(c35_20 y z w a b u)*(d0_21 y z w a b u))+((c35_21 y z w a b u)*(d0_22 y z w a b u)+(c35_22 y z w a b u)*(d0_23 y z w a b u))))+((((c35_23 y z w a b u)*(d0_24 y z w a b u)+(c35_24 y z w a b u)*(d0_25 y z w a b u))+((c35_25 y z w a b u)*(d0_26 y z w a b u)+(c35_26 y z w a b u)*(d0_27 y z w a b u)))+(((c35_27 y z w a b u)*(d0_28 y z w a b u)+(c35_28 y z w a b u)*(d0_29 y z w a b u))+((c35_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c35_30 y z w a b u)*(d1_35 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e4 checked_4
  simp only [e4, eval_add, eval_mul, eval_scale, eval_pow, product_124_value, product_125_value, product_126_value, product_127_value, product_128_value, product_129_value, product_130_value, product_131_value, product_132_value, product_133_value, product_134_value, product_135_value, product_136_value, product_137_value, product_138_value, partial_sum_24_value, partial_sum_25_value, product_139_value, product_140_value, product_141_value, product_142_value, product_143_value, product_144_value, product_145_value, product_146_value, partial_sum_26_value, product_147_value, product_148_value, product_149_value, product_150_value, product_151_value, product_152_value, product_153_value, product_154_value, partial_sum_27_value, partial_sum_28_value, partial_sum_29_value, n_c35_0_value y z w a b u, n_c35_1_value y z w a b u, n_c35_10_value y z w a b u, n_c35_11_value y z w a b u, n_c35_12_value y z w a b u, n_c35_13_value y z w a b u, n_c35_14_value y z w a b u, n_c35_15_value y z w a b u, n_c35_16_value y z w a b u, n_c35_17_value y z w a b u, n_c35_18_value y z w a b u, n_c35_19_value y z w a b u, n_c35_2_value y z w a b u, n_c35_20_value y z w a b u, n_c35_21_value y z w a b u, n_c35_22_value y z w a b u, n_c35_23_value y z w a b u, n_c35_24_value y z w a b u, n_c35_25_value y z w a b u, n_c35_26_value y z w a b u, n_c35_27_value y z w a b u, n_c35_28_value y z w a b u, n_c35_29_value y z w a b u, n_c35_3_value y z w a b u, n_c35_30_value y z w a b u, n_c35_4_value y z w a b u, n_c35_5_value y z w a b u, n_c35_6_value y z w a b u, n_c35_7_value y z w a b u, n_c35_8_value y z w a b u, n_c35_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_35_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_155_checked :
    mulShort n_c36_0 n_d0_0=product_155 := by
  decide +kernel
compact_certificate_declaration theorem product_155_value (v : ℕ→ℂ) :
    eval v product_155=eval v n_c36_0*eval v n_d0_0 := by
  rw [←product_155_checked, eval_mulShort]
compact_certificate_declaration theorem product_156_checked :
    mulShort n_c36_1 n_d0_1=product_156 := by
  decide +kernel
compact_certificate_declaration theorem product_156_value (v : ℕ→ℂ) :
    eval v product_156=eval v n_c36_1*eval v n_d0_1 := by
  rw [←product_156_checked, eval_mulShort]
compact_certificate_declaration theorem product_157_checked :
    mulShort n_c36_2 n_d0_2=product_157 := by
  decide +kernel
compact_certificate_declaration theorem product_157_value (v : ℕ→ℂ) :
    eval v product_157=eval v n_c36_2*eval v n_d0_2 := by
  rw [←product_157_checked, eval_mulShort]
compact_certificate_declaration theorem product_158_checked :
    mulShort n_c36_3 n_d0_3=product_158 := by
  decide +kernel
compact_certificate_declaration theorem product_158_value (v : ℕ→ℂ) :
    eval v product_158=eval v n_c36_3*eval v n_d0_3 := by
  rw [←product_158_checked, eval_mulShort]
compact_certificate_declaration theorem product_159_checked :
    mulShort n_c36_4 n_d0_4=product_159 := by
  decide +kernel
compact_certificate_declaration theorem product_159_value (v : ℕ→ℂ) :
    eval v product_159=eval v n_c36_4*eval v n_d0_4 := by
  rw [←product_159_checked, eval_mulShort]
compact_certificate_declaration theorem product_160_checked :
    mulShort n_c36_5 n_d0_5=product_160 := by
  decide +kernel
compact_certificate_declaration theorem product_160_value (v : ℕ→ℂ) :
    eval v product_160=eval v n_c36_5*eval v n_d0_5 := by
  rw [←product_160_checked, eval_mulShort]
compact_certificate_declaration theorem product_161_checked :
    mulShort n_c36_6 n_d0_6=product_161 := by
  decide +kernel
compact_certificate_declaration theorem product_161_value (v : ℕ→ℂ) :
    eval v product_161=eval v n_c36_6*eval v n_d0_6 := by
  rw [←product_161_checked, eval_mulShort]
compact_certificate_declaration theorem product_162_checked :
    mulShort n_c36_7 n_d0_7=product_162 := by
  decide +kernel
compact_certificate_declaration theorem product_162_value (v : ℕ→ℂ) :
    eval v product_162=eval v n_c36_7*eval v n_d0_7 := by
  rw [←product_162_checked, eval_mulShort]
compact_certificate_declaration theorem product_163_checked :
    mulShort n_c36_8 n_d0_8=product_163 := by
  decide +kernel
compact_certificate_declaration theorem product_163_value (v : ℕ→ℂ) :
    eval v product_163=eval v n_c36_8*eval v n_d0_8 := by
  rw [←product_163_checked, eval_mulShort]
compact_certificate_declaration theorem product_164_checked :
    mulShort n_c36_9 n_d0_9=product_164 := by
  decide +kernel
compact_certificate_declaration theorem product_164_value (v : ℕ→ℂ) :
    eval v product_164=eval v n_c36_9*eval v n_d0_9 := by
  rw [←product_164_checked, eval_mulShort]
compact_certificate_declaration theorem product_165_checked :
    mulShort n_c36_10 n_d0_10=product_165 := by
  decide +kernel
compact_certificate_declaration theorem product_165_value (v : ℕ→ℂ) :
    eval v product_165=eval v n_c36_10*eval v n_d0_10 := by
  rw [←product_165_checked, eval_mulShort]
compact_certificate_declaration theorem product_166_checked :
    mulShort n_c36_11 n_d0_12=product_166 := by
  decide +kernel
compact_certificate_declaration theorem product_166_value (v : ℕ→ℂ) :
    eval v product_166=eval v n_c36_11*eval v n_d0_12 := by
  rw [←product_166_checked, eval_mulShort]
compact_certificate_declaration theorem product_167_checked :
    mulShort n_c36_12 n_d0_13=product_167 := by
  decide +kernel
compact_certificate_declaration theorem product_167_value (v : ℕ→ℂ) :
    eval v product_167=eval v n_c36_12*eval v n_d0_13 := by
  rw [←product_167_checked, eval_mulShort]
compact_certificate_declaration theorem product_168_checked :
    mulShort n_c36_13 n_d0_14=product_168 := by
  decide +kernel
compact_certificate_declaration theorem product_168_value (v : ℕ→ℂ) :
    eval v product_168=eval v n_c36_13*eval v n_d0_14 := by
  rw [←product_168_checked, eval_mulShort]
compact_certificate_declaration theorem product_169_checked :
    mulShort n_c36_14 n_d0_15=product_169 := by
  decide +kernel
compact_certificate_declaration theorem product_169_value (v : ℕ→ℂ) :
    eval v product_169=eval v n_c36_14*eval v n_d0_15 := by
  rw [←product_169_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_30_checked :
    (spadd (spadd (spadd product_162 product_163) (spadd product_164 product_165)) (spadd (spadd product_166 product_167) (spadd product_168 product_169)))=partial_sum_30 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_30_value (v : ℕ→ℂ) :
    eval v partial_sum_30=eval v (spadd (spadd product_162 product_163) (spadd product_164 product_165))+eval v (spadd (spadd product_166 product_167) (spadd product_168 product_169)) := by
  rw [←partial_sum_30_checked, eval_add]
compact_certificate_declaration theorem partial_sum_31_checked :
    (spadd (spadd (spadd product_155 (spadd product_156 product_157)) (spadd (spadd product_158 product_159) (spadd product_160 product_161))) partial_sum_30)=partial_sum_31 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_31_value (v : ℕ→ℂ) :
    eval v partial_sum_31=eval v (spadd (spadd product_155 (spadd product_156 product_157)) (spadd (spadd product_158 product_159) (spadd product_160 product_161)))+eval v partial_sum_30 := by
  rw [←partial_sum_31_checked, eval_add]
compact_certificate_declaration theorem product_170_checked :
    mulShort n_c36_15 n_d0_16=product_170 := by
  decide +kernel
compact_certificate_declaration theorem product_170_value (v : ℕ→ℂ) :
    eval v product_170=eval v n_c36_15*eval v n_d0_16 := by
  rw [←product_170_checked, eval_mulShort]
compact_certificate_declaration theorem product_171_checked :
    mulShort n_c36_16 n_d0_17=product_171 := by
  decide +kernel
compact_certificate_declaration theorem product_171_value (v : ℕ→ℂ) :
    eval v product_171=eval v n_c36_16*eval v n_d0_17 := by
  rw [←product_171_checked, eval_mulShort]
compact_certificate_declaration theorem product_172_checked :
    mulShort n_c36_17 n_d0_18=product_172 := by
  decide +kernel
compact_certificate_declaration theorem product_172_value (v : ℕ→ℂ) :
    eval v product_172=eval v n_c36_17*eval v n_d0_18 := by
  rw [←product_172_checked, eval_mulShort]
compact_certificate_declaration theorem product_173_checked :
    mulShort n_c36_18 n_d0_19=product_173 := by
  decide +kernel
compact_certificate_declaration theorem product_173_value (v : ℕ→ℂ) :
    eval v product_173=eval v n_c36_18*eval v n_d0_19 := by
  rw [←product_173_checked, eval_mulShort]
compact_certificate_declaration theorem product_174_checked :
    mulShort n_c36_19 n_d0_20=product_174 := by
  decide +kernel
compact_certificate_declaration theorem product_174_value (v : ℕ→ℂ) :
    eval v product_174=eval v n_c36_19*eval v n_d0_20 := by
  rw [←product_174_checked, eval_mulShort]
compact_certificate_declaration theorem product_175_checked :
    mulShort n_c36_20 n_d0_21=product_175 := by
  decide +kernel
compact_certificate_declaration theorem product_175_value (v : ℕ→ℂ) :
    eval v product_175=eval v n_c36_20*eval v n_d0_21 := by
  rw [←product_175_checked, eval_mulShort]
compact_certificate_declaration theorem product_176_checked :
    mulShort n_c36_21 n_d0_22=product_176 := by
  decide +kernel
compact_certificate_declaration theorem product_176_value (v : ℕ→ℂ) :
    eval v product_176=eval v n_c36_21*eval v n_d0_22 := by
  rw [←product_176_checked, eval_mulShort]
compact_certificate_declaration theorem product_177_checked :
    mulShort n_c36_22 n_d0_23=product_177 := by
  decide +kernel
compact_certificate_declaration theorem product_177_value (v : ℕ→ℂ) :
    eval v product_177=eval v n_c36_22*eval v n_d0_23 := by
  rw [←product_177_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_32_checked :
    (spadd (spadd (spadd product_170 product_171) (spadd product_172 product_173)) (spadd (spadd product_174 product_175) (spadd product_176 product_177)))=partial_sum_32 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_32_value (v : ℕ→ℂ) :
    eval v partial_sum_32=eval v (spadd (spadd product_170 product_171) (spadd product_172 product_173))+eval v (spadd (spadd product_174 product_175) (spadd product_176 product_177)) := by
  rw [←partial_sum_32_checked, eval_add]
compact_certificate_declaration theorem product_178_checked :
    mulShort n_c36_23 n_d0_24=product_178 := by
  decide +kernel
compact_certificate_declaration theorem product_178_value (v : ℕ→ℂ) :
    eval v product_178=eval v n_c36_23*eval v n_d0_24 := by
  rw [←product_178_checked, eval_mulShort]
compact_certificate_declaration theorem product_179_checked :
    mulShort n_c36_24 n_d0_25=product_179 := by
  decide +kernel
compact_certificate_declaration theorem product_179_value (v : ℕ→ℂ) :
    eval v product_179=eval v n_c36_24*eval v n_d0_25 := by
  rw [←product_179_checked, eval_mulShort]
compact_certificate_declaration theorem product_180_checked :
    mulShort n_c36_25 n_d0_26=product_180 := by
  decide +kernel
compact_certificate_declaration theorem product_180_value (v : ℕ→ℂ) :
    eval v product_180=eval v n_c36_25*eval v n_d0_26 := by
  rw [←product_180_checked, eval_mulShort]
compact_certificate_declaration theorem product_181_checked :
    mulShort n_c36_26 n_d0_27=product_181 := by
  decide +kernel
compact_certificate_declaration theorem product_181_value (v : ℕ→ℂ) :
    eval v product_181=eval v n_c36_26*eval v n_d0_27 := by
  rw [←product_181_checked, eval_mulShort]
compact_certificate_declaration theorem product_182_checked :
    mulShort n_c36_27 n_d0_28=product_182 := by
  decide +kernel
compact_certificate_declaration theorem product_182_value (v : ℕ→ℂ) :
    eval v product_182=eval v n_c36_27*eval v n_d0_28 := by
  rw [←product_182_checked, eval_mulShort]
compact_certificate_declaration theorem product_183_checked :
    mulShort n_c36_28 n_d0_29=product_183 := by
  decide +kernel
compact_certificate_declaration theorem product_183_value (v : ℕ→ℂ) :
    eval v product_183=eval v n_c36_28*eval v n_d0_29 := by
  rw [←product_183_checked, eval_mulShort]
compact_certificate_declaration theorem product_184_checked :
    mulShort n_c36_29 n_d0_30=product_184 := by
  decide +kernel
compact_certificate_declaration theorem product_184_value (v : ℕ→ℂ) :
    eval v product_184=eval v n_c36_29*eval v n_d0_30 := by
  rw [←product_184_checked, eval_mulShort]
compact_certificate_declaration theorem product_185_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c36_30) n_d1_36=product_185 := by
  decide +kernel
compact_certificate_declaration theorem product_185_value (v : ℕ→ℂ) :
    eval v product_185=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c36_30)*eval v n_d1_36 := by
  rw [←product_185_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_33_checked :
    (spadd (spadd (spadd product_178 product_179) (spadd product_180 product_181)) (spadd (spadd product_182 product_183) (spadd product_184 product_185)))=partial_sum_33 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_33_value (v : ℕ→ℂ) :
    eval v partial_sum_33=eval v (spadd (spadd product_178 product_179) (spadd product_180 product_181))+eval v (spadd (spadd product_182 product_183) (spadd product_184 product_185)) := by
  rw [←partial_sum_33_checked, eval_add]
compact_certificate_declaration theorem partial_sum_34_checked :
    (spadd partial_sum_32 partial_sum_33)=partial_sum_34 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_34_value (v : ℕ→ℂ) :
    eval v partial_sum_34=eval v partial_sum_32+eval v partial_sum_33 := by
  rw [←partial_sum_34_checked, eval_add]
compact_certificate_declaration theorem partial_sum_35_checked :
    (spadd partial_sum_31 partial_sum_34)=partial_sum_35 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_35_value (v : ℕ→ℂ) :
    eval v partial_sum_35=eval v partial_sum_31+eval v partial_sum_34 := by
  rw [←partial_sum_35_checked, eval_add]
compact_certificate_declaration theorem checked_5 : checkZero e5=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_5 (y z w a b u : ℂ) :
    (certificate y z w a b u)[5]?=some 0 := by
  change some ((((((c36_0 y z w a b u)*(d0_0 y z w a b u)+((c36_1 y z w a b u)*(d0_1 y z w a b u)+(c36_2 y z w a b u)*(d0_2 y z w a b u)))+(((c36_3 y z w a b u)*(d0_3 y z w a b u)+(c36_4 y z w a b u)*(d0_4 y z w a b u))+((c36_5 y z w a b u)*(d0_5 y z w a b u)+(c36_6 y z w a b u)*(d0_6 y z w a b u))))+((((c36_7 y z w a b u)*(d0_7 y z w a b u)+(c36_8 y z w a b u)*(d0_8 y z w a b u))+((c36_9 y z w a b u)*(d0_9 y z w a b u)+(c36_10 y z w a b u)*(d0_10 y z w a b u)))+(((c36_11 y z w a b u)*(d0_12 y z w a b u)+(c36_12 y z w a b u)*(d0_13 y z w a b u))+((c36_13 y z w a b u)*(d0_14 y z w a b u)+(c36_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c36_15 y z w a b u)*(d0_16 y z w a b u)+(c36_16 y z w a b u)*(d0_17 y z w a b u))+((c36_17 y z w a b u)*(d0_18 y z w a b u)+(c36_18 y z w a b u)*(d0_19 y z w a b u)))+(((c36_19 y z w a b u)*(d0_20 y z w a b u)+(c36_20 y z w a b u)*(d0_21 y z w a b u))+((c36_21 y z w a b u)*(d0_22 y z w a b u)+(c36_22 y z w a b u)*(d0_23 y z w a b u))))+((((c36_23 y z w a b u)*(d0_24 y z w a b u)+(c36_24 y z w a b u)*(d0_25 y z w a b u))+((c36_25 y z w a b u)*(d0_26 y z w a b u)+(c36_26 y z w a b u)*(d0_27 y z w a b u)))+(((c36_27 y z w a b u)*(d0_28 y z w a b u)+(c36_28 y z w a b u)*(d0_29 y z w a b u))+((c36_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c36_30 y z w a b u)*(d1_36 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e5 checked_5
  simp only [e5, eval_add, eval_mul, eval_scale, eval_pow, product_155_value, product_156_value, product_157_value, product_158_value, product_159_value, product_160_value, product_161_value, product_162_value, product_163_value, product_164_value, product_165_value, product_166_value, product_167_value, product_168_value, product_169_value, partial_sum_30_value, partial_sum_31_value, product_170_value, product_171_value, product_172_value, product_173_value, product_174_value, product_175_value, product_176_value, product_177_value, partial_sum_32_value, product_178_value, product_179_value, product_180_value, product_181_value, product_182_value, product_183_value, product_184_value, product_185_value, partial_sum_33_value, partial_sum_34_value, partial_sum_35_value, n_c36_0_value y z w a b u, n_c36_1_value y z w a b u, n_c36_10_value y z w a b u, n_c36_11_value y z w a b u, n_c36_12_value y z w a b u, n_c36_13_value y z w a b u, n_c36_14_value y z w a b u, n_c36_15_value y z w a b u, n_c36_16_value y z w a b u, n_c36_17_value y z w a b u, n_c36_18_value y z w a b u, n_c36_19_value y z w a b u, n_c36_2_value y z w a b u, n_c36_20_value y z w a b u, n_c36_21_value y z w a b u, n_c36_22_value y z w a b u, n_c36_23_value y z w a b u, n_c36_24_value y z w a b u, n_c36_25_value y z w a b u, n_c36_26_value y z w a b u, n_c36_27_value y z w a b u, n_c36_28_value y z w a b u, n_c36_29_value y z w a b u, n_c36_3_value y z w a b u, n_c36_30_value y z w a b u, n_c36_4_value y z w a b u, n_c36_5_value y z w a b u, n_c36_6_value y z w a b u, n_c36_7_value y z w a b u, n_c36_8_value y z w a b u, n_c36_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_36_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_186_checked :
    mulShort n_c37_0 n_d0_0=product_186 := by
  decide +kernel
compact_certificate_declaration theorem product_186_value (v : ℕ→ℂ) :
    eval v product_186=eval v n_c37_0*eval v n_d0_0 := by
  rw [←product_186_checked, eval_mulShort]
compact_certificate_declaration theorem product_187_checked :
    mulShort n_c37_1 n_d0_1=product_187 := by
  decide +kernel
compact_certificate_declaration theorem product_187_value (v : ℕ→ℂ) :
    eval v product_187=eval v n_c37_1*eval v n_d0_1 := by
  rw [←product_187_checked, eval_mulShort]
compact_certificate_declaration theorem product_188_checked :
    mulShort n_c37_2 n_d0_2=product_188 := by
  decide +kernel
compact_certificate_declaration theorem product_188_value (v : ℕ→ℂ) :
    eval v product_188=eval v n_c37_2*eval v n_d0_2 := by
  rw [←product_188_checked, eval_mulShort]
compact_certificate_declaration theorem product_189_checked :
    mulShort n_c37_3 n_d0_3=product_189 := by
  decide +kernel
compact_certificate_declaration theorem product_189_value (v : ℕ→ℂ) :
    eval v product_189=eval v n_c37_3*eval v n_d0_3 := by
  rw [←product_189_checked, eval_mulShort]
compact_certificate_declaration theorem product_190_checked :
    mulShort n_c37_4 n_d0_4=product_190 := by
  decide +kernel
compact_certificate_declaration theorem product_190_value (v : ℕ→ℂ) :
    eval v product_190=eval v n_c37_4*eval v n_d0_4 := by
  rw [←product_190_checked, eval_mulShort]
compact_certificate_declaration theorem product_191_checked :
    mulShort n_c37_5 n_d0_5=product_191 := by
  decide +kernel
compact_certificate_declaration theorem product_191_value (v : ℕ→ℂ) :
    eval v product_191=eval v n_c37_5*eval v n_d0_5 := by
  rw [←product_191_checked, eval_mulShort]
compact_certificate_declaration theorem product_192_checked :
    mulShort n_c37_6 n_d0_6=product_192 := by
  decide +kernel
compact_certificate_declaration theorem product_192_value (v : ℕ→ℂ) :
    eval v product_192=eval v n_c37_6*eval v n_d0_6 := by
  rw [←product_192_checked, eval_mulShort]
compact_certificate_declaration theorem product_193_checked :
    mulShort n_c37_7 n_d0_7=product_193 := by
  decide +kernel
compact_certificate_declaration theorem product_193_value (v : ℕ→ℂ) :
    eval v product_193=eval v n_c37_7*eval v n_d0_7 := by
  rw [←product_193_checked, eval_mulShort]
compact_certificate_declaration theorem product_194_checked :
    mulShort n_c37_8 n_d0_8=product_194 := by
  decide +kernel
compact_certificate_declaration theorem product_194_value (v : ℕ→ℂ) :
    eval v product_194=eval v n_c37_8*eval v n_d0_8 := by
  rw [←product_194_checked, eval_mulShort]
compact_certificate_declaration theorem product_195_checked :
    mulShort n_c37_9 n_d0_9=product_195 := by
  decide +kernel
compact_certificate_declaration theorem product_195_value (v : ℕ→ℂ) :
    eval v product_195=eval v n_c37_9*eval v n_d0_9 := by
  rw [←product_195_checked, eval_mulShort]
compact_certificate_declaration theorem product_196_checked :
    mulShort n_c37_10 n_d0_10=product_196 := by
  decide +kernel
compact_certificate_declaration theorem product_196_value (v : ℕ→ℂ) :
    eval v product_196=eval v n_c37_10*eval v n_d0_10 := by
  rw [←product_196_checked, eval_mulShort]
compact_certificate_declaration theorem product_197_checked :
    mulShort n_c37_11 n_d0_12=product_197 := by
  decide +kernel
compact_certificate_declaration theorem product_197_value (v : ℕ→ℂ) :
    eval v product_197=eval v n_c37_11*eval v n_d0_12 := by
  rw [←product_197_checked, eval_mulShort]
compact_certificate_declaration theorem product_198_checked :
    mulShort n_c37_12 n_d0_13=product_198 := by
  decide +kernel
compact_certificate_declaration theorem product_198_value (v : ℕ→ℂ) :
    eval v product_198=eval v n_c37_12*eval v n_d0_13 := by
  rw [←product_198_checked, eval_mulShort]
compact_certificate_declaration theorem product_199_checked :
    mulShort n_c37_13 n_d0_14=product_199 := by
  decide +kernel
compact_certificate_declaration theorem product_199_value (v : ℕ→ℂ) :
    eval v product_199=eval v n_c37_13*eval v n_d0_14 := by
  rw [←product_199_checked, eval_mulShort]
compact_certificate_declaration theorem product_200_checked :
    mulShort n_c37_14 n_d0_15=product_200 := by
  decide +kernel
compact_certificate_declaration theorem product_200_value (v : ℕ→ℂ) :
    eval v product_200=eval v n_c37_14*eval v n_d0_15 := by
  rw [←product_200_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_36_checked :
    (spadd (spadd (spadd product_193 product_194) (spadd product_195 product_196)) (spadd (spadd product_197 product_198) (spadd product_199 product_200)))=partial_sum_36 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_36_value (v : ℕ→ℂ) :
    eval v partial_sum_36=eval v (spadd (spadd product_193 product_194) (spadd product_195 product_196))+eval v (spadd (spadd product_197 product_198) (spadd product_199 product_200)) := by
  rw [←partial_sum_36_checked, eval_add]
compact_certificate_declaration theorem partial_sum_37_checked :
    (spadd (spadd (spadd product_186 (spadd product_187 product_188)) (spadd (spadd product_189 product_190) (spadd product_191 product_192))) partial_sum_36)=partial_sum_37 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_37_value (v : ℕ→ℂ) :
    eval v partial_sum_37=eval v (spadd (spadd product_186 (spadd product_187 product_188)) (spadd (spadd product_189 product_190) (spadd product_191 product_192)))+eval v partial_sum_36 := by
  rw [←partial_sum_37_checked, eval_add]
compact_certificate_declaration theorem product_201_checked :
    mulShort n_c37_15 n_d0_16=product_201 := by
  decide +kernel
compact_certificate_declaration theorem product_201_value (v : ℕ→ℂ) :
    eval v product_201=eval v n_c37_15*eval v n_d0_16 := by
  rw [←product_201_checked, eval_mulShort]
compact_certificate_declaration theorem product_202_checked :
    mulShort n_c37_16 n_d0_17=product_202 := by
  decide +kernel
compact_certificate_declaration theorem product_202_value (v : ℕ→ℂ) :
    eval v product_202=eval v n_c37_16*eval v n_d0_17 := by
  rw [←product_202_checked, eval_mulShort]
compact_certificate_declaration theorem product_203_checked :
    mulShort n_c37_17 n_d0_18=product_203 := by
  decide +kernel
compact_certificate_declaration theorem product_203_value (v : ℕ→ℂ) :
    eval v product_203=eval v n_c37_17*eval v n_d0_18 := by
  rw [←product_203_checked, eval_mulShort]
compact_certificate_declaration theorem product_204_checked :
    mulShort n_c37_18 n_d0_19=product_204 := by
  decide +kernel
compact_certificate_declaration theorem product_204_value (v : ℕ→ℂ) :
    eval v product_204=eval v n_c37_18*eval v n_d0_19 := by
  rw [←product_204_checked, eval_mulShort]
compact_certificate_declaration theorem product_205_checked :
    mulShort n_c37_19 n_d0_20=product_205 := by
  decide +kernel
compact_certificate_declaration theorem product_205_value (v : ℕ→ℂ) :
    eval v product_205=eval v n_c37_19*eval v n_d0_20 := by
  rw [←product_205_checked, eval_mulShort]
compact_certificate_declaration theorem product_206_checked :
    mulShort n_c37_20 n_d0_21=product_206 := by
  decide +kernel
compact_certificate_declaration theorem product_206_value (v : ℕ→ℂ) :
    eval v product_206=eval v n_c37_20*eval v n_d0_21 := by
  rw [←product_206_checked, eval_mulShort]
compact_certificate_declaration theorem product_207_checked :
    mulShort n_c37_21 n_d0_22=product_207 := by
  decide +kernel
compact_certificate_declaration theorem product_207_value (v : ℕ→ℂ) :
    eval v product_207=eval v n_c37_21*eval v n_d0_22 := by
  rw [←product_207_checked, eval_mulShort]
compact_certificate_declaration theorem product_208_checked :
    mulShort n_c37_22 n_d0_23=product_208 := by
  decide +kernel
compact_certificate_declaration theorem product_208_value (v : ℕ→ℂ) :
    eval v product_208=eval v n_c37_22*eval v n_d0_23 := by
  rw [←product_208_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_38_checked :
    (spadd (spadd (spadd product_201 product_202) (spadd product_203 product_204)) (spadd (spadd product_205 product_206) (spadd product_207 product_208)))=partial_sum_38 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_38_value (v : ℕ→ℂ) :
    eval v partial_sum_38=eval v (spadd (spadd product_201 product_202) (spadd product_203 product_204))+eval v (spadd (spadd product_205 product_206) (spadd product_207 product_208)) := by
  rw [←partial_sum_38_checked, eval_add]
compact_certificate_declaration theorem product_209_checked :
    mulShort n_c37_23 n_d0_24=product_209 := by
  decide +kernel
compact_certificate_declaration theorem product_209_value (v : ℕ→ℂ) :
    eval v product_209=eval v n_c37_23*eval v n_d0_24 := by
  rw [←product_209_checked, eval_mulShort]
compact_certificate_declaration theorem product_210_checked :
    mulShort n_c37_24 n_d0_25=product_210 := by
  decide +kernel
compact_certificate_declaration theorem product_210_value (v : ℕ→ℂ) :
    eval v product_210=eval v n_c37_24*eval v n_d0_25 := by
  rw [←product_210_checked, eval_mulShort]

}
certificate_batch {
compact_certificate_declaration theorem product_211_checked :
    mulShort n_c37_25 n_d0_26=product_211 := by
  decide +kernel
compact_certificate_declaration theorem product_211_value (v : ℕ→ℂ) :
    eval v product_211=eval v n_c37_25*eval v n_d0_26 := by
  rw [←product_211_checked, eval_mulShort]
compact_certificate_declaration theorem product_212_checked :
    mulShort n_c37_26 n_d0_27=product_212 := by
  decide +kernel
compact_certificate_declaration theorem product_212_value (v : ℕ→ℂ) :
    eval v product_212=eval v n_c37_26*eval v n_d0_27 := by
  rw [←product_212_checked, eval_mulShort]
compact_certificate_declaration theorem product_213_checked :
    mulShort n_c37_27 n_d0_28=product_213 := by
  decide +kernel
compact_certificate_declaration theorem product_213_value (v : ℕ→ℂ) :
    eval v product_213=eval v n_c37_27*eval v n_d0_28 := by
  rw [←product_213_checked, eval_mulShort]
compact_certificate_declaration theorem product_214_checked :
    mulShort n_c37_28 n_d0_29=product_214 := by
  decide +kernel
compact_certificate_declaration theorem product_214_value (v : ℕ→ℂ) :
    eval v product_214=eval v n_c37_28*eval v n_d0_29 := by
  rw [←product_214_checked, eval_mulShort]
compact_certificate_declaration theorem product_215_checked :
    mulShort n_c37_29 n_d0_30=product_215 := by
  decide +kernel
compact_certificate_declaration theorem product_215_value (v : ℕ→ℂ) :
    eval v product_215=eval v n_c37_29*eval v n_d0_30 := by
  rw [←product_215_checked, eval_mulShort]
compact_certificate_declaration theorem product_216_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c37_30) n_d1_37=product_216 := by
  decide +kernel
compact_certificate_declaration theorem product_216_value (v : ℕ→ℂ) :
    eval v product_216=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c37_30)*eval v n_d1_37 := by
  rw [←product_216_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_39_checked :
    (spadd (spadd (spadd product_209 product_210) (spadd product_211 product_212)) (spadd (spadd product_213 product_214) (spadd product_215 product_216)))=partial_sum_39 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_39_value (v : ℕ→ℂ) :
    eval v partial_sum_39=eval v (spadd (spadd product_209 product_210) (spadd product_211 product_212))+eval v (spadd (spadd product_213 product_214) (spadd product_215 product_216)) := by
  rw [←partial_sum_39_checked, eval_add]
compact_certificate_declaration theorem partial_sum_40_checked :
    (spadd partial_sum_38 partial_sum_39)=partial_sum_40 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_40_value (v : ℕ→ℂ) :
    eval v partial_sum_40=eval v partial_sum_38+eval v partial_sum_39 := by
  rw [←partial_sum_40_checked, eval_add]
compact_certificate_declaration theorem partial_sum_41_checked :
    (spadd partial_sum_37 partial_sum_40)=partial_sum_41 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_41_value (v : ℕ→ℂ) :
    eval v partial_sum_41=eval v partial_sum_37+eval v partial_sum_40 := by
  rw [←partial_sum_41_checked, eval_add]
compact_certificate_declaration theorem checked_6 : checkZero e6=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_6 (y z w a b u : ℂ) :
    (certificate y z w a b u)[6]?=some 0 := by
  change some ((((((c37_0 y z w a b u)*(d0_0 y z w a b u)+((c37_1 y z w a b u)*(d0_1 y z w a b u)+(c37_2 y z w a b u)*(d0_2 y z w a b u)))+(((c37_3 y z w a b u)*(d0_3 y z w a b u)+(c37_4 y z w a b u)*(d0_4 y z w a b u))+((c37_5 y z w a b u)*(d0_5 y z w a b u)+(c37_6 y z w a b u)*(d0_6 y z w a b u))))+((((c37_7 y z w a b u)*(d0_7 y z w a b u)+(c37_8 y z w a b u)*(d0_8 y z w a b u))+((c37_9 y z w a b u)*(d0_9 y z w a b u)+(c37_10 y z w a b u)*(d0_10 y z w a b u)))+(((c37_11 y z w a b u)*(d0_12 y z w a b u)+(c37_12 y z w a b u)*(d0_13 y z w a b u))+((c37_13 y z w a b u)*(d0_14 y z w a b u)+(c37_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c37_15 y z w a b u)*(d0_16 y z w a b u)+(c37_16 y z w a b u)*(d0_17 y z w a b u))+((c37_17 y z w a b u)*(d0_18 y z w a b u)+(c37_18 y z w a b u)*(d0_19 y z w a b u)))+(((c37_19 y z w a b u)*(d0_20 y z w a b u)+(c37_20 y z w a b u)*(d0_21 y z w a b u))+((c37_21 y z w a b u)*(d0_22 y z w a b u)+(c37_22 y z w a b u)*(d0_23 y z w a b u))))+((((c37_23 y z w a b u)*(d0_24 y z w a b u)+(c37_24 y z w a b u)*(d0_25 y z w a b u))+((c37_25 y z w a b u)*(d0_26 y z w a b u)+(c37_26 y z w a b u)*(d0_27 y z w a b u)))+(((c37_27 y z w a b u)*(d0_28 y z w a b u)+(c37_28 y z w a b u)*(d0_29 y z w a b u))+((c37_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c37_30 y z w a b u)*(d1_37 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e6 checked_6
  simp only [e6, eval_add, eval_mul, eval_scale, eval_pow, product_186_value, product_187_value, product_188_value, product_189_value, product_190_value, product_191_value, product_192_value, product_193_value, product_194_value, product_195_value, product_196_value, product_197_value, product_198_value, product_199_value, product_200_value, partial_sum_36_value, partial_sum_37_value, product_201_value, product_202_value, product_203_value, product_204_value, product_205_value, product_206_value, product_207_value, product_208_value, partial_sum_38_value, product_209_value, product_210_value, product_211_value, product_212_value, product_213_value, product_214_value, product_215_value, product_216_value, partial_sum_39_value, partial_sum_40_value, partial_sum_41_value, n_c37_0_value y z w a b u, n_c37_1_value y z w a b u, n_c37_10_value y z w a b u, n_c37_11_value y z w a b u, n_c37_12_value y z w a b u, n_c37_13_value y z w a b u, n_c37_14_value y z w a b u, n_c37_15_value y z w a b u, n_c37_16_value y z w a b u, n_c37_17_value y z w a b u, n_c37_18_value y z w a b u, n_c37_19_value y z w a b u, n_c37_2_value y z w a b u, n_c37_20_value y z w a b u, n_c37_21_value y z w a b u, n_c37_22_value y z w a b u, n_c37_23_value y z w a b u, n_c37_24_value y z w a b u, n_c37_25_value y z w a b u, n_c37_26_value y z w a b u, n_c37_27_value y z w a b u, n_c37_28_value y z w a b u, n_c37_29_value y z w a b u, n_c37_3_value y z w a b u, n_c37_30_value y z w a b u, n_c37_4_value y z w a b u, n_c37_5_value y z w a b u, n_c37_6_value y z w a b u, n_c37_7_value y z w a b u, n_c37_8_value y z w a b u, n_c37_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_37_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_217_checked :
    mulShort n_c38_0 n_d0_0=product_217 := by
  decide +kernel
compact_certificate_declaration theorem product_217_value (v : ℕ→ℂ) :
    eval v product_217=eval v n_c38_0*eval v n_d0_0 := by
  rw [←product_217_checked, eval_mulShort]
compact_certificate_declaration theorem product_218_checked :
    mulShort n_c38_1 n_d0_1=product_218 := by
  decide +kernel
compact_certificate_declaration theorem product_218_value (v : ℕ→ℂ) :
    eval v product_218=eval v n_c38_1*eval v n_d0_1 := by
  rw [←product_218_checked, eval_mulShort]
compact_certificate_declaration theorem product_219_checked :
    mulShort n_c38_2 n_d0_2=product_219 := by
  decide +kernel
compact_certificate_declaration theorem product_219_value (v : ℕ→ℂ) :
    eval v product_219=eval v n_c38_2*eval v n_d0_2 := by
  rw [←product_219_checked, eval_mulShort]
compact_certificate_declaration theorem product_220_checked :
    mulShort n_c38_3 n_d0_3=product_220 := by
  decide +kernel
compact_certificate_declaration theorem product_220_value (v : ℕ→ℂ) :
    eval v product_220=eval v n_c38_3*eval v n_d0_3 := by
  rw [←product_220_checked, eval_mulShort]
compact_certificate_declaration theorem product_221_checked :
    mulShort n_c38_4 n_d0_4=product_221 := by
  decide +kernel
compact_certificate_declaration theorem product_221_value (v : ℕ→ℂ) :
    eval v product_221=eval v n_c38_4*eval v n_d0_4 := by
  rw [←product_221_checked, eval_mulShort]
compact_certificate_declaration theorem product_222_checked :
    mulShort n_c38_5 n_d0_5=product_222 := by
  decide +kernel
compact_certificate_declaration theorem product_222_value (v : ℕ→ℂ) :
    eval v product_222=eval v n_c38_5*eval v n_d0_5 := by
  rw [←product_222_checked, eval_mulShort]
compact_certificate_declaration theorem product_223_checked :
    mulShort n_c38_6 n_d0_6=product_223 := by
  decide +kernel
compact_certificate_declaration theorem product_223_value (v : ℕ→ℂ) :
    eval v product_223=eval v n_c38_6*eval v n_d0_6 := by
  rw [←product_223_checked, eval_mulShort]
compact_certificate_declaration theorem product_224_checked :
    mulShort n_c38_7 n_d0_7=product_224 := by
  decide +kernel
compact_certificate_declaration theorem product_224_value (v : ℕ→ℂ) :
    eval v product_224=eval v n_c38_7*eval v n_d0_7 := by
  rw [←product_224_checked, eval_mulShort]
compact_certificate_declaration theorem product_225_checked :
    mulShort n_c38_8 n_d0_8=product_225 := by
  decide +kernel
compact_certificate_declaration theorem product_225_value (v : ℕ→ℂ) :
    eval v product_225=eval v n_c38_8*eval v n_d0_8 := by
  rw [←product_225_checked, eval_mulShort]
compact_certificate_declaration theorem product_226_checked :
    mulShort n_c38_9 n_d0_9=product_226 := by
  decide +kernel
compact_certificate_declaration theorem product_226_value (v : ℕ→ℂ) :
    eval v product_226=eval v n_c38_9*eval v n_d0_9 := by
  rw [←product_226_checked, eval_mulShort]
compact_certificate_declaration theorem product_227_checked :
    mulShort n_c38_10 n_d0_10=product_227 := by
  decide +kernel
compact_certificate_declaration theorem product_227_value (v : ℕ→ℂ) :
    eval v product_227=eval v n_c38_10*eval v n_d0_10 := by
  rw [←product_227_checked, eval_mulShort]
compact_certificate_declaration theorem product_228_checked :
    mulShort n_c38_11 n_d0_12=product_228 := by
  decide +kernel
compact_certificate_declaration theorem product_228_value (v : ℕ→ℂ) :
    eval v product_228=eval v n_c38_11*eval v n_d0_12 := by
  rw [←product_228_checked, eval_mulShort]
compact_certificate_declaration theorem product_229_checked :
    mulShort n_c38_12 n_d0_13=product_229 := by
  decide +kernel
compact_certificate_declaration theorem product_229_value (v : ℕ→ℂ) :
    eval v product_229=eval v n_c38_12*eval v n_d0_13 := by
  rw [←product_229_checked, eval_mulShort]
compact_certificate_declaration theorem product_230_checked :
    mulShort n_c38_13 n_d0_14=product_230 := by
  decide +kernel
compact_certificate_declaration theorem product_230_value (v : ℕ→ℂ) :
    eval v product_230=eval v n_c38_13*eval v n_d0_14 := by
  rw [←product_230_checked, eval_mulShort]
compact_certificate_declaration theorem product_231_checked :
    mulShort n_c38_14 n_d0_15=product_231 := by
  decide +kernel
compact_certificate_declaration theorem product_231_value (v : ℕ→ℂ) :
    eval v product_231=eval v n_c38_14*eval v n_d0_15 := by
  rw [←product_231_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_42_checked :
    (spadd (spadd (spadd product_224 product_225) (spadd product_226 product_227)) (spadd (spadd product_228 product_229) (spadd product_230 product_231)))=partial_sum_42 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_42_value (v : ℕ→ℂ) :
    eval v partial_sum_42=eval v (spadd (spadd product_224 product_225) (spadd product_226 product_227))+eval v (spadd (spadd product_228 product_229) (spadd product_230 product_231)) := by
  rw [←partial_sum_42_checked, eval_add]
compact_certificate_declaration theorem partial_sum_43_checked :
    (spadd (spadd (spadd product_217 (spadd product_218 product_219)) (spadd (spadd product_220 product_221) (spadd product_222 product_223))) partial_sum_42)=partial_sum_43 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_43_value (v : ℕ→ℂ) :
    eval v partial_sum_43=eval v (spadd (spadd product_217 (spadd product_218 product_219)) (spadd (spadd product_220 product_221) (spadd product_222 product_223)))+eval v partial_sum_42 := by
  rw [←partial_sum_43_checked, eval_add]
compact_certificate_declaration theorem product_232_checked :
    mulShort n_c38_15 n_d0_16=product_232 := by
  decide +kernel
compact_certificate_declaration theorem product_232_value (v : ℕ→ℂ) :
    eval v product_232=eval v n_c38_15*eval v n_d0_16 := by
  rw [←product_232_checked, eval_mulShort]
compact_certificate_declaration theorem product_233_checked :
    mulShort n_c38_16 n_d0_17=product_233 := by
  decide +kernel
compact_certificate_declaration theorem product_233_value (v : ℕ→ℂ) :
    eval v product_233=eval v n_c38_16*eval v n_d0_17 := by
  rw [←product_233_checked, eval_mulShort]
compact_certificate_declaration theorem product_234_checked :
    mulShort n_c38_17 n_d0_18=product_234 := by
  decide +kernel
compact_certificate_declaration theorem product_234_value (v : ℕ→ℂ) :
    eval v product_234=eval v n_c38_17*eval v n_d0_18 := by
  rw [←product_234_checked, eval_mulShort]
compact_certificate_declaration theorem product_235_checked :
    mulShort n_c38_18 n_d0_19=product_235 := by
  decide +kernel
compact_certificate_declaration theorem product_235_value (v : ℕ→ℂ) :
    eval v product_235=eval v n_c38_18*eval v n_d0_19 := by
  rw [←product_235_checked, eval_mulShort]
compact_certificate_declaration theorem product_236_checked :
    mulShort n_c38_19 n_d0_20=product_236 := by
  decide +kernel
compact_certificate_declaration theorem product_236_value (v : ℕ→ℂ) :
    eval v product_236=eval v n_c38_19*eval v n_d0_20 := by
  rw [←product_236_checked, eval_mulShort]
compact_certificate_declaration theorem product_237_checked :
    mulShort n_c38_20 n_d0_21=product_237 := by
  decide +kernel
compact_certificate_declaration theorem product_237_value (v : ℕ→ℂ) :
    eval v product_237=eval v n_c38_20*eval v n_d0_21 := by
  rw [←product_237_checked, eval_mulShort]
compact_certificate_declaration theorem product_238_checked :
    mulShort n_c38_21 n_d0_22=product_238 := by
  decide +kernel
compact_certificate_declaration theorem product_238_value (v : ℕ→ℂ) :
    eval v product_238=eval v n_c38_21*eval v n_d0_22 := by
  rw [←product_238_checked, eval_mulShort]
compact_certificate_declaration theorem product_239_checked :
    mulShort n_c38_22 n_d0_23=product_239 := by
  decide +kernel
compact_certificate_declaration theorem product_239_value (v : ℕ→ℂ) :
    eval v product_239=eval v n_c38_22*eval v n_d0_23 := by
  rw [←product_239_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_44_checked :
    (spadd (spadd (spadd product_232 product_233) (spadd product_234 product_235)) (spadd (spadd product_236 product_237) (spadd product_238 product_239)))=partial_sum_44 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_44_value (v : ℕ→ℂ) :
    eval v partial_sum_44=eval v (spadd (spadd product_232 product_233) (spadd product_234 product_235))+eval v (spadd (spadd product_236 product_237) (spadd product_238 product_239)) := by
  rw [←partial_sum_44_checked, eval_add]
compact_certificate_declaration theorem product_240_checked :
    mulShort n_c38_23 n_d0_24=product_240 := by
  decide +kernel
compact_certificate_declaration theorem product_240_value (v : ℕ→ℂ) :
    eval v product_240=eval v n_c38_23*eval v n_d0_24 := by
  rw [←product_240_checked, eval_mulShort]
compact_certificate_declaration theorem product_241_checked :
    mulShort n_c38_24 n_d0_25=product_241 := by
  decide +kernel
compact_certificate_declaration theorem product_241_value (v : ℕ→ℂ) :
    eval v product_241=eval v n_c38_24*eval v n_d0_25 := by
  rw [←product_241_checked, eval_mulShort]
compact_certificate_declaration theorem product_242_checked :
    mulShort n_c38_25 n_d0_26=product_242 := by
  decide +kernel
compact_certificate_declaration theorem product_242_value (v : ℕ→ℂ) :
    eval v product_242=eval v n_c38_25*eval v n_d0_26 := by
  rw [←product_242_checked, eval_mulShort]
compact_certificate_declaration theorem product_243_checked :
    mulShort n_c38_26 n_d0_27=product_243 := by
  decide +kernel
compact_certificate_declaration theorem product_243_value (v : ℕ→ℂ) :
    eval v product_243=eval v n_c38_26*eval v n_d0_27 := by
  rw [←product_243_checked, eval_mulShort]
compact_certificate_declaration theorem product_244_checked :
    mulShort n_c38_27 n_d0_28=product_244 := by
  decide +kernel
compact_certificate_declaration theorem product_244_value (v : ℕ→ℂ) :
    eval v product_244=eval v n_c38_27*eval v n_d0_28 := by
  rw [←product_244_checked, eval_mulShort]
compact_certificate_declaration theorem product_245_checked :
    mulShort n_c38_28 n_d0_29=product_245 := by
  decide +kernel
compact_certificate_declaration theorem product_245_value (v : ℕ→ℂ) :
    eval v product_245=eval v n_c38_28*eval v n_d0_29 := by
  rw [←product_245_checked, eval_mulShort]
compact_certificate_declaration theorem product_246_checked :
    mulShort n_c38_29 n_d0_30=product_246 := by
  decide +kernel
compact_certificate_declaration theorem product_246_value (v : ℕ→ℂ) :
    eval v product_246=eval v n_c38_29*eval v n_d0_30 := by
  rw [←product_246_checked, eval_mulShort]
compact_certificate_declaration theorem product_247_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c38_30) n_d1_38=product_247 := by
  decide +kernel
compact_certificate_declaration theorem product_247_value (v : ℕ→ℂ) :
    eval v product_247=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c38_30)*eval v n_d1_38 := by
  rw [←product_247_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_45_checked :
    (spadd (spadd (spadd product_240 product_241) (spadd product_242 product_243)) (spadd (spadd product_244 product_245) (spadd product_246 product_247)))=partial_sum_45 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_45_value (v : ℕ→ℂ) :
    eval v partial_sum_45=eval v (spadd (spadd product_240 product_241) (spadd product_242 product_243))+eval v (spadd (spadd product_244 product_245) (spadd product_246 product_247)) := by
  rw [←partial_sum_45_checked, eval_add]
compact_certificate_declaration theorem partial_sum_46_checked :
    (spadd partial_sum_44 partial_sum_45)=partial_sum_46 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_46_value (v : ℕ→ℂ) :
    eval v partial_sum_46=eval v partial_sum_44+eval v partial_sum_45 := by
  rw [←partial_sum_46_checked, eval_add]
compact_certificate_declaration theorem partial_sum_47_checked :
    (spadd partial_sum_43 partial_sum_46)=partial_sum_47 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_47_value (v : ℕ→ℂ) :
    eval v partial_sum_47=eval v partial_sum_43+eval v partial_sum_46 := by
  rw [←partial_sum_47_checked, eval_add]
compact_certificate_declaration theorem checked_7 : checkZero e7=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_7 (y z w a b u : ℂ) :
    (certificate y z w a b u)[7]?=some 0 := by
  change some ((((((c38_0 y z w a b u)*(d0_0 y z w a b u)+((c38_1 y z w a b u)*(d0_1 y z w a b u)+(c38_2 y z w a b u)*(d0_2 y z w a b u)))+(((c38_3 y z w a b u)*(d0_3 y z w a b u)+(c38_4 y z w a b u)*(d0_4 y z w a b u))+((c38_5 y z w a b u)*(d0_5 y z w a b u)+(c38_6 y z w a b u)*(d0_6 y z w a b u))))+((((c38_7 y z w a b u)*(d0_7 y z w a b u)+(c38_8 y z w a b u)*(d0_8 y z w a b u))+((c38_9 y z w a b u)*(d0_9 y z w a b u)+(c38_10 y z w a b u)*(d0_10 y z w a b u)))+(((c38_11 y z w a b u)*(d0_12 y z w a b u)+(c38_12 y z w a b u)*(d0_13 y z w a b u))+((c38_13 y z w a b u)*(d0_14 y z w a b u)+(c38_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c38_15 y z w a b u)*(d0_16 y z w a b u)+(c38_16 y z w a b u)*(d0_17 y z w a b u))+((c38_17 y z w a b u)*(d0_18 y z w a b u)+(c38_18 y z w a b u)*(d0_19 y z w a b u)))+(((c38_19 y z w a b u)*(d0_20 y z w a b u)+(c38_20 y z w a b u)*(d0_21 y z w a b u))+((c38_21 y z w a b u)*(d0_22 y z w a b u)+(c38_22 y z w a b u)*(d0_23 y z w a b u))))+((((c38_23 y z w a b u)*(d0_24 y z w a b u)+(c38_24 y z w a b u)*(d0_25 y z w a b u))+((c38_25 y z w a b u)*(d0_26 y z w a b u)+(c38_26 y z w a b u)*(d0_27 y z w a b u)))+(((c38_27 y z w a b u)*(d0_28 y z w a b u)+(c38_28 y z w a b u)*(d0_29 y z w a b u))+((c38_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c38_30 y z w a b u)*(d1_38 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e7 checked_7
  simp only [e7, eval_add, eval_mul, eval_scale, eval_pow, product_217_value, product_218_value, product_219_value, product_220_value, product_221_value, product_222_value, product_223_value, product_224_value, product_225_value, product_226_value, product_227_value, product_228_value, product_229_value, product_230_value, product_231_value, partial_sum_42_value, partial_sum_43_value, product_232_value, product_233_value, product_234_value, product_235_value, product_236_value, product_237_value, product_238_value, product_239_value, partial_sum_44_value, product_240_value, product_241_value, product_242_value, product_243_value, product_244_value, product_245_value, product_246_value, product_247_value, partial_sum_45_value, partial_sum_46_value, partial_sum_47_value, n_c38_0_value y z w a b u, n_c38_1_value y z w a b u, n_c38_10_value y z w a b u, n_c38_11_value y z w a b u, n_c38_12_value y z w a b u, n_c38_13_value y z w a b u, n_c38_14_value y z w a b u, n_c38_15_value y z w a b u, n_c38_16_value y z w a b u, n_c38_17_value y z w a b u, n_c38_18_value y z w a b u, n_c38_19_value y z w a b u, n_c38_2_value y z w a b u, n_c38_20_value y z w a b u, n_c38_21_value y z w a b u, n_c38_22_value y z w a b u, n_c38_23_value y z w a b u, n_c38_24_value y z w a b u, n_c38_25_value y z w a b u, n_c38_26_value y z w a b u, n_c38_27_value y z w a b u, n_c38_28_value y z w a b u, n_c38_29_value y z w a b u, n_c38_3_value y z w a b u, n_c38_30_value y z w a b u, n_c38_4_value y z w a b u, n_c38_5_value y z w a b u, n_c38_6_value y z w a b u, n_c38_7_value y z w a b u, n_c38_8_value y z w a b u, n_c38_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_38_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_248_checked :
    mulShort n_c39_0 n_d0_0=product_248 := by
  decide +kernel
compact_certificate_declaration theorem product_248_value (v : ℕ→ℂ) :
    eval v product_248=eval v n_c39_0*eval v n_d0_0 := by
  rw [←product_248_checked, eval_mulShort]
compact_certificate_declaration theorem product_249_checked :
    mulShort n_c39_1 n_d0_1=product_249 := by
  decide +kernel
compact_certificate_declaration theorem product_249_value (v : ℕ→ℂ) :
    eval v product_249=eval v n_c39_1*eval v n_d0_1 := by
  rw [←product_249_checked, eval_mulShort]
compact_certificate_declaration theorem product_250_checked :
    mulShort n_c39_2 n_d0_2=product_250 := by
  decide +kernel
compact_certificate_declaration theorem product_250_value (v : ℕ→ℂ) :
    eval v product_250=eval v n_c39_2*eval v n_d0_2 := by
  rw [←product_250_checked, eval_mulShort]
compact_certificate_declaration theorem product_251_checked :
    mulShort n_c39_3 n_d0_3=product_251 := by
  decide +kernel
compact_certificate_declaration theorem product_251_value (v : ℕ→ℂ) :
    eval v product_251=eval v n_c39_3*eval v n_d0_3 := by
  rw [←product_251_checked, eval_mulShort]
compact_certificate_declaration theorem product_252_checked :
    mulShort n_c39_4 n_d0_4=product_252 := by
  decide +kernel
compact_certificate_declaration theorem product_252_value (v : ℕ→ℂ) :
    eval v product_252=eval v n_c39_4*eval v n_d0_4 := by
  rw [←product_252_checked, eval_mulShort]
compact_certificate_declaration theorem product_253_checked :
    mulShort n_c39_5 n_d0_5=product_253 := by
  decide +kernel
compact_certificate_declaration theorem product_253_value (v : ℕ→ℂ) :
    eval v product_253=eval v n_c39_5*eval v n_d0_5 := by
  rw [←product_253_checked, eval_mulShort]
compact_certificate_declaration theorem product_254_checked :
    mulShort n_c39_6 n_d0_6=product_254 := by
  decide +kernel
compact_certificate_declaration theorem product_254_value (v : ℕ→ℂ) :
    eval v product_254=eval v n_c39_6*eval v n_d0_6 := by
  rw [←product_254_checked, eval_mulShort]
compact_certificate_declaration theorem product_255_checked :
    mulShort n_c39_7 n_d0_7=product_255 := by
  decide +kernel
compact_certificate_declaration theorem product_255_value (v : ℕ→ℂ) :
    eval v product_255=eval v n_c39_7*eval v n_d0_7 := by
  rw [←product_255_checked, eval_mulShort]
compact_certificate_declaration theorem product_256_checked :
    mulShort n_c39_8 n_d0_8=product_256 := by
  decide +kernel
compact_certificate_declaration theorem product_256_value (v : ℕ→ℂ) :
    eval v product_256=eval v n_c39_8*eval v n_d0_8 := by
  rw [←product_256_checked, eval_mulShort]
compact_certificate_declaration theorem product_257_checked :
    mulShort n_c39_9 n_d0_9=product_257 := by
  decide +kernel
compact_certificate_declaration theorem product_257_value (v : ℕ→ℂ) :
    eval v product_257=eval v n_c39_9*eval v n_d0_9 := by
  rw [←product_257_checked, eval_mulShort]
compact_certificate_declaration theorem product_258_checked :
    mulShort n_c39_10 n_d0_10=product_258 := by
  decide +kernel
compact_certificate_declaration theorem product_258_value (v : ℕ→ℂ) :
    eval v product_258=eval v n_c39_10*eval v n_d0_10 := by
  rw [←product_258_checked, eval_mulShort]
compact_certificate_declaration theorem product_259_checked :
    mulShort n_c39_11 n_d0_12=product_259 := by
  decide +kernel
compact_certificate_declaration theorem product_259_value (v : ℕ→ℂ) :
    eval v product_259=eval v n_c39_11*eval v n_d0_12 := by
  rw [←product_259_checked, eval_mulShort]
compact_certificate_declaration theorem product_260_checked :
    mulShort n_c39_12 n_d0_13=product_260 := by
  decide +kernel
compact_certificate_declaration theorem product_260_value (v : ℕ→ℂ) :
    eval v product_260=eval v n_c39_12*eval v n_d0_13 := by
  rw [←product_260_checked, eval_mulShort]
compact_certificate_declaration theorem product_261_checked :
    mulShort n_c39_13 n_d0_14=product_261 := by
  decide +kernel
compact_certificate_declaration theorem product_261_value (v : ℕ→ℂ) :
    eval v product_261=eval v n_c39_13*eval v n_d0_14 := by
  rw [←product_261_checked, eval_mulShort]
compact_certificate_declaration theorem product_262_checked :
    mulShort n_c39_14 n_d0_15=product_262 := by
  decide +kernel
compact_certificate_declaration theorem product_262_value (v : ℕ→ℂ) :
    eval v product_262=eval v n_c39_14*eval v n_d0_15 := by
  rw [←product_262_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_48_checked :
    (spadd (spadd (spadd product_255 product_256) (spadd product_257 product_258)) (spadd (spadd product_259 product_260) (spadd product_261 product_262)))=partial_sum_48 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_48_value (v : ℕ→ℂ) :
    eval v partial_sum_48=eval v (spadd (spadd product_255 product_256) (spadd product_257 product_258))+eval v (spadd (spadd product_259 product_260) (spadd product_261 product_262)) := by
  rw [←partial_sum_48_checked, eval_add]
compact_certificate_declaration theorem partial_sum_49_checked :
    (spadd (spadd (spadd product_248 (spadd product_249 product_250)) (spadd (spadd product_251 product_252) (spadd product_253 product_254))) partial_sum_48)=partial_sum_49 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_49_value (v : ℕ→ℂ) :
    eval v partial_sum_49=eval v (spadd (spadd product_248 (spadd product_249 product_250)) (spadd (spadd product_251 product_252) (spadd product_253 product_254)))+eval v partial_sum_48 := by
  rw [←partial_sum_49_checked, eval_add]
compact_certificate_declaration theorem product_263_checked :
    mulShort n_c39_15 n_d0_16=product_263 := by
  decide +kernel
compact_certificate_declaration theorem product_263_value (v : ℕ→ℂ) :
    eval v product_263=eval v n_c39_15*eval v n_d0_16 := by
  rw [←product_263_checked, eval_mulShort]
compact_certificate_declaration theorem product_264_checked :
    mulShort n_c39_16 n_d0_17=product_264 := by
  decide +kernel
compact_certificate_declaration theorem product_264_value (v : ℕ→ℂ) :
    eval v product_264=eval v n_c39_16*eval v n_d0_17 := by
  rw [←product_264_checked, eval_mulShort]
compact_certificate_declaration theorem product_265_checked :
    mulShort n_c39_17 n_d0_18=product_265 := by
  decide +kernel
compact_certificate_declaration theorem product_265_value (v : ℕ→ℂ) :
    eval v product_265=eval v n_c39_17*eval v n_d0_18 := by
  rw [←product_265_checked, eval_mulShort]
compact_certificate_declaration theorem product_266_checked :
    mulShort n_c39_18 n_d0_19=product_266 := by
  decide +kernel
compact_certificate_declaration theorem product_266_value (v : ℕ→ℂ) :
    eval v product_266=eval v n_c39_18*eval v n_d0_19 := by
  rw [←product_266_checked, eval_mulShort]
compact_certificate_declaration theorem product_267_checked :
    mulShort n_c39_19 n_d0_20=product_267 := by
  decide +kernel
compact_certificate_declaration theorem product_267_value (v : ℕ→ℂ) :
    eval v product_267=eval v n_c39_19*eval v n_d0_20 := by
  rw [←product_267_checked, eval_mulShort]
compact_certificate_declaration theorem product_268_checked :
    mulShort n_c39_20 n_d0_21=product_268 := by
  decide +kernel
compact_certificate_declaration theorem product_268_value (v : ℕ→ℂ) :
    eval v product_268=eval v n_c39_20*eval v n_d0_21 := by
  rw [←product_268_checked, eval_mulShort]
compact_certificate_declaration theorem product_269_checked :
    mulShort n_c39_21 n_d0_22=product_269 := by
  decide +kernel
compact_certificate_declaration theorem product_269_value (v : ℕ→ℂ) :
    eval v product_269=eval v n_c39_21*eval v n_d0_22 := by
  rw [←product_269_checked, eval_mulShort]
compact_certificate_declaration theorem product_270_checked :
    mulShort n_c39_22 n_d0_23=product_270 := by
  decide +kernel
compact_certificate_declaration theorem product_270_value (v : ℕ→ℂ) :
    eval v product_270=eval v n_c39_22*eval v n_d0_23 := by
  rw [←product_270_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_50_checked :
    (spadd (spadd (spadd product_263 product_264) (spadd product_265 product_266)) (spadd (spadd product_267 product_268) (spadd product_269 product_270)))=partial_sum_50 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_50_value (v : ℕ→ℂ) :
    eval v partial_sum_50=eval v (spadd (spadd product_263 product_264) (spadd product_265 product_266))+eval v (spadd (spadd product_267 product_268) (spadd product_269 product_270)) := by
  rw [←partial_sum_50_checked, eval_add]
compact_certificate_declaration theorem product_271_checked :
    mulShort n_c39_23 n_d0_24=product_271 := by
  decide +kernel
compact_certificate_declaration theorem product_271_value (v : ℕ→ℂ) :
    eval v product_271=eval v n_c39_23*eval v n_d0_24 := by
  rw [←product_271_checked, eval_mulShort]
compact_certificate_declaration theorem product_272_checked :
    mulShort n_c39_24 n_d0_25=product_272 := by
  decide +kernel
compact_certificate_declaration theorem product_272_value (v : ℕ→ℂ) :
    eval v product_272=eval v n_c39_24*eval v n_d0_25 := by
  rw [←product_272_checked, eval_mulShort]
compact_certificate_declaration theorem product_273_checked :
    mulShort n_c39_25 n_d0_26=product_273 := by
  decide +kernel
compact_certificate_declaration theorem product_273_value (v : ℕ→ℂ) :
    eval v product_273=eval v n_c39_25*eval v n_d0_26 := by
  rw [←product_273_checked, eval_mulShort]
compact_certificate_declaration theorem product_274_checked :
    mulShort n_c39_26 n_d0_27=product_274 := by
  decide +kernel
compact_certificate_declaration theorem product_274_value (v : ℕ→ℂ) :
    eval v product_274=eval v n_c39_26*eval v n_d0_27 := by
  rw [←product_274_checked, eval_mulShort]
compact_certificate_declaration theorem product_275_checked :
    mulShort n_c39_27 n_d0_28=product_275 := by
  decide +kernel
compact_certificate_declaration theorem product_275_value (v : ℕ→ℂ) :
    eval v product_275=eval v n_c39_27*eval v n_d0_28 := by
  rw [←product_275_checked, eval_mulShort]
compact_certificate_declaration theorem product_276_checked :
    mulShort n_c39_28 n_d0_29=product_276 := by
  decide +kernel
compact_certificate_declaration theorem product_276_value (v : ℕ→ℂ) :
    eval v product_276=eval v n_c39_28*eval v n_d0_29 := by
  rw [←product_276_checked, eval_mulShort]
compact_certificate_declaration theorem product_277_checked :
    mulShort n_c39_29 n_d0_30=product_277 := by
  decide +kernel
compact_certificate_declaration theorem product_277_value (v : ℕ→ℂ) :
    eval v product_277=eval v n_c39_29*eval v n_d0_30 := by
  rw [←product_277_checked, eval_mulShort]
compact_certificate_declaration theorem product_278_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c39_30) n_d1_39=product_278 := by
  decide +kernel
compact_certificate_declaration theorem product_278_value (v : ℕ→ℂ) :
    eval v product_278=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c39_30)*eval v n_d1_39 := by
  rw [←product_278_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_51_checked :
    (spadd (spadd (spadd product_271 product_272) (spadd product_273 product_274)) (spadd (spadd product_275 product_276) (spadd product_277 product_278)))=partial_sum_51 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_51_value (v : ℕ→ℂ) :
    eval v partial_sum_51=eval v (spadd (spadd product_271 product_272) (spadd product_273 product_274))+eval v (spadd (spadd product_275 product_276) (spadd product_277 product_278)) := by
  rw [←partial_sum_51_checked, eval_add]
compact_certificate_declaration theorem partial_sum_52_checked :
    (spadd partial_sum_50 partial_sum_51)=partial_sum_52 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_52_value (v : ℕ→ℂ) :
    eval v partial_sum_52=eval v partial_sum_50+eval v partial_sum_51 := by
  rw [←partial_sum_52_checked, eval_add]
compact_certificate_declaration theorem partial_sum_53_checked :
    (spadd partial_sum_49 partial_sum_52)=partial_sum_53 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_53_value (v : ℕ→ℂ) :
    eval v partial_sum_53=eval v partial_sum_49+eval v partial_sum_52 := by
  rw [←partial_sum_53_checked, eval_add]

compact_certificate_declaration theorem checked_8 : checkZero e8=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_8 (y z w a b u : ℂ) :
    (certificate y z w a b u)[8]?=some 0 := by
  change some ((((((c39_0 y z w a b u)*(d0_0 y z w a b u)+((c39_1 y z w a b u)*(d0_1 y z w a b u)+(c39_2 y z w a b u)*(d0_2 y z w a b u)))+(((c39_3 y z w a b u)*(d0_3 y z w a b u)+(c39_4 y z w a b u)*(d0_4 y z w a b u))+((c39_5 y z w a b u)*(d0_5 y z w a b u)+(c39_6 y z w a b u)*(d0_6 y z w a b u))))+((((c39_7 y z w a b u)*(d0_7 y z w a b u)+(c39_8 y z w a b u)*(d0_8 y z w a b u))+((c39_9 y z w a b u)*(d0_9 y z w a b u)+(c39_10 y z w a b u)*(d0_10 y z w a b u)))+(((c39_11 y z w a b u)*(d0_12 y z w a b u)+(c39_12 y z w a b u)*(d0_13 y z w a b u))+((c39_13 y z w a b u)*(d0_14 y z w a b u)+(c39_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c39_15 y z w a b u)*(d0_16 y z w a b u)+(c39_16 y z w a b u)*(d0_17 y z w a b u))+((c39_17 y z w a b u)*(d0_18 y z w a b u)+(c39_18 y z w a b u)*(d0_19 y z w a b u)))+(((c39_19 y z w a b u)*(d0_20 y z w a b u)+(c39_20 y z w a b u)*(d0_21 y z w a b u))+((c39_21 y z w a b u)*(d0_22 y z w a b u)+(c39_22 y z w a b u)*(d0_23 y z w a b u))))+((((c39_23 y z w a b u)*(d0_24 y z w a b u)+(c39_24 y z w a b u)*(d0_25 y z w a b u))+((c39_25 y z w a b u)*(d0_26 y z w a b u)+(c39_26 y z w a b u)*(d0_27 y z w a b u)))+(((c39_27 y z w a b u)*(d0_28 y z w a b u)+(c39_28 y z w a b u)*(d0_29 y z w a b u))+((c39_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c39_30 y z w a b u)*(d1_39 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e8 checked_8
  simp only [e8, eval_add, eval_mul, eval_scale, eval_pow, product_248_value, product_249_value, product_250_value, product_251_value, product_252_value, product_253_value, product_254_value, product_255_value, product_256_value, product_257_value, product_258_value, product_259_value, product_260_value, product_261_value, product_262_value, partial_sum_48_value, partial_sum_49_value, product_263_value, product_264_value, product_265_value, product_266_value, product_267_value, product_268_value, product_269_value, product_270_value, partial_sum_50_value, product_271_value, product_272_value, product_273_value, product_274_value, product_275_value, product_276_value, product_277_value, product_278_value, partial_sum_51_value, partial_sum_52_value, partial_sum_53_value, n_c39_0_value y z w a b u, n_c39_1_value y z w a b u, n_c39_10_value y z w a b u, n_c39_11_value y z w a b u, n_c39_12_value y z w a b u, n_c39_13_value y z w a b u, n_c39_14_value y z w a b u, n_c39_15_value y z w a b u, n_c39_16_value y z w a b u, n_c39_17_value y z w a b u, n_c39_18_value y z w a b u, n_c39_19_value y z w a b u, n_c39_2_value y z w a b u, n_c39_20_value y z w a b u, n_c39_21_value y z w a b u, n_c39_22_value y z w a b u, n_c39_23_value y z w a b u, n_c39_24_value y z w a b u, n_c39_25_value y z w a b u, n_c39_26_value y z w a b u, n_c39_27_value y z w a b u, n_c39_28_value y z w a b u, n_c39_29_value y z w a b u, n_c39_3_value y z w a b u, n_c39_30_value y z w a b u, n_c39_4_value y z w a b u, n_c39_5_value y z w a b u, n_c39_6_value y z w a b u, n_c39_7_value y z w a b u, n_c39_8_value y z w a b u, n_c39_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_39_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_279_checked :
    mulShort n_c40_0 n_d0_0=product_279 := by
  decide +kernel
compact_certificate_declaration theorem product_279_value (v : ℕ→ℂ) :
    eval v product_279=eval v n_c40_0*eval v n_d0_0 := by
  rw [←product_279_checked, eval_mulShort]
compact_certificate_declaration theorem product_280_checked :
    mulShort n_c40_1 n_d0_1=product_280 := by
  decide +kernel
compact_certificate_declaration theorem product_280_value (v : ℕ→ℂ) :
    eval v product_280=eval v n_c40_1*eval v n_d0_1 := by
  rw [←product_280_checked, eval_mulShort]
compact_certificate_declaration theorem product_281_checked :
    mulShort n_c40_2 n_d0_2=product_281 := by
  decide +kernel
compact_certificate_declaration theorem product_281_value (v : ℕ→ℂ) :
    eval v product_281=eval v n_c40_2*eval v n_d0_2 := by
  rw [←product_281_checked, eval_mulShort]
compact_certificate_declaration theorem product_282_checked :
    mulShort n_c40_3 n_d0_3=product_282 := by
  decide +kernel
compact_certificate_declaration theorem product_282_value (v : ℕ→ℂ) :
    eval v product_282=eval v n_c40_3*eval v n_d0_3 := by
  rw [←product_282_checked, eval_mulShort]
compact_certificate_declaration theorem product_283_checked :
    mulShort n_c40_4 n_d0_4=product_283 := by
  decide +kernel
compact_certificate_declaration theorem product_283_value (v : ℕ→ℂ) :
    eval v product_283=eval v n_c40_4*eval v n_d0_4 := by
  rw [←product_283_checked, eval_mulShort]
compact_certificate_declaration theorem product_284_checked :
    mulShort n_c40_5 n_d0_5=product_284 := by
  decide +kernel
compact_certificate_declaration theorem product_284_value (v : ℕ→ℂ) :
    eval v product_284=eval v n_c40_5*eval v n_d0_5 := by
  rw [←product_284_checked, eval_mulShort]
compact_certificate_declaration theorem product_285_checked :
    mulShort n_c40_6 n_d0_6=product_285 := by
  decide +kernel
compact_certificate_declaration theorem product_285_value (v : ℕ→ℂ) :
    eval v product_285=eval v n_c40_6*eval v n_d0_6 := by
  rw [←product_285_checked, eval_mulShort]
compact_certificate_declaration theorem product_286_checked :
    mulShort n_c40_7 n_d0_7=product_286 := by
  decide +kernel
compact_certificate_declaration theorem product_286_value (v : ℕ→ℂ) :
    eval v product_286=eval v n_c40_7*eval v n_d0_7 := by
  rw [←product_286_checked, eval_mulShort]
compact_certificate_declaration theorem product_287_checked :
    mulShort n_c40_8 n_d0_8=product_287 := by
  decide +kernel
compact_certificate_declaration theorem product_287_value (v : ℕ→ℂ) :
    eval v product_287=eval v n_c40_8*eval v n_d0_8 := by
  rw [←product_287_checked, eval_mulShort]
compact_certificate_declaration theorem product_288_checked :
    mulShort n_c40_9 n_d0_9=product_288 := by
  decide +kernel
compact_certificate_declaration theorem product_288_value (v : ℕ→ℂ) :
    eval v product_288=eval v n_c40_9*eval v n_d0_9 := by
  rw [←product_288_checked, eval_mulShort]
compact_certificate_declaration theorem product_289_checked :
    mulShort n_c40_10 n_d0_10=product_289 := by
  decide +kernel
compact_certificate_declaration theorem product_289_value (v : ℕ→ℂ) :
    eval v product_289=eval v n_c40_10*eval v n_d0_10 := by
  rw [←product_289_checked, eval_mulShort]
compact_certificate_declaration theorem product_290_checked :
    mulShort n_c40_11 n_d0_12=product_290 := by
  decide +kernel
compact_certificate_declaration theorem product_290_value (v : ℕ→ℂ) :
    eval v product_290=eval v n_c40_11*eval v n_d0_12 := by
  rw [←product_290_checked, eval_mulShort]
compact_certificate_declaration theorem product_291_checked :
    mulShort n_c40_12 n_d0_13=product_291 := by
  decide +kernel
compact_certificate_declaration theorem product_291_value (v : ℕ→ℂ) :
    eval v product_291=eval v n_c40_12*eval v n_d0_13 := by
  rw [←product_291_checked, eval_mulShort]
compact_certificate_declaration theorem product_292_checked :
    mulShort n_c40_13 n_d0_14=product_292 := by
  decide +kernel
compact_certificate_declaration theorem product_292_value (v : ℕ→ℂ) :
    eval v product_292=eval v n_c40_13*eval v n_d0_14 := by
  rw [←product_292_checked, eval_mulShort]
compact_certificate_declaration theorem product_293_checked :
    mulShort n_c40_14 n_d0_15=product_293 := by
  decide +kernel
compact_certificate_declaration theorem product_293_value (v : ℕ→ℂ) :
    eval v product_293=eval v n_c40_14*eval v n_d0_15 := by
  rw [←product_293_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_54_checked :
    (spadd (spadd (spadd product_286 product_287) (spadd product_288 product_289)) (spadd (spadd product_290 product_291) (spadd product_292 product_293)))=partial_sum_54 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_54_value (v : ℕ→ℂ) :
    eval v partial_sum_54=eval v (spadd (spadd product_286 product_287) (spadd product_288 product_289))+eval v (spadd (spadd product_290 product_291) (spadd product_292 product_293)) := by
  rw [←partial_sum_54_checked, eval_add]
compact_certificate_declaration theorem partial_sum_55_checked :
    (spadd (spadd (spadd product_279 (spadd product_280 product_281)) (spadd (spadd product_282 product_283) (spadd product_284 product_285))) partial_sum_54)=partial_sum_55 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_55_value (v : ℕ→ℂ) :
    eval v partial_sum_55=eval v (spadd (spadd product_279 (spadd product_280 product_281)) (spadd (spadd product_282 product_283) (spadd product_284 product_285)))+eval v partial_sum_54 := by
  rw [←partial_sum_55_checked, eval_add]
compact_certificate_declaration theorem product_294_checked :
    mulShort n_c40_15 n_d0_16=product_294 := by
  decide +kernel
compact_certificate_declaration theorem product_294_value (v : ℕ→ℂ) :
    eval v product_294=eval v n_c40_15*eval v n_d0_16 := by
  rw [←product_294_checked, eval_mulShort]
compact_certificate_declaration theorem product_295_checked :
    mulShort n_c40_16 n_d0_17=product_295 := by
  decide +kernel
compact_certificate_declaration theorem product_295_value (v : ℕ→ℂ) :
    eval v product_295=eval v n_c40_16*eval v n_d0_17 := by
  rw [←product_295_checked, eval_mulShort]
compact_certificate_declaration theorem product_296_checked :
    mulShort n_c40_17 n_d0_18=product_296 := by
  decide +kernel
compact_certificate_declaration theorem product_296_value (v : ℕ→ℂ) :
    eval v product_296=eval v n_c40_17*eval v n_d0_18 := by
  rw [←product_296_checked, eval_mulShort]
compact_certificate_declaration theorem product_297_checked :
    mulShort n_c40_18 n_d0_19=product_297 := by
  decide +kernel
compact_certificate_declaration theorem product_297_value (v : ℕ→ℂ) :
    eval v product_297=eval v n_c40_18*eval v n_d0_19 := by
  rw [←product_297_checked, eval_mulShort]
compact_certificate_declaration theorem product_298_checked :
    mulShort n_c40_19 n_d0_20=product_298 := by
  decide +kernel
compact_certificate_declaration theorem product_298_value (v : ℕ→ℂ) :
    eval v product_298=eval v n_c40_19*eval v n_d0_20 := by
  rw [←product_298_checked, eval_mulShort]
compact_certificate_declaration theorem product_299_checked :
    mulShort n_c40_20 n_d0_21=product_299 := by
  decide +kernel
compact_certificate_declaration theorem product_299_value (v : ℕ→ℂ) :
    eval v product_299=eval v n_c40_20*eval v n_d0_21 := by
  rw [←product_299_checked, eval_mulShort]
compact_certificate_declaration theorem product_300_checked :
    mulShort n_c40_21 n_d0_22=product_300 := by
  decide +kernel
compact_certificate_declaration theorem product_300_value (v : ℕ→ℂ) :
    eval v product_300=eval v n_c40_21*eval v n_d0_22 := by
  rw [←product_300_checked, eval_mulShort]
compact_certificate_declaration theorem product_301_checked :
    mulShort n_c40_22 n_d0_23=product_301 := by
  decide +kernel
compact_certificate_declaration theorem product_301_value (v : ℕ→ℂ) :
    eval v product_301=eval v n_c40_22*eval v n_d0_23 := by
  rw [←product_301_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_56_checked :
    (spadd (spadd (spadd product_294 product_295) (spadd product_296 product_297)) (spadd (spadd product_298 product_299) (spadd product_300 product_301)))=partial_sum_56 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_56_value (v : ℕ→ℂ) :
    eval v partial_sum_56=eval v (spadd (spadd product_294 product_295) (spadd product_296 product_297))+eval v (spadd (spadd product_298 product_299) (spadd product_300 product_301)) := by
  rw [←partial_sum_56_checked, eval_add]
compact_certificate_declaration theorem product_302_checked :
    mulShort n_c40_23 n_d0_24=product_302 := by
  decide +kernel
compact_certificate_declaration theorem product_302_value (v : ℕ→ℂ) :
    eval v product_302=eval v n_c40_23*eval v n_d0_24 := by
  rw [←product_302_checked, eval_mulShort]
compact_certificate_declaration theorem product_303_checked :
    mulShort n_c40_24 n_d0_25=product_303 := by
  decide +kernel
compact_certificate_declaration theorem product_303_value (v : ℕ→ℂ) :
    eval v product_303=eval v n_c40_24*eval v n_d0_25 := by
  rw [←product_303_checked, eval_mulShort]
compact_certificate_declaration theorem product_304_checked :
    mulShort n_c40_25 n_d0_26=product_304 := by
  decide +kernel
compact_certificate_declaration theorem product_304_value (v : ℕ→ℂ) :
    eval v product_304=eval v n_c40_25*eval v n_d0_26 := by
  rw [←product_304_checked, eval_mulShort]
compact_certificate_declaration theorem product_305_checked :
    mulShort n_c40_26 n_d0_27=product_305 := by
  decide +kernel
compact_certificate_declaration theorem product_305_value (v : ℕ→ℂ) :
    eval v product_305=eval v n_c40_26*eval v n_d0_27 := by
  rw [←product_305_checked, eval_mulShort]
compact_certificate_declaration theorem product_306_checked :
    mulShort n_c40_27 n_d0_28=product_306 := by
  decide +kernel
compact_certificate_declaration theorem product_306_value (v : ℕ→ℂ) :
    eval v product_306=eval v n_c40_27*eval v n_d0_28 := by
  rw [←product_306_checked, eval_mulShort]
compact_certificate_declaration theorem product_307_checked :
    mulShort n_c40_28 n_d0_29=product_307 := by
  decide +kernel
compact_certificate_declaration theorem product_307_value (v : ℕ→ℂ) :
    eval v product_307=eval v n_c40_28*eval v n_d0_29 := by
  rw [←product_307_checked, eval_mulShort]
compact_certificate_declaration theorem product_308_checked :
    mulShort n_c40_29 n_d0_30=product_308 := by
  decide +kernel
compact_certificate_declaration theorem product_308_value (v : ℕ→ℂ) :
    eval v product_308=eval v n_c40_29*eval v n_d0_30 := by
  rw [←product_308_checked, eval_mulShort]
compact_certificate_declaration theorem product_309_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c40_30) n_d1_40=product_309 := by
  decide +kernel
compact_certificate_declaration theorem product_309_value (v : ℕ→ℂ) :
    eval v product_309=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c40_30)*eval v n_d1_40 := by
  rw [←product_309_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_57_checked :
    (spadd (spadd (spadd product_302 product_303) (spadd product_304 product_305)) (spadd (spadd product_306 product_307) (spadd product_308 product_309)))=partial_sum_57 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_57_value (v : ℕ→ℂ) :
    eval v partial_sum_57=eval v (spadd (spadd product_302 product_303) (spadd product_304 product_305))+eval v (spadd (spadd product_306 product_307) (spadd product_308 product_309)) := by
  rw [←partial_sum_57_checked, eval_add]
compact_certificate_declaration theorem partial_sum_58_checked :
    (spadd partial_sum_56 partial_sum_57)=partial_sum_58 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_58_value (v : ℕ→ℂ) :
    eval v partial_sum_58=eval v partial_sum_56+eval v partial_sum_57 := by
  rw [←partial_sum_58_checked, eval_add]
compact_certificate_declaration theorem partial_sum_59_checked :
    (spadd partial_sum_55 partial_sum_58)=partial_sum_59 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_59_value (v : ℕ→ℂ) :
    eval v partial_sum_59=eval v partial_sum_55+eval v partial_sum_58 := by
  rw [←partial_sum_59_checked, eval_add]
compact_certificate_declaration theorem checked_9 : checkZero e9=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_9 (y z w a b u : ℂ) :
    (certificate y z w a b u)[9]?=some 0 := by
  change some ((((((c40_0 y z w a b u)*(d0_0 y z w a b u)+((c40_1 y z w a b u)*(d0_1 y z w a b u)+(c40_2 y z w a b u)*(d0_2 y z w a b u)))+(((c40_3 y z w a b u)*(d0_3 y z w a b u)+(c40_4 y z w a b u)*(d0_4 y z w a b u))+((c40_5 y z w a b u)*(d0_5 y z w a b u)+(c40_6 y z w a b u)*(d0_6 y z w a b u))))+((((c40_7 y z w a b u)*(d0_7 y z w a b u)+(c40_8 y z w a b u)*(d0_8 y z w a b u))+((c40_9 y z w a b u)*(d0_9 y z w a b u)+(c40_10 y z w a b u)*(d0_10 y z w a b u)))+(((c40_11 y z w a b u)*(d0_12 y z w a b u)+(c40_12 y z w a b u)*(d0_13 y z w a b u))+((c40_13 y z w a b u)*(d0_14 y z w a b u)+(c40_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c40_15 y z w a b u)*(d0_16 y z w a b u)+(c40_16 y z w a b u)*(d0_17 y z w a b u))+((c40_17 y z w a b u)*(d0_18 y z w a b u)+(c40_18 y z w a b u)*(d0_19 y z w a b u)))+(((c40_19 y z w a b u)*(d0_20 y z w a b u)+(c40_20 y z w a b u)*(d0_21 y z w a b u))+((c40_21 y z w a b u)*(d0_22 y z w a b u)+(c40_22 y z w a b u)*(d0_23 y z w a b u))))+((((c40_23 y z w a b u)*(d0_24 y z w a b u)+(c40_24 y z w a b u)*(d0_25 y z w a b u))+((c40_25 y z w a b u)*(d0_26 y z w a b u)+(c40_26 y z w a b u)*(d0_27 y z w a b u)))+(((c40_27 y z w a b u)*(d0_28 y z w a b u)+(c40_28 y z w a b u)*(d0_29 y z w a b u))+((c40_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c40_30 y z w a b u)*(d1_40 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e9 checked_9
  simp only [e9, eval_add, eval_mul, eval_scale, eval_pow, product_279_value, product_280_value, product_281_value, product_282_value, product_283_value, product_284_value, product_285_value, product_286_value, product_287_value, product_288_value, product_289_value, product_290_value, product_291_value, product_292_value, product_293_value, partial_sum_54_value, partial_sum_55_value, product_294_value, product_295_value, product_296_value, product_297_value, product_298_value, product_299_value, product_300_value, product_301_value, partial_sum_56_value, product_302_value, product_303_value, product_304_value, product_305_value, product_306_value, product_307_value, product_308_value, product_309_value, partial_sum_57_value, partial_sum_58_value, partial_sum_59_value, n_c40_0_value y z w a b u, n_c40_1_value y z w a b u, n_c40_10_value y z w a b u, n_c40_11_value y z w a b u, n_c40_12_value y z w a b u, n_c40_13_value y z w a b u, n_c40_14_value y z w a b u, n_c40_15_value y z w a b u, n_c40_16_value y z w a b u, n_c40_17_value y z w a b u, n_c40_18_value y z w a b u, n_c40_19_value y z w a b u, n_c40_2_value y z w a b u, n_c40_20_value y z w a b u, n_c40_21_value y z w a b u, n_c40_22_value y z w a b u, n_c40_23_value y z w a b u, n_c40_24_value y z w a b u, n_c40_25_value y z w a b u, n_c40_26_value y z w a b u, n_c40_27_value y z w a b u, n_c40_28_value y z w a b u, n_c40_29_value y z w a b u, n_c40_3_value y z w a b u, n_c40_30_value y z w a b u, n_c40_4_value y z w a b u, n_c40_5_value y z w a b u, n_c40_6_value y z w a b u, n_c40_7_value y z w a b u, n_c40_8_value y z w a b u, n_c40_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_40_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_310_checked :
    mulShort n_c41_0 n_d0_0=product_310 := by
  decide +kernel
compact_certificate_declaration theorem product_310_value (v : ℕ→ℂ) :
    eval v product_310=eval v n_c41_0*eval v n_d0_0 := by
  rw [←product_310_checked, eval_mulShort]
compact_certificate_declaration theorem product_311_checked :
    mulShort n_c41_1 n_d0_1=product_311 := by
  decide +kernel
compact_certificate_declaration theorem product_311_value (v : ℕ→ℂ) :
    eval v product_311=eval v n_c41_1*eval v n_d0_1 := by
  rw [←product_311_checked, eval_mulShort]
compact_certificate_declaration theorem product_312_checked :
    mulShort n_c41_2 n_d0_2=product_312 := by
  decide +kernel
compact_certificate_declaration theorem product_312_value (v : ℕ→ℂ) :
    eval v product_312=eval v n_c41_2*eval v n_d0_2 := by
  rw [←product_312_checked, eval_mulShort]
compact_certificate_declaration theorem product_313_checked :
    mulShort n_c41_3 n_d0_3=product_313 := by
  decide +kernel
compact_certificate_declaration theorem product_313_value (v : ℕ→ℂ) :
    eval v product_313=eval v n_c41_3*eval v n_d0_3 := by
  rw [←product_313_checked, eval_mulShort]
}
certificate_batch {
compact_certificate_declaration theorem product_314_checked :
    mulShort n_c41_4 n_d0_4=product_314 := by
  decide +kernel
compact_certificate_declaration theorem product_314_value (v : ℕ→ℂ) :
    eval v product_314=eval v n_c41_4*eval v n_d0_4 := by
  rw [←product_314_checked, eval_mulShort]
compact_certificate_declaration theorem product_315_checked :
    mulShort n_c41_5 n_d0_5=product_315 := by
  decide +kernel
compact_certificate_declaration theorem product_315_value (v : ℕ→ℂ) :
    eval v product_315=eval v n_c41_5*eval v n_d0_5 := by
  rw [←product_315_checked, eval_mulShort]
compact_certificate_declaration theorem product_316_checked :
    mulShort n_c41_6 n_d0_6=product_316 := by
  decide +kernel
compact_certificate_declaration theorem product_316_value (v : ℕ→ℂ) :
    eval v product_316=eval v n_c41_6*eval v n_d0_6 := by
  rw [←product_316_checked, eval_mulShort]
compact_certificate_declaration theorem product_317_checked :
    mulShort n_c41_7 n_d0_7=product_317 := by
  decide +kernel
compact_certificate_declaration theorem product_317_value (v : ℕ→ℂ) :
    eval v product_317=eval v n_c41_7*eval v n_d0_7 := by
  rw [←product_317_checked, eval_mulShort]
compact_certificate_declaration theorem product_318_checked :
    mulShort n_c41_8 n_d0_8=product_318 := by
  decide +kernel
compact_certificate_declaration theorem product_318_value (v : ℕ→ℂ) :
    eval v product_318=eval v n_c41_8*eval v n_d0_8 := by
  rw [←product_318_checked, eval_mulShort]
compact_certificate_declaration theorem product_319_checked :
    mulShort n_c41_9 n_d0_9=product_319 := by
  decide +kernel
compact_certificate_declaration theorem product_319_value (v : ℕ→ℂ) :
    eval v product_319=eval v n_c41_9*eval v n_d0_9 := by
  rw [←product_319_checked, eval_mulShort]
compact_certificate_declaration theorem product_320_checked :
    mulShort n_c41_10 n_d0_10=product_320 := by
  decide +kernel
compact_certificate_declaration theorem product_320_value (v : ℕ→ℂ) :
    eval v product_320=eval v n_c41_10*eval v n_d0_10 := by
  rw [←product_320_checked, eval_mulShort]
compact_certificate_declaration theorem product_321_checked :
    mulShort n_c41_11 n_d0_12=product_321 := by
  decide +kernel
compact_certificate_declaration theorem product_321_value (v : ℕ→ℂ) :
    eval v product_321=eval v n_c41_11*eval v n_d0_12 := by
  rw [←product_321_checked, eval_mulShort]
compact_certificate_declaration theorem product_322_checked :
    mulShort n_c41_12 n_d0_13=product_322 := by
  decide +kernel
compact_certificate_declaration theorem product_322_value (v : ℕ→ℂ) :
    eval v product_322=eval v n_c41_12*eval v n_d0_13 := by
  rw [←product_322_checked, eval_mulShort]
compact_certificate_declaration theorem product_323_checked :
    mulShort n_c41_13 n_d0_14=product_323 := by
  decide +kernel
compact_certificate_declaration theorem product_323_value (v : ℕ→ℂ) :
    eval v product_323=eval v n_c41_13*eval v n_d0_14 := by
  rw [←product_323_checked, eval_mulShort]
compact_certificate_declaration theorem product_324_checked :
    mulShort n_c41_14 n_d0_15=product_324 := by
  decide +kernel
compact_certificate_declaration theorem product_324_value (v : ℕ→ℂ) :
    eval v product_324=eval v n_c41_14*eval v n_d0_15 := by
  rw [←product_324_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_60_checked :
    (spadd (spadd (spadd product_317 product_318) (spadd product_319 product_320)) (spadd (spadd product_321 product_322) (spadd product_323 product_324)))=partial_sum_60 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_60_value (v : ℕ→ℂ) :
    eval v partial_sum_60=eval v (spadd (spadd product_317 product_318) (spadd product_319 product_320))+eval v (spadd (spadd product_321 product_322) (spadd product_323 product_324)) := by
  rw [←partial_sum_60_checked, eval_add]
compact_certificate_declaration theorem partial_sum_61_checked :
    (spadd (spadd (spadd product_310 (spadd product_311 product_312)) (spadd (spadd product_313 product_314) (spadd product_315 product_316))) partial_sum_60)=partial_sum_61 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_61_value (v : ℕ→ℂ) :
    eval v partial_sum_61=eval v (spadd (spadd product_310 (spadd product_311 product_312)) (spadd (spadd product_313 product_314) (spadd product_315 product_316)))+eval v partial_sum_60 := by
  rw [←partial_sum_61_checked, eval_add]
compact_certificate_declaration theorem product_325_checked :
    mulShort n_c41_15 n_d0_16=product_325 := by
  decide +kernel
compact_certificate_declaration theorem product_325_value (v : ℕ→ℂ) :
    eval v product_325=eval v n_c41_15*eval v n_d0_16 := by
  rw [←product_325_checked, eval_mulShort]
compact_certificate_declaration theorem product_326_checked :
    mulShort n_c41_16 n_d0_17=product_326 := by
  decide +kernel
compact_certificate_declaration theorem product_326_value (v : ℕ→ℂ) :
    eval v product_326=eval v n_c41_16*eval v n_d0_17 := by
  rw [←product_326_checked, eval_mulShort]
compact_certificate_declaration theorem product_327_checked :
    mulShort n_c41_17 n_d0_18=product_327 := by
  decide +kernel
compact_certificate_declaration theorem product_327_value (v : ℕ→ℂ) :
    eval v product_327=eval v n_c41_17*eval v n_d0_18 := by
  rw [←product_327_checked, eval_mulShort]
compact_certificate_declaration theorem product_328_checked :
    mulShort n_c41_18 n_d0_19=product_328 := by
  decide +kernel
compact_certificate_declaration theorem product_328_value (v : ℕ→ℂ) :
    eval v product_328=eval v n_c41_18*eval v n_d0_19 := by
  rw [←product_328_checked, eval_mulShort]
compact_certificate_declaration theorem product_329_checked :
    mulShort n_c41_19 n_d0_20=product_329 := by
  decide +kernel
compact_certificate_declaration theorem product_329_value (v : ℕ→ℂ) :
    eval v product_329=eval v n_c41_19*eval v n_d0_20 := by
  rw [←product_329_checked, eval_mulShort]
compact_certificate_declaration theorem product_330_checked :
    mulShort n_c41_20 n_d0_21=product_330 := by
  decide +kernel
compact_certificate_declaration theorem product_330_value (v : ℕ→ℂ) :
    eval v product_330=eval v n_c41_20*eval v n_d0_21 := by
  rw [←product_330_checked, eval_mulShort]
compact_certificate_declaration theorem product_331_checked :
    mulShort n_c41_21 n_d0_22=product_331 := by
  decide +kernel
compact_certificate_declaration theorem product_331_value (v : ℕ→ℂ) :
    eval v product_331=eval v n_c41_21*eval v n_d0_22 := by
  rw [←product_331_checked, eval_mulShort]
compact_certificate_declaration theorem product_332_checked :
    mulShort n_c41_22 n_d0_23=product_332 := by
  decide +kernel
compact_certificate_declaration theorem product_332_value (v : ℕ→ℂ) :
    eval v product_332=eval v n_c41_22*eval v n_d0_23 := by
  rw [←product_332_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_62_checked :
    (spadd (spadd (spadd product_325 product_326) (spadd product_327 product_328)) (spadd (spadd product_329 product_330) (spadd product_331 product_332)))=partial_sum_62 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_62_value (v : ℕ→ℂ) :
    eval v partial_sum_62=eval v (spadd (spadd product_325 product_326) (spadd product_327 product_328))+eval v (spadd (spadd product_329 product_330) (spadd product_331 product_332)) := by
  rw [←partial_sum_62_checked, eval_add]
compact_certificate_declaration theorem product_333_checked :
    mulShort n_c41_23 n_d0_24=product_333 := by
  decide +kernel
compact_certificate_declaration theorem product_333_value (v : ℕ→ℂ) :
    eval v product_333=eval v n_c41_23*eval v n_d0_24 := by
  rw [←product_333_checked, eval_mulShort]
compact_certificate_declaration theorem product_334_checked :
    mulShort n_c41_24 n_d0_25=product_334 := by
  decide +kernel
compact_certificate_declaration theorem product_334_value (v : ℕ→ℂ) :
    eval v product_334=eval v n_c41_24*eval v n_d0_25 := by
  rw [←product_334_checked, eval_mulShort]
compact_certificate_declaration theorem product_335_checked :
    mulShort n_c41_25 n_d0_26=product_335 := by
  decide +kernel
compact_certificate_declaration theorem product_335_value (v : ℕ→ℂ) :
    eval v product_335=eval v n_c41_25*eval v n_d0_26 := by
  rw [←product_335_checked, eval_mulShort]
compact_certificate_declaration theorem product_336_checked :
    mulShort n_c41_26 n_d0_27=product_336 := by
  decide +kernel
compact_certificate_declaration theorem product_336_value (v : ℕ→ℂ) :
    eval v product_336=eval v n_c41_26*eval v n_d0_27 := by
  rw [←product_336_checked, eval_mulShort]
compact_certificate_declaration theorem product_337_checked :
    mulShort n_c41_27 n_d0_28=product_337 := by
  decide +kernel
compact_certificate_declaration theorem product_337_value (v : ℕ→ℂ) :
    eval v product_337=eval v n_c41_27*eval v n_d0_28 := by
  rw [←product_337_checked, eval_mulShort]
compact_certificate_declaration theorem product_338_checked :
    mulShort n_c41_28 n_d0_29=product_338 := by
  decide +kernel
compact_certificate_declaration theorem product_338_value (v : ℕ→ℂ) :
    eval v product_338=eval v n_c41_28*eval v n_d0_29 := by
  rw [←product_338_checked, eval_mulShort]
compact_certificate_declaration theorem product_339_checked :
    mulShort n_c41_29 n_d0_30=product_339 := by
  decide +kernel
compact_certificate_declaration theorem product_339_value (v : ℕ→ℂ) :
    eval v product_339=eval v n_c41_29*eval v n_d0_30 := by
  rw [←product_339_checked, eval_mulShort]
compact_certificate_declaration theorem product_340_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c41_30) n_d1_41=product_340 := by
  decide +kernel
compact_certificate_declaration theorem product_340_value (v : ℕ→ℂ) :
    eval v product_340=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c41_30)*eval v n_d1_41 := by
  rw [←product_340_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_63_checked :
    (spadd (spadd (spadd product_333 product_334) (spadd product_335 product_336)) (spadd (spadd product_337 product_338) (spadd product_339 product_340)))=partial_sum_63 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_63_value (v : ℕ→ℂ) :
    eval v partial_sum_63=eval v (spadd (spadd product_333 product_334) (spadd product_335 product_336))+eval v (spadd (spadd product_337 product_338) (spadd product_339 product_340)) := by
  rw [←partial_sum_63_checked, eval_add]
compact_certificate_declaration theorem partial_sum_64_checked :
    (spadd partial_sum_62 partial_sum_63)=partial_sum_64 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_64_value (v : ℕ→ℂ) :
    eval v partial_sum_64=eval v partial_sum_62+eval v partial_sum_63 := by
  rw [←partial_sum_64_checked, eval_add]
compact_certificate_declaration theorem partial_sum_65_checked :
    (spadd partial_sum_61 partial_sum_64)=partial_sum_65 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_65_value (v : ℕ→ℂ) :
    eval v partial_sum_65=eval v partial_sum_61+eval v partial_sum_64 := by
  rw [←partial_sum_65_checked, eval_add]
compact_certificate_declaration theorem checked_10 : checkZero e10=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_10 (y z w a b u : ℂ) :
    (certificate y z w a b u)[10]?=some 0 := by
  change some ((((((c41_0 y z w a b u)*(d0_0 y z w a b u)+((c41_1 y z w a b u)*(d0_1 y z w a b u)+(c41_2 y z w a b u)*(d0_2 y z w a b u)))+(((c41_3 y z w a b u)*(d0_3 y z w a b u)+(c41_4 y z w a b u)*(d0_4 y z w a b u))+((c41_5 y z w a b u)*(d0_5 y z w a b u)+(c41_6 y z w a b u)*(d0_6 y z w a b u))))+((((c41_7 y z w a b u)*(d0_7 y z w a b u)+(c41_8 y z w a b u)*(d0_8 y z w a b u))+((c41_9 y z w a b u)*(d0_9 y z w a b u)+(c41_10 y z w a b u)*(d0_10 y z w a b u)))+(((c41_11 y z w a b u)*(d0_12 y z w a b u)+(c41_12 y z w a b u)*(d0_13 y z w a b u))+((c41_13 y z w a b u)*(d0_14 y z w a b u)+(c41_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c41_15 y z w a b u)*(d0_16 y z w a b u)+(c41_16 y z w a b u)*(d0_17 y z w a b u))+((c41_17 y z w a b u)*(d0_18 y z w a b u)+(c41_18 y z w a b u)*(d0_19 y z w a b u)))+(((c41_19 y z w a b u)*(d0_20 y z w a b u)+(c41_20 y z w a b u)*(d0_21 y z w a b u))+((c41_21 y z w a b u)*(d0_22 y z w a b u)+(c41_22 y z w a b u)*(d0_23 y z w a b u))))+((((c41_23 y z w a b u)*(d0_24 y z w a b u)+(c41_24 y z w a b u)*(d0_25 y z w a b u))+((c41_25 y z w a b u)*(d0_26 y z w a b u)+(c41_26 y z w a b u)*(d0_27 y z w a b u)))+(((c41_27 y z w a b u)*(d0_28 y z w a b u)+(c41_28 y z w a b u)*(d0_29 y z w a b u))+((c41_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c41_30 y z w a b u)*(d1_41 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e10 checked_10
  simp only [e10, eval_add, eval_mul, eval_scale, eval_pow, product_310_value, product_311_value, product_312_value, product_313_value, product_314_value, product_315_value, product_316_value, product_317_value, product_318_value, product_319_value, product_320_value, product_321_value, product_322_value, product_323_value, product_324_value, partial_sum_60_value, partial_sum_61_value, product_325_value, product_326_value, product_327_value, product_328_value, product_329_value, product_330_value, product_331_value, product_332_value, partial_sum_62_value, product_333_value, product_334_value, product_335_value, product_336_value, product_337_value, product_338_value, product_339_value, product_340_value, partial_sum_63_value, partial_sum_64_value, partial_sum_65_value, n_c41_0_value y z w a b u, n_c41_1_value y z w a b u, n_c41_10_value y z w a b u, n_c41_11_value y z w a b u, n_c41_12_value y z w a b u, n_c41_13_value y z w a b u, n_c41_14_value y z w a b u, n_c41_15_value y z w a b u, n_c41_16_value y z w a b u, n_c41_17_value y z w a b u, n_c41_18_value y z w a b u, n_c41_19_value y z w a b u, n_c41_2_value y z w a b u, n_c41_20_value y z w a b u, n_c41_21_value y z w a b u, n_c41_22_value y z w a b u, n_c41_23_value y z w a b u, n_c41_24_value y z w a b u, n_c41_25_value y z w a b u, n_c41_26_value y z w a b u, n_c41_27_value y z w a b u, n_c41_28_value y z w a b u, n_c41_29_value y z w a b u, n_c41_3_value y z w a b u, n_c41_30_value y z w a b u, n_c41_4_value y z w a b u, n_c41_5_value y z w a b u, n_c41_6_value y z w a b u, n_c41_7_value y z w a b u, n_c41_8_value y z w a b u, n_c41_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_41_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_341_checked :
    mulShort n_c42_0 n_d0_0=product_341 := by
  decide +kernel
compact_certificate_declaration theorem product_341_value (v : ℕ→ℂ) :
    eval v product_341=eval v n_c42_0*eval v n_d0_0 := by
  rw [←product_341_checked, eval_mulShort]
compact_certificate_declaration theorem product_342_checked :
    mulShort n_c42_1 n_d0_1=product_342 := by
  decide +kernel
compact_certificate_declaration theorem product_342_value (v : ℕ→ℂ) :
    eval v product_342=eval v n_c42_1*eval v n_d0_1 := by
  rw [←product_342_checked, eval_mulShort]
compact_certificate_declaration theorem product_343_checked :
    mulShort n_c42_2 n_d0_2=product_343 := by
  decide +kernel
compact_certificate_declaration theorem product_343_value (v : ℕ→ℂ) :
    eval v product_343=eval v n_c42_2*eval v n_d0_2 := by
  rw [←product_343_checked, eval_mulShort]
compact_certificate_declaration theorem product_344_checked :
    mulShort n_c42_3 n_d0_3=product_344 := by
  decide +kernel
compact_certificate_declaration theorem product_344_value (v : ℕ→ℂ) :
    eval v product_344=eval v n_c42_3*eval v n_d0_3 := by
  rw [←product_344_checked, eval_mulShort]
compact_certificate_declaration theorem product_345_checked :
    mulShort n_c42_4 n_d0_4=product_345 := by
  decide +kernel
compact_certificate_declaration theorem product_345_value (v : ℕ→ℂ) :
    eval v product_345=eval v n_c42_4*eval v n_d0_4 := by
  rw [←product_345_checked, eval_mulShort]
compact_certificate_declaration theorem product_346_checked :
    mulShort n_c42_5 n_d0_5=product_346 := by
  decide +kernel
compact_certificate_declaration theorem product_346_value (v : ℕ→ℂ) :
    eval v product_346=eval v n_c42_5*eval v n_d0_5 := by
  rw [←product_346_checked, eval_mulShort]
compact_certificate_declaration theorem product_347_checked :
    mulShort n_c42_6 n_d0_6=product_347 := by
  decide +kernel
compact_certificate_declaration theorem product_347_value (v : ℕ→ℂ) :
    eval v product_347=eval v n_c42_6*eval v n_d0_6 := by
  rw [←product_347_checked, eval_mulShort]
compact_certificate_declaration theorem product_348_checked :
    mulShort n_c42_7 n_d0_7=product_348 := by
  decide +kernel
compact_certificate_declaration theorem product_348_value (v : ℕ→ℂ) :
    eval v product_348=eval v n_c42_7*eval v n_d0_7 := by
  rw [←product_348_checked, eval_mulShort]
compact_certificate_declaration theorem product_349_checked :
    mulShort n_c42_8 n_d0_8=product_349 := by
  decide +kernel

compact_certificate_declaration theorem product_349_value (v : ℕ→ℂ) :
    eval v product_349=eval v n_c42_8*eval v n_d0_8 := by
  rw [←product_349_checked, eval_mulShort]
compact_certificate_declaration theorem product_350_checked :
    mulShort n_c42_9 n_d0_9=product_350 := by
  decide +kernel
compact_certificate_declaration theorem product_350_value (v : ℕ→ℂ) :
    eval v product_350=eval v n_c42_9*eval v n_d0_9 := by
  rw [←product_350_checked, eval_mulShort]
compact_certificate_declaration theorem product_351_checked :
    mulShort n_c42_10 n_d0_10=product_351 := by
  decide +kernel
compact_certificate_declaration theorem product_351_value (v : ℕ→ℂ) :
    eval v product_351=eval v n_c42_10*eval v n_d0_10 := by
  rw [←product_351_checked, eval_mulShort]
compact_certificate_declaration theorem product_352_checked :
    mulShort n_c42_11 n_d0_12=product_352 := by
  decide +kernel
compact_certificate_declaration theorem product_352_value (v : ℕ→ℂ) :
    eval v product_352=eval v n_c42_11*eval v n_d0_12 := by
  rw [←product_352_checked, eval_mulShort]
compact_certificate_declaration theorem product_353_checked :
    mulShort n_c42_12 n_d0_13=product_353 := by
  decide +kernel
compact_certificate_declaration theorem product_353_value (v : ℕ→ℂ) :
    eval v product_353=eval v n_c42_12*eval v n_d0_13 := by
  rw [←product_353_checked, eval_mulShort]
compact_certificate_declaration theorem product_354_checked :
    mulShort n_c42_13 n_d0_14=product_354 := by
  decide +kernel
compact_certificate_declaration theorem product_354_value (v : ℕ→ℂ) :
    eval v product_354=eval v n_c42_13*eval v n_d0_14 := by
  rw [←product_354_checked, eval_mulShort]
compact_certificate_declaration theorem product_355_checked :
    mulShort n_c42_14 n_d0_15=product_355 := by
  decide +kernel
compact_certificate_declaration theorem product_355_value (v : ℕ→ℂ) :
    eval v product_355=eval v n_c42_14*eval v n_d0_15 := by
  rw [←product_355_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_66_checked :
    (spadd (spadd (spadd product_348 product_349) (spadd product_350 product_351)) (spadd (spadd product_352 product_353) (spadd product_354 product_355)))=partial_sum_66 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_66_value (v : ℕ→ℂ) :
    eval v partial_sum_66=eval v (spadd (spadd product_348 product_349) (spadd product_350 product_351))+eval v (spadd (spadd product_352 product_353) (spadd product_354 product_355)) := by
  rw [←partial_sum_66_checked, eval_add]
compact_certificate_declaration theorem partial_sum_67_checked :
    (spadd (spadd (spadd product_341 (spadd product_342 product_343)) (spadd (spadd product_344 product_345) (spadd product_346 product_347))) partial_sum_66)=partial_sum_67 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_67_value (v : ℕ→ℂ) :
    eval v partial_sum_67=eval v (spadd (spadd product_341 (spadd product_342 product_343)) (spadd (spadd product_344 product_345) (spadd product_346 product_347)))+eval v partial_sum_66 := by
  rw [←partial_sum_67_checked, eval_add]
compact_certificate_declaration theorem product_356_checked :
    mulShort n_c42_15 n_d0_16=product_356 := by
  decide +kernel
compact_certificate_declaration theorem product_356_value (v : ℕ→ℂ) :
    eval v product_356=eval v n_c42_15*eval v n_d0_16 := by
  rw [←product_356_checked, eval_mulShort]
compact_certificate_declaration theorem product_357_checked :
    mulShort n_c42_16 n_d0_17=product_357 := by
  decide +kernel
compact_certificate_declaration theorem product_357_value (v : ℕ→ℂ) :
    eval v product_357=eval v n_c42_16*eval v n_d0_17 := by
  rw [←product_357_checked, eval_mulShort]
compact_certificate_declaration theorem product_358_checked :
    mulShort n_c42_17 n_d0_18=product_358 := by
  decide +kernel
compact_certificate_declaration theorem product_358_value (v : ℕ→ℂ) :
    eval v product_358=eval v n_c42_17*eval v n_d0_18 := by
  rw [←product_358_checked, eval_mulShort]
compact_certificate_declaration theorem product_359_checked :
    mulShort n_c42_18 n_d0_19=product_359 := by
  decide +kernel
compact_certificate_declaration theorem product_359_value (v : ℕ→ℂ) :
    eval v product_359=eval v n_c42_18*eval v n_d0_19 := by
  rw [←product_359_checked, eval_mulShort]
compact_certificate_declaration theorem product_360_checked :
    mulShort n_c42_19 n_d0_20=product_360 := by
  decide +kernel
compact_certificate_declaration theorem product_360_value (v : ℕ→ℂ) :
    eval v product_360=eval v n_c42_19*eval v n_d0_20 := by
  rw [←product_360_checked, eval_mulShort]
compact_certificate_declaration theorem product_361_checked :
    mulShort n_c42_20 n_d0_21=product_361 := by
  decide +kernel
compact_certificate_declaration theorem product_361_value (v : ℕ→ℂ) :
    eval v product_361=eval v n_c42_20*eval v n_d0_21 := by
  rw [←product_361_checked, eval_mulShort]
compact_certificate_declaration theorem product_362_checked :
    mulShort n_c42_21 n_d0_22=product_362 := by
  decide +kernel
compact_certificate_declaration theorem product_362_value (v : ℕ→ℂ) :
    eval v product_362=eval v n_c42_21*eval v n_d0_22 := by
  rw [←product_362_checked, eval_mulShort]
compact_certificate_declaration theorem product_363_checked :
    mulShort n_c42_22 n_d0_23=product_363 := by
  decide +kernel
compact_certificate_declaration theorem product_363_value (v : ℕ→ℂ) :
    eval v product_363=eval v n_c42_22*eval v n_d0_23 := by
  rw [←product_363_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_68_checked :
    (spadd (spadd (spadd product_356 product_357) (spadd product_358 product_359)) (spadd (spadd product_360 product_361) (spadd product_362 product_363)))=partial_sum_68 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_68_value (v : ℕ→ℂ) :
    eval v partial_sum_68=eval v (spadd (spadd product_356 product_357) (spadd product_358 product_359))+eval v (spadd (spadd product_360 product_361) (spadd product_362 product_363)) := by
  rw [←partial_sum_68_checked, eval_add]
compact_certificate_declaration theorem product_364_checked :
    mulShort n_c42_23 n_d0_24=product_364 := by
  decide +kernel
compact_certificate_declaration theorem product_364_value (v : ℕ→ℂ) :
    eval v product_364=eval v n_c42_23*eval v n_d0_24 := by
  rw [←product_364_checked, eval_mulShort]
compact_certificate_declaration theorem product_365_checked :
    mulShort n_c42_24 n_d0_25=product_365 := by
  decide +kernel
compact_certificate_declaration theorem product_365_value (v : ℕ→ℂ) :
    eval v product_365=eval v n_c42_24*eval v n_d0_25 := by
  rw [←product_365_checked, eval_mulShort]
compact_certificate_declaration theorem product_366_checked :
    mulShort n_c42_25 n_d0_26=product_366 := by
  decide +kernel
compact_certificate_declaration theorem product_366_value (v : ℕ→ℂ) :
    eval v product_366=eval v n_c42_25*eval v n_d0_26 := by
  rw [←product_366_checked, eval_mulShort]
compact_certificate_declaration theorem product_367_checked :
    mulShort n_c42_26 n_d0_27=product_367 := by
  decide +kernel
compact_certificate_declaration theorem product_367_value (v : ℕ→ℂ) :
    eval v product_367=eval v n_c42_26*eval v n_d0_27 := by
  rw [←product_367_checked, eval_mulShort]
compact_certificate_declaration theorem product_368_checked :
    mulShort n_c42_27 n_d0_28=product_368 := by
  decide +kernel
compact_certificate_declaration theorem product_368_value (v : ℕ→ℂ) :
    eval v product_368=eval v n_c42_27*eval v n_d0_28 := by
  rw [←product_368_checked, eval_mulShort]
compact_certificate_declaration theorem product_369_checked :
    mulShort n_c42_28 n_d0_29=product_369 := by
  decide +kernel
compact_certificate_declaration theorem product_369_value (v : ℕ→ℂ) :
    eval v product_369=eval v n_c42_28*eval v n_d0_29 := by
  rw [←product_369_checked, eval_mulShort]
compact_certificate_declaration theorem product_370_checked :
    mulShort n_c42_29 n_d0_30=product_370 := by
  decide +kernel
compact_certificate_declaration theorem product_370_value (v : ℕ→ℂ) :
    eval v product_370=eval v n_c42_29*eval v n_d0_30 := by
  rw [←product_370_checked, eval_mulShort]
compact_certificate_declaration theorem product_371_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c42_30) n_d1_42=product_371 := by
  decide +kernel
compact_certificate_declaration theorem product_371_value (v : ℕ→ℂ) :
    eval v product_371=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c42_30)*eval v n_d1_42 := by
  rw [←product_371_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_69_checked :
    (spadd (spadd (spadd product_364 product_365) (spadd product_366 product_367)) (spadd (spadd product_368 product_369) (spadd product_370 product_371)))=partial_sum_69 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_69_value (v : ℕ→ℂ) :
    eval v partial_sum_69=eval v (spadd (spadd product_364 product_365) (spadd product_366 product_367))+eval v (spadd (spadd product_368 product_369) (spadd product_370 product_371)) := by
  rw [←partial_sum_69_checked, eval_add]
compact_certificate_declaration theorem partial_sum_70_checked :
    (spadd partial_sum_68 partial_sum_69)=partial_sum_70 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_70_value (v : ℕ→ℂ) :
    eval v partial_sum_70=eval v partial_sum_68+eval v partial_sum_69 := by
  rw [←partial_sum_70_checked, eval_add]
compact_certificate_declaration theorem partial_sum_71_checked :
    (spadd partial_sum_67 partial_sum_70)=partial_sum_71 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_71_value (v : ℕ→ℂ) :
    eval v partial_sum_71=eval v partial_sum_67+eval v partial_sum_70 := by
  rw [←partial_sum_71_checked, eval_add]
compact_certificate_declaration theorem checked_11 : checkZero e11=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_11 (y z w a b u : ℂ) :
    (certificate y z w a b u)[11]?=some 0 := by
  change some ((((((c42_0 y z w a b u)*(d0_0 y z w a b u)+((c42_1 y z w a b u)*(d0_1 y z w a b u)+(c42_2 y z w a b u)*(d0_2 y z w a b u)))+(((c42_3 y z w a b u)*(d0_3 y z w a b u)+(c42_4 y z w a b u)*(d0_4 y z w a b u))+((c42_5 y z w a b u)*(d0_5 y z w a b u)+(c42_6 y z w a b u)*(d0_6 y z w a b u))))+((((c42_7 y z w a b u)*(d0_7 y z w a b u)+(c42_8 y z w a b u)*(d0_8 y z w a b u))+((c42_9 y z w a b u)*(d0_9 y z w a b u)+(c42_10 y z w a b u)*(d0_10 y z w a b u)))+(((c42_11 y z w a b u)*(d0_12 y z w a b u)+(c42_12 y z w a b u)*(d0_13 y z w a b u))+((c42_13 y z w a b u)*(d0_14 y z w a b u)+(c42_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c42_15 y z w a b u)*(d0_16 y z w a b u)+(c42_16 y z w a b u)*(d0_17 y z w a b u))+((c42_17 y z w a b u)*(d0_18 y z w a b u)+(c42_18 y z w a b u)*(d0_19 y z w a b u)))+(((c42_19 y z w a b u)*(d0_20 y z w a b u)+(c42_20 y z w a b u)*(d0_21 y z w a b u))+((c42_21 y z w a b u)*(d0_22 y z w a b u)+(c42_22 y z w a b u)*(d0_23 y z w a b u))))+((((c42_23 y z w a b u)*(d0_24 y z w a b u)+(c42_24 y z w a b u)*(d0_25 y z w a b u))+((c42_25 y z w a b u)*(d0_26 y z w a b u)+(c42_26 y z w a b u)*(d0_27 y z w a b u)))+(((c42_27 y z w a b u)*(d0_28 y z w a b u)+(c42_28 y z w a b u)*(d0_29 y z w a b u))+((c42_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c42_30 y z w a b u)*(d1_42 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e11 checked_11
  simp only [e11, eval_add, eval_mul, eval_scale, eval_pow, product_341_value, product_342_value, product_343_value, product_344_value, product_345_value, product_346_value, product_347_value, product_348_value, product_349_value, product_350_value, product_351_value, product_352_value, product_353_value, product_354_value, product_355_value, partial_sum_66_value, partial_sum_67_value, product_356_value, product_357_value, product_358_value, product_359_value, product_360_value, product_361_value, product_362_value, product_363_value, partial_sum_68_value, product_364_value, product_365_value, product_366_value, product_367_value, product_368_value, product_369_value, product_370_value, product_371_value, partial_sum_69_value, partial_sum_70_value, partial_sum_71_value, n_c42_0_value y z w a b u, n_c42_1_value y z w a b u, n_c42_10_value y z w a b u, n_c42_11_value y z w a b u, n_c42_12_value y z w a b u, n_c42_13_value y z w a b u, n_c42_14_value y z w a b u, n_c42_15_value y z w a b u, n_c42_16_value y z w a b u, n_c42_17_value y z w a b u, n_c42_18_value y z w a b u, n_c42_19_value y z w a b u, n_c42_2_value y z w a b u, n_c42_20_value y z w a b u, n_c42_21_value y z w a b u, n_c42_22_value y z w a b u, n_c42_23_value y z w a b u, n_c42_24_value y z w a b u, n_c42_25_value y z w a b u, n_c42_26_value y z w a b u, n_c42_27_value y z w a b u, n_c42_28_value y z w a b u, n_c42_29_value y z w a b u, n_c42_3_value y z w a b u, n_c42_30_value y z w a b u, n_c42_4_value y z w a b u, n_c42_5_value y z w a b u, n_c42_6_value y z w a b u, n_c42_7_value y z w a b u, n_c42_8_value y z w a b u, n_c42_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_42_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_372_checked :
    mulShort n_c43_0 n_d0_0=product_372 := by
  decide +kernel
compact_certificate_declaration theorem product_372_value (v : ℕ→ℂ) :
    eval v product_372=eval v n_c43_0*eval v n_d0_0 := by
  rw [←product_372_checked, eval_mulShort]
compact_certificate_declaration theorem product_373_checked :
    mulShort n_c43_1 n_d0_1=product_373 := by
  decide +kernel
compact_certificate_declaration theorem product_373_value (v : ℕ→ℂ) :
    eval v product_373=eval v n_c43_1*eval v n_d0_1 := by
  rw [←product_373_checked, eval_mulShort]
compact_certificate_declaration theorem product_374_checked :
    mulShort n_c43_2 n_d0_2=product_374 := by
  decide +kernel
compact_certificate_declaration theorem product_374_value (v : ℕ→ℂ) :
    eval v product_374=eval v n_c43_2*eval v n_d0_2 := by
  rw [←product_374_checked, eval_mulShort]
compact_certificate_declaration theorem product_375_checked :
    mulShort n_c43_3 n_d0_3=product_375 := by
  decide +kernel
compact_certificate_declaration theorem product_375_value (v : ℕ→ℂ) :
    eval v product_375=eval v n_c43_3*eval v n_d0_3 := by
  rw [←product_375_checked, eval_mulShort]
compact_certificate_declaration theorem product_376_checked :
    mulShort n_c43_4 n_d0_4=product_376 := by
  decide +kernel
compact_certificate_declaration theorem product_376_value (v : ℕ→ℂ) :
    eval v product_376=eval v n_c43_4*eval v n_d0_4 := by
  rw [←product_376_checked, eval_mulShort]
compact_certificate_declaration theorem product_377_checked :
    mulShort n_c43_5 n_d0_5=product_377 := by
  decide +kernel
compact_certificate_declaration theorem product_377_value (v : ℕ→ℂ) :
    eval v product_377=eval v n_c43_5*eval v n_d0_5 := by
  rw [←product_377_checked, eval_mulShort]
compact_certificate_declaration theorem product_378_checked :
    mulShort n_c43_6 n_d0_6=product_378 := by
  decide +kernel
compact_certificate_declaration theorem product_378_value (v : ℕ→ℂ) :
    eval v product_378=eval v n_c43_6*eval v n_d0_6 := by
  rw [←product_378_checked, eval_mulShort]
compact_certificate_declaration theorem product_379_checked :
    mulShort n_c43_7 n_d0_7=product_379 := by
  decide +kernel
compact_certificate_declaration theorem product_379_value (v : ℕ→ℂ) :
    eval v product_379=eval v n_c43_7*eval v n_d0_7 := by
  rw [←product_379_checked, eval_mulShort]
compact_certificate_declaration theorem product_380_checked :
    mulShort n_c43_8 n_d0_8=product_380 := by
  decide +kernel
compact_certificate_declaration theorem product_380_value (v : ℕ→ℂ) :
    eval v product_380=eval v n_c43_8*eval v n_d0_8 := by
  rw [←product_380_checked, eval_mulShort]
compact_certificate_declaration theorem product_381_checked :
    mulShort n_c43_9 n_d0_9=product_381 := by
  decide +kernel
compact_certificate_declaration theorem product_381_value (v : ℕ→ℂ) :
    eval v product_381=eval v n_c43_9*eval v n_d0_9 := by
  rw [←product_381_checked, eval_mulShort]
compact_certificate_declaration theorem product_382_checked :
    mulShort n_c43_10 n_d0_10=product_382 := by
  decide +kernel
compact_certificate_declaration theorem product_382_value (v : ℕ→ℂ) :
    eval v product_382=eval v n_c43_10*eval v n_d0_10 := by
  rw [←product_382_checked, eval_mulShort]
compact_certificate_declaration theorem product_383_checked :
    mulShort n_c43_11 n_d0_12=product_383 := by
  decide +kernel
compact_certificate_declaration theorem product_383_value (v : ℕ→ℂ) :
    eval v product_383=eval v n_c43_11*eval v n_d0_12 := by
  rw [←product_383_checked, eval_mulShort]
compact_certificate_declaration theorem product_384_checked :
    mulShort n_c43_12 n_d0_13=product_384 := by
  decide +kernel
compact_certificate_declaration theorem product_384_value (v : ℕ→ℂ) :
    eval v product_384=eval v n_c43_12*eval v n_d0_13 := by
  rw [←product_384_checked, eval_mulShort]
compact_certificate_declaration theorem product_385_checked :
    mulShort n_c43_13 n_d0_14=product_385 := by
  decide +kernel
compact_certificate_declaration theorem product_385_value (v : ℕ→ℂ) :
    eval v product_385=eval v n_c43_13*eval v n_d0_14 := by
  rw [←product_385_checked, eval_mulShort]
compact_certificate_declaration theorem product_386_checked :
    mulShort n_c43_14 n_d0_15=product_386 := by
  decide +kernel
compact_certificate_declaration theorem product_386_value (v : ℕ→ℂ) :
    eval v product_386=eval v n_c43_14*eval v n_d0_15 := by
  rw [←product_386_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_72_checked :
    (spadd (spadd (spadd product_379 product_380) (spadd product_381 product_382)) (spadd (spadd product_383 product_384) (spadd product_385 product_386)))=partial_sum_72 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_72_value (v : ℕ→ℂ) :
    eval v partial_sum_72=eval v (spadd (spadd product_379 product_380) (spadd product_381 product_382))+eval v (spadd (spadd product_383 product_384) (spadd product_385 product_386)) := by
  rw [←partial_sum_72_checked, eval_add]
compact_certificate_declaration theorem partial_sum_73_checked :
    (spadd (spadd (spadd product_372 (spadd product_373 product_374)) (spadd (spadd product_375 product_376) (spadd product_377 product_378))) partial_sum_72)=partial_sum_73 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_73_value (v : ℕ→ℂ) :
    eval v partial_sum_73=eval v (spadd (spadd product_372 (spadd product_373 product_374)) (spadd (spadd product_375 product_376) (spadd product_377 product_378)))+eval v partial_sum_72 := by
  rw [←partial_sum_73_checked, eval_add]
compact_certificate_declaration theorem product_387_checked :
    mulShort n_c43_15 n_d0_16=product_387 := by
  decide +kernel
compact_certificate_declaration theorem product_387_value (v : ℕ→ℂ) :
    eval v product_387=eval v n_c43_15*eval v n_d0_16 := by
  rw [←product_387_checked, eval_mulShort]
compact_certificate_declaration theorem product_388_checked :
    mulShort n_c43_16 n_d0_17=product_388 := by
  decide +kernel
compact_certificate_declaration theorem product_388_value (v : ℕ→ℂ) :
    eval v product_388=eval v n_c43_16*eval v n_d0_17 := by
  rw [←product_388_checked, eval_mulShort]
compact_certificate_declaration theorem product_389_checked :
    mulShort n_c43_17 n_d0_18=product_389 := by
  decide +kernel
compact_certificate_declaration theorem product_389_value (v : ℕ→ℂ) :
    eval v product_389=eval v n_c43_17*eval v n_d0_18 := by
  rw [←product_389_checked, eval_mulShort]
compact_certificate_declaration theorem product_390_checked :
    mulShort n_c43_18 n_d0_19=product_390 := by
  decide +kernel
compact_certificate_declaration theorem product_390_value (v : ℕ→ℂ) :
    eval v product_390=eval v n_c43_18*eval v n_d0_19 := by
  rw [←product_390_checked, eval_mulShort]
compact_certificate_declaration theorem product_391_checked :
    mulShort n_c43_19 n_d0_20=product_391 := by
  decide +kernel
compact_certificate_declaration theorem product_391_value (v : ℕ→ℂ) :
    eval v product_391=eval v n_c43_19*eval v n_d0_20 := by
  rw [←product_391_checked, eval_mulShort]
compact_certificate_declaration theorem product_392_checked :
    mulShort n_c43_20 n_d0_21=product_392 := by
  decide +kernel
compact_certificate_declaration theorem product_392_value (v : ℕ→ℂ) :
    eval v product_392=eval v n_c43_20*eval v n_d0_21 := by
  rw [←product_392_checked, eval_mulShort]
compact_certificate_declaration theorem product_393_checked :
    mulShort n_c43_21 n_d0_22=product_393 := by
  decide +kernel
compact_certificate_declaration theorem product_393_value (v : ℕ→ℂ) :
    eval v product_393=eval v n_c43_21*eval v n_d0_22 := by
  rw [←product_393_checked, eval_mulShort]
compact_certificate_declaration theorem product_394_checked :
    mulShort n_c43_22 n_d0_23=product_394 := by
  decide +kernel
compact_certificate_declaration theorem product_394_value (v : ℕ→ℂ) :
    eval v product_394=eval v n_c43_22*eval v n_d0_23 := by
  rw [←product_394_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_74_checked :
    (spadd (spadd (spadd product_387 product_388) (spadd product_389 product_390)) (spadd (spadd product_391 product_392) (spadd product_393 product_394)))=partial_sum_74 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_74_value (v : ℕ→ℂ) :
    eval v partial_sum_74=eval v (spadd (spadd product_387 product_388) (spadd product_389 product_390))+eval v (spadd (spadd product_391 product_392) (spadd product_393 product_394)) := by
  rw [←partial_sum_74_checked, eval_add]
compact_certificate_declaration theorem product_395_checked :
    mulShort n_c43_23 n_d0_24=product_395 := by
  decide +kernel
compact_certificate_declaration theorem product_395_value (v : ℕ→ℂ) :
    eval v product_395=eval v n_c43_23*eval v n_d0_24 := by
  rw [←product_395_checked, eval_mulShort]
compact_certificate_declaration theorem product_396_checked :
    mulShort n_c43_24 n_d0_25=product_396 := by
  decide +kernel
compact_certificate_declaration theorem product_396_value (v : ℕ→ℂ) :
    eval v product_396=eval v n_c43_24*eval v n_d0_25 := by
  rw [←product_396_checked, eval_mulShort]
compact_certificate_declaration theorem product_397_checked :
    mulShort n_c43_25 n_d0_26=product_397 := by
  decide +kernel
compact_certificate_declaration theorem product_397_value (v : ℕ→ℂ) :
    eval v product_397=eval v n_c43_25*eval v n_d0_26 := by
  rw [←product_397_checked, eval_mulShort]
compact_certificate_declaration theorem product_398_checked :
    mulShort n_c43_26 n_d0_27=product_398 := by
  decide +kernel
compact_certificate_declaration theorem product_398_value (v : ℕ→ℂ) :
    eval v product_398=eval v n_c43_26*eval v n_d0_27 := by
  rw [←product_398_checked, eval_mulShort]
compact_certificate_declaration theorem product_399_checked :
    mulShort n_c43_27 n_d0_28=product_399 := by
  decide +kernel
compact_certificate_declaration theorem product_399_value (v : ℕ→ℂ) :
    eval v product_399=eval v n_c43_27*eval v n_d0_28 := by
  rw [←product_399_checked, eval_mulShort]
compact_certificate_declaration theorem product_400_checked :
    mulShort n_c43_28 n_d0_29=product_400 := by
  decide +kernel
compact_certificate_declaration theorem product_400_value (v : ℕ→ℂ) :
    eval v product_400=eval v n_c43_28*eval v n_d0_29 := by
  rw [←product_400_checked, eval_mulShort]
compact_certificate_declaration theorem product_401_checked :
    mulShort n_c43_29 n_d0_30=product_401 := by
  decide +kernel
compact_certificate_declaration theorem product_401_value (v : ℕ→ℂ) :
    eval v product_401=eval v n_c43_29*eval v n_d0_30 := by
  rw [←product_401_checked, eval_mulShort]
compact_certificate_declaration theorem product_402_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c43_30) n_d1_43=product_402 := by
  decide +kernel
compact_certificate_declaration theorem product_402_value (v : ℕ→ℂ) :
    eval v product_402=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c43_30)*eval v n_d1_43 := by
  rw [←product_402_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_75_checked :
    (spadd (spadd (spadd product_395 product_396) (spadd product_397 product_398)) (spadd (spadd product_399 product_400) (spadd product_401 product_402)))=partial_sum_75 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_75_value (v : ℕ→ℂ) :
    eval v partial_sum_75=eval v (spadd (spadd product_395 product_396) (spadd product_397 product_398))+eval v (spadd (spadd product_399 product_400) (spadd product_401 product_402)) := by
  rw [←partial_sum_75_checked, eval_add]
compact_certificate_declaration theorem partial_sum_76_checked :
    (spadd partial_sum_74 partial_sum_75)=partial_sum_76 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_76_value (v : ℕ→ℂ) :
    eval v partial_sum_76=eval v partial_sum_74+eval v partial_sum_75 := by
  rw [←partial_sum_76_checked, eval_add]
compact_certificate_declaration theorem partial_sum_77_checked :
    (spadd partial_sum_73 partial_sum_76)=partial_sum_77 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_77_value (v : ℕ→ℂ) :
    eval v partial_sum_77=eval v partial_sum_73+eval v partial_sum_76 := by
  rw [←partial_sum_77_checked, eval_add]
compact_certificate_declaration theorem checked_12 : checkZero e12=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_12 (y z w a b u : ℂ) :
    (certificate y z w a b u)[12]?=some 0 := by
  change some ((((((c43_0 y z w a b u)*(d0_0 y z w a b u)+((c43_1 y z w a b u)*(d0_1 y z w a b u)+(c43_2 y z w a b u)*(d0_2 y z w a b u)))+(((c43_3 y z w a b u)*(d0_3 y z w a b u)+(c43_4 y z w a b u)*(d0_4 y z w a b u))+((c43_5 y z w a b u)*(d0_5 y z w a b u)+(c43_6 y z w a b u)*(d0_6 y z w a b u))))+((((c43_7 y z w a b u)*(d0_7 y z w a b u)+(c43_8 y z w a b u)*(d0_8 y z w a b u))+((c43_9 y z w a b u)*(d0_9 y z w a b u)+(c43_10 y z w a b u)*(d0_10 y z w a b u)))+(((c43_11 y z w a b u)*(d0_12 y z w a b u)+(c43_12 y z w a b u)*(d0_13 y z w a b u))+((c43_13 y z w a b u)*(d0_14 y z w a b u)+(c43_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c43_15 y z w a b u)*(d0_16 y z w a b u)+(c43_16 y z w a b u)*(d0_17 y z w a b u))+((c43_17 y z w a b u)*(d0_18 y z w a b u)+(c43_18 y z w a b u)*(d0_19 y z w a b u)))+(((c43_19 y z w a b u)*(d0_20 y z w a b u)+(c43_20 y z w a b u)*(d0_21 y z w a b u))+((c43_21 y z w a b u)*(d0_22 y z w a b u)+(c43_22 y z w a b u)*(d0_23 y z w a b u))))+((((c43_23 y z w a b u)*(d0_24 y z w a b u)+(c43_24 y z w a b u)*(d0_25 y z w a b u))+((c43_25 y z w a b u)*(d0_26 y z w a b u)+(c43_26 y z w a b u)*(d0_27 y z w a b u)))+(((c43_27 y z w a b u)*(d0_28 y z w a b u)+(c43_28 y z w a b u)*(d0_29 y z w a b u))+((c43_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c43_30 y z w a b u)*(d1_43 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e12 checked_12
  simp only [e12, eval_add, eval_mul, eval_scale, eval_pow, product_372_value, product_373_value, product_374_value, product_375_value, product_376_value, product_377_value, product_378_value, product_379_value, product_380_value, product_381_value, product_382_value, product_383_value, product_384_value, product_385_value, product_386_value, partial_sum_72_value, partial_sum_73_value, product_387_value, product_388_value, product_389_value, product_390_value, product_391_value, product_392_value, product_393_value, product_394_value, partial_sum_74_value, product_395_value, product_396_value, product_397_value, product_398_value, product_399_value, product_400_value, product_401_value, product_402_value, partial_sum_75_value, partial_sum_76_value, partial_sum_77_value, n_c43_0_value y z w a b u, n_c43_1_value y z w a b u, n_c43_10_value y z w a b u, n_c43_11_value y z w a b u, n_c43_12_value y z w a b u, n_c43_13_value y z w a b u, n_c43_14_value y z w a b u, n_c43_15_value y z w a b u, n_c43_16_value y z w a b u, n_c43_17_value y z w a b u, n_c43_18_value y z w a b u, n_c43_19_value y z w a b u, n_c43_2_value y z w a b u, n_c43_20_value y z w a b u, n_c43_21_value y z w a b u, n_c43_22_value y z w a b u, n_c43_23_value y z w a b u, n_c43_24_value y z w a b u, n_c43_25_value y z w a b u, n_c43_26_value y z w a b u, n_c43_27_value y z w a b u, n_c43_28_value y z w a b u, n_c43_29_value y z w a b u, n_c43_3_value y z w a b u, n_c43_30_value y z w a b u, n_c43_4_value y z w a b u, n_c43_5_value y z w a b u, n_c43_6_value y z w a b u, n_c43_7_value y z w a b u, n_c43_8_value y z w a b u, n_c43_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_43_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_403_checked :
    mulShort n_c44_0 n_d0_0=product_403 := by
  decide +kernel
compact_certificate_declaration theorem product_403_value (v : ℕ→ℂ) :
    eval v product_403=eval v n_c44_0*eval v n_d0_0 := by
  rw [←product_403_checked, eval_mulShort]
compact_certificate_declaration theorem product_404_checked :
    mulShort n_c44_1 n_d0_1=product_404 := by
  decide +kernel
compact_certificate_declaration theorem product_404_value (v : ℕ→ℂ) :
    eval v product_404=eval v n_c44_1*eval v n_d0_1 := by
  rw [←product_404_checked, eval_mulShort]
compact_certificate_declaration theorem product_405_checked :
    mulShort n_c44_2 n_d0_2=product_405 := by
  decide +kernel
compact_certificate_declaration theorem product_405_value (v : ℕ→ℂ) :
    eval v product_405=eval v n_c44_2*eval v n_d0_2 := by
  rw [←product_405_checked, eval_mulShort]
compact_certificate_declaration theorem product_406_checked :
    mulShort n_c44_3 n_d0_3=product_406 := by
  decide +kernel
compact_certificate_declaration theorem product_406_value (v : ℕ→ℂ) :
    eval v product_406=eval v n_c44_3*eval v n_d0_3 := by
  rw [←product_406_checked, eval_mulShort]
compact_certificate_declaration theorem product_407_checked :
    mulShort n_c44_4 n_d0_4=product_407 := by
  decide +kernel
compact_certificate_declaration theorem product_407_value (v : ℕ→ℂ) :
    eval v product_407=eval v n_c44_4*eval v n_d0_4 := by
  rw [←product_407_checked, eval_mulShort]
compact_certificate_declaration theorem product_408_checked :
    mulShort n_c44_5 n_d0_5=product_408 := by
  decide +kernel
compact_certificate_declaration theorem product_408_value (v : ℕ→ℂ) :
    eval v product_408=eval v n_c44_5*eval v n_d0_5 := by
  rw [←product_408_checked, eval_mulShort]
compact_certificate_declaration theorem product_409_checked :
    mulShort n_c44_6 n_d0_6=product_409 := by
  decide +kernel
compact_certificate_declaration theorem product_409_value (v : ℕ→ℂ) :
    eval v product_409=eval v n_c44_6*eval v n_d0_6 := by
  rw [←product_409_checked, eval_mulShort]
compact_certificate_declaration theorem product_410_checked :
    mulShort n_c44_7 n_d0_7=product_410 := by
  decide +kernel
compact_certificate_declaration theorem product_410_value (v : ℕ→ℂ) :
    eval v product_410=eval v n_c44_7*eval v n_d0_7 := by
  rw [←product_410_checked, eval_mulShort]
compact_certificate_declaration theorem product_411_checked :
    mulShort n_c44_8 n_d0_8=product_411 := by
  decide +kernel
compact_certificate_declaration theorem product_411_value (v : ℕ→ℂ) :
    eval v product_411=eval v n_c44_8*eval v n_d0_8 := by
  rw [←product_411_checked, eval_mulShort]
compact_certificate_declaration theorem product_412_checked :
    mulShort n_c44_9 n_d0_9=product_412 := by
  decide +kernel
compact_certificate_declaration theorem product_412_value (v : ℕ→ℂ) :
    eval v product_412=eval v n_c44_9*eval v n_d0_9 := by
  rw [←product_412_checked, eval_mulShort]
compact_certificate_declaration theorem product_413_checked :
    mulShort n_c44_10 n_d0_10=product_413 := by
  decide +kernel
compact_certificate_declaration theorem product_413_value (v : ℕ→ℂ) :
    eval v product_413=eval v n_c44_10*eval v n_d0_10 := by
  rw [←product_413_checked, eval_mulShort]
compact_certificate_declaration theorem product_414_checked :
    mulShort n_c44_11 n_d0_12=product_414 := by
  decide +kernel
compact_certificate_declaration theorem product_414_value (v : ℕ→ℂ) :
    eval v product_414=eval v n_c44_11*eval v n_d0_12 := by
  rw [←product_414_checked, eval_mulShort]
compact_certificate_declaration theorem product_415_checked :
    mulShort n_c44_12 n_d0_13=product_415 := by
  decide +kernel
compact_certificate_declaration theorem product_415_value (v : ℕ→ℂ) :
    eval v product_415=eval v n_c44_12*eval v n_d0_13 := by
  rw [←product_415_checked, eval_mulShort]
compact_certificate_declaration theorem product_416_checked :
    mulShort n_c44_13 n_d0_14=product_416 := by
  decide +kernel
compact_certificate_declaration theorem product_416_value (v : ℕ→ℂ) :
    eval v product_416=eval v n_c44_13*eval v n_d0_14 := by
  rw [←product_416_checked, eval_mulShort]
compact_certificate_declaration theorem product_417_checked :
    mulShort n_c44_14 n_d0_15=product_417 := by
  decide +kernel
compact_certificate_declaration theorem product_417_value (v : ℕ→ℂ) :
    eval v product_417=eval v n_c44_14*eval v n_d0_15 := by
  rw [←product_417_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_78_checked :
    (spadd (spadd (spadd product_410 product_411) (spadd product_412 product_413)) (spadd (spadd product_414 product_415) (spadd product_416 product_417)))=partial_sum_78 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_78_value (v : ℕ→ℂ) :
    eval v partial_sum_78=eval v (spadd (spadd product_410 product_411) (spadd product_412 product_413))+eval v (spadd (spadd product_414 product_415) (spadd product_416 product_417)) := by
  rw [←partial_sum_78_checked, eval_add]
compact_certificate_declaration theorem partial_sum_79_checked :
    (spadd (spadd (spadd product_403 (spadd product_404 product_405)) (spadd (spadd product_406 product_407) (spadd product_408 product_409))) partial_sum_78)=partial_sum_79 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_79_value (v : ℕ→ℂ) :
    eval v partial_sum_79=eval v (spadd (spadd product_403 (spadd product_404 product_405)) (spadd (spadd product_406 product_407) (spadd product_408 product_409)))+eval v partial_sum_78 := by
  rw [←partial_sum_79_checked, eval_add]
compact_certificate_declaration theorem product_418_checked :
    mulShort n_c44_15 n_d0_16=product_418 := by
  decide +kernel
compact_certificate_declaration theorem product_418_value (v : ℕ→ℂ) :
    eval v product_418=eval v n_c44_15*eval v n_d0_16 := by
  rw [←product_418_checked, eval_mulShort]

}
certificate_batch {
compact_certificate_declaration theorem product_419_checked :
    mulShort n_c44_16 n_d0_17=product_419 := by
  decide +kernel
compact_certificate_declaration theorem product_419_value (v : ℕ→ℂ) :
    eval v product_419=eval v n_c44_16*eval v n_d0_17 := by
  rw [←product_419_checked, eval_mulShort]
compact_certificate_declaration theorem product_420_checked :
    mulShort n_c44_17 n_d0_18=product_420 := by
  decide +kernel
compact_certificate_declaration theorem product_420_value (v : ℕ→ℂ) :
    eval v product_420=eval v n_c44_17*eval v n_d0_18 := by
  rw [←product_420_checked, eval_mulShort]
compact_certificate_declaration theorem product_421_checked :
    mulShort n_c44_18 n_d0_19=product_421 := by
  decide +kernel
compact_certificate_declaration theorem product_421_value (v : ℕ→ℂ) :
    eval v product_421=eval v n_c44_18*eval v n_d0_19 := by
  rw [←product_421_checked, eval_mulShort]
compact_certificate_declaration theorem product_422_checked :
    mulShort n_c44_19 n_d0_20=product_422 := by
  decide +kernel
compact_certificate_declaration theorem product_422_value (v : ℕ→ℂ) :
    eval v product_422=eval v n_c44_19*eval v n_d0_20 := by
  rw [←product_422_checked, eval_mulShort]
compact_certificate_declaration theorem product_423_checked :
    mulShort n_c44_20 n_d0_21=product_423 := by
  decide +kernel
compact_certificate_declaration theorem product_423_value (v : ℕ→ℂ) :
    eval v product_423=eval v n_c44_20*eval v n_d0_21 := by
  rw [←product_423_checked, eval_mulShort]
compact_certificate_declaration theorem product_424_checked :
    mulShort n_c44_21 n_d0_22=product_424 := by
  decide +kernel
compact_certificate_declaration theorem product_424_value (v : ℕ→ℂ) :
    eval v product_424=eval v n_c44_21*eval v n_d0_22 := by
  rw [←product_424_checked, eval_mulShort]
compact_certificate_declaration theorem product_425_checked :
    mulShort n_c44_22 n_d0_23=product_425 := by
  decide +kernel
compact_certificate_declaration theorem product_425_value (v : ℕ→ℂ) :
    eval v product_425=eval v n_c44_22*eval v n_d0_23 := by
  rw [←product_425_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_80_checked :
    (spadd (spadd (spadd product_418 product_419) (spadd product_420 product_421)) (spadd (spadd product_422 product_423) (spadd product_424 product_425)))=partial_sum_80 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_80_value (v : ℕ→ℂ) :
    eval v partial_sum_80=eval v (spadd (spadd product_418 product_419) (spadd product_420 product_421))+eval v (spadd (spadd product_422 product_423) (spadd product_424 product_425)) := by
  rw [←partial_sum_80_checked, eval_add]
compact_certificate_declaration theorem product_426_checked :
    mulShort n_c44_23 n_d0_24=product_426 := by
  decide +kernel
compact_certificate_declaration theorem product_426_value (v : ℕ→ℂ) :
    eval v product_426=eval v n_c44_23*eval v n_d0_24 := by
  rw [←product_426_checked, eval_mulShort]
compact_certificate_declaration theorem product_427_checked :
    mulShort n_c44_24 n_d0_25=product_427 := by
  decide +kernel
compact_certificate_declaration theorem product_427_value (v : ℕ→ℂ) :
    eval v product_427=eval v n_c44_24*eval v n_d0_25 := by
  rw [←product_427_checked, eval_mulShort]
compact_certificate_declaration theorem product_428_checked :
    mulShort n_c44_25 n_d0_26=product_428 := by
  decide +kernel
compact_certificate_declaration theorem product_428_value (v : ℕ→ℂ) :
    eval v product_428=eval v n_c44_25*eval v n_d0_26 := by
  rw [←product_428_checked, eval_mulShort]
compact_certificate_declaration theorem product_429_checked :
    mulShort n_c44_26 n_d0_27=product_429 := by
  decide +kernel
compact_certificate_declaration theorem product_429_value (v : ℕ→ℂ) :
    eval v product_429=eval v n_c44_26*eval v n_d0_27 := by
  rw [←product_429_checked, eval_mulShort]
compact_certificate_declaration theorem product_430_checked :
    mulShort n_c44_27 n_d0_28=product_430 := by
  decide +kernel
compact_certificate_declaration theorem product_430_value (v : ℕ→ℂ) :
    eval v product_430=eval v n_c44_27*eval v n_d0_28 := by
  rw [←product_430_checked, eval_mulShort]
compact_certificate_declaration theorem product_431_checked :
    mulShort n_c44_28 n_d0_29=product_431 := by
  decide +kernel
compact_certificate_declaration theorem product_431_value (v : ℕ→ℂ) :
    eval v product_431=eval v n_c44_28*eval v n_d0_29 := by
  rw [←product_431_checked, eval_mulShort]
compact_certificate_declaration theorem product_432_checked :
    mulShort n_c44_29 n_d0_30=product_432 := by
  decide +kernel
compact_certificate_declaration theorem product_432_value (v : ℕ→ℂ) :
    eval v product_432=eval v n_c44_29*eval v n_d0_30 := by
  rw [←product_432_checked, eval_mulShort]
compact_certificate_declaration theorem product_433_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c44_30) n_d1_44=product_433 := by
  decide +kernel
compact_certificate_declaration theorem product_433_value (v : ℕ→ℂ) :
    eval v product_433=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c44_30)*eval v n_d1_44 := by
  rw [←product_433_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_81_checked :
    (spadd (spadd (spadd product_426 product_427) (spadd product_428 product_429)) (spadd (spadd product_430 product_431) (spadd product_432 product_433)))=partial_sum_81 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_81_value (v : ℕ→ℂ) :
    eval v partial_sum_81=eval v (spadd (spadd product_426 product_427) (spadd product_428 product_429))+eval v (spadd (spadd product_430 product_431) (spadd product_432 product_433)) := by
  rw [←partial_sum_81_checked, eval_add]
compact_certificate_declaration theorem partial_sum_82_checked :
    (spadd partial_sum_80 partial_sum_81)=partial_sum_82 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_82_value (v : ℕ→ℂ) :
    eval v partial_sum_82=eval v partial_sum_80+eval v partial_sum_81 := by
  rw [←partial_sum_82_checked, eval_add]
compact_certificate_declaration theorem partial_sum_83_checked :
    (spadd partial_sum_79 partial_sum_82)=partial_sum_83 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_83_value (v : ℕ→ℂ) :
    eval v partial_sum_83=eval v partial_sum_79+eval v partial_sum_82 := by
  rw [←partial_sum_83_checked, eval_add]
compact_certificate_declaration theorem checked_13 : checkZero e13=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_13 (y z w a b u : ℂ) :
    (certificate y z w a b u)[13]?=some 0 := by
  change some ((((((c44_0 y z w a b u)*(d0_0 y z w a b u)+((c44_1 y z w a b u)*(d0_1 y z w a b u)+(c44_2 y z w a b u)*(d0_2 y z w a b u)))+(((c44_3 y z w a b u)*(d0_3 y z w a b u)+(c44_4 y z w a b u)*(d0_4 y z w a b u))+((c44_5 y z w a b u)*(d0_5 y z w a b u)+(c44_6 y z w a b u)*(d0_6 y z w a b u))))+((((c44_7 y z w a b u)*(d0_7 y z w a b u)+(c44_8 y z w a b u)*(d0_8 y z w a b u))+((c44_9 y z w a b u)*(d0_9 y z w a b u)+(c44_10 y z w a b u)*(d0_10 y z w a b u)))+(((c44_11 y z w a b u)*(d0_12 y z w a b u)+(c44_12 y z w a b u)*(d0_13 y z w a b u))+((c44_13 y z w a b u)*(d0_14 y z w a b u)+(c44_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c44_15 y z w a b u)*(d0_16 y z w a b u)+(c44_16 y z w a b u)*(d0_17 y z w a b u))+((c44_17 y z w a b u)*(d0_18 y z w a b u)+(c44_18 y z w a b u)*(d0_19 y z w a b u)))+(((c44_19 y z w a b u)*(d0_20 y z w a b u)+(c44_20 y z w a b u)*(d0_21 y z w a b u))+((c44_21 y z w a b u)*(d0_22 y z w a b u)+(c44_22 y z w a b u)*(d0_23 y z w a b u))))+((((c44_23 y z w a b u)*(d0_24 y z w a b u)+(c44_24 y z w a b u)*(d0_25 y z w a b u))+((c44_25 y z w a b u)*(d0_26 y z w a b u)+(c44_26 y z w a b u)*(d0_27 y z w a b u)))+(((c44_27 y z w a b u)*(d0_28 y z w a b u)+(c44_28 y z w a b u)*(d0_29 y z w a b u))+((c44_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c44_30 y z w a b u)*(d1_44 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e13 checked_13
  simp only [e13, eval_add, eval_mul, eval_scale, eval_pow, product_403_value, product_404_value, product_405_value, product_406_value, product_407_value, product_408_value, product_409_value, product_410_value, product_411_value, product_412_value, product_413_value, product_414_value, product_415_value, product_416_value, product_417_value, partial_sum_78_value, partial_sum_79_value, product_418_value, product_419_value, product_420_value, product_421_value, product_422_value, product_423_value, product_424_value, product_425_value, partial_sum_80_value, product_426_value, product_427_value, product_428_value, product_429_value, product_430_value, product_431_value, product_432_value, product_433_value, partial_sum_81_value, partial_sum_82_value, partial_sum_83_value, n_c44_0_value y z w a b u, n_c44_1_value y z w a b u, n_c44_10_value y z w a b u, n_c44_11_value y z w a b u, n_c44_12_value y z w a b u, n_c44_13_value y z w a b u, n_c44_14_value y z w a b u, n_c44_15_value y z w a b u, n_c44_16_value y z w a b u, n_c44_17_value y z w a b u, n_c44_18_value y z w a b u, n_c44_19_value y z w a b u, n_c44_2_value y z w a b u, n_c44_20_value y z w a b u, n_c44_21_value y z w a b u, n_c44_22_value y z w a b u, n_c44_23_value y z w a b u, n_c44_24_value y z w a b u, n_c44_25_value y z w a b u, n_c44_26_value y z w a b u, n_c44_27_value y z w a b u, n_c44_28_value y z w a b u, n_c44_29_value y z w a b u, n_c44_3_value y z w a b u, n_c44_30_value y z w a b u, n_c44_4_value y z w a b u, n_c44_5_value y z w a b u, n_c44_6_value y z w a b u, n_c44_7_value y z w a b u, n_c44_8_value y z w a b u, n_c44_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_44_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_434_checked :
    mulShort n_c45_0 n_d0_0=product_434 := by
  decide +kernel
compact_certificate_declaration theorem product_434_value (v : ℕ→ℂ) :
    eval v product_434=eval v n_c45_0*eval v n_d0_0 := by
  rw [←product_434_checked, eval_mulShort]
compact_certificate_declaration theorem product_435_checked :
    mulShort n_c45_1 n_d0_1=product_435 := by
  decide +kernel
compact_certificate_declaration theorem product_435_value (v : ℕ→ℂ) :
    eval v product_435=eval v n_c45_1*eval v n_d0_1 := by
  rw [←product_435_checked, eval_mulShort]
compact_certificate_declaration theorem product_436_checked :
    mulShort n_c45_2 n_d0_2=product_436 := by
  decide +kernel
compact_certificate_declaration theorem product_436_value (v : ℕ→ℂ) :
    eval v product_436=eval v n_c45_2*eval v n_d0_2 := by
  rw [←product_436_checked, eval_mulShort]
compact_certificate_declaration theorem product_437_checked :
    mulShort n_c45_3 n_d0_3=product_437 := by
  decide +kernel
compact_certificate_declaration theorem product_437_value (v : ℕ→ℂ) :
    eval v product_437=eval v n_c45_3*eval v n_d0_3 := by
  rw [←product_437_checked, eval_mulShort]
compact_certificate_declaration theorem product_438_checked :
    mulShort n_c45_4 n_d0_4=product_438 := by
  decide +kernel
compact_certificate_declaration theorem product_438_value (v : ℕ→ℂ) :
    eval v product_438=eval v n_c45_4*eval v n_d0_4 := by
  rw [←product_438_checked, eval_mulShort]
compact_certificate_declaration theorem product_439_checked :
    mulShort n_c45_5 n_d0_5=product_439 := by
  decide +kernel
compact_certificate_declaration theorem product_439_value (v : ℕ→ℂ) :
    eval v product_439=eval v n_c45_5*eval v n_d0_5 := by
  rw [←product_439_checked, eval_mulShort]
compact_certificate_declaration theorem product_440_checked :
    mulShort n_c45_6 n_d0_6=product_440 := by
  decide +kernel
compact_certificate_declaration theorem product_440_value (v : ℕ→ℂ) :
    eval v product_440=eval v n_c45_6*eval v n_d0_6 := by
  rw [←product_440_checked, eval_mulShort]
compact_certificate_declaration theorem product_441_checked :
    mulShort n_c45_7 n_d0_7=product_441 := by
  decide +kernel
compact_certificate_declaration theorem product_441_value (v : ℕ→ℂ) :
    eval v product_441=eval v n_c45_7*eval v n_d0_7 := by
  rw [←product_441_checked, eval_mulShort]
compact_certificate_declaration theorem product_442_checked :
    mulShort n_c45_8 n_d0_8=product_442 := by
  decide +kernel
compact_certificate_declaration theorem product_442_value (v : ℕ→ℂ) :
    eval v product_442=eval v n_c45_8*eval v n_d0_8 := by
  rw [←product_442_checked, eval_mulShort]
compact_certificate_declaration theorem product_443_checked :
    mulShort n_c45_9 n_d0_9=product_443 := by
  decide +kernel
compact_certificate_declaration theorem product_443_value (v : ℕ→ℂ) :
    eval v product_443=eval v n_c45_9*eval v n_d0_9 := by
  rw [←product_443_checked, eval_mulShort]
compact_certificate_declaration theorem product_444_checked :
    mulShort n_c45_10 n_d0_10=product_444 := by
  decide +kernel
compact_certificate_declaration theorem product_444_value (v : ℕ→ℂ) :
    eval v product_444=eval v n_c45_10*eval v n_d0_10 := by
  rw [←product_444_checked, eval_mulShort]
compact_certificate_declaration theorem product_445_checked :
    mulShort n_c45_11 n_d0_12=product_445 := by
  decide +kernel
compact_certificate_declaration theorem product_445_value (v : ℕ→ℂ) :
    eval v product_445=eval v n_c45_11*eval v n_d0_12 := by
  rw [←product_445_checked, eval_mulShort]
compact_certificate_declaration theorem product_446_checked :
    mulShort n_c45_12 n_d0_13=product_446 := by
  decide +kernel
compact_certificate_declaration theorem product_446_value (v : ℕ→ℂ) :
    eval v product_446=eval v n_c45_12*eval v n_d0_13 := by
  rw [←product_446_checked, eval_mulShort]
compact_certificate_declaration theorem product_447_checked :
    mulShort n_c45_13 n_d0_14=product_447 := by
  decide +kernel
compact_certificate_declaration theorem product_447_value (v : ℕ→ℂ) :
    eval v product_447=eval v n_c45_13*eval v n_d0_14 := by
  rw [←product_447_checked, eval_mulShort]
compact_certificate_declaration theorem product_448_checked :
    mulShort n_c45_14 n_d0_15=product_448 := by
  decide +kernel
compact_certificate_declaration theorem product_448_value (v : ℕ→ℂ) :
    eval v product_448=eval v n_c45_14*eval v n_d0_15 := by
  rw [←product_448_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_84_checked :
    (spadd (spadd (spadd product_441 product_442) (spadd product_443 product_444)) (spadd (spadd product_445 product_446) (spadd product_447 product_448)))=partial_sum_84 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_84_value (v : ℕ→ℂ) :
    eval v partial_sum_84=eval v (spadd (spadd product_441 product_442) (spadd product_443 product_444))+eval v (spadd (spadd product_445 product_446) (spadd product_447 product_448)) := by
  rw [←partial_sum_84_checked, eval_add]
compact_certificate_declaration theorem partial_sum_85_checked :
    (spadd (spadd (spadd product_434 (spadd product_435 product_436)) (spadd (spadd product_437 product_438) (spadd product_439 product_440))) partial_sum_84)=partial_sum_85 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_85_value (v : ℕ→ℂ) :
    eval v partial_sum_85=eval v (spadd (spadd product_434 (spadd product_435 product_436)) (spadd (spadd product_437 product_438) (spadd product_439 product_440)))+eval v partial_sum_84 := by
  rw [←partial_sum_85_checked, eval_add]
compact_certificate_declaration theorem product_449_checked :
    mulShort n_c45_15 n_d0_16=product_449 := by
  decide +kernel
compact_certificate_declaration theorem product_449_value (v : ℕ→ℂ) :
    eval v product_449=eval v n_c45_15*eval v n_d0_16 := by
  rw [←product_449_checked, eval_mulShort]
compact_certificate_declaration theorem product_450_checked :
    mulShort n_c45_16 n_d0_17=product_450 := by
  decide +kernel
compact_certificate_declaration theorem product_450_value (v : ℕ→ℂ) :
    eval v product_450=eval v n_c45_16*eval v n_d0_17 := by
  rw [←product_450_checked, eval_mulShort]
compact_certificate_declaration theorem product_451_checked :
    mulShort n_c45_17 n_d0_18=product_451 := by
  decide +kernel
compact_certificate_declaration theorem product_451_value (v : ℕ→ℂ) :
    eval v product_451=eval v n_c45_17*eval v n_d0_18 := by
  rw [←product_451_checked, eval_mulShort]
compact_certificate_declaration theorem product_452_checked :
    mulShort n_c45_18 n_d0_19=product_452 := by
  decide +kernel
compact_certificate_declaration theorem product_452_value (v : ℕ→ℂ) :
    eval v product_452=eval v n_c45_18*eval v n_d0_19 := by
  rw [←product_452_checked, eval_mulShort]
compact_certificate_declaration theorem product_453_checked :
    mulShort n_c45_19 n_d0_20=product_453 := by
  decide +kernel
compact_certificate_declaration theorem product_453_value (v : ℕ→ℂ) :
    eval v product_453=eval v n_c45_19*eval v n_d0_20 := by
  rw [←product_453_checked, eval_mulShort]
compact_certificate_declaration theorem product_454_checked :
    mulShort n_c45_20 n_d0_21=product_454 := by
  decide +kernel
compact_certificate_declaration theorem product_454_value (v : ℕ→ℂ) :
    eval v product_454=eval v n_c45_20*eval v n_d0_21 := by
  rw [←product_454_checked, eval_mulShort]
compact_certificate_declaration theorem product_455_checked :
    mulShort n_c45_21 n_d0_22=product_455 := by
  decide +kernel
compact_certificate_declaration theorem product_455_value (v : ℕ→ℂ) :
    eval v product_455=eval v n_c45_21*eval v n_d0_22 := by
  rw [←product_455_checked, eval_mulShort]
compact_certificate_declaration theorem product_456_checked :
    mulShort n_c45_22 n_d0_23=product_456 := by
  decide +kernel
compact_certificate_declaration theorem product_456_value (v : ℕ→ℂ) :
    eval v product_456=eval v n_c45_22*eval v n_d0_23 := by
  rw [←product_456_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_86_checked :
    (spadd (spadd (spadd product_449 product_450) (spadd product_451 product_452)) (spadd (spadd product_453 product_454) (spadd product_455 product_456)))=partial_sum_86 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_86_value (v : ℕ→ℂ) :
    eval v partial_sum_86=eval v (spadd (spadd product_449 product_450) (spadd product_451 product_452))+eval v (spadd (spadd product_453 product_454) (spadd product_455 product_456)) := by
  rw [←partial_sum_86_checked, eval_add]
compact_certificate_declaration theorem product_457_checked :
    mulShort n_c45_23 n_d0_24=product_457 := by
  decide +kernel
compact_certificate_declaration theorem product_457_value (v : ℕ→ℂ) :
    eval v product_457=eval v n_c45_23*eval v n_d0_24 := by
  rw [←product_457_checked, eval_mulShort]
compact_certificate_declaration theorem product_458_checked :
    mulShort n_c45_24 n_d0_25=product_458 := by
  decide +kernel
compact_certificate_declaration theorem product_458_value (v : ℕ→ℂ) :
    eval v product_458=eval v n_c45_24*eval v n_d0_25 := by
  rw [←product_458_checked, eval_mulShort]
compact_certificate_declaration theorem product_459_checked :
    mulShort n_c45_25 n_d0_26=product_459 := by
  decide +kernel
compact_certificate_declaration theorem product_459_value (v : ℕ→ℂ) :
    eval v product_459=eval v n_c45_25*eval v n_d0_26 := by
  rw [←product_459_checked, eval_mulShort]
compact_certificate_declaration theorem product_460_checked :
    mulShort n_c45_26 n_d0_27=product_460 := by
  decide +kernel
compact_certificate_declaration theorem product_460_value (v : ℕ→ℂ) :
    eval v product_460=eval v n_c45_26*eval v n_d0_27 := by
  rw [←product_460_checked, eval_mulShort]
compact_certificate_declaration theorem product_461_checked :
    mulShort n_c45_27 n_d0_28=product_461 := by
  decide +kernel
compact_certificate_declaration theorem product_461_value (v : ℕ→ℂ) :
    eval v product_461=eval v n_c45_27*eval v n_d0_28 := by
  rw [←product_461_checked, eval_mulShort]
compact_certificate_declaration theorem product_462_checked :
    mulShort n_c45_28 n_d0_29=product_462 := by
  decide +kernel
compact_certificate_declaration theorem product_462_value (v : ℕ→ℂ) :
    eval v product_462=eval v n_c45_28*eval v n_d0_29 := by
  rw [←product_462_checked, eval_mulShort]
compact_certificate_declaration theorem product_463_checked :
    mulShort n_c45_29 n_d0_30=product_463 := by
  decide +kernel
compact_certificate_declaration theorem product_463_value (v : ℕ→ℂ) :
    eval v product_463=eval v n_c45_29*eval v n_d0_30 := by
  rw [←product_463_checked, eval_mulShort]
compact_certificate_declaration theorem product_464_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c45_30) n_d1_45=product_464 := by
  decide +kernel
compact_certificate_declaration theorem product_464_value (v : ℕ→ℂ) :
    eval v product_464=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c45_30)*eval v n_d1_45 := by
  rw [←product_464_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_87_checked :
    (spadd (spadd (spadd product_457 product_458) (spadd product_459 product_460)) (spadd (spadd product_461 product_462) (spadd product_463 product_464)))=partial_sum_87 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_87_value (v : ℕ→ℂ) :
    eval v partial_sum_87=eval v (spadd (spadd product_457 product_458) (spadd product_459 product_460))+eval v (spadd (spadd product_461 product_462) (spadd product_463 product_464)) := by
  rw [←partial_sum_87_checked, eval_add]
compact_certificate_declaration theorem partial_sum_88_checked :
    (spadd partial_sum_86 partial_sum_87)=partial_sum_88 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_88_value (v : ℕ→ℂ) :
    eval v partial_sum_88=eval v partial_sum_86+eval v partial_sum_87 := by
  rw [←partial_sum_88_checked, eval_add]
compact_certificate_declaration theorem partial_sum_89_checked :
    (spadd partial_sum_85 partial_sum_88)=partial_sum_89 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_89_value (v : ℕ→ℂ) :
    eval v partial_sum_89=eval v partial_sum_85+eval v partial_sum_88 := by
  rw [←partial_sum_89_checked, eval_add]
compact_certificate_declaration theorem checked_14 : checkZero e14=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_14 (y z w a b u : ℂ) :
    (certificate y z w a b u)[14]?=some 0 := by
  change some ((((((c45_0 y z w a b u)*(d0_0 y z w a b u)+((c45_1 y z w a b u)*(d0_1 y z w a b u)+(c45_2 y z w a b u)*(d0_2 y z w a b u)))+(((c45_3 y z w a b u)*(d0_3 y z w a b u)+(c45_4 y z w a b u)*(d0_4 y z w a b u))+((c45_5 y z w a b u)*(d0_5 y z w a b u)+(c45_6 y z w a b u)*(d0_6 y z w a b u))))+((((c45_7 y z w a b u)*(d0_7 y z w a b u)+(c45_8 y z w a b u)*(d0_8 y z w a b u))+((c45_9 y z w a b u)*(d0_9 y z w a b u)+(c45_10 y z w a b u)*(d0_10 y z w a b u)))+(((c45_11 y z w a b u)*(d0_12 y z w a b u)+(c45_12 y z w a b u)*(d0_13 y z w a b u))+((c45_13 y z w a b u)*(d0_14 y z w a b u)+(c45_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c45_15 y z w a b u)*(d0_16 y z w a b u)+(c45_16 y z w a b u)*(d0_17 y z w a b u))+((c45_17 y z w a b u)*(d0_18 y z w a b u)+(c45_18 y z w a b u)*(d0_19 y z w a b u)))+(((c45_19 y z w a b u)*(d0_20 y z w a b u)+(c45_20 y z w a b u)*(d0_21 y z w a b u))+((c45_21 y z w a b u)*(d0_22 y z w a b u)+(c45_22 y z w a b u)*(d0_23 y z w a b u))))+((((c45_23 y z w a b u)*(d0_24 y z w a b u)+(c45_24 y z w a b u)*(d0_25 y z w a b u))+((c45_25 y z w a b u)*(d0_26 y z w a b u)+(c45_26 y z w a b u)*(d0_27 y z w a b u)))+(((c45_27 y z w a b u)*(d0_28 y z w a b u)+(c45_28 y z w a b u)*(d0_29 y z w a b u))+((c45_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c45_30 y z w a b u)*(d1_45 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e14 checked_14
  simp only [e14, eval_add, eval_mul, eval_scale, eval_pow, product_434_value, product_435_value, product_436_value, product_437_value, product_438_value, product_439_value, product_440_value, product_441_value, product_442_value, product_443_value, product_444_value, product_445_value, product_446_value, product_447_value, product_448_value, partial_sum_84_value, partial_sum_85_value, product_449_value, product_450_value, product_451_value, product_452_value, product_453_value, product_454_value, product_455_value, product_456_value, partial_sum_86_value, product_457_value, product_458_value, product_459_value, product_460_value, product_461_value, product_462_value, product_463_value, product_464_value, partial_sum_87_value, partial_sum_88_value, partial_sum_89_value, n_c45_0_value y z w a b u, n_c45_1_value y z w a b u, n_c45_10_value y z w a b u, n_c45_11_value y z w a b u, n_c45_12_value y z w a b u, n_c45_13_value y z w a b u, n_c45_14_value y z w a b u, n_c45_15_value y z w a b u, n_c45_16_value y z w a b u, n_c45_17_value y z w a b u, n_c45_18_value y z w a b u, n_c45_19_value y z w a b u, n_c45_2_value y z w a b u, n_c45_20_value y z w a b u, n_c45_21_value y z w a b u, n_c45_22_value y z w a b u, n_c45_23_value y z w a b u, n_c45_24_value y z w a b u, n_c45_25_value y z w a b u, n_c45_26_value y z w a b u, n_c45_27_value y z w a b u, n_c45_28_value y z w a b u, n_c45_29_value y z w a b u, n_c45_3_value y z w a b u, n_c45_30_value y z w a b u, n_c45_4_value y z w a b u, n_c45_5_value y z w a b u, n_c45_6_value y z w a b u, n_c45_7_value y z w a b u, n_c45_8_value y z w a b u, n_c45_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_45_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_465_checked :
    mulShort n_c46_0 n_d0_0=product_465 := by
  decide +kernel
compact_certificate_declaration theorem product_465_value (v : ℕ→ℂ) :
    eval v product_465=eval v n_c46_0*eval v n_d0_0 := by
  rw [←product_465_checked, eval_mulShort]
compact_certificate_declaration theorem product_466_checked :
    mulShort n_c46_1 n_d0_1=product_466 := by
  decide +kernel
compact_certificate_declaration theorem product_466_value (v : ℕ→ℂ) :
    eval v product_466=eval v n_c46_1*eval v n_d0_1 := by
  rw [←product_466_checked, eval_mulShort]
compact_certificate_declaration theorem product_467_checked :
    mulShort n_c46_2 n_d0_2=product_467 := by
  decide +kernel
compact_certificate_declaration theorem product_467_value (v : ℕ→ℂ) :
    eval v product_467=eval v n_c46_2*eval v n_d0_2 := by
  rw [←product_467_checked, eval_mulShort]
compact_certificate_declaration theorem product_468_checked :
    mulShort n_c46_3 n_d0_3=product_468 := by
  decide +kernel
compact_certificate_declaration theorem product_468_value (v : ℕ→ℂ) :
    eval v product_468=eval v n_c46_3*eval v n_d0_3 := by
  rw [←product_468_checked, eval_mulShort]
compact_certificate_declaration theorem product_469_checked :
    mulShort n_c46_4 n_d0_4=product_469 := by
  decide +kernel
compact_certificate_declaration theorem product_469_value (v : ℕ→ℂ) :
    eval v product_469=eval v n_c46_4*eval v n_d0_4 := by
  rw [←product_469_checked, eval_mulShort]
compact_certificate_declaration theorem product_470_checked :
    mulShort n_c46_5 n_d0_5=product_470 := by
  decide +kernel
compact_certificate_declaration theorem product_470_value (v : ℕ→ℂ) :
    eval v product_470=eval v n_c46_5*eval v n_d0_5 := by
  rw [←product_470_checked, eval_mulShort]
compact_certificate_declaration theorem product_471_checked :
    mulShort n_c46_6 n_d0_6=product_471 := by
  decide +kernel
compact_certificate_declaration theorem product_471_value (v : ℕ→ℂ) :
    eval v product_471=eval v n_c46_6*eval v n_d0_6 := by
  rw [←product_471_checked, eval_mulShort]
compact_certificate_declaration theorem product_472_checked :
    mulShort n_c46_7 n_d0_7=product_472 := by
  decide +kernel
compact_certificate_declaration theorem product_472_value (v : ℕ→ℂ) :
    eval v product_472=eval v n_c46_7*eval v n_d0_7 := by
  rw [←product_472_checked, eval_mulShort]
compact_certificate_declaration theorem product_473_checked :
    mulShort n_c46_8 n_d0_8=product_473 := by
  decide +kernel
compact_certificate_declaration theorem product_473_value (v : ℕ→ℂ) :
    eval v product_473=eval v n_c46_8*eval v n_d0_8 := by
  rw [←product_473_checked, eval_mulShort]
compact_certificate_declaration theorem product_474_checked :
    mulShort n_c46_9 n_d0_9=product_474 := by
  decide +kernel
compact_certificate_declaration theorem product_474_value (v : ℕ→ℂ) :
    eval v product_474=eval v n_c46_9*eval v n_d0_9 := by
  rw [←product_474_checked, eval_mulShort]
compact_certificate_declaration theorem product_475_checked :
    mulShort n_c46_10 n_d0_10=product_475 := by
  decide +kernel
compact_certificate_declaration theorem product_475_value (v : ℕ→ℂ) :
    eval v product_475=eval v n_c46_10*eval v n_d0_10 := by
  rw [←product_475_checked, eval_mulShort]
compact_certificate_declaration theorem product_476_checked :
    mulShort n_c46_11 n_d0_12=product_476 := by
  decide +kernel
compact_certificate_declaration theorem product_476_value (v : ℕ→ℂ) :
    eval v product_476=eval v n_c46_11*eval v n_d0_12 := by
  rw [←product_476_checked, eval_mulShort]
compact_certificate_declaration theorem product_477_checked :
    mulShort n_c46_12 n_d0_13=product_477 := by
  decide +kernel
compact_certificate_declaration theorem product_477_value (v : ℕ→ℂ) :
    eval v product_477=eval v n_c46_12*eval v n_d0_13 := by
  rw [←product_477_checked, eval_mulShort]
compact_certificate_declaration theorem product_478_checked :
    mulShort n_c46_13 n_d0_14=product_478 := by
  decide +kernel
compact_certificate_declaration theorem product_478_value (v : ℕ→ℂ) :
    eval v product_478=eval v n_c46_13*eval v n_d0_14 := by
  rw [←product_478_checked, eval_mulShort]
compact_certificate_declaration theorem product_479_checked :
    mulShort n_c46_14 n_d0_15=product_479 := by
  decide +kernel
compact_certificate_declaration theorem product_479_value (v : ℕ→ℂ) :
    eval v product_479=eval v n_c46_14*eval v n_d0_15 := by
  rw [←product_479_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_90_checked :
    (spadd (spadd (spadd product_472 product_473) (spadd product_474 product_475)) (spadd (spadd product_476 product_477) (spadd product_478 product_479)))=partial_sum_90 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_90_value (v : ℕ→ℂ) :
    eval v partial_sum_90=eval v (spadd (spadd product_472 product_473) (spadd product_474 product_475))+eval v (spadd (spadd product_476 product_477) (spadd product_478 product_479)) := by
  rw [←partial_sum_90_checked, eval_add]
compact_certificate_declaration theorem partial_sum_91_checked :
    (spadd (spadd (spadd product_465 (spadd product_466 product_467)) (spadd (spadd product_468 product_469) (spadd product_470 product_471))) partial_sum_90)=partial_sum_91 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_91_value (v : ℕ→ℂ) :
    eval v partial_sum_91=eval v (spadd (spadd product_465 (spadd product_466 product_467)) (spadd (spadd product_468 product_469) (spadd product_470 product_471)))+eval v partial_sum_90 := by
  rw [←partial_sum_91_checked, eval_add]
compact_certificate_declaration theorem product_480_checked :
    mulShort n_c46_15 n_d0_16=product_480 := by
  decide +kernel
compact_certificate_declaration theorem product_480_value (v : ℕ→ℂ) :
    eval v product_480=eval v n_c46_15*eval v n_d0_16 := by
  rw [←product_480_checked, eval_mulShort]
compact_certificate_declaration theorem product_481_checked :
    mulShort n_c46_16 n_d0_17=product_481 := by
  decide +kernel
compact_certificate_declaration theorem product_481_value (v : ℕ→ℂ) :
    eval v product_481=eval v n_c46_16*eval v n_d0_17 := by
  rw [←product_481_checked, eval_mulShort]
compact_certificate_declaration theorem product_482_checked :
    mulShort n_c46_17 n_d0_18=product_482 := by
  decide +kernel
compact_certificate_declaration theorem product_482_value (v : ℕ→ℂ) :
    eval v product_482=eval v n_c46_17*eval v n_d0_18 := by
  rw [←product_482_checked, eval_mulShort]
compact_certificate_declaration theorem product_483_checked :
    mulShort n_c46_18 n_d0_19=product_483 := by
  decide +kernel
compact_certificate_declaration theorem product_483_value (v : ℕ→ℂ) :
    eval v product_483=eval v n_c46_18*eval v n_d0_19 := by
  rw [←product_483_checked, eval_mulShort]
compact_certificate_declaration theorem product_484_checked :
    mulShort n_c46_19 n_d0_20=product_484 := by
  decide +kernel
compact_certificate_declaration theorem product_484_value (v : ℕ→ℂ) :
    eval v product_484=eval v n_c46_19*eval v n_d0_20 := by
  rw [←product_484_checked, eval_mulShort]
compact_certificate_declaration theorem product_485_checked :
    mulShort n_c46_20 n_d0_21=product_485 := by
  decide +kernel
compact_certificate_declaration theorem product_485_value (v : ℕ→ℂ) :
    eval v product_485=eval v n_c46_20*eval v n_d0_21 := by
  rw [←product_485_checked, eval_mulShort]
compact_certificate_declaration theorem product_486_checked :
    mulShort n_c46_21 n_d0_22=product_486 := by
  decide +kernel
compact_certificate_declaration theorem product_486_value (v : ℕ→ℂ) :
    eval v product_486=eval v n_c46_21*eval v n_d0_22 := by
  rw [←product_486_checked, eval_mulShort]
compact_certificate_declaration theorem product_487_checked :
    mulShort n_c46_22 n_d0_23=product_487 := by
  decide +kernel
compact_certificate_declaration theorem product_487_value (v : ℕ→ℂ) :
    eval v product_487=eval v n_c46_22*eval v n_d0_23 := by
  rw [←product_487_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_92_checked :
    (spadd (spadd (spadd product_480 product_481) (spadd product_482 product_483)) (spadd (spadd product_484 product_485) (spadd product_486 product_487)))=partial_sum_92 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_92_value (v : ℕ→ℂ) :
    eval v partial_sum_92=eval v (spadd (spadd product_480 product_481) (spadd product_482 product_483))+eval v (spadd (spadd product_484 product_485) (spadd product_486 product_487)) := by
  rw [←partial_sum_92_checked, eval_add]
compact_certificate_declaration theorem product_488_checked :
    mulShort n_c46_23 n_d0_24=product_488 := by
  decide +kernel
compact_certificate_declaration theorem product_488_value (v : ℕ→ℂ) :
    eval v product_488=eval v n_c46_23*eval v n_d0_24 := by
  rw [←product_488_checked, eval_mulShort]

compact_certificate_declaration theorem product_489_checked :
    mulShort n_c46_24 n_d0_25=product_489 := by
  decide +kernel
compact_certificate_declaration theorem product_489_value (v : ℕ→ℂ) :
    eval v product_489=eval v n_c46_24*eval v n_d0_25 := by
  rw [←product_489_checked, eval_mulShort]
compact_certificate_declaration theorem product_490_checked :
    mulShort n_c46_25 n_d0_26=product_490 := by
  decide +kernel
compact_certificate_declaration theorem product_490_value (v : ℕ→ℂ) :
    eval v product_490=eval v n_c46_25*eval v n_d0_26 := by
  rw [←product_490_checked, eval_mulShort]
compact_certificate_declaration theorem product_491_checked :
    mulShort n_c46_26 n_d0_27=product_491 := by
  decide +kernel
compact_certificate_declaration theorem product_491_value (v : ℕ→ℂ) :
    eval v product_491=eval v n_c46_26*eval v n_d0_27 := by
  rw [←product_491_checked, eval_mulShort]
compact_certificate_declaration theorem product_492_checked :
    mulShort n_c46_27 n_d0_28=product_492 := by
  decide +kernel
compact_certificate_declaration theorem product_492_value (v : ℕ→ℂ) :
    eval v product_492=eval v n_c46_27*eval v n_d0_28 := by
  rw [←product_492_checked, eval_mulShort]
compact_certificate_declaration theorem product_493_checked :
    mulShort n_c46_28 n_d0_29=product_493 := by
  decide +kernel
compact_certificate_declaration theorem product_493_value (v : ℕ→ℂ) :
    eval v product_493=eval v n_c46_28*eval v n_d0_29 := by
  rw [←product_493_checked, eval_mulShort]
compact_certificate_declaration theorem product_494_checked :
    mulShort n_c46_29 n_d0_30=product_494 := by
  decide +kernel
compact_certificate_declaration theorem product_494_value (v : ℕ→ℂ) :
    eval v product_494=eval v n_c46_29*eval v n_d0_30 := by
  rw [←product_494_checked, eval_mulShort]
compact_certificate_declaration theorem product_495_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c46_30) n_d1_46=product_495 := by
  decide +kernel
compact_certificate_declaration theorem product_495_value (v : ℕ→ℂ) :
    eval v product_495=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c46_30)*eval v n_d1_46 := by
  rw [←product_495_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_93_checked :
    (spadd (spadd (spadd product_488 product_489) (spadd product_490 product_491)) (spadd (spadd product_492 product_493) (spadd product_494 product_495)))=partial_sum_93 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_93_value (v : ℕ→ℂ) :
    eval v partial_sum_93=eval v (spadd (spadd product_488 product_489) (spadd product_490 product_491))+eval v (spadd (spadd product_492 product_493) (spadd product_494 product_495)) := by
  rw [←partial_sum_93_checked, eval_add]
compact_certificate_declaration theorem partial_sum_94_checked :
    (spadd partial_sum_92 partial_sum_93)=partial_sum_94 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_94_value (v : ℕ→ℂ) :
    eval v partial_sum_94=eval v partial_sum_92+eval v partial_sum_93 := by
  rw [←partial_sum_94_checked, eval_add]
compact_certificate_declaration theorem partial_sum_95_checked :
    (spadd partial_sum_91 partial_sum_94)=partial_sum_95 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_95_value (v : ℕ→ℂ) :
    eval v partial_sum_95=eval v partial_sum_91+eval v partial_sum_94 := by
  rw [←partial_sum_95_checked, eval_add]
compact_certificate_declaration theorem checked_15 : checkZero e15=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_15 (y z w a b u : ℂ) :
    (certificate y z w a b u)[15]?=some 0 := by
  change some ((((((c46_0 y z w a b u)*(d0_0 y z w a b u)+((c46_1 y z w a b u)*(d0_1 y z w a b u)+(c46_2 y z w a b u)*(d0_2 y z w a b u)))+(((c46_3 y z w a b u)*(d0_3 y z w a b u)+(c46_4 y z w a b u)*(d0_4 y z w a b u))+((c46_5 y z w a b u)*(d0_5 y z w a b u)+(c46_6 y z w a b u)*(d0_6 y z w a b u))))+((((c46_7 y z w a b u)*(d0_7 y z w a b u)+(c46_8 y z w a b u)*(d0_8 y z w a b u))+((c46_9 y z w a b u)*(d0_9 y z w a b u)+(c46_10 y z w a b u)*(d0_10 y z w a b u)))+(((c46_11 y z w a b u)*(d0_12 y z w a b u)+(c46_12 y z w a b u)*(d0_13 y z w a b u))+((c46_13 y z w a b u)*(d0_14 y z w a b u)+(c46_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c46_15 y z w a b u)*(d0_16 y z w a b u)+(c46_16 y z w a b u)*(d0_17 y z w a b u))+((c46_17 y z w a b u)*(d0_18 y z w a b u)+(c46_18 y z w a b u)*(d0_19 y z w a b u)))+(((c46_19 y z w a b u)*(d0_20 y z w a b u)+(c46_20 y z w a b u)*(d0_21 y z w a b u))+((c46_21 y z w a b u)*(d0_22 y z w a b u)+(c46_22 y z w a b u)*(d0_23 y z w a b u))))+((((c46_23 y z w a b u)*(d0_24 y z w a b u)+(c46_24 y z w a b u)*(d0_25 y z w a b u))+((c46_25 y z w a b u)*(d0_26 y z w a b u)+(c46_26 y z w a b u)*(d0_27 y z w a b u)))+(((c46_27 y z w a b u)*(d0_28 y z w a b u)+(c46_28 y z w a b u)*(d0_29 y z w a b u))+((c46_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c46_30 y z w a b u)*(d1_46 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e15 checked_15
  simp only [e15, eval_add, eval_mul, eval_scale, eval_pow, product_465_value, product_466_value, product_467_value, product_468_value, product_469_value, product_470_value, product_471_value, product_472_value, product_473_value, product_474_value, product_475_value, product_476_value, product_477_value, product_478_value, product_479_value, partial_sum_90_value, partial_sum_91_value, product_480_value, product_481_value, product_482_value, product_483_value, product_484_value, product_485_value, product_486_value, product_487_value, partial_sum_92_value, product_488_value, product_489_value, product_490_value, product_491_value, product_492_value, product_493_value, product_494_value, product_495_value, partial_sum_93_value, partial_sum_94_value, partial_sum_95_value, n_c46_0_value y z w a b u, n_c46_1_value y z w a b u, n_c46_10_value y z w a b u, n_c46_11_value y z w a b u, n_c46_12_value y z w a b u, n_c46_13_value y z w a b u, n_c46_14_value y z w a b u, n_c46_15_value y z w a b u, n_c46_16_value y z w a b u, n_c46_17_value y z w a b u, n_c46_18_value y z w a b u, n_c46_19_value y z w a b u, n_c46_2_value y z w a b u, n_c46_20_value y z w a b u, n_c46_21_value y z w a b u, n_c46_22_value y z w a b u, n_c46_23_value y z w a b u, n_c46_24_value y z w a b u, n_c46_25_value y z w a b u, n_c46_26_value y z w a b u, n_c46_27_value y z w a b u, n_c46_28_value y z w a b u, n_c46_29_value y z w a b u, n_c46_3_value y z w a b u, n_c46_30_value y z w a b u, n_c46_4_value y z w a b u, n_c46_5_value y z w a b u, n_c46_6_value y z w a b u, n_c46_7_value y z w a b u, n_c46_8_value y z w a b u, n_c46_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_46_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
compact_certificate_declaration theorem product_496_checked :
    mulShort n_c47_0 n_d0_0=product_496 := by
  decide +kernel
compact_certificate_declaration theorem product_496_value (v : ℕ→ℂ) :
    eval v product_496=eval v n_c47_0*eval v n_d0_0 := by
  rw [←product_496_checked, eval_mulShort]
compact_certificate_declaration theorem product_497_checked :
    mulShort n_c47_1 n_d0_1=product_497 := by
  decide +kernel
compact_certificate_declaration theorem product_497_value (v : ℕ→ℂ) :
    eval v product_497=eval v n_c47_1*eval v n_d0_1 := by
  rw [←product_497_checked, eval_mulShort]
compact_certificate_declaration theorem product_498_checked :
    mulShort n_c47_2 n_d0_2=product_498 := by
  decide +kernel
compact_certificate_declaration theorem product_498_value (v : ℕ→ℂ) :
    eval v product_498=eval v n_c47_2*eval v n_d0_2 := by
  rw [←product_498_checked, eval_mulShort]
compact_certificate_declaration theorem product_499_checked :
    mulShort n_c47_3 n_d0_3=product_499 := by
  decide +kernel
compact_certificate_declaration theorem product_499_value (v : ℕ→ℂ) :
    eval v product_499=eval v n_c47_3*eval v n_d0_3 := by
  rw [←product_499_checked, eval_mulShort]
compact_certificate_declaration theorem product_500_checked :
    mulShort n_c47_4 n_d0_4=product_500 := by
  decide +kernel
compact_certificate_declaration theorem product_500_value (v : ℕ→ℂ) :
    eval v product_500=eval v n_c47_4*eval v n_d0_4 := by
  rw [←product_500_checked, eval_mulShort]
compact_certificate_declaration theorem product_501_checked :
    mulShort n_c47_5 n_d0_5=product_501 := by
  decide +kernel
compact_certificate_declaration theorem product_501_value (v : ℕ→ℂ) :
    eval v product_501=eval v n_c47_5*eval v n_d0_5 := by
  rw [←product_501_checked, eval_mulShort]
compact_certificate_declaration theorem product_502_checked :
    mulShort n_c47_6 n_d0_6=product_502 := by
  decide +kernel
compact_certificate_declaration theorem product_502_value (v : ℕ→ℂ) :
    eval v product_502=eval v n_c47_6*eval v n_d0_6 := by
  rw [←product_502_checked, eval_mulShort]
compact_certificate_declaration theorem product_503_checked :
    mulShort n_c47_7 n_d0_7=product_503 := by
  decide +kernel
compact_certificate_declaration theorem product_503_value (v : ℕ→ℂ) :
    eval v product_503=eval v n_c47_7*eval v n_d0_7 := by
  rw [←product_503_checked, eval_mulShort]
compact_certificate_declaration theorem product_504_checked :
    mulShort n_c47_8 n_d0_8=product_504 := by
  decide +kernel
compact_certificate_declaration theorem product_504_value (v : ℕ→ℂ) :
    eval v product_504=eval v n_c47_8*eval v n_d0_8 := by
  rw [←product_504_checked, eval_mulShort]
compact_certificate_declaration theorem product_505_checked :
    mulShort n_c47_9 n_d0_9=product_505 := by
  decide +kernel
compact_certificate_declaration theorem product_505_value (v : ℕ→ℂ) :
    eval v product_505=eval v n_c47_9*eval v n_d0_9 := by
  rw [←product_505_checked, eval_mulShort]
compact_certificate_declaration theorem product_506_checked :
    mulShort n_c47_10 n_d0_10=product_506 := by
  decide +kernel
compact_certificate_declaration theorem product_506_value (v : ℕ→ℂ) :
    eval v product_506=eval v n_c47_10*eval v n_d0_10 := by
  rw [←product_506_checked, eval_mulShort]
compact_certificate_declaration theorem product_507_checked :
    mulShort n_c47_11 n_d0_12=product_507 := by
  decide +kernel
compact_certificate_declaration theorem product_507_value (v : ℕ→ℂ) :
    eval v product_507=eval v n_c47_11*eval v n_d0_12 := by
  rw [←product_507_checked, eval_mulShort]
compact_certificate_declaration theorem product_508_checked :
    mulShort n_c47_12 n_d0_13=product_508 := by
  decide +kernel
compact_certificate_declaration theorem product_508_value (v : ℕ→ℂ) :
    eval v product_508=eval v n_c47_12*eval v n_d0_13 := by
  rw [←product_508_checked, eval_mulShort]
compact_certificate_declaration theorem product_509_checked :
    mulShort n_c47_13 n_d0_14=product_509 := by
  decide +kernel
compact_certificate_declaration theorem product_509_value (v : ℕ→ℂ) :
    eval v product_509=eval v n_c47_13*eval v n_d0_14 := by
  rw [←product_509_checked, eval_mulShort]
compact_certificate_declaration theorem product_510_checked :
    mulShort n_c47_14 n_d0_15=product_510 := by
  decide +kernel
compact_certificate_declaration theorem product_510_value (v : ℕ→ℂ) :
    eval v product_510=eval v n_c47_14*eval v n_d0_15 := by
  rw [←product_510_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_96_checked :
    (spadd (spadd (spadd product_503 product_504) (spadd product_505 product_506)) (spadd (spadd product_507 product_508) (spadd product_509 product_510)))=partial_sum_96 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_96_value (v : ℕ→ℂ) :
    eval v partial_sum_96=eval v (spadd (spadd product_503 product_504) (spadd product_505 product_506))+eval v (spadd (spadd product_507 product_508) (spadd product_509 product_510)) := by
  rw [←partial_sum_96_checked, eval_add]
compact_certificate_declaration theorem partial_sum_97_checked :
    (spadd (spadd (spadd product_496 (spadd product_497 product_498)) (spadd (spadd product_499 product_500) (spadd product_501 product_502))) partial_sum_96)=partial_sum_97 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_97_value (v : ℕ→ℂ) :
    eval v partial_sum_97=eval v (spadd (spadd product_496 (spadd product_497 product_498)) (spadd (spadd product_499 product_500) (spadd product_501 product_502)))+eval v partial_sum_96 := by
  rw [←partial_sum_97_checked, eval_add]
compact_certificate_declaration theorem product_511_checked :
    mulShort n_c47_15 n_d0_16=product_511 := by
  decide +kernel
compact_certificate_declaration theorem product_511_value (v : ℕ→ℂ) :
    eval v product_511=eval v n_c47_15*eval v n_d0_16 := by
  rw [←product_511_checked, eval_mulShort]
compact_certificate_declaration theorem product_512_checked :
    mulShort n_c47_16 n_d0_17=product_512 := by
  decide +kernel
compact_certificate_declaration theorem product_512_value (v : ℕ→ℂ) :
    eval v product_512=eval v n_c47_16*eval v n_d0_17 := by
  rw [←product_512_checked, eval_mulShort]
compact_certificate_declaration theorem product_513_checked :
    mulShort n_c47_17 n_d0_18=product_513 := by
  decide +kernel
compact_certificate_declaration theorem product_513_value (v : ℕ→ℂ) :
    eval v product_513=eval v n_c47_17*eval v n_d0_18 := by
  rw [←product_513_checked, eval_mulShort]
compact_certificate_declaration theorem product_514_checked :
    mulShort n_c47_18 n_d0_19=product_514 := by
  decide +kernel
compact_certificate_declaration theorem product_514_value (v : ℕ→ℂ) :
    eval v product_514=eval v n_c47_18*eval v n_d0_19 := by
  rw [←product_514_checked, eval_mulShort]
compact_certificate_declaration theorem product_515_checked :
    mulShort n_c47_19 n_d0_20=product_515 := by
  decide +kernel
compact_certificate_declaration theorem product_515_value (v : ℕ→ℂ) :
    eval v product_515=eval v n_c47_19*eval v n_d0_20 := by
  rw [←product_515_checked, eval_mulShort]
compact_certificate_declaration theorem product_516_checked :
    mulShort n_c47_20 n_d0_21=product_516 := by
  decide +kernel
compact_certificate_declaration theorem product_516_value (v : ℕ→ℂ) :
    eval v product_516=eval v n_c47_20*eval v n_d0_21 := by
  rw [←product_516_checked, eval_mulShort]
compact_certificate_declaration theorem product_517_checked :
    mulShort n_c47_21 n_d0_22=product_517 := by
  decide +kernel
compact_certificate_declaration theorem product_517_value (v : ℕ→ℂ) :
    eval v product_517=eval v n_c47_21*eval v n_d0_22 := by
  rw [←product_517_checked, eval_mulShort]
compact_certificate_declaration theorem product_518_checked :
    mulShort n_c47_22 n_d0_23=product_518 := by
  decide +kernel
compact_certificate_declaration theorem product_518_value (v : ℕ→ℂ) :
    eval v product_518=eval v n_c47_22*eval v n_d0_23 := by
  rw [←product_518_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_98_checked :
    (spadd (spadd (spadd product_511 product_512) (spadd product_513 product_514)) (spadd (spadd product_515 product_516) (spadd product_517 product_518)))=partial_sum_98 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_98_value (v : ℕ→ℂ) :
    eval v partial_sum_98=eval v (spadd (spadd product_511 product_512) (spadd product_513 product_514))+eval v (spadd (spadd product_515 product_516) (spadd product_517 product_518)) := by
  rw [←partial_sum_98_checked, eval_add]
compact_certificate_declaration theorem product_519_checked :
    mulShort n_c47_23 n_d0_24=product_519 := by
  decide +kernel
compact_certificate_declaration theorem product_519_value (v : ℕ→ℂ) :
    eval v product_519=eval v n_c47_23*eval v n_d0_24 := by
  rw [←product_519_checked, eval_mulShort]
compact_certificate_declaration theorem product_520_checked :
    mulShort n_c47_24 n_d0_25=product_520 := by
  decide +kernel
compact_certificate_declaration theorem product_520_value (v : ℕ→ℂ) :
    eval v product_520=eval v n_c47_24*eval v n_d0_25 := by
  rw [←product_520_checked, eval_mulShort]
compact_certificate_declaration theorem product_521_checked :
    mulShort n_c47_25 n_d0_26=product_521 := by
  decide +kernel
compact_certificate_declaration theorem product_521_value (v : ℕ→ℂ) :
    eval v product_521=eval v n_c47_25*eval v n_d0_26 := by
  rw [←product_521_checked, eval_mulShort]
compact_certificate_declaration theorem product_522_checked :
    mulShort n_c47_26 n_d0_27=product_522 := by
  decide +kernel
compact_certificate_declaration theorem product_522_value (v : ℕ→ℂ) :
    eval v product_522=eval v n_c47_26*eval v n_d0_27 := by
  rw [←product_522_checked, eval_mulShort]
compact_certificate_declaration theorem product_523_checked :
    mulShort n_c47_27 n_d0_28=product_523 := by
  decide +kernel
compact_certificate_declaration theorem product_523_value (v : ℕ→ℂ) :
    eval v product_523=eval v n_c47_27*eval v n_d0_28 := by
  rw [←product_523_checked, eval_mulShort]
compact_certificate_declaration theorem product_524_checked :
    mulShort n_c47_28 n_d0_29=product_524 := by
  decide +kernel
compact_certificate_declaration theorem product_524_value (v : ℕ→ℂ) :
    eval v product_524=eval v n_c47_28*eval v n_d0_29 := by
  rw [←product_524_checked, eval_mulShort]
}
certificate_batch {
compact_certificate_declaration theorem product_525_checked :
    mulShort n_c47_29 n_d0_30=product_525 := by
  decide +kernel
compact_certificate_declaration theorem product_525_value (v : ℕ→ℂ) :
    eval v product_525=eval v n_c47_29*eval v n_d0_30 := by
  rw [←product_525_checked, eval_mulShort]
compact_certificate_declaration theorem product_526_checked :
    mulShort (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c47_30) n_d1_47=product_526 := by
  decide +kernel
compact_certificate_declaration theorem product_526_value (v : ℕ→ℂ) :
    eval v product_526=eval v (spmul (spscale [] (-1) [([],(Int.ofNat 1))]) n_c47_30)*eval v n_d1_47 := by
  rw [←product_526_checked, eval_mulShort]
compact_certificate_declaration theorem partial_sum_99_checked :
    (spadd (spadd (spadd product_519 product_520) (spadd product_521 product_522)) (spadd (spadd product_523 product_524) (spadd product_525 product_526)))=partial_sum_99 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_99_value (v : ℕ→ℂ) :
    eval v partial_sum_99=eval v (spadd (spadd product_519 product_520) (spadd product_521 product_522))+eval v (spadd (spadd product_523 product_524) (spadd product_525 product_526)) := by
  rw [←partial_sum_99_checked, eval_add]
compact_certificate_declaration theorem partial_sum_100_checked :
    (spadd partial_sum_98 partial_sum_99)=partial_sum_100 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_100_value (v : ℕ→ℂ) :
    eval v partial_sum_100=eval v partial_sum_98+eval v partial_sum_99 := by
  rw [←partial_sum_100_checked, eval_add]
compact_certificate_declaration theorem partial_sum_101_checked :
    (spadd partial_sum_97 partial_sum_100)=partial_sum_101 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_101_value (v : ℕ→ℂ) :
    eval v partial_sum_101=eval v partial_sum_97+eval v partial_sum_100 := by
  rw [←partial_sum_101_checked, eval_add]
compact_certificate_declaration theorem checked_16 : checkZero e16=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_16 (y z w a b u : ℂ) :
    (certificate y z w a b u)[16]?=some 0 := by
  change some ((((((c47_0 y z w a b u)*(d0_0 y z w a b u)+((c47_1 y z w a b u)*(d0_1 y z w a b u)+(c47_2 y z w a b u)*(d0_2 y z w a b u)))+(((c47_3 y z w a b u)*(d0_3 y z w a b u)+(c47_4 y z w a b u)*(d0_4 y z w a b u))+((c47_5 y z w a b u)*(d0_5 y z w a b u)+(c47_6 y z w a b u)*(d0_6 y z w a b u))))+((((c47_7 y z w a b u)*(d0_7 y z w a b u)+(c47_8 y z w a b u)*(d0_8 y z w a b u))+((c47_9 y z w a b u)*(d0_9 y z w a b u)+(c47_10 y z w a b u)*(d0_10 y z w a b u)))+(((c47_11 y z w a b u)*(d0_12 y z w a b u)+(c47_12 y z w a b u)*(d0_13 y z w a b u))+((c47_13 y z w a b u)*(d0_14 y z w a b u)+(c47_14 y z w a b u)*(d0_15 y z w a b u)))))+(((((c47_15 y z w a b u)*(d0_16 y z w a b u)+(c47_16 y z w a b u)*(d0_17 y z w a b u))+((c47_17 y z w a b u)*(d0_18 y z w a b u)+(c47_18 y z w a b u)*(d0_19 y z w a b u)))+(((c47_19 y z w a b u)*(d0_20 y z w a b u)+(c47_20 y z w a b u)*(d0_21 y z w a b u))+((c47_21 y z w a b u)*(d0_22 y z w a b u)+(c47_22 y z w a b u)*(d0_23 y z w a b u))))+((((c47_23 y z w a b u)*(d0_24 y z w a b u)+(c47_24 y z w a b u)*(d0_25 y z w a b u))+((c47_25 y z w a b u)*(d0_26 y z w a b u)+(c47_26 y z w a b u)*(d0_27 y z w a b u)))+(((c47_27 y z w a b u)*(d0_28 y z w a b u)+(c47_28 y z w a b u)*(d0_29 y z w a b u))+((c47_29 y z w a b u)*(d0_30 y z w a b u)+-1*(c47_30 y z w a b u)*(d1_47 y z w a b u)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b u) e16 checked_16
  simp only [e16, eval_add, eval_mul, eval_scale, eval_pow, product_496_value, product_497_value, product_498_value, product_499_value, product_500_value, product_501_value, product_502_value, product_503_value, product_504_value, product_505_value, product_506_value, product_507_value, product_508_value, product_509_value, product_510_value, partial_sum_96_value, partial_sum_97_value, product_511_value, product_512_value, product_513_value, product_514_value, product_515_value, product_516_value, product_517_value, product_518_value, partial_sum_98_value, product_519_value, product_520_value, product_521_value, product_522_value, product_523_value, product_524_value, product_525_value, product_526_value, partial_sum_99_value, partial_sum_100_value, partial_sum_101_value, n_c47_0_value y z w a b u, n_c47_1_value y z w a b u, n_c47_10_value y z w a b u, n_c47_11_value y z w a b u, n_c47_12_value y z w a b u, n_c47_13_value y z w a b u, n_c47_14_value y z w a b u, n_c47_15_value y z w a b u, n_c47_16_value y z w a b u, n_c47_17_value y z w a b u, n_c47_18_value y z w a b u, n_c47_19_value y z w a b u, n_c47_2_value y z w a b u, n_c47_20_value y z w a b u, n_c47_21_value y z w a b u, n_c47_22_value y z w a b u, n_c47_23_value y z w a b u, n_c47_24_value y z w a b u, n_c47_25_value y z w a b u, n_c47_26_value y z w a b u, n_c47_27_value y z w a b u, n_c47_28_value y z w a b u, n_c47_29_value y z w a b u, n_c47_3_value y z w a b u, n_c47_30_value y z w a b u, n_c47_4_value y z w a b u, n_c47_5_value y z w a b u, n_c47_6_value y z w a b u, n_c47_7_value y z w a b u, n_c47_8_value y z w a b u, n_c47_9_value y z w a b u, n_d0_0_value y z w a b u, n_d0_1_value y z w a b u, n_d0_10_value y z w a b u, n_d0_12_value y z w a b u, n_d0_13_value y z w a b u, n_d0_14_value y z w a b u, n_d0_15_value y z w a b u, n_d0_16_value y z w a b u, n_d0_17_value y z w a b u, n_d0_18_value y z w a b u, n_d0_19_value y z w a b u, n_d0_2_value y z w a b u, n_d0_20_value y z w a b u, n_d0_21_value y z w a b u, n_d0_22_value y z w a b u, n_d0_23_value y z w a b u, n_d0_24_value y z w a b u, n_d0_25_value y z w a b u, n_d0_26_value y z w a b u, n_d0_27_value y z w a b u, n_d0_28_value y z w a b u, n_d0_29_value y z w a b u, n_d0_3_value y z w a b u, n_d0_30_value y z w a b u, n_d0_4_value y z w a b u, n_d0_5_value y z w a b u, n_d0_6_value y z w a b u, n_d0_7_value y z w a b u, n_d0_8_value y z w a b u, n_d0_9_value y z w a b u, n_d1_47_value y z w a b u] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, cast_int_ofNat, Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
}
#print axioms coefficient_0
#print axioms coefficient_1
#print axioms coefficient_2
#print axioms coefficient_3
#print axioms coefficient_4
#print axioms coefficient_5
#print axioms coefficient_6
#print axioms coefficient_7
#print axioms coefficient_8
#print axioms coefficient_9
#print axioms coefficient_10
#print axioms coefficient_11
#print axioms coefficient_12
#print axioms coefficient_13
#print axioms coefficient_14
#print axioms coefficient_15
#print axioms coefficient_16
end SmallLevelTwentyFiveStageSixBlockReflectedIntegral
