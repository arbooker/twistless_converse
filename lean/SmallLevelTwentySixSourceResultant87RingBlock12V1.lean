module
public import SmallLevelTwentySixSourceResultantIndexDataSeriesV4
public meta import SmallLevelCertificateBatchCommandV1
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelTwentySixSourceResultant87
open SmallLevelPolynomialCoefficientCertificate
certificate_batch {

private def bounded_coefficient_26_value4 (y z w a b u : ℂ) : ℂ := ((((-465373268736567750)*a + (-1209970498715076150)))*y + ((((383467573438931826)*u)*a + (((4985078454706113738/5:ℂ))*u))))

private theorem bounded_coefficient_26_step4 (y z w a b u : ℂ) : c2_19 y z w a b u * c3_7 y z w a b u + 0 = bounded_coefficient_26_value4 y z w a b u := by
  simp only [c2_19,c3_7,bounded_coefficient_26_value4]
  ring
#print axioms bounded_coefficient_26_step4

private def bounded_coefficient_26_value3 (y z w a b u : ℂ) : ℂ := (((((6582446345573897175/16:ℂ))*y + (((-558447922483881300)*a + ((((152722794551761346913/200:ℂ))*u + ((-10047050892585008055/8:ℂ))))))))*y + (((((15351733389081896937/50:ℂ))*u)*a + ((((((-51320934500943703869/400:ℂ))*u + ((546600091828948268553/200:ℂ))))*u + ((-1725604080475193217/10:ℂ)))))))

private theorem bounded_coefficient_26_step3 (y z w a b u : ℂ) : c2_18 y z w a b u * c3_8 y z w a b u + bounded_coefficient_26_value4 y z w a b u = bounded_coefficient_26_value3 y z w a b u := by
  simp only [c2_18,c3_8,bounded_coefficient_26_value3,bounded_coefficient_26_value4]
  ring
#print axioms bounded_coefficient_26_step3

private def bounded_coefficient_26_value2 (y z w a b u : ℂ) : ℂ := (((((28971938542575566187/80:ℂ))*y + ((((450877807615025817/5:ℂ))*a + ((((78382582782597994797/200:ℂ))*u + ((-56768116484946449583/100:ℂ))))))))*y + ((((((332784963834408189/10:ℂ))*a + ((((10117453940033305437/200:ℂ))*u + ((19932376526360574939/50:ℂ))))))*a + ((((((-183057367497141343869/400:ℂ))*u + ((29234868620003415369/25:ℂ))))*u + ((71427144180674970909/200:ℂ)))))))

private theorem bounded_coefficient_26_step2 (y z w a b u : ℂ) : c0_3 y z w a b u * c1_23 y z w a b u + bounded_coefficient_26_value3 y z w a b u = bounded_coefficient_26_value2 y z w a b u := by
  simp only [c0_3,c1_23,bounded_coefficient_26_value2,bounded_coefficient_26_value3]
  ring
#print axioms bounded_coefficient_26_step2

private def bounded_coefficient_26_value1 (y z w a b u : ℂ) : ℂ := (((((15859332080362836/5:ℂ))*y + ((((315084227506795071/5:ℂ))*a + ((90506141488161536319/200:ℂ))))))*y + ((((((332784963834408189/10:ℂ))*a + ((((13612646889627669/8:ℂ))*u + ((24458829196634933139/50:ℂ))))))*a + ((((176964409565159697/40:ℂ))*u + ((189013374578542430709/200:ℂ)))))))

private theorem bounded_coefficient_26_step1 (y z w a b u : ℂ) : c0_2 y z w a b u * c1_24 y z w a b u + bounded_coefficient_26_value2 y z w a b u = bounded_coefficient_26_value1 y z w a b u := by
  simp only [c0_2,c1_24,bounded_coefficient_26_value1,bounded_coefficient_26_value2]
  ring
#print axioms bounded_coefficient_26_step1

private theorem bounded_coefficient_26_step0 (y z w a b u : ℂ) : c0_1 y z w a b u * c1_25 y z w a b u + bounded_coefficient_26_value1 y z w a b u = c4_26 y z w a b u := by
  simp only [c0_1,c1_25,c4_26,bounded_coefficient_26_value1]
  ring
#print axioms bounded_coefficient_26_step0

theorem coefficient_26 (y z w a b u : ℂ) :
    (certificate y z w a b u)[26]?=some 0 := by
  change some (((((c0_1 y z w a b u*c1_25 y z w a b u)+((c0_2 y z w a b u*c1_24 y z w a b u)+(c0_3 y z w a b u*c1_23 y z w a b u)))+((c2_18 y z w a b u*c3_8 y z w a b u)+(c2_19 y z w a b u*c3_7 y z w a b u)))+((-1)*c4_26 y z w a b u)))=some 0
  apply congrArg some
  have h0 := bounded_coefficient_26_step4 y z w a b u
  have h1 := bounded_coefficient_26_step3 y z w a b u
  have h2 := bounded_coefficient_26_step2 y z w a b u
  have h3 := bounded_coefficient_26_step1 y z w a b u
  have h4 := bounded_coefficient_26_step0 y z w a b u
  linear_combination h0 + h1 + h2 + h3 + h4
#print axioms coefficient_26

private def bounded_coefficient_27_value2 (y z w a b u : ℂ) : ℂ := (((418835941862910975/2:ℂ))*y + (((-1725604080475193217/10:ℂ))*u))

private theorem bounded_coefficient_27_step2 (y z w a b u : ℂ) : c2_19 y z w a b u * c3_8 y z w a b u + 0 = bounded_coefficient_27_value2 y z w a b u := by
  simp only [c2_19,c3_8,bounded_coefficient_27_value2]
  ring
#print axioms bounded_coefficient_27_step2

private def bounded_coefficient_27_value1 (y z w a b u : ℂ) : ℂ := (((-1196010905838367437/40:ℂ))*y + ((((-90529053405487164/5:ℂ))*a + ((((-122513822006649021/40:ℂ))*u + ((-587931151989337299/5:ℂ)))))))

private theorem bounded_coefficient_27_step1 (y z w a b u : ℂ) : c0_3 y z w a b u * c1_24 y z w a b u + bounded_coefficient_27_value2 y z w a b u = bounded_coefficient_27_value1 y z w a b u := by
  simp only [c0_3,c1_24,bounded_coefficient_27_value1,bounded_coefficient_27_value2]
  ring
#print axioms bounded_coefficient_27_step1

private theorem bounded_coefficient_27_step0 (y z w a b u : ℂ) : c0_2 y z w a b u * c1_25 y z w a b u + bounded_coefficient_27_value1 y z w a b u = c4_27 y z w a b u := by
  simp only [c0_2,c1_25,c4_27,bounded_coefficient_27_value1]
  ring
#print axioms bounded_coefficient_27_step0

theorem coefficient_27 (y z w a b u : ℂ) :
    (certificate y z w a b u)[27]?=some 0 := by
  change some (((((c0_2 y z w a b u*c1_25 y z w a b u)+(c0_3 y z w a b u*c1_24 y z w a b u))+(c2_19 y z w a b u*c3_8 y z w a b u))+((-1)*c4_27 y z w a b u)))=some 0
  apply congrArg some
  have h0 := bounded_coefficient_27_step2 y z w a b u
  have h1 := bounded_coefficient_27_step1 y z w a b u
  have h2 := bounded_coefficient_27_step0 y z w a b u
  linear_combination h0 + h1 + h2
#print axioms coefficient_27

theorem coefficient_28 (y z w a b u : ℂ) :
    (certificate y z w a b u)[28]?=some 0 := by
  change some (((c0_3 y z w a b u*c1_25 y z w a b u)+((-1)*c4_28 y z w a b u)))=some 0
  congr 1 <;> simp only [c0_3,c1_25,c4_28] <;> ring
#print axioms coefficient_28

}
end SmallLevelTwentySixSourceResultant87
