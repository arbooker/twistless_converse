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
namespace SmallLevelTwentySixSourceResultant89
open SmallLevelPolynomialCoefficientCertificate
certificate_batch {

private def bounded_coefficient_27_value4 (y z w a b u : ℂ) : ℂ := ((((465373268736567750)*a + (1209970498715076150)))*y + (((((-3287396770355114586/5:ℂ))*u)*a + (((-42736158014616489618/25:ℂ))*u))))

private theorem bounded_coefficient_27_step4 (y z w a b u : ℂ) : c2_20 y z w a b u * c3_7 y z w a b u + 0 = bounded_coefficient_27_value4 y z w a b u := by
  simp only [c2_20,c3_7,bounded_coefficient_27_value4]
  ring
#print axioms bounded_coefficient_27_step4

private def bounded_coefficient_27_value3 (y z w a b u : ℂ) : ℂ := (((((-6747912396680232375/16:ℂ))*y + (((465373268736567750)*a + ((((-84116565288820187721/200:ℂ))*u + ((22077803532699298215/8:ℂ))))))))*y + (((((-36148334022381636549/50:ℂ))*u)*a + ((((((1769131196810631107649/2000:ℂ))*u + ((-4882232867867414902557/1000:ℂ))))*u + ((14793285466598015637/50:ℂ)))))))

private theorem bounded_coefficient_27_step3 (y z w a b u : ℂ) : c2_19 y z w a b u * c3_8 y z w a b u + bounded_coefficient_27_value4 y z w a b u = bounded_coefficient_27_value3 y z w a b u := by
  simp only [c2_19,c3_8,bounded_coefficient_27_value3,bounded_coefficient_27_value4]
  ring
#print axioms bounded_coefficient_27_step3

private def bounded_coefficient_27_value2 (y z w a b u : ℂ) : ℂ := (((((-5570124416306436519/16:ℂ))*y + ((((-755278427947316949/10:ℂ))*a + ((((-40064731339004444241/200:ℂ))*u + ((4820849764471363077/20:ℂ))))))))*y + ((((((48677106539514843/10:ℂ))*a + ((((2400935382948910743/200:ℂ))*u + ((16733512017885180141/50:ℂ))))))*a + ((((((1634881638015736774209/2000:ℂ))*u + ((-125653747748222178108/125:ℂ))))*u + ((583182670276662745419/200:ℂ)))))))

private theorem bounded_coefficient_27_step2 (y z w a b u : ℂ) : c0_3 y z w a b u * c1_24 y z w a b u + bounded_coefficient_27_value3 y z w a b u = bounded_coefficient_27_value2 y z w a b u := by
  simp only [c0_3,c1_24,bounded_coefficient_27_value2,bounded_coefficient_27_value3]
  ring
#print axioms bounded_coefficient_27_step2

private def bounded_coefficient_27_value1 (y z w a b u : ℂ) : ℂ := (((((77273467217368812/5:ℂ))*y + ((((-400352591885228541/5:ℂ))*a + ((-249582801354829493499/200:ℂ))))))*y + ((((((48677106539514843/10:ℂ))*a + ((((153114434663173191/40:ℂ))*u + ((17490624614937515691/50:ℂ))))))*a + ((((1990487650621251483/200:ℂ))*u + ((767848179247081948899/200:ℂ)))))))

private theorem bounded_coefficient_27_step1 (y z w a b u : ℂ) : c0_2 y z w a b u * c1_25 y z w a b u + bounded_coefficient_27_value2 y z w a b u = bounded_coefficient_27_value1 y z w a b u := by
  simp only [c0_2,c1_25,bounded_coefficient_27_value1,bounded_coefficient_27_value2]
  ring
#print axioms bounded_coefficient_27_step1

private theorem bounded_coefficient_27_step0 (y z w a b u : ℂ) : c0_1 y z w a b u * c1_26 y z w a b u + bounded_coefficient_27_value1 y z w a b u = c4_27 y z w a b u := by
  simp only [c0_1,c1_26,c4_27,bounded_coefficient_27_value1]
  ring
#print axioms bounded_coefficient_27_step0

theorem coefficient_27 (y z w a b u : ℂ) :
    (certificate y z w a b u)[27]?=some 0 := by
  change some (((((c0_1 y z w a b u*c1_26 y z w a b u)+((c0_2 y z w a b u*c1_25 y z w a b u)+(c0_3 y z w a b u*c1_24 y z w a b u)))+((c2_19 y z w a b u*c3_8 y z w a b u)+(c2_20 y z w a b u*c3_7 y z w a b u)))+((-1)*c4_27 y z w a b u)))=some 0
  apply congrArg some
  have h0 := bounded_coefficient_27_step4 y z w a b u
  have h1 := bounded_coefficient_27_step3 y z w a b u
  have h2 := bounded_coefficient_27_step2 y z w a b u
  have h3 := bounded_coefficient_27_step1 y z w a b u
  have h4 := bounded_coefficient_27_step0 y z w a b u
  linear_combination h0 + h1 + h2 + h3 + h4
#print axioms coefficient_27

private def bounded_coefficient_28_value2 (y z w a b u : ℂ) : ℂ := (((-418835941862910975/2:ℂ))*y + (((14793285466598015637/50:ℂ))*u))

private theorem bounded_coefficient_28_step2 (y z w a b u : ℂ) : c2_20 y z w a b u * c3_8 y z w a b u + 0 = bounded_coefficient_28_value2 y z w a b u := by
  simp only [c2_20,c3_8,bounded_coefficient_28_value2]
  ring
#print axioms bounded_coefficient_28_step2

private def bounded_coefficient_28_value1 (y z w a b u : ℂ) : ℂ := (((1318947015078475029/40:ℂ))*y + ((((-15142251941046711/5:ℂ))*a + ((((-1378029911968558719/200:ℂ))*u + ((-4616637724260480087/25:ℂ)))))))

private theorem bounded_coefficient_28_step1 (y z w a b u : ℂ) : c0_3 y z w a b u * c1_25 y z w a b u + bounded_coefficient_28_value2 y z w a b u = bounded_coefficient_28_value1 y z w a b u := by
  simp only [c0_3,c1_25,bounded_coefficient_28_value1,bounded_coefficient_28_value2]
  ring
#print axioms bounded_coefficient_28_step1

private theorem bounded_coefficient_28_step0 (y z w a b u : ℂ) : c0_2 y z w a b u * c1_26 y z w a b u + bounded_coefficient_28_value1 y z w a b u = c4_28 y z w a b u := by
  simp only [c0_2,c1_26,c4_28,bounded_coefficient_28_value1]
  ring
#print axioms bounded_coefficient_28_step0

theorem coefficient_28 (y z w a b u : ℂ) :
    (certificate y z w a b u)[28]?=some 0 := by
  change some (((((c0_2 y z w a b u*c1_26 y z w a b u)+(c0_3 y z w a b u*c1_25 y z w a b u))+(c2_20 y z w a b u*c3_8 y z w a b u))+((-1)*c4_28 y z w a b u)))=some 0
  apply congrArg some
  have h0 := bounded_coefficient_28_step2 y z w a b u
  have h1 := bounded_coefficient_28_step1 y z w a b u
  have h2 := bounded_coefficient_28_step0 y z w a b u
  linear_combination h0 + h1 + h2
#print axioms coefficient_28

theorem coefficient_29 (y z w a b u : ℂ) :
    (certificate y z w a b u)[29]?=some 0 := by
  change some (((c0_3 y z w a b u*c1_26 y z w a b u)+((-1)*c4_29 y z w a b u)))=some 0
  congr 1 <;> simp only [c0_3,c1_26,c4_29] <;> ring
#print axioms coefficient_29

}
end SmallLevelTwentySixSourceResultant89
