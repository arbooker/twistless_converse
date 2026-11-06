module
public import SmallLevelTwentySixPariSourcePolynomialIndexBundleSeriesV4
public import SmallLevelTwentySixPariSourcePolynomialIndexTransposeDataSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixPariSourcePolynomial87
open QuantitativeArithmeticSevenLaurentRows SmallLevelPolynomialCoefficientCertificate
theorem raw_evaluation (x y z w a b u : ℂ) :
    eval x y z w a b 1 (fun j => if j=0 then 1 else u) SmallLevelTwentySixPariRawSource87.rawData=
      evaluate 1 (List.ofFn (partVector x y z w a b u)) := by
  simp only [SmallLevelTwentySixPariRawSource87.rawData,eval_append,part000_binding,part001_binding,part002_binding,part003_binding,part004_binding,part005_binding,part006_binding,part007_binding,part008_binding,part009_binding,part010_binding,part011_binding,part012_binding,part013_binding,part014_binding,part015_binding,part016_binding,part017_binding,part018_binding,part019_binding,part020_binding,part021_binding,part022_binding,part023_binding,part024_binding,part025_binding,part026_binding,part027_binding,part028_binding,part029_binding,part030_binding,part031_binding,part032_binding,part033_binding,part034_binding,part035_binding,part036_binding,part037_binding,part038_binding,part039_binding,part040_binding,part041_binding,part042_binding,part043_binding,part044_binding,part045_binding,part046_binding,part047_binding,part048_binding,part049_binding,part050_binding,part051_binding,part052_binding,part053_binding,part054_binding,part055_binding,part056_binding,part057_binding,part058_binding,part059_binding,part060_binding,part061_binding,part062_binding]
  change _=evaluate 1 [part000 x y z w a b u,part001 x y z w a b u,part002 x y z w a b u,part003 x y z w a b u,part004 x y z w a b u,part005 x y z w a b u,part006 x y z w a b u,part007 x y z w a b u,part008 x y z w a b u,part009 x y z w a b u,part010 x y z w a b u,part011 x y z w a b u,part012 x y z w a b u,part013 x y z w a b u,part014 x y z w a b u,part015 x y z w a b u,part016 x y z w a b u,part017 x y z w a b u,part018 x y z w a b u,part019 x y z w a b u,part020 x y z w a b u,part021 x y z w a b u,part022 x y z w a b u,part023 x y z w a b u,part024 x y z w a b u,part025 x y z w a b u,part026 x y z w a b u,part027 x y z w a b u,part028 x y z w a b u,part029 x y z w a b u,part030 x y z w a b u,part031 x y z w a b u,part032 x y z w a b u,part033 x y z w a b u,part034 x y z w a b u,part035 x y z w a b u,part036 x y z w a b u,part037 x y z w a b u,part038 x y z w a b u,part039 x y z w a b u,part040 x y z w a b u,part041 x y z w a b u,part042 x y z w a b u,part043 x y z w a b u,part044 x y z w a b u,part045 x y z w a b u,part046 x y z w a b u,part047 x y z w a b u,part048 x y z w a b u,part049 x y z w a b u,part050 x y z w a b u,part051 x y z w a b u,part052 x y z w a b u,part053 x y z w a b u,part054 x y z w a b u,part055 x y z w a b u,part056 x y z w a b u,part057 x y z w a b u,part058 x y z w a b u,part059 x y z w a b u,part060 x y z w a b u,part061 x y z w a b u,part062 x y z w a b u]
  simp only [evaluate,one_mul,add_zero]
  ring
#print axioms raw_evaluation

end SmallLevelTwentySixPariSourcePolynomial87
end

section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixPariSourcePolynomial89
open QuantitativeArithmeticSevenLaurentRows SmallLevelPolynomialCoefficientCertificate
theorem raw_evaluation (x y z w a b u : ℂ) :
    eval x y z w a b 1 (fun j => if j=0 then 1 else u) SmallLevelTwentySixPariRawSource89.rawData=
      evaluate 1 (List.ofFn (partVector x y z w a b u)) := by
  simp only [SmallLevelTwentySixPariRawSource89.rawData,eval_append,part000_binding,part001_binding,part002_binding,part003_binding,part004_binding,part005_binding,part006_binding,part007_binding,part008_binding,part009_binding,part010_binding,part011_binding,part012_binding,part013_binding,part014_binding,part015_binding,part016_binding,part017_binding,part018_binding,part019_binding,part020_binding,part021_binding,part022_binding,part023_binding,part024_binding,part025_binding,part026_binding,part027_binding,part028_binding,part029_binding,part030_binding,part031_binding,part032_binding,part033_binding,part034_binding,part035_binding,part036_binding,part037_binding,part038_binding,part039_binding,part040_binding,part041_binding,part042_binding,part043_binding,part044_binding,part045_binding,part046_binding,part047_binding,part048_binding,part049_binding,part050_binding,part051_binding,part052_binding,part053_binding,part054_binding,part055_binding,part056_binding,part057_binding,part058_binding,part059_binding,part060_binding,part061_binding,part062_binding,part063_binding,part064_binding,part065_binding,part066_binding,part067_binding,part068_binding,part069_binding,part070_binding,part071_binding,part072_binding,part073_binding]
  change _=evaluate 1 [part000 x y z w a b u,part001 x y z w a b u,part002 x y z w a b u,part003 x y z w a b u,part004 x y z w a b u,part005 x y z w a b u,part006 x y z w a b u,part007 x y z w a b u,part008 x y z w a b u,part009 x y z w a b u,part010 x y z w a b u,part011 x y z w a b u,part012 x y z w a b u,part013 x y z w a b u,part014 x y z w a b u,part015 x y z w a b u,part016 x y z w a b u,part017 x y z w a b u,part018 x y z w a b u,part019 x y z w a b u,part020 x y z w a b u,part021 x y z w a b u,part022 x y z w a b u,part023 x y z w a b u,part024 x y z w a b u,part025 x y z w a b u,part026 x y z w a b u,part027 x y z w a b u,part028 x y z w a b u,part029 x y z w a b u,part030 x y z w a b u,part031 x y z w a b u,part032 x y z w a b u,part033 x y z w a b u,part034 x y z w a b u,part035 x y z w a b u,part036 x y z w a b u,part037 x y z w a b u,part038 x y z w a b u,part039 x y z w a b u,part040 x y z w a b u,part041 x y z w a b u,part042 x y z w a b u,part043 x y z w a b u,part044 x y z w a b u,part045 x y z w a b u,part046 x y z w a b u,part047 x y z w a b u,part048 x y z w a b u,part049 x y z w a b u,part050 x y z w a b u,part051 x y z w a b u,part052 x y z w a b u,part053 x y z w a b u,part054 x y z w a b u,part055 x y z w a b u,part056 x y z w a b u,part057 x y z w a b u,part058 x y z w a b u,part059 x y z w a b u,part060 x y z w a b u,part061 x y z w a b u,part062 x y z w a b u,part063 x y z w a b u,part064 x y z w a b u,part065 x y z w a b u,part066 x y z w a b u,part067 x y z w a b u,part068 x y z w a b u,part069 x y z w a b u,part070 x y z w a b u,part071 x y z w a b u,part072 x y z w a b u,part073 x y z w a b u]
  simp only [evaluate,one_mul,add_zero]
  ring
#print axioms raw_evaluation

end SmallLevelTwentySixPariSourcePolynomial89
end
